use core::fmt;
use std::ffi::CStr;
use std::io::Write as _;
use std::str::FromStr;
use std::sync::LazyLock;
use std::time::Duration;

use pgrx::pgrx_sql_entity_graph::metadata::{
    ArgumentError, Returns, ReturnsError, SqlMapping, SqlTranslatable,
};
use pgrx::StringInfo;
use pgrx::{pg_shmem_init, prelude::*, PGRXSharedMemory, PgLwLock};

mod base32;
use base32::Base32Encoder;

::pgrx::pg_module_magic!(name, version);

// SAFETY: C FFI
static SHARED_MONOTONICITY_STATE: PgLwLock<MonotonicityState> =
    unsafe { PgLwLock::new(c"pgx_plid_monotonicity_state") };

#[pg_guard]
pub extern "C-unwind" fn _PG_init() {
    pg_shmem_init!(SHARED_MONOTONICITY_STATE = MonotonicityState::Uninitialized);
}

const PREFIX_CHARS: &[u8] = b"\0abcdefghijklmnopqrstuvwxyz";
const POSTGRES_EPOCH_OFFSET: Duration = Duration::from_secs(946684800);
const PREFIX_LEN: usize = 3;
const SEPARATOR: char = '_';
const TIME_MASK: u64 = 0x0000_FFFF_FFFF_FFFF_u64;

/// A ULID inspired id with a compact 128 bit representation.
///
/// ## Components
/// - **Prefix:** Up to 3 characters of prefix. 16 bits
/// - **Timestamp:** 48 bits of timestamp information. Millisecond precision with UNIX epoch. Max
///   date: 2527-06-23T06:20:44.416Z  Mon Jun 23 2527 07:20:44
/// - **Random:** 64 bits of random data.
///
/// ## String representation
///
/// The string representation is the initial prefix, `_` separator, followed by the base32 encoded
/// representation of the timestamp and random components. The base32 encoding is Crockford's
/// base32 encoding (no padding, no ambiguous characters).
/// Examples:
///
/// * `abc_01ARZ3NDEKTSV4RRFFQ69G5FAV`
/// * `ab_01ARZ3NDEKTSV4RRFFQ69G5FAV`
/// * `a_01ARZ3NDEKTSV4RRFFQ69G5FAV`
///
/// The valid alphabet for the prefix is `[a-z]`.
///
/// When parsing, uppercase letters are also accepted and mapped to lowercase. For the base32
/// portion of the string there is disambiguation as per Crockford's base32 specification.
///
/// ## Layout
/// ```text
/// 0                   1                   2                   3
/// 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |         prefix              |0|      timestamp first 16 bits  |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |                     timestamp last 32 bits                    |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |                      64 bits  of random data                  |
/// |                                                               |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// ```
///
/// The prefix represents at most 3 characters, each character taking 5 bits, with the last bit of
/// the 16 first bit reserved (set to 0). This allows for prefixes of length 1-3 characters.
/// The prefix numbering is 'a' = 1, 'b' = 2, ..., 'z' = 26.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Hash, Ord)]
#[repr(C)]
pub struct Plid(u128);

extension_sql!(
    r#"CREATE TYPE plid;"#,
    name = "create_plid_shell_type",
    creates = [Type(Plid)]
);

impl Plid {
    /// Generate a new Plid with the given prefix.
    /// The prefix must be 1-3 characters long, and only contain characters in the range 'a'-'z'.
    /// Returns an error if the prefix is invalid or if strong random bytes cannot be generated.
    /// The [`make_time`] function is used to generate the timestamp portion, and should return the
    /// unix epoch time in milliseconds.
    /// The [`make_random`] function is used to fill a byte slice with strong random bytes. It should
    /// return true on success, false on failure. On success, the byte slice should be filled with
    /// random bytes.
    /// The [`ensure_monotonicity`] function is used to ensure that the generated Plid is
    /// monotonic with respect to previously generated Plids. This is necessary when
    /// multiple Plids are generated with the same timestamp. The function should return
    /// Ok(plid) if the plid is valid, or an error if monotonicity cannot be ensured.
    pub fn gen(
        prefix: &str,
        make_time: impl Fn() -> u64,
        make_random: impl Fn(&mut [u8]) -> bool,
        ensure_monotonicity: impl Fn(Plid) -> Result<Plid>,
    ) -> Result<Self> {
        let prefix = map_prefix(prefix)?;
        let time = make_time();
        if time >> 48 != 0 {
            // Timestamp too large to fit in 48 bits
            return Err(Error::TimestampOverflow);
        }

        let random_bytes = 0u64.to_ne_bytes();
        let mut random_bytes = random_bytes;
        let success = make_random(&mut random_bytes);
        if !success {
            return Err(Error::NoStrongRandom);
        }

        let out = ((prefix as u128) << 112)
            | (((time & TIME_MASK) as u128) << 64)
            | (u64::from_ne_bytes(random_bytes) as u128);

        // Make sure we are monotonic
        ensure_monotonicity(Self(out))
    }

    /// Create a new Plid with the same timestamp but new random bits.
    fn with_random_bits_u64(self, new_random: u64) -> Self {
        Self((self.0 & 0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0000) | (new_random as u128))
    }

    fn as_prefix_bytes(&self) -> [u8; PREFIX_LEN] {
        // FFFF FSSS SSTT TTTR
        let mut prefix = [0u8; PREFIX_LEN];
        let p = (self.0 >> 112) as u16;

        let i1 = (p >> 11) as usize;
        let i2 = ((p & 0x7C0) >> 6) as usize;
        let i3 = ((p & 0x03E) >> 1) as usize;
        prefix[0] = PREFIX_CHARS[i1];
        prefix[1] = PREFIX_CHARS[i2];
        prefix[2] = PREFIX_CHARS[i3];

        prefix
    }

    fn as_duration_since_epoch(&self) -> Duration {
        let ms = self.as_timestamp_u64();

        Duration::from_millis(ms)
    }

    fn as_timestamp_u64(&self) -> u64 {
        ((self.0 >> 64) & 0x0000_FFFF_FFFF_FFFF) as u64
    }

    fn as_random_bits_u64(&self) -> u64 {
        self.0 as u64
    }
}

/// State used to ensure monotonicity when generating Plids with the same timestamp.
enum MonotonicityState {
    Uninitialized,
    Initialized(InitializedMonotonicityState),
}

/// State used when the monotonicity state has been initialized for a given timestamp.
struct InitializedMonotonicityState {
    /// The timestamp for this state.
    /// 48 bit milliseconds since UNIX epoch.
    timestamp: u64,
    /// The last random value used for this timestamp.
    last_random: u64,
}

impl MonotonicityState {
    fn ensure(&mut self, plid: Plid) -> Result<Plid> {
        let current = match self {
            MonotonicityState::Uninitialized => {
                let new_state = InitializedMonotonicityState {
                    timestamp: plid.as_timestamp_u64(),
                    last_random: plid.as_random_bits_u64(),
                };
                *self = MonotonicityState::Initialized(new_state);
                return Ok(plid);
            }
            MonotonicityState::Initialized(s) => s,
        };

        if plid.as_timestamp_u64() != current.timestamp {
            // New timestamp, reset state
            current.timestamp = plid.as_timestamp_u64();
            current.last_random = plid.as_random_bits_u64();
            return Ok(plid);
        }

        // Same timestamp, increment random portion
        let new_random = current.last_random.wrapping_add(1);
        if new_random == 0 {
            return Err(Error::RandomOverflow);
        }
        current.last_random = new_random;

        Ok(plid.with_random_bits_u64(new_random))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    PrefixTooShort,
    PrefixTooLong { length: usize },
    InvalidPrefixCharacter { at: usize, character: char },
    NoStrongRandom,
    RandomOverflow,
    MissingSeparator,
    DecodeError(base32::DecodeError),
    // The rest portion must be exactly 23 characters long
    InvalidIdPortion { length: usize },
    TimestampOverflow,
}

type Result<T, E = Error> = core::result::Result<T, E>;

#[inline]
fn map_prefix(prefix: &str) -> Result<u16> {
    if prefix.is_empty() {
        return Err(Error::PrefixTooShort);
    }
    if prefix.len() > PREFIX_LEN {
        return Err(Error::PrefixTooLong {
            length: prefix.len(),
        });
    }

    let mut out = 0_u16;
    let prefix_bytes = prefix.as_bytes();

    // 1111 1222 2233 333R
    for (i, &b) in prefix_bytes.iter().take(PREFIX_LEN).enumerate() {
        if !b.is_ascii_lowercase() && !b.is_ascii_uppercase() {
            return Err(Error::InvalidPrefixCharacter {
                at: i,
                character: b as char,
            });
        }
        let index = if b.is_ascii_uppercase() {
            b - b'A' + 1
        } else {
            b - b'a' + 1
        };
        match i {
            0 => {
                out |= ((index as u16) << 11) & 0xF800;
            }
            1 => {
                out |= ((index as u16) << 6) & 0x7C0;
            }
            2 => {
                out |= ((index as u16) << 1) & 0x03E;
            }
            _ => unreachable!("Previously limited to 3 chars"),
        }
    }

    Ok(out)
}

fn prefix_bytes_as_str(prefix: &[u8; PREFIX_LEN]) -> &str {
    let first_zero = prefix.iter().position(|&c| c == 0).unwrap_or(PREFIX_LEN);
    str::from_utf8(&prefix[..first_zero]).expect("Valid UTF-8 because only a-z used")
}

// TODO: Can this be `parallel_safe`? Does pgalloc allow that?
#[pg_extern(immutable, strict)]
fn plid_in(input: &core::ffi::CStr) -> BoxedPlid {
    let s = input.to_str().expect("Valid UTF-8 string");
    let parsed = s.parse();

    let plid = match parsed {
        Ok(plid) => plid,
        Err(err) => {
            ereport!(
                ERROR,
                PgSqlErrorCode::ERRCODE_INVALID_TEXT_REPRESENTATION,
                format!("invalid input syntax for type plid: \"{s}\": {err}")
            );
        }
    };

    // SAFETY: C FFI
    let mut alloc = unsafe { PgBox::<Plid>::alloc() };
    *alloc = plid;

    alloc.into_pg_boxed()
}

#[pg_extern(immutable, strict, parallel_safe)]
fn plid_out(plid: BoxedPlid) -> &'static CStr {
    let mut sb = StringInfo::new();
    write!(sb, "{plid}").expect("Writing to StringInfo cannot fail");

    // SAFETY: StringInfo guarantees null termination, Postgres owns the memory after leak
    unsafe { sb.leak_cstr() }
}

/// This is the internal type that Postgres will use to represent Plid values.
/// It is boxed because Postgres cannot natively handle 128 bit integers.
/// This matches Posgres's internal representation of other 128 bit types like UUID.
type BoxedPlid = PgBox<Plid>;

/// Send an instance of a plid in Postgres's internal format, return a bytea.
#[pg_extern(immutable, strict, parallel_safe)]
fn plid_send(plid: BoxedPlid) -> Vec<u8> {
    // TODO: Figure out how to avoid the allocation on the Rust side by directly using `pg_sys` to
    // construct a `bytea`.
    let bytes = plid.0.to_ne_bytes();
    bytes.to_vec()

    // C code from uuid.h:
    //
    // StringInfoData buffer;
    // pq_begintypsend(&buffer);
    // pq_sendbytes(&buffer, uuid->data, UUID_LEN);
    // PG_RETURN_BYTEA_P(pq_endtypsend(&buffer));
    //
    // Rust translation attempt:
    //
    // let mut buffer = pg_sys::StringInfoData::default();
    // unsafe {
    //     pg_sys::pq_begintypsend(&mut buffer as *mut pg_sys::StringInfoData);
    //     pg_sys::pq_sendbytes(
    //         &mut buffer as *mut pg_sys::StringInfoData,
    //         bytes.as_ptr(),
    //         bytes.len() as i32,
    //     );
    //     let bytea_ptr = pg_sys::pq_endtypsend(&mut buffer as *mut pg_sys::StringInfoData);
    //     Unclear what the return type should be to please pg_extern. Returning a raw Datum
    //     doesn't work.
    //     bytea_ptr.into()
    // }
}

/// Receive an instance of a plid in Postgres's internal format, return a BoxedPlid.
// TOOD: Can this be `parallel_safe`? Does pgalloc allow that?
#[pg_extern(immutable, strict)]
fn plid_recv(mut internal: pgrx::datum::Internal) -> BoxedPlid {
    // SAFETY: Postgres guarantees that that this is a valid StringInfoData pointer
    let string_info = unsafe {
        StringInfo::from_pg(internal.get_mut().unwrap() as *mut pg_sys::StringInfoData).unwrap()
    };
    let slice = string_info.as_bytes();
    assert_eq!(slice.len(), 16, "plid RECV input must be 16 bytes");
    let bytes: [u8; 16] = slice.try_into().expect("16 bytes for Plid");
    // SAFETY: C FFI
    let mut alloc = unsafe { PgBox::<Plid>::alloc() };
    let plid = Plid(u128::from_ne_bytes(bytes));
    *alloc = plid;

    alloc.into_pg_boxed()
}

extension_sql!(
    r#"
    CREATE TYPE plid (
        INTERNALLENGTH = 16,
        INPUT = plid_in,
        OUTPUT = plid_out,
        RECEIVE = plid_recv,
        SEND = plid_send
    );
"#,
    name = "create_plid_type",
    requires = [
        "create_plid_shell_type",
        plid_in,
        plid_out,
        plid_recv,
        plid_send
    ],
);

#[pg_extern(immutable, strict, parallel_safe)]
fn plid_lt(plid1: BoxedPlid, plid2: BoxedPlid) -> bool {
    plid1.0 < plid2.0
}
#[pg_extern(immutable, strict, parallel_safe)]
fn plid_le(plid1: BoxedPlid, plid2: BoxedPlid) -> bool {
    plid1.0 <= plid2.0
}

#[pg_extern(immutable, strict, parallel_safe)]
fn plid_eq(plid1: BoxedPlid, plid2: BoxedPlid) -> bool {
    plid1 == plid2
}

#[pg_extern(immutable, strict, parallel_safe)]
fn plid_neq(plid1: BoxedPlid, plid2: BoxedPlid) -> bool {
    plid1 != plid2
}

#[pg_extern(immutable, strict, parallel_safe)]
fn plid_ge(plid1: BoxedPlid, plid2: BoxedPlid) -> bool {
    plid1.0 >= plid2.0
}

#[pg_extern(immutable, strict, parallel_safe)]
fn plid_gt(plid1: BoxedPlid, plid2: BoxedPlid) -> bool {
    plid1.0 > plid2.0
}
#[pg_extern(immutable, strict, parallel_safe)]
fn btree_plid_cmp(plid1: BoxedPlid, plid2: BoxedPlid) -> i32 {
    plid1.0.cmp(&plid2.0) as i32
}

extension_sql!(
    r#"
    CREATE OPERATOR <  (
        LEFTARG = plid,
        RIGHTARG = plid,
        PROCEDURE = plid_lt,
        COMMUTATOR = >,
        NEGATOR = >=,
        RESTRICT = scalarltsel,
        JOIN = scalarltjoinsel
    );
"#,
    name = "create_plid_lt_operator",
    requires = ["create_plid_type", plid_lt]
);

extension_sql!(
    r#"
    CREATE OPERATOR <=  (
        LEFTARG = plid,
        RIGHTARG = plid,
        PROCEDURE = plid_le,
        COMMUTATOR = >=,
        NEGATOR = >,
        RESTRICT = scalarlesel,
        JOIN = scalarlejoinsel
    );
"#,
    name = "create_plid_le_operator",
    requires = ["create_plid_type", plid_le]
);

extension_sql!(
    r#"
    CREATE OPERATOR =  (
        LEFTARG = plid,
        RIGHTARG = plid,
        COMMUTATOR = =,
        NEGATOR = <>,
        PROCEDURE = plid_eq,
        RESTRICT = eqsel,
        JOIN = eqjoinsel
    );
"#,
    name = "create_plid_eq_operator",
    requires = ["create_plid_type", plid_eq]
);

extension_sql!(
    r#"
    CREATE OPERATOR <>  (
        LEFTARG = plid,
        RIGHTARG = plid,
        COMMUTATOR = <>,
        NEGATOR = =,
        PROCEDURE = plid_neq,
        RESTRICT = neqsel,
        JOIN = neqjoinsel
    );
"#,
    name = "create_plid_neq_operator",
    requires = ["create_plid_type", plid_neq]
);

extension_sql!(
    r#"
    CREATE OPERATOR >=  (
        LEFTARG = plid,
        RIGHTARG = plid,
        PROCEDURE = plid_ge,
        COMMUTATOR = <=,
        NEGATOR = <,
        RESTRICT = scalargesel,
        JOIN = scalargejoinsel
    );
"#,
    name = "create_plid_ge_operator",
    requires = ["create_plid_type", plid_ge]
);

extension_sql!(
    r#"
    CREATE OPERATOR >  (
        LEFTARG = plid,
        RIGHTARG = plid,
        PROCEDURE = plid_gt,
        COMMUTATOR = <,
        NEGATOR = <=,
        RESTRICT = scalargtsel,
        JOIN = scalargtjoinsel
    );
"#,
    name = "create_plid_gt_operator",
    requires = ["create_plid_type", plid_gt]
);

extension_sql!(
    r#"
    CREATE OPERATOR CLASS plid_btree_ops
    DEFAULT FOR TYPE plid USING btree AS
        OPERATOR 1 < ,
        OPERATOR 2 <= ,
        OPERATOR 3 = ,
        OPERATOR 4 >= ,
        OPERATOR 5 > ,
        FUNCTION 1 btree_plid_cmp(plid, plid);
"#,
    name = "create_plid_btree_ops",
    requires = [
        "create_plid_type",
        "create_plid_lt_operator",
        "create_plid_le_operator",
        "create_plid_eq_operator",
        "create_plid_ge_operator",
        "create_plid_gt_operator",
        btree_plid_cmp
    ]
);

// `SqlTranslatable` safety requirements:
// By implementing this, you assert you are not lying to either Postgres or Rust in doing so.
// This trait asserts a safe translation exists between values of this type from Rust to SQL,
// or from SQL into Rust. If you are mistaken about how this works, either the Postgres C API
// or the Rust handling in PGRX may emit undefined behavior.
//
// SAFETY: We have implement ed the required methods to correctly map the `Plid` type
// to the corresponding SQL type `plid`.
unsafe impl SqlTranslatable for Plid {
    fn argument_sql() -> Result<SqlMapping, ArgumentError> {
        Ok(SqlMapping::literal("plid"))
    }

    fn return_sql() -> Result<Returns, ReturnsError> {
        Ok(Returns::One(SqlMapping::literal("plid")))
    }
}

impl FromStr for Plid {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let Some((prefix, rest)) = s.split_once(SEPARATOR) else {
            return Err(Error::MissingSeparator)
        };

        let prefix = map_prefix(prefix)?;
        if rest.len() != 23 {
            return Err(Error::InvalidIdPortion { length: rest.len() });
        }
        // NB: 23 bytes of base32 encodes to 15 bytes of data (23 * 5 = 115 bits). However, we
        // only need 14 bytes thus we ignore the last 2 bits of the decoded data.
        let mut bytes = [0u8; 16];
        base32::decode(rest, &mut bytes[2..]).map_err(Error::DecodeError)?;
        let time_and_random = u128::from_be_bytes(bytes[..].try_into().unwrap());
        let combined = ((prefix as u128) << 112) | time_and_random;

        Ok(Plid(combined))
    }
}

/// Get the current time in milliseconds since UNIX epoch.
/// This is used for generating the timestamp portion of the Plid.
fn pg_time_millis() -> u64 {
    // SAFETY: C FFI call to Postgres function
    unsafe {
        (pg_sys::GetCurrentTimestamp() as u64 / 1000) + POSTGRES_EPOCH_OFFSET.as_millis() as u64
    }
}

fn pg_strong_random(bytes: &mut [u8]) -> bool {
    // SAFETY: C FFI call to Postgres function
    unsafe { pg_sys::pg_strong_random(bytes.as_mut_ptr() as *mut core::ffi::c_void, bytes.len()) }
}

fn pg_ensure_monotonicity(plid: Plid) -> Result<Plid> {
    let mut state = SHARED_MONOTONICITY_STATE.exclusive();

    state.ensure(plid)
}

fn pg_no_monotonicity(plid: Plid) -> Result<Plid> {
    Ok(plid)
}

/// Generate a new Plid with the given prefix.
#[pg_extern(parallel_safe, strict)]
fn gen_plid(prefix: &str) -> Result<BoxedPlid> {
    // SAFETY: C FFI
    let mut alloc = unsafe { PgBox::<Plid>::alloc() };
    let plid = Plid::gen(prefix, pg_time_millis, pg_strong_random, pg_no_monotonicity)?;
    *alloc = plid;

    Ok(alloc.into_pg_boxed())
}

#[pg_extern(parallel_safe, strict)]
fn gen_plid_monotonic(prefix: &str) -> Result<BoxedPlid> {
    // SAFETY: C FFI
    let mut alloc = unsafe { PgBox::<Plid>::alloc() };
    let plid = Plid::gen(
        prefix,
        pg_time_millis,
        pg_strong_random,
        pg_ensure_monotonicity,
    )?;
    *alloc = plid;

    Ok(alloc.into_pg_boxed())
}

#[pg_extern(immutable, parallel_safe, strict)]
fn plid_to_timestamptz(plid: BoxedPlid) -> TimestampWithTimeZone {
    let duration_since_epoch = plid.as_duration_since_epoch();
    to_timestamp(duration_since_epoch.as_secs_f64())
}

#[pg_extern(immutable, parallel_safe, strict)]
fn plid_to_timestamp(plid: BoxedPlid) -> Timestamp {
    plid_to_timestamptz(plid).into()
}

static UNIX_EPOCH: LazyLock<TimestampWithTimeZone> = LazyLock::new(|| to_timestamp(0.0));
/// Turn a timestamp with time zone into a Plid with the given prefix.
/// The random bits are set to all 1s.
/// This is useful for generating plids for range queries.
#[pg_extern(immutable, parallel_safe, strict)]
fn timestamptz_to_plid(ts: TimestampWithTimeZone, prefix: &str) -> Result<BoxedPlid> {
    let duration_since_epoch: Duration = (ts - *UNIX_EPOCH)
        .try_into()
        .expect("Timestamp to be after UNIX epoch");
    let millis = duration_since_epoch.as_millis() as u64;

    // SAFETY: C FFI
    let mut alloc = unsafe { PgBox::<Plid>::alloc() };
    let plid = Plid::gen(
        prefix,
        || millis,
        |bytes| {
            bytes.fill(0xFF);

            true
        },
        Ok,
    )?;
    *alloc = plid;

    Ok(alloc.into_pg_boxed())
}

#[pg_extern(immutable, parallel_safe, strict)]
fn plid_to_prefix(plid: BoxedPlid) -> String {
    let bytes = plid.as_prefix_bytes();
    let prefix = prefix_bytes_as_str(&bytes);
    prefix.to_string()
}

impl fmt::Display for Plid {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let prefix_bytes = self.as_prefix_bytes();
        let prefix = prefix_bytes_as_str(&prefix_bytes);
        let rest = &self.0.to_be_bytes()[2..];
        let base32_encoder: Base32Encoder = rest.into();
        write!(f, "{}{}{}", prefix, SEPARATOR, base32_encoder)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::PrefixTooShort => write!(f, "Prefix is too short; must be at least 1 character"),
            Error::PrefixTooLong { length } => write!(
                f,
                "Prefix is too long ({} characters); must be at most 3 characters",
                length
            ),
            Error::InvalidPrefixCharacter { at, character } => write!(
                f,
                "Invalid character '{}' at position {} in prefix; only 'a'-'z' allowed",
                character, at
            ),
            Error::NoStrongRandom => write!(f, "Failed to generate strong random bytes"),
            Error::RandomOverflow => write!(
                f,
                "Random portion overflowed while ensuring monotonicity for Plid generation"
            ),
            Error::MissingSeparator => write!(f, "Missing separator character '_' in Plid string"),
            Error::DecodeError(decode_error) => {
                write!(f, "Base 32 Decode error: {}", decode_error)
            }
            Error::InvalidIdPortion { length } => write!(
                f,
                "Invalid ID portion length ({} characters); must be exactly 23 characters",
                length
            ),
            Error::TimestampOverflow => write!(
                f,
                "Timestamp overflowed 48 bits; too large to encode in Plid"
            ),
        }
    }
}

/// SAFETY: This type is safe to be used in Postgres shared memory because it only contains
/// other types that are safe to be used in shared memory, and it does not contain any
/// references or pointers.
unsafe impl PGRXSharedMemory for MonotonicityState {}

#[cfg(test)]
mod rust_tests {
    use quickcheck::{Arbitrary, Gen};

    use quickcheck_macros::quickcheck;

    use super::*;

    #[test]
    fn test_gen_monotonicity_overflow() {
        let result = Plid::gen("zzz", || 0, |_| true, |_| Err(Error::RandomOverflow));

        assert_eq!(result, Err(Error::RandomOverflow));
    }

    #[test]
    fn test_gen_high_timestamp() {
        // The largest valid timestamp is 0x0000_FFFF_FFFF_FFFF
        // +010889-08-02T05:31:50.655Z
        let date = 0x0000_FFFF_FFFF_FFFF_u64;
        let result =
            Plid::gen("zzz", || date, |_| true, |plid| Ok(plid)).expect("Should generate Plid");

        assert_eq!(result.as_timestamp_u64(), date);
        assert_eq!(result.as_prefix_bytes(), *b"zzz");
        assert_eq!(result.as_random_bits_u64(), 0);
    }

    #[test]
    fn test_map_prefix() {
        let mapped = map_prefix("cba").unwrap();
        // Top 5 bits = c = 3
        // Next 5 bits = b = 2
        // Next 5 bits = a = 1
        // Last bit reserved = 0
        assert_eq!(mapped, 0b00011_00010_00001_0);

        let mapped = map_prefix("zzz").unwrap();
        // Top 5 bits = c = 26
        // Next 5 bits = b = 26
        // Next 5 bits = a = 26
        // Last bit reserved = 0
        assert_eq!(mapped, 0b11010_11010_11010_0);
    }

    #[test]
    fn test_plid_display() {
        let plid = Plid(0x1882_019b1a078508_5b39ca05003e1307);
        assert_eq!(plid.to_string(), "cba_06DHM1W511DKKJG500Z161R");

        let plid = super::Plid(0x1880_019b1a078508_5b39ca05003e1307);
        assert_eq!(plid.to_string(), "cb_06DHM1W511DKKJG500Z161R");

        let plid = super::Plid(0x1800_019b1a078508_5b39ca05003e1307);
        assert_eq!(plid.to_string(), "c_06DHM1W511DKKJG500Z161R");

        let plid = super::Plid(0x0800_ffffffffffff_ffffffffffffffff);
        assert_eq!(plid.to_string(), "a_ZZZZZZZZZZZZZZZZZZZZZZR");
    }

    #[test]
    fn test_plid_parse() {
        // Time: 0x019B1A078508
        // Random: 0x5b39ca05003e1307
        // Full: 0x019B1A0785085b39ca05003e1307
        let plid = "cba_06DHM1W511DKKJG500Z161R";
        let parsed: Plid = plid.parse().unwrap();
        assert_eq!(parsed, Plid(0x1882_019b1a078508_5b39ca05003e1307));
    }

    #[test]
    fn test_plid_parse_lowercase_b32() {
        // Lowercase some of the base32 portion. Notably some uppercase letter don't parse as their
        // lowercase equivalents (e.g. 'I' and 'L' parse as '1')
        let plid = "cba_06Dhm1w511DkkjG500Z161R";
        let parsed: Plid = plid.parse().expect("Should parse lowercase base32");
        assert_eq!(parsed, Plid(0x1882_019b1a078508_5b39ca05003e1307));
    }

    #[test]
    fn test_plid_parse_disambiguated_b32() {
        // Here we replace some instances of '1' and '0' with their ambiguous counterparts
        // 'I'/'L'/'l' for '1' and 'O' for '0
        let plid = "cba_06DHMlW5ILDKKJG5OoZ161R";
        let parse: Plid = plid.parse().expect("Should parse lowercase base32");
        assert_eq!(parse, Plid(0x1882_019b1a078508_5b39ca05003e1307));
    }

    #[test]
    fn test_plid_parse_too_short() {
        // We lost two characters from the base32 portion
        let plid = "cba_06DHM1W511DKKJG500Z16";
        let result = plid.parse::<Plid>();
        assert_eq!(result, Err(Error::InvalidIdPortion { length: 21 }));
    }

    #[test]
    fn test_plid_parse_too_long() {
        // We lost two characters from the base32 portion
        let plid = "cba_06DHM1W511DKKJG500Z161RHM";
        let result = plid.parse::<Plid>();
        assert_eq!(result, Err(Error::InvalidIdPortion { length: 25 }));
    }

    #[test]
    fn test_plid_parse_invalid_base32() {
        let plid = "cba_06DHM1W511@KKJG500Z161R";
        let result = plid.parse::<Plid>();
        assert_eq!(
            result,
            Err(Error::DecodeError(base32::DecodeError::InvalidCharacter {
                at: 10,
                character: '@'
            }))
        );
    }

    #[test]
    fn test_plid_parse_uppercase_prefix() {
        let plid = "ABZ_06DHM1W511DKKJG500Z161R";
        let parsed: Plid = plid.parse().expect("Should parse uppercase prefix");
        assert_eq!(parsed, Plid(0x08B4_019b1a078508_5b39ca05003e1307));
    }

    #[test]
    fn test_plid_parse_no_prefix() {
        let plid = "_06DHM1W511DKKJG500Z161R";
        let result = plid.parse::<Plid>();
        assert_eq!(result, Err(Error::PrefixTooShort));
    }

    #[test]
    fn test_plid_parse_no_nil_prefix() {
        let plid = "\0_06DHM1W511DKKJG500Z161R";
        let result = plid.parse::<Plid>();
        assert_eq!(
            result,
            Err(Error::InvalidPrefixCharacter {
                at: 0,
                character: '\0'
            })
        );
    }

    #[test]
    fn test_plid_parse_too_long_prefix() {
        let plid = "aaaa_06DHM1W511DKKJG500Z161R";
        let result = plid.parse::<Plid>();
        assert_eq!(result, Err(Error::PrefixTooLong { length: 4 }));
    }

    #[test]
    fn test_plid_parse_invalid_prefix() {
        let plid = "aa0_06DHM1W511DKKJG500Z161R";
        let result = plid.parse::<Plid>();
        assert_eq!(
            result,
            Err(Error::InvalidPrefixCharacter {
                at: 2,
                character: '0'
            })
        );
    }

    #[test]
    fn test_timestamp_extraction() {
        let plid = Plid(0x4304_019b1a078508_5b39ca05003e1307);
        let duration_since_epoch = plid.as_duration_since_epoch();
        assert_eq!(duration_since_epoch.as_millis(), 0x019B1A078508);
    }

    #[test]
    fn test_less_than_prefix_length() {
        // Because the prefix bits are the highest order bits, they should determine
        // the ordering first.
        // In lhs: we have prefix 'u' (21) and then all zero bits for the rest of the prefix. This
        // yields the prefix D800
        // In rhs: we have prefix 'ua' (21, 1) and then a zero bit for the rest of the prefix. This
        // yields the prefix D801
        let lhs = "u_06DJJV74BMNW0KXF1CVTWZ0".parse::<Plid>().unwrap();
        let rhs = "ua_06DJJV74BMNW0KXF1CVTWZ0".parse::<Plid>().unwrap();
        assert!(lhs < rhs);
    }

    #[quickcheck]
    fn prop_plid_sorting_matches_string_sorting(plid1: Plid, plid2: Plid) -> bool {
        let str1 = plid1.to_string();
        let str2 = plid2.to_string();

        let ord_plid = plid1.cmp(&plid2);
        let ord_str = str1.cmp(&str2);

        ord_plid == ord_str
    }

    #[quickcheck]
    fn prop_plid_prefix_matches(prefix: ArbitraryPrefix) -> bool {
        let plid = Plid::gen(&prefix.0, || 0, |_| true, |p| Ok(p))
            .expect("Plid generation should not fail");

        let prefix_bytes = plid.as_prefix_bytes();
        let prefix_str = prefix_bytes_as_str(&prefix_bytes);

        prefix_str == prefix.0
    }

    static ASCII_LOWERCASE: &[u8] = b"abcdefghijklmnopqrstuvwxyz";

    impl Arbitrary for Plid {
        fn arbitrary(g: &mut Gen) -> Self {
            let prefix = ArbitraryPrefix::arbitrary(g);
            let time = u64::arbitrary(g) & TIME_MASK; // Ensure time fits in 48 bits
            let random: u64 = u64::arbitrary(g);
            Plid::gen(
                &prefix.0,
                || time,
                |bytes| {
                    bytes[..8].copy_from_slice(&random.to_ne_bytes());
                    true
                },
                |p| Ok(p),
            )
            .expect("Arbitrary Plid generation should not fail")
        }
    }

    #[derive(Debug, Clone)]
    struct ArbitraryPrefix(String);

    impl Arbitrary for ArbitraryPrefix {
        fn arbitrary(g: &mut Gen) -> Self {
            let prefix_len = u8::arbitrary(g) % 3 + 1; // 1 to 3
            let prefix: String = (0..prefix_len)
                .map(|_| {
                    let c = g.choose(ASCII_LOWERCASE).copied().unwrap();
                    c as char
                })
                .collect();
            ArbitraryPrefix(prefix)
        }
    }
}

#[cfg(any(test, feature = "pg_test"))]
#[pg_schema]
mod tests {
    use super::*;

    #[pg_test]
    fn test_gen_plid() {
        // Can generate a plid with prefix "abc"
        Spi::run("SELECT gen_plid('abc');").expect("gen_plid to not fail");
    }

    #[pg_test]
    fn test_cast_to_plid_no_panic() {
        // Can parse a plid with prefix "u"
        Spi::run("SELECT 'u_06DJJM4MJJAG72678PDJX30'::plid;").expect("plid cast to not fail");
    }

    #[pg_test]
    fn test_cast_to_plid() {
        // Can generate a plid with prefix "abc"
        let plid: BoxedPlid = Spi::get_one("SELECT 'c_06DHM1W511DKKJG500Z161R'::plid;")
            .expect("plid cast to not fail")
            .expect("plid not null");
        assert_eq!(*plid, Plid(0x1800_019b1a078508_5b39ca05003e1307));
    }

    #[pg_test]
    fn test_plid_to_prefix() {
        let prefix: String =
            Spi::get_one("SELECT plid_to_prefix('c_06DHM1W511DKKJG500Z161R'::plid);")
                .expect("plid_to_prefix to not fail")
                .expect("prefix not null");
        assert_eq!(&prefix, "c");

        let prefix: String =
            Spi::get_one("SELECT plid_to_prefix('ac_06DHM1W511DKKJG500Z161R'::plid);")
                .expect("plid_to_prefix to not fail")
                .expect("prefix not null");
        assert_eq!(&prefix, "ac");
    }

    #[pg_test]
    fn test_plid_to_timestamptz() {
        // Time component is: 2025-12-13T23:24:19.080Z
        let expected_timestamp =
            TimestampWithTimeZone::with_timezone(2025, 12, 13, 23, 24, 19.080, "UTC")
                .expect("valid timestamp");
        let timestamp: TimestampWithTimeZone =
            Spi::get_one("SELECT plid_to_timestamptz('c_06DHM1W511DKKJG500Z161R'::plid);")
                .expect("plid_to_timestamptz to not fail")
                .expect("timestamp not null");
        assert_eq!(timestamp, expected_timestamp);
    }

    #[pg_test]
    fn test_plid_is_16_bytes() {
        let length: i32 = Spi::get_one("SELECT pg_column_size('c_06DHM1W511DKKJG500Z161R'::plid);")
            .expect("pg_column_size to not fail")
            .expect("length not null");
        assert_eq!(length, 16);
    }

    #[pg_test]
    fn test_plid_as_primary_key() {
        // This verifies that plid can be used as a primary key in a table.
        // Implicitly this verifies that the btree operator class works.
        Spi::run(
            "
            CREATE TABLE test_plid_pk (
                id plid PRIMARY KEY,
                value TEXT
            );
            ",
        )
        .expect("Create table with plid primary key to not fail");

        Spi::run(
            "
            INSERT INTO test_plid_pk (id, value)
            VALUES ('a_06DHM1W511DKKJG500Z161R'::plid, 'test value');
            ",
        )
        .expect("Insert into table with plid primary key to not fail");

        let value: String = Spi::get_one(
            "
            SELECT value FROM test_plid_pk
            WHERE id = 'a_06DHM1W511DKKJG500Z161R'::plid;
            ",
        )
        .expect("Select from table with plid primary key to not fail")
        .expect("value not null");

        assert_eq!(&value, "test value");
    }

    #[pg_test]
    #[should_panic(expected = "invalid input syntax for type plid")]
    fn test_cast_to_plid_empty_string() {
        let _ = Spi::run("SELECT ''::plid;");
    }

    #[pg_test]
    #[should_panic(expected = "invalid input syntax for type plid")]
    fn test_cast_to_plid_missing_prefix() {
        let _ = Spi::run("SELECT '06DHM1W511DKKJG500Z161R'::plid;");
    }

    #[pg_test]
    #[should_panic(expected = "invalid input syntax for type plid")]
    fn test_cast_to_too_long_prefix() {
        let _ = Spi::run("SELECT 'aaaa_06DHM1W511DKKJG500Z161R'::plid;");
    }

    #[pg_test]
    #[should_panic(expected = "invalid input syntax for type plid")]
    fn test_cast_to_invalid_characters_in_prefix() {
        let _ = Spi::run("SELECT 'aaä_06DHM1W511DKKJG500Z161R'::plid;");
    }
}

/// This module is required by `cargo pgrx test` invocations.
/// It must be visible at the root of your extension crate.
#[cfg(test)]
pub mod pg_test {
    pub fn setup(_options: Vec<&str>) {
        // perform one-off initialization when the pg_test framework starts
    }

    #[must_use]
    pub fn postgresql_conf_options() -> Vec<&'static str> {
        // return any postgresql.conf settings that are required for your tests
        vec!["shared_preload_libraries = 'plid'"]
    }
}

use core::fmt;
use std::fmt::Write as _;

pub struct Base32Encoder<'b> {
    bytes: &'b [u8],
}

#[derive(Debug, PartialEq, Eq)]
pub enum DecodeError {
    InvalidCharacter { at: usize, character: char },
    OutputTooSmall,
}

// Decode table indexed by (byte - b'0')
// Covers '0' (48) through 'z' (122), so 122 - 48 + 1 = 75 elements
const DECODE: [u8; 75] = [
    0,   // '0' (48)
    1,   // '1' (49)
    2,   // '2' (50)
    3,   // '3' (51)
    4,   // '4' (52)
    5,   // '5' (53)
    6,   // '6' (54)
    7,   // '7' (55)
    8,   // '8' (56)
    9,   // '9' (57)
    255, // ':' (58) - invalid
    255, // ';' (59) - invalid
    255, // '<' (60) - invalid
    255, // '=' (61) - invalid
    255, // '>' (62) - invalid
    255, // '?' (63) - invalid
    255, // '@' (64) - invalid
    10,  // 'A' (65)
    11,  // 'B' (66)
    12,  // 'C' (67)
    13,  // 'D' (68)
    14,  // 'E' (69)
    15,  // 'F' (70)
    16,  // 'G' (71)
    17,  // 'H' (72)
    1,   // 'I' (73) -> 1
    18,  // 'J' (74)
    19,  // 'K' (75)
    1,   // 'L' (76) -> 1
    20,  // 'M' (77)
    21,  // 'N' (78)
    0,   // 'O' (79) -> 0
    22,  // 'P' (80)
    23,  // 'Q' (81)
    24,  // 'R' (82)
    25,  // 'S' (83)
    26,  // 'T' (84)
    255, // 'U' (85) - invalid
    27,  // 'V' (86)
    28,  // 'W' (87)
    29,  // 'X' (88)
    30,  // 'Y' (89)
    31,  // 'Z' (90)
    255, // '[' (91) - invalid
    255, // '\' (92) - invalid
    255, // ']' (93) - invalid
    255, // '^' (94) - invalid
    255, // '_' (95) - invalid
    255, // '`' (96) - invalid
    10,  // 'a' (97)
    11,  // 'b' (98)
    12,  // 'c' (99)
    13,  // 'd' (100)
    14,  // 'e' (101)
    15,  // 'f' (102)
    16,  // 'g' (103)
    17,  // 'h' (104)
    1,   // 'i' (105) -> 1
    18,  // 'j' (106)
    19,  // 'k' (107)
    1,   // 'l' (108) -> 1
    20,  // 'm' (109)
    21,  // 'n' (110)
    0,   // 'o' (111) -> 0
    22,  // 'p' (112)
    23,  // 'q' (113)
    24,  // 'r' (114)
    25,  // 's' (115)
    26,  // 't' (116)
    255, // 'u' (117) - invalid
    27,  // 'v' (118)
    28,  // 'w' (119)
    29,  // 'x' (120)
    30,  // 'y' (121)
    31,  // 'z' (122)
];

pub fn decode(s: &str, out: &mut [u8]) -> Result<(), DecodeError> {
    let mut bits = 0u32;
    let mut bit_count = 0;
    let mut out_index = 0;

    for (i, c) in s.bytes().enumerate() {
        if !(b'0'..=b'z').contains(&c) {
            return Err(DecodeError::InvalidCharacter {
                at: i,
                character: c as char,
            });
        }
        let val = DECODE[(c - b'0') as usize];
        if val == 255 {
            return Err(DecodeError::InvalidCharacter {
                at: i,
                character: c as char,
            });
        }

        bits = (bits << 5) | (val as u32);
        bit_count += 5;

        while bit_count >= 8 {
            bit_count -= 8;
            if out_index >= out.len() {
                return Err(DecodeError::OutputTooSmall);
            }
            out[out_index] = ((bits >> bit_count) & 0xFF) as u8;
            out_index += 1;
        }
    }

    Ok(())
}

impl fmt::Display for Base32Encoder<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        const BASE32_ALPHABET: &[u8; 32] = b"0123456789ABCDEFGHJKMNPQRSTVWXYZ"; // Crockford's base32

        let mut bits = 0u32;
        let mut bit_count = 0;

        for &byte in self.bytes {
            bits = (bits << 8) | (byte as u32);
            bit_count += 8;

            while bit_count >= 5 {
                bit_count -= 5;
                let index = ((bits >> bit_count) & 0x1F) as usize;
                f.write_char(BASE32_ALPHABET[index] as char)?;
            }
        }

        if bit_count > 0 {
            bits <<= 5 - bit_count;
            let index = (bits & 0x1F) as usize;
            f.write_char(BASE32_ALPHABET[index] as char)?;
        }

        Ok(())
    }
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::InvalidCharacter { at, character } => {
                write!(f, "Invalid character '{}' at position {}", character, at)
            }
            DecodeError::OutputTooSmall => write!(f, "Output buffer is too small"),
        }
    }
}

impl<'b> From<&'b [u8]> for Base32Encoder<'b> {
    fn from(bytes: &'b [u8]) -> Self {
        Base32Encoder { bytes }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_base32_encode() {
        let data = b"The quick brown fox jumps over the lazy dog.";
        let encoder = Base32Encoder::from(data.as_slice());
        let encoded = format!("{}", encoder);
        assert_eq!(
            encoded,
            "AHM6A83HENMP6TS0C9S6YXVE41K6YY10D9TPTW3K41QQCSBJ41T6GS90DHGQMY90CHQPEBG"
        );
    }

    #[test]
    fn test_base_32_symmetry() {
        let data = b"Hello, World!";
        let encoder = Base32Encoder::from(data.as_slice());
        let encoded = format!("{}", encoder);

        let mut decoded = vec![0u8; data.len()];
        decode(&encoded, &mut decoded).unwrap();

        assert_eq!(data.as_slice(), decoded.as_slice());
    }

    #[ignore]
    #[test]
    fn test_base_32_symmetry_fuzz() {
        use rand::prelude::*;

        let mut rng = rand::rng();
        let mut bytes: [u8; 32768] = [0; 32768];
        loop {
            let len = rng.random::<u64>() % 100;
            rng.fill(&mut bytes[..len as usize]);

            let data = &bytes[..len as usize];

            let encoder = Base32Encoder::from(data);
            let encoded = format!("{}", encoder);

            let mut decoded = vec![0u8; data.len()];
            decode(&encoded, &mut decoded).unwrap();

            assert_eq!(data, decoded.as_slice());
        }
    }
}

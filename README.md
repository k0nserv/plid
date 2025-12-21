# plid

[ulid][ulid-spec]-inspired ID type with prefix that fits in 128 bits.

* 128 bits in total.
* 16 bits for prefix, 1-3 characters long `a-z`.
* 48 bits for timestamp (milliseconds since Unix epoch).
* 64 bits for randomness.
* String representation is at most 27 characters long and at least 25
  characters long (depending on prefix length).
* Lexicographically sortable like ULID.
* Numeric sorting matches lexicographic sorting.
* Uses Crockford's Base32 encoding like ULID.
* Case insensitive like ULID.
* Double click to select the entire ID in most contexts.
* Optional monotonic counter within the same millisecond like ULID.

Generate a PLID with prefix `usr`:

```text
-- Generate a PLID with prefix 'usr'
SELECT gen_plid('usr') AS user_id;
           user_id
-----------------------------
 usr_06DJX8T67BP71A4MYW9VXNR
(1 row)
```

## State of this project

I wrote this mostly as an exercise to learn more about authoring Postgres extensions and learning about Postgres internals. I have not used in a production system myself. That said it is feature complete and has good test coverage.

## Installation

Use `pgrx` to build and install the extension. Follow their [instructions](https://github.com/pgcentralfoundation/pgrx/blob/master/cargo-pgrx/README.md#installing-your-extension-locally).

This extensions uses shared memory to maintain state for monotonic ID generation. You need to add the following line to your `postgresql.conf` file:

```text
shared_preload_libraries = 'plid'
```



## Usage 

```sql
-- Generate a PLID with prefix 'usr'
SELECT gen_plid('usr') AS user_id;
```

<details>
<summary>Output</summary>

```text
           user_id
-----------------------------
 usr_06DKQTMAVXMQ5RAYYSMJCD0
(1 row)
```

</details>

```sql
-- Generate a PLID with prefix 'usr' and monotonicity enabled
-- Randomness increments within the same millisecond to preserve ordering
SELECT gen_plid_monotonic('usr') AS user_id;
```

<details>
<summary>Output</summary>

```text
           user_id
-----------------------------
 usr_06DKQTNW858RVRQFRMFBBP0
(1 row)
```

</details>

```sql
-- Create a table with a PLID primary key
CREATE TABLE users (
    id plid PRIMARY KEY DEFAULT gen_plid_monotonic('usr'),
    name TEXT NOT NULL
);
```

```sql
-- Cast a string to plid
SELECT 'usr_06DJX8T67BP71A4MYW9VXNR'::plid AS user_id;
```

<details>
<summary>Output</summary>

```text
           user_id
-----------------------------
 usr_06DJX8T67BP71A4MYW9VXNR
(1 row)
```

</details>

```sql
-- Cast a string with mixed case to plid
SELECT 'uSR_06DK5gkRYA7Z7X49zS28R10'::plid;
```

<details>
<summary>Output</summary>

```text
            plid
-----------------------------
 usr_06DK5GKRYA7Z7X49ZS28R10
(1 row)
```

</details>

```sql
-- Extract timestamptz from a plid
SELECT plid_to_timestamptz('usr_06DJX8T67BP71A4MYW9VXNR') AS ts;
```

<details>
<summary>Output</summary>

```text
             ts
----------------------------
 2025-12-17 23:26:50.938+00
(1 row)
```

</details>

```sql
-- Turn a timestamptz into a plid with prefix 'usr'.
-- The random bits are all set to 1.
-- This is useful for range queries based on timestamp.
SELECT timestamptz_to_plid('2025-12-21T13:37:00Z', 'usr') AS plid;
```

<details>
<summary>Output</summary>

```text
            plid
-----------------------------
 usr_06DM285GC3ZZZZZZZZZZZZR
(1 row)
```

</details>

## Performance

Performance is about on par with Postgres's native UUID v7 implementation.

These comparison were ran on Postgres 18 on a Macbook Pro M1 Max.

<details>

<summary>Generate one million ids</summary>

```text
plid=# EXPLAIN ANALYZE SELECT gen_plid_monotonic('usr') FROM generate_series(1, 1000000);
                                                               QUERY PLAN
----------------------------------------------------------------------------------------------------------------------------------------
 Function Scan on generate_series  (cost=0.00..12500.00 rows=1000000 width=16) (actual time=113.870..11945.202 rows=1000000.00 loops=1)
   Buffers: temp read=1709 written=1709
 Planning Time: 0.295 ms
 Execution Time: 11974.366 ms
(4 rows)

plid=# EXPLAIN ANALYZE SELECT gen_plid('usr') FROM generate_series(1, 1000000);
                                                               QUERY PLAN
----------------------------------------------------------------------------------------------------------------------------------------
 Function Scan on generate_series  (cost=0.00..12500.00 rows=1000000 width=16) (actual time=100.528..11946.489 rows=1000000.00 loops=1)
   Buffers: temp read=1709 written=1709
 Planning Time: 0.052 ms
 Execution Time: 11977.537 ms
(4 rows)

plid=# EXPLAIN ANALYZE SELECT uuidv7() FROM generate_series(1, 1000000);
                                                               QUERY PLAN
----------------------------------------------------------------------------------------------------------------------------------------
 Function Scan on generate_series  (cost=0.00..12500.00 rows=1000000 width=16) (actual time=102.687..11719.179 rows=1000000.00 loops=1)
   Buffers: temp read=1709 written=1709
 Planning Time: 0.048 ms
 Execution Time: 11747.149 ms
(4 rows)

plid=# EXPLAIN ANALYZE SELECT uuidv4() FROM generate_series(1, 1000000);
                                                               QUERY PLAN
----------------------------------------------------------------------------------------------------------------------------------------
 Function Scan on generate_series  (cost=0.00..12500.00 rows=1000000 width=16) (actual time=102.711..12073.273 rows=1000000.00 loops=1)
   Buffers: temp read=1709 written=1709
 Planning Time: 0.053 ms
 Execution Time: 12101.747 ms
(4 rows)
```

</details>

## Binary Representation

```text
0                   1                   2                   3
0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|         prefix              |0|      timestamp first 16 bits  |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                     timestamp last 32 bits                    |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      64 bits  of random data                  |
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

The prefix represents at most 3 characters, each character taking 5 bits, with the last bit of
the 16 first bit reserved (set to 0). This allows for prefixes of length 1-3 characters.
The prefix numbering is 'a' = 1, 'b' = 2, ..., 'z' = 26.

Prefix encoding:

```text
0                   1
0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|F F F F F S S S S S T T T T T|0|
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

The `F` bits represent the first character of the prefix, the `S` bits represent the second, and the `T` bits represent the third. The last bit is always 0.

Values for the 5 bit chunks larger than 26 are reserved and should not be used.



### String Representation

The string representation is similar to ULID, with the addition of the prefix and an underscore `_`
separating the prefix from the rest of the ID.

### Encoding


The string representation is constructed as follows:

1. Encode the prefix (1-3 characters) as ASCII lowercase letters `a-z`. If a prefix group is 0 it and the remainder of the prefix is omitted. There must be at least one character in the prefix.
2. Append an underscore `_`.
3. Encode the remaining 112 bits (14 bytes) using Crockford's Base32 encoding. Use big-endian byte order.

### Decoding

To decode a PLID string representation back to its binary form:

1. Split the string at the underscore `_` to separate the prefix from the encoded part. Error if there is no underscore or if the prefix is empty.
2. Decode the prefix characters back to their 5-bit representation error on invalid characters and ensure the prefix length is between 1 and 3 characters.
3. Decode the remaining part using Crockford's Base32 decoding to get the 112 bits (14 bytes) in big endian byte order. Skip the last 2 bit from the last character for example `ZZZZZZZZZZZZZZZZZZZZZZZ` decodes to `ffffffffffffffffffffffffffff`.


## Todo

Things that still need to be done:

- [ ] Get rid of last allocation in Rust for `plid_send` by directly constructing a bytea.
- [ ] Add some proper benchmarks.
- [ ] Hash index support.

## Inspiration

This project was inspired by [ULID][ulid-spec]. I also took inspiration from [pgrx-ulid][pgrx-ulid] which is a Postgres extension that implements ULID in Rust using the pgrx framework.


[ulid-spec]: https://github.com/ulid/spec
[pgrx-ulid]: https://github.com/pksunkara/pgx_ulid

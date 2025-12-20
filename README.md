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

```sql
plid=# SELECT gen_plid('usr') AS user_id;
           user_id
-----------------------------
 usr_06DJX8T67BP71A4MYW9VXNR
(1 row)
```

## State of this project

I wrote this mostly as an exercise to learn more about authoring Postgres extensions and learning about Postgres internals. I have not used in a production system myself. That said it is feature complete and has good test coverage.

## Usage 

```sql
# Generate a PLID with prefix 'usr'
SELECT gen_plid('usr') AS user_id;
```

```sql
# Generate a PLID with prefix 'usr' and monotonicity enabled
# If two PLIDs are generated within the same millisecond, the
# randomness part will be incremented to ensure uniqueness and ordering.
SELECT gen_plid_monotonic('usr') AS user_id;
```

```sql
# Create a table with a PLID primary key
CREATE TABLE users (
    id plid PRIMARY KEY DEFAULT gen_plid_monotonic('usr'),
    name TEXT NOT NULL
);
```

```sql
# Cast a string to plid
SELECT 'usr_06DJX8T67BP71A4MYW9VXNR'::plid AS user_id;
```

## Performance

Performance is about on par with Postgres's native UUID v7 implementation.

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

## Inspiration

This project was inspired by [ULID][ulid-spec]. I also took inspiration from [pgrx-ulid][pgrx-ulid] which is a Postgres extension that implements ULID in Rust using the pgrx framework.


[ulid-spec]: https://github.com/ulid/spec
[pgrx-ulid]: https://github.com/pksunkara/pgx_ulid

#!/usr/bin/env python3
"""Checks that build archives are named by the hash of their content.

    lake-hash.py FILE...

Lake stores a build output under the hash of its bytes, 16 hex digits, and
refuses a download whose bytes hash to something else. The workflow
cache-upload runs this over the archives that a run of CI staged, before it
uploads any: a file whose name does not start with its hash is reported and
the script exits with 1. So the bucket never holds an archive under a name
that is not its own, whatever a build handed over.

Lake's hash of a file (`Hash.ofByteArray` in Lake/Build/Trace.lean) is
`mixHash 1723 (hash bytes)`: `hash` of a byte array is MurmurHash64A with
seed 11, and `mixHash` is `lean_uint64_mix_hash`, both from Lean's runtime.
If a new toolchain changes it, every archive fails this check and nothing is
uploaded; the builds go on without the bucket.
"""
import os, struct, sys

M = 0xC6A4A7935BD1E995
R = 47
MASK = (1 << 64) - 1


def murmur64a(data, seed=11):
    n = len(data)
    h = (seed ^ (n * M)) & MASK
    for (k,) in struct.iter_unpack("<Q", data[: n // 8 * 8]):
        k = (k * M) & MASK
        k ^= k >> R
        k = (k * M) & MASK
        h ^= k
        h = (h * M) & MASK
    tail = data[n // 8 * 8 :]
    if tail:
        h ^= int.from_bytes(tail, "little")
        h = (h * M) & MASK
    h ^= h >> R
    h = (h * M) & MASK
    h ^= h >> R
    return h


def mix(h, k):
    k = (k * M) & MASK
    k ^= k >> R
    k ^= M
    h ^= k
    return (h * M) & MASK


def lake_hash(data):
    return "%016x" % mix(1723, murmur64a(data))


if __name__ == "__main__":
    bad = 0
    for path in sys.argv[1:]:
        with open(path, "rb") as f:
            h = lake_hash(f.read())
        if os.path.basename(path).split(".")[0] != h:
            print("%s: content hashes to %s" % (path, h), file=sys.stderr)
            bad = 1
    sys.exit(bad)

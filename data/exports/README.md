# Self-containment artifacts (temporary home)

One directory per registered source: the per-module exports Gate 2 reads
(`<module>.ndjson`: the library's own declarations, elaborated, proofs dropped),
the closures (`<module>.names.json`) and the notation-expanded sources
(`<module>.expanded.lean`). Produced once per library by `scripts/setup-source.mjs`
from the source's own toolchain and build, then the build is deleted.

They live here so any checkout of this app can translate those libraries without
building them. This is not their right home: they are tentative, self-contained
theorem data, and belong next to the tentative records in the Tengoku tree. They
will move once that has a place for them.

Libraries whose exports were produced before proof terms were dropped from
theorems are not committed until re-exported (their files are several times larger).

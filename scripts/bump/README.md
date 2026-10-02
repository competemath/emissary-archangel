# Bump: translating a whole library the way Mathlib moves to a new Lean

The per-theorem pipeline (`translate*.yml`, `queue-server.mjs`, the bridge's `recurseOneEntry`) compiles a synthetic file per
theorem on Leak IV and runs Gate 2 (≈90 s of import plus the original's export parse) per theorem. No mathematics happens in
that time; it is repeated set-up. Mathlib does not move that way: it builds everything, reads what the compiler reports,
applies the fixes the compiler names (`scripts/fix_deprecations.py`), and bumps one release at a time. This directory is the
same shape for a library left behind. Everything runs on GitHub runners, with no Claude and no Leak.

```
 library @ its commit ──retarget──▶ Mathlib release(s) ──tolerant build──▶ repair ◀─┐
                                          │                  │ errors ───────────────┘ (rounds)
                                          │                  ▼
                                          │          portfolio (proofs only)
                                          ▼                  │
                                   batched Gate 2 ◀──────────┘     one Lean process, every declaration
                                          │
                                  records + ledger rows ──▶ bank (bank-flush.mjs ▶ tengoku staging PRs ▶ the tree's build gate)
```

| step | file | what it does |
|---|---|---|
| plan | `plan_chain.py` | `chain=auto`: the Mathlib releases to go through (≤ `step` Lean minors apart), so each deprecated alias is rewritten while it exists (they are deleted after ~6 months). `chain=direct`: one jump. |
| imports | `engine.py normalize-imports` | `imports=full` (default): every Mathlib/Batteries/Aesop/Qq/ProofWidgets import becomes the umbrella imports. That is the environment a record is verified in (the tree holds all of them, a record's own imports are stripped), so moved/split/merged Mathlib modules stop mattering. `imports=minimal`: keep the imports and repair them with `mine_moves.py`. |
| build | `tolerant_build.py`, `TolerantBuild.lean` | Every `.lean` file under the roots, in import order, N at a time, cached by source + dependency olean hashes. `lean -o` writes no `.olean` when a file has an error, so `lake build` blocks the module and everything downstream; the driver is `runFrontend` cut where it drops the environment, and writes it. A failing declaration then stands on `sorryAx` (or is absent) and costs only itself. |
| repair | `engine.py repair` | Mathlib's `fix_deprecations.py` algorithm over our own log (positions, not `lake build --no-build`); a file whose replaced import proved insufficient falls back to `import Mathlib`. Every repair is checked by the next build. |
| portfolio | `portfolio.py` | A theorem whose proof failed (and nothing else about it) gets its proof replaced by `first | grind | simp_all | aesop | omega | …`. The header is never touched. |
| Gate 2 | `gate2_batch.py` | See below. One Lean process imports every built module and checks every ledger declaration, the original's export parsed once per module. |
| records | `records.py`, `stage-records.mjs`, `ledger_rows.py` | The exact dependency closure of each passed theorem (from the environment) and each declaration's source range give the record's `context` in the shape `generate.py` parses; `lib/stage-record.mjs` makes the record; ledger rows say `bump`. |

## What is guaranteed, and by what

A declaration is reported as translated only if ALL of these hold; none of them is trusted from a repair step.

1. **It is a real proof.** Its axioms are a subset of `propext`, `Classical.choice`, `Quot.sound` (`collectAxioms`): nothing that failed in the tolerant build, and nothing built on something that failed, passes (`uses_sorry`, `nonstandard_axiom`). The kernel checked the proof when the declaration was added.
2. **Its statement entails the original's.** Either the two types are structurally equal (`via=equal`), or the bridge `fun h => h : NewType → OldType` is accepted by the kernel (`via=entails`), after replaying the original's statement closure from the committed export. Gate 2's own Lean code (`gate2/server.py` `_HEADER`) is used, not a copy.
3. **The library definitions the statement is built on mean what they meant.** Identical type and value, or the kernel accepts `c = c._gate2old` by `Eq.refl` with the original definition (and the original library definitions it is built from, theorems as statement-only axioms) replayed beside the native one: exactly definitional equality. The per-theorem Gate 2 compares a definition by TYPE only, so a definition whose body changed meaning with the same type was never noticed there; here it is `name_collision`.
4. **The checker is not vacuous.** `--controls N` also checks pairs of unrelated declarations; every one must FAIL.
5. **The repaired text is allowed to change only how the source is read, never what a statement says**: imports, call-site names Lean itself names as replacements, proofs. A change that did alter a statement shows up in 2/3.

Not guaranteed (by design, as before): the meaning of a *Mathlib* constant is whatever the target Mathlib says. A statement about `Real.sqrt` is translated to the current `Real.sqrt`; Gate 2 holds Mathlib names to type-compatibility only, since Mathlib is the foundation the tree is built on.

The last gate is the one every record always had: the tree's build (`promote.py`, the merge queue). A record that passes everything here and does not build in the tree is a pruning problem in `records.py`, not an unsound translation.

## Run it

```
gh workflow run bump-library.yml -R competemath/emissary-archangel -f key=leray-hopf [-f chain=auto] [-f imports=minimal] [-f portfolio=off]
```
Artifacts: `build-*.log`, `tb-*.json` (per-module state), `pass-*.json`, `repair-*.json`, `portfolio-*.json`, `repairs.patch` (every source edit), `gate2.log`, `gate2-results.json` (verdicts by pipeline outcome, controls, definitions), `passed.json`, `composed.jsonl`, `bank.jsonl`, `ledger-rows.jsonl`.
`tolerant-smoke.yml` proves the tolerant build on a toy project, and runs the unit tests (`scripts/bump/tests/`).

Nothing commits to `data/bank` or the ledger yet: `bank-flush.mjs` opens tengoku PRs for every banked record, and each needs approval.

## From a verified library to the tree (the intake lane)

Per-theorem records cannot carry this volume: a record repeats its whole context (33 KB each on average: 600 MB per 17.6k records, about
4 GB for the registered corpus). A library goes to the tree as a **bundle**: its Lean modules, each ONCE, cut down to what the factory verified.

| step | file |
|---|---|
| plan a big library into dependency-closed shards (a module goes to the shard that already builds most of what it imports) | `plan_shards.py`, `import_graph.py` (measured cost: `library-graphs.yml`) |
| one shard: build its closure, repair, batched Gate 2 for its targets, the constants its passed theorems are made of | `bump-shard.yml` (called by `bump-sharded.yml`), `shard_pack.py` |
| the bundle: keep every declaration in the closure of the passed theorems and all glue, drop the rest and any block Lean reported an error in, map imports to the tree, apply the tree's content lint, write the manifest | `bundle.py` (`lint/` is a pinned copy of tengoku's allow-list) |
| prove the pruned sources build clean (single-job libraries; sharded ones are built by the tree's own queue) | `bundle.py check`, `bump-library.yml` |
| one reproducible archive, attested (SLSA build provenance), `.tar.gz` for transport | `bundle_tar.py` (the same function and golden digest as tengoku's `scripts/ci/bundle_tar.py`) |
| every library, unattended, by size, within the runner capacity | `bump-all.yml`, `orchestrate.py` |
| a finished run -> an intake PR | `open_intake_pr.py` |

Two bundles per run. `strict` is tengoku's content allow-list as it is: no `notation`, `infix`, `macro` (the lint was written for records; a record never carries a
notation). `proposed` additionally allows the notation commands (`notation`, `infix`, `prefix`, `postfix`, `notation3`, `scoped`, `local`): they elaborate a term
like any other and cannot run code of the library's, and without them most libraries' statements do not read. `report.json` says what each rule costs in
theorems. Which one the tree takes is a policy decision (`vars.TENGOKU_INTAKE_LINT` in the gate).

On the tengoku side (proved in tengoku-sandbox first, then ported): class `intake` (from the factory's account only, one library, nothing else),
`scripts/ci/intake_check.py` (shape, manifest, lint, the archive rebuilt from the PR's files), `gh attestation verify` against the factory's workflows,
the queue builds the library root (no generation, no derived-files comparison) and checks axioms of every theorem as it does for every other PR.

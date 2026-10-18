# Memory intake

How theorems that Leak's Control II memory variants proved on the way to a target enter Tengoku. Nothing from memory reaches Tengoku by itself: the author nominates 3 to 10 theorems for one target, and the bundle has to pass three stages.

```
competemath.com/leak  ── Export nominated ──▶  bundle.json          (leak-memory-bundle/1, memory-intake/bundle.schema.json)
                                                   │
        node scripts/memory-intake.mjs run bundle.json --leak-iv <url>
                                                   │
   1 preflight   shape · 3–10 entries · no sorry/admit/native_decide/axiom/import/#eval · every closure compiles on Leak IV
   2 audit       ten clean-room reviewers (lib/memory-intake-rubrics.mjs); any blocking reject, or a reviewer with no usable verdict, fails
   3 stage       data/staging/target-<id>/<UTC>-001.jsonl · registration.json · jinshi-nomination.json
                                                   │
        staged in tengoku-sandbox, Jinshi runs on the nominated module, then the usual gate and promotion
```

## Where it lands: one library per target

A target is a library, `target-<id>` (`target-erdos-396`), so a target's theorems stay together, are attributed together and can be removed together.

| What | Path |
|---|---|
| staged records | `data/staging/target-erdos-396/<UTC>-NNN.jsonl` |
| trusted records, after promotion | `data/trusted/target-erdos-396.jsonl` |
| module | `Tengoku/Target/Erdos396.lean` |
| registration | a `target-erdos-396` entry in the sources file (`registration.json` is the draft) |

Records have the shape `stagingRecord` (lib/stage-record.mjs) already produces for every other library: `name`, `statement`, `proof`, `context` (the helper declarations the theorem needs, which the generator folds into the module), `status`, `library`, `source_url`, `toolchain`; the intake adds `author` (the account that ran and nominated) and `bundle` (a hash of the target and the nominated ids, so a re-export of the same set is recognisable).

## The audit

Ten read-only `claude -p` reviewers, each in a temporary directory that holds only the bundle and its `.lean` files, each returning `{verdict, summary, findings[{file,line,issue,fix,evidence}]}`. This follows Tau Ceti's review (four blocking, six advisory rubrics) with one deliberate change: generality blocks as well, and reuse is told to search Tengoku when a Leak I server is given (`--mcp-config`). The aim is that what enters is the reusable form of a result, not the instance a long run happened to need. Reviewers that return nothing usable fail the bundle (fail closed).

## Jinshi

`jinshi-nomination.json` names the module and the nominated theorems. Jinshi takes modules, runs only in the sandbox, and is advisory (exit 0), so this stage is: open the staged records as a sandbox pull request, point Jinshi at that module, read its report. It is not automated here.

## What is and is not tested

Tested (`node scripts/test-memory-intake.mjs`): the bundle checks, the banned constructs, preflight against a stub Leak IV, the verdict rules, the audit against a stub CLI (including that an unreachable CLI fails closed), staging into the existing record shape, and the command line end to end.

Not tested, because it needs things this repository does not have in CI: the real `claude` reviewers' judgement, the real Leak IV, and Jinshi. The registration entry is a draft whose fields have not been checked against the sources file's current schema. There is no workflow yet; the natural one is a manual dispatch against `competemath/tengoku-sandbox` that runs `run` and opens the staging pull request as the intake App, rehearsed in the sandbox before anything points at `competemath/tengoku`.

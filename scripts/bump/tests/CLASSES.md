# Classes of bug the factory's tests guard

Each class below cost a production run (an hour and a half to three hours of runners) at least once. The tests listed do not check the instance that was found; they check the INVARIANT of the class on
random or enumerated inputs, so the next member of the class fails in CI instead. When something new breaks in production, find its class here (or add one), then add a pattern/scenario to the test
that guards it, never only a regression test of the one instance.

| class | invariant | where it is enforced | what it cost |
|---|---|---|---|
| **absence of evidence is not evidence of absence** | a build that completed built every target, with or without a `Built` line; a module is refused only on evidence; a build that built nothing never got going and is refused | `test_classes_verify.py` (random import graphs x random logs: Evidence, NeverGotGoing) | Navier 2026-10-20: 67 modules had no line, 676 importers refused with them; 2026-10-21: toolchain download failed, an empty cut reported as success |
| **closure** | whatever ships imports only what ships; whatever is refused takes its importers with it, exactly; verdict and cut use ONE notion of importer | `test_classes_verify.py` (Closure), `test_classes_compose.py` (Closed: random DAGs, failures, aliases; oracle written independently) | Navier: 72 modules refused for an import an aliased copy took with it, 971 with importers |
| **monotone** | more evidence never removes a verified module | `test_classes_verify.py` (Monotone) | |
| **log segments** | what is appended to a build log (the second build, a repair round) never changes what the first build proves; a repaired module is judged on its round | `test_classes_verify.py` (Segments) | Navier: the ending of the second build was taken for the first's |
| **edits preserve meaning** | the text edits (fork wrap, alias, repair) leave the declarations of every module as they were, for every Lean scoping construct | `edit_corpus.py` + `bundle-keep-tests.yml` (real Lean: each pattern built original, forked, aliased; fingerprints compared); `test_edit_corpus.py` (corpus well-formed, comment-aware) | Navier: bare names through a re-opened namespace (#83), `open _root_.X` on a namespace nothing imports (#85), `open N` of a namespace declared on both sides (found by the corpus before it cost a run) |
| **a name in two worlds** | a name the forked copy and the tree both declare is the fork's wherever a wrapped file opens its namespace; the tree's is hidden exactly where the tree's module is in the file's import closure (Lean refuses to hide a name that does not exist), and nowhere else; no other name is lost | `test_classes_fork_names.py` (a model of what each `open` makes visible, on random files and hide sets; `fork_hide` against a naive closure on random import DAGs; plan -> merge -> compose bytes), `edit_corpus.py` (real Lean: the `fork_and_tree_*` patterns, hide computed from the real fingerprints and files) | Navier recut 8: `Ambiguous term Coefficients`, 24 modules refused |
| **edits are reproducible** | what the tree built is byte for byte what ships; an edit planned on the bytes of one stage is made at the stage whose bytes it was planned on | `test_classes_compose.py` (RepairLast), `tree_verify.py check` | |
| **workflow control flow** | a step that repairs and builds again repeats until a round finds nothing (bounded), repairs a module once, never plans without time to build, never empties a log for a build that does not run, leaves the last round's log for the verdicts | `test_classes_workflow_shell.py` (the real `run:` text under a fake `lake`/`date`/`elan`) | Navier: one repair round was not enough (3 more modules); a log emptied for a build that never ran refuses every importer |
| **infrastructure is not a result** | a transient error (toolchain download) is retried, never read as a verdict | `test_classes_workflow_shell.py` (ToolchainRetry), `test_classes_verify.py` (NeverGotGoing) | 17 minutes and a silent empty cut |
| **memory/time budgets of Gate 2** | a module that cannot be judged does not eat the budget of the ones that can | `test_gate2_driver.py` (skip list, guard poll interval) | Navier: 168 modules unjudged, most of them only because a time budget ran out |

KNOWN GAPS (the failure is an honest refusal, never a wrong ship): `open N (a b)`, `open N hiding x` and `open N renaming a → b` are not rewritten, so a name found only in the tree's N through them is not found;
`open … in` inside a term or a tactic block is not a line-start command and is not rewritten; a name the fork and the tree both declare and a THIRD module of the closure declares too is not hidden.

How to add to a class: a new Lean construct -> a `Pattern` in `edit_corpus.py` (it is built by real Lean in CI, nothing else to write); a new log shape -> a generator branch in `Lib.log` of
`test_classes_verify.py`; a new step with a loop -> a scenario in `test_classes_workflow_shell.py` (a module kind in the fake lake: marker line + behaviour); a new way to drop or edit modules in compose ->
an extra argument in `Case.compose` of `test_classes_compose.py` and the invariants already check it.

Mutation check: after writing a class test, break the code the way the old bug did and see the test fail (the commit messages of the PRs that introduced these tests list the mutants tried).

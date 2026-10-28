A COPY of tengoku's content lint (the allow-list: what Lean text the tree may compile), taken from competemath/tengoku PR #247 (branch intake-class,
which brings the allow-list to the library's main; before that it was the copy in competemath/tengoku-sandbox). The factory uses it to decide
which modules of a bundle the tree would accept, and to say how many theorems each rule costs. Tengoku's gate runs its own copy; this
one decides nothing there. Refresh by copying the four files again (allowlist.py, allowed-options.json, lean_lex.py and command-keywords.json: the keywords of the
tree's Lean, schemas/command-keywords.json in tengoku, which the exact column-0 rule reads).

2026-10-18: the copy has `unscoped_violations` as well (tengoku scripts/ci/allowlist.py): a notation, `macro` or `syntax` command without `scoped` or `local` is refused by tengoku's lint in
every mode, and `bundle.py compose` runs the same check on the text it ships, after `scope_bundle.py` has scoped what it can. Refresh it with the rest of the file (the functions
`unscoped_violations` and its two patterns are appended at the end of tengoku's allowlist.py).

2026-10-28: refreshed from tengoku main: the same rules; `allowlist.py` now has the column-0 reading in a helper (`_command_lead`) and longer comments, `command-keywords.json` a longer `about`. A daily lint-drift check that says when this copy and tengoku differ is added by #119 (`scripts/check-lint-drift.mjs`, not in this tree yet).

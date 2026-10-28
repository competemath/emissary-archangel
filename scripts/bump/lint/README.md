A COPY of tengoku's content lint (the allow-list: what Lean text the tree may compile), taken from competemath/tengoku PR #247 (branch intake-class,
which brings the allow-list to the library's main; before that it was the copy in competemath/tengoku-sandbox). The factory uses it to decide
which modules of a bundle the tree would accept, and to say how many theorems each rule costs. Tengoku's gate runs its own copy; this
one decides nothing there. Refresh by copying the four files again (allowlist.py, allowed-options.json, lean_lex.py and command-keywords.json: the keywords of the
tree's Lean, schemas/command-keywords.json in tengoku, which the exact column-0 rule reads).

2026-10-18: the copy has `unscoped_violations` as well (tengoku scripts/ci/allowlist.py): a notation, `macro` or `syntax` command without `scoped` or `local` is refused by tengoku's lint in
every mode, and `bundle.py compose` runs the same check on the text it ships, after `scope_bundle.py` has scoped what it can. Refresh it with the rest of the file (the functions
`unscoped_violations` and its two patterns are appended at the end of tengoku's allowlist.py).

Drift is checked every day by .github/workflows/lint-drift.yml (scripts/check-lint-drift.mjs: the four files of tengoku's main against these, byte for byte; it opens or updates ONE issue, "pinned content lint
differs from tengoku main", with the options, keywords and definitions that were added or removed). `node scripts/check-lint-drift.mjs` runs it by hand. After a refresh the check must print "identical".

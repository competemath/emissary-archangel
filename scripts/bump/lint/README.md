A COPY of tengoku's content lint (the allow-list: what Lean text the tree may compile), taken from competemath/tengoku PR #247 (branch intake-class,
which brings the allow-list to the library's main; before that it was the copy in competemath/tengoku-sandbox). The factory uses it to decide
which modules of a bundle the tree would accept, and to say how many theorems each rule costs. Tengoku's gate runs its own copy; this
one decides nothing there. Refresh by copying the four files again (allowlist.py, allowed-options.json, lean_lex.py and command-keywords.json: the keywords of the
tree's Lean, schemas/command-keywords.json in tengoku, which the exact column-0 rule reads).

# Memory intake

How the theorems that Leak's runs proved and rated four stars or more get into Tengoku, and how their authors (and their drivers) hear what became of them. Everything is a workflow of this
repository, `.github/workflows/memory-intake.yml`, and `scripts/memory_intake/`.

```
competemath.com   kept theorems (>= 4 stars) of the accounts that share them (LEAK_INTAKE_ACCOUNTS)
      │  GET /api/leak/memory/candidates         (this job's OIDC token)
      ▼
 collect   compose each bundle (scripts/memory_intake/compose.py): one module per theorem, the manifest lines, the report
           praiser's text checks and its bar (bar/0)  →  accept / return (codes) / reject
           attest the archive the gate will rebuild (tengoku scripts/ci/studied_check.py)
      ▼
 open      one PR per bundle on competemath/tengoku, as the studied App (tengoku-supervisor), label `studied`; the PR's body carries a marker
      ▼
 post      POST /api/leak/memory/intake-events      returned / rejected theorems and the PRs that were opened (notices)
           POST /api/leak/memory/candidates         the theorems now in a bundle are not offered again
 every 30 minutes: report   the state of every studied PR (checks, reviews, merged, closed) → the same endpoint
```

tengoku does the rest: its autotag workflows write the isnad tags into the PR (docs/isnad.md, "Born tagged"), its gate (`scripts/ci/studied_check.py`, `born_tagged.py`) holds the PR to its
shape, evidence and attestation, the merge queue builds every module and recomputes every tag, and one code owner or two independent contributors approve.

## What this job does not do

* **It compiles nothing.** A candidate is a theorem the run's verifier (Leak IV) accepted when it was saved and whose harness evidence the site judged; the Tengoku tree builds every module in
  the autotag build and again in the merge queue. The report says so (`preflight.how`).
* **It runs no Jinshi and no model.** The reviewer is praiser's mechanical checks, the bar is a table (`praiser/bar.py`): the report's `review` names them, and has no `jinshi` section.
* **It checks duplicates and reuse only inside the studied lane** (the bundle and the target's earlier theorems), not against the Seed: that needs the tree's statements indexed.

## Rehearsal

`workflow_dispatch` with `target: competemath/tengoku-sandbox` and `dry_run: true` prints the PRs that would open and opens nothing. The App's secrets are `SUPERVISOR_APP_ID` and
`SUPERVISOR_APP_KEY`; `LEAK_INTAKE_ENABLED=1` (a repository variable here, an environment variable on the site) turns the schedule on.

## Tests

```bash
python3 -m unittest discover -s scripts/memory_intake/tests -t .
```

`compose.py`, `events.py` are pure; `githubapi.py` takes the GitHub API as a function. The cross-check that matters (a composition passes tengoku's real `studied_check.py`, and the archive
built here is byte for byte the one the gate rebuilds) was run against tengoku's gate by hand: the composer's tests cannot import tengoku.

## The earlier design

`bundle.schema.json` is the export of the first design (an account nominated 3 to 10 theorems and ten AI reviewers read them). It is not used by this pipeline.

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
 settle    close the PRs a code owner decided on, free the theorems nobody decided on (below)
 every 30 minutes: report   the state of every studied PR (checks, reviews, a code owner's decisions, merged, closed) → the same endpoint
```

tengoku does the rest: its autotag workflows write the isnad tags into the PR (docs/isnad.md, "Born tagged"), its gate (`scripts/ci/studied_check.py`, `born_tagged.py`) holds the PR to its
shape, evidence and attestation, the merge queue builds every module and recomputes every tag, and one code owner or two independent contributors approve.

## Sending single theorems back

A bundle is one pull request and its attestation covers all of it, so a theorem cannot be taken out of an open pull request. A **code owner** (the `*` line of tengoku's `.github/CODEOWNERS`, and a
GitHub association that means write access) decides on single theorems with plain lines in a comment on the pull request; the first eight characters of each theorem's id are in the PR body
(`· id a1b2c3d4`) and in the module's name (`S<id12>.lean`):

```
studied: return a1b2c3d4 merit  not used by anything yet          return codes: merit duplicate general naming docs
studied: reject e5f6a7b8 hygiene                                  reject codes: hygiene scope report
```

`return`: the author may come back with a better one. `reject`: not shipped, and this text is not sent again, whatever the proof (its id is the hash of the statement): use it for what must never ship, and
`return` for everything a better version could fix. The words after the code are the owner's own (the account reads them; the driver is
never given them: it is told what the code means by the site's catalogue, `src/app/lib/leak-memory/notices-catalogue.ts`). The specialised reviewer's file in tengoku, `.gitar/review/studied.md`,
writes these lines for the owner to copy.

What counts: a line that starts a line of a comment of a code owner. What does not (and is never guessed at): another account, a bot, the pull request's author; a quoted line (`>`), a line in a code
block or in an HTML comment, an indented one, one in a list; a malformed line, a code of the other verdict, an id that is not one of the pull request's or is the start of two. The latest decision of an
id wins. A malformed line of an owner is answered once on the pull request ("line 2: `deadbeef` is not the id of exactly one theorem") and in the job's log; a non-owner's is only in the log.

What happens (`scripts/memory_intake/decisions.py`, `settle.py`):

1. **Every 30 minutes (`report`)** the decisions go to the site with the PR's state: one notice per verdict and code (`review.return.merit`, `review.reject.hygiene`, ...), and the decided theorems are *held*
   (the site's kept row: returned or rejected).
2. **Within the half hour (`settle`, the App's token, right after the report; the `open` job of an intake runs the same step too)** the pull request is closed with a comment that names every theorem's fate, and the theorems nobody decided on
   are *freed* (their kept row is marked not-submitted again). They are bundled in the next intake (hourly), as a new pull request. A closed pull request is left alone; the comment
   has a marker, so a run that stopped between the comment and the close finishes without a second comment. A code owner who closes a pull request by hand *after* deciding on some of its theorems
   frees the rest in the same way (the next report sees a closed pull request with decisions); to drop a whole bundle, close it without a decision line.
3. **A rejected theorem** stays held for good (its id is the hash of its statement: the same statement is never offered again). **A returned one** is offered again only when its text changed (name, statement
   or proof) and the kept copy is replaced by the new save: the site says so to the driver ("revise it, save it again").
4. **A bundle of the same theorems** can be formed again after such a close (their ids are the same, so the bundle id and the branch name are). The pull request the intake closed that way is over: the new
   one is opened on the branch `studied/<target>/<bundle16>-r2` (`-r3`, ...). A pull request a person closed, or that merged, is not a round.

Tengoku needs no change for any of this: a closed pull request touches nothing, and the gate never sees the decisions.

## Adding a target

A target is one of the Leak page's statements. For its proved-on-the-way theorems to reach Tengoku:

1. **The site** (`mikael-bashir/compete-math`): add `src/data/leak-targets/<id>.json` and list it in `src/data/leak-targets/index.ts`. The id never changes afterwards (a saved theorem is kept per account and
   target id). Use the strict form: lower case letters and digits in words joined by single hyphens, **starting with a letter** (`erdos-396`, `collatz`): the intake refuses anything else
   (`compose.TARGET_ID`, tengoku `studied_check.py`), and the Lean namespace is the id in Pascal case (`Erdos396`), which must be a plain identifier and not one of tengoku's reserved folder names.
2. **Nothing in tengoku or here.** The first accepted bundle creates `data/studied/<id>/`, `Tengoku/Studied/<Ns>/` and `Tengoku/Studied/<Ns>.lean`, and adds one import line to `Tengoku/Studied.lean`.
3. **Who and what flows:** only accounts in `LEAK_INTAKE_ACCOUNTS` (a setting of the host) that have ticked "share" in the memory modal; only theorems rated `KEEP_AT` stars (4) or more whose run
   ticket and receipt passed and whose build the project published; at most ten per bundle; a target the account paused in the notices modal is skipped. A theorem the bar returns or rejects
   (praiser's `bar/0`; the codes are in the notice) never opens a pull request.
4. **Check it** with `workflow_dispatch` of `memory-intake` (`target: competemath/tengoku-sandbox`, `dry_run: true`): it prints the pull requests that would open.

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

`compose.py`, `events.py`, `decisions.py` are pure; `githubapi.py` and `settle.py` take the GitHub API as a function. The cross-check that matters (a composition passes tengoku's real `studied_check.py`, and the archive
built here is byte for byte the one the gate rebuilds) was run against tengoku's gate by hand: the composer's tests cannot import tengoku.

## The earlier design

`bundle.schema.json` is the export of the first design (an account nominated 3 to 10 theorems and ten AI reviewers read them). It is not used by this pipeline.

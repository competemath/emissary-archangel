# Emissary-Archangel

Translates verified Lean theorems from a source corpus on one Lean toolchain
into the [Tengoku](https://github.com/competemath/tengoku) tree on its
toolchain, and vouches for each translation twice before it is banked.

A translation of a theorem `T` is accepted only when

1. **Gate 1 — [Leak IV](https://github.com/mikael-bashir/leak-iv)**: the translated script elaborates on the Tengoku
   environment with no errors, no warnings and no `sorry`, and
2. **Gate 2 — Archangel**: the *original* `T` is replayed from an export of
   its module into that same environment and the kernel accepts
   `fun h => h : T_translated → T_original` — the translation proves at
   least what the original proved, under the original's own names.

Accepted translations are banked as **staging** records in the tree's
repository; a record becomes **trusted** only when its module builds in the
tree (`scripts/promote.py` there).

## Names

| Name | Meaning |
|---|---|
| **Emissary** | The translation side: reconstructing the original theorem with everything it depends on (the *dependency prelude*), a mechanical attempt (the original text resubmitted unchanged under the target toolchain), and an agent loop when that fails. |
| **Archangel** | The entailment gate (Gate 2) and its daemon (`gate2/`). |
| **Bridge** | `public/local-claude-bridge.mjs`: the local process that runs the Claude CLI agent with its MCP servers, hosts the harness routes (`/archangel-translate`, `/archangel-recurse`) and the governor. |
| **Governor** | The bridge's MCP proxy the agent's Leak IV calls pass through, so the harness sees every compile result and runs Gate 2 itself. The agent has no Gate 2 tool. |
| **Recursion engine** | `/archangel-recurse`: walks the queue file by file, mechanical attempt first, agent second, banking each success. |
| **Queue** | `data/queue-<source>.json` and the console (`app/page.tsx`): every entry to translate with its status. |
| **Corpus** | The source library at its own toolchain, checked out under `infra/`. Today: [equational_theories](https://github.com/teorth/equational_theories) at `e218ce18` on Lean v4.29.1. |
| **Exports** | `lean4export` dumps of an original module's declarations (`data/exports/<module>.ndjson`), corpus-scoped, which Gate 2 replays. |
| **Leak IV / Leak I** | The verifier (`verify_full_script`) and the search service (loogle + moogle), both running on the Tengoku tree. |

## Pipeline panel (run everything from the console)

The console at http://localhost:3000 has a **Pipeline** panel that owns the
whole local pipeline, so nothing needs a terminal after `pnpm dev`:

- **Local services** — Leak IV (verifier), Gate 2 (Archangel), Leak I (loogle)
  and a private bridge, each with start/stop and a live log. They import
  `Tengoku.All` from a *cache-pinned clone* of the tree (`~/tengoku-cache`,
  made with `scripts/pin.sh`), which is never compiled.
- **Tree cache** — check whether a newer nightly cache is published, and
  refresh the clone to it (download + replay check only). Restart the services
  afterwards so they load the new oleans.
- **Promote loop** — `scripts/promote-loop.sh` in the *working* tree: turns
  quiet staging files into trusted modules, commits and pushes.
- **Recursion run** — `scripts/run-recurse.mjs` against the private bridge,
  scoped to all pending entries, one file, or one entry; progress, per-outcome
  counts and the live log. Stop aborts the run at the bridge.
- **Configuration** — paths, ports and the bridge token, saved to
  `data/pipeline-config.json` (git-ignored).

Every process is spawned detached with a pid file and log under
`data/pipeline/`, so it survives closing the tab or reloading the dev server.
The API (`/api/pipeline`) only answers requests whose Host is localhost.

## Layout

```
app/                 Next.js console and the banking API (app/api/queue)
components/, lib/    console UI, MCP client, queue helpers
public/local-claude-bridge.mjs   the bridge (downloaded by users; also served by the app)
gate2/               the Archangel Gate 2 daemon: server.py, lsp_driver.py, Vendor/*.lean
infra/leak-iv-4291   the source-toolchain verifier (submodule; used to check reconstructions)
infra/equational-theories-manifest.jsonl   the corpus's theorem manifest
data/                queue files (run state)
```

Not in git (built or cloned locally, see below): `infra/equational-theories-4291/repo`
(the corpus checkout), `infra/lean4export` (the exporter built on the corpus's
toolchain), `data/exports/` and `data/recurse-prefix-cache.json` (run caches).

## Running it

Prerequisites: Node 22 + pnpm, Python 3.11+, `elan` with the corpus toolchain
(v4.29.1) and Tengoku's (v4.34.0-rc2), a checkout of the Tengoku tree with
its build in place (`scripts/cache.sh get` there), and the Claude CLI logged
in (the agent runs through it).

1. **Corpus** — clone the corpus at its pinned commit and build it on its
   own toolchain:
   ```bash
   git clone https://github.com/teorth/equational_theories infra/equational-theories-4291/repo
   git -C infra/equational-theories-4291/repo checkout e218ce18
   (cd infra/equational-theories-4291/repo && lake exe cache get && lake build)
   ```
2. **Exporter** — build `lean4export` on the corpus toolchain:
   ```bash
   git clone https://github.com/leanprover/lean4export infra/lean4export
   (cd infra/lean4export && git checkout <last commit whose lean-toolchain is v4.29.*> && echo leanprover/lean4:v4.29.1 > lean-toolchain && lake build)
   ```
3. **Gate 2 daemon** (`gate2/`):
   ```bash
   cd gate2 && lake update && (cd .lake/packages/tengoku && scripts/cache.sh get) && lake build
   python3 -m venv venv && venv/bin/pip install -r requirements.txt
   PORT=7872 GATE2_TREE_IMPORT=Tengoku.All EMISSARY_OLD_EXPORT=../data/export.ndjson venv/bin/python server.py
   ```
   Tools: `gate2_verify_entailment`, `gate2_list_dependencies`, `gate2_sync`
   (pull the tree, fetch its cache, rebuild, restart the resident elaborator).
4. **Leak IV and Leak I on the tree** — the `tengoku-env` branches of
   [leak-iv](https://github.com/mikael-bashir/leak-iv) and
   [leak-i](https://github.com/mikael-bashir/leak-i); each has a
   `tengoku_sync` tool.
5. **Console** — `pnpm install && pnpm dev`, open it, register the three
   MCP servers (Leak IV, Leak I, Archangel), copy the bridge setup command it
   shows (it carries `EMISSARY_APP_ROOT`, the token and the allowed origin),
   run it in a terminal, then **Recurse**.

Every bank writes `data/staging/<source>.jsonl` in the tree checkout
(`TENGOKU_STAGING_REPO`, default `../compete-math/tengoku`), runs promotion
there, and commits.

### Environment

| Variable | Used by | Default |
|---|---|---|
| `EMISSARY_APP_ROOT` | bridge | this checkout when served from `public/` |
| `GATE2_EXPORTS_DIR` | bridge | `<root>/data/exports` |
| `LEAN4EXPORT_BIN` | bridge | `<root>/infra/lean4export/.lake/build/bin/lean4export` |
| `CORPUS_ROOT_EQUATIONAL_THEORIES` | bridge | `<root>/infra/equational-theories-4291/repo` |
| `RECURSE_PREFIX_CACHE_PATH` | bridge | `<root>/data/recurse-prefix-cache.json` |
| `QUEUE_APP_URL` | bridge | `http://localhost:3000` |
| `BRIDGE_TOKEN`, `PORT`, `ALLOWED_ORIGINS` | bridge | random token, 4123, localhost |
| `TENGOKU_STAGING_REPO` | app | `../compete-math/tengoku` |
| `GATE2_TREE_IMPORT`, `EMISSARY_OLD_EXPORT`, `PORT` | gate2 | `Tengoku.All`, `gate2/data/export.ndjson`, 7861 |

## What the agent is and is not allowed

- It compiles only through `verify_full_script`; local `lean`/`lake`/`elan`
  and network commands are blocked by hooks, and every run starts in a
  throwaway working directory with no memory of earlier runs.
- It never calls Gate 2: the harness runs it on every Leak IV pass and
  appends the verdict to the same tool result.
- It must keep the original's names (Gate 2 shares them with the replayed
  original); a name that already exists in the target environment with a
  different definition ends the entry as untranslatable.

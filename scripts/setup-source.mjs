#!/usr/bin/env node
// Make one translation source self-contained, once.
//   node scripts/setup-source.mjs <key> [--concurrency N] [--keep-build]
//                                       [--reseed] [--uninstall-toolchain] [--only seed|build|export]
// Reads sources.json. Steps, each skipped when its output already exists:
//   1. toolchain   elan installs the source's own Lean (its .oleans must be read by a matching lean4export)
//   2. clone       infra/<key>/repo at the pinned commit (blobless clone, sources only)
//   3. seed        data/queue-<key>.json from the tree's data/tentative/<key>.jsonl — one pending
//                  entry per record whose module root is one of the source's `roots`, source line
//                  verified against the checkout
//   4. build       lake exe cache get (Mathlib .oleans) + lake build of exactly the modules that carry entries
//   5. lean4export built on that toolchain (infra/lean4export/<toolchain>/)
//   6. export      data/exports/<key>/<module>.names.json (corpus closure, one Lean process for all modules)
//                  and <module>.ndjson (lean4export of that closure, `concurrency` at a time)
//   7. cleanup     rm -rf infra/<key>/repo/.lake — the bridge and Gate 2 only ever read the exports and
//                  the source files from here on; --keep-build keeps it, --uninstall-toolchain also
//                  removes a toolchain that is neither the tree's nor 4.29.1
// Writes infra/<key>/setup.json with the counts. Re-runnable: finished steps are skipped.
//
// Split across runners (.github/workflows/setup-sharded.yml), for a library too big for one 6-hour job:
//   --phase build [--restore <b>]   toolchain, clone, build in module-name order (shared modules first); stops
//                                   there and keeps the build, which the workflow hands to the shards. With --restore
//                                   an earlier round's build is unpacked first, so rounds add up instead of starting over
//   --phase build-status            no Lean: how many of the modules have an .olean; writes infra/<key>/build-status.json
//                                   and prints `complete=true|false` (the workflow starts the shards only when true)
//   --phase shard --shard i/N       --restore <build.tar.zst>, then build the rest of this shard's modules (a stable
//                                   hash of the module name picks them) and run closures, notation expansion and
//                                   exports for them; writes data/exports/<key>/.shards/<i>-of-<N>.json when done
//   --phase finish                  writes setup.json from the exports and the shard records, once every module
//                                   is exported or recorded as failed by a shard that finished
import { execFile, execFileSync, spawn } from "node:child_process"
import { closeSync, existsSync, mkdirSync, openSync, readFileSync, readSync, renameSync, rmSync, writeFileSync, writeSync, readdirSync, statSync } from "node:fs"
import os from "node:os"
import { basename, dirname, join, relative, resolve } from "node:path"
import { StringDecoder } from "node:string_decoder"
import { fileURLToPath } from "node:url"
import { promisify } from "node:util"
import { collectTools, exporterAction, mergeTools, patchFingerprint, brokenLine, errorLineKeeper, brokenAlone, retrying, rootOfRepoPath, transientDownload } from "./setup-tools.mjs"
import { bisectItems } from "./bisect.mjs"
import { repairPins } from "./pinned-deps.mjs"
import { aloneFirstMs, availableFrom, buildAttempts, closureBigModules, closureBudgetMs, closureRetryMs, membersOf, soloBuildMs, soloMax } from "./memory-rules.mjs"

const x = promisify(execFile)
const APP_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..")
const HOME = os.homedir()
const PATH = [join(HOME, ".elan", "bin"), "/opt/homebrew/bin", "/usr/local/bin", process.env.PATH || ""].join(":")
// LEAN_NUM_THREADS bounds the Lean runtime's task pool, which is what Lake builds
// with: 2 compilers at a time (each a few GB on Mathlib-heavy files) instead of
// one per core. The setup must stay well under 20 GB alongside the Leak services.
const ENV = { ...process.env, PATH, HOME, LEAN_NUM_THREADS: process.env.LEAN_NUM_THREADS || "4" }

const argv = process.argv.slice(2)
const key = argv.find((a) => !a.startsWith("--") && !/^\d+$/.test(a))
const flag = (name, dflt) => {
  const i = argv.indexOf(`--${name}`)
  return i >= 0 ? argv[i + 1] ?? true : dflt
}
// One Lean process at a time: each import of Mathlib is a few GB, and the resident
// Leak services already hold theirs. Three at once pushed the machine into swap.
const CONCURRENCY = Number(flag("concurrency", 1))
// Lake has NO -j flag (it rejects it: "unknown short option"); its job pool is the Lean task pool,
// capped by LEAN_NUM_THREADS in ENV below. Three libraries were built with -j on 2026-09-24 and lost their build.
// Every `lean --run` (closures, notation expansion) is capped: one runaway expansion reached 18 GB and
// filled the swap and the disk. Past the cap Lean aborts with an out-of-memory error and the module is
// recorded as failed instead of taking the machine (EMISSARY_LEAN_MB, default 11264). Lean's check counts
// resident memory, and a process importing all of Mathlib maps ~7 GB of .olean files into it (the expander
// on a formal-conjectures module: 7 GB resident, 136 MB real footprint), so a 6 GB cap failed every
// Mathlib-wide import; 11 GB still stops a runaway like the 18 GB one.
const LEAN_MB = Math.max(1024, Number(process.env.EMISSARY_LEAN_MB || 11264))
const EXPORT_BATCH = Math.max(1, Number(flag("export-batch", 8)))
// How long an export may take. A healthy batch of 400 modules took 5.5 min (flt-anthropic, 4 Nov 2026), so a batch gets a base plus a few seconds per module, up to an hour,
// instead of an hour whatever its size: a batch that hangs is found in minutes, and each halving of it is cheaper than the one before. One module alone gets EXPORT_SINGLE_MS.
// a positive number of milliseconds a timer can hold (setTimeout turns a longer delay into 1 ms, and 0 would end every export at once); anything else is the default
const envMs = (name, dflt) => (Number(process.env[name]) > 0 && Number(process.env[name]) <= 2 ** 31 - 1 ? Number(process.env[name]) : dflt)
const EXPORT_BASE_MS = envMs("EMISSARY_EXPORT_BASE_MS", 3 * 60 * 1000)
const EXPORT_PER_MODULE_MS = envMs("EMISSARY_EXPORT_PER_MODULE_MS", 3000)
const EXPORT_SINGLE_MS = envMs("EMISSARY_EXPORT_SINGLE_MS", 20 * 60 * 1000)
const exportBatchMs = (n) => Math.min(60 * 60 * 1000, EXPORT_BASE_MS + EXPORT_PER_MODULE_MS * n)
// The closure phase, the same way (flt-anthropic, round 5, 5 Nov 2026: shard 59's closure batch of 337 modules ran its whole hour and failed, then 169 failed after another hour, and the
// shard took 4 hours; shard 55's batch of 497 the same): a closure process imports the union of its batch's modules, and for heavy modules that grows faster than the batch.
const CLOSURE_BASE_MS = envMs("EMISSARY_CLOSURE_BASE_MS", 10 * 60 * 1000)
const CLOSURE_PER_MODULE_MS = envMs("EMISSARY_CLOSURE_PER_MODULE_MS", 30 * 1000)
const CLOSURE_SINGLE_MS = envMs("EMISSARY_CLOSURE_SINGLE_MS", 20 * 60 * 1000)
const STARTED_MS = Date.now()
const CLOSURE_BUDGET_MS = closureBudgetMs()
const closureBatchMs = (n) => Math.min(60 * 60 * 1000, CLOSURE_BASE_MS + CLOSURE_PER_MODULE_MS * n)
// Per-process sizes; a library of tens of thousands of tiny modules (flt-anthropic) wants them
// large: every process pays the environment import, the modules themselves cost seconds.
const BUILD_CHUNK = Math.max(1, Number(flag("build-chunk", 150)))
const CLOSURE_BATCH = Math.max(1, Number(flag("closure-batch", 120)))
const KEEP_BUILD = argv.includes("--keep-build")
const RESEED = argv.includes("--reseed")
const UNINSTALL_TC = argv.includes("--uninstall-toolchain")
const ONLY = flag("only", null)
const KEEP_TOOLCHAINS = new Set(["leanprover/lean4:v4.34.0-rc2", "leanprover/lean4:v4.29.1"])

const ts = () => new Date().toISOString().slice(11, 19)
const log = (s) => console.log(`[${ts()}] ${s}`)
const fail = (s) => {
  console.error(`[${ts()}] FAIL ${s}`)
  process.exit(1)
}

if (!key) fail("usage: setup-source.mjs <key>")
const registry = JSON.parse(readFileSync(join(APP_ROOT, "sources.json"), "utf8"))
const src = registry.sources[key]
if (!src) fail(`unknown source ${key} (sources.json)`)
if (!src.repo || !src.commit || !src.toolchain || !src.roots?.length) fail(`${key}: sources.json entry needs repo, commit, toolchain, roots`)

const PHASE = flag("phase", null)
if (PHASE && !["build", "build-status", "shard", "finish"].includes(PHASE)) fail(`--phase is build, build-status, shard or finish, not ${PHASE}`)
const SHARD = (() => {
  const s = flag("shard", null)
  if (!s) return null
  const [i, n] = String(s).split("/").map(Number)
  if (!(Number.isInteger(i) && Number.isInteger(n) && n > 0 && i >= 0 && i < n)) fail(`--shard wants i/N with 0 <= i < N, not ${s}`)
  return { i, n }
})()
if (PHASE === "shard" && !SHARD) fail("--phase shard needs --shard i/N")
const RESTORE = flag("restore", null)
// FNV-1a of the module name: the same module lands in the same shard on every runner and every dispatch.
const shardOf = (m) => {
  let h = 0x811c9dc5
  for (const c of Buffer.from(m, "utf8")) h = Math.imul(h ^ c, 0x01000193) >>> 0
  return h % SHARD.n
}
const inShard = (m) => !SHARD || shardOf(m) === SHARD.i

const INFRA = join(APP_ROOT, "infra", key)
// The clone, and the Lake project inside it (`subdir`, for a repository of several projects such as
// anthropics/formal-math, whose zeta23/ has its own lakefile and toolchain).
const CLONE = src.corpusRoot ? resolve(APP_ROOT, src.corpusRoot) : join(INFRA, "repo")
const REPO = src.subdir ? join(CLONE, src.subdir) : CLONE
const EXPORTS = join(APP_ROOT, "data", "exports", key)
const QUEUE = join(APP_ROOT, "data", src.queueFile || `queue-${key}.json`)
// One tentative file per source, or several for a repo the harvester sharded (leanbridge-001…015).
const TENTATIVE_FILES = (src.tentative || [`${key}.jsonl`]).map((f) =>
  resolve(APP_ROOT, process.env.EMISSARY_TENTATIVE_DIR || registry.tentativeDir || "../compete-math/tengoku/data/tentative", f),
)
// Written next to the exports by .github/workflows/setup-libraries.yml: the library was set up on a runner.
const CI_RECORD = join(EXPORTS, "setup.ci.json")
const TC_SLUG = src.toolchain.replace(/[^A-Za-z0-9.-]+/g, "_")
const L4E_DIR = join(APP_ROOT, "infra", "lean4export", TC_SLUG)
const L4E_BIN = join(L4E_DIR, ".lake", "build", "bin", "lean4export")
const CLOSURE_LEAN = join(APP_ROOT, "scripts", "corpus-closure-batch.lean")
const SETUP_JSON = join(INFRA, "setup.json")
mkdirSync(INFRA, { recursive: true })
mkdirSync(EXPORTS, { recursive: true })

// The commands that are running (each leads its own process group): a SIGINT or SIGTERM to this script, which no longer reaches them through the terminal's group, ends them too.
const live = new Set()
for (const [sig, code] of [["SIGINT", 130], ["SIGTERM", 143]]) {
  process.on(sig, () => {
    for (const p of live) killGroup(p)
    process.exit(code)
  })
}
// Kills a command started with `detached: true` and everything it started (its process group); the command alone if the group is already gone.
function killGroup(p) {
  try {
    process.kill(-p.pid, "SIGKILL")
  } catch {
    try { p.kill("SIGKILL") } catch { /* already exited */ }
  }
}

// Streams a long command's output to our stdout (lake build progress) and resolves with its exit code.
function run(cmd, args, { cwd = APP_ROOT, timeoutMs = 4 * 3600 * 1000, quiet = false } = {}) {
  return new Promise((res) => {
    if (!quiet) log(`$ ${cmd} ${args.join(" ")}  (cwd ${cwd})`)
    // detached: the command leads its own process group, so that a timeout can kill the whole tree. `lake env <tool>` runs the tool as a child of `lake`:
    // killing `lake` alone left the tool running, reparented to init, out of the watchdog's sight, and holding the CPU and memory the next attempt needed
    // (flt-anthropic round 4, 4 Nov 2026: four shards re-ran a timed-out export on halves of 200, 100 and 50 modules, each timing out too, for five hours).
    const p = spawn(cmd, args, { cwd, env: ENV, stdio: ["ignore", "pipe", "pipe"], detached: true })
    live.add(p)
    let tail = ""
    const errors = errorLineKeeper()
    const onData = (stream) => (d) => {
      const s = d.toString()
      tail = (tail + s).slice(-4000)
      errors.add(s, stream)
      if (!quiet) process.stdout.write(s)
    }
    p.stdout.on("data", onData("out"))
    p.stderr.on("data", onData("err"))
    const t = setTimeout(() => {
      killGroup(p)
      res({ code: 124, tail: tail + `\n[timed out after ${timeoutMs / 1000}s]`, errors: errors.text() })
    }, timeoutMs)
    p.on("close", (code) => {
      live.delete(p)
      clearTimeout(t)
      res({ code: code ?? 1, tail, errors: errors.text() })
    })
  })
}
// Which tools are producing this setup (Lean, Lake, elan, lean4export's commit and patch, node, the runner image): written into the record, so that two runs that differ have an explanation on file.
// Asked of the machine that ran the Lean code. A tool that cannot be asked is null in the record, never a reason to fail the setup.
const PATCH_SCRIPT = join(APP_ROOT, "scripts", "patch-lean4export.py")
const PATCH_MARK = join(L4E_DIR, ".patch-sha") // the fingerprint of the patch script the exporter in this folder was built with
const toolsNow = () =>
  collectTools({
    exec: (cmd, args) => x(cmd, args, { env: ENV, timeout: 60000 }).then((r) => r.stdout),
    env: process.env,
    nodeVersion: process.version,
    toolchain: src.toolchain,
    l4eDir: L4E_DIR,
    patchRecorded: existsSync(PATCH_MARK) ? readFileSync(PATCH_MARK, "utf8") : null,
  })
// Like run(), with stdout (up to maxBuffer bytes) and the tail of stderr handed back. A timeout kills the whole process group, so that `lake env lean` leaves no `lean` behind
// (execFile's `timeout` kills only `lake`).
function runCapture(cmd, args, { cwd = APP_ROOT, timeoutMs = 4 * 3600 * 1000, maxBuffer = 512 * 1024 * 1024 } = {}) {
  return new Promise((res) => {
    const p = spawn(cmd, args, { cwd, env: ENV, stdio: ["ignore", "pipe", "pipe"], detached: true })
    live.add(p)
    const out = []
    let size = 0
    let tail = ""
    let done = false
    const finish = (r) => {
      if (done) return
      done = true
      clearTimeout(t)
      live.delete(p)
      res(r)
    }
    p.stdout.on("data", (d) => {
      size += d.length
      if (size > maxBuffer) {
        killGroup(p)
        return finish({ code: 1, stdout: "", tail: `stdout over ${maxBuffer} bytes` })
      }
      out.push(d)
    })
    p.stderr.on("data", (d) => { tail = (tail + d.toString()).slice(-4000) })
    const t = setTimeout(() => {
      killGroup(p)
      finish({ code: 124, stdout: "", tail: tail + `\n[timed out after ${timeoutMs / 1000}s]` })
    }, timeoutMs)
    p.on("close", (code) => finish({ code: code ?? 1, stdout: Buffer.concat(out).toString(), tail }))
    p.on("error", (e) => finish({ code: 1, stdout: "", tail: String(e) }))
  })
}
// Like run(), with stdout written to `outPath` (stderr captured for the report).
function runToFile(cmd, args, outPath, { cwd = APP_ROOT, timeoutMs = 4 * 3600 * 1000 } = {}) {
  return new Promise((res) => {
    const fd = openSync(outPath, "w")
    const p = spawn(cmd, args, { cwd, env: ENV, stdio: ["ignore", fd, "pipe"], detached: true })
    live.add(p)
    let tail = ""
    p.stderr.on("data", (d) => { tail = (tail + d.toString()).slice(-4000) })
    // the file is closed once: after a timeout the killed command's own `close` event comes as well, and a second closeSync of the same descriptor throws (EBADF)
    let open = true
    const closeOnce = () => { if (open) { open = false; closeSync(fd) } }
    const t = setTimeout(() => { killGroup(p); closeOnce(); res({ code: 124, tail: tail + `\n[timed out after ${timeoutMs / 1000}s]` }) }, timeoutMs)
    p.on("close", (code) => { live.delete(p); clearTimeout(t); closeOnce(); res({ code: code ?? 1, tail }) })
  })
}
// A path component that is not a plain identifier (formal-conjectures' arXiv directories,
// `Arxiv/1102.4662/`) is a module-name component only when written `«1102.4662»`: Lean reads
// `A.1102.4662.C` as four components and the import fails. Same rule both ways.
const PLAIN_COMPONENT = /^[\p{L}_][\p{L}\p{N}_'!?]*$/u
const moduleOfPath = (p) =>
  p
    .replace(/\.lean$/, "")
    .split("/")
    .map((c) => (PLAIN_COMPONENT.test(c) ? c : `«${c}»`))
    .join(".")
const moduleComponents = (m) => [...m.matchAll(/«[^»]*»|[^.]+/g)].map((x) => x[0].replace(/^«|»$/g, ""))
const pathOfModule = (m) => moduleComponents(m).join("/") + ".lean"
// Lake's build layout: .lake/build/lib/lean/ since about v4.3, build/lib/ before (the v4.0–v4.2 sources).
const oleanOf = (m) => {
  const rel = pathOfModule(m).replace(/\.lean$/, ".olean")
  const cur = join(REPO, ".lake", "build", "lib", "lean", rel)
  const old = join(REPO, "build", "lib", rel)
  return !existsSync(cur) && existsSync(old) ? old : cur
}
// ---- modules that need more memory than the machine lets one process have ----------------------------------------
// A module whose Lean process passes EMISSARY_FOOTPRINT_MB is killed by the watchdog below, its `lake build` chunk fails, and every module
// that imports it can never compile. Until 2026-10-29 that was invisible: flt-anthropic's Def_WeierstrassCurve_DivPolyMulFormula was killed
// at 11 GB in 5 of the first 17 chunks of every round, for rounds, with the module's name cut off the log line, and 2,896 modules never built.
// Now: the kill names the module (`oomKilled`); the module is built again ALONE, with the machine to itself and a higher limit; one that
// still does not fit is written to .lake/build/emissary-oom.json (packed with the build, so the next round knows) and it, and everything that
// imports it, is left out of the chunks instead of being killed again. buildStatus reports them.
const oomKilled = new Map() // module -> { mb, why }: killed by the watchdog since the last time it was looked at
const RETRY_FOOTPRINT_MB = Number(process.env.EMISSARY_RETRY_FOOTPRINT_MB) > 0 ? Number(process.env.EMISSARY_RETRY_FOOTPRINT_MB) : 14336
const OOM_FILE = join(REPO, ".lake", "build", "emissary-oom.json")
const SOLO_MAX = soloMax() // modules built alone in one run: each can take minutes (memory-rules.mjs: more when the retry limit is the escalation's, EMISSARY_RETRY_FOOTPRINT_MB >= 57344)
const BUILD_ATTEMPTS = buildAttempts() // tries of one chunk, each after the killed modules were built alone
const SOLO_BUILD_MS = soloBuildMs()
const MODULE_NAME = /^(?:[\p{L}_][\p{L}\p{N}_'!?]*|«[^»]+»)(?:\.(?:[\p{L}_][\p{L}\p{N}_'!?]*|«[^»]+»))*$/u
// `srcdir` is one folder or a list of them (a monorepo of Lake libraries); the longest that matches, so that `a/b` is tried before `a`
const SRCDIRS = [].concat(src.srcdir || []).sort((x, y) => y.length - x.length)
const fromSrcdir = (p) => {
  const dir = SRCDIRS.find((d) => p.startsWith(d + "/"))
  return dir ? p.slice(dir.length + 1) : p
}
const moduleOfCommand = (cmd) => {
  for (const tok of cmd.split(/\s+/)) {
    if (!tok.endsWith(".lean")) continue
    const rel = relative(REPO, resolve(REPO, tok)).replace(/\\/g, "/")
    if (rel && !rel.startsWith("..")) return moduleOfPath(fromSrcdir(rel))
  }
  return null
}
// What an earlier round recorded. It comes out of an artifact, so it is data: anything that is not a module name with two numbers is dropped.
// An entry recorded under a lower limit than this run's is dropped too, so that raising the limit tries the module again.
function loadOom({ prune = false } = {}) {
  const out = new Map()
  let dropped = 0
  try {
    const raw = JSON.parse(readFileSync(OOM_FILE, "utf8"))
    for (const [m, v] of Object.entries(raw?.toobig ?? {})) {
      if (m.length <= 300 && MODULE_NAME.test(m) && Number.isFinite(v?.peakMB) && Number.isFinite(v?.capMB) && v.capMB >= RETRY_FOOTPRINT_MB) out.set(m, { peakMB: Math.round(v.peakMB), capMB: Math.round(v.capMB) })
      else dropped++
    }
  } catch {
    /* none yet, or unreadable: nothing is known */
  }
  if (prune && dropped) saveOom(out) // the build phase writes the forgetting down; the status phase only reads
  return out
}
// A module that does not compile at the library's own commit, with every library module it imports built: its own file has an error (tnlean, 6 Nov 2026:
// TNLean.Archive.BlockingPeriodicityCFII2, two unknown identifiers upstream). No round can build it, so it is written down here (packed with the build, as the
// too-big ones are) and buildStatus counts it, and what imports it, like a too-big module: the build is complete without them and the shards export the rest.
// Before, one such file stopped the whole library: the round after added nothing, the chain stopped, and 1,155 built modules were never exported.
const BROKEN_FILE = join(REPO, ".lake", "build", "emissary-broken.json")
const BROKEN_PROBE_MAX = 50 // modules tried alone for this at the end of a round (each a few seconds to minutes)
function loadBroken() {
  const out = new Map()
  try {
    const raw = JSON.parse(readFileSync(BROKEN_FILE, "utf8"))
    // broken at THIS commit only: a library re-pinned to another commit may compile the module now
    if (raw?.commit !== src.commit) return out
    for (const [m, v] of Object.entries(raw?.broken ?? {})) if (m.length <= 300 && MODULE_NAME.test(m) && typeof v?.error === "string") out.set(m, { error: v.error.slice(0, 300) })
  } catch {
    /* none yet, or unreadable */
  }
  return out
}
function saveBroken(map) {
  mkdirSync(dirname(BROKEN_FILE), { recursive: true })
  writeAtomic(BROKEN_FILE, JSON.stringify({ version: 1, commit: src.commit, broken: Object.fromEntries(map) }, null, 2))
}
// The first error a build printed for the file of module `m` itself (`error: ./Lib/X.lean:3:4: ...`, or without ./), or null.
// ... or an import of its own library that has no source file at this commit (setup-tools.mjs missingOwnImport)
const sourceExists = (m) => [pathOfModule(m), ...SRCDIRS.map((d) => `${d}/${pathOfModule(m)}`)].some((p) => existsSync(join(REPO, p)))
const OWN = { roots: src.roots, exists: sourceExists }
const ownError = (m, text) => brokenLine(pathOfModule(m), SRCDIRS, text, OWN)
function saveOom(map) {
  mkdirSync(dirname(OOM_FILE), { recursive: true })
  writeAtomic(OOM_FILE, JSON.stringify({ version: 1, toobig: Object.fromEntries(map) }, null, 2))
}
// The imports of a Lean file: only its header counts (comments, `module`, `prelude` and imports come first).
function parseImports(text) {
  const out = []
  let depth = 0 // block comments nest in Lean: `/- a /- b -/ c -/` is one comment
  for (const line of text.split("\n")) {
    const t = line.trim()
    if (depth > 0 || t.startsWith("/-")) {
      for (const m of t.matchAll(/\/-|-\//g)) depth = Math.max(0, depth + (m[0] === "/-" ? 1 : -1))
      continue
    }
    if (!t || t.startsWith("--")) continue
    const m = t.match(/^(?:(?:public|meta|private)\s+)*import\s+(?:all\s+)?(.*)$/)
    if (m) {
      out.push(...m[1].split("--")[0].trim().split(/\s+/).filter(Boolean))
      continue
    }
    if (/^(?:module|prelude)\b/.test(t)) continue
    break
  }
  return out
}
const importCache = new Map()
const importsOf = (m) => {
  if (!importCache.has(m)) {
    let imports = null // null: not a file of this library (Mathlib, Lean, Std)
    try {
      imports = parseImports(readFileSync(join(REPO, pathOfModule(m)), "utf8"))
    } catch {
      /* not here */
    }
    importCache.set(m, imports)
  }
  return importCache.get(m)
}
// module -> the too-big module it cannot be built without, for every module of `modules` that imports one (a too-big module blocks itself).
function blockedBy(toobig, modules) {
  const blocker = new Map()
  if (!toobig.size) return blocker
  const memo = new Map()
  const visiting = new Set()
  const find = (m) => {
    if (toobig.has(m)) return m
    if (memo.has(m)) return memo.get(m)
    if (visiting.has(m)) return null
    visiting.add(m)
    let hit = null
    for (const i of importsOf(m) ?? []) if ((hit = find(i))) break
    visiting.delete(m)
    memo.set(m, hit)
    return hit
  }
  for (const m of modules) {
    const b = find(m)
    if (b) blocker.set(m, b)
  }
  return blocker
}
// Every file a later run treats as "done" is written whole or not at all: the setup can be killed at
// any moment (sleep, a closed network, a restart) and the next run skips whatever exists.
function writeAtomic(path, data) {
  const tmp = `${path}.tmp-${process.pid}`
  writeFileSync(tmp, data)
  renameSync(tmp, path)
}
// The bytes of JSON.stringify(items, null, 2), written item by item as the seed makes them: leanbridge's queue (15 tentative files of ~40 MB, records with long proofs) as one
// string did not fit in Node's heap (setup runs 42387020776, 42411218917), and neither did the entries themselves, every statement and proof kept until the end (1,645 records of
// leanbridge-001 take 118 MB of heap, ~1.7 GB for the 15 files: "JavaScript heap out of memory" in the seed of every build round of setup run 42427677819 and the five after it).
// The file is renamed into place by close(), so a queue is whole or absent.
function jsonArrayWriter(path) {
  const tmp = `${path}.tmp-${process.pid}`
  const fd = openSync(tmp, "w")
  let n = 0
  return {
    push(e) {
      writeSync(fd, (n++ ? ",\n" : "[\n") + "  " + JSON.stringify(e, null, 2).replace(/\n/g, "\n  "))
    },
    close() {
      writeSync(fd, n ? "\n]" : "[]")
      closeSync(fd)
      renameSync(tmp, path)
    },
  }
}
// The entries of a queue in the shape JSON.stringify(items, null, 2) writes, read one entry at a time: leanbridge's queue is ~600 million characters, longer than the longest string
// Node can make, so the next step of the same job (build-status after the build) could not read it whole. JSON strings hold no raw newline, so an entry is the lines from "  {"
// to "  }" or "  },", and the commas are checked (every entry but the last ends with one). `keep` cuts each entry down to what is used. A file of another shape (minified, "[]")
// is parsed whole, as before.
function readQueueEntries(path, keep) {
  const fd = openSync(path, "r")
  try {
    const head = Buffer.alloc(2)
    if (readSync(fd, head, 0, 2, 0) < 2 || head.toString() !== "[\n") return JSON.parse(readFileSync(path, "utf8")).map(keep)
    const out = []
    const dec = new StringDecoder("utf8")
    const buf = Buffer.allocUnsafe(1 << 24)
    let rest = ""
    let cur = null
    let ended = false
    let after = "[" // what the last entry ended with: "[" (none yet), "," (another must follow) or "}" (the last one: "]" must follow)
    const line = (l, no) => {
      if (ended) {
        if (l !== "") throw new Error(`queue ${path}: text after the closing ]`)
      } else if (no === 0) {
        if (l !== "[") throw new Error(`queue ${path}: does not start with [`)
      } else if (cur === null) {
        if (l === "]" && after === "}") ended = true
        else if (l === "  {" && after !== "}") cur = [l]
        else throw new Error(`queue ${path}: line ${no + 1} is not ${after === "}" ? "the closing ] (an entry without a comma before it?)" : after === "," ? "the start of an entry (a comma before the closing ]?)" : "the start of an entry"}`)
      } else if (l === "  }" || l === "  },") {
        cur.push("}")
        out.push(keep(JSON.parse(cur.join("\n"))))
        cur = null
        after = l === "  }" ? "}" : ","
      } else cur.push(l)
    }
    let no = 0
    for (let pos = 0, got; (got = readSync(fd, buf, 0, buf.length, pos)) > 0; pos += got) {
      const lines = (rest + dec.write(buf.subarray(0, got))).split("\n")
      rest = lines.pop()
      for (const l of lines) line(l, no++)
    }
    line(rest + dec.end(), no)
    if (!ended || cur !== null) throw new Error(`queue ${path}: ends before its closing ]`)
    return out
  } finally {
    closeSync(fd)
  }
}
// What the setup itself uses of an entry (its module, and the count): the statement and proof stay in the queue file, for the translation that reads it (queue-server.mjs).
const slimEntry = (e) => ({ id: e.id, name: e.name, sourcePath: e.sourcePath, sourceLine: e.sourceLine, status: e.status })
// The lines of the tentative files, one file in memory at a time (leanbridge has 15 of them, ~600 MB together).
function* tentativeLines() {
  for (const f of TENTATIVE_FILES) yield* readFileSync(f, "utf8").split("\n")
}
// github.com reachable: a failure while offline is an interruption, not a verdict on the library.
const online = () => x("curl", ["-sI", "-m", "10", "https://github.com"], { env: ENV }).then(() => true, () => false)

// ---- 1. toolchain ---------------------------------------------------------------
async function ensureToolchain() {
  const { stdout } = await x("elan", ["toolchain", "list"], { env: ENV })
  if (stdout.split("\n").some((l) => l.trim().startsWith(src.toolchain))) return log(`toolchain ${src.toolchain} present`)
  const r = await retrying(() => run("elan", ["toolchain", "install", src.toolchain], { timeoutMs: 30 * 60 * 1000 }), { warn: log, shouldRetry: transientDownload })
  if (r.code !== 0) fail(`elan toolchain install ${src.toolchain}: ${r.tail.slice(-500)}`)
}

// ---- 2. clone -------------------------------------------------------------------
async function ensureClone() {
  if (!existsSync(join(CLONE, ".git"))) {
    mkdirSync(dirname(CLONE), { recursive: true })
    const r = await run("git", ["clone", "-q", "--filter=blob:none", src.repo, CLONE], { timeoutMs: 30 * 60 * 1000 })
    if (r.code !== 0) fail(`git clone: ${r.tail.slice(-500)}`)
  }
  const head = (await x("git", ["rev-parse", "HEAD"], { cwd: REPO, env: ENV })).stdout.trim()
  if (head !== src.commit) {
    const r = await run("git", ["-c", "advice.detachedHead=false", "checkout", "-q", src.commit], { cwd: REPO, timeoutMs: 10 * 60 * 1000 })
    if (r.code !== 0) fail(`git checkout ${src.commit}: ${r.tail.slice(-500)}`)
  }
  const pinned = existsSync(join(REPO, "lean-toolchain")) ? readFileSync(join(REPO, "lean-toolchain"), "utf8").trim() : ""
  if (pinned && pinned !== src.toolchain && src.pinToolchain) {
    // the registry wins: the library's own Mathlib needs another toolchain than its lean-toolchain says (flt-anthropic: v4.33.1 against Mathlib's v4.33.0), and then
    // `lake exe cache get` refuses and every build compiles Mathlib from source
    log(`checkout pins ${pinned}; the registry's ${src.toolchain} is used instead (pinToolchain), written into the checkout's lean-toolchain`)
    writeFileSync(join(REPO, "lean-toolchain"), `${src.toolchain}\n`)
  } else {
    if (pinned && pinned !== src.toolchain) log(`WARNING: checkout pins ${pinned}, registry says ${src.toolchain} — using the checkout's`)
    if (pinned) src.toolchain = pinned
  }
  if (SRCDIRS.length) {
    const r = await run("python3", [join(APP_ROOT, "scripts", "bump", "link_srcdir.py"), key, REPO], { timeoutMs: 60 * 1000 })
    if (r.code !== 0) fail(`link_srcdir: ${r.tail.slice(-500)}`)
  }
  log(`checkout ${REPO} @ ${src.commit.slice(0, 12)} (${src.toolchain})`)
}

// ---- 3. seed the queue ----------------------------------------------------------
const DECL_KW = "(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)"
const escapeRe = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")
// The name a statement declares. The tree's harvester cut `name` at the first
// non-ASCII identifier character (`pairwiseDisjoint_𝔘₁` arrived as
// `pairwiseDisjoint_`, eleven times over); the statement text has the real one.
const NAME_RE = new RegExp(`(?:^|\\n)\\s*(?:@\\[[^\\]]*\\]\\s*)*(?:(?:private|protected|nonrec|noncomputable|scoped|unsafe|partial)\\s+)*${DECL_KW}\\s+([^\\s(\\[{⦃:]+)`, "u")
function declaredName(statement) {
  const m = String(statement).match(NAME_RE)
  return m ? m[1].replace(/[«»]/g, "") : null
}
// Block-comment depth at the start of every line (`/-` opens, `-/` closes, nested).
// The tree's harvester read declarations out of commented-out blocks too; those
// are not declarations and must not become entries.
function commentDepths(lines) {
  const out = new Array(lines.length)
  let depth = 0
  for (let i = 0; i < lines.length; i++) {
    out[i] = depth
    const l = lines[i]
    for (let j = 0; j < l.length - 1; j++) {
      if (l[j] === "/" && l[j + 1] === "-") {
        depth++
        j++
      } else if (l[j] === "-" && l[j + 1] === "/" && depth > 0) {
        depth--
        j++
      } else if (depth === 0 && l[j] === "-" && l[j + 1] === "-") break
    }
  }
  return out
}
// The bridge's deriveQualifiedName, verbatim in spirit: the `namespace X` / `end X`
// stack above the declaration. Entries are named by this so two `foo`s in two
// namespaces are two records, not a duplicate.
function qualify(lines, declLine, bare) {
  const stack = []
  for (const line of lines.slice(0, Math.max(0, declLine - 1))) {
    const ns = line.match(/^\s*namespace\s+(\S+)/)
    if (ns) {
      stack.push(ns[1])
      continue
    }
    const end = line.match(/^\s*end\s+(\S+)/)
    if (end && stack.length && stack[stack.length - 1] === end[1]) stack.pop()
  }
  return stack.length ? `${stack.join(".")}.${bare}` : bare
}
function seedQueue() {
  const stats = { records: 0, kept: 0, skippedRoot: 0, skippedDup: 0, skippedNoFile: 0, skippedCommented: 0, lineFixed: 0, lineUnverified: 0, nameFixed: 0, sorryOriginals: 0, emptyProofs: 0 }
  if (existsSync(QUEUE) && !RESEED) {
    const q = readQueueEntries(QUEUE, slimEntry)
    log(`queue exists: ${QUEUE} (${q.length} entries) — keeping it (--reseed to rebuild)`)
    return { entries: q, stats: null }
  }
  for (const f of TENTATIVE_FILES) if (!existsSync(f)) fail(`no tentative file at ${f}`)
  const roots = new Set(src.roots)
  const seen = new Set()
  // The files read so far, kept within a budget (EMISSARY_SEED_CACHE_MB of text, default 256): leanbridge (7 Nov 2026) has 1.5 GB of Lean sources (LMFDB tables, up to 53 MB a
  // file), and keeping every file's lines killed Node at its 4 GB heap in every phase ("JavaScript heap out of memory", setup runs 42386199526 and 42387020776). The records of a
  // file come together (each tentative file lists them file by file), so each file is read once; a file evicted and asked for again is read again, with the same result.
  const budgetMb = Number(process.env.EMISSARY_SEED_CACHE_MB || 256)
  const cacheBudget = (Number.isFinite(budgetMb) && budgetMb >= 1 ? budgetMb : 256) * 1024 * 1024 // a value that is no finite number of MB falls back to the default
  log(`seed: the files read are kept within ${cacheBudget / 1024 / 1024} MB of text`)
  const fileCache = new Map()
  let cached = 0
  const fileOf = (p) => {
    if (fileCache.has(p)) {
      const hit = fileCache.get(p)
      fileCache.delete(p) // most recently used last
      fileCache.set(p, hit)
      return hit
    }
    const abs = join(REPO, p)
    let file = null
    if (existsSync(abs)) {
      const text = readFileSync(abs, "utf8")
      const lines = text.split("\n")
      file = { lines, depth: commentDepths(lines), size: text.length }
    }
    if (file && file.size > cacheBudget) return file // a file larger than the whole budget is used and not kept
    fileCache.set(p, file)
    cached += file ? file.size : 0
    for (const [k, v] of fileCache) {
      if (cached <= cacheBudget || k === p) break
      fileCache.delete(k)
      cached -= v ? v.size : 0
    }
    return file
  }
  const entries = []
  const skippedTops = new Map() // what the records outside the roots start with, for the message below
  const queue = jsonArrayWriter(QUEUE)
  for (const raw of tentativeLines()) {
    if (!raw.trim()) continue
    const r = JSON.parse(raw)
    stats.records++
    const m = r.source_url.match(/^https:\/\/github\.com\/([^/]+\/[^/]+)\/blob\/([0-9a-f]+)\/(.+?)#L(\d+)$/)
    if (!m) {
      stats.skippedNoFile++
      continue
    }
    let [, ownerRepo, commit, path] = m
    let line = Number(m[4])
    if (src.subdir && path.startsWith(src.subdir + "/")) path = path.slice(src.subdir.length + 1) // records are repository-relative
    path = fromSrcdir(path) // and a module is named from inside its source folder (Lean4/A/B.lean is A.B)
    if (!roots.has(rootOfRepoPath(path)) || path.includes("..")) {
      stats.skippedRoot++
      const top = path.split("/")[0]
      skippedTops.set(top, (skippedTops.get(top) || 0) + 1)
      continue
    }
    const file = fileOf(path)
    if (!file) {
      stats.skippedNoFile++
      continue
    }
    const { lines, depth } = file
    // The harvester's line is usually the one ABOVE the declaration (it keeps the
    // leading blank line); the recursion loop slices the file prefix at sourceLine,
    // so it must be the declaration's own first line (attributes included). Find the
    // nearest line that starts with the statement's first line and is followed by
    // the declaration of this very name.
    const first = String(r.statement).split("\n")[0].trim()
    const declared = declaredName(r.statement) || String(r.name)
    if (declared !== r.name) stats.nameFixed++
    const bare = declared.split(".").pop()
    const declRe = new RegExp(`(?:^|\\s)${DECL_KW}\\s+(?:[\\w'.«»]*\\.)?${escapeRe(bare)}(?![\\w'])`)
    const at = (n) => (n >= 1 && n <= lines.length ? lines[n - 1].trim() : null)
    const declaresHere = (n) => {
      for (let k = n; k <= Math.min(n + 3, lines.length); k++) if (declRe.test(lines[k - 1])) return true
      return false
    }
    let found = null
    for (const d of [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 8, -8, 10, -10]) {
      const n = line + d
      const t = at(n)
      if (t == null || !t.startsWith(first) || !declaresHere(n)) continue
      found = n
      break
    }
    if (found == null) stats.lineUnverified++
    else {
      if (found !== line) stats.lineFixed++
      line = found
    }
    if (depth[line - 1] > 0 || (at(line) || "").startsWith("--")) {
      stats.skippedCommented++
      continue
    }
    const name = qualify(lines, line, declared)
    if (seen.has(name)) {
      stats.skippedDup++
      continue
    }
    if (/\bsorry\b/.test(r.proof || "")) stats.sorryOriginals++
    if (!String(r.proof || "").replace(/^\s*:=\s*/, "").trim()) stats.emptyProofs++
    seen.add(name)
    const entry = {
      id: entries.length + 1,
      name,
      oldStatement: r.statement,
      oldProofText: r.proof,
      oldExportNames: declared,
      status: "pending",
      exportNamesConfirmed: true,
      source: key,
      category: basename(path),
      sourceRef: `${ownerRepo}@${commit}:${path}#L${line}`,
      sourcePath: path,
      sourceLine: line,
    }
    queue.push(entry)
    entries.push(slimEntry(entry))
    stats.kept++
  }
  queue.close()
  // A library with records of which none is kept is a registry that does not describe the repository (or a harvest of something else), never a library with nothing to give:
  // such a setup used to succeed with 0 modules, and 35,297 records of four libraries were lost without a word (8 Nov 2026). It stops here, and leaves no empty queue for the next run to keep.
  if (stats.records && stats.kept === 0) {
    rmSync(QUEUE, { force: true })
    const tops = [...skippedTops].sort((x, y) => y[1] - x[1]).slice(0, 5).map(([t, n]) => `${t} (${n})`).join(", ")
    fail(
      `seed: none of the ${stats.records} records was kept (outside the roots ${[...roots].join(", ")}: ${stats.skippedRoot}${tops ? `, paths starting with ${tops}` : ""}; no file: ${stats.skippedNoFile}; duplicates: ${stats.skippedDup}; commented out: ${stats.skippedCommented}): fix the roots or the layout of ${key} in sources.json`,
    )
  }
  log(`seed: ${[...fileCache.values()].filter(Boolean).length} source file(s) kept at the end`) // a missing file is cached as null: not a file kept
  log(`seeded ${QUEUE}: ${JSON.stringify(stats)}`)
  return { entries, stats }
}

// ---- 4. build -------------------------------------------------------------------
// Lake resolves the library's dependencies first. A dependency pinned to a commit that no branch holds (padic-l-functions, 7 Nov 2026: "fatal: unable to read tree") is fetched
// by its hash and Lake runs again (pinned-deps.mjs); any other failure is left to the steps after it, which report it as before.
async function ensureDeps() {
  for (let i = 0; i < 5; i++) {
    const r = await run("lake", ["env", "true"], { cwd: REPO, timeoutMs: 90 * 60 * 1000 })
    if (r.code === 0) return true
    const { fetched, failed } = repairPins(REPO, r.tail, { log })
    for (const f of failed) log(`WARNING: dependency ${f.pkg} at ${f.rev.slice(0, 12)} cannot be checked out: ${f.why}`)
    if (!fetched.length) return false
  }
  return false
}

async function mathlibCache() {
  await ensureDeps()
  const manifest = join(REPO, "lake-manifest.json")
  const hasMathlib = existsSync(manifest) && /"name":\s*"mathlib"/.test(readFileSync(manifest, "utf8"))
  if (hasMathlib) {
    const r = await run("lake", ["exe", "cache", "get"], { cwd: REPO, timeoutMs: 90 * 60 * 1000 })
    if (r.code !== 0 && !(await online())) fail(`lake exe cache get exited ${r.code} while offline — rerun when the network is back`)
    if (r.code !== 0) log(`WARNING: lake exe cache get exited ${r.code}: ${r.tail.slice(-300)} — building from source`)
  }
  return hasMathlib
}

// Builds one module that the watchdog killed, with the machine to itself (the other chunks have finished) and a higher limit; true when it now has an .olean.
let aloneResult = { code: 0, errors: "", tail: "" } // what the last build alone answered
async function buildAlone(m) {
  footprintLimit = RETRY_FOOTPRINT_MB
  try {
    const r = await run("lake", ["build", m], { cwd: REPO, timeoutMs: SOLO_BUILD_MS })
    aloneResult = r
    if (r.code !== 0) log(`WARNING: lake build ${m} (alone) exited ${r.code}`)
  } finally {
    footprintLimit = FOOTPRINT_MB
  }
  return existsSync(oleanOf(m))
}

async function build(modules) {
  const hasMathlib = await mathlibCache()
  // Only the modules that carry entries (and, through lake, what they import).
  const toobig = loadOom({ prune: true })
  // Modules not built again in THIS run: the too-big ones of earlier rounds, and any that was killed but not built alone (the cap) or failed alone for another reason.
  // Only toobig is written down for the next round; the others get another go then.
  // ... and the modules an earlier round found broken (they do not compile at this commit; BROKEN_FILE): not handed to lake again, nor what imports them
  const avoid = new Set([...toobig.keys(), ...loadBroken().keys()])
  let blocker = blockedBy(avoid, modules)
  if (toobig.size) log(`memory: ${toobig.size} modules did not fit in ${RETRY_FOOTPRINT_MB} MB in an earlier round; they and the ${[...blocker.keys()].filter((m) => !avoid.has(m)).length} modules that import them are not built again`)
  let solos = 0
  // After a failed chunk: every module the watchdog killed is built again alone. True when one of them now exists, so that the chunk is worth a second go.
  const settle = async () => {
    let rescued = false
    for (const [m, k] of [...oomKilled]) {
      oomKilled.delete(m)
      if (existsSync(oleanOf(m)) || avoid.has(m)) continue
      if (solos >= SOLO_MAX) {
        log(`memory: ${m} was killed at ${k.mb} MB; ${SOLO_MAX} modules were built alone in this run already, so it waits for the next round`)
        avoid.add(m)
        blocker = blockedBy(avoid, modules)
        continue
      }
      solos++
      log(`memory: ${m} was killed at ${k.mb} MB (${k.why}); building it alone, limit ${RETRY_FOOTPRINT_MB} MB`)
      if (await buildAlone(m)) {
        log(`memory: ${m} built alone`)
        rescued = true
        continue
      }
      avoid.add(m)
      const retryKill = oomKilled.get(m)
      oomKilled.delete(m)
      if (!retryKill) {
        // failed alone, but not killed: a compile error or a timeout, not memory. Not written down as too big (that would block its importers for good). An error in its own file means it does
        // not compile at this commit, and the probe at the end of the round never reaches a module left out here (aintlib, 9 Nov 2026: ModularCurves.EllipticCurve.ProjectiveSpaceTwist).
        const err = brokenAlone(aloneResult, pathOfModule(m), SRCDIRS, OWN)
        if (err) {
          const known = loadBroken()
          known.set(m, { error: err })
          saveBroken(known)
          log(`broken: ${m} does not compile at this commit (${err}); it and the modules that import it are left out, the rest is exported`)
        } else {
          log(`memory: ${m} failed alone without a watchdog kill (a compile error or a timeout?): not recorded as too big, tried again next round`)
        }
        blocker = blockedBy(avoid, modules)
        continue
      }
      const peak = Math.max(k.mb, retryKill.mb)
      toobig.set(m, { peakMB: peak, capMB: RETRY_FOOTPRINT_MB })
      saveOom(toobig)
      blocker = blockedBy(avoid, modules)
      log(`memory: ${m} did not build alone either (killed at ${peak} MB, limit ${RETRY_FOOTPRINT_MB} MB): it and the ${[...blocker.entries()].filter(([x, b]) => b === m && x !== m).length} modules that import it are left out`)
    }
    return rescued
  }
  for (let i = 0; i < modules.length; i += BUILD_CHUNK) {
    let chunk = modules.slice(i, i + BUILD_CHUNK).filter((m) => !blocker.has(m))
    for (let attempt = 0; chunk.length && attempt < BUILD_ATTEMPTS; attempt++) {
      const r = await run("lake", ["build", ...chunk], { cwd: REPO, timeoutMs: 6 * 3600 * 1000 })
      if (r.code === 0) break
      log(`WARNING: lake build chunk ${i / BUILD_CHUNK + 1} exited ${r.code}: ${r.tail.slice(-400)} — modules that did not build are reported at export`)
      if (!(await settle())) break
      chunk = chunk.filter((m) => !blocker.has(m) && !existsSync(oleanOf(m)))
    }
  }
  // Modules still without an .olean whose library imports are all built and that are not left out for memory: built alone once more; one that fails with an error in its
  // own file (and no watchdog kill) does not compile at this commit and is written down as broken (BROKEN_FILE).
  const broken = loadBroken()
  let probed = 0
  for (const m of modules) {
    if (probed >= BROKEN_PROBE_MAX) break
    if (existsSync(oleanOf(m)) || blocker.has(m) || broken.has(m)) continue
    const own = (importsOf(m) ?? []).filter((i) => importsOf(i) !== null)
    if (!own.every((i) => existsSync(oleanOf(i)))) continue
    probed++
    oomKilled.delete(m)
    const r = await run("lake", ["build", m], { cwd: REPO, timeoutMs: SOLO_BUILD_MS })
    if (existsSync(oleanOf(m)) || oomKilled.has(m) || r.code === 124) continue
    const err = ownError(m, `${r.errors}\n${r.tail}`)
    if (err) {
      broken.set(m, { error: err })
      saveBroken(broken) // at once: a job that runs out of time later must not lose what was found
      log(`broken: ${m} does not compile at this commit (${err}); it and the modules that import it are left out, the rest is exported`)
    }
  }
  // None of the modules built (an invalid lake flag, a dependency that failed to fetch): writing setup.json
  // now would record a library with 0 exports as done — zkevm-clean, aisafety-atlas and algolean were.
  const built = modules.filter((m) => existsSync(oleanOf(m))).length
  // ... counting only the modules that can be built: a module recorded as not compiling at this commit (BROKEN_FILE) or too big, and what imports one, is not a sign of a broken build. tnlean, 2026-11-07: the export
  // shard that held its one broken file had nothing else left to build, stopped here ("none of the 1 modules"), never recorded the module as failed, and the rounds went on forever.
  const buildable = modules.filter((m) => !blocker.has(m)) // a module left out for memory or as broken, or one that imports such a module, cannot be built
  if (buildable.length && !buildable.some((m) => existsSync(oleanOf(m)))) fail(`lake build produced none of the ${buildable.length} modules — not recording this library as set up`)
  log(`build: ${built}/${modules.length} modules have an .olean`)
  // A Mathlib the cache did not serve (a pin off Mathlib's master) was compiled here, hours of
  // work: pack it into the local cache, which lives on until the toolchain group ends, so the
  // next library pinning the same commit gets it from `cache get` instead of compiling it again.
  if (hasMathlib && !PHASE) {
    const r = await run("lake", ["exe", "cache", "pack"], { cwd: REPO, timeoutMs: 60 * 60 * 1000 })
    if (r.code !== 0) log(`WARNING: lake exe cache pack exited ${r.code}: ${r.tail.slice(-300)}`)
  }
}

// ---- 5. lean4export on this toolchain --------------------------------------------
async function ensureLean4export() {
  // A build from before the --batch patch (scripts/patch-lean4export.py) is rebuilt: its exports would
  // fall back to one process per module. So is one built with another patch than the script has now (from a fresh clone: the patch is idempotent).
  const batchable = existsSync(join(L4E_DIR, "Main.lean")) && readFileSync(join(L4E_DIR, "Main.lean"), "utf8").includes("runBatch")
  const current = patchFingerprint(existsSync(PATCH_SCRIPT) ? readFileSync(PATCH_SCRIPT, "utf8") : null)
  const action = exporterAction({ binExists: existsSync(L4E_BIN), batchable, recorded: existsSync(PATCH_MARK) ? readFileSync(PATCH_MARK, "utf8") : null, current })
  if (action === "reuse") return log(`lean4export present: ${L4E_BIN}`)
  if (action === "rebuild") log(`lean4export at ${L4E_DIR} predates --batch: rebuilding`)
  if (action === "rebuild-clean") {
    log(`lean4export at ${L4E_DIR} was built with another version of scripts/patch-lean4export.py: rebuilding from a fresh clone`)
    rmSync(L4E_DIR, { recursive: true, force: true })
  }
  const r = await run("bash", [join(APP_ROOT, "scripts", "build-lean4export.sh"), src.toolchain, L4E_DIR], { timeoutMs: 40 * 60 * 1000 })
  if (r.code !== 0 || !existsSync(L4E_BIN)) fail(`lean4export build for ${src.toolchain}: ${r.tail.slice(-600)}`)
  if (current) writeAtomic(PATCH_MARK, current + "\n")
}

// ---- 6. exports -----------------------------------------------------------------
async function closures(modules) {
  // A module the build did not produce would fail its whole batch (tnlean: one missing
  // .olean sent 1,156 modules down the one-process-each path, a minute apiece). Skip
  // those up front; the export step reports them as unbuilt.
  const unbuilt = new Set(modules.filter((m) => !existsSync(oleanOf(m))))
  if (unbuilt.size) log(`closures: ${unbuilt.size} modules have no .olean — skipped: ${[...unbuilt].slice(0, 6).join(", ")}${unbuilt.size > 6 ? ", …" : ""}`)
  let todo = modules.filter((m) => !unbuilt.has(m) && !existsSync(join(EXPORTS, `${m}.names.json`)))
  if (!todo.length) return log("closures: all present")
  // BIG modules first, each alone (memory-rules.mjs closureBigModules / aloneFirstMs): a module whose import closure is most of the library loses its time in batches. Measured only for a
  // short list (a round for a few named modules, like flt-anthropic's 86): counting the closure of every module of a 60,000-module library would cost more than it saves.
  if (todo.length <= 500) {
    const big = todo.filter((m) => libraryClosureSize(m, closureBigModules()) >= closureBigModules())
    for (let k = 0; k < big.length; k++) {
      const m = big[k]
      const limit = aloneFirstMs({ elapsedMs: Date.now() - STARTED_MS, budgetMs: CLOSURE_BUDGET_MS, left: big.length - k })
      if (!limit) {
        log(`closure: ${m} imports most of the library and the job's budget has no room left for it; it waits for the next round`)
        continue
      }
      log(`closure: ${m} imports most of the library: alone first, limit ${Math.round(limit / 1000)} s`)
      const r = await runCapture("lake", ["env", "lean", "-M", String(leanMB()), "--run", CLOSURE_LEAN, m.split(".")[0], m], { cwd: REPO, timeoutMs: limit, maxBuffer: 256 * 1024 * 1024 })
      if (r.code !== 0) log(`closure failed for ${m}: exit ${r.code} (${r.tail.slice(-300)})`)
      else {
        try {
          writeClosureSections(r.stdout)
        } catch (e) {
          log(`closure failed for ${m}: could not be written (${e.message})`)
        }
      }
    }
    const done = new Set(big)
    todo = todo.filter((m) => !done.has(m))
    if (!todo.length) return
  }
  // One process per root prefix (the closure is filtered by module prefix), all of its modules at once.
  const byPfx = new Map()
  for (const m of todo) byPfx.set(m.split(".")[0], [...(byPfx.get(m.split(".")[0]) || []), m])
  for (const [pfx, mods] of byPfx) {
    for (let i = 0; i < mods.length; i += CLOSURE_BATCH) {
      const chunk = mods.slice(i, i + CLOSURE_BATCH)
      log(`closure: ${chunk.length} modules under ${pfx} (${i + 1}-${i + chunk.length} of ${mods.length}); limits: a batch ${closureBatchMs(chunk.length) / 1000} s at most, one module alone ${CLOSURE_SINGLE_MS / 1000} s`)
      const runBatch = async (batch) => {
        const r = await runCapture("lake", ["env", "lean", "-M", String(leanMB()), "--run", CLOSURE_LEAN, pfx, ...batch], { cwd: REPO, timeoutMs: closureBatchMs(batch.length) })
        if (r.code !== 0) {
          log(`WARNING: closure batch of ${batch.length} failed, exit ${r.code} (${r.tail.slice(-600)})`)
          return false
        }
        try {
          writeClosureSections(r.stdout)
        } catch (e) {
          // as before: a section that cannot be read or written is a failed batch (logged, then halved), not the end of the setup
          log(`WARNING: closure batch of ${batch.length} could not be written (${e.message})`)
          return false
        }
        return true
      }
      const runOne = async (m) => {
        let r = await runCapture("lake", ["env", "lean", "-M", String(leanMB()), "--run", CLOSURE_LEAN, pfx, m], { cwd: REPO, timeoutMs: CLOSURE_SINGLE_MS, maxBuffer: 256 * 1024 * 1024 })
        if (r.code === 124) {
          // out of time alone: one more try with a longer limit while the job's budget holds it (memory-rules.mjs closureRetryMs); a module that needs more time is not a module that cannot be exported
          const longer = closureRetryMs({ singleMs: CLOSURE_SINGLE_MS, elapsedMs: Date.now() - STARTED_MS, budgetMs: CLOSURE_BUDGET_MS })
          if (longer > 0) {
            log(`closure: ${m} ran out of ${CLOSURE_SINGLE_MS / 1000} s alone; trying it once more with ${longer / 1000} s`)
            r = await runCapture("lake", ["env", "lean", "-M", String(leanMB()), "--run", CLOSURE_LEAN, pfx, m], { cwd: REPO, timeoutMs: longer, maxBuffer: 256 * 1024 * 1024 })
          } else log(`closure: ${m} ran out of ${CLOSURE_SINGLE_MS / 1000} s alone and the job's budget has no room for a longer try`)
        }
        if (r.code !== 0) return log(`closure failed for ${m}: exit ${r.code} (${r.tail.slice(-300)})`)
        try {
          writeClosureSections(r.stdout)
        } catch (e) {
          log(`closure failed for ${m}: could not be written (${e.message})`)
        }
      }
      await bisect(chunk, runBatch, runOne, "closure")
    }
  }
}
// How many modules of the library a module imports, itself included, directly or not; counting stops at `cap` (only "at least cap" matters).
function libraryClosureSize(m, cap) {
  const seen = new Set([m])
  const todo = [m]
  while (todo.length && seen.size < cap) {
    for (const d of importsOf(todo.pop()) ?? []) {
      if (!seen.has(d) && importsOf(d) !== null) {
        seen.add(d)
        todo.push(d)
      }
    }
  }
  return seen.size
}
function writeClosureSections(stdout) {
  let cur = null
  const acc = {}
  for (const raw of stdout.split("\n")) {
    const line = raw.trim()
    if (!line) continue
    if (line.startsWith("== ")) {
      cur = line.slice(3).trim()
      acc[cur] = { names: [], modules: new Set(), moduleOf: {}, deps: {} }
      continue
    }
    if (!cur) continue
    const [name, mod, depStr] = line.split("\t")
    if (!name) continue
    const a = acc[cur]
    a.names.push(name)
    if (mod) {
      a.modules.add(mod)
      a.moduleOf[name] = mod
    }
    a.deps[name] = depStr ? depStr.split(",").filter(Boolean) : []
  }
  for (const [m, a] of Object.entries(acc)) {
    if (!a.names.length) {
      log(`closure of ${m} is empty — not written`)
      continue
    }
    writeAtomic(join(EXPORTS, `${m}.names.json`), JSON.stringify({ names: a.names, modules: Array.from(a.modules), moduleOf: a.moduleOf, deps: a.deps }))
  }
}

function removeLeftovers() {
  for (const f of readdirSync(EXPORTS)) if (/\.tmp(-\d+)?$/.test(f) || /^\.batch-.*\.tsv$/.test(f)) rmSync(join(EXPORTS, f), { force: true })
}
async function exports(modules) {
  const failed = []
  const brokenHere = loadBroken()
  const todo = modules.filter((m) => !existsSync(join(EXPORTS, `${m}.ndjson`)))
  log(`exports: ${todo.length} to do, ${modules.length - todo.length} present, batches of ${EXPORT_BATCH}, concurrency ${CONCURRENCY}; limits: a batch ${EXPORT_BASE_MS / 1000} s + ${EXPORT_PER_MODULE_MS / 1000} s per module (at most 60 min), one module alone ${EXPORT_SINGLE_MS / 1000} s`)
  let done = 0
  const namesOf = (m) => {
    const namesPath = join(EXPORTS, `${m}.names.json`)
    return existsSync(namesPath) ? JSON.parse(readFileSync(namesPath, "utf8")).names : null
  }
  // The export is complete when it holds a declaration; then it takes its final name.
  const finish = async (m) => {
    const tmp = join(EXPORTS, `${m}.ndjson.tmp`)
    const has = existsSync(tmp) && (await x("grep", ["-q", "-m1", "-E", '"(thm|def|inductive|axiom)"', tmp], { env: ENV }).then(() => true, () => false))
    if (!has) {
      try { rmSync(tmp, { force: true }) } catch { /* nothing to remove */ }
      return false
    }
    renameSync(tmp, join(EXPORTS, `${m}.ndjson`))
    return true
  }
  const exportOne = async (m, names) => {
    const bytes = names.reduce((a, n) => a + n.length + 1, 0)
    if (bytes > 900 * 1024) return failed.push([m, `closure too large for argv (${names.length} names)`])
    try {
      // --only-listed (scripts/patch-lean4export.py): the closure's own constants, not everything they
      // reach in Mathlib. Streamed straight to the file: a Node string tops out around 512 MB, and
      // one Sendov module's export was bigger than that.
      const tmp = join(EXPORTS, `${m}.ndjson.tmp`)
      const r = await runToFile("lake", ["env", L4E_BIN, m, "--only-listed", "--", ...names], tmp, { cwd: REPO, timeoutMs: EXPORT_SINGLE_MS })
      if (r.code !== 0) throw new Error(`lean4export exited ${r.code}: ${r.tail.slice(-300)}`)
      if (!(await finish(m))) throw new Error("lean4export produced no declarations")
    } catch (e) {
      try { rmSync(join(EXPORTS, `${m}.ndjson.tmp`), { force: true }) } catch { /* nothing to remove */ }
      failed.push([m, (e.stderr || e.message || String(e)).toString().slice(-300).replace(/\s+/g, " ")])
    }
  }
  const worker = async () => {
    while (todo.length) {
      // Importing the environment is the whole cost of an export (tnlean: ~110 s per module for a
      // dump of a few seconds): a batch imports the union of its modules once (--batch, see
      // patch-lean4export.py). A batch that fails (two modules that cannot share an environment)
      // falls back to one process per module.
      const group = todo.splice(0, EXPORT_BATCH)
      const members = []
      for (const m of group) {
        const names = namesOf(m)
        if (!names) failed.push([m, brokenHere.has(m) ? `does not compile at the library's own commit: ${brokenHere.get(m).error}` : "no closure"])
        else members.push([m, names])
      }
      const runBatch = async (batch) => {
        const listPath = join(EXPORTS, `.batch-${process.pid}-${Math.random().toString(36).slice(2)}.tsv`)
        writeFileSync(listPath, batch.map(([m, names]) => [m, join(EXPORTS, `${m}.ndjson.tmp`), ...names].join("\t")).join("\n") + "\n")
        let r
        try {
          r = await run("lake", ["env", L4E_BIN, "--only-listed", `--batch=${listPath}`], { cwd: REPO, timeoutMs: exportBatchMs(batch.length) })
        } catch (e) {
          r = { code: -1, tail: String(e) }
        }
        try { rmSync(listPath, { force: true }) } catch { /* nothing to remove */ }
        if (r.code !== 0) {
          log(`WARNING: export batch of ${batch.length} exited ${r.code}: ${(r.tail || "").slice(-300).replace(/\s+/g, " ")}`)
          return false
        }
        // the batch went through: a member it left without a declaration is exported alone (as before)
        for (const [m, names] of batch) if (!(await finish(m))) await exportOne(m, names)
        return true
      }
      if (members.length) await bisect(members, runBatch, ([m, names]) => exportOne(m, names), "export")
      done += group.length
      log(`exports: ${done} done, ${todo.length} left, ${failed.length} failed`)
    }
  }
  await Promise.all(Array.from({ length: Math.max(1, CONCURRENCY) }, worker))
  return failed
}

function closureModules(modules) {
  const all = new Set(modules)
  for (const m of modules) {
    const p = join(EXPORTS, `${m}.names.json`)
    if (!existsSync(p)) continue
    try {
      for (const x of JSON.parse(readFileSync(p, "utf8")).modules || []) if (x) all.add(x)
    } catch {
      /* recomputed by closures() if unreadable */
    }
  }
  return Array.from(all).sort()
}

// ---- 6b. notation expansion -----------------------------------------------------
// scripts/expand-notations.lean, under the corpus's own toolchain: each module
// rewritten with the corpus's own notations expanded, so the text the bridge
// pastes is free of them (the tree's content lint refuses notation and macro
// declarations, and dropping a declaration breaks every use).
const EXPAND_LEAN = join(APP_ROOT, "scripts", "expand-notations.lean")
const EXPAND_CHUNK = Math.max(1, Number(process.env.EMISSARY_EXPAND_CHUNK || 1))
// Every notation, macro or syntax the corpus declares: the modules declaring one are always
// expanded (a `local` notation is usable only there), and a module can use a global one only if
// every atom (string literal) of its declaration occurs in the text — identifier-like atoms as
// whole tokens. Anything else needs no expansion: the bridge reads its raw source, which is what
// an all-verbatim expansion is. Expansion re-elaborates every file (tnlean: 1 of its first 155
// modules had anything to expand, minutes per chunk of 8; the filter keeps 89 of 1,227). Null
// when a global declaration has no atom, in which case every module is expanded as before.
const SYNTAX_DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:scoped(?:\[[^\]]*\])?|local)\s+)?(?:notation3?|macro|syntax|infixl?|infixr|prefix|postfix|elab)\b/
const LOCAL_DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)*local\s/
const SYNTAX_ABBREV_RE = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:scoped(?:\[[^\]]*\])?|local)\s+)?syntax\s+[^\s:"(]+\s*:=/
const IDENT_ATOM_RE = /^[\p{L}\p{N}_'.₀-₉]+$/u
function leanFilesUnder(dir) {
  const out = []
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, e.name)
    if (e.isDirectory()) out.push(...leanFilesUnder(p))
    else if (e.name.endsWith(".lean")) out.push(p)
  }
  return out
}
function corpusSyntax() {
  const decls = []
  const declaring = new Set()
  for (const root of src.roots) {
    const base = join(REPO, ...root.split("."))
    const files = [base + ".lean", ...(existsSync(base) && statSync(base).isDirectory() ? leanFilesUnder(base) : [])]
    for (const f of files) {
      if (!existsSync(f)) continue
      const lines = readFileSync(f, "utf8").split("\n")
      let depth = 0
      for (let i = 0; i < lines.length; i++) {
        const line = lines[i]
        if (depth === 0 && !/^\s*--/.test(line) && SYNTAX_DECL_RE.test(line)) {
          declaring.add(f)
          let cmd = line
          for (let j = i + 1; j < lines.length && /^\s+\S/.test(lines[j]); j++) cmd += "\n" + lines[j]
          // `syntax name := parser` only names a parser for other syntax declarations: nothing uses it
          // directly (formal-conjectures' `syntax subjectList := many(num)` had no atom and switched the
          // filter off, sending all 626 modules through the expander).
          if (!SYNTAX_ABBREV_RE.test(line) && !LOCAL_DECL_RE.test(line)) {
            const atoms = [...cmd.matchAll(/"((?:[^"\\]|\\.)*)"/g)].map((s) => s[1].trim()).filter(Boolean)
            if (!atoms.length) return null
            decls.push(atoms)
          }
        }
        depth = Math.max(0, depth + (line.match(/\/-/g) || []).length - (line.match(/-\//g) || []).length)
      }
    }
  }
  return { decls, declaring }
}
function occurs(text, atom) {
  if (!IDENT_ATOM_RE.test(atom)) return text.includes(atom)
  return new RegExp(`(?<![\\p{L}\\p{N}_'.₀-₉])${atom.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![\\p{L}\\p{N}_'.₀-₉])`, "u").test(text)
}
async function expand(modules) {
  const syntax = corpusSyntax()
  const mayUseNotation = (m) => {
    if (syntax === null) return true
    const p = join(REPO, pathOfModule(m))
    if (!existsSync(p) || syntax.declaring.has(p)) return true
    const text = readFileSync(p, "utf8")
    return syntax.decls.some((atoms) => atoms.every((a) => occurs(text, a)))
  }
  const missing = modules.filter((m) => !existsSync(join(EXPORTS, `${m}.expanded.lean`)))
  const unbuilt = missing.filter((m) => !existsSync(oleanOf(m)))
  if (unbuilt.length) log(`expand: ${unbuilt.length} modules have no .olean — skipped: ${unbuilt.slice(0, 6).join(", ")}${unbuilt.length > 6 ? ", …" : ""}`)
  const todo = missing.filter((m) => existsSync(oleanOf(m)) && mayUseNotation(m))
  log(
    `expand: ${todo.length} to do, ${modules.length - missing.length} present, ${missing.length - todo.length} cannot use a corpus notation (${syntax ? syntax.decls.length : "?"} global syntax declarations, ${syntax ? syntax.declaring.size : "?"} declaring modules), concurrency ${CONCURRENCY}`,
  )
  const failed = []
  const stats = { expanded: 0, verbatim: 0, unexpanded: 0 }
  const chunks = []
  // One module per process by default: the expander imports each module's own header separately anyway, so a
  // chunk saves only process start-up, while its imports pile up in one process (formal-conjectures: every
  // chunk of 8 passed 11 GB and was killed; each module alone went through).
  for (let i = 0; i < todo.length; i += EXPAND_CHUNK) chunks.push(todo.slice(i, i + EXPAND_CHUNK))
  let processed = 0
  const worker = async () => {
    while (chunks.length) {
      const chunk = chunks.shift()
      try {
        const { stdout } = await x("lake", ["env", "lean", "-M", String(leanMB()), "--run", EXPAND_LEAN, EXPORTS, src.roots.join(","), ...chunk], { cwd: REPO, env: ENV, maxBuffer: 64 * 1024 * 1024, timeout: 60 * 60 * 1000 })
        for (const line of stdout.split("\n")) {
          const [m, e, v, u] = line.split("\t")
          if (m && u != null) {
            stats.expanded += Number(e)
            stats.verbatim += Number(v)
            stats.unexpanded += Number(u)
          }
        }
        for (const m of chunk) if (!existsSync(join(EXPORTS, `${m}.expanded.lean`))) failed.push([m, "no output"])
      } catch (e) {
        // One bad module must not take its chunk down: retry each alone.
        for (const m of chunk) {
          try {
            await x("lake", ["env", "lean", "-M", String(leanMB()), "--run", EXPAND_LEAN, EXPORTS, src.roots.join(","), m], { cwd: REPO, env: ENV, maxBuffer: 64 * 1024 * 1024, timeout: 20 * 60 * 1000 })
          } catch (e2) {
            failed.push([m, (e2.stderr || e2.message || String(e2)).toString().slice(-300).replace(/\s+/g, " ")])
          }
        }
      }
      processed += chunk.length
      if (processed % 25 < chunk.length || !chunks.length) log(`expand: ${processed}/${todo.length} done, ${failed.length} failed`)
    }
  }
  await Promise.all(Array.from({ length: Math.max(1, CONCURRENCY) }, worker))
  log(`expand: commands expanded ${stats.expanded}, verbatim ${stats.verbatim}, unexpanded ${stats.unexpanded}; ${failed.length} modules failed`)
  return { failed, stats }
}

// ---- 7. cleanup -----------------------------------------------------------------
async function cleanup() {
  if (KEEP_BUILD) return log("keeping the build (--keep-build)")
  const lake = join(REPO, ".lake")
  if (existsSync(lake)) {
    rmSync(lake, { recursive: true, force: true })
    log(`removed ${lake}`)
  }
  // Pre-v4.3 Lake builds into build/ — removed only when git does not track anything there.
  const oldBuild = join(REPO, "build")
  if (existsSync(join(oldBuild, "lib")) && !(await x("git", ["ls-files", "build"], { cwd: REPO, env: ENV })).stdout.trim()) {
    rmSync(oldBuild, { recursive: true, force: true })
    log(`removed ${oldBuild}`)
  }
  // Mathlib's cache tool keeps every downloaded archive under ~/.cache/mathlib;
  // across a hundred libraries on different Mathlib commits that is hundreds of
  // GB. A re-download costs minutes; the disk does not come back. It is kept
  // until the toolchain group ends: libraries on one toolchain often pin the same
  // Mathlib commit, and one the cache never served was compiled and packed here.
  const mlcache = join(HOME, ".cache", "mathlib")
  if (UNINSTALL_TC && existsSync(mlcache)) {
    rmSync(mlcache, { recursive: true, force: true })
    log(`removed ${mlcache}`)
  }
  if (UNINSTALL_TC && !KEEP_TOOLCHAINS.has(src.toolchain)) {
    const r = await run("elan", ["toolchain", "uninstall", src.toolchain], { timeoutMs: 5 * 60 * 1000 })
    log(r.code === 0 ? `uninstalled ${src.toolchain}` : `WARNING: could not uninstall ${src.toolchain}: ${r.tail.slice(-200)}`)
  }
}

const dirSize = (p) => {
  try {
    return Number(execFileSync("du", ["-sk", p]).toString().split("\t")[0]) * 1024
  } catch {
    return 0
  }
}

// A runner already set this library up at this commit: its exports are committed, so this machine needs only
// the checkout (the bridge reads source text from it) and the queue. Nothing is built, no toolchain installed.
// Adopted only when every module that carries an entry was handled there (exported, or recorded as failed).
function adopt(entries, modules, stats, t0) {
  if (!existsSync(CI_RECORD)) return false
  let ci
  try {
    ci = JSON.parse(readFileSync(CI_RECORD, "utf8"))
  } catch {
    return false
  }
  if (ci.commit !== src.commit) {
    log(`runner record is for ${String(ci.commit).slice(0, 12)}, not ${src.commit.slice(0, 12)} — setting up here`)
    return false
  }
  // A library set up across runners keeps its machine exports in a release archive (ci.archive), which the bridge
  // downloads the first time a translation needs it: there the record, not the local files, says what was exported.
  const archived = ci.archive && ci.modules === modules.length && ci.exported + (ci.failed || []).length === ci.modules
  const handled = new Set([...(ci.failed || []).map((f) => f.module), ...modules.filter((m) => archived || existsSync(join(EXPORTS, `${m}.ndjson`)))])
  const missing = modules.filter((m) => !handled.has(m))
  if (missing.length) {
    log(`runner record does not cover ${missing.length} modules (${missing.slice(0, 3).join(", ")}) — setting up here`)
    return false
  }
  const report = {
    ...ci,
    corpusRoot: REPO,
    entries: entries.length,
    seed: stats,
    adoptedFrom: "setup.ci.json",
    minutes: Math.round((Date.now() - t0) / 60000),
    finishedAt: new Date().toISOString(),
  }
  writeAtomic(SETUP_JSON, JSON.stringify(report, null, 2))
  log(`adopted the runner's setup: ${ci.exported}/${ci.modules} modules exported on ${ci.toolchain} — nothing built here${archived ? ` (exports in ${ci.archive.asset}, downloaded on first use)` : ""}`)
  return true
}

// Swap for the big-memory round (EMISSARY_ADD_SWAP_GB, set by the prime job when swap_gb is not 0): added here, right after the earlier build is unpacked and its archive deleted,
// by scripts/add-swap.sh, which sizes it from the free space at this moment. Synchronous: no module is compiled before it is there, and a failure to add it stops the phase.
async function addSwap() {
  const gb = process.env.EMISSARY_ADD_SWAP_GB
  if (!gb || gb === "0") return
  if (!/^[1-9][0-9]{0,2}$/.test(gb)) fail(`EMISSARY_ADD_SWAP_GB is a number of GB, not ${gb}`)
  const r = await run("sh", [join(APP_ROOT, "scripts", "add-swap.sh"), gb, "25"], { timeoutMs: 10 * 60 * 1000 })
  if (r.code !== 0) fail(`could not add the swap for the big-memory round (add-swap.sh exited ${r.code}): ${r.tail.slice(-300)}`)
}

// Unpacks an earlier round's build over the checkout. A shard needs it (it is the prime's build); the prime
// itself uses it to carry on where the last round stopped, and goes without when the artifact has expired.
// The *.setup.json files (Lake's per-module setup, 7.6 MB each here, 89 GB for 11,792 modules) are never restored, also from a build packed before they were left out.
// ONLY THESE MODULES (EMISSARY_ONLY_MODULES, a comma list; setup-sharded.yml only_modules): the build and build-status phases look at these modules only, and the earlier build is
// restored for their closure only. For adding a few modules that could not be built before (flt-anthropic's 86 top-of-proof modules) to a library whose earlier build is far too big
// to unpack next to its own archive on one runner (the 16.5 GB archive of 30,000 modules: "No space left on device" twice, 5 Nov 2026). Names are checked: a typo must not look like a build.
function onlyModules() {
  const raw = process.env.EMISSARY_ONLY_MODULES
  if (!raw) return null
  const names = raw.split(",").map((s) => s.trim()).filter(Boolean)
  if (!raw.trim()) return null
  if (!names.length) fail(`EMISSARY_ONLY_MODULES holds no module name: ${raw.slice(0, 40)}`)
  for (const m of names) if (m.length > 300 || !MODULE_NAME.test(m)) fail(`EMISSARY_ONLY_MODULES: not a module name: ${m.slice(0, 80)}`)
  return new Set(names)
}
// the module and everything of the library it imports, directly or not
function closureOf(roots) {
  const seen = new Set()
  const stack = [...roots]
  while (stack.length) {
    const m = stack.pop()
    if (seen.has(m)) continue
    seen.add(m)
    for (const i of importsOf(m) ?? []) stack.push(i)
  }
  return seen
}
function restoreBuild({ required }) {
  if (!RESTORE) return Promise.resolve()
  if (!existsSync(resolve(RESTORE))) {
    if (required) fail(`no build to restore at ${RESTORE}`)
    log(`no earlier build at ${RESTORE}: building from what the checkout has`)
    return Promise.resolve()
  }
  const only = onlyModules()
  const unpack = async () => {
    if (!only) return run("tar", ["--zstd", "--exclude=*.setup.json", "-xf", resolve(RESTORE), "-C", REPO], { timeoutMs: 60 * 60 * 1000 })
    // the closure of the named modules only: list the archive, keep their files, unpack exactly those
    const keep = new Set([...closureOf(only)].map((m) => pathOfModule(m).replace(/\.lean$/, "")))
    const listFile = join(INFRA, "restore-listing.txt")
    const l = await runToFile("tar", ["--zstd", "-tf", resolve(RESTORE)], listFile, { timeoutMs: 30 * 60 * 1000 })
    if (l.code !== 0) return l
    const members = membersOf(readFileSync(listFile, "utf8"), keep)
    const pick = join(INFRA, "restore-members.txt")
    writeFileSync(pick, members.join("\n") + "\n")
    log(`restoring the closure of ${only.size} modules only: ${keep.size} modules, ${members.length} files of the archive`)
    rmSync(listFile, { force: true })
    if (!members.length) return { code: 0, tail: "" }
    return run("tar", ["--zstd", "-xf", resolve(RESTORE), "-C", REPO, "-T", pick], { timeoutMs: 60 * 60 * 1000 })
  }
  return unpack().then((r) => {
    if (r.code !== 0) fail(`could not restore the build from ${RESTORE}: ${r.tail.slice(-300)}`)
    // EMISSARY_DROP_RESTORED=1 (the prime job): the archive is not needed any more, and 16 GB of it is what the swap of the big-memory round has to be added from
    if (process.env.EMISSARY_DROP_RESTORED === "1") {
      try {
        rmSync(resolve(RESTORE), { force: true })
        log(`restored build unpacked; ${RESTORE} deleted to free its disk space`)
      } catch (e) {
        // the swap is sized from the space this frees: without it the big-memory round would run with less swap than it asked for, or none
        if (process.env.EMISSARY_ADD_SWAP_GB && process.env.EMISSARY_ADD_SWAP_GB !== "0") fail(`could not delete ${RESTORE}, which the swap of the big-memory round needs the space of: ${e.message}`)
        log(`WARNING: could not delete ${RESTORE}: ${e.message}`)
      }
    }
  })
}

// How much of the library is compiled. Runs no Lean and no lake, so it is safe to run after the build step in
// the job that ran the library's own code; the workflow reads only the lines `complete=true|false`, `built=<n>` and `modules=<n>` from it (each cut down to its shape).
function buildStatus(modules) {
  const missing = modules.filter((m) => !existsSync(oleanOf(m)))
  const built = modules.length - missing.length
  const toobig = loadOom()
  const broken = loadBroken()
  const blocker = blockedBy(new Set([...toobig.keys(), ...broken.keys()]), modules)
  const blockedMissing = missing.filter((m) => blocker.has(m) && !toobig.has(m) && !broken.has(m))
  const other = missing.filter((m) => !blocker.has(m))
  const status = {
    key,
    commit: src.commit,
    modules: modules.length,
    built,
    // complete: nothing more can be built. Every module is built, or is missing only because it was killed for memory even alone (toobig) or imports one that was (blocked):
    // another round adds nothing then (flt-anthropic, 2 Nov 2026: round 37 added 0 of 84 and the chain stopped with an error instead of going on to the shards)
    complete: other.length === 0,
    // Why modules are missing, as far as it is known: killed for memory (and not built alone either), blocked behind one of those, and the rest (an error, or not tried yet).
    toobig: [...toobig].map(([module, v]) => ({ module, peakMB: v.peakMB, capMB: v.capMB, blocks: [...blocker].filter(([x, b]) => b === module && x !== module).length })),
    // does not compile at the library's own commit (an error in its own file, every import built): left out with what imports it
    broken: [...broken].filter(([m]) => missing.includes(m)).map(([module, v]) => ({ module, error: v.error })),
    blocked: blockedMissing.length,
    other: other.length,
    otherSample: other.slice(0, 20),
    at: new Date().toISOString(),
  }
  writeAtomic(join(INFRA, "build-status.json"), JSON.stringify(status, null, 2))
  const md = [`### Modules without an .olean: ${missing.length} of ${modules.length}`, ""]
  if (status.toobig.length) {
    md.push(`Killed for memory, and not built alone either (${status.toobig.length}):`, "")
    for (const t of status.toobig.slice(0, 20)) md.push(`- \`${t.module}\`: killed at ${t.peakMB} MB with a limit of ${t.capMB} MB; ${t.blocks} modules import it`)
    md.push("")
  }
  if (status.broken.length) {
    md.push(`Do not compile at the library's own commit (${status.broken.length}):`, "")
    for (const b of status.broken.slice(0, 20)) md.push(`- \`${b.module}\`: ${b.error.replace(/`/g, "'")}`)
    md.push("")
  }
  md.push(`${blockedMissing.length} modules wait behind those; ${other.length} are missing for another reason${other.length ? ", first: " + other.slice(0, 5).map((m) => `\`${m}\``).join(", ") : ""}.`)
  writeAtomic(join(INFRA, "unbuilt-summary.md"), md.join("\n") + "\n")
  log(`build status: ${built}/${modules.length} modules have an .olean; ${toobig.size} too big, ${status.broken.length} do not compile, ${blockedMissing.length} behind them, ${other.length} other`)
  console.log(`built=${built}`)
  console.log(`modules=${modules.length}`)
  console.log(`toobig=${toobig.size}`)
  console.log(`blocked=${blockedMissing.length}`)
  console.log(`complete=${status.complete}`)
}

// ---- sharded setup (.github/workflows/setup-sharded.yml) ----------------------------
const SHARD_DIR = join(EXPORTS, ".shards")

async function shard(modules, t0) {
  await mathlibCache() // resolves the packages, and Mathlib's .oleans, before the build is laid over them
  await restoreBuild({ required: Boolean(RESTORE) })
  const entryModules = new Set(modules)
  const mine = modules.filter(inShard)
  log(`shard ${SHARD.i}/${SHARD.n}: ${mine.length} of ${modules.length} modules`)
  // what neither the build phase nor an earlier round reached: a module exported in an earlier round is done
  await build(mine.filter((m) => !existsSync(join(EXPORTS, `${m}.ndjson`))))
  await withSoloLimit("closures", () => closures(mine))
  // A module that carries entries is expanded by its own shard; one that only appears in closures is expanded
  // by every shard that needs it (the same text, so the commits merge).
  const expansion = await withSoloLimit("expand", () => expand(closureModules(mine).filter((m) => !entryModules.has(m) || inShard(m))))
  await ensureLean4export()
  const failed = await withSoloLimit("exports", () => exports(mine))
  const record = {
    shard: SHARD.i,
    shards: SHARD.n,
    commit: src.commit,
    toolchain: src.toolchain,
    modules: mine.length,
    exported: mine.filter((m) => existsSync(join(EXPORTS, `${m}.ndjson`))).length,
    failed: failed.map(([m, why]) => ({ module: m, why })),
    expansion: { ...expansion.stats, failed: expansion.failed.map(([m, why]) => ({ module: m, why })) },
    tools: await toolsNow(),
    minutes: Math.round((Date.now() - t0) / 60000),
    finishedAt: new Date().toISOString(),
  }
  mkdirSync(SHARD_DIR, { recursive: true })
  writeAtomic(join(SHARD_DIR, `${SHARD.i}-of-${SHARD.n}.json`), JSON.stringify(record, null, 2))
  log(`shard ${SHARD.i}/${SHARD.n} done: ${record.exported}/${mine.length} exported, ${failed.length} failed, ${record.minutes} min`)
}

// Every module exported, or recorded as failed by a shard that finished (on this commit): then setup.json.
// Anything else is not done — dispatch the workflow again and the shards carry on from what is committed.
function finish(entries, modules, stats, t0) {
  const records = existsSync(SHARD_DIR)
    ? readdirSync(SHARD_DIR)
        .filter((f) => /^\d+-of-\d+\.json$/.test(f))
        .map((f) => JSON.parse(readFileSync(join(SHARD_DIR, f), "utf8")))
        .filter((r) => r.commit === src.commit)
    : []
  const exported = new Set(modules.filter((m) => existsSync(join(EXPORTS, `${m}.ndjson`))))
  const why = new Map(records.flatMap((r) => r.failed.map((f) => [f.module, f.why])))
  const missing = modules.filter((m) => !exported.has(m) && !why.has(m))
  if (missing.length) {
    log(`not finished: ${missing.length} of ${modules.length} modules neither exported nor recorded as failed (${missing.slice(0, 3).join(", ")}) — dispatch again`)
    return
  }
  const failed = modules.filter((m) => !exported.has(m)).map((m) => ({ module: m, why: why.get(m) }))
  const sum = (k) => records.reduce((a, r) => a + (r.expansion?.[k] || 0), 0)
  const report = {
    key,
    repo: src.repo,
    commit: src.commit,
    toolchain: src.toolchain,
    roots: src.roots,
    corpusRoot: REPO,
    entries: entries.length,
    modules: modules.length,
    exported: exported.size,
    failed,
    expansion: { expanded: sum("expanded"), verbatim: sum("verbatim"), unexpanded: sum("unexpanded"), failed: records.flatMap((r) => r.expansion?.failed || []) },
    seed: stats,
    sharded: { records: records.length, shards: [...new Set(records.map((r) => r.shards))] },
    // the finish job runs no Lean: the tools are the ones the shards (which did) wrote into their records; a field they disagree on holds every value
    ...(mergeTools(records.map((r) => r.tools)) ? { tools: mergeTools(records.map((r) => r.tools)) } : {}),
    exportsBytes: dirSize(EXPORTS),
    minutes: Math.round((Date.now() - t0) / 60000) + records.reduce((a, r) => Math.max(a, r.minutes || 0), 0),
    finishedAt: new Date().toISOString(),
  }
  writeAtomic(SETUP_JSON, JSON.stringify(report, null, 2))
  log(`done ${key} (sharded): ${exported.size}/${modules.length} modules exported, ${failed.length} failed, from ${records.length} shard records — ${SETUP_JSON}`)
}

// ---- memory watchdog ------------------------------------------------------------
// `lean -M` counts resident memory, and macOS compresses a runaway's pages instead of keeping them
// resident: a notation expansion reached 33 GB (30 GB compressed, 3 GB resident) far past an 11 GB cap.
// Every 10 s this reads the real footprint of every process under this one (macOS: top's MEM, which
// counts compressed pages; Linux: VmRSS + VmSwap) and kills any process over EMISSARY_FOOTPRINT_MB
// (default 10240). The killed command fails like any other and its module is recorded as failed.
const FOOTPRINT_MB = Number(process.env.EMISSARY_FOOTPRINT_MB || 10240)
let footprintLimit = FOOTPRINT_MB // raised while a module killed for its memory is built alone (buildAlone)
// The phases after the build (closures, notation expansion, exports) run one Lean process at a time by default (--concurrency 1), and
// each imports the whole environment of a batch of modules, which for a deep library is most of the library: flt-anthropic, 3-4 Nov 2026,
// every closure process, a batch of 350-600 modules or a single module, was killed at 10.3-11.8 GB under the 10 GB limit, 62 of 64 shards
// ran to their 300-minute cap and exported nothing, and round 2 was going the same way. A process that has the machine to itself gets the
// limit a module built alone gets (EMISSARY_RETRY_FOOTPRINT_MB, 14 GB of a 16 GB runner; the available-memory guard below still protects
// the runner), and Lean's own heap cap (-M) follows it, so that the watchdog is what decides. With more than one process at a time the
// per-process limit stays what it was.
function soloLimitMB() {
  return CONCURRENCY <= 1 ? RETRY_FOOTPRINT_MB : FOOTPRINT_MB
}
async function withSoloLimit(what, fn) {
  const before = footprintLimit
  footprintLimit = soloLimitMB()
  log(`${what}: memory limit ${footprintLimit} MB per process (${CONCURRENCY <= 1 ? "one process at a time" : `${CONCURRENCY} at a time`})`)
  try {
    return await fn()
  } finally {
    footprintLimit = before
  }
}
function leanMB() {
  return Math.max(LEAN_MB, footprintLimit)
}
// A batch that fails (a memory kill, two modules that cannot share an environment) is split in two and each half tried, down to single
// modules: every batch that fits costs one environment import, instead of one import per module from the first failure on (flt-anthropic:
// one batch of 471 killed at once sent the shard down 471 single imports of ~11 GB each, past its 5 hours, for 129 files). `runBatch` says
// whether the batch went through; `runOne` handles a single module and its own failure.
const bisect = (items, runBatch, runOne, label) =>
  bisectItems(items, runBatch, runOne, (size, half) => log(`${label}: a batch of ${size} failed: trying its two halves (${half} and ${size - half})`))
const WATCH_MS = Number(process.env.EMISSARY_WATCH_MS) > 0 ? Number(process.env.EMISSARY_WATCH_MS) : 10000
const UNIT_MB = { B: 1 / 1048576, K: 1 / 1024, M: 1, G: 1024, T: 1048576 }
function descendants(root) {
  const kids = new Map()
  for (const line of execFileSync("ps", ["-A", "-o", "pid=,ppid="]).toString().trim().split("\n")) {
    const [pid, ppid] = line.trim().split(/\s+/).map(Number)
    kids.set(ppid, [...(kids.get(ppid) || []), pid])
  }
  const out = []
  for (const stack = [root]; stack.length; ) for (const c of kids.get(stack.pop()) || []) out.push(c), stack.push(c)
  return out
}
function footprintsMB(pids) {
  const want = new Set(pids)
  const out = new Map()
  if (!want.size) return out
  if (process.platform === "darwin") {
    for (const line of execFileSync("top", ["-l", "1", "-stats", "pid,mem"]).toString().split("\n")) {
      const m = line.match(/^\s*(\d+)\s+([\d.]+)([BKMGT])[+-]?\s*$/)
      if (m && want.has(Number(m[1]))) out.set(Number(m[1]), Number(m[2]) * UNIT_MB[m[3]])
    }
  } else {
    for (const pid of want) {
      try {
        const st = readFileSync(`/proc/${pid}/status`, "utf8")
        const kb = (k) => Number((st.match(new RegExp(`^${k}:\\s+(\\d+)`, "m")) || [0, 0])[1])
        out.set(pid, (kb("VmRSS") + kb("VmSwap")) / 1024)
      } catch {
        /* exited */
      }
    }
  }
  return out
}
function killProcess(pid, mb, why) {
  let cmd = "?"
  try {
    cmd = execFileSync("ps", ["-o", "command=", "-p", String(pid)]).toString().trim()
  } catch {
    /* exited */
  }
  process.kill(pid, "SIGKILL")
  // The module first: the command line is cut at 160 characters, and the module's name sits after the toolchain's and the project's paths (2026-10-29: 9 kills, none named).
  const mod = moduleOfCommand(cmd)
  if (mod) oomKilled.set(mod, { mb: Math.max(oomKilled.get(mod)?.mb ?? 0, Math.round(mb)), why })
  log(`memory watchdog: killed ${pid} at ${Math.round(mb)} MB (${why})${mod ? `, module ${mod}` : ""}: ${cmd.slice(0, 160)}`)
}
function watchMemory() {
  try {
    for (const [pid, mb] of footprintsMB(descendants(process.pid))) {
      if (mb > footprintLimit) killProcess(pid, mb, `limit ${footprintLimit} MB`)
    }
  } catch (e) {
    log(`memory watchdog: ${e.message}`)
  }
}
// Several processes under the per-process limit can still add up to more than the machine has: on a
// 16 GB runner, three Lean processes at 9 GB each. The runner then dies ("received a shutdown signal")
// and the whole round is lost, where killing the biggest process only fails one module. On Linux the
// kernel's own MemAvailable (free memory plus what can be reclaimed, so shared mapped .olean files are
// not counted twice) is read every 2 s; under EMISSARY_MIN_AVAILABLE_MB (default 1536) the largest
// process is killed. Not on macOS, where compression makes the figure unreliable.
// A value that is not a positive number ("1536MB") falls back to the default; NaN would make every check a shortage.
const MIN_AVAILABLE_MB = Number(process.env.EMISSARY_MIN_AVAILABLE_MB) > 0 ? Number(process.env.EMISSARY_MIN_AVAILABLE_MB) : 1536
const COUNT_SWAP = process.env.EMISSARY_COUNT_SWAP === "1"
function availableMB() {
  return availableFrom(readFileSync("/proc/meminfo", "utf8"), COUNT_SWAP)
}
function watchAvailable() {
  try {
    const avail = availableMB()
    if (avail >= MIN_AVAILABLE_MB) return
    const sizes = [...footprintsMB(descendants(process.pid))].sort((a, b) => b[1] - a[1])
    if (sizes.length) killProcess(sizes[0][0], sizes[0][1], `only ${Math.round(avail)} MB left of the machine's memory, under ${MIN_AVAILABLE_MB} MB`)
  } catch (e) {
    log(`memory watchdog: ${e.message}`)
  }
}

async function main() {
  const t0 = Date.now()
  setInterval(watchMemory, WATCH_MS).unref()
  if (process.platform === "linux") setInterval(watchAvailable, 2000).unref()
  removeLeftovers()
  log(`setup ${key}: ${src.repo} @ ${src.commit.slice(0, 12)} on ${src.toolchain}, roots ${src.roots.join(", ")}`)
  await ensureClone()
  const { entries, stats } = seedQueue()
  let modules = Array.from(new Set(entries.map((e) => moduleOfPath(e.sourcePath)))).sort()
  const only = PHASE === "build" || PHASE === "build-status" || PHASE === "shard" ? onlyModules() : null
  if (only) {
    const unknown = [...only].filter((m) => !modules.includes(m))
    if (unknown.length) fail(`EMISSARY_ONLY_MODULES names modules with no entries in ${key}: ${unknown.slice(0, 5).join(", ")}`)
    modules = modules.filter((m) => only.has(m))
    log(`only ${modules.length} named modules are built and judged (EMISSARY_ONLY_MODULES)`)
  }
  log(`${entries.length} entries in ${modules.length} modules`)
  if (ONLY === "seed") return
  if (PHASE === "finish") return finish(entries, modules, stats, t0)
  if (PHASE === "build-status") return buildStatus(modules)
  if (!ONLY && !PHASE && adopt(entries, modules, stats, t0)) return
  await ensureToolchain()
  if (PHASE === "build") {
    await restoreBuild({ required: false })
    await addSwap()
    await build(modules)
    return log(`done ${key} (build phase): the build stays for the shards`)
  }
  if (PHASE === "shard") return shard(modules, t0)
  if (ONLY !== "export") await build(modules)
  await withSoloLimit("closures", () => closures(modules))
  const expansion = await withSoloLimit("expand", () => expand(closureModules(modules)))
  if (ONLY === "expand") {
    await cleanup()
    return log(`done ${key} (expand only): ${JSON.stringify(expansion.stats)}, ${expansion.failed.length} failed`)
  }
  await ensureLean4export()
  const failed = await withSoloLimit("exports", () => exports(modules))
  const exported = modules.filter((m) => existsSync(join(EXPORTS, `${m}.ndjson`)))
  const report = {
    key,
    repo: src.repo,
    commit: src.commit,
    toolchain: src.toolchain,
    roots: src.roots,
    corpusRoot: REPO,
    entries: entries.length,
    modules: modules.length,
    exported: exported.length,
    failed: failed.map(([m, why]) => ({ module: m, why })),
    expansion: { ...expansion.stats, failed: expansion.failed.map(([m, why]) => ({ module: m, why })) },
    seed: stats,
    tools: await toolsNow(),
    exportsBytes: dirSize(EXPORTS),
    minutes: Math.round((Date.now() - t0) / 60000),
    finishedAt: new Date().toISOString(),
  }
  writeAtomic(SETUP_JSON, JSON.stringify(report, null, 2))
  log(`exports: ${exported.length}/${modules.length} modules (${failed.length} failed) → ${EXPORTS}`)
  for (const [m, why] of failed.slice(0, 15)) log(`  failed ${m}: ${why}`)
  await cleanup()
  log(`done ${key} in ${report.minutes} min — ${SETUP_JSON}`)
}
main().catch((e) => fail(e?.stack || e?.message || String(e)))

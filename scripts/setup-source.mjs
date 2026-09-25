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
import { execFile, execFileSync, spawn } from "node:child_process"
import { closeSync, existsSync, mkdirSync, openSync, readFileSync, renameSync, rmSync, writeFileSync, readdirSync, statSync } from "node:fs"
import os from "node:os"
import { basename, dirname, join, resolve } from "node:path"
import { fileURLToPath } from "node:url"
import { promisify } from "node:util"

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

// Streams a long command's output to our stdout (lake build progress) and resolves with its exit code.
function run(cmd, args, { cwd = APP_ROOT, timeoutMs = 4 * 3600 * 1000, quiet = false } = {}) {
  return new Promise((res) => {
    if (!quiet) log(`$ ${cmd} ${args.join(" ")}  (cwd ${cwd})`)
    const p = spawn(cmd, args, { cwd, env: ENV, stdio: ["ignore", "pipe", "pipe"] })
    let tail = ""
    const onData = (d) => {
      const s = d.toString()
      tail = (tail + s).slice(-4000)
      if (!quiet) process.stdout.write(s)
    }
    p.stdout.on("data", onData)
    p.stderr.on("data", onData)
    const t = setTimeout(() => {
      p.kill("SIGKILL")
      res({ code: 124, tail: tail + `\n[timed out after ${timeoutMs / 1000}s]` })
    }, timeoutMs)
    p.on("close", (code) => {
      clearTimeout(t)
      res({ code: code ?? 1, tail })
    })
  })
}
// Like run(), with stdout written to `outPath` (stderr captured for the report).
function runToFile(cmd, args, outPath, { cwd = APP_ROOT, timeoutMs = 4 * 3600 * 1000 } = {}) {
  return new Promise((res) => {
    const fd = openSync(outPath, "w")
    const p = spawn(cmd, args, { cwd, env: ENV, stdio: ["ignore", fd, "pipe"] })
    let tail = ""
    p.stderr.on("data", (d) => { tail = (tail + d.toString()).slice(-4000) })
    const t = setTimeout(() => { p.kill("SIGKILL"); closeSync(fd); res({ code: 124, tail: tail + `\n[timed out after ${timeoutMs / 1000}s]` }) }, timeoutMs)
    p.on("close", (code) => { clearTimeout(t); closeSync(fd); res({ code: code ?? 1, tail }) })
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
// Every file a later run treats as "done" is written whole or not at all: the setup can be killed at
// any moment (sleep, a closed network, a restart) and the next run skips whatever exists.
function writeAtomic(path, data) {
  const tmp = `${path}.tmp-${process.pid}`
  writeFileSync(tmp, data)
  renameSync(tmp, path)
}
// github.com reachable: a failure while offline is an interruption, not a verdict on the library.
const online = () => x("curl", ["-sI", "-m", "10", "https://github.com"], { env: ENV }).then(() => true, () => false)

// ---- 1. toolchain ---------------------------------------------------------------
async function ensureToolchain() {
  const { stdout } = await x("elan", ["toolchain", "list"], { env: ENV })
  if (stdout.split("\n").some((l) => l.trim().startsWith(src.toolchain))) return log(`toolchain ${src.toolchain} present`)
  const r = await run("elan", ["toolchain", "install", src.toolchain], { timeoutMs: 30 * 60 * 1000 })
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
  if (pinned && pinned !== src.toolchain) log(`WARNING: checkout pins ${pinned}, registry says ${src.toolchain} — using the checkout's`)
  if (pinned) src.toolchain = pinned
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
    const q = JSON.parse(readFileSync(QUEUE, "utf8"))
    log(`queue exists: ${QUEUE} (${q.length} entries) — keeping it (--reseed to rebuild)`)
    return { entries: q, stats: null }
  }
  for (const f of TENTATIVE_FILES) if (!existsSync(f)) fail(`no tentative file at ${f}`)
  const roots = new Set(src.roots)
  const seen = new Set()
  const fileCache = new Map()
  const fileOf = (p) => {
    if (!fileCache.has(p)) {
      const abs = join(REPO, p)
      if (!existsSync(abs)) fileCache.set(p, null)
      else {
        const lines = readFileSync(abs, "utf8").split("\n")
        fileCache.set(p, { lines, depth: commentDepths(lines) })
      }
    }
    return fileCache.get(p)
  }
  const entries = []
  for (const raw of TENTATIVE_FILES.flatMap((f) => readFileSync(f, "utf8").split("\n"))) {
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
    if (!roots.has(path.split("/")[0]) || path.includes("..")) {
      stats.skippedRoot++
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
    entries.push({
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
    })
    stats.kept++
  }
  writeAtomic(QUEUE, JSON.stringify(entries, null, 2))
  log(`seeded ${QUEUE}: ${JSON.stringify(stats)}`)
  return { entries, stats }
}

// ---- 4. build -------------------------------------------------------------------
async function build(modules) {
  const manifest = join(REPO, "lake-manifest.json")
  const hasMathlib = existsSync(manifest) && /"name":\s*"mathlib"/.test(readFileSync(manifest, "utf8"))
  if (hasMathlib) {
    const r = await run("lake", ["exe", "cache", "get"], { cwd: REPO, timeoutMs: 90 * 60 * 1000 })
    if (r.code !== 0 && !(await online())) fail(`lake exe cache get exited ${r.code} while offline — rerun when the network is back`)
    if (r.code !== 0) log(`WARNING: lake exe cache get exited ${r.code}: ${r.tail.slice(-300)} — building from source`)
  }
  // Only the modules that carry entries (and, through lake, what they import).
  for (let i = 0; i < modules.length; i += BUILD_CHUNK) {
    const chunk = modules.slice(i, i + BUILD_CHUNK)
    const r = await run("lake", ["build", ...chunk], { cwd: REPO, timeoutMs: 6 * 3600 * 1000 })
    if (r.code !== 0) log(`WARNING: lake build chunk ${i / BUILD_CHUNK + 1} exited ${r.code}: ${r.tail.slice(-400)} — modules that did not build are reported at export`)
  }
  // None of the modules built (an invalid lake flag, a dependency that failed to fetch): writing setup.json
  // now would record a library with 0 exports as done — zkevm-clean, aisafety-atlas and algolean were.
  const built = modules.filter((m) => existsSync(oleanOf(m))).length
  if (modules.length && !built) fail(`lake build produced none of the ${modules.length} modules — not recording this library as set up`)
  log(`build: ${built}/${modules.length} modules have an .olean`)
  // A Mathlib the cache did not serve (a pin off Mathlib's master) was compiled here, hours of
  // work: pack it into the local cache, which lives on until the toolchain group ends, so the
  // next library pinning the same commit gets it from `cache get` instead of compiling it again.
  if (hasMathlib) {
    const r = await run("lake", ["exe", "cache", "pack"], { cwd: REPO, timeoutMs: 60 * 60 * 1000 })
    if (r.code !== 0) log(`WARNING: lake exe cache pack exited ${r.code}: ${r.tail.slice(-300)}`)
  }
}

// ---- 5. lean4export on this toolchain --------------------------------------------
async function ensureLean4export() {
  // A build from before the --batch patch (scripts/patch-lean4export.py) is rebuilt: its exports would
  // fall back to one process per module.
  const batchable = existsSync(join(L4E_DIR, "Main.lean")) && readFileSync(join(L4E_DIR, "Main.lean"), "utf8").includes("runBatch")
  if (existsSync(L4E_BIN) && batchable) return log(`lean4export present: ${L4E_BIN}`)
  if (existsSync(L4E_BIN)) log(`lean4export at ${L4E_DIR} predates --batch: rebuilding`)
  const r = await run("bash", [join(APP_ROOT, "scripts", "build-lean4export.sh"), src.toolchain, L4E_DIR], { timeoutMs: 40 * 60 * 1000 })
  if (r.code !== 0 || !existsSync(L4E_BIN)) fail(`lean4export build for ${src.toolchain}: ${r.tail.slice(-600)}`)
}

// ---- 6. exports -----------------------------------------------------------------
async function closures(modules) {
  // A module the build did not produce would fail its whole batch (tnlean: one missing
  // .olean sent 1,156 modules down the one-process-each path, a minute apiece). Skip
  // those up front; the export step reports them as unbuilt.
  const unbuilt = new Set(modules.filter((m) => !existsSync(oleanOf(m))))
  if (unbuilt.size) log(`closures: ${unbuilt.size} modules have no .olean — skipped: ${[...unbuilt].slice(0, 6).join(", ")}${unbuilt.size > 6 ? ", …" : ""}`)
  const todo = modules.filter((m) => !unbuilt.has(m) && !existsSync(join(EXPORTS, `${m}.names.json`)))
  if (!todo.length) return log("closures: all present")
  // One process per root prefix (the closure is filtered by module prefix), all of its modules at once.
  const byPfx = new Map()
  for (const m of todo) byPfx.set(m.split(".")[0], [...(byPfx.get(m.split(".")[0]) || []), m])
  for (const [pfx, mods] of byPfx) {
    for (let i = 0; i < mods.length; i += CLOSURE_BATCH) {
      const chunk = mods.slice(i, i + CLOSURE_BATCH)
      log(`closure: ${chunk.length} modules under ${pfx} (${i + 1}-${i + chunk.length} of ${mods.length})`)
      let stdout = ""
      try {
        ;({ stdout } = await x("lake", ["env", "lean", "-M", String(LEAN_MB), "--run", CLOSURE_LEAN, pfx, ...chunk], { cwd: REPO, env: ENV, maxBuffer: 512 * 1024 * 1024, timeout: 60 * 60 * 1000 }))
      } catch (e) {
        log(`WARNING: closure batch failed (${(e.stderr || e.message || "").toString().slice(-600)}) — falling back to one module per process`)
        for (const m of chunk) {
          try {
            ;({ stdout } = await x("lake", ["env", "lean", "-M", String(LEAN_MB), "--run", CLOSURE_LEAN, pfx, m], { cwd: REPO, env: ENV, maxBuffer: 256 * 1024 * 1024, timeout: 20 * 60 * 1000 }))
            writeClosureSections(stdout)
          } catch (e2) {
            log(`closure failed for ${m}: ${(e2.stderr || e2.message || "").toString().slice(-300)}`)
          }
        }
        continue
      }
      writeClosureSections(stdout)
    }
  }
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
  const todo = modules.filter((m) => !existsSync(join(EXPORTS, `${m}.ndjson`)))
  log(`exports: ${todo.length} to do, ${modules.length - todo.length} present, batches of ${EXPORT_BATCH}, concurrency ${CONCURRENCY}`)
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
      const r = await runToFile("lake", ["env", L4E_BIN, m, "--only-listed", "--", ...names], tmp, { cwd: REPO, timeoutMs: 30 * 60 * 1000 })
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
        if (!names) failed.push([m, "no closure"])
        else members.push([m, names])
      }
      if (members.length) {
        const listPath = join(EXPORTS, `.batch-${process.pid}-${Math.random().toString(36).slice(2)}.tsv`)
        writeFileSync(listPath, members.map(([m, names]) => [m, join(EXPORTS, `${m}.ndjson.tmp`), ...names].join("\t")).join("\n") + "\n")
        let r
        try {
          r = await run("lake", ["env", L4E_BIN, "--only-listed", `--batch=${listPath}`], { cwd: REPO, timeoutMs: 60 * 60 * 1000 })
        } catch (e) {
          r = { code: -1, tail: String(e) }
        }
        try { rmSync(listPath, { force: true }) } catch { /* nothing to remove */ }
        if (r.code !== 0) log(`WARNING: export batch of ${members.length} exited ${r.code}: ${(r.tail || "").slice(-300).replace(/\s+/g, " ")} — one module per process`)
        for (const [m, names] of members) {
          if (r.code === 0 && (await finish(m))) continue
          await exportOne(m, names)
        }
      }
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
        const { stdout } = await x("lake", ["env", "lean", "-M", String(LEAN_MB), "--run", EXPAND_LEAN, EXPORTS, src.roots.join(","), ...chunk], { cwd: REPO, env: ENV, maxBuffer: 64 * 1024 * 1024, timeout: 60 * 60 * 1000 })
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
            await x("lake", ["env", "lean", "-M", String(LEAN_MB), "--run", EXPAND_LEAN, EXPORTS, src.roots.join(","), m], { cwd: REPO, env: ENV, maxBuffer: 64 * 1024 * 1024, timeout: 20 * 60 * 1000 })
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
  const handled = new Set([...(ci.failed || []).map((f) => f.module), ...modules.filter((m) => existsSync(join(EXPORTS, `${m}.ndjson`)))])
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
  log(`adopted the runner's setup: ${ci.exported}/${ci.modules} modules exported on ${ci.toolchain} — nothing built here`)
  return true
}

// ---- memory watchdog ------------------------------------------------------------
// `lean -M` counts resident memory, and macOS compresses a runaway's pages instead of keeping them
// resident: a notation expansion reached 33 GB (30 GB compressed, 3 GB resident) far past an 11 GB cap.
// Every 10 s this reads the real footprint of every process under this one (macOS: top's MEM, which
// counts compressed pages; Linux: VmRSS + VmSwap) and kills any process over EMISSARY_FOOTPRINT_MB
// (default 10240). The killed command fails like any other and its module is recorded as failed.
const FOOTPRINT_MB = Number(process.env.EMISSARY_FOOTPRINT_MB || 10240)
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
function watchMemory() {
  try {
    for (const [pid, mb] of footprintsMB(descendants(process.pid))) {
      if (mb <= FOOTPRINT_MB) continue
      let cmd = "?"
      try {
        cmd = execFileSync("ps", ["-o", "command=", "-p", String(pid)]).toString().trim().slice(0, 160)
      } catch {
        /* exited */
      }
      process.kill(pid, "SIGKILL")
      log(`memory watchdog: killed ${pid} at ${Math.round(mb)} MB (limit ${FOOTPRINT_MB} MB): ${cmd}`)
    }
  } catch (e) {
    log(`memory watchdog: ${e.message}`)
  }
}

async function main() {
  const t0 = Date.now()
  setInterval(watchMemory, 10000).unref()
  removeLeftovers()
  log(`setup ${key}: ${src.repo} @ ${src.commit.slice(0, 12)} on ${src.toolchain}, roots ${src.roots.join(", ")}`)
  await ensureClone()
  const { entries, stats } = seedQueue()
  const modules = Array.from(new Set(entries.map((e) => moduleOfPath(e.sourcePath)))).sort()
  log(`${entries.length} entries in ${modules.length} modules`)
  if (ONLY === "seed") return
  if (!ONLY && adopt(entries, modules, stats, t0)) return
  await ensureToolchain()
  if (ONLY !== "export") await build(modules)
  await closures(modules)
  const expansion = await expand(closureModules(modules))
  if (ONLY === "expand") {
    await cleanup()
    return log(`done ${key} (expand only): ${JSON.stringify(expansion.stats)}, ${expansion.failed.length} failed`)
  }
  await ensureLean4export()
  const failed = await exports(modules)
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

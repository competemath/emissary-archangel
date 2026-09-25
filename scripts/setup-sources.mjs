#!/usr/bin/env node
// Set up every registered library, one at a time, starting from whatever the disk says.
//   node scripts/setup-sources.mjs [key...]          run until nothing is left (default: every source)
//   node scripts/setup-sources.mjs --status          what is done, pending and given up; changes nothing
//   node scripts/setup-sources.mjs --retry-gave-up   also retry the libraries that gave up
//
// Stateless. Nothing is carried in memory from one library to the next and nothing assumes the run
// finishes in one go: the machine can sleep, the network can be switched off, the driver can be
// killed, and running the same command again resumes. Every decision is re-read from disk:
//   done      infra/<key>/setup.json newer than .proof-term-fix-marker
//   stale     setup.json older than the marker (exported with proof terms): re-exported after the rest
//   gave-up   data/pipeline/state/<key>.json counts MAX_ATTEMPTS failures that happened while online
//   pending   everything else with a repo
// Inside a library, scripts/setup-source.mjs skips every step and module whose output exists, so a
// killed library resumes where it stopped (Lake resumes its own build).
//
// Every library is banked the moment it finishes: data/exports/<key> is committed on main and pushed.
// A push that fails offline goes out with the next one; a library finished while no driver was
// watching (a setup that outlived a killed driver) is banked by the sweep at the top of every loop.
//
// One driver at a time: data/pipeline/setup.lock holds its pid; a second invocation exits at once.
// Failures while offline are interruptions, not attempts: the driver waits for github.com and retries.
import { spawn, spawnSync, execFileSync } from "node:child_process"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { fileURLToPath } from "node:url"

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..")
process.chdir(ROOT)
const PIPE = path.join(ROOT, "data", "pipeline")
const STATE = path.join(PIPE, "state")
const LOCK = path.join(PIPE, "setup.lock")
const MARKER = path.join(ROOT, ".proof-term-fix-marker")
const MAX_ATTEMPTS = Number(process.env.EMISSARY_MAX_ATTEMPTS || 3)
// Below this the driver clears the Mathlib download cache, and below half of it waits instead of
// starting a build (a full disk corrupts builds and takes the Leak services down with it).
const MIN_FREE_GB = Number(process.env.EMISSARY_MIN_FREE_GB || 12)
const GITHUB_FILE_LIMIT = 95 * 1024 * 1024
const HOME = os.homedir()
const ENV = {
  ...process.env,
  PATH: [path.join(HOME, ".elan", "bin"), path.dirname(process.execPath), "/opt/homebrew/bin", "/usr/local/bin", process.env.PATH || ""].join(":"),
}

const argv = process.argv.slice(2)
const ONLY = argv.filter((a) => !a.startsWith("--"))
const STATUS = argv.includes("--status")
const RETRY_GAVE_UP = argv.includes("--retry-gave-up")

const ts = () => new Date().toTimeString().slice(0, 8)
const log = (s) => console.log(`[${ts()}] ${s}`)
const sleep = (ms) => new Promise((r) => setTimeout(r, ms))
const mtime = (p) => {
  try {
    return fs.statSync(p).mtimeMs
  } catch {
    return 0
  }
}
const readJSON = (p, dflt = null) => {
  try {
    return JSON.parse(fs.readFileSync(p, "utf8"))
  } catch {
    return dflt
  }
}
const writeAtomic = (p, data) => {
  fs.mkdirSync(path.dirname(p), { recursive: true })
  fs.writeFileSync(`${p}.tmp-${process.pid}`, data)
  fs.renameSync(`${p}.tmp-${process.pid}`, p)
}
const alive = (pid) => {
  try {
    process.kill(pid, 0)
    return true
  } catch (e) {
    return e.code === "EPERM"
  }
}
const online = () => spawnSync("curl", ["-sI", "-m", "10", "https://github.com"], { stdio: "ignore" }).status === 0
const git = (args) => spawnSync("git", args, { cwd: ROOT, env: ENV, encoding: "utf8" })
const freeGB = () => Number(execFileSync("df", ["-k", ROOT]).toString().trim().split("\n").pop().split(/\s+/)[3]) / 1048576

// ---- state, read from disk every time ---------------------------------------------------------
const setupJson = (key) => path.join(ROOT, "infra", key, "setup.json")
const stateFile = (key) => path.join(STATE, `${key}.json`)
const reseedFile = (key) => path.join(ROOT, "infra", key, "reseed")
const repoDir = (key, src) => path.join(src.corpusRoot ? path.resolve(ROOT, src.corpusRoot) : path.join(ROOT, "infra", key, "repo"), src.subdir || "")
const queuePath = (key, src) => path.join(ROOT, "data", src.queueFile || `queue-${key}.json`)

function stateOf(key) {
  const t = mtime(setupJson(key))
  if (t && t > mtime(MARKER)) return "done"
  if ((readJSON(stateFile(key), {}).attempts || 0) >= MAX_ATTEMPTS) return "gave-up"
  return t ? "stale" : "pending"
}
const ver = (tc) => {
  const m = /v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?/.exec(tc || "")
  return m ? [+m[1], +m[2], +m[3], m[4] ? +m[4] : 99] : [0, 0, 0, 0]
}
const newerFirst = (a, b) => {
  const [x, y] = [ver(a), ver(b)]
  for (let i = 0; i < 4; i++) if (x[i] !== y[i]) return y[i] - x[i]
  return 0
}
// Order: pending before stale, a source marked `setup.order: "last"` (flt-anthropic, days of work)
// after the other pending ones; within a tier a library with a build already on disk first (it holds
// the disk and resumes), then the tree's toolchain, then newest toolchain first so each toolchain is
// installed once and uninstalled after its last library.
function plan() {
  const reg = readJSON(path.join(ROOT, "sources.json"))
  const tree = reg.targetToolchain
  const rows = []
  for (const [key, src] of Object.entries(reg.sources)) {
    if (!src.repo || (ONLY.length && !ONLY.includes(key))) continue
    rows.push({ key, src, state: stateOf(key), parked: fs.existsSync(path.join(repoDir(key, src), ".lake")) })
  }
  const tier = (r) => (r.state === "stale" ? 2 : r.src.setup?.order === "last" ? 1 : 0)
  const todo = rows
    .filter((r) => r.state === "pending" || r.state === "stale")
    .sort(
      (a, b) =>
        tier(a) - tier(b) ||
        Number(b.parked) - Number(a.parked) ||
        Number(a.src.toolchain !== tree) - Number(b.src.toolchain !== tree) ||
        newerFirst(a.src.toolchain, b.src.toolchain) ||
        a.key.localeCompare(b.key),
    )
  return { rows, todo }
}

// ---- banking ------------------------------------------------------------------------------------
async function gitIdle() {
  for (let i = 0; i < 60 && fs.existsSync(path.join(ROOT, ".git", "index.lock")); i++) await sleep(2000)
  return !fs.existsSync(path.join(ROOT, ".git", "index.lock"))
}
// Commit data/exports/<key> on main (only those paths: anything else staged is left alone).
async function bank(key) {
  const dir = path.join("data", "exports", key)
  if (!fs.existsSync(path.join(ROOT, dir)) && !git(["ls-files", "--", dir]).stdout.trim()) return false
  if (git(["branch", "--show-current"]).stdout.trim() !== "main") {
    log(`bank ${key}: the checkout is not on main — banking deferred`)
    return false
  }
  if (!(await gitIdle())) {
    log(`bank ${key}: .git/index.lock held for 2 min — banking deferred`)
    return false
  }
  // GitHub refuses a file over 100 MB, and one refused file blocks every later push.
  const big = fs.existsSync(path.join(ROOT, dir))
    ? fs.readdirSync(path.join(ROOT, dir)).filter((f) => fs.statSync(path.join(ROOT, dir, f)).size > GITHUB_FILE_LIMIT)
    : []
  for (const f of big) log(`bank ${key}: ${f} is over 95 MB — left out`)
  git(["add", "-A", "--", dir, ...big.map((f) => `:(exclude)${path.join(dir, f)}`)])
  if (git(["diff", "--cached", "--quiet", "--", dir]).status === 0) return false
  const sj = readJSON(setupJson(key), {})
  const body = sj.modules != null
    ? `${sj.exported}/${sj.modules} modules exported on ${sj.toolchain} (${sj.repo} @ ${String(sj.commit).slice(0, 12)}). Banked by scripts/setup-sources.mjs when the library's setup finished (temporary home, see data/exports/README.md).`
    : "Banked by scripts/setup-sources.mjs (temporary home, see data/exports/README.md)."
  const r = git(["commit", "-q", "-s", "-m", `exports: ${key}`, "-m", body, "-m", "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>", "--", dir])
  if (r.status !== 0) {
    log(`bank ${key}: commit failed: ${(r.stderr || r.stdout).trim().slice(-300)}`)
    return false
  }
  log(`banked ${key}: ${git(["log", "-1", "--format=%h"]).stdout.trim()}`)
  return true
}
function push() {
  const ahead = Number(git(["rev-list", "--count", "origin/main..main"]).stdout.trim() || 0)
  if (!ahead) return
  if (!online()) return log(`push: offline — ${ahead} commit(s) go out with the next bank`)
  let r = git(["push", "-q", "origin", "main"])
  if (r.status !== 0) {
    // origin moved (a merged PR): replay the export commits on top, once
    const busy = ["rebase-merge", "rebase-apply", "MERGE_HEAD"].some((f) => fs.existsSync(path.join(ROOT, ".git", f)))
    if (!busy && git(["pull", "-q", "--rebase", "--autostash", "origin", "main"]).status === 0) r = git(["push", "-q", "origin", "main"])
    else if (!busy) git(["rebase", "--abort"])
  }
  log(r.status === 0 ? `pushed ${ahead} commit(s)` : `push failed, commits stay local: ${(r.stderr || "").trim().slice(-300)}`)
}

// A done library whose exports are not committed yet, or whose build outlived its cleanup.
async function sweep(rows) {
  let banked = false
  for (const r of rows.filter((r) => r.state === "done")) {
    if (await bank(r.key)) banked = true
    const lake = path.join(repoDir(r.key, r.src), ".lake")
    if (fs.existsSync(lake)) {
      fs.rmSync(lake, { recursive: true, force: true })
      log(`removed the leftover build ${path.relative(ROOT, lake)}`)
    }
  }
  if (banked || Number(git(["rev-list", "--count", "origin/main..main"]).stdout.trim() || 0)) push()
}

// ---- waiting --------------------------------------------------------------------------------------
async function until(cond, what, everyMs = 60000) {
  let said = false
  while (!stopping && !cond()) {
    if (!said) log(`waiting: ${what}`)
    said = true
    await sleep(everyMs)
  }
  if (said && !stopping) log(`resumed: ${what}`)
}
// A setup-source.mjs of THIS checkout that this driver did not start (one that outlived a killed driver,
// or run by hand): its command line names the checkout, or its working directory is the checkout.
const strays = () =>
  spawnSync("pgrep", ["-f", "scripts/setup-source\\.mjs"], { encoding: "utf8" })
    .stdout.split("\n")
    .filter(Boolean)
    .map(Number)
    .filter((p) => p !== child?.pid)
    .filter((p) => {
      const cmd = spawnSync("ps", ["-o", "command=", "-p", String(p)], { encoding: "utf8" }).stdout
      if (cmd.includes(path.join(ROOT, "scripts", "setup-source.mjs"))) return true
      const cwd = spawnSync("lsof", ["-a", "-d", "cwd", "-Fn", "-p", String(p)], { encoding: "utf8" }).stdout.split("\n").find((l) => l.startsWith("n"))
      return cwd?.slice(1) === ROOT
    })
function makeRoom() {
  if (freeGB() >= MIN_FREE_GB) return
  const cache = path.join(HOME, ".cache", "mathlib")
  if (fs.existsSync(cache)) {
    fs.rmSync(cache, { recursive: true, force: true })
    log(`disk under ${MIN_FREE_GB} GB free: removed ${cache} (now ${freeGB().toFixed(1)} GB free)`)
  }
}

// ---- one library ----------------------------------------------------------------------------------
let child = null
let stopping = false
let startedAt = new Date().toISOString()
const writeLock = (extra = {}) => writeAtomic(LOCK, JSON.stringify({ pid: process.pid, startedAt, ...extra }))

function prepare(r, todo) {
  if (r.state === "stale") {
    // Exported before proof terms were dropped. A queue nobody has worked on is reseeded too (it
    // picks up every seeding fix since, aintlib's and ieantn's misnamed dotted directories among
    // them) and its exports are redone from scratch; otherwise only the .ndjson files are.
    const q = readJSON(queuePath(r.key, r.src), [])
    const untouched = !q.length || q.every((e) => e.status === "pending")
    const dir = path.join(ROOT, "data", "exports", r.key)
    if (untouched) {
      fs.writeFileSync(reseedFile(r.key), new Date().toISOString())
      fs.rmSync(dir, { recursive: true, force: true })
    } else if (fs.existsSync(dir)) for (const f of fs.readdirSync(dir)) if (f.endsWith(".ndjson")) fs.rmSync(path.join(dir, f))
    fs.rmSync(setupJson(r.key), { force: true })
    log(`${r.key}: stale export (before the proof-term fix) — ${untouched ? "reseeding and redoing its exports" : "redoing its .ndjson exports"}`)
  }
  const args = [...(r.src.setup?.args || [])]
  if (fs.existsSync(reseedFile(r.key))) args.push("--reseed")
  // The last library on its toolchain takes the toolchain and the Mathlib download cache with it.
  if (!todo.some((o) => o.key !== r.key && o.src.toolchain === r.src.toolchain)) args.push("--uninstall-toolchain")
  return args
}
function runSetup(key, args) {
  return new Promise((resolve) => {
    const logPath = path.join(PIPE, `setup-${key}.log`)
    const fd = fs.openSync(logPath, "a")
    fs.writeSync(fd, `\n===== ${new Date().toISOString()} setup-source.mjs ${key} ${args.join(" ")} (driver ${process.pid})\n`)
    // Its own process group, so stopping the driver stops lake and lean too.
    child = spawn(process.execPath, [path.join(ROOT, "scripts", "setup-source.mjs"), key, ...args], { cwd: ROOT, env: ENV, stdio: ["ignore", fd, fd], detached: true })
    writeLock({ key, child: child.pid })
    child.on("close", (code, signal) => {
      fs.closeSync(fd)
      child = null
      writeLock()
      resolve({ code, signal, logPath })
    })
  })
}
function lastFailure(logPath) {
  // the tail only: a lake build log runs to hundreds of MB
  const fd = fs.openSync(logPath, "r")
  const size = fs.fstatSync(fd).size
  const buf = Buffer.alloc(Math.min(size, 200000))
  fs.readSync(fd, buf, 0, buf.length, size - buf.length)
  fs.closeSync(fd)
  const text = buf.toString("utf8")
  const attempt = text.slice(text.lastIndexOf("\n===== "))
  const fails = attempt.split("\n").filter((l) => / FAIL /.test(l))
  return (fails.pop() || attempt.trim().split("\n").pop() || "").replace(/^\[[\d:]+\] FAIL /, "").slice(0, 400)
}

async function runOne(r, todo) {
  const args = prepare(r, todo)
  log(`=== ${r.key} (${r.src.toolchain}) ${args.join(" ")} → data/pipeline/setup-${r.key}.log`)
  const t0 = Date.now()
  const { code, signal, logPath } = await runSetup(r.key, args)
  const minutes = Math.round((Date.now() - t0) / 60000)
  if (code === 0 && stateOf(r.key) === "done") {
    const sj = readJSON(setupJson(r.key), {})
    log(`=== ${r.key} done in ${minutes} min: ${sj.exported}/${sj.modules} modules exported`)
    fs.rmSync(stateFile(r.key), { force: true })
    fs.rmSync(reseedFile(r.key), { force: true })
    if (await bank(r.key)) push()
    return
  }
  const why = lastFailure(logPath) || `exit ${code ?? signal}`
  if (stopping) return log(`=== ${r.key} stopped with the driver (resumes on the next run)`)
  if (!online()) return log(`=== ${r.key} interrupted while offline after ${minutes} min — not counted: ${why}`)
  const st = readJSON(stateFile(r.key), {})
  st.attempts = (st.attempts || 0) + 1
  st.lastError = why
  st.lastAt = new Date().toISOString()
  writeAtomic(stateFile(r.key), JSON.stringify(st, null, 2))
  log(`=== ${r.key} failed (attempt ${st.attempts}/${MAX_ATTEMPTS}) after ${minutes} min: ${why}`)
}

// ---- status -------------------------------------------------------------------------------------
function status() {
  const { rows, todo } = plan()
  const by = (s) => rows.filter((r) => r.state === s)
  console.log(`done ${by("done").length}, pending ${by("pending").length}, stale ${by("stale").length}, gave up ${by("gave-up").length} (of ${rows.length} with a repo)`)
  const lock = readJSON(LOCK)
  console.log(lock && alive(lock.pid) ? `driver ${lock.pid} running${lock.key ? `, on ${lock.key}` : ""}` : "no driver running")
  if (todo.length) console.log(`next: ${todo.slice(0, 8).map((r) => r.key + (r.parked ? " (build on disk)" : "")).join(", ")}${todo.length > 8 ? ", …" : ""}`)
  for (const r of by("gave-up")) {
    const st = readJSON(stateFile(r.key), {})
    console.log(`gave up: ${r.key} after ${st.attempts} attempts — ${st.lastError}`)
  }
  for (const r of rows.filter((r) => r.state === "pending" && fs.existsSync(stateFile(r.key)))) {
    const st = readJSON(stateFile(r.key), {})
    console.log(`failed ${st.attempts}x, will retry: ${r.key} — ${st.lastError}`)
  }
}

// ---- main ---------------------------------------------------------------------------------------
function takeLock() {
  fs.mkdirSync(PIPE, { recursive: true })
  for (let i = 0; i < 2; i++) {
    try {
      const fd = fs.openSync(LOCK, "wx")
      fs.writeSync(fd, JSON.stringify({ pid: process.pid, startedAt }))
      fs.closeSync(fd)
      return null
    } catch (e) {
      if (e.code !== "EEXIST") throw e
      const held = readJSON(LOCK, {})
      if (held.pid && held.pid !== process.pid && alive(held.pid)) return held
      fs.rmSync(LOCK, { force: true }) // a killed driver's lock; its setup, if still running, is waited for below
    }
  }
  return readJSON(LOCK, {})
}
function stop(sig) {
  if (stopping) return
  stopping = true
  log(`driver: ${sig} — stopping${child ? ` ${child.pid} and its lake/lean` : ""}`)
  if (!child) process.exit(0)
  try {
    process.kill(-child.pid, "SIGTERM")
  } catch {}
  setTimeout(() => {
    try {
      if (child) process.kill(-child.pid, "SIGKILL")
    } catch {}
  }, 20000).unref()
}

async function main() {
  if (STATUS) return status()
  const held = takeLock()
  if (held) return log(`driver ${held.pid} is already running${held.key ? ` (on ${held.key})` : ""} — nothing to do`)
  process.on("exit", () => {
    if (readJSON(LOCK, {}).pid === process.pid) fs.rmSync(LOCK, { force: true })
  })
  for (const s of ["SIGTERM", "SIGINT"]) process.on(s, () => stop(s))
  process.on("SIGHUP", () => {}) // a closed terminal is not a reason to stop
  if (RETRY_GAVE_UP) for (const r of plan().rows.filter((r) => r.state === "gave-up")) fs.rmSync(stateFile(r.key), { force: true })
  log(`driver ${process.pid} up: ${plan().todo.length} libraries to do`)
  while (!stopping) {
    await sweep(plan().rows)
    if (!plan().todo.length) break
    await until(() => !strays().length, `another setup-source.mjs is running (${strays().join(", ")})`)
    await until(online, "github.com unreachable")
    makeRoom()
    await until(() => freeGB() >= MIN_FREE_GB / 2, `under ${MIN_FREE_GB / 2} GB of free disk`, 10 * 60000)
    if (stopping) break
    const { todo } = plan() // re-read: a stray may have finished a library while we waited
    if (!todo.length) continue
    await runOne(todo[0], todo)
  }
  if (!stopping) {
    const { rows } = plan()
    const n = (s) => rows.filter((r) => r.state === s).length
    log(`driver: nothing left to do — ${n("done")} done, ${n("gave-up")} gave up (node scripts/setup-sources.mjs --status)`)
  }
}
main().catch((e) => {
  log(`driver crashed: ${e?.stack || e}`)
  process.exit(1)
})

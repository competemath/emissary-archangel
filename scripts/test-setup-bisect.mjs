// node scripts/test-setup-bisect.mjs — the closure and export phases: a batch that fails is split in two and each half tried (down to
// single modules, where a module that fails alone is recorded once and the rest go on), and the phases after the build run under the
// lone-process memory limit, with Lean's -M following it in the phases that run Lean itself (closures, expansion; lean4export takes no
// -M, the watchdog alone bounds it). Runs setup-source.mjs for real, in a throwaway root, against a local git
// repository, a stand-in `elan`, a stand-in lean4export folder and a stand-in `lake` whose `lean --run` refuses a closure batch larger
// than FAKE_CLOSURE_MAX modules and whose `lean4export --batch` refuses one larger than FAKE_EXPORT_MAX (as a memory kill does), and
// whose exporter refuses the module FAKE_EXPORT_REFUSE in any company, and hangs (a child process that never ends, as lean4export under `lake env` does)
// on the module FAKE_EXPORT_HANG (and a closure run on FAKE_CLOSURE_HANG): the timeouts are scaled down to a second or two for it. No Lean, no network.
// Why: flt-anthropic, 3-4 Nov 2026. Every closure process was killed at 10.3-11.8 GB under the 10 GB per-process limit, a batch of
// 350-600 or a single module alike; the fallback then ran one ~11 GB import per module, serially, and 62 of 64 export shards ran to their
// 300-minute cap with nothing exported (shard 5 handed on 129 files). Round 2 was repeating it on 12 runners.
import { execFileSync, spawn, spawnSync } from "node:child_process"
import { createHash } from "node:crypto"
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const tmp = mkdtempSync(join(os.tmpdir(), "setup-bisect-test-"))
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) {
    bad++
    console.log("FAIL", name, detail ?? "")
  } else console.log("ok", name)
}
const sh = (cmd, args, opts = {}) => execFileSync(cmd, args, { stdio: ["ignore", "pipe", "pipe"], ...opts }).toString()

// the library: six modules, no imports between them (the build is not under test)
const lib = join(tmp, "lib-src")
mkdirSync(join(lib, "Lib"), { recursive: true })
const names = ["A", "B", "C", "D", "E", "F"]
for (const m of names) writeFileSync(join(lib, "Lib", `${m}.lean`), `theorem t_${m.toLowerCase()} : True := trivial\n`)
const TC = "leanprover/lean4:v4.0.0"
writeFileSync(join(lib, "lean-toolchain"), TC + "\n")
const git = (...a) => sh("git", ["-c", "user.name=t", "-c", "user.email=t@t", ...a], { cwd: lib })
git("init", "-q")
git("add", ".")
git("commit", "-q", "-m", "lib")
const commit = git("rev-parse", "HEAD").trim()

const root = join(tmp, "root")
mkdirSync(join(root, "scripts"), { recursive: true })
mkdirSync(join(root, "data"), { recursive: true })
cpSync(join(here, "setup-source.mjs"), join(root, "scripts", "setup-source.mjs"))
cpSync(join(here, "setup-tools.mjs"), join(root, "scripts", "setup-tools.mjs"))
cpSync(join(here, "patch-lean4export.py"), join(root, "scripts", "patch-lean4export.py"))
writeFileSync(join(root, "sources.json"), JSON.stringify({ sources: { t: { repo: lib, commit, toolchain: TC, roots: ["Lib"] } } }))
writeFileSync(
  join(root, "data", "queue-t.json"),
  JSON.stringify(names.map((m, i) => ({ id: i + 1, name: `t_${m.toLowerCase()}`, sourcePath: `Lib/${m}.lean`, sourceLine: 1, status: "pending" }))),
)

const home = join(tmp, "home")
const bin = join(home, ".elan", "bin")
mkdirSync(bin, { recursive: true })
writeFileSync(join(bin, "elan"), `#!/bin/sh\necho "${TC} (default)"\n`)
// lake: `lake build M...` writes an .olean per module; `lake env lean -M <mb> --run <closure script> <prefix> M...` prints one section per
// module, or fails (like a memory kill) when the batch is bigger than FAKE_CLOSURE_MAX; `lake env <lean4export> --only-listed --batch=<tsv>`
// writes one declaration to each listed module's file, or fails when the list is longer than FAKE_EXPORT_MAX or holds FAKE_EXPORT_REFUSE;
// `lake env <lean4export> M --only-listed -- names...` prints one declaration, or fails for FAKE_EXPORT_REFUSE. Every call is appended to a
// log as its argument list (a Lean call with its -M value); an export call is logged again as `export-batch M...` or `export-one M`.
writeFileSync(
  join(bin, "lake"),
  `#!/usr/bin/env node
const fs = require("node:fs")
const path = require("node:path")
const args = process.argv.slice(2)
fs.appendFileSync(${JSON.stringify(join(tmp, "lake-calls"))}, args.join(" ") + "\\n")
const [cmd] = args
if (cmd === "build") {
  for (const m of args.slice(1)) {
    const olean = path.join(".lake", "build", "lib", "lean", m.split(".").join("/") + ".olean")
    fs.mkdirSync(path.dirname(olean), { recursive: true })
    fs.writeFileSync(olean, "")
  }
  process.exit(0)
}
if (cmd === "env" && args[1] === "lean") {
  const script = args[args.indexOf("--run") + 1]
  const rest = args.slice(args.indexOf("--run") + 2)
  if (script.endsWith("corpus-closure-batch.lean")) {
    const [pfx, ...mods] = rest
    const max = Number(process.env.FAKE_CLOSURE_MAX || 1000)
    if (process.env.FAKE_CLOSURE_HANG && mods.includes(process.env.FAKE_CLOSURE_HANG)) hangForever()
    if (process.env.FAKE_CLOSURE_BAD && mods.includes(process.env.FAKE_CLOSURE_BAD)) { process.stdout.write("== nodir/Lib.F\\nname\\tmod\\t\\n"); process.exit(0) }
    if (mods.length > max) { process.stderr.write("memory\\n"); process.exit(1) }
    for (const m of mods) process.stdout.write("== " + m + "\\n" + "t_" + m.split(".").pop().toLowerCase() + "\\t" + m + "\\t\\n")
    process.exit(0)
  }
}
// the exporter under lake env: a child of this process that never ends; its pid goes to a file, and this process waits for it
function hangForever() {
  const child = require("node:child_process").spawn(process.execPath, ["-e", "setInterval(() => {}, 1000)"], { stdio: "ignore" })
  fs.appendFileSync(${JSON.stringify(join(tmp, "hung-pids"))}, child.pid + "\\n")
  for (;;) Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 1000) // lake waits for its child; only a kill of the group ends either
}
if (cmd === "env" && args[1].endsWith("lean4export")) {
  const refuse = process.env.FAKE_EXPORT_REFUSE || ""
  const batch = args.find((a) => a.startsWith("--batch="))
  if (batch) {
    const rows = fs.readFileSync(batch.slice(8), "utf8").trim().split("\\n").map((l) => l.split("\\t"))
    fs.appendFileSync(${JSON.stringify(join(tmp, "lake-calls"))}, "export-batch " + rows.map((r) => r[0]).join(" ") + "\\n")
    const max = Number(process.env.FAKE_EXPORT_MAX || 1000)
    if (process.env.FAKE_EXPORT_HANG && rows.some((r) => r[0] === process.env.FAKE_EXPORT_HANG)) hangForever()
    if (rows.length > max || rows.some((r) => r[0] === refuse)) { process.stderr.write("memory\\n"); process.exit(1) }
    for (const [m, out] of rows) fs.writeFileSync(out, JSON.stringify({ thm: m }) + "\\n")
    process.exit(0)
  }
  const m = args[2]
  fs.appendFileSync(${JSON.stringify(join(tmp, "lake-calls"))}, "export-one " + m + "\\n")
  if (process.env.FAKE_EXPORT_HANG && m === process.env.FAKE_EXPORT_HANG) hangForever()
  if (m === refuse) { process.stderr.write("memory\\n"); process.exit(1) }
  process.stdout.write(JSON.stringify({ thm: m }) + "\\n")
  process.exit(0)
}
process.exit(0)
`,
)
// the exporter folder setup-source.mjs reuses: a binary, a Main.lean with the --batch patch, the patch script's fingerprint
const l4eDir = join(root, "infra", "lean4export", TC.replace(/[^A-Za-z0-9.-]+/g, "_"))
const fakeExporter = () => {
  mkdirSync(join(l4eDir, ".lake", "build", "bin"), { recursive: true })
  writeFileSync(join(l4eDir, ".lake", "build", "bin", "lean4export"), "")
  writeFileSync(join(l4eDir, "Main.lean"), "def runBatch := ()\n")
  writeFileSync(join(l4eDir, ".patch-sha"), createHash("sha256").update(readFileSync(join(here, "patch-lean4export.py"), "utf8")).digest("hex").slice(0, 12) + "\n")
}
chmodSync(join(bin, "elan"), 0o755)
chmodSync(join(bin, "lake"), 0o755)

const exportsDir = join(root, "data", "exports", "t")
const setup = (args, env = {}, only = ["--only", "expand"]) =>
  spawnSync("node", [join(root, "scripts", "setup-source.mjs"), "t", ...only, "--keep-build", ...args], {
    // every FAKE_* knob is set here, so that nothing in the caller's environment changes a split
    env: { ...process.env, HOME: home, EMISSARY_WATCH_MS: "300", EMISSARY_FOOTPRINT_MB: "150", EMISSARY_RETRY_FOOTPRINT_MB: "2048", EMISSARY_LEAN_MB: "100", FAKE_CLOSURE_MAX: "1000", FAKE_EXPORT_MAX: "1000", FAKE_EXPORT_REFUSE: "", FAKE_EXPORT_HANG: "", FAKE_CLOSURE_HANG: "", FAKE_CLOSURE_BAD: "", ...env },
    encoding: "utf8",
  })
const calls = () => (existsSync(join(tmp, "lake-calls")) ? readFileSync(join(tmp, "lake-calls"), "utf8").trim().split("\n") : [])
const closureCalls = () => calls().filter((c) => c.includes("corpus-closure-batch.lean")).map((c) => c.split("corpus-closure-batch.lean Lib ")[1].split(" "))
const fresh = () => {
  rmSync(join(root, "infra"), { recursive: true, force: true })
  rmSync(exportsDir, { recursive: true, force: true })
  rmSync(join(tmp, "lake-calls"), { force: true })
}
const out = (r) => r.stdout + r.stderr
const closures = () => names.filter((m) => existsSync(join(exportsDir, `Lib.${m}.names.json`)))
const exported = () => names.filter((m) => existsSync(join(exportsDir, `Lib.${m}.ndjson`)))
const exportCalls = () => calls().filter((c) => c.startsWith("export-")).map((c) => c.split(" "))
const sizes = (cc) => cc.map((c) => c.length - 1).join(",")

// 1. a batch of six that only fits three at a time: the batch fails, its two halves go through — three processes, not seven (1 + 6 singles)
fresh()
let r = setup(["--closure-batch", "6"], { FAKE_CLOSURE_MAX: "3" })
let cc = closureCalls()
check("every module has its closure", r.status === 0 && closures().length === 6, out(r))
check("the batch of six, then its halves of three: three closure processes", cc.map((c) => c.length).join(",") === "6,3,3", cc.map((c) => c.length).join(","))
check("the log says the batch is split", /closure: a batch of 6 failed: trying its two halves \(3 and 3\)/.test(r.stdout), r.stdout)

// 2. the limit: one process at a time gets the lone-process limit, and Lean's -M follows it (the script's floor for -M is 1024, which would have stopped Lean before a 2048 MB watchdog)
check("closures run under the lone-process limit", /closures: memory limit 2048 MB per process \(one process at a time\)/.test(r.stdout), r.stdout)
check("Lean's heap cap follows the limit", calls().some((c) => / -M 2048 --run /.test(c)) && !calls().some((c) => / -M 1024 --run /.test(c)), calls().join("\n"))
check("the expansion phase gets the same lone-process limit", /expand: memory limit 2048 MB/.test(r.stdout), r.stdout)

// 3. nothing fits but single modules: still every closure, by halving down to one (6 -> 3,3 -> 2,1,2,1 -> singles)
fresh()
r = setup(["--closure-batch", "6"], { FAKE_CLOSURE_MAX: "1" })
cc = closureCalls()
check("with only single modules fitting, every module still gets its closure", r.status === 0 && closures().length === 6, out(r))
check("and no module is tried more than once alone", cc.filter((c) => c.length === 1).length === 6, cc.map((c) => c.length).join(","))

// 4. a batch that fits is one process
fresh()
r = setup(["--closure-batch", "6"], { FAKE_CLOSURE_MAX: "6" })
cc = closureCalls()
check("a batch that fits is one process", r.status === 0 && cc.length === 1 && cc[0].length === 6 && closures().length === 6, cc.map((c) => c.length).join(","))

// 5. more than one process at a time keeps the ordinary per-process limit
fresh()
r = setup(["--closure-batch", "6", "--concurrency", "2"], { FAKE_CLOSURE_MAX: "6" })
check("two at a time: the per-process limit stays 150", /closures: memory limit 150 MB per process \(2 at a time\)/.test(r.stdout), r.stdout)

// 6. the export phase: a batch of six that only fits three at a time is halved the same way, under the same lone-process limit
fresh()
fakeExporter()
r = setup(["--export-batch", "6"], { FAKE_EXPORT_MAX: "3" }, [])
let ec = exportCalls()
check("every module is exported", r.status === 0 && exported().length === 6, out(r))
check("the export batch of six, then its halves of three: three exporter processes, no single", sizes(ec) === "6,3,3" && ec.every((c) => c[0] === "export-batch"), ec.map((c) => c.join(" ")).join("\n"))
check("the log says the export batch is split", /export: a batch of 6 failed: trying its two halves \(3 and 3\)/.test(r.stdout), r.stdout)
check("exports run under the lone-process limit", /exports: memory limit 2048 MB per process \(one process at a time\)/.test(r.stdout), r.stdout)

// 7. one module the exporter refuses in any company: the halving isolates it, it is tried alone once, recorded as failed, and the other five are exported
fresh()
fakeExporter()
r = setup(["--export-batch", "6"], { FAKE_EXPORT_REFUSE: "Lib.F" }, [])
ec = exportCalls()
const report = existsSync(join(root, "infra", "t", "setup.json")) ? JSON.parse(readFileSync(join(root, "infra", "t", "setup.json"), "utf8")) : null
check("the five modules the exporter accepts are exported, the refused one is not", r.status === 0 && exported().join("") === "ABCDE", out(r))
check("the halving isolates the refused module: 6, 3+3, 2+1", sizes(ec) === "6,3,3,2,1", ec.map((c) => c.join(" ")).join("\n"))
check("the refused module is tried alone exactly once, through the single-module exporter", ec.filter((c) => c[0] === "export-one").map((c) => c[1]).join(",") === "Lib.F", ec.map((c) => c.join(" ")).join("\n"))
check("the record names the module and the exporter's exit", report && report.exported === 5 && report.failed.length === 1 && report.failed[0].module === "Lib.F" && /lean4export exited 1/.test(report.failed[0].why), JSON.stringify(report && report.failed))

// 8. an export that hangs: the batch is cut off by its scaled timeout (base + per module), the halving goes on with ever smaller limits, the module that hangs alone is cut off
// by the single-module limit and recorded, and every process the timeouts killed is gone (`lake` runs the exporter as its child: killing `lake` alone left it running, and the
// next attempt shared the machine with it; flt-anthropic round 4, 4 Nov 2026: four shards re-ran halves of 200, 100 and 50 modules, each timing out too, for five hours)
fresh()
fakeExporter()
rmSync(join(tmp, "hung-pids"), { force: true })
const started = Date.now()
r = setup(["--export-batch", "6"], { FAKE_EXPORT_HANG: "Lib.F", EMISSARY_EXPORT_BASE_MS: "1000", EMISSARY_EXPORT_PER_MODULE_MS: "100", EMISSARY_EXPORT_SINGLE_MS: "900" }, [])
ec = exportCalls()
const hangReport = existsSync(join(root, "infra", "t", "setup.json")) ? JSON.parse(readFileSync(join(root, "infra", "t", "setup.json"), "utf8")) : null
check("the five modules that do not hang are exported", r.status === 0 && exported().join("") === "ABCDE", out(r))
check("the halving isolates the module that hangs: 6, 3+3, 2+1", sizes(ec) === "6,3,3,2,1", ec.map((c) => c.join(" ")).join("\n"))
check("a batch's limit is the base plus so much per module: 1.6 s for six, 1.3 s for three", /export batch of 6 exited 124:[^\n]*timed out after 1\.6s/.test(r.stdout) && /export batch of 3 exited 124:[^\n]*timed out after 1\.3s/.test(r.stdout), r.stdout)
check("the module alone has its own limit and is recorded as timed out", hangReport && hangReport.failed.length === 1 && hangReport.failed[0].module === "Lib.F" && /timed out after 0\.9s/.test(hangReport.failed[0].why), JSON.stringify(hangReport && hangReport.failed))
const pids = existsSync(join(tmp, "hung-pids")) ? readFileSync(join(tmp, "hung-pids"), "utf8").trim().split("\n").map(Number) : []
const alive = (pid) => {
  try {
    process.kill(pid, 0)
    return true
  } catch {
    return false
  }
}
for (let i = 0; i < 20 && pids.some(alive); i++) spawnSync("sleep", ["0.2"])
check("three exporters hung, and none of them is still running", pids.length === 3 && !pids.some(alive), `pids ${pids.join(",")}, alive ${pids.filter(alive).join(",")}`)
for (const pid of pids.filter(alive)) process.kill(pid, "SIGKILL") // a failing run must not leave them behind
check("it took seconds, not the hours of the old limits", Date.now() - started < 60000, `${Date.now() - started} ms`)

check("the limits in force are in the log: the knobs as set", /limits: a batch 1 s \+ 0\.1 s per module \(at most 60 min\), one module alone 0\.9 s/.test(r.stdout), r.stdout)

// 9. the knobs take only a positive number a timer can hold: 0, text and 99999999999 ms (setTimeout turns a delay over 2^31-1 ms into 1 ms) fall back to the defaults
fresh()
fakeExporter()
r = setup(["--export-batch", "6"], { EMISSARY_EXPORT_BASE_MS: "0", EMISSARY_EXPORT_PER_MODULE_MS: "abc", EMISSARY_EXPORT_SINGLE_MS: "99999999999" }, [])
check("a knob that is 0, text or too large for a timer is the default", r.status === 0 && /limits: a batch 180 s \+ 3 s per module \(at most 60 min\), one module alone 1200 s/.test(r.stdout), r.stdout)

// 10. a SIGTERM to the script ends the commands it started: each leads its own process group, so the terminal's Ctrl-C and a plain kill of the script no longer reach them
fresh()
fakeExporter()
rmSync(join(tmp, "hung-pids"), { force: true })
const child = spawn("node", [join(root, "scripts", "setup-source.mjs"), "t", "--keep-build", "--export-batch", "6"], {
  // the three export knobs are the defaults, whatever the caller has set: a short limit would end the hang before the SIGTERM; its own process group, so that a failing test can end the script and the fake lake with it
  env: { ...process.env, HOME: home, EMISSARY_WATCH_MS: "300", EMISSARY_FOOTPRINT_MB: "150", EMISSARY_RETRY_FOOTPRINT_MB: "2048", EMISSARY_LEAN_MB: "100", FAKE_EXPORT_HANG: "Lib.F", EMISSARY_EXPORT_BASE_MS: "180000", EMISSARY_EXPORT_PER_MODULE_MS: "3000", EMISSARY_EXPORT_SINGLE_MS: "1200000" },
  stdio: "ignore",
  detached: true,
})
const exitCode = new Promise((res) => child.on("close", (code, sig) => res(sig ?? code)))
for (let i = 0; i < 100 && !existsSync(join(tmp, "hung-pids")); i++) await new Promise((r2) => setTimeout(r2, 200))
const hung = existsSync(join(tmp, "hung-pids")) ? readFileSync(join(tmp, "hung-pids"), "utf8").trim().split("\n").map(Number) : []
check("the exporter hangs under the default limits (the script is waiting for it)", hung.length === 1 && alive(hung[0]), `pids ${hung.join(",")}`)
child.kill("SIGTERM")
let guard
const how = await Promise.race([exitCode, new Promise((r2) => { guard = setTimeout(() => r2("still running"), 15000) })])
clearTimeout(guard)
for (let i = 0; i < 20 && hung.some(alive); i++) await new Promise((r2) => setTimeout(r2, 200))
check("after a SIGTERM the script has exited, with 143", how === 143, String(how))
check("and the exporter it was waiting for is gone", hung.length === 1 && !alive(hung[0]), `alive ${hung.filter(alive).join(",")}`)
for (const pid of hung.filter(alive)) process.kill(pid, "SIGKILL")
if (how === "still running") {
  try {
    process.kill(-child.pid, "SIGKILL") // the script, the fake lake and whatever else is in its group
  } catch {
    /* already gone */
  }
}

// 11. a closure run that hangs: the same limits and the same cleanup as for the export (the closure processes were run through execFile, whose timeout kills `lake` and leaves `lean`):
// the batch of six is cut off after 1.6 s, the halving isolates the module, which is cut off alone after 0.9 s, the five others have their closures, no hung process is left
fresh()
rmSync(join(tmp, "hung-pids"), { force: true })
r = setup(["--closure-batch", "6"], { FAKE_CLOSURE_HANG: "Lib.F", EMISSARY_CLOSURE_BASE_MS: "1000", EMISSARY_CLOSURE_PER_MODULE_MS: "100", EMISSARY_CLOSURE_SINGLE_MS: "900" })
cc = closureCalls()
check("the five modules that do not hang have their closure, the hanging one does not", r.status === 0 && closures().join("") === "ABCDE", out(r))
check("the closure halving isolates the module that hangs: 6, 3+3, 2+1", cc.map((c) => c.length).join(",") === "6,3,3,2,1", cc.map((c) => c.length).join(","))
check("the closure limits: 1.6 s for six, 1.3 s for three, 0.9 s for a module alone", /closure batch of 6 failed, exit 124[\s\S]{0,80}timed out after 1\.6s/.test(r.stdout) && /closure batch of 3 failed, exit 124[\s\S]{0,80}timed out after 1\.3s/.test(r.stdout) && /closure failed for Lib\.F: exit 124[\s\S]{0,80}timed out after 0\.9s/.test(r.stdout), r.stdout)
const cpids = existsSync(join(tmp, "hung-pids")) ? readFileSync(join(tmp, "hung-pids"), "utf8").trim().split("\n").map(Number) : []
for (let i = 0; i < 20 && cpids.some(alive); i++) spawnSync("sleep", ["0.2"])
check("three closure runs hung, and none of them is still running", cpids.length === 3 && !cpids.some(alive), `pids ${cpids.join(",")}, alive ${cpids.filter(alive).join(",")}`)
for (const pid of cpids.filter(alive)) process.kill(pid, "SIGKILL")

// 12. a closure output that cannot be written (a section named for a folder that does not exist) is a failed batch, halved like any other: the setup goes on, and the modules around it have their closures
fresh()
r = setup(["--closure-batch", "6"], { FAKE_CLOSURE_BAD: "Lib.F" })
cc = closureCalls()
check("a closure output that cannot be written does not stop the setup: the five others have their closures", r.status === 0 && closures().join("") === "ABCDE", out(r))
check("it is logged and halved like any failed batch: 6, 3+3, 2+1", /closure batch of 6 could not be written/.test(r.stdout) && cc.map((c) => c.length).join(",") === "6,3,3,2,1", cc.map((c) => c.length).join(",") + "\n" + r.stdout)

rmSync(tmp, { recursive: true, force: true })
if (bad) {
  console.log(`${bad} check(s) failed`)
  process.exit(1)
}
console.log("setup-bisect: all checks passed")

// node scripts/test-setup-bisect.mjs — the closure and export phases: a batch that fails is split in two and each half tried (down to
// single modules, where a module that fails alone is recorded once and the rest go on), and the phases after the build run under the
// lone-process memory limit, with Lean's -M following it. Runs setup-source.mjs for real, in a throwaway root, against a local git
// repository, a stand-in `elan`, a stand-in lean4export folder and a stand-in `lake` whose `lean --run` refuses a closure batch larger
// than FAKE_CLOSURE_MAX modules and whose `lean4export --batch` refuses one larger than FAKE_EXPORT_MAX (as a memory kill does), and
// whose exporter refuses the module FAKE_EXPORT_REFUSE in any company. No Lean, no network.
// Why: flt-anthropic, 3-4 Nov 2026. Every closure process was killed at 10.3-11.8 GB under the 10 GB per-process limit, a batch of
// 350-600 or a single module alike; the fallback then ran one ~11 GB import per module, serially, and 62 of 64 export shards ran to their
// 300-minute cap with nothing exported (shard 5 handed on 129 files). Round 2 was repeating it on 12 runners.
import { execFileSync, spawnSync } from "node:child_process"
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
// log with its -M value; an export call is logged as `export-batch M...` or `export-one M`.
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
    if (mods.length > max) { process.stderr.write("memory\\n"); process.exit(1) }
    for (const m of mods) process.stdout.write("== " + m + "\\n" + "t_" + m.split(".").pop().toLowerCase() + "\\t" + m + "\\t\\n")
    process.exit(0)
  }
}
if (cmd === "env" && args[1].endsWith("lean4export")) {
  const refuse = process.env.FAKE_EXPORT_REFUSE || ""
  const batch = args.find((a) => a.startsWith("--batch="))
  if (batch) {
    const rows = fs.readFileSync(batch.slice(8), "utf8").trim().split("\\n").map((l) => l.split("\\t"))
    fs.appendFileSync(${JSON.stringify(join(tmp, "lake-calls"))}, "export-batch " + rows.map((r) => r[0]).join(" ") + "\\n")
    const max = Number(process.env.FAKE_EXPORT_MAX || 1000)
    if (rows.length > max || rows.some((r) => r[0] === refuse)) { process.stderr.write("memory\\n"); process.exit(1) }
    for (const [m, out] of rows) fs.writeFileSync(out, JSON.stringify({ thm: m }) + "\\n")
    process.exit(0)
  }
  const m = args[2]
  fs.appendFileSync(${JSON.stringify(join(tmp, "lake-calls"))}, "export-one " + m + "\\n")
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
    env: { ...process.env, HOME: home, EMISSARY_WATCH_MS: "300", EMISSARY_FOOTPRINT_MB: "150", EMISSARY_RETRY_FOOTPRINT_MB: "2048", EMISSARY_LEAN_MB: "100", ...env },
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

rmSync(tmp, { recursive: true, force: true })
if (bad) {
  console.log(`${bad} check(s) failed`)
  process.exit(1)
}
console.log("setup-bisect: all checks passed")

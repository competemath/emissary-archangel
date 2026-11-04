// node scripts/test-setup-bisect.mjs — the closure phase: a batch that fails is split in two and each half tried (down to single modules),
// and the phases after the build run under the lone-process memory limit, with Lean's -M following it. Runs setup-source.mjs for real,
// in a throwaway root, against a local git repository, a stand-in `elan` and a stand-in `lake` whose `lean --run` refuses a closure batch
// larger than FAKE_CLOSURE_MAX modules (as a memory kill does). No Lean, no network.
// Why: flt-anthropic, 3-4 Nov 2026. Every closure process was killed at 10.3-11.8 GB under the 10 GB per-process limit, a batch of
// 350-600 or a single module alike; the fallback then ran one ~11 GB import per module, serially, and 62 of 64 export shards ran to their
// 300-minute cap with nothing exported (shard 5 handed on 129 files). Round 2 was repeating it on 12 runners.
import { execFileSync, spawnSync } from "node:child_process"
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
// module, or fails (like a memory kill) when the batch is bigger than FAKE_CLOSURE_MAX; every call is appended to a log with its -M value.
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
process.exit(0)
`,
)
chmodSync(join(bin, "elan"), 0o755)
chmodSync(join(bin, "lake"), 0o755)

const exportsDir = join(root, "data", "exports", "t")
const setup = (args, env = {}) =>
  spawnSync("node", [join(root, "scripts", "setup-source.mjs"), "t", "--only", "expand", "--keep-build", ...args], {
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

rmSync(tmp, { recursive: true, force: true })
if (bad) {
  console.log(`${bad} check(s) failed`)
  process.exit(1)
}
console.log("setup-bisect: all checks passed")

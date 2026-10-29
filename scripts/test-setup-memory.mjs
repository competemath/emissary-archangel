// node scripts/test-setup-memory.mjs — a module whose Lean process passes the memory limit is killed by the watchdog; the build names it, builds it
// again alone with a higher limit, and one that still does not fit is remembered (and everything importing it is left out) instead of being killed
// again, round after round. Runs setup-source.mjs for real, in a throwaway root, against a local git repository, a stand-in `elan` and a stand-in
// `lake` that really holds the memory a module is declared to need (no Lean, no network).
// Why: flt-anthropic, 2026-10-29: Def_WeierstrassCurve_DivPolyMulFormula was killed at 11 GB in 5 of the first 17 chunks of every round, the log line cut
// the module's name off, nothing ever built the 2,896 modules behind it, and rounds 27 and 28 added nothing.
import { execFileSync, spawnSync } from "node:child_process"
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const tmp = mkdtempSync(join(os.tmpdir(), "setup-memory-test-"))
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name)
}
const sh = (cmd, args, opts = {}) => execFileSync(cmd, args, { stdio: ["ignore", "pipe", "pipe"], ...opts }).toString()

// the library: A; C and E and F import A; D imports C
const lib = join(tmp, "lib-src")
mkdirSync(join(lib, "Lib"), { recursive: true })
const files = { A: "", C: "import Lib.A\n", D: "-- header comment\nimport Lib.C\n", E: "import Lib.A\n", F: "/- block\ncomment -/\nimport Lib.A -- trailing\n" }
for (const [m, imp] of Object.entries(files)) writeFileSync(join(lib, "Lib", `${m}.lean`), `${imp}\ntheorem t_${m.toLowerCase()} : True := trivial\n`)
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
const names = Object.keys(files)
writeFileSync(join(root, "data", "queue-t.json"), JSON.stringify(names.map((m, i) => ({ id: i + 1, name: m.toLowerCase(), sourcePath: `Lib/${m}.lean`, sourceLine: 1, status: "pending" }))))

const home = join(tmp, "home")
const bin = join(home, ".elan", "bin")
mkdirSync(bin, { recursive: true })
writeFileSync(join(bin, "elan"), `#!/bin/sh\necho "${TC} (default)"\n`)
// lake: `lake build M...` builds each module after its imports, as Lake does (a module whose import failed is skipped, and a failure is remembered for the
// rest of the call). A module in FAKE_HUNGRY needs that many MB: a child process holds them, with the module's file in its command line as lean has.
writeFileSync(join(bin, "lake"), `#!/usr/bin/env node
const fs = require("node:fs")
const path = require("node:path")
const { spawnSync } = require("node:child_process")
const [cmd, ...mods] = process.argv.slice(2)
fs.appendFileSync(${JSON.stringify(join(tmp, "lake-calls"))}, process.argv.slice(2).join(" ") + "\\n")
if (cmd !== "build") process.exit(0)
const hungry = JSON.parse(process.env.FAKE_HUNGRY || "{}")
const imports = JSON.parse(process.env.FAKE_IMPORTS || "{}")
const olean = (m) => path.join(".lake", "build", "lib", "lean", m.split(".").join("/") + ".olean")
const result = new Map()
const build = (m) => {
  if (fs.existsSync(olean(m))) return true
  if (result.has(m)) return result.get(m)
  for (const i of imports[m] || []) if (!build(i)) { result.set(m, false); return false }
  if (hungry[m]) {
    const file = path.join(process.cwd(), m.split(".").join("/") + ".lean")
    const r = spawnSync(process.execPath, ["-e", "const b = Buffer.alloc(" + hungry[m] + " * 1024 * 1024, 1); Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, " + (process.env.FAKE_HOLD_MS || 4000) + "); process.exit(b.length ? 0 : 1)", "--", file, "-R", "."])
    if (r.status !== 0) { result.set(m, false); return false }
  }
  fs.mkdirSync(path.dirname(olean(m)), { recursive: true })
  fs.writeFileSync(olean(m), "")
  result.set(m, true)
  return true
}
let ok = true
for (const m of mods) if (!build(m)) ok = false
process.exit(ok ? 0 : 1)
`)
chmodSync(join(bin, "elan"), 0o755)
chmodSync(join(bin, "lake"), 0o755)

const repo = join(root, "infra", "t", "repo")
const olean = (m) => join(repo, ".lake", "build", "lib", "lean", "Lib", `${m}.olean`)
const memo = join(repo, ".lake", "build", "emissary-oom.json")
const IMPORTS = JSON.stringify({ "Lib.C": ["Lib.A"], "Lib.D": ["Lib.C"], "Lib.E": ["Lib.A"], "Lib.F": ["Lib.A"] })
// a watchdog that looks every 300 ms, a limit of 150 MB for a process, 500 MB for one built alone
const setup = (args, env = {}) =>
  spawnSync("node", [join(root, "scripts", "setup-source.mjs"), "t", ...args], {
    env: { ...process.env, HOME: home, FAKE_IMPORTS: IMPORTS, EMISSARY_WATCH_MS: "300", EMISSARY_FOOTPRINT_MB: "150", EMISSARY_RETRY_FOOTPRINT_MB: "500", ...env },
    encoding: "utf8",
  })
const calls = () => (existsSync(join(tmp, "lake-calls")) ? readFileSync(join(tmp, "lake-calls"), "utf8").trim().split("\n") : [])
const fresh = () => { rmSync(join(repo, ".lake"), { recursive: true, force: true }); rmSync(join(tmp, "lake-calls"), { force: true }) }
const statusOf = () => JSON.parse(readFileSync(join(root, "infra", "t", "build-status.json"), "utf8"))
const out = (r) => r.stdout + r.stderr

// 1. a module that needs 300 MB under a limit of 150: killed in the chunk, named, built alone under 500, and the modules behind it follow
fresh()
let r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 300 }) })
check("a killed module is built alone with the higher limit, and what imports it is built after it", r.status === 0 && names.every((m) => existsSync(olean(m))), out(r))
check("the watchdog's line names the module (it used to cut the command off before it)", /memory watchdog: killed \d+ at \d+ MB \(limit 150 MB\), module Lib\.C/.test(r.stdout), r.stdout)
check("the build says it builds the module alone, and that it worked", /Lib\.C was killed at \d+ MB .*building it alone, limit 500 MB/.test(r.stdout) && /Lib\.C built alone/.test(r.stdout), r.stdout)
check("lake is asked for the module alone", calls().includes("build Lib.C"), calls().join("\n"))
check("a module that fits after all is not remembered as too big", !existsSync(memo) || Object.keys(JSON.parse(readFileSync(memo, "utf8")).toobig).length === 0, "")
r = setup(["--phase", "build-status"])
check("status after the rescue: complete, nothing too big", /^complete=true$/m.test(r.stdout) && /^toobig=0$/m.test(r.stdout) && /^blocked=0$/m.test(r.stdout), r.stdout)

// 2. a module that needs 700 MB does not fit under 500 either: remembered, and D (which imports it) is left out
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 700 }) })
check("the build finishes (it does not fail the round) with what fits built", r.status === 0 && existsSync(olean("A")) && existsSync(olean("E")) && existsSync(olean("F")), out(r))
check("the too-big module and the one importing it are not built", !existsSync(olean("C")) && !existsSync(olean("D")), "")
check("the build says the module did not fit alone either, and how many modules wait behind it", /Lib\.C did not build alone either \(killed at \d+ MB, limit 500 MB\): it and the 1 modules that import it are left out/.test(r.stdout), r.stdout)
const saved = existsSync(memo) ? JSON.parse(readFileSync(memo, "utf8")) : null
check("the module is written to the build folder, which is what gets packed", saved?.toobig?.["Lib.C"]?.capMB === 500 && saved.toobig["Lib.C"].peakMB >= 500, JSON.stringify(saved))
r = setup(["--phase", "build-status"])
const st = statusOf()
check("status says why: 1 too big, 1 blocked behind it, nothing unexplained", /^toobig=1$/m.test(r.stdout) && /^blocked=1$/m.test(r.stdout) && st.complete === false && st.built === 3 && st.other === 0 && st.toobig[0].module === "Lib.C" && st.toobig[0].blocks === 1, JSON.stringify(st))
const summary = readFileSync(join(root, "infra", "t", "unbuilt-summary.md"), "utf8")
check("the run summary names the module and the size", /Modules without an \.olean: 2 of 5/.test(summary) && /`Lib\.C`: killed at \d+ MB with a limit of 500 MB; 1 modules import it/.test(summary), summary)

// 3. the next round (the memo comes back with the build): the module is not tried again, and neither is anything behind it
const before = calls().length
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 700 }) })
const later = calls().slice(before)
check("the next round does not kill it again", r.status === 0 && !/memory watchdog: killed/.test(r.stdout), r.stdout)
check("the next round does not ask lake for the too-big module or what imports it", later.length > 0 && later.every((c) => !/Lib\.C|Lib\.D/.test(c)), later.join("\n"))
check("the next round says what it is leaving out", /1 modules did not fit in 500 MB in an earlier round; they and the 1 modules that import them are not built again/.test(r.stdout), r.stdout)

// 4. a higher limit tries the module again (it was remembered under 500; with 900 it is worth another go)
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 700 }), EMISSARY_RETRY_FOOTPRINT_MB: "900" })
check("raising the limit forgets the entry, and the module is built", r.status === 0 && names.every((m) => existsSync(olean(m))) && !/Lib\.C did not build alone/.test(r.stdout), out(r))

// 5. the memo is an artifact: anything in it that is not a module name with two numbers is ignored
fresh()
mkdirSync(dirname(memo), { recursive: true })
writeFileSync(memo, JSON.stringify({ version: 1, toobig: { "Lib.C; rm -rf /": { peakMB: 1, capMB: 99999 }, "Lib.D": { peakMB: "big", capMB: 99999 }, "Lib.E": { peakMB: 5 }, "": { peakMB: 1, capMB: 99999 } } }))
r = setup(["--phase", "build-status"])
check("a memo with bad names and bad numbers names nothing", /^toobig=0$/m.test(r.stdout) && statusOf().toobig.length === 0, r.stdout)
writeFileSync(memo, "{ not json")
r = setup(["--phase", "build-status"])
check("a memo that is not JSON is not an error", r.status === 0 && /^toobig=0$/m.test(r.stdout), out(r))

// 6. only EMISSARY_SOLO_MAX modules are built alone in one run: the others wait for the next round and are not remembered as too big
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 300, "Lib.F": 300 }), EMISSARY_SOLO_MAX: "1" })
const rescued = ["C", "F"].filter((m) => existsSync(olean(m)))
check("with a limit of one module built alone, one is rescued and the other waits for the next round", r.status === 0 && rescued.length === 1 && /modules were built alone in this run already, so it waits for the next round/.test(r.stdout), out(r))
check("the one that waited is not remembered as too big", !existsSync(memo) || Object.keys(JSON.parse(readFileSync(memo, "utf8")).toobig).length === 0, "")

rmSync(tmp, { recursive: true, force: true })
process.exit(bad ? 1 : 0)

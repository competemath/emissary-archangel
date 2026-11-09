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
const CHAIN = 6 // G1 imports A, G2 imports G1, ... (a `Thm_` module imports its `P2M.Sol` proof: each try of the chunk finds one new kill)
const files = { A: "", C: "import Lib.A\n", D: "-- header comment\n/- outer\n/- nested -/\nstill the outer comment -/\nimport Lib.C\n", E: "import Lib.A\n", F: "/- block\ncomment -/\nimport Lib.A -- trailing\n" }
for (const [m, imp] of Object.entries(files)) writeFileSync(join(lib, "Lib", `${m}.lean`), `${imp}\ntheorem t_${m.toLowerCase()} : True := trivial\n`)
const TC = "leanprover/lean4:v4.0.0"
writeFileSync(join(lib, "lean-toolchain"), TC + "\n")
for (let i = 1; i <= CHAIN; i++) writeFileSync(join(lib, "Lib", `G${i}.lean`), `import Lib.${i === 1 ? "A" : `G${i - 1}`}\n\ntheorem t_g${i} : True := trivial\n`)
for (let i = 1; i <= CHAIN; i++) files[`G${i}`] = "" // only their names are needed below
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
cpSync(join(here, "bisect.mjs"), join(root, "scripts", "bisect.mjs"))
cpSync(join(here, "memory-rules.mjs"), join(root, "scripts", "memory-rules.mjs"))
cpSync(join(here, "pinned-deps.mjs"), join(root, "scripts", "pinned-deps.mjs"))
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
const failAlone = JSON.parse(process.env.FAKE_FAIL_ALONE || "[]")
const brokenMods = JSON.parse(process.env.FAKE_BROKEN || "[]")
const failElsewhere = JSON.parse(process.env.FAKE_FAIL_ELSEWHERE || "[]")
const chatty = JSON.parse(process.env.FAKE_BROKEN_CHATTY || "[]")
const errorAlone = JSON.parse(process.env.FAKE_ERROR_ALONE || "[]")
const olean = (m) => path.join(".lake", "build", "lib", "lean", m.split(".").join("/") + ".olean")
const result = new Map()
const build = (m) => {
  if (fs.existsSync(olean(m))) return true
  if (result.has(m)) return result.get(m)
  for (const i of imports[m] || []) if (!build(i)) { result.set(m, false); return false }
  if (mods.length === 1 && errorAlone.includes(m)) { console.log("error: " + m.split(".").join("/") + ".lean:940:8: (kernel) deterministic timeout"); result.set(m, false); return false } // killed in a chunk, then a real error alone
  if (mods.length === 1 && failAlone.includes(m)) { result.set(m, false); return false } // a compile error that only shows alone, not a kill
  // does not compile at all: Lake's own error line for the module's file, as tnlean's TNLean/Archive/BlockingPeriodicityCFII2.lean printed it on 2026-11-06
  // fails, but the error Lake prints is in ANOTHER file (a dependency's, a generated one): not this module's own error
  if (failElsewhere.includes(m)) { console.log("error: Lib/Generated.lean:1:1: something else"); result.set(m, false); return false }
  if (chatty.includes(m)) { console.log("error: " + m.split(".").join("/") + ".lean:78:8: (kernel) deterministic timeout"); for (let i = 0; i < 400; i++) console.log("warning: " + m.split(".").join("/") + ".lean:" + i + ":2: Try this: omit [CommRing A] in theorem"); result.set(m, false); return false }
  if (brokenMods.includes(m)) { console.log("error: " + m.split(".").join("/") + ".lean:694:4: Unknown identifier \`isIrreducibleCP_transferMap_of_isIrreducibleTensor\`"); console.log("error: Lean exited with code 1"); result.set(m, false); return false }
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
const IMPORTS = JSON.stringify({ "Lib.C": ["Lib.A"], "Lib.D": ["Lib.C"], "Lib.E": ["Lib.A"], "Lib.F": ["Lib.A"], "Lib.G1": ["Lib.A"], ...Object.fromEntries(Array.from({ length: CHAIN - 1 }, (_, k) => [`Lib.G${k + 2}`, [`Lib.G${k + 1}`]])) })
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
check("status says why: 1 too big, 1 blocked behind it, nothing unexplained, so no further round can add anything: complete", /^toobig=1$/m.test(r.stdout) && /^blocked=1$/m.test(r.stdout) && /^complete=true$/m.test(r.stdout) && st.complete === true && st.built === names.length - 2 && st.other === 0 && st.toobig[0].module === "Lib.C" && st.toobig[0].blocks === 1, JSON.stringify(st))
const summary = readFileSync(join(root, "infra", "t", "unbuilt-summary.md"), "utf8")
check("the run summary names the module and the size", new RegExp(`Modules without an \\.olean: 2 of ${names.length}`).test(summary) && /`Lib\.C`: killed at \d+ MB with a limit of 500 MB; 1 modules import it/.test(summary), summary)

// 3. the next round (the memo comes back with the build): the module is not tried again, and neither is anything behind it
const before = calls().length
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 700 }) })
const later = calls().slice(before)
check("the next round does not kill it again", r.status === 0 && !/memory watchdog: killed/.test(r.stdout), r.stdout)
check("the next round does not ask lake for the too-big module or what imports it", later.length > 0 && later.every((c) => !/Lib\.C|Lib\.D/.test(c)), later.join("\n"))
check("the next round says what it is leaving out", /1 modules did not fit in 500 MB in an earlier round; they and the 1 modules that import them are not built again/.test(r.stdout), r.stdout)

// 4. a higher limit tries the module again (it was remembered under 500; with 900 it is worth another go)
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 700 }), EMISSARY_RETRY_FOOTPRINT_MB: "900" })
check("raising the limit forgets the entry (in the file too), and the module is built", r.status === 0 && names.every((m) => existsSync(olean(m))) && !/Lib\.C did not build alone/.test(r.stdout) && (!existsSync(memo) || !Object.hasOwn(JSON.parse(readFileSync(memo, "utf8")).toobig ?? {}, "Lib.C")), out(r))

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
const waited = ["C", "F"].find((m) => !existsSync(olean(m)))
check("with a limit of one module built alone, one is rescued and the other waits for the next round", r.status === 0 && rescued.length === 1 && /modules were built alone in this run already, so it waits for the next round/.test(r.stdout), out(r))
check("the one that waits is not asked of lake again in this run (it is in the first chunk only)", waited !== undefined && calls().filter((c) => c.split(" ").includes(`Lib.${waited}`)).length === 1, calls().join("\n"))
check("the one that waited is not remembered as too big", !existsSync(memo) || Object.keys(JSON.parse(readFileSync(memo, "utf8")).toobig).length === 0, "")

// 7. killed in the chunk, but alone it fails for another reason (a compile error, a timeout): not memory, so NOT remembered as too big (that would block its importers for good)
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 300 }), FAKE_FAIL_ALONE: JSON.stringify(["Lib.C"]) })
check("a module that fails alone without a watchdog kill is said so, not called too big", r.status === 0 && /Lib\.C failed alone without a watchdog kill/.test(r.stdout) && !/did not build alone either/.test(r.stdout), out(r))
check("and it is not written to the memo", !existsSync(memo) || Object.keys(JSON.parse(readFileSync(memo, "utf8")).toobig).length === 0, "")
r = setup(["--phase", "build-status"])
check("status counts it as missing for another reason, with the module behind it", /^toobig=0$/m.test(r.stdout) && statusOf().other === 2 && statusOf().blocked === 0, JSON.stringify(statusOf()))

// 8. a chain of big modules, each importing the one before: every try of the chunk finds ONE new kill (the 86 of flt-anthropic: a Thm_ module imports its P2M.Sol proof, round 4 of
// 2026-11-05 finished 4 of them in 4 tries and the next round started from a 28 minute restore). A build with the default 4 tries leaves the end of the chain for the next round;
// a build with the tries the escalation gives (EMISSARY_BUILD_ATTEMPTS here, memory-rules.mjs buildAttempts for the real rule) finishes it in one run.
const gs = Array.from({ length: CHAIN }, (_, i) => i + 1)
const hungryChain = JSON.stringify(Object.fromEntries(gs.map((i) => [`Lib.G${i}`, 300])))
const gBuilt = () => gs.filter((i) => existsSync(olean(`G${i}`)))
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: hungryChain, FAKE_HOLD_MS: "3000", EMISSARY_SOLO_MAX: "50" })
check("default tries (4): the first four of a chain of six big modules are built, the last two wait for the next round", r.status === 0 && gBuilt().join() === gs.slice(0, 4).join(), `${gBuilt()}\n${out(r)}`)
check("the two that wait are not remembered as too big", !existsSync(memo) || Object.keys(JSON.parse(readFileSync(memo, "utf8")).toobig).length === 0, "")
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: hungryChain, FAKE_HOLD_MS: "3000", EMISSARY_SOLO_MAX: "50", EMISSARY_BUILD_ATTEMPTS: "20" })
check("20 tries: the whole chain is built in one run, each module alone after its own kill", r.status === 0 && gBuilt().join() === gs.join() && gs.every((i) => new RegExp(`Lib\\.G${i} built alone`).test(r.stdout)), `${gBuilt()}\n${out(r)}`)
check("and the build says it is complete", (setup(["--phase", "build-status"]).stdout.match(/^complete=true$/m) ?? []).length === 1, "")
// the tries are a limit, not a promise: a chain whose modules do not fit even alone stops at the first one (nothing is rescued, so the chunk is not tried again and again)
fresh()
const before8 = calls().length
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.G1": 700, "Lib.G2": 700 }), FAKE_HOLD_MS: "3000", EMISSARY_BUILD_ATTEMPTS: "1000" })
const lakeCalls = calls().slice(before8).filter((c) => c.startsWith("build "))
check("1000 tries, a module that does not fit alone: the chunk is not tried over and over (a try that rescues nothing ends it)", r.status === 0 && lakeCalls.length <= 4 && /Lib\.G1 did not build alone either/.test(r.stdout), `${lakeCalls.length} lake builds\n${out(r)}`)

// 9. a module that does not compile at the library's own commit (an error in its own file, its imports built): tnlean, 2026-11-06, 1,155 of 1,156 modules built and the
// chain stopped because the next round added nothing, so nothing was exported. It is written down as broken, the build is complete without it (and what imports it),
// and the shards export the rest.
const brokenMemo = join(repo, ".lake", "build", "emissary-broken.json")
fresh()
r = setup(["--phase", "build"], { FAKE_BROKEN: JSON.stringify(["Lib.C"]) })
const bm = existsSync(brokenMemo) ? JSON.parse(readFileSync(brokenMemo, "utf8")).broken : {}
check("a module with an error in its own file is recorded as broken, with Lake's error line", r.status === 0 && Object.keys(bm).join() === "Lib.C" && /BlockingPeriodicityCFII2|Lib\/C\.lean:694:4: Unknown identifier/.test(bm["Lib.C"].error) && /broken: Lib\.C does not compile at this commit/.test(r.stdout), out(r))
r = setup(["--phase", "build-status"])
check("the build is complete without it and the module that imports it (D)", /^complete=true$/m.test(r.stdout) && statusOf().other === 0 && statusOf().blocked === 1 && statusOf().broken.map((b) => b.module).join() === "Lib.C", JSON.stringify(statusOf()))
check("the others are built", ["A", "E", "F"].every((m) => existsSync(olean(m))) && !existsSync(olean("D")), "")
// the next round does not try it again (it is blocked like a too-big one) and the record survives the round
const before9 = calls().length
r = setup(["--phase", "build"], { FAKE_BROKEN: JSON.stringify(["Lib.C"]) })
const round2 = calls().slice(before9).join("\n")
check("a second round does not hand the broken module or its importer to lake", !/\bLib\.C\b/.test(round2) && !/\bLib\.D\b/.test(round2), round2)
check("a second round keeps the record and says nothing new about it", r.status === 0 && Object.keys(JSON.parse(readFileSync(brokenMemo, "utf8")).broken).join() === "Lib.C" && !/broken: Lib\.C/.test(r.stdout), out(r))

// 9b. the export shard that holds a broken module and nothing else left to build: the build must not stop the shard as "none of the 1 modules" (tnlean, 2026-11-07: the
// module was never recorded as failed and the export rounds went on forever). Here: the broken record is there, and the build is asked for that module only.
r = setup(["--phase", "build"], { FAKE_BROKEN: JSON.stringify(["Lib.C"]), EMISSARY_ONLY_MODULES: "Lib.C" })
check("a build asked only for a module recorded as broken does not stop the job", r.status === 0 && !/produced none of the/.test(out(r)), out(r))
r = setup(["--phase", "build"], { FAKE_BROKEN: JSON.stringify(["Lib.C"]), EMISSARY_ONLY_MODULES: "Lib.D" })
check("nor does a build asked only for a module that imports one (D imports the broken C)", r.status === 0 && !/produced none of the/.test(out(r)), out(r))

// 9c. aintlib, 9 Nov 2026: the error line came before thousands of characters of warnings, so it was no longer in the last 4,000 characters of what the command printed
fresh()
r = setup(["--phase", "build"], { FAKE_BROKEN_CHATTY: JSON.stringify(["Lib.C"]) })
check("an error followed by thousands of characters of warnings still makes the module broken", r.status === 0 && existsSync(brokenMemo) && Object.keys(JSON.parse(readFileSync(brokenMemo, "utf8")).broken).join() === "Lib.C" && /deterministic timeout/.test(JSON.stringify(JSON.parse(readFileSync(brokenMemo, "utf8")).broken)), out(r))
check("and the build is complete without it", /^complete=true$/m.test(setup(["--phase", "build-status"]).stdout), "")
// 9d. aintlib, 9 Nov 2026: killed for memory in a chunk, then a real error when built alone with room. It is left out for the round before the broken probe, so the probe never saw it
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 300 }), FAKE_ERROR_ALONE: JSON.stringify(["Lib.C"]) })
check("a module killed in a chunk that then fails alone with an error in its own file is broken", r.status === 0 && existsSync(brokenMemo) && Object.keys(JSON.parse(readFileSync(brokenMemo, "utf8")).broken).join() === "Lib.C" && /deterministic timeout/.test(JSON.stringify(JSON.parse(readFileSync(brokenMemo, "utf8")).broken)), out(r))
check("and the build is complete without it and what imports it", /^complete=true$/m.test(setup(["--phase", "build-status"]).stdout) && statusOf().other === 0, JSON.stringify(statusOf()))
// 10. NOT broken: a module that fails without an error line of its own file (case 7's compile error that only shows alone, printed nowhere), a module whose import is missing
// (D imports C, which was killed for memory: its import has no .olean, so it is never probed), and one whose error line is in another file
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 300 }), FAKE_FAIL_ALONE: JSON.stringify(["Lib.C"]) })
check("a failure without an error line of the module's own file is not called broken", r.status === 0 && !existsSync(brokenMemo), out(r))
check("so the build is not complete (it may build next round)", /^complete=false$/m.test(setup(["--phase", "build-status"]).stdout), "")
fresh()
r = setup(["--phase", "build"], { FAKE_HUNGRY: JSON.stringify({ "Lib.C": 700 }) })
check("a module behind one too big for memory is not called broken (D imports C, which was killed)", r.status === 0 && !existsSync(brokenMemo), out(r))
// a module that fails with an error in a different file, its imports built and nothing killed: probed, and NOT called broken
fresh()
r = setup(["--phase", "build"], { FAKE_FAIL_ELSEWHERE: JSON.stringify(["Lib.E"]) })
check("a failure whose error line names another file is not called broken", r.status === 0 && !existsSync(brokenMemo) && !existsSync(olean("E")) && calls().some((c) => c === "build Lib.E"), out(r) + calls().join("\n"))
check("and the build is not complete", /^complete=false$/m.test(setup(["--phase", "build-status"]).stdout), "")
// a record from an artifact is data: anything that is not a module name with an error text is dropped
fresh()
mkdirSync(dirname(brokenMemo), { recursive: true })
writeFileSync(brokenMemo, JSON.stringify({ version: 1, commit, broken: { "Lib.C": { error: "error: x" }, "bad name;rm": { error: "e" }, "Lib.E": { error: 7 } } }))
r = setup(["--phase", "build-status"])
check("a malformed broken record keeps only the well-formed entry", statusOf().broken.map((b) => b.module).join() === "Lib.C", JSON.stringify(statusOf()))
// a record made at another commit of the library says nothing about this one (a re-pin may have fixed the file)
writeFileSync(brokenMemo, JSON.stringify({ version: 1, commit: "0".repeat(40), broken: { "Lib.C": { error: "error: x" } } }))
r = setup(["--phase", "build-status"])
check("a broken record of another library commit is ignored", statusOf().broken.length === 0, JSON.stringify(statusOf()))
writeFileSync(brokenMemo, JSON.stringify({ version: 1, broken: { "Lib.C": { error: "error: x" } } }))
r = setup(["--phase", "build-status"])
check("so is one that names no commit", statusOf().broken.length === 0, JSON.stringify(statusOf()))

rmSync(tmp, { recursive: true, force: true })
process.exit(bad ? 1 : 0)

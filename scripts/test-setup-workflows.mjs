// node scripts/test-setup-workflows.mjs — what the setup workflows may and may not do (exits 1 on a violation).
// Textual, no YAML library: the checks are on the job blocks of .github/workflows/setup-sharded.yml and setup-auto.yml.
//   - a job that runs the library's own code (prime: lake build; shard: lake build and lean) holds no write permission;
//   - the one job that dispatches the next build round runs no code from the library: it checks nothing out;
//   - the shards and the finish job start only on a complete build (or the legacy no-prime flow, or a bank_run);
//   - a build round that did nothing is not followed by another (build-gate stops with the numbers; ONE issue is opened or updated by a job that holds issues: write and nothing else);
//   - setup-auto.yml dispatches and writes nothing else, and its values reach the shell through env, never inline.
import { spawnSync } from "node:child_process"
import { chmodSync, existsSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { roundProgress, roundsCap, slicedSwitch, escalation, ESCALATE_RETRY_MB, ESCALATE_SWAP_GB, ESCALATE_SOLO_MINUTES } from "./setup-plan.mjs"

const wf = join(dirname(fileURLToPath(import.meta.url)), "..", ".github", "workflows")
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name)
}
const jobsOf = (file) => {
  const text = readFileSync(join(wf, file), "utf8")
  const after = text.slice(text.indexOf("\njobs:\n") + 6)
  const jobs = {}
  let name = null
  for (const line of after.split("\n")) {
    const m = line.match(/^  ([a-z][a-z-]*):\s*$/)
    if (m) { name = m[1]; jobs[name] = []; continue }
    if (name) jobs[name].push(line)
  }
  return Object.fromEntries(Object.entries(jobs).map(([k, v]) => [k, v.join("\n")]))
}
const permissionsOf = (block) => (block.match(/^    permissions:\s*(.*)$/m) || [])[1] ?? null
const writes = (perm) => perm == null || /write/.test(perm)

const sharded = jobsOf("setup-sharded.yml")
check("setup-sharded has prime, build-gate, shard and finish", ["prime", "build-gate", "shard", "finish"].every((j) => j in sharded), Object.keys(sharded))
check("prime runs the library's build and holds no write permission", /lake|setup-source\.mjs/.test(sharded.prime) && !writes(permissionsOf(sharded.prime)) , permissionsOf(sharded.prime))
check("shard runs the library's build and holds no write permission", /--phase shard/.test(sharded.shard) && !writes(permissionsOf(sharded.shard)), permissionsOf(sharded.shard))
check("build-gate may dispatch (actions: write) and nothing else", /actions:\s*write/.test(permissionsOf(sharded["build-gate"]) || "") && !/contents/.test(permissionsOf(sharded["build-gate"]) || ""), permissionsOf(sharded["build-gate"]))
check("build-gate checks nothing out and runs no node, lake or lean", !/actions\/checkout|setup-node|setup-source|\blake\b|\blean\b|elan/.test(sharded["build-gate"].replace(/#.*$/gm, "")), "")
check("build-gate sends only numbers to the dispatch, checked first", /\^\[0-9\]\+\$/.test(sharded["build-gate"]) && !/\$\{\{\s*needs\.prime\.outputs[^}]*\}\}[^\n]*gh workflow run/.test(sharded["build-gate"]), "")
check("build-gate stops at max_build_rounds", /BUILD_ROUND" -ge "\$MAX_BUILD_ROUNDS"/.test(sharded["build-gate"]), "")
check("build-gate runs only when the build is incomplete", /needs\.prime\.outputs\.complete != 'true'/.test(sharded["build-gate"]), "")
check("shard starts only on a complete build (or without a prime)", /prime_minutes == '0' \|\| \(needs\.prime\.outputs\.complete == 'true' && needs\.prime\.outputs\.escalate != 'true'\)/.test(sharded.shard.split("runs-on")[0]), "")
check("finish starts only on a complete build (or a bank_run, or without a prime)", /inputs\.bank_run != '' \|\| inputs\.prime_minutes == '0' \|\| \(needs\.prime\.outputs\.complete == 'true' && needs\.prime\.outputs\.escalate != 'true'\)/.test(sharded.finish.split("runs-on")[0]), "")
check("the complete word is cut down to true or false before it is an output", /grep -E '\^complete=\(true\|false\)\$'/.test(sharded.prime), "")
check("the prime job restores the previous build and goes on if it has expired", /continue-on-error: true/.test(sharded.prime.split("Build what fits")[0].split("The previous round's build")[1] || ""), "")
check("build-gate forwards tengoku_ref, as the export round does (after checking it is a branch name)", /-f tengoku_ref="\$TENGOKU_REF"/.test(sharded["build-gate"]) && /TENGOKU_REF" =~ \^\[A-Za-z0-9\._\/-\]\*\$/.test(sharded["build-gate"]), "")
check("the export round forwards tengoku_ref", /-f tengoku_ref="\$TENGOKU_REF"/.test(sharded.finish), "")
check("the build is packed without the setup.json files, which unpack to 90 GB", /tar --zstd --exclude='\*\.setup\.json' -cf build\.tar\.zst/.test(sharded.prime), "")
check(
  "the cleanup loops look in the Lake project (repo/<subdir>), not in the repo root, in both the prime and the shard job",
  [sharded.prime, sharded.shard].every((job) => /sub=\$\(python3 -c "[^"]*\.get\('subdir', ''\)\)"\)/.test(job) && /find "infra\/\$KEY\/repo\/\$sub\/\.lake\/build\/ir"/.test(job) && !/find "infra\/\$KEY\/repo\/\.lake/.test(job)),
  "",
)
check(
  "the cleaner is stopped right after the build in both jobs, before the build is packed (a running cleaner made tar fail after 5 hours)",
  [sharded.prime, sharded.shard].every((job) => /cleaner=\$!/.test(job) && /kill "\$cleaner"/.test(job)) && sharded.prime.indexOf('kill "$cleaner"') < sharded.prime.indexOf("- name: Pack the build"),
  "",
)
check(
  "the prime job's watcher (one metrics line a minute) is stopped with the cleaner, before the build is packed, and its summary and file are kept even when the build step fails",
  /watcher=\$!/.test(sharded.prime) && /kill "\$watcher"/.test(sharded.prime) && sharded.prime.indexOf('kill "$watcher"') < sharded.prime.indexOf("- name: Pack the build") &&
    /name: This round in numbers\n\s+if: always\(\)/.test(sharded.prime) && /if: always\(\) && inputs\.prime_minutes != '0'\n\s+with: \{ name: "build-metrics-\$\{\{ inputs\.build_round \}\}", path: build-metrics\.tsv/.test(sharded.prime) &&
    !/run: \|[^]*\$\{\{ inputs\.build_round \}\}[^]*- uses: actions\/upload-artifact/.test(sharded.prime.slice(sharded.prime.indexOf("- name: This round in numbers"), sharded.prime.indexOf("- name: Is the build complete?"))),
  "",
)
check("tar exit 1 (a file changed while it was read) does not lose the round: only other exit codes fail the pack step", /\|\| \{ rc=\$\?; \[ "\$rc" -eq 1 \] \|\| exit "\$rc"/.test(sharded.prime), "")
check("prime and shard delete old setup.json files while they build", (sharded.prime.match(/-name '\*\.setup\.json' -mmin \+15 -delete/g) || []).length === 1 && (sharded.shard.match(/-name '\*\.setup\.json' -mmin \+15 -delete/g) || []).length === 1, "")
check("the next export round carries max_build_rounds on", /-f max_build_rounds="\$MAX_BUILD_ROUNDS"/.test(sharded.finish), "")

// ---- a build round that did nothing ----
const gate = sharded["build-gate"]
const report = sharded["report-stall"] || ""
const inputsOf = readFileSync(join(wf, "setup-sharded.yml"), "utf8").split("\n  prime:\n")[0]
check("prev_built (default empty) and min_progress (default 1) are workflow inputs", /\n      prev_built:\n(?:        .*\n)*?        default: ""\n/.test(inputsOf) && /\n      min_progress:\n(?:        .*\n)*?        default: "1"\n/.test(inputsOf), "")
check("the prime job hands the build-gate its counts, each cut down to a decimal number first", /built: \$\{\{ steps\.status\.outputs\.built \}\}/.test(sharded.prime) && /\^\$\{name\}=\(0\|\[1-9\]\[0-9\]\{0,8\}\)\$/.test(sharded.prime) && /for name in built modules/.test(sharded.prime), "")
check("the counts reach the build-gate through env, are validated before use, and prev_built is passed on to the next round", /BUILT: \$\{\{ needs\.prime\.outputs\.built \}\}/.test(gate) && /\^\(0\|\[1-9\]\[0-9\]\{0,8\}\)\$/.test(gate) && /-f prev_built="\$BUILT"/.test(gate) && /-f min_progress="\$MIN_PROGRESS"/.test(gate), "")
check("build-gate stops with an ::error:: holding the numbers, before it dispatches anything", /::error::[^\n]*\$BUILT[^\n]*\$PREV_BUILT[^\n]*\$added/.test(gate) && gate.indexOf("made no progress") > 0 && gate.indexOf("made no progress") < gate.lastIndexOf("gh workflow run"), "")
check("build-gate judges only a round after the first", /if \[ "\$BUILD_ROUND" -gt 1 \] && \[ -n "\$PREV_BUILT" \] && \[ -n "\$BUILT" \]/.test(gate), "")
check("build-gate still holds actions: write and nothing else (the issue is written by another job)", /^\{ actions: write \}$/.test(permissionsOf(gate) || ""), permissionsOf(gate))
check("report-stall holds issues: write and nothing else, and no other job holds it", /^\{ issues: write \}$/.test(permissionsOf(report) || "") && Object.keys(sharded).filter((j) => /issues/.test(permissionsOf(sharded[j]) || "")).join() === "report-stall", permissionsOf(report))
check("report-stall runs only after a stop of the build-gate, and runs none of the library's code (no checkout, node, lake, lean, elan)", /needs: build-gate/.test(report) && /needs\.build-gate\.outputs\.stalled == 'true'/.test(report) && !/actions\/checkout|setup-node|setup-source|\bnode\b|\blake\b|\blean\b|elan|download-artifact/.test(report.replace(/#.*$/gm, "")), "")
check("report-stall: one issue, titled \"setup <key>: build round made no progress\", opened when none is open and edited when one is", /title="setup \$KEY: build round made no progress"/.test(report) && /gh issue list[^\n]*--state open[^\n]*in:title/.test(report) && /\.title == \$t/.test(report) && /gh issue edit "\$number"/.test(report) && /gh issue create[^\n]*--title "\$title"/.test(report), "")
check("report-stall: the key and the numbers are checked before use, and no ${{ }} expression sits in its shell", /KEY" =~ \^\[a-z0-9\]\[a-z0-9-\]\*\$/.test(report) && /BUILT" "\$PREV_BUILT"/.test(report) && !/run: \|[^]*\$\{\{/.test(report.slice(report.indexOf("run: |"))), "")

// The shell of the build-gate against the rule (setup-plan.mjs roundProgress), run for real with a fake `gh`, on enumerated boundaries and random rounds.
const stepRun = (block, name) => {
  const at = block.indexOf(`- name: ${name}`)
  const lines = block.slice(at).split("\n")
  const i = lines.findIndex((l) => /^ {8}run: \|$/.test(l))
  const out = []
  for (const l of lines.slice(i + 1)) { if (l.trim() && !/^ {10}/.test(l)) break; out.push(l.replace(/^ {10}/, "")) }
  return out.join("\n")
}
const gateScript = stepRun(gate, "Dispatch the next build round")
const envNames = [...gate.slice(gate.indexOf("env:"), gate.indexOf("run: |")).matchAll(/^ {10}([A-Z_]+):/gm)].map((m) => m[1])
check("the harness gives the build-gate step every variable its env defines, and nothing it does not", ["BUILT", "MODULES", "TOOBIG", "BLOCKED", "PREV_BUILT", "MIN_PROGRESS", "BUILD_ROUND", "MAX_BUILD_ROUNDS", "TENGOKU_REF"].every((n) => envNames.includes(n)) && ["ESCALATE", "RETRY_MB", "SWAP_GB", "SOLO_MINUTES", "FROM_RELEASE", "ONLY_MODULES"].every((n) => envNames.includes(n)) && envNames.length === 23, envNames)
const sandbox = mkdtempSync(join(tmpdir(), "gate-"))
writeFileSync(join(sandbox, "gh"), '#!/bin/sh\necho "gh $*" >> "$GH_CALLS"\nexit 0\n')
chmodSync(join(sandbox, "gh"), 0o755)
const runGate = (script, c) => {
  const outFile = join(sandbox, "output"), calls = join(sandbox, "calls")
  writeFileSync(outFile, "")
  writeFileSync(calls, "")
  writeFileSync(join(sandbox, "gate.sh"), script)
  const r = spawnSync("bash", ["--noprofile", "--norc", "-eo", "pipefail", join(sandbox, "gate.sh")], {
    encoding: "utf8",
    env: {
      PATH: `${sandbox}:${process.env.PATH}`, GH_CALLS: calls, GITHUB_OUTPUT: outFile, GITHUB_REPOSITORY: "o/r", GH_TOKEN: "x", KEY: "k",
      SHARDS: "16", PRIME_MINUTES: "300", EXPAND_CHUNK: "1", ROUND: "1", MAX_ROUNDS: "4", PARALLEL: "6", RESUME_RUN: "", GITHUB_RUN_ID: "77", TENGOKU_REF: "", MAX_BUILD_ROUNDS: String(c.maxRounds ?? 99),
      BUILD_ROUND: String(c.round), PREV_BUILT: c.prev, BUILT: c.built, MODULES: c.modules ?? "", MIN_PROGRESS: String(c.min), TOOBIG: c.toobig ?? "", BLOCKED: c.blocked ?? "",
      ESCALATE: c.escalate ?? "", RETRY_MB: c.retry ?? "14336", SWAP_GB: c.swap ?? "0", SOLO_MINUTES: c.solo ?? "90", FROM_RELEASE: c.fromRelease ?? "false", ONLY_MODULES: c.only ?? "",
    },
  })
  return { code: r.status, text: r.stdout + r.stderr, output: readFileSync(outFile, "utf8"), calls: readFileSync(calls, "utf8") }
}
// what the rule says of this case; an empty count is "nothing to compare with"
const expected = (c) => (c.built === "" ? { stop: false } : roundProgress({ round: c.round, prev: c.prev === "" ? null : Number(c.prev), built: Number(c.built), min: c.min }))
const wrong = (script, cases, first = false) => {
  const bad = []
  for (const c of cases) {
    const e = expected(c), g = runGate(script, c)
    const dispatched = g.calls.includes("workflow run")
    let ok
    if (e.stop) ok = g.code !== 0 && !dispatched && g.text.includes("::error::") && [c.built, c.prev, String(e.added)].every((n) => g.text.includes(n)) && /stalled=true/.test(g.output) && g.output.includes(`added=${e.added}`)
    else ok = g.code === 0 && dispatched && g.calls.includes(`prev_built=${c.built}`) && g.calls.includes(`min_progress=${c.min}`) && g.calls.includes(`build_round=${c.round + 1}`) && !/stalled/.test(g.output) && g.text.split("\n").filter(Boolean).every((l) => l.startsWith("::notice::")) // a shell error that is carried on past is no pass
    if (!ok) bad.push({ c, e, code: g.code, calls: g.calls.slice(0, 200), text: g.text.slice(0, 300) })
    if (!ok && first) break
  }
  return bad
}
const cases = []
for (const min of [0, 1, 3]) for (const prev of [0, 30000]) for (const delta of [-2, -1, 0, 1]) for (const round of [1, 3]) cases.push({ round, prev: String(prev), built: String(Math.max(0, prev + min + delta)), min }) // added = min + delta: below, on and over the line
for (const round of [2, 4]) for (const prev of ["500", "30000"]) cases.push({ round, prev, built: "3", min: 0 }) // a count that fell, with min_progress 0: the chain goes on
for (const round of [1, 2, 4]) for (const prev of ["", "5"]) for (const built of ["", "5", "0"]) cases.push({ round, prev, built, min: 1 })
let seed = 7
const rnd = (n) => { seed = (seed + 0x6d2b79f5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) % n }
for (let i = 0; i < 30; i++) { const prev = rnd(30000); cases.push({ round: 1 + rnd(6), prev: rnd(6) === 0 ? "" : String(prev), built: String(Math.max(0, prev + rnd(7) - 3)), min: rnd(4) }) }
const verdicts = wrong(gateScript, cases)
check(`build-gate's shell does what the rule says, on ${cases.length} rounds (boundaries, empty counts, random)`, verdicts.length === 0, verdicts.slice(0, 3))
check("the cases hold both a stop and a dispatch, rounds with and without a count, and a fall at min 0", cases.some((c) => c.min === 0 && c.round > 1 && Number(c.built) < Number(c.prev) && !expected(c).stop) && cases.some((c) => expected(c).stop) && cases.some((c) => !expected(c).stop) && cases.some((c) => c.round > 1 && c.prev === ""), "")

// past the planned number of build rounds (flt-anthropic, 6 Nov 2026: round 6 of 6 built 85 of 86 modules and the chain stopped until a person raised the cap): the plan is a budget, not a wall.
// Every round from 1 to one past the ceiling, every plan size, every kind of count; the shell against roundsCap (and the stall rule that comes first).
{
  const capCases = []
  for (const maxRounds of [1, 2, 6]) for (let round = 1; round <= maxRounds * 3 + 1; round++) for (const [prev, built] of [["", ""], ["100", ""], ["", "100"], ["100", "100"], ["100", "101"], ["100", "186"], ["100", "99"]]) for (const min of [0, 1, 5]) capCases.push({ round, maxRounds, prev, built, min })
  const verdict = (script, c) => {
    const stall = expected(c)
    const cap = stall.stop ? { stop: true } : roundsCap({ round: c.round, maxRounds: c.maxRounds, prev: c.prev === "" ? null : Number(c.prev), built: c.built === "" ? null : Number(c.built), min: c.min })
    const g = runGate(script, { ...c, maxRounds: c.maxRoundsText ?? c.maxRounds })
    const dispatched = g.calls.includes("workflow run")
    return { ok: cap.stop ? g.code !== 0 && !dispatched : g.code === 0 && dispatched && g.calls.includes(`build_round=${c.round + 1}`), c, cap, code: g.code, text: g.text.slice(0, 200) }
  }
  // a plan size written with a leading zero is a decimal number (08 was read as octal and aborted the arithmetic): cubic, #145
  for (const [maxRounds, text] of [[6, "06"], [8, "08"], [9, "09"], [10, "010"]]) for (const round of [maxRounds, maxRounds + 1, maxRounds * 3 - 1, maxRounds * 3]) for (const [prev, built] of [["70", "85"], ["85", "85"]]) capCases.push({ round, maxRounds, maxRoundsText: text, prev, built, min: 1 })
  const bad = capCases.map((c) => verdict(gateScript, c)).filter((v) => !v.ok)
  check(`build-gate past the planned rounds: another round while a round still adds modules, a stop at no gain, no count, or three times the plan, on ${capCases.length} cases`, bad.length === 0, bad.slice(0, 3))
  check("the cap cases hold rounds before, at and past the plan, the ceiling, and both outcomes", capCases.some((c) => c.round === 7 && c.maxRounds === 6 && c.built === "101") && capCases.some((c) => c.round === 18 && c.maxRounds === 6) && capCases.some((c) => c.round < c.maxRounds), "")
  // the escalation round is ONE round that is never followed by another, so the ceiling does not apply to it (cubic, #145): defined here, not left implicit
  for (const round of [6, 17, 18, 40]) {
    const g = runGate(gateScript, { round, maxRounds: 6, prev: "100", built: "100", min: 1, toobig: "4", escalate: "true", fromRelease: "true", only: "Theorem.A" })
    check(`an escalation at round ${round} of a plan of 6 is dispatched whatever the ceiling (it is never followed by another)`, g.code === 0 && g.calls.includes("retry_mb=57344") && g.calls.includes(`build_round=${round + 1}`), g.text.slice(0, 200))
  }
  // an enormous plan size would overflow the shell arithmetic of the ceiling (cubic, #145): refused with a message, nothing dispatched
  for (const huge of ["9223372036854775808", "99999999999999999999", "10000"]) {
    const g = runGate(gateScript, { round: 7, maxRounds: huge, prev: "70", built: "85", min: 1 })
    check(`a max_build_rounds of ${huge} is refused before any arithmetic`, g.code !== 0 && !g.calls.includes("workflow run") && /at most four digits/.test(g.text), g.text.slice(0, 200))
  }
  const messages = runGate(gateScript, { round: 6, maxRounds: 6, prev: "70", built: "85", min: 1 })
  check("the notice at the boundary says the planned round was reached and names the ceiling, the next one says planned and ceiling", /reached the planned 6/.test(messages.text) && /ceiling 18/.test(messages.text) && /planned 6, ceiling 18/.test(messages.text), messages.text)
  const stop = runGate(gateScript, { round: 7, maxRounds: 6, prev: "", built: "", min: 1 })
  check("a stop without counts says that the counts are not available", stop.code !== 0 && /is not available/.test(stop.text) && /planned 6, ceiling 18/.test(stop.text), stop.text)
  const capMutants = {
    "the octal trap is back": gateScript.replace("ceiling=$(( 10#$MAX_BUILD_ROUNDS * 3 ))", "ceiling=$(( MAX_BUILD_ROUNDS * 3 ))"),
    "the plan is a wall again": gateScript.replace('if [ "$BUILD_ROUND" -lt "$ceiling" ] && [ -n "$PREV_BUILT" ] && [ -n "$BUILT" ] && [ $(( 10#$BUILT - 10#$PREV_BUILT )) -ge "$need" ]; then', "if false; then"),
    "no ceiling": gateScript.replace('[ "$BUILD_ROUND" -lt "$ceiling" ] && ', ""),
    "progress is not asked for": gateScript.replace(' && [ $(( 10#$BUILT - 10#$PREV_BUILT )) -ge "$need" ]', ""),
    "any gain will do, min_progress ignored": gateScript.replace("need=$(( 10#$MIN_PROGRESS > 0 ? 10#$MIN_PROGRESS : 1 ))", "need=1"),
  }
  for (const [name, mutated] of Object.entries(capMutants)) {
    const caught = mutated !== gateScript && capCases.some((c) => !verdict(mutated, c).ok)
    check(`mutant: ${name} is noticed`, caught, mutated === gateScript ? "pattern not found" : "")
  }
}

// the memory counts: passed on when the gate stops, checked before use, and said in the issue
{
  const stalled = runGate(gateScript, { round: 3, prev: "100", built: "100", min: 1, toobig: "2", blocked: "40" })
  check("a stop passes the memory counts on to the issue job", stalled.code !== 0 && /^toobig=2$/m.test(stalled.output) && /^blocked=40$/m.test(stalled.output), stalled.output + stalled.text)
  const quiet = runGate(gateScript, { round: 3, prev: "100", built: "100", min: 1 })
  check("a stop with no memory counts (an older prime job) passes them on empty, and still stops", quiet.code !== 0 && /^toobig=$/m.test(quiet.output) && /stalled=true/.test(quiet.output), quiet.output + quiet.text)
  for (const key of ["toobig", "blocked"]) {
    const g = runGate(gateScript, { round: 3, prev: "100", built: "101", min: 1, [key]: "x; rm -rf /" })
    check(`a ${key} count that is not a number stops the gate before it dispatches anything`, g.code !== 0 && !g.calls.includes("workflow run") && /not a number/.test(g.text), g.text)
  }
  const reportScript = stepRun(report, "Open or update the issue")
  const rdir = mkdtempSync(join(tmpdir(), "report-"))
  writeFileSync(join(rdir, "gh"), `#!/bin/sh\necho "gh $*" >> "${join(rdir, "calls")}"\nif [ "$1 $2" = "issue list" ]; then echo '[]'; fi\nexit 0\n`)
  writeFileSync(join(rdir, "jq"), "#!/bin/sh\ncat > /dev/null\n")
  chmodSync(join(rdir, "gh"), 0o755); chmodSync(join(rdir, "jq"), 0o755)
  writeFileSync(join(rdir, "report.sh"), reportScript)
  const runReport = (over) => {
    const r = spawnSync("bash", ["--noprofile", "--norc", "-eo", "pipefail", join(rdir, "report.sh")], {
      cwd: rdir, encoding: "utf8",
      env: { PATH: `${rdir}:${process.env.PATH}`, GH_TOKEN: "x", KEY: "k", BUILD_ROUND: "3", BUILT: "100", PREV_BUILT: "100", MODULES: "200", ADDED: "0", MIN_PROGRESS: "1", RUN_ID: "5", GITHUB_SERVER_URL: "https://github.com", GITHUB_REPOSITORY: "o/r", TOOBIG: "", BLOCKED: "", ...over },
    })
    return { code: r.status, text: r.stdout + r.stderr, body: existsSync(join(rdir, "body.md")) ? readFileSync(join(rdir, "body.md"), "utf8") : "" }
  }
  let rep = runReport({ TOOBIG: "2", BLOCKED: "40" })
  check("the issue says how many modules were killed for memory and how many wait behind them", rep.code === 0 && /\*\*2 module\(s\) were killed for memory even when built alone, and 40 more are left out/.test(rep.body), rep.text + rep.body)
  rep = runReport({ TOOBIG: "0", BLOCKED: "0" })
  check("with no module killed for memory the issue says the build is not stuck on memory", rep.code === 0 && /No module was killed for memory/.test(rep.body) && !/were killed for memory even/.test(rep.body), rep.text + rep.body)
  rep = runReport({})
  check("with no count at all (an older prime job) the issue says nothing about memory", rep.code === 0 && !/memory/.test(rep.body), rep.text + rep.body)
  rep = runReport({ TOOBIG: "1; echo hi" })
  check("a count that is not a number stops the issue job", rep.code !== 0 && /not a number/.test(rep.text), rep.text)
}
for (const [name, from, to] of [
  ["stopping at exactly min instead of below it", '-lt "$MIN_PROGRESS"', '-le "$MIN_PROGRESS"'],
  ["stopping on a fall although min_progress is 0", '[ "$MIN_PROGRESS" -gt 0 ] && [ "$added" -lt "$MIN_PROGRESS" ]', '[ "$added" -lt "$MIN_PROGRESS" ]'],
  ["stopping the first round too", '[ "$BUILD_ROUND" -gt 1 ] && [ -n "$PREV_BUILT" ]', '[ "$BUILD_ROUND" -ge 1 ] && [ -n "$PREV_BUILT" ]'],
  ["subtracting the wrong way round", "$((10#$BUILT - 10#$PREV_BUILT))", "$((10#$PREV_BUILT - 10#$BUILT))"],
  ["dispatching after the error", "    exit 1\n  fi\nelif", "    :\n  fi\nelif"],
  ["passing the old count on to the next round", '-f prev_built="$BUILT"', '-f prev_built="$PREV_BUILT"'],
  ["not forwarding min_progress", ' -f min_progress="$MIN_PROGRESS"', ""],
  ["stopping when the count of the round before is missing", '[ "$BUILD_ROUND" -gt 1 ] && [ -n "$PREV_BUILT" ] && [ -n "$BUILT" ]', '[ "$BUILD_ROUND" -gt 1 ] && [ -n "$BUILT" ]'],
]) {
  const at = gateScript.lastIndexOf(from)   // the ordinary dispatch comes after the escalation one, which has some of the same words
  const mutated = at < 0 ? gateScript : gateScript.slice(0, at) + to + gateScript.slice(at + from.length)
  check(`mutant: ${name} is noticed`, mutated !== gateScript && wrong(mutated, cases, true).length > 0, mutated === gateScript ? "pattern not found" : "")
}

// ---- modules too big for a runner: the memory knobs, the swap, the escalation round, the published archive as a starting point ----
// (flt-anthropic, 5 Nov 2026: 86 modules, the final theorem and everything leading to it, were left out for 14 GB and the build was called complete)
{
  const text = readFileSync(join(wf, "setup-sharded.yml"), "utf8")
  const inputBlock = (name) => (text.match(new RegExp(`\\n      ${name}:\\n((?:        .*\\n)+)`)) || [])[1] || ""
  check("retry_mb, swap_gb, solo_minutes and from_release are inputs, with defaults that change nothing (14336, 0, 90, false)", /default: "14336"/.test(inputBlock("retry_mb")) && /default: "0"/.test(inputBlock("swap_gb")) && /default: "90"/.test(inputBlock("solo_minutes")) && /default: "false"/.test(inputBlock("from_release")), "")
  const memEnv = "EMISSARY_RETRY_FOOTPRINT_MB: ${{ inputs.retry_mb }}"
  check("the bigger limit and the solo time are set in the prime job and in no other (a shard has no swap: a limit above its RAM would let a runaway take the runner)", sharded.prime.includes(memEnv) && !sharded.shard.includes("EMISSARY_RETRY_FOOTPRINT_MB") && !sharded.finish.includes("EMISSARY_RETRY_FOOTPRINT_MB") && !text.split("\njobs:\n")[0].includes("EMISSARY_RETRY_FOOTPRINT_MB"), "")
  check("the guard counts swap only in the prime job, and only when the job added swap", /EMISSARY_COUNT_SWAP: \$\{\{ inputs\.swap_gb != '0' && '1' \|\| '0' \}\}/.test(sharded.prime) && !/EMISSARY_COUNT_SWAP/.test(sharded.shard + sharded.finish), "")
  const buildStep = sharded.prime.slice(sharded.prime.indexOf("- name: Build what fits"), sharded.prime.indexOf("- name: This round in numbers"))
  check("the swap is added by setup-source.mjs itself (EMISSARY_ADD_SWAP_GB from swap_gb, prime job only), synchronously after the unpack and before the build, not by a background process in the workflow", /EMISSARY_ADD_SWAP_GB: \$\{\{ inputs\.swap_gb \}\}/.test(sharded.prime.split("steps:")[0]) && !/EMISSARY_ADD_SWAP_GB/.test(sharded.shard + sharded.finish) && !/sh scripts\/add-swap\.sh/.test(sharded.prime) && !/- name: Swap \(swap_gb\)/.test(sharded.prime) && (() => { const src = readFileSync(join(dirname(fileURLToPath(import.meta.url)), "setup-source.mjs"), "utf8"); const at = src.indexOf('if (PHASE === "build") {'); const blk = src.slice(at, src.indexOf("return log(`done ${key} (build phase)", at)); return blk.indexOf("await restoreBuild") >= 0 && blk.indexOf("await restoreBuild") < blk.indexOf("await addSwap()") && blk.indexOf("await addSwap()") < blk.indexOf("await build(modules)") })(), buildStep)
  check("the prime job deletes the unpacked earlier build's archive (EMISSARY_DROP_RESTORED=1) and removes the swap file before the build is packed", /EMISSARY_DROP_RESTORED: "1"/.test(sharded.prime.split("steps:")[0]) && !/EMISSARY_DROP_RESTORED/.test(sharded.shard + sharded.finish) && sharded.prime.indexOf("swapoff /swapfile") > sharded.prime.indexOf("- name: Pack the build") && sharded.prime.indexOf("swapoff /swapfile") < sharded.prime.indexOf("tar --zstd --exclude"), "")
  const knobStep = sharded.prime.slice(sharded.prime.indexOf("- name: The memory knobs are numbers"), sharded.prime.indexOf("- name: Free disk"))
  check("the prime job's first step checks retry_mb, swap_gb and solo_minutes are numbers (a malformed retry_mb silently switched the escalation off), through env", sharded.prime.indexOf("- name: The memory knobs are numbers") > 0 && sharded.prime.indexOf("- name: The memory knobs are numbers") < sharded.prime.indexOf("- name: Free disk") && /RETRY_MB" =~ \^\[1-9\]\[0-9\]\{0,8\}\$/.test(knobStep) && /SWAP_GB" =~ \^\(0\|\[1-9\]\[0-9\]\{0,2\}\)\$/.test(knobStep) && /SOLO_MINUTES" -le 340/.test(knobStep) && !/\$\{\{/.test(knobStep.slice(knobStep.indexOf("run: |"))), knobStep)
  {
    const kdir = mkdtempSync(join(tmpdir(), "knobs-")), ks = stepRun(sharded.prime, "The memory knobs are numbers")
    writeFileSync(join(kdir, "k.sh"), ks)
    const runKnobs = (script, e) => spawnSync("bash", ["--noprofile", "--norc", "-e", script], { encoding: "utf8", env: { PATH: process.env.PATH, RETRY_MB: "14336", SWAP_GB: "0", SOLO_MINUTES: "90", ONLY_MODULES: "", FROM_RELEASE: "false", ...e } }).status
    let okc = 0, wrongK = []
    for (const [e, want] of [[{}, 0], [{ RETRY_MB: "57344", SWAP_GB: "48", SOLO_MINUTES: "300" }, 0], [{ SOLO_MINUTES: "340" }, 0], [{ RETRY_MB: "" }, 1], [{ RETRY_MB: "0" }, 1], [{ RETRY_MB: "14336 " }, 1], [{ RETRY_MB: "1e5" }, 1], [{ RETRY_MB: "14336; id" }, 1], [{ RETRY_MB: "-5" }, 1], [{ RETRY_MB: "0123" }, 1], [{ SWAP_GB: "4G" }, 1], [{ SWAP_GB: "" }, 1], [{ SWAP_GB: "1000" }, 1], [{ ONLY_MODULES: "Theorems.Thm_A,Definitions.Def_B", FROM_RELEASE: "true" }, 0], [{ ONLY_MODULES: "«a.b».C,D,Lib.α,Ünï.β", FROM_RELEASE: "true" }, 0], [{ ONLY_MODULES: "Theorems.Thm_A" }, 1], [{ FROM_RELEASE: "yes" }, 1], [{ FROM_RELEASE: "" }, 1], [{ FROM_RELEASE: "TRUE" }, 1], [{ FROM_RELEASE: "true" }, 0], [{ FROM_RELEASE: "true; id" }, 1], [{ ONLY_MODULES: "A;id", FROM_RELEASE: "true" }, 1], [{ ONLY_MODULES: "A B", FROM_RELEASE: "true" }, 1], [{ ONLY_MODULES: "A$(id)", FROM_RELEASE: "true" }, 1], [{ ONLY_MODULES: "A`id`", FROM_RELEASE: "true" }, 1], [{ ONLY_MODULES: "A|B", FROM_RELEASE: "true" }, 1], [{ ONLY_MODULES: "x".repeat(60001), FROM_RELEASE: "true" }, 1], [{ SOLO_MINUTES: "341" }, 1], [{ SOLO_MINUTES: "0" }, 1], [{ SOLO_MINUTES: "x" }, 1]]) {
      okc++
      if ((runKnobs(join(kdir, "k.sh"), e) === 0 ? 0 : 1) !== want) wrongK.push(e)
    }
    check(`the knob step accepts good values and refuses malformed ones, on ${okc} inputs`, wrongK.length === 0, wrongK)
    writeFileSync(join(kdir, "m.sh"), ks.replace("RETRY_MB\" =~ ^[1-9][0-9]{0,8}$", "RETRY_MB\" =~ ^[0-9]*$"))
    check("mutant: a retry_mb check that lets an empty value through is noticed", runKnobs(join(kdir, "m.sh"), { RETRY_MB: "" }) === 0, "")
  }
  check("the shards (not the finish job) get EMISSARY_ONLY_MODULES, so that they export only the named modules and unpack only their closure; setup-source.mjs applies it in the shard phase", /EMISSARY_ONLY_MODULES: \$\{\{ inputs\.only_modules \}\}/.test(sharded.shard.split("steps:")[0]) && !/EMISSARY_ONLY_MODULES/.test(sharded.finish) && /PHASE === "build" \|\| PHASE === "build-status" \|\| PHASE === "shard" \? onlyModules\(\)/.test(readFileSync(join(dirname(fileURLToPath(import.meta.url)), "setup-source.mjs"), "utf8")), "")
  check("the prime job hands the build-gate an escalate word, and the shards and the finish job wait for it to be false", /escalate: \$\{\{ steps\.status\.outputs\.escalate \}\}/.test(sharded.prime) && /needs\.prime\.outputs\.complete == 'true' && needs\.prime\.outputs\.escalate != 'true'/.test(sharded.shard.split("runs-on")[0]) && /needs\.prime\.outputs\.complete == 'true' && needs\.prime\.outputs\.escalate != 'true'/.test(sharded.finish.split("runs-on")[0]), "")
  check("the build-gate also runs when the build is complete but the prime job says escalate", /\(needs\.prime\.outputs\.complete != 'true' \|\| needs\.prime\.outputs\.escalate == 'true'\)/.test(gate.split("runs-on")[0]), gate.split("runs-on")[0])
  check("ESCALATE_MB in the workflow is the limit setup-plan.mjs escalation uses", new RegExp(`ESCALATE_MB: "${ESCALATE_RETRY_MB}"`).test(sharded.prime) && new RegExp(`retry_mb="${ESCALATE_RETRY_MB}" -f swap_gb="${ESCALATE_SWAP_GB}" -f solo_minutes="${ESCALATE_SOLO_MINUTES}"`).test(gate), `${ESCALATE_RETRY_MB} ${ESCALATE_SWAP_GB} ${ESCALATE_SOLO_MINUTES}`)
  for (const [name, block] of [["build-gate (ordinary round)", gate], ["finish (next export round)", sharded.finish]]) {
    check(`${name} carries retry_mb, swap_gb, solo_minutes, from_release and only_modules on`, /-f retry_mb="\$RETRY_MB" -f swap_gb="\$SWAP_GB" -f solo_minutes="\$SOLO_MINUTES" -f from_release="\$FROM_RELEASE" -f only_modules="\$ONLY_MODULES"/.test(block), "")
  }
  for (const job of ["shard", "finish"]) {
    const b = sharded[job]
    const at = b.indexOf("- name: The published export archive (from_release)")
    const step = b.slice(at, b.indexOf("- name:", at + 10))
    check(`${job}: from_release downloads the library's release archive (joined when published in parts) before anything is unpacked, only when asked`, at > 0 && /if: inputs\.from_release == 'true'/.test(step) && /gh release download "exports-\$KEY" -R "\$GITHUB_REPOSITORY" -p "\$asset\*"/.test(step) && /cat release-dl\/"\$asset"\.part-\* > release\.tar\.zst/.test(step) && at < b.indexOf("unpack release.tar.zst"), step)
    check(`${job}: the release archive is unpacked FIRST, so that exports-partial and the shards' outputs lay over it`, b.indexOf("unpack release.tar.zst") > 0 && b.indexOf("unpack release.tar.zst") < b.indexOf("unpack exports-partial.tar.zst"), "")
  }
  check("the shard job still holds no write permission with from_release (the release is read, not written)", !writes(permissionsOf(sharded.shard)), permissionsOf(sharded.shard))

  // the status step against the rule: run for real with a fake node that prints what --phase build-status prints
  const statusScript = stepRun(sharded.prime, "Is the build complete?")
  const sdir = mkdtempSync(join(tmpdir(), "status-"))
  writeFileSync(join(sdir, "node"), '#!/bin/sh\nprintf "%s\\n" "$FAKE_ANSWER"\nexit 0\n')
  chmodSync(join(sdir, "node"), 0o755)
  writeFileSync(join(sdir, "status.sh"), statusScript)
  const runStatus = (answer, retry) => {
    const out = join(sdir, "output"), summary = join(sdir, "summary")
    writeFileSync(out, ""); writeFileSync(summary, "")
    const r = spawnSync("bash", ["--noprofile", "--norc", "-e", join(sdir, "status.sh")], { cwd: sdir, encoding: "utf8", env: { PATH: `${sdir}:${process.env.PATH}`, GITHUB_OUTPUT: out, GITHUB_STEP_SUMMARY: summary, KEY: "k", RETRY_MB: String(retry), ESCALATE_MB: String(ESCALATE_RETRY_MB), FAKE_ANSWER: answer } })
    const o = readFileSync(out, "utf8")
    return { code: r.status, text: r.stdout + r.stderr, escalate: (o.match(/^escalate=(.*)$/gm) || []).map((l) => l.slice(9)), complete: (o.match(/^complete=(.*)$/m) || [])[1], out: o }
  }
  const answerOf = (complete, toobig, extra = "") => `[19:52:20] build status: 30576/30662 modules have an .olean; ${toobig} too big\nbuilt=30576\nmodules=30662\ntoobig=${toobig}\nblocked=82\ncomplete=${complete}\n${extra}`
  let n = 0, wrongStatus = []
  for (const complete of [true, false]) for (const toobig of [0, 1, 4, 86, 123456]) for (const retry of [0, 14336, 20000, ESCALATE_RETRY_MB - 1, ESCALATE_RETRY_MB, ESCALATE_RETRY_MB + 1]) {
    n++
    const r = runStatus(answerOf(complete, toobig), retry)
    const want = escalation({ complete, toobig, retryMb: retry }).escalate
    if (r.code !== 0 || r.escalate.length !== 1 || r.escalate[0] !== String(want) || r.complete !== String(complete)) wrongStatus.push({ complete, toobig, retry, got: r.escalate, code: r.code, text: r.text.slice(0, 200) })
  }
  check(`the status step says escalate exactly when the rule (setup-plan.mjs escalation) does, once, on ${n} states`, wrongStatus.length === 0, wrongStatus.slice(0, 3))
  for (const [name, answer, retry, want] of [
    ["a toobig line that is not a count is ignored (no escalation)", answerOf(true, 0, "toobig=4; rm -rf /\ntoobig=-3\n"), 14336, "false"],
    ["a RETRY_MB that is not a number never escalates", answerOf(true, 4), "14336; id", "false"],
    ["no toobig line at all (an older setup-source) never escalates", "built=5\nmodules=5\ncomplete=true\n", 14336, "false"],
    ["the last toobig line counts", answerOf(true, 0, "toobig=4\n"), 14336, "true"],
  ]) {
    n++
    const r = runStatus(answer, retry)
    check(name, r.code === 0 && r.escalate.length === 1 && r.escalate[0] === want, r.out + r.text)
  }
  const warn = runStatus(answerOf(true, 4), ESCALATE_RETRY_MB)
  check("a build that ends with modules too big even for swap says so with a ::warning:: (no silence), naming the counts", /::warning::4 module\(s\) did not fit in 57344 MB of RAM and swap and are left out, with 82 modules/.test(warn.text), warn.text)
  check("no warning when nothing is too big, or while the escalation is still to come", !/::warning::/.test(runStatus(answerOf(true, 0), ESCALATE_RETRY_MB).text) && !/::warning::/.test(runStatus(answerOf(true, 4), 14336).text), "")

  // the gate against the rule: the escalation round is dispatched once, with the top settings, never judged for progress, whatever the numbers
  let g = 0, wrongGate = []
  const escCases = []
  for (const round of [1, 2, 3, 6]) for (const [prev, built] of [["", "30576"], ["30576", "30576"], ["30000", "30576"], ["30576", "100"]]) for (const min of [0, 1, 5]) for (const retry of ["14336", "20000"]) for (const fromRelease of ["false", "true"]) escCases.push({ round, prev, built, min, retry, fromRelease, escalate: "true", toobig: "4", blocked: "82", only: fromRelease === "true" && (round + min) % 2 ? "Theorems.Thm_A,Definitions.Def_B,Lib.α" : "" })
  const escOk = (c, r) => {
    const calls = r.calls.split("\n").filter((l) => l.includes("workflow run"))
    return r.code === 0 && calls.length === 1 && calls[0].includes('retry_mb=57344') && calls[0].includes(`swap_gb=${ESCALATE_SWAP_GB}`) && calls[0].includes(`solo_minutes=${ESCALATE_SOLO_MINUTES}`) && calls[0].includes("build_run=77") && calls[0].includes(`build_round=${c.round + 1}`) && calls[0].includes(`from_release=${c.fromRelease}`) && calls[0].split(/\s+/).includes(`only_modules=${c.only ?? ""}`) && calls[0].includes(`prev_built=${c.built}`) && /dispatched build round/.test(r.text) && !/::error::/.test(r.text) && !/stalled/.test(r.output)
  }
  const wrongEsc = (script, first = false) => {
    const bad = []
    for (const c of escCases) { g++; const r = runGate(script, c); if (!escOk(c, r)) { bad.push({ c, code: r.code, calls: r.calls.slice(0, 220), text: r.text.slice(0, 200) }); if (first) break } }
    return bad
  }
  wrongGate = wrongEsc(gateScript)
  check(`the gate dispatches the escalation round exactly once, with swap and the top limit, whatever the progress numbers, on ${escCases.length} states`, wrongGate.length === 0, wrongGate.slice(0, 2))
  // an ordinary round (no escalate word) still carries the knobs it was given, unchanged
  let ordinary = 0, wrongOrd = []
  for (const retry of ["14336", "57344"]) for (const swap of ["0", "48"]) for (const solo of ["90", "300"]) for (const fromRelease of ["false", "true"]) for (const round of [2, 3]) {
    ordinary++
    const c = { round, prev: "100", built: "200", min: 1, retry, swap, solo, fromRelease, escalate: "false", only: round === 3 && fromRelease === "true" ? "Theorems.Thm_A,Definitions.Def_B,Lib.α" : "" }
    const r = runGate(gateScript, c)
    const call = r.calls.split("\n").find((l) => l.includes("workflow run")) || ""
    if (!(r.code === 0 && call.includes(`retry_mb=${retry}`) && call.includes(`swap_gb=${swap}`) && call.includes(`solo_minutes=${solo}`) && call.includes(`from_release=${fromRelease}`) && call.split(/\s+/).includes(`only_modules=${c.only}`) && call.includes(`build_round=${round + 1}`))) wrongOrd.push({ c, call: call.slice(0, 200) })
  }
  check(`an ordinary round carries retry_mb, swap_gb, solo_minutes and from_release on unchanged, on ${ordinary} states`, wrongOrd.length === 0, wrongOrd.slice(0, 2))
  for (const [name, c] of [["a retry_mb that is not a number", { round: 2, prev: "1", built: "2", min: 1, retry: "14336;id" }], ["a swap_gb that is not a number", { round: 2, prev: "1", built: "2", min: 1, swap: "4G" }], ["a solo_minutes that is not a number", { round: 2, prev: "1", built: "2", min: 1, solo: "x" }], ["a from_release that is neither true nor false", { round: 2, prev: "1", built: "2", min: 1, fromRelease: "yes" }], ["an only_modules with a shell word in it", { round: 2, prev: "1", built: "2", min: 1, fromRelease: "true", only: "Theorems.Thm_A; rm -rf /" }], ["an only_modules with a space", { round: 2, prev: "1", built: "2", min: 1, fromRelease: "true", only: "A B" }], ["an only_modules without from_release (the finish job would publish a library of only those modules)", { round: 2, prev: "1", built: "2", min: 1, fromRelease: "false", only: "Theorems.Thm_A" }]]) {
    const r = runGate(gateScript, c)
    check(`the gate refuses ${name} before it dispatches anything`, r.code !== 0 && !r.calls.includes("workflow run"), r.text)
  }
  // the old stall rule still applies to an ordinary round when ESCALATE is anything but "true"
  for (const e of ["", "false", "TRUE", "1", "true; id"]) {
    const r = runGate(gateScript, { round: 3, prev: "100", built: "100", min: 1, escalate: e })
    check(`ESCALATE=${JSON.stringify(e)} is not an escalation: a round that added nothing still stops`, r.code !== 0 && !r.calls.includes("workflow run") && /stalled=true/.test(r.output), r.text)
  }
  const escMutants = [
    ["the escalation round is followed by an ordinary dispatch too (no exit after it)", '  exit 0\nfi\n# A build too slow for rounds', "  :\nfi\n# A build too slow for rounds"],
    ["the escalation round keeps the old limit", '-f retry_mb="57344"', '-f retry_mb="$RETRY_MB"'],
    ["the escalation round has no swap", `-f swap_gb="${ESCALATE_SWAP_GB}"`, '-f swap_gb="$SWAP_GB"'],
    ["the escalation round is judged for progress first (the escalation moved below the stall check)", 'if [ "$ESCALATE" = "true" ]; then', 'if [ "$ESCALATE" = "true" ] && [ "$BUILT" != "$PREV_BUILT" ]; then'],
    ["the escalation round forgets which build it continues", '-f build_run="$GITHUB_RUN_ID" -f build_round="$((BUILD_ROUND + 1))" -f max_build_rounds="$MAX_BUILD_ROUNDS" \\\n    -f tengoku_ref', '-f build_round="$((BUILD_ROUND + 1))" -f max_build_rounds="$MAX_BUILD_ROUNDS" \\\n    -f tengoku_ref'],
    ["the escalation round forgets from_release", ' -f from_release="$FROM_RELEASE" -f only_modules="$ONLY_MODULES"\n  echo "::notice::${TOOBIG', ' -f only_modules="$ONLY_MODULES"\n  echo "::notice::${TOOBIG'],
    ["the escalation round forgets only_modules", ' -f only_modules="$ONLY_MODULES"\n  echo "::notice::${TOOBIG', '\n  echo "::notice::${TOOBIG'],
  ]
  for (const [name, from, to] of escMutants) {
    const mutated = gateScript.replace(from, to)
    check(`mutant: ${name} is noticed`, mutated !== gateScript && wrongEsc(mutated, true).length > 0, mutated === gateScript ? "pattern not found" : "")
  }
  const ordMutants = [
    ["the ordinary dispatch drops retry_mb", ' -f retry_mb="$RETRY_MB" -f swap_gb="$SWAP_GB" -f solo_minutes="$SOLO_MINUTES" -f from_release="$FROM_RELEASE" -f only_modules', ' -f swap_gb="$SWAP_GB" -f solo_minutes="$SOLO_MINUTES" -f from_release="$FROM_RELEASE" -f only_modules'],
    ["the ordinary dispatch drops from_release", ' -f solo_minutes="$SOLO_MINUTES" -f from_release="$FROM_RELEASE" -f only_modules="$ONLY_MODULES"\necho "::notice::the build is not complete', ' -f solo_minutes="$SOLO_MINUTES" -f only_modules="$ONLY_MODULES"\necho "::notice::the build is not complete'],
    ["the ordinary dispatch drops only_modules", ' -f only_modules="$ONLY_MODULES"\necho "::notice::the build is not complete', '\necho "::notice::the build is not complete'],
  ]
  for (const [name, from, to] of ordMutants) {
    const mutated = gateScript.replace(from, to)
    let caughtOrd = false
    if (mutated !== gateScript) for (const retry of ["57344"]) { const r = runGate(mutated, { round: 2, prev: "1", built: "2", min: 1, retry, escalate: "false", fromRelease: "true", only: "Theorems.Thm_A" }); const call = r.calls.split("\n").find((l) => l.includes("workflow run")) || ""; if (!(call.includes("retry_mb=57344") && call.includes("from_release=true") && call.includes("only_modules=Theorems.Thm_A"))) caughtOrd = true }
    check(`mutant: ${name} is noticed`, caughtOrd, mutated === gateScript ? "pattern not found" : "")
  }
  // mutants of the status step
  for (const [name, from, to] of [
    ["the status step escalates without checking that the build is complete", '[ "${word#complete=}" = "true" ] && ', ""],
    ["the status step escalates at the top limit too", '[ "$RETRY_MB" -lt "$ESCALATE_MB" ]; then\n  echo "escalate=true"', '[ "$RETRY_MB" -le "$ESCALATE_MB" ]; then\n  echo "escalate=true"'],
    ["the status step escalates with nothing too big", '[ "${toobig:-0}" -gt 0 ] && [ "$RETRY_MB" -lt', '[ "${toobig:-0}" -ge 0 ] && [ "$RETRY_MB" -lt'],
  ]) {
    const mutated = statusScript.replace(from, to)
    writeFileSync(join(sdir, "status.sh"), mutated)
    let caughtStatus = false
    for (const [complete, toobig, retry] of [[false, 4, 14336], [true, 4, ESCALATE_RETRY_MB], [true, 0, 14336]]) { const r = runStatus(answerOf(complete, toobig), retry); if (r.escalate[0] !== String(escalation({ complete, toobig, retryMb: retry }).escalate)) caughtStatus = true }
    check(`mutant: ${name} is noticed`, mutated !== statusScript && caughtStatus, mutated === statusScript ? "pattern not found" : "")
    writeFileSync(join(sdir, "status.sh"), statusScript)
  }
  console.log(`(escalation checks ran ${n} status runs and ${g + ordinary} gate runs)`)
}

const auto = jobsOf("setup-auto.yml")
const planBlock = auto.plan || ""
check("setup-auto has one job, which dispatches and only reads contents", /actions:\s*write/.test(permissionsOf(planBlock) || "") && /contents:\s*read/.test(permissionsOf(planBlock) || "") && !/contents:\s*write/.test(permissionsOf(planBlock) || ""), permissionsOf(planBlock))
check("setup-auto reads the records from tengoku_ref and hands it to both routes", /origin\/\$TENGOKU_REF/.test(planBlock) && (planBlock.match(/-f tengoku_ref="\$TENGOKU_REF"/g) || []).length === 2, (planBlock.match(/-f tengoku_ref/g) || []).length)
check("setup-auto never builds or runs the library", !/\blake\b|elan|setup-source\.mjs/.test(planBlock.replace(/#.*$/gm, "")), "")
check("setup-auto checks the key before using it", /\^\[a-z0-9\]\[a-z0-9-\]\*\$/.test(planBlock), "")
const runBodies = [...planBlock.matchAll(/run: \|\n((?: {10}.*\n?|\n)+)/g)].map((m) => m[1]).join("\n")
check("no ${{ }} expression sits inside a shell script of setup-auto", !/\$\{\{/.test(runBodies), runBodies.match(/.*\$\{\{.*/)?.[0])

// a round that was cancelled never merged its shard outputs: the next round (shards and finish alike) falls back to them instead of failing on a missing exports-partial
// (flt-anthropic, 4 Nov 2026: round 5 failed in every shard after round 4 was cancelled; it took a hand-dispatched bank run to get the finished shards' exports back)
for (const job of ["shard", "finish"]) {
  const b = sharded[job]
  const prev = b.slice(b.indexOf("- name: The previous round's outputs"))
  check(`${job}: the previous round's exports-partial is read with continue-on-error and an id`, /- name: The previous round's outputs\n\s+id: partial\n\s+if: inputs\.resume_run != ''\n\s+continue-on-error: true/.test(b), "")
  check(`${job}: when exports-partial is missing the shard outputs (out-*) of that round are read`, /steps\.partial\.outcome == 'failure'/.test(prev) && /pattern: "out-\*", path: prev-out, merge-multiple: true, run-id: "\$\{\{ inputs\.resume_run \}\}"/.test(prev), "")
  check(`${job}: those outputs are unpacked with the rest`, /if \[ -d prev-out \]; then for f in prev-out\/\*\.tar\.zst; do \[ -f "\$f" \] && unpack "\$f"; done; rm -rf prev-out; fi/.test(b), "")
}
// the round a bank run dispatches takes the build the bank run was given: a bank run has no prime job, so its own run id carries no build
const dispatch = sharded.finish.slice(sharded.finish.indexOf("gh workflow run setup-sharded.yml") - 1200)
check("the next round gets build_run from a bank run's input (and the default from an ordinary round), in the step that dispatches", /BUILD_RUN: \$\{\{ inputs\.bank_run != '' && inputs\.build_run \|\| '' \}\}[\s\S]*gh workflow run setup-sharded\.yml[^\n]*[\s\S]*-f build_run="\$BUILD_RUN"/.test(dispatch), "")
for (const job of ["shard", "finish"]) {
  const b = sharded[job]
  const step = b.slice(b.indexOf("- name: The previous round's shard outputs"), b.indexOf("- name: The previous round's shard outputs") + 1400)
  check(`${job}: a cancelled run without out-* does not end the round (the fallback download goes on after a failure)`, /continue-on-error: true\n\s+uses: actions\/download-artifact/.test(step), "")
}

// the fallback is not silent: a round that went on from deltas says so (a transient failure of the exports-partial read looks like a missing artifact)
for (const job of ["shard", "finish"]) {
  const b = sharded[job]
  const say = b.slice(b.indexOf("- name: Say that the round resumed from deltas"), b.indexOf("- name: Say that the round resumed from deltas") + 1500)
  check(`${job}: a round that resumed from the per-shard outputs says so, when exports-partial failed, with values through env`, /if: inputs\.resume_run != '' && steps\.partial\.outcome == 'failure'\n\s+env: \{ RESUME_RUN: "\$\{\{ inputs\.resume_run \}\}", OUTS: "\$\{\{ steps\.outs\.outcome \}\}" \}/.test(say), "")
  check(`${job}: the warning names the run and the outcome of the out-* download, in a block scalar (a colon-space in a one-line value made the workflow invalid YAML)`, /\n\s+run: \|\n\s+echo "::warning::exports-partial of run \$RESUME_RUN [^\n]*\(download outcome: \$OUTS\)/.test(say), "")
}

// ---- a build too slow for rounds is split over runners (slicedSwitch) ----
// finite-simple-groups-lean, 14 Nov 2026: round 1 built 95 of 3,964 modules (the round before the storm rule, 13): 41 more rounds, about 200 hours. The shell of the build-gate against the rule, run for
// real with a fake `gh`, on the real rounds, on a grid of every kind of count and on random rounds; and mutants of the shell that must each be noticed.
{
  const sw = (c) => slicedSwitch({ round: c.round, prev: c.prev === "" ? null : Number(c.prev), built: c.built === "" ? null : Number(c.built), modules: c.modules === "" ? null : Number(c.modules), maxBuildRounds: c.maxRounds ?? 6, min: c.min ?? 1, fromRelease: c.fromRelease === "true", onlyModules: (c.only ?? "") !== "" })
  const real = [
    // MEASURED, 14 Nov 2026: 64 slices of finite-simple-groups-lean (62 on average, 65 in shard 0) ran out of the 300 minutes of a shard (each builds the import closure of its slice: 111 to 205 modules, ~1,500 jobs) and exported nothing
    { name: "finite-simple-groups-lean round 1 (95 of 3,964, 14 Nov 2026): 62 a slice ran out of a shard's time, rounds go on", c: { round: 1, prev: "", built: "95", modules: "3964", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "finite-simple-groups-lean round 1 before the storm rule (13 of 3,964): rounds go on", c: { round: 1, prev: "", built: "13", modules: "3964", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "finite-simple-groups-lean, 3,000 of 3,964 built at 95 a round: rounds go on", c: { round: 2, prev: "2905", built: "3000", modules: "3964", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "an 800-module library at 95 a round: 62 slices of 13 modules", c: { round: 1, prev: "", built: "95", modules: "800", min: 1, maxRounds: 6 }, want: { switch: true, shards: 62 } },
    { name: "an 800-module library at 90 a round in round 2: the slices still divide all 800", c: { round: 2, prev: "80", built: "90", modules: "800", min: 1, maxRounds: 6 }, want: { switch: true, shards: 62 } },
    { name: "the largest sliced library, 832 modules: 64 slices of 13", c: { round: 1, prev: "", built: "10", modules: "832", min: 1, maxRounds: 6 }, want: { switch: true, shards: 64 } },
    { name: "833 modules: the biggest slice is up to 26, over what a shard holds, rounds go on", c: { round: 1, prev: "", built: "10", modules: "833", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "flt-anthropic's 30,662 modules: 480 a slice, rounds go on", c: { round: 1, prev: "", built: "9", modules: "30662", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "flt-anthropic's 86 modules, round 6 built 85 of 86 (a delta from the archive)", c: { round: 6, prev: "1", built: "85", modules: "86", min: 1, maxRounds: 6, fromRelease: "true", only: "Theorems.Thm_A" }, want: { switch: false } },
    { name: "the 800-module pace with from_release: the archive keeps the rounds", c: { round: 1, prev: "", built: "95", modules: "800", min: 1, maxRounds: 6, fromRelease: "true" }, want: { switch: false } },
    { name: "the same 86 without the archive flags: 85 of 86 is nearly done", c: { round: 6, prev: "1", built: "85", modules: "86", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "a library that needs three rounds at its pace (2,900 a round of 8,000)", c: { round: 2, prev: "3000", built: "5900", modules: "8000", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "a round that added nothing is the stall rule's", c: { round: 3, prev: "100", built: "100", modules: "800", min: 1, maxRounds: 6 }, want: { switch: false } },
    { name: "a round that added 1 with min_progress 5 is the stall rule's", c: { round: 3, prev: "100", built: "101", modules: "800", min: 5, maxRounds: 6 }, want: { switch: false } },
    { name: "a round after the first with no count of the round before is not judged", c: { round: 3, prev: "", built: "95", modules: "800", min: 1, maxRounds: 6 }, want: { switch: false } },
  ]
  for (const { name, c, want } of real) {
    const e = sw(c), g = runGate(gateScript, c)
    const sliced = g.calls.includes("prime_minutes=0")
    check(`slicedSwitch: ${name}: switch=${want.switch}`, e.switch === want.switch && (!want.switch || e.shards === want.shards), e)
    check(`build-gate: ${name}: ${want.switch ? "dispatches the slices" : "does not"}`, sliced === want.switch && (!want.switch || (g.code === 0 && g.calls.includes(`shards=${want.shards} `) && !g.calls.includes("build_run=") && !g.calls.includes("prev_built=") && g.calls.includes("from_release=false") && g.calls.split("\n").filter((l) => l.includes("workflow run")).length === 1)), g.calls.slice(0, 300))
  }
  const grid = []
  for (const round of [1, 2, 6]) for (const maxRounds of [1, 6]) for (const modules of ["", "86", "800", "1500", "3964", "30662"]) for (const built of ["", "0", "13", "95", "3964"]) for (const prev of ["", "0", "90"]) for (const extra of [{}, { fromRelease: "true" }]) for (const min of [0, 5]) grid.push({ round, maxRounds, modules, built, prev, min, ...extra })
  for (let i = 0; i < 700; i++) { const m = 1 + rnd(rnd(3) === 0 ? 40000 : 900), b = rnd(2) === 0 ? rnd(Math.min(m, 300) + 1) : rnd(m + 1), p = rnd(m + 1); grid.push({ round: 1 + rnd(8), maxRounds: 1 + rnd(8), modules: String(m), built: String(b), prev: rnd(5) === 0 ? "" : String(p), min: rnd(6) }) }
  let wrongSw = [], switched = 0, kept = 0
  for (const c of grid) {
    const e = sw(c), g = runGate(gateScript, c)
    const sliced = g.calls.includes("prime_minutes=0")
    if (sliced) switched++; else kept++
    if (sliced !== e.switch || (e.switch && !g.calls.includes(`shards=${e.shards} `))) wrongSw.push({ c, e, calls: g.calls.slice(0, 160) })
  }
  check(`build-gate's shell and slicedSwitch agree on ${grid.length} rounds (${switched} slice, ${kept} do not): counts, empty counts, falls, min_progress, archive flags`, wrongSw.length === 0 && switched > 100 && kept > 100, wrongSw.slice(0, 3))
  const swMutants = [
    ["the switch ignores the archive flags (from_release)", '[ "$FROM_RELEASE" = false ] && [ -n "$BUILT" ] && [ -n "$MODULES" ]', '[ -n "$BUILT" ] && [ -n "$MODULES" ]'],
    ["the switch fires on a round that added nothing (pace 0)", 'if [ "$pace" -gt 0 ] && {', 'if [ "$pace" -ge 0 ] && {'],
    ["the switch ignores min_progress (a stalled round slices)", ' || [ "$MIN_PROGRESS" -eq 0 ] || [ "$pace" -ge "$MIN_PROGRESS" ]; }', ' || true; }'],
    ["the switch judges a round with no count of the round before it on the total built", 'elif [ -n "$PREV_BUILT" ]; then pace=$(( 10#$BUILT - 10#$PREV_BUILT )); fi', 'else pace=$(( 10#$BUILT - 10#${PREV_BUILT:-0} )); fi'],
    ["the switch counts the rounds left without the rounds done (round 1 of a plan of 6)", '[ $(( 10#$BUILD_ROUND + rounds_left )) -gt $(( 10#$MAX_BUILD_ROUNDS )) ]', '[ $(( rounds_left )) -gt $(( 10#$MAX_BUILD_ROUNDS )) ]'],
    ["the switch rounds the rounds left down", 'rounds_left=$(( (remaining + pace - 1) / pace ))', 'rounds_left=$(( remaining / pace ))'],
    ["the shards divide the modules that are left, not all of them", 'slices=$(( (10#$MODULES + 12) / 13 ))', 'slices=$(( (remaining + 12) / 13 ))'],
    ["the slices are not capped at 64", '[ "$slices" -gt 64 ] && slices=64', ':'],
    ["the biggest slice is taken to be the mean (an unbalanced hash bucket can pass 25)", 'print p + t', 'print p'],
    ["a slice may be any size (the 30,662-module library and finite-simple-groups-lean are sliced)", ' && [ "$biggest" -le 25 ]; then', '; then'],
    ["the slices keep the build of the round before (build_run)", '-f from_release=false\n', '-f from_release=false -f build_run="$GITHUB_RUN_ID"\n'],
    ["the slices still have a prime build", '-f prime_minutes=0', '-f prime_minutes="$PRIME_MINUTES"'],
    ["the switch slices a build that needs only one more round", 'if [ "$rounds_left" -ge 2 ] && ', 'if '],
    ["the switch is left out", 'if [ -z "$ONLY_MODULES" ] && [ "$FROM_RELEASE" = false ] && [ -n "$BUILT" ]', 'if false && [ -n "$BUILT" ]'],
  ]
  for (const [name, from, to] of swMutants) {
    const mutated = gateScript.replace(from, to)
    let caught = false
    if (mutated !== gateScript) for (const c of [...real.map((r) => r.c), ...grid.slice(0, 1500)]) { const e = sw(c), g = runGate(mutated, c), b = runGate(gateScript, c); const sliced = g.calls.includes("prime_minutes=0"); if (sliced !== e.switch || (sliced && (g.calls.includes("build_run=") || !g.calls.includes(`shards=${e.shards} `))) || g.code !== b.code || g.calls !== b.calls || g.output !== b.output || g.text !== b.text) { caught = true; break } }
    check(`mutant: ${name} is noticed`, caught, mutated === gateScript ? "pattern not found" : "")
  }
  // a CANCELLED run is stopped: always() let finish run after a cancel, find the shards had exported nothing and dispatch the next round (finite-simple-groups-lean, 14 Nov 2026: cancelling the wasteful
  // sliced run started it again as round 2 with 10 runners; it took a force-cancel). The three jobs that dispatch or report after other jobs use !cancelled(): they still run when a job FAILED.
  const jobIf = (job) => (job.match(/^ {4}if: (.*)$/m) || [])[1] || ""
  for (const name of ["build-gate", "finish", "report-stall"]) {
    const cond = jobIf(sharded[name])
    check(`${name}: runs unless the run was cancelled (!cancelled(), never always()), in an expression so the YAML is valid`, /^\$\{\{ !cancelled\(\) && .* \}\}$/.test(cond) && !/always\(\)/.test(cond), cond)
    const mutated = jobIf(sharded[name].replace(cond, cond.replace("!cancelled()", "always()")))
    check(`mutant: ${name} with always() again is noticed`, /always\(\)/.test(mutated) && !/^\$\{\{ !cancelled\(\)/.test(mutated), mutated)
  }
  check("the build-gate still holds actions: write and nothing else, and has no new variable", /^\{ actions: write \}$/.test(permissionsOf(gate) || "") && envNames.length === 23, envNames.length)
}
process.exit(bad ? 1 : 0)

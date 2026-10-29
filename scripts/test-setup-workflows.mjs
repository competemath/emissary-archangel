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
import { roundProgress } from "./setup-plan.mjs"

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
check("shard starts only on a complete build (or without a prime)", /prime_minutes == '0' \|\| needs\.prime\.outputs\.complete == 'true'/.test(sharded.shard.split("runs-on")[0]), "")
check("finish starts only on a complete build (or a bank_run, or without a prime)", /inputs\.bank_run != '' \|\| inputs\.prime_minutes == '0' \|\| needs\.prime\.outputs\.complete == 'true'/.test(sharded.finish.split("runs-on")[0]), "")
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
check("build-gate stops with an ::error:: holding the numbers, before it dispatches anything", /::error::[^\n]*\$BUILT[^\n]*\$PREV_BUILT[^\n]*\$added/.test(gate) && gate.indexOf("made no progress") > 0 && gate.indexOf("made no progress") < gate.indexOf("gh workflow run"), "")
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
check("the harness gives the build-gate step every variable its env defines, and nothing it does not", ["BUILT", "MODULES", "TOOBIG", "BLOCKED", "PREV_BUILT", "MIN_PROGRESS", "BUILD_ROUND", "MAX_BUILD_ROUNDS", "TENGOKU_REF"].every((n) => envNames.includes(n)) && envNames.length === 17, envNames)
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
      SHARDS: "16", PRIME_MINUTES: "300", EXPAND_CHUNK: "1", ROUND: "1", MAX_ROUNDS: "4", PARALLEL: "6", RESUME_RUN: "", GITHUB_RUN_ID: "77", TENGOKU_REF: "", MAX_BUILD_ROUNDS: "99",
      BUILD_ROUND: String(c.round), PREV_BUILT: c.prev, BUILT: c.built, MODULES: "30662", MIN_PROGRESS: String(c.min), TOOBIG: c.toobig ?? "", BLOCKED: c.blocked ?? "",
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
  ["stopping when the count of the round before is missing", '&& [ -n "$PREV_BUILT" ] && [ -n "$BUILT" ]', "&& [ -n \"$BUILT\" ]"],
]) {
  const mutated = gateScript.replace(from.replaceAll("\n", "\n"), to)
  check(`mutant: ${name} is noticed`, mutated !== gateScript && wrong(mutated, cases, true).length > 0, mutated === gateScript ? "pattern not found" : "")
}

const auto = jobsOf("setup-auto.yml")
const planBlock = auto.plan || ""
check("setup-auto has one job, which dispatches and only reads contents", /actions:\s*write/.test(permissionsOf(planBlock) || "") && /contents:\s*read/.test(permissionsOf(planBlock) || "") && !/contents:\s*write/.test(permissionsOf(planBlock) || ""), permissionsOf(planBlock))
check("setup-auto reads the records from tengoku_ref and hands it to both routes", /origin\/\$TENGOKU_REF/.test(planBlock) && (planBlock.match(/-f tengoku_ref="\$TENGOKU_REF"/g) || []).length === 2, (planBlock.match(/-f tengoku_ref/g) || []).length)
check("setup-auto never builds or runs the library", !/\blake\b|elan|setup-source\.mjs/.test(planBlock.replace(/#.*$/gm, "")), "")
check("setup-auto checks the key before using it", /\^\[a-z0-9\]\[a-z0-9-\]\*\$/.test(planBlock), "")
const runBodies = [...planBlock.matchAll(/run: \|\n((?: {10}.*\n?|\n)+)/g)].map((m) => m[1]).join("\n")
check("no ${{ }} expression sits inside a shell script of setup-auto", !/\$\{\{/.test(runBodies), runBodies.match(/.*\$\{\{.*/)?.[0])
process.exit(bad ? 1 : 0)

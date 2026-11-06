// node scripts/test-memory-rules.mjs — the memory rules that decide whether a module too big for a runner is tried again, on REAL values.
//   1. availableFrom (the guard that kills the biggest process when the runner runs out of memory): scripts/fixtures/real-free-memory.json holds every real "free memory" sample
//      the sampler took on the runners that built flt-anthropic and others (build-metrics.tsv of the setup-sharded rounds, one line a minute). Each is put into a /proc/meminfo text
//      with swap of every size seen on runners (none, the 4 GB of a hosted runner, the 48 GB the escalation round adds) and checked:
//        a. without countSwap the answer is exactly MemAvailable, whatever the swap (the old guard, unchanged);
//        b. with countSwap it is MemAvailable plus SwapFree, never less than without;
//        c. the guard (under 1536 MB left) fires on the same samples as before when swap is not counted, and on none of them with 48 GB of swap counted;
//        d. a text with no MemAvailable (not Linux) is Infinity.
//   2. soloBuildMs (how long a killed module may take alone): the values the workflow inputs can hold, and values that must fall back to the default.
//   3b. buildAttempts / soloMax (how many tries a chunk gets and how many killed modules are built alone): the grid of every retry limit and every setting a person could write.
//   3. escalation (setup-plan.mjs): every combination of the build's state, and the real states flt-anthropic had.
// Then the same checks run on broken versions of each rule, and each must be caught.
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { availableFrom, buildAttempts, closureBudgetMs, closureRetryMs, CLOSURE_RETRY_FACTOR, CLOSURE_RETRY_MAX_MS, CLOSURE_BUDGET_DEFAULT_MS, BUILD_ATTEMPTS_DEFAULT, BUILD_ATTEMPTS_ESCALATED, ESCALATED_RETRY_MB, membersOf, soloBuildMs, SOLO_BUILD_DEFAULT_MS, soloMax, SOLO_MAX_DEFAULT, SOLO_MAX_ESCALATED } from "./memory-rules.mjs"
import { escalation, ESCALATE_RETRY_MB, ESCALATE_SWAP_GB, ESCALATE_SOLO_MINUTES } from "./setup-plan.mjs"

const here = dirname(fileURLToPath(import.meta.url))
const fixture = JSON.parse(readFileSync(join(here, "fixtures", "real-free-memory.json"), "utf8"))
const samples = fixture.free_mb
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name)
}
if (!Array.isArray(samples) || samples.length < 2000) { console.log(`FAIL the real sample file is missing or too small: ${samples?.length}`); process.exit(1) }

// a real /proc/meminfo has these fields in this order; only the three that matter change
const meminfo = (availMb, swapTotalMb, swapFreeMb) =>
  [
    `MemTotal:       ${16 * 1024 * 1024} kB`, `MemFree:        ${Math.round(availMb * 300)} kB`, `MemAvailable:   ${Math.round(availMb * 1024)} kB`, "Buffers:          123456 kB",
    "Cached:          3456789 kB", `SwapCached:            0 kB`, "Active:          2345678 kB", "Inactive:        1234567 kB",
    `SwapTotal:      ${Math.round(swapTotalMb * 1024)} kB`, `SwapFree:       ${Math.round(swapFreeMb * 1024)} kB`, "Dirty:               456 kB", "",
  ].join("\n")
const SWAPS = [[0, 0], [4096, 4096], [4096, 1000], [49152, 49152], [49152, 20000]]
const MIN_AVAILABLE_MB = 1536

function run(rules, print) {
  let cases = 0, violations = 0
  const v = (what, detail) => { violations++; if (print && violations <= 8) console.log("FAIL", what, detail ?? "") }
  for (const mb of samples) {
    for (const [total, free] of SWAPS) {
      const text = meminfo(mb, total, free)
      cases++
      const plain = rules.availableFrom(text, false), counted = rules.availableFrom(text, true)
      if (Math.abs(plain - Math.round(mb * 1024) / 1024) > 1e-6) v("a: without countSwap the answer is not MemAvailable", `${mb} ${total}/${free}: ${plain}`)
      if (Math.abs(counted - (Math.round(mb * 1024) + Math.round(free * 1024)) / 1024) > 1e-6) v("b: with countSwap the answer is not MemAvailable plus SwapFree", `${mb} ${total}/${free}: ${counted}`)
      if (counted < plain) v("b: counting swap made the answer smaller", `${mb}`)
      if ((plain < MIN_AVAILABLE_MB) !== (mb < MIN_AVAILABLE_MB)) v("c: the guard fires differently without swap", `${mb}`)
      if (free >= 20000 && counted < MIN_AVAILABLE_MB) v("c: with 20+ GB of free swap counted the guard still fires", `${mb} ${free}: ${counted}`)
    }
  }
  if (rules.availableFrom("Linux without the field\n", true) !== Infinity) v("d: a text with no MemAvailable is not Infinity")
  if (rules.availableFrom("", false) !== Infinity) v("d: an empty text is not Infinity")
  // soloBuildMs
  const table = [
    ["90", 90 * 60e3], ["300", 300 * 60e3], ["340", 340 * 60e3], ["1", 60e3], ["120.5", Math.round(120.5 * 60e3)], [" 90 ", 90 * 60e3],
    ["", SOLO_BUILD_DEFAULT_MS], ["0", SOLO_BUILD_DEFAULT_MS], ["-5", SOLO_BUILD_DEFAULT_MS], ["341", SOLO_BUILD_DEFAULT_MS], ["99999", SOLO_BUILD_DEFAULT_MS], ["abc", SOLO_BUILD_DEFAULT_MS],
    ["0.0000001", SOLO_BUILD_DEFAULT_MS], ["0.000001", SOLO_BUILD_DEFAULT_MS], ["0.00001", 1], ["0.0000083", SOLO_BUILD_DEFAULT_MS],
    ["300; rm -rf /", SOLO_BUILD_DEFAULT_MS], ["1e3", SOLO_BUILD_DEFAULT_MS], ["NaN", SOLO_BUILD_DEFAULT_MS], ["Infinity", SOLO_BUILD_DEFAULT_MS], ["0x10", SOLO_BUILD_DEFAULT_MS], ["9 0", SOLO_BUILD_DEFAULT_MS],
  ]
  for (const [input, want] of table) {
    cases++
    const got = rules.soloBuildMs({ EMISSARY_SOLO_BUILD_MINUTES: input })
    if (got !== want) v("soloBuildMs", `${JSON.stringify(input)}: ${got} != ${want}`)
  }
  cases++
  if (rules.soloBuildMs({}) !== SOLO_BUILD_DEFAULT_MS) v("soloBuildMs: unset is not the default")
  // every whole number of minutes 1..340 is kept, 341..400 fall back
  for (let m = 1; m <= 400; m++) {
    cases++
    const got = rules.soloBuildMs({ EMISSARY_SOLO_BUILD_MINUTES: String(m) })
    if (got !== (m <= 340 ? m * 60e3 : SOLO_BUILD_DEFAULT_MS)) v("soloBuildMs over the whole range", `${m}: ${got}`)
  }
  // escalation: the full grid, and the rule stated once more in the simplest form
  for (const complete of [true, false]) for (const toobig of [0, 1, 4, 86, 123456]) for (const retryMb of [0, 1, 10240, 14336, 40000, ESCALATE_RETRY_MB - 1, ESCALATE_RETRY_MB, ESCALATE_RETRY_MB + 1, 999999]) {
    cases++
    const g = rules.escalation({ complete, toobig, retryMb })
    const want = complete && toobig > 0 && retryMb < ESCALATE_RETRY_MB
    if (g.escalate !== want || typeof g.why !== "string" || !g.why) v("escalation", `${JSON.stringify({ complete, toobig, retryMb })}: ${JSON.stringify(g)}`)
  }
  // the real states flt-anthropic had (Nov 2026): 4 modules too big at 14336 MB, 84 behind them, the build "complete"; then after the escalation round
  const flt = [
    [{ complete: true, toobig: 4, retryMb: 14336 }, true],
    [{ complete: true, toobig: 4, retryMb: ESCALATE_RETRY_MB }, false],
    [{ complete: true, toobig: 0, retryMb: ESCALATE_RETRY_MB }, false],
    [{ complete: false, toobig: 4, retryMb: 14336 }, false],
    [{ complete: true, toobig: 0, retryMb: 14336 }, false],
  ]
  for (const [s, want] of flt) { cases++; if (rules.escalation(s).escalate !== want) v("escalation on a real state of flt-anthropic", JSON.stringify(s)) }
  // buildAttempts and soloMax: the defaults for a build without swap, the larger ones for the escalation's, a valid setting wins, anything else is ignored
  // literal expected values, written out (not recomputed with the rule's own regex): which retry limits are the escalation's (57344 MB or more, read as a number), and what each setting means
  const retries = [[undefined, false], ["", false], [" ", false], ["abc", false], ["-1", false], ["0", false], ["1", false], ["500", false], ["14336", false], ["40000", false], ["57343", false], ["57343.9", false], ["5e4", false],
    ["57344", true], [" 57344 ", true], ["57344.5", true], ["57345", true], ["6e4", true], ["99999999", true]]
  const settings = [[undefined, null], ["", null], [" ", null], ["0", null], ["1", 1], ["2", 2], ["4", 4], ["7", 7], ["25", 25], ["99", 99], ["100", 100], ["999", 999], ["1000", 1000], ["1001", null], ["99999", null], ["-3", null],
    ["2.5", null], ["1e2", null], ["abc", null], ["0012", null], [" 12 ", 12], ["12 ", 12], ["0x10", null], ["٣", null], ["5;rm", null]]
  for (const [r, isEsc] of retries) for (const [s, set] of settings) for (const [fn, key, dflt, bigger] of [["buildAttempts", "EMISSARY_BUILD_ATTEMPTS", BUILD_ATTEMPTS_DEFAULT, BUILD_ATTEMPTS_ESCALATED], ["soloMax", "EMISSARY_SOLO_MAX", SOLO_MAX_DEFAULT, SOLO_MAX_ESCALATED]]) {
    cases++
    const env = {}
    if (r !== undefined) env.EMISSARY_RETRY_FOOTPRINT_MB = r
    if (s !== undefined) env[key] = s
    const want = set ?? (isEsc ? bigger : dflt)
    const got = rules[fn](env)
    if (got !== want) v(fn, `${JSON.stringify(env)}: ${got} != ${want}`)
  }
  cases++
  if (BUILD_ATTEMPTS_DEFAULT !== 4 || SOLO_MAX_DEFAULT !== 25 || BUILD_ATTEMPTS_ESCALATED !== 100 || SOLO_MAX_ESCALATED !== 200 || ESCALATED_RETRY_MB !== 57344 || ESCALATED_RETRY_MB !== ESCALATE_RETRY_MB) v("the constants are not 4/25/100/200 and the escalation's 57344 (setup-plan.mjs ESCALATE_RETRY_MB)")
  cases++
  if (rules.buildAttempts({}) !== 4 || rules.soloMax({}) !== 25) v("buildAttempts/soloMax: the unset defaults are not 4 and 25 (a build without swap is unchanged)")
  cases++
  if (rules.buildAttempts({ EMISSARY_RETRY_FOOTPRINT_MB: "57344" }) < 86 || rules.soloMax({ EMISSARY_RETRY_FOOTPRINT_MB: "57344" }) < 86) v("the escalation's round cannot try or rescue the 86 modules of flt-anthropic")
  // the escalation round is one round: asking again with the settings it dispatched never escalates
  cases++
  if (rules.escalation({ complete: true, toobig: 9, retryMb: ESCALATE_RETRY_MB }).escalate) v("the escalated round escalates again")
  return { cases, violations }
}

const real = { availableFrom, soloBuildMs, escalation, buildAttempts, soloMax }
const good = run(real, true)
console.log(`memory rules: ${good.cases} cases over ${samples.length} real memory samples (${fixture.source}): ${good.violations} violations`)
check("the real rules hold on every case", good.violations === 0, good.violations)
check("the escalation settings are inside what a hosted runner and a job can do", ESCALATE_SWAP_GB >= 16 && ESCALATE_SWAP_GB <= 100 && ESCALATE_SOLO_MINUTES <= 340 && ESCALATE_RETRY_MB > 14336 && ESCALATE_RETRY_MB <= (16 + ESCALATE_SWAP_GB) * 1024, `${ESCALATE_RETRY_MB} ${ESCALATE_SWAP_GB} ${ESCALATE_SOLO_MINUTES}`)


// ---- membersOf: which files of a packed build belong to the modules whose closure is restored (only_modules) ----
// Every real module of every library set up so far (scripts/fixtures/real-module-lists.json: 110 libraries, 14,913 modules, with dots, guillemets and long names) gets the files a Lake build leaves for it
// (olean, ilean, hashes, trace, C output, and the setup.json that is never restored), in both places, in a made-up archive listing; a random subset is kept, and the files returned must be exactly
// the files of the kept modules, whatever their neighbours are called (A, A_b, A.B and AB all in one archive).
{
  const real = JSON.parse(readFileSync(join(here, "fixtures", "real-module-lists.json"), "utf8"))
  const componentsOf = (m) => m.match(/«[^»]+»|[^.«»]+/g)
  const pathOf = (m) => componentsOf(m).map((c) => c.replace(/^«|»$/g, "")).join("/")   // as setup-source.mjs pathOfModule: no guillemets in a file path
  const LIB = [".olean", ".ilean", ".olean.hash", ".ilean.hash", ".trace", ".hash"], IR = [".c", ".c.hash", ".setup.json"]
  const filesOf = (m) => [...LIB.map((s) => `.lake/build/lib/lean/${pathOf(m)}${s}`), ...IR.map((s) => `.lake/build/ir/${pathOf(m)}${s}`)]
  const wanted = (m) => filesOf(m).filter((f) => !f.endsWith(".setup.json"))
  let seed = 42
  const rnd = (n) => { seed = (seed + 0x6d2b79f5) | 0; let x = Math.imul(seed ^ (seed >>> 15), 1 | seed); x = (x + Math.imul(x ^ (x >>> 7), 61 | x)) ^ x; return ((x ^ (x >>> 14)) >>> 0) % n }
  const run2 = (rule, print) => {
    let cases = 0, wrongM = 0
    for (const [lib, mods] of Object.entries(real)) {
      const all = [...new Set(mods)]
      for (const frac of [0, 1, 5, 50, 100]) {
        const keepMods = all.filter(() => rnd(100) < frac)
        const keep = new Set(keepMods.map(pathOf))
        const listing = [...all.flatMap(filesOf), ".lake/build/lib/lean/", ".lake/build/", ".lake/build/lib/lean/Zzz.lock", ".lake/build/ir/Lib.c.txt", "./.lake/build/lib/lean/Elsewhere.olean"].sort(() => rnd(3) - 1).join("\n")
        const got = rule(listing, keep).sort()
        const want = keepMods.flatMap(wanted).sort()
        cases++
        // never one file too few; a file too many only where a kept module's path is the start of another module's (X/c and X/c.d)
        const wantSet = new Set(want)
        const allPaths = all.map(pathOf)
        const extraOk = (f) => [...keep].some((k) => allPaths.some((q) => q.startsWith(`${k}.`) && f.includes(`/${q}.`)))   // a file of a module whose path starts with a kept path plus a dot
        if (want.some((f) => !got.includes(f)) || got.some((f) => !wantSet.has(f) && !extraOk(f))) { wrongM++; if (print && wrongM <= 3) console.log("FAIL membersOf", lib, frac, got.length, want.length) }
      }
    }
    return { cases, wrongM }
  }
  const goodM = run2(membersOf, true)
  const nmods = Object.values(real).reduce((a, m) => a + new Set(m).size, 0)
  check(`membersOf returns every file of the kept modules and nothing else (bar a module whose path starts another's), on ${goodM.cases} real library listings (${nmods} real modules, ${nmods * 9} files, 5 keep fractions), never a setup.json`, goodM.wrongM === 0, goodM.wrongM)
  // neighbours with a similar name are not confused
  const near = ["A", "A_b", "AB", "A.B", "A.B.C", "Ab"].flatMap((m) => filesOf(m)).join("\n")
  { const odd = ["«a.b».C", "X.«c.d»", "Y.«e.f».«g.h»", "Lib.α"], ol = odd.flatMap(filesOf).join("\n"); check("modules with dotted «guillemet» components (their files are X/c.d.olean, with no guillemets) and Unicode names are found", odd.every((m) => JSON.stringify(membersOf(ol, new Set([pathOf(m)])).sort()) === JSON.stringify(wanted(m).sort())), odd.map((m) => `${m} -> ${pathOf(m)}`).join(" ")) }
  { const both = ["X.c", "X.«c.d»"], bl = both.flatMap(filesOf).join("\n"); check("a module and one whose path starts with its own (X/c and X/c.d): keeping X/c.d takes only its own files, keeping X/c may take both, never fewer", JSON.stringify(membersOf(bl, new Set(["X/c.d"])).sort()) === JSON.stringify(wanted("X.«c.d»").sort()) && wanted("X.c").every((f) => membersOf(bl, new Set(["X/c"])).includes(f)), "") }
  check("neighbouring names (A, A_b, AB, A.B, Ab) are told apart", JSON.stringify(membersOf(near, new Set(["A"])).sort()) === JSON.stringify(wanted("A").sort()) && JSON.stringify(membersOf(near, new Set(["A/B"])).sort()) === JSON.stringify(wanted("A.B").sort()), "")
  const brokenRules = {
    "setup.json files are restored too": (l, k) => { const out = []; for (const line of l.split("\n")) { const m = /^\.lake\/build\/(?:lib\/lean|ir)\/(.+)$/.exec(line); if (!m) continue; const parts = m[1].split("/"); const last = parts.pop(); if (k.has([...parts, last.split(".")[0]].join("/"))) out.push(line) } return out },
    "a module is matched by prefix (A takes A_b)": (l, k) => l.split("\n").filter((line) => [...k].some((x) => line.includes(`/${x}`))),
    "only the lib/lean files are kept, not the C output": (l, k) => membersOf(l, k).filter((f) => f.includes("/lib/lean/")),
    "the path is cut at the first dot of the file name (the old rule)": (l, k) => { const out = []; for (const line of l.split("\n")) { const m = /^\.lake\/build\/(?:lib\/lean|ir)\/(.+)$/.exec(line); if (!m || line.endsWith(".setup.json")) continue; const parts = m[1].split("/"); const last = parts.pop(); if (k.has([...parts, last.split(".")[0]].join("/"))) out.push(line) } return out },
  }
  let caughtM = 0
  for (const [name, rule] of Object.entries(brokenRules)) {
    const r = run2(rule, false)
    // names the real corpus may not have: a dotted «guillemet» component, one more neighbour
    const odd = ["«a.b».C", "X.«c.d»", "Y.«e.f».«g.h»", "Lib.α"]
    const oddListing = odd.flatMap(filesOf).join("\n")
    for (const keepOne of odd) { r.cases++; if (JSON.stringify(rule(oddListing, new Set([pathOf(keepOne)])).sort()) !== JSON.stringify(wanted(keepOne).sort())) r.wrongM++ }
    if (r.wrongM > 0) caughtM++
    check(`the broken version "${name}" is caught (${r.wrongM} of ${r.cases} listings wrong)`, r.wrongM > 0, "")
  }
  check("every broken membersOf was caught", caughtM === Object.keys(brokenRules).length, `${caughtM}`)
}

// setup-source.mjs really uses them: the solo build is bounded by the rule, the guard reads meminfo through it
{
  const src = readFileSync(join(here, "setup-source.mjs"), "utf8")
  check("buildAlone's timeout is the rule's, not a fixed 90 minutes", /const SOLO_BUILD_MS = soloBuildMs\(\)/.test(src) && /run\("lake", \["build", m\], \{ cwd: REPO, timeoutMs: SOLO_BUILD_MS \}\)/.test(src), "")
  check("a chunk is tried BUILD_ATTEMPTS times (the rule's number), not a fixed 4, and the solo cap is the rule's", /const BUILD_ATTEMPTS = buildAttempts\(\)/.test(src) && /attempt < BUILD_ATTEMPTS; attempt\+\+/.test(src) && /const SOLO_MAX = soloMax\(\)/.test(src) && !/attempt < 4/.test(src), "")
  check("the available-memory guard reads /proc/meminfo through availableFrom, counting swap only when the job said so (EMISSARY_COUNT_SWAP=1)", /availableFrom\(readFileSync\("\/proc\/meminfo", "utf8"\), COUNT_SWAP\)/.test(src) && /const COUNT_SWAP = process\.env\.EMISSARY_COUNT_SWAP === "1"/.test(src), "")
}

// ---- closureRetryMs / closureBudgetMs: a closure that ran out of time alone gets one longer try while the job's budget holds it (flt-anthropic, 6 Nov 2026: 86 top-of-proof modules "failed") ----
{
  const MIN = 60 * 1000
  const rule = (impl) => {
    let cases = 0, wrongN = 0
    for (const singleMs of [1000, 3500, 20 * MIN, 59 * MIN, 61 * MIN, 120 * MIN, 600 * MIN]) for (const elapsedMs of [0, 1, 17 * MIN, 100 * MIN, 280 * MIN, 299 * MIN, 300 * MIN, 5000 * MIN]) for (const budgetMs of [300 * MIN, 12 * 1000, 1, 0, -5, 340 * MIN]) {
      cases++
      const want = Math.min(singleMs * 4, 4 * 60 * MIN)
      const ok = budgetMs > 0 && budgetMs - elapsedMs >= want
      if (impl({ singleMs, elapsedMs, budgetMs }) !== (ok ? want : 0)) wrongN++
    }
    for (const bad of [{ singleMs: 0, elapsedMs: 0, budgetMs: 1e9 }, { singleMs: -1, elapsedMs: 0, budgetMs: 1e9 }, { singleMs: 1000, elapsedMs: -1, budgetMs: 1e9 }, { singleMs: NaN, elapsedMs: 0, budgetMs: 1e9 }, { singleMs: 1000, elapsedMs: 0, budgetMs: NaN }]) { cases++; if (impl(bad) !== 0) wrongN++ }
    return { cases, wrongN }
  }
  const good = rule(closureRetryMs)
  check(`closureRetryMs: four times the limit, at most four hours, only while the budget holds it, on ${good.cases} cases`, good.wrongN === 0 && CLOSURE_RETRY_FACTOR === 4 && CLOSURE_RETRY_MAX_MS === 4 * 60 * MIN, good.wrongN)
  check("the real case: a module alone gets 20 minutes, its retry is 80 minutes, 17 minutes into a 300-minute budget", closureRetryMs({ singleMs: 20 * MIN, elapsedMs: 17 * MIN, budgetMs: 300 * MIN }) === 80 * MIN && closureRetryMs({ singleMs: 20 * MIN, elapsedMs: 230 * MIN, budgetMs: 300 * MIN }) === 0, "")
  for (const [name, impl] of Object.entries({
    "the factor is 2": ({ singleMs, elapsedMs, budgetMs }) => (budgetMs - elapsedMs >= Math.min(singleMs * 2, 4 * 60 * MIN) ? Math.min(singleMs * 2, 4 * 60 * MIN) : 0),
    "no four hour ceiling": ({ singleMs, elapsedMs, budgetMs }) => (budgetMs - elapsedMs >= singleMs * 4 ? singleMs * 4 : 0),
    "the budget is ignored": ({ singleMs }) => Math.min(singleMs * 4, 4 * 60 * MIN),
    "a try is made that does not fit the budget": ({ singleMs, elapsedMs, budgetMs }) => (budgetMs - elapsedMs > 0 ? Math.min(singleMs * 4, 4 * 60 * MIN) : 0),
  })) check(`mutant: ${name} is noticed`, rule(impl).wrongN > 0, "")
  const budgetTable = [[undefined, CLOSURE_BUDGET_DEFAULT_MS], ["", CLOSURE_BUDGET_DEFAULT_MS], ["abc", CLOSURE_BUDGET_DEFAULT_MS], ["0", CLOSURE_BUDGET_DEFAULT_MS], ["-5", CLOSURE_BUDGET_DEFAULT_MS], ["1e2", CLOSURE_BUDGET_DEFAULT_MS], ["341", CLOSURE_BUDGET_DEFAULT_MS], ["340", 340 * MIN], ["0.2", 12000], ["120", 120 * MIN], [" 120 ", 120 * MIN], ["300", 300 * MIN]]
  check(`closureBudgetMs: minutes, a number up to 340, anything else is the default (${budgetTable.length} settings)`, budgetTable.every(([v, want]) => closureBudgetMs(v === undefined ? {} : { EMISSARY_CLOSURE_BUDGET_MINUTES: v }) === want), "")
}

// broken versions: each must be noticed
const valid0 = (s) => typeof s === "string" && /^[1-9][0-9]{0,3}$/.test(s.trim()) && Number(s) <= 1000
const mutants = {
  "swap is always counted": { ...real, availableFrom: (t) => availableFrom(t, true) },
  "swap is never counted": { ...real, availableFrom: (t) => availableFrom(t, false) },
  "SwapTotal is counted instead of SwapFree": { ...real, availableFrom: (t, c) => { const a = availableFrom(t, false); const m = /^SwapTotal:\s+(\d+) kB/m.exec(t); return c && m ? a + Number(m[1]) / 1024 : a } },
  "a text with no MemAvailable is zero": { ...real, availableFrom: (t, c) => { const r = availableFrom(t, c); return r === Infinity ? 0 : r } },
  "the solo time has no upper limit": { ...real, soloBuildMs: (env) => (Number(env.EMISSARY_SOLO_BUILD_MINUTES) > 0 ? Number(env.EMISSARY_SOLO_BUILD_MINUTES) * 60e3 : SOLO_BUILD_DEFAULT_MS) },
  "the solo time accepts a value that rounds to 0 ms": { ...real, soloBuildMs: (env) => { const v = env.EMISSARY_SOLO_BUILD_MINUTES; if (typeof v !== "string" || !/^[0-9]+(\.[0-9]+)?$/.test(v.trim())) return SOLO_BUILD_DEFAULT_MS; const m = Number(v); return m > 0 && m <= 340 ? Math.round(m * 60e3) : SOLO_BUILD_DEFAULT_MS } },
  "the solo time accepts anything Number() accepts": { ...real, soloBuildMs: (env) => (Number(env.EMISSARY_SOLO_BUILD_MINUTES) > 0 && Number(env.EMISSARY_SOLO_BUILD_MINUTES) <= 340 ? Math.round(Number(env.EMISSARY_SOLO_BUILD_MINUTES) * 60e3) : SOLO_BUILD_DEFAULT_MS) },
  "a chunk is always tried 4 times": { ...real, buildAttempts: () => 4 },
  "the escalation's round gets the same tries as any build": { ...real, buildAttempts: (env) => { const v = env.EMISSARY_BUILD_ATTEMPTS; return typeof v === "string" && /^[1-9][0-9]{0,3}$/.test(v.trim()) && Number(v) <= 1000 ? Number(v) : 4 } },
  "the solo cap is always 25": { ...real, soloMax: () => 25 },
  "the tries setting accepts anything Number() accepts": { ...real, buildAttempts: (env) => (Number(env.EMISSARY_BUILD_ATTEMPTS) > 0 ? Number(env.EMISSARY_BUILD_ATTEMPTS) : real.buildAttempts({ ...env, EMISSARY_BUILD_ATTEMPTS: undefined })) },
  "the solo cap has no upper limit": { ...real, soloMax: (env) => (Number(env.EMISSARY_SOLO_MAX) > 0 ? Number(env.EMISSARY_SOLO_MAX) : real.soloMax({ ...env, EMISSARY_SOLO_MAX: undefined })) },
  "a limit just below the escalation's counts as escalated": { ...real, buildAttempts: (env) => (valid0(env.EMISSARY_BUILD_ATTEMPTS) ? Number(env.EMISSARY_BUILD_ATTEMPTS) : Number(env.EMISSARY_RETRY_FOOTPRINT_MB) >= ESCALATED_RETRY_MB - 1 ? BUILD_ATTEMPTS_ESCALATED : 4) },
  "the retry limit is read as whole digits only (57344.5 and 6e4 are not escalated)": { ...real, buildAttempts: (env) => (valid0(env.EMISSARY_BUILD_ATTEMPTS) ? Number(env.EMISSARY_BUILD_ATTEMPTS) : /^[0-9]+$/.test(String(env.EMISSARY_RETRY_FOOTPRINT_MB ?? "").trim()) && Number(env.EMISSARY_RETRY_FOOTPRINT_MB) >= ESCALATED_RETRY_MB ? BUILD_ATTEMPTS_ESCALATED : 4) },
  "the escalated limit is 49152 (not the escalation's 57344)": { ...real, buildAttempts: (env) => (valid0(env.EMISSARY_BUILD_ATTEMPTS) ? Number(env.EMISSARY_BUILD_ATTEMPTS) : Number(env.EMISSARY_RETRY_FOOTPRINT_MB) >= 49152 ? BUILD_ATTEMPTS_ESCALATED : 4) },
  "the escalation never stops (no limit check)": { ...real, escalation: (s) => ({ escalate: s.complete && s.toobig > 0, why: "x" }) },
  "the escalation ignores a build that is not complete": { ...real, escalation: (s) => ({ escalate: s.toobig > 0 && s.retryMb < ESCALATE_RETRY_MB, why: "x" }) },
  "the escalation fires with nothing too big": { ...real, escalation: (s) => ({ escalate: s.complete && s.retryMb < ESCALATE_RETRY_MB, why: "x" }) },
}
let caught = 0
for (const [name, rules] of Object.entries(mutants)) {
  const r = run(rules, false)
  if (r.violations > 0) caught++
  check(`the broken version "${name}" is caught (${r.violations} violations in ${r.cases} cases)`, r.violations > 0, "")
}
check("every broken version was caught", caught === Object.keys(mutants).length, `${caught}/${Object.keys(mutants).length}`)
process.exit(bad ? 1 : 0)

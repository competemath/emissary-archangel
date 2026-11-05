// node scripts/test-memory-rules.mjs — the memory rules that decide whether a module too big for a runner is tried again, on REAL values.
//   1. availableFrom (the guard that kills the biggest process when the runner runs out of memory): scripts/fixtures/real-free-memory.json holds every real "free memory" sample
//      the sampler took on the runners that built flt-anthropic and others (build-metrics.tsv of the setup-sharded rounds, one line a minute). Each is put into a /proc/meminfo text
//      with swap of every size seen on runners (none, the 4 GB of a hosted runner, the 48 GB the escalation round adds) and checked:
//        a. without countSwap the answer is exactly MemAvailable, whatever the swap (the old guard, unchanged);
//        b. with countSwap it is MemAvailable plus SwapFree, never less than without;
//        c. the guard (under 1536 MB left) fires on the same samples as before when swap is not counted, and on none of them with 48 GB of swap counted;
//        d. a text with no MemAvailable (not Linux) is Infinity.
//   2. soloBuildMs (how long a killed module may take alone): the values the workflow inputs can hold, and values that must fall back to the default.
//   3. escalation (setup-plan.mjs): every combination of the build's state, and the real states flt-anthropic had.
// Then the same checks run on broken versions of each rule, and each must be caught.
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { availableFrom, soloBuildMs, SOLO_BUILD_DEFAULT_MS } from "./memory-rules.mjs"
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
  // the escalation round is one round: asking again with the settings it dispatched never escalates
  cases++
  if (rules.escalation({ complete: true, toobig: 9, retryMb: ESCALATE_RETRY_MB }).escalate) v("the escalated round escalates again")
  return { cases, violations }
}

const real = { availableFrom, soloBuildMs, escalation }
const good = run(real, true)
console.log(`memory rules: ${good.cases} cases over ${samples.length} real memory samples (${fixture.source}): ${good.violations} violations`)
check("the real rules hold on every case", good.violations === 0, good.violations)
check("the escalation settings are inside what a hosted runner and a job can do", ESCALATE_SWAP_GB >= 16 && ESCALATE_SWAP_GB <= 100 && ESCALATE_SOLO_MINUTES <= 340 && ESCALATE_RETRY_MB > 14336 && ESCALATE_RETRY_MB <= (16 + ESCALATE_SWAP_GB) * 1024, `${ESCALATE_RETRY_MB} ${ESCALATE_SWAP_GB} ${ESCALATE_SOLO_MINUTES}`)

// setup-source.mjs really uses them: the solo build is bounded by the rule, the guard reads meminfo through it
{
  const src = readFileSync(join(here, "setup-source.mjs"), "utf8")
  check("buildAlone's timeout is the rule's, not a fixed 90 minutes", /const SOLO_BUILD_MS = soloBuildMs\(\)/.test(src) && /run\("lake", \["build", m\], \{ cwd: REPO, timeoutMs: SOLO_BUILD_MS \}\)/.test(src), "")
  check("the available-memory guard reads /proc/meminfo through availableFrom, counting swap only when the job said so (EMISSARY_COUNT_SWAP=1)", /availableFrom\(readFileSync\("\/proc\/meminfo", "utf8"\), COUNT_SWAP\)/.test(src) && /const COUNT_SWAP = process\.env\.EMISSARY_COUNT_SWAP === "1"/.test(src), "")
}

// broken versions: each must be noticed
const mutants = {
  "swap is always counted": { ...real, availableFrom: (t) => availableFrom(t, true) },
  "swap is never counted": { ...real, availableFrom: (t) => availableFrom(t, false) },
  "SwapTotal is counted instead of SwapFree": { ...real, availableFrom: (t, c) => { const a = availableFrom(t, false); const m = /^SwapTotal:\s+(\d+) kB/m.exec(t); return c && m ? a + Number(m[1]) / 1024 : a } },
  "a text with no MemAvailable is zero": { ...real, availableFrom: (t, c) => { const r = availableFrom(t, c); return r === Infinity ? 0 : r } },
  "the solo time has no upper limit": { ...real, soloBuildMs: (env) => (Number(env.EMISSARY_SOLO_BUILD_MINUTES) > 0 ? Number(env.EMISSARY_SOLO_BUILD_MINUTES) * 60e3 : SOLO_BUILD_DEFAULT_MS) },
  "the solo time accepts a value that rounds to 0 ms": { ...real, soloBuildMs: (env) => { const v = env.EMISSARY_SOLO_BUILD_MINUTES; if (typeof v !== "string" || !/^[0-9]+(\\.[0-9]+)?$/.test(v.trim())) return SOLO_BUILD_DEFAULT_MS; const m = Number(v); return m > 0 && m <= 340 ? Math.round(m * 60e3) : SOLO_BUILD_DEFAULT_MS } },
  "the solo time accepts anything Number() accepts": { ...real, soloBuildMs: (env) => (Number(env.EMISSARY_SOLO_BUILD_MINUTES) > 0 && Number(env.EMISSARY_SOLO_BUILD_MINUTES) <= 340 ? Math.round(Number(env.EMISSARY_SOLO_BUILD_MINUTES) * 60e3) : SOLO_BUILD_DEFAULT_MS) },
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

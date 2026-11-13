// node scripts/test-memory-storm.mjs — the kill-storm rule of scripts/memory-rules.mjs (stormKills, stormTripped) on the REAL kills of finite-simple-groups-lean.
//
// scripts/fixtures/real-fsgl-memory-kills.json: every `memory watchdog: killed` line of the first lake build chunk of setup-sharded run 43435939792 (13 Nov 2026, round 1 build 2, four Lean threads on a
// 16 GB runner): 610 kills in 4.96 hours of FiniteSimpleGroups.Sporadic.Co2.SiftCert<N> modules at 3.4-7.9 GB each, one kill every 30-60 s, one chunk that never ended, 15 of 3,964 modules built.
// Checked:
//   a. replayed with the default limit on four threads the rule trips at the 8th kill, 230 s after the first (the real run went on for 17,850 s): it would have stopped the chunk 99% sooner;
//   b. on one thread it never trips, whatever the kills (there a kill is a module that does not fit alone, which the solo rule handles);
//   c. it never trips before the limit, and always at or after it, on several threads (every kill count 0-700, every limit, threads 1-8);
//   d. 5,000 random (kills, threads, limit) agree with the rule written apart;
//   e. stormKills reads the setting: a whole number 1-1000 (spaces allowed), anything else is the default 8.
// Then the same checks on broken versions (threads ignored, > for >=, the limit ignored, the default changed, a setting of 0 accepted), and each must be caught.
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import * as real from "./memory-rules.mjs"

const here = dirname(fileURLToPath(import.meta.url))
const fx = JSON.parse(readFileSync(join(here, "fixtures", "real-fsgl-memory-kills.json"), "utf8"))
let bad = 0
const check = (name, ok, detail) => {
  console.log(`${ok ? "ok" : "FAIL"} ${name}`)
  if (!ok) { bad++; if (detail !== undefined) console.log(String(detail).slice(0, 400)) }
}

function run(rules, print) {
  let cases = 0, violations = 0
  const v = (what, detail) => { violations++; if (print && violations <= 8) console.log("FAIL", what, detail ?? "") }
  const t = (what, ok, detail) => { cases++; if (!ok) v(what, detail) }
  const limit = rules.stormKills({})
  // a. the real run
  const kills = fx.kills
  t("a: 610 real kills", kills.length === 610, kills.length)
  let tripAt = null
  for (let n = 1; n <= kills.length; n++) if (tripAt === null && rules.stormTripped({ kills: n, threads: fx.threads, limit })) tripAt = n
  t("a: trips at the 8th kill", tripAt === 8, tripAt)
  t("a: within 5 minutes of the first kill", tripAt !== null && kills[tripAt - 1][0] <= 300, tripAt && kills[tripAt - 1][0])
  t("a: 99% sooner than the real run", tripAt !== null && kills[tripAt - 1][0] / kills[kills.length - 1][0] < 0.02, tripAt && kills[tripAt - 1][0])
  // b. one thread: never
  for (let n = 0; n <= 700; n++) t("b: one thread never trips", !rules.stormTripped({ kills: n, threads: 1, limit }), n)
  // c. grid
  for (let threads = 1; threads <= 8; threads++)
    for (const lim of [1, 2, 3, 8, 50, 1000])
      for (let n = 0; n <= 700; n += 1) {
        const got = rules.stormTripped({ kills: n, threads, limit: lim })
        if (threads > 1 && n >= lim) t("c: trips at or after the limit", got === true, `${n} ${threads} ${lim}`)
        else t("c: not before the limit, not on one thread", got === false, `${n} ${threads} ${lim}`)
      }
  // d. random
  let seed = 7
  const rnd = (m) => ((seed = (seed * 1103515245 + 12345) & 0x7fffffff) % m)
  for (let i = 0; i < 5000; i++) {
    const a = { kills: rnd(2000), threads: 1 + rnd(16), limit: 1 + rnd(1000) }
    t("d: against the rule written apart", rules.stormTripped(a) === (a.threads > 1 && a.kills >= a.limit), JSON.stringify(a))
  }
  // e. the setting
  for (const [v_, want] of [["12", 12], [" 7 ", 7], ["1", 1], ["1000", 1000], ["0", 8], ["1001", 8], ["abc", 8], ["", 8], ["-3", 8], ["2.5", 8], ["5e2", 8], [undefined, 8]]) {
    t(`e: EMISSARY_STORM_KILLS=${JSON.stringify(v_)}`, rules.stormKills(v_ === undefined ? {} : { EMISSARY_STORM_KILLS: v_ }) === want, rules.stormKills(v_ === undefined ? {} : { EMISSARY_STORM_KILLS: v_ }))
  }
  return { cases, violations }
}

const r0 = run(real, true)
check(`the rule holds on ${r0.cases} cases (the real run, one thread, a grid, 5,000 random, the setting)`, r0.violations === 0, `${r0.violations} violations`)

const mutants = {
  "threads ignored (trips on one thread too)": { ...real, stormTripped: ({ kills, limit }) => kills >= limit },
  "> instead of >=": { ...real, stormTripped: ({ kills, threads, limit }) => threads > 1 && kills > limit },
  "the limit ignored (trips at once)": { ...real, stormTripped: ({ threads }) => threads > 1 },
  "never trips": { ...real, stormTripped: () => false },
  "the default limit is 80": { ...real, stormKills: (env = {}) => (/^[1-9][0-9]{0,3}$/.test(String(env.EMISSARY_STORM_KILLS ?? "").trim()) && Number(env.EMISSARY_STORM_KILLS) <= 1000 ? Number(env.EMISSARY_STORM_KILLS) : 80) },
  "a setting of 0 is taken": { ...real, stormKills: (env = {}) => (/^[0-9]{1,4}$/.test(String(env.EMISSARY_STORM_KILLS ?? "").trim()) ? Number(env.EMISSARY_STORM_KILLS) : 8) },
}
let caught = 0
for (const [name, rules] of Object.entries(mutants)) {
  const r = run(rules, false)
  if (r.violations > 0) caught++
  check(`the broken version "${name}" is caught (${r.violations} violations in ${r.cases} cases)`, r.violations > 0, "")
}
check("every broken version was caught", caught === Object.keys(mutants).length, `${caught}/${Object.keys(mutants).length}`)
process.exit(bad ? 1 : 0)

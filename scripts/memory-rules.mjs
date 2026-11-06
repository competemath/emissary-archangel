// The memory rules of scripts/setup-source.mjs that do not need a Lean process to be checked (scripts/test-memory-rules.mjs runs them on real values).

// How long one module killed for its memory may take when built alone: 90 minutes, and for the round that gives such modules swap and a bigger limit
// (setup-sharded.yml, solo_minutes) as long as the job has. A value that is not a positive number of minutes the job can hold is the default
// (a wait longer than the job's 350 minutes would only lose the round).
export const SOLO_BUILD_DEFAULT_MS = 90 * 60 * 1000
export const SOLO_BUILD_MAX_MINUTES = 340
export function soloBuildMs(env = process.env) {
  const v = env.EMISSARY_SOLO_BUILD_MINUTES
  if (typeof v !== "string" || !/^[0-9]+(\.[0-9]+)?$/.test(v.trim())) return SOLO_BUILD_DEFAULT_MS
  const minutes = Number(v)
  const ms = Math.round(minutes * 60 * 1000)
  return minutes <= SOLO_BUILD_MAX_MINUTES && ms > 0 ? ms : SOLO_BUILD_DEFAULT_MS // a sub-millisecond value rounds to 0, which would end every solo build at once
}

// How many times one chunk of the build is tried, and how many killed modules one run builds alone. A killed module is built alone and the chunk is tried again; when a
// chain of big modules each imports the one before (flt-anthropic: a `Thm_` module imports its `P2M.Sol` proof), every try finds ONE new kill, so the number of tries is
// the number of modules the round can finish. 4 tries and 25 solos were the defaults of a build that had no swap; the round that has swap (the retry limit is the escalation's,
// 57344 MB or more, setup-plan.mjs ESCALATE_RETRY_MB) finished 4 of the 86 modules per round (round 4, 2026-11-05) while a restore alone costs 28 minutes. A try always rescues something, or the chunk stops,
// so a higher number only lets a chunk that is making progress go on. EMISSARY_BUILD_ATTEMPTS and EMISSARY_SOLO_MAX (a positive whole number up to 1000) set them; anything else is the default.
export const BUILD_ATTEMPTS_DEFAULT = 4
export const SOLO_MAX_DEFAULT = 25
export const ESCALATED_RETRY_MB = 57344 // setup-plan.mjs ESCALATE_RETRY_MB (test-memory-rules.mjs checks they are the same number)
export const BUILD_ATTEMPTS_ESCALATED = 100
export const SOLO_MAX_ESCALATED = 200
const positiveInt = (v, max) => (typeof v === "string" && /^[1-9][0-9]{0,3}$/.test(v.trim()) && Number(v) <= max ? Number(v) : null)
const escalated = (env) => Number(env.EMISSARY_RETRY_FOOTPRINT_MB) >= ESCALATED_RETRY_MB // the same reading of the number as setup-source.mjs RETRY_FOOTPRINT_MB (57344.5 and 6e4 count)
export const buildAttempts = (env = process.env) => positiveInt(env.EMISSARY_BUILD_ATTEMPTS, 1000) ?? (escalated(env) ? BUILD_ATTEMPTS_ESCALATED : BUILD_ATTEMPTS_DEFAULT)
export const soloMax = (env = process.env) => positiveInt(env.EMISSARY_SOLO_MAX, 1000) ?? (escalated(env) ? SOLO_MAX_ESCALATED : SOLO_MAX_DEFAULT)

// A module whose closure ran out of time alone gets ONE more try with a longer limit (flt-anthropic, 6 Nov 2026: the closure of the 86 top-of-proof modules, the final theorem among them, took
// more than the 20 minutes a single module gets, so the export recorded "86 failed" after 5 hours and nobody could tell the library from a module that needs more time). The retry is four times the
// first limit, at most four hours, and only when what is left of the job's budget (EMISSARY_CLOSURE_BUDGET_MINUTES, default and at most 300: the shard process's own timeout) holds it; 0 means no retry.
export const CLOSURE_RETRY_FACTOR = 4
export const CLOSURE_RETRY_MAX_MS = 4 * 60 * 60 * 1000
export const CLOSURE_BUDGET_DEFAULT_MS = 300 * 60 * 1000
export function closureBudgetMs(env = process.env) {
  const v = env.EMISSARY_CLOSURE_BUDGET_MINUTES
  if (typeof v !== "string" || !/^[0-9]+(\.[0-9]+)?$/.test(v.trim())) return CLOSURE_BUDGET_DEFAULT_MS
  const ms = Math.round(Number(v) * 60 * 1000)
  return ms > 0 && ms <= CLOSURE_BUDGET_DEFAULT_MS ? ms : CLOSURE_BUDGET_DEFAULT_MS  // never more than the 300 minutes of the shard process (setup-sharded.yml): a longer budget could be cut off by the workflow before it ends
}
export function closureRetryMs({ singleMs, elapsedMs, budgetMs }) {
  if (!(singleMs > 0) || !(elapsedMs >= 0) || !(budgetMs > 0)) return 0
  const want = Math.min(singleMs * CLOSURE_RETRY_FACTOR, CLOSURE_RETRY_MAX_MS)
  return budgetMs - elapsedMs >= want ? want : 0
}

// Memory a process can still get, in MB, from the text of /proc/meminfo. With `countSwap` (the job added swap for the modules that do not fit in a runner's RAM,
// EMISSARY_COUNT_SWAP=1) the free swap counts too: those modules are meant to run on swap, and RAM alone is nearly all used then, which the guard would take for a
// shortage and kill the very module the swap was added for. Without it swap is not counted: the 4 GB a hosted runner has by default must not hide a real shortage.
// Infinity when the text has no MemAvailable (not Linux): nothing to judge by.
export function availableFrom(meminfo, countSwap = false) {
  const m = /^MemAvailable:\s+(\d+) kB/m.exec(meminfo)
  if (!m) return Infinity
  const swap = countSwap ? /^SwapFree:\s+(\d+) kB/m.exec(meminfo) : null
  return (Number(m[1]) + (swap ? Number(swap[1]) : 0)) / 1024
}

// The files of a packed build (.lake/build/lib/lean/<path>.* and .lake/build/ir/<path>.*, never *.setup.json) that belong to the modules in `keep`; `listing` is `tar -t` of the archive.
// `keep` holds module paths as setup-source.mjs's pathOfModule writes them (a «guillemet» component is written without the guillemets, dots inside it stay: X.«c.d» is X/c.d).
// A file is <path>.<suffixes>, and a path may itself hold dots, so every dot of the last component is tried as the end of the path. That can take the files of a module X/c.d along with those
// of a module X/c (when both exist): a few files too many, never one too few.
export function membersOf(listing, keep) {
  const out = []
  for (const line of listing.split("\n")) {
    const f = line.replace(/^\.\//, "")
    const m = /^\.lake\/build\/(?:lib\/lean|ir)\/(.+)$/.exec(f)
    if (!m || f.endsWith(".setup.json")) continue
    const parts = m[1].split("/")
    const last = parts.pop()
    for (let i = last.indexOf("."); i > 0; i = last.indexOf(".", i + 1)) {
      if (keep.has([...parts, last.slice(0, i)].join("/"))) {
        out.push(f)
        break
      }
    }
  }
  return out
}

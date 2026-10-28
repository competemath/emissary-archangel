// Decides how one library is set up, from what is known before anything is built.
//   node scripts/setup-plan.mjs <key>      env MODE (auto | oneshot | staged), SHARDS (0 = chosen here)
// Prints the plan as `name=value` lines (written to $GITHUB_OUTPUT by .github/workflows/setup-auto.yml).
//
//   oneshot  the whole setup in one job (.github/workflows/setup-libraries.yml): build, closures, exports, bank.
//   staged   .github/workflows/setup-sharded.yml: the build alone first, as many 5-hour rounds as it takes, each
//            carrying on from the last; then the exports, split across runners. Whether one round was enough is
//            not guessed here: the workflow looks at the build after every round (--phase build-status).
//
// The size of a build cannot be read off a library: complexitylib (26,785 entries) took 69 minutes in one job and physlib (10,589)
// 256. What the 94 libraries set up in one job do show is that 79 have at most 3,000 entries and none of those took more than 142 of
// the job's 350 minutes, so that is the line: at or under it one job is the cheaper route, over it the work is staged, where a
// library that turns out to be quick costs one extra round and a slow one still gets there.
import { existsSync, readFileSync } from "node:fs"
import { dirname, join, resolve } from "node:path"
import { fileURLToPath } from "node:url"

export const ONE_SHOT_MAX_ENTRIES = 3000
export const ENTRIES_PER_SHARD = 750
export const MAX_SHARDS = 64
export const MODES = ["auto", "oneshot", "staged"]

export function decide({ entries, mode = "auto", shards = 0 }) {
  if (!MODES.includes(mode)) throw new Error(`mode is ${MODES.join(", ")}, not ${mode}`)
  if (!Number.isInteger(entries) || entries < 0) throw new Error(`entries must be a count, not ${entries}`)
  if (!Number.isInteger(shards) || shards < 0 || shards > MAX_SHARDS) throw new Error(`shards is 0 (chosen here) to ${MAX_SHARDS}, not ${shards}`)
  const route = mode !== "auto" ? mode : entries <= ONE_SHOT_MAX_ENTRIES ? "oneshot" : "staged"
  const why =
    mode !== "auto"
      ? `mode ${mode} was asked for`
      : route === "oneshot"
        ? `${entries} entries is at most ${ONE_SHOT_MAX_ENTRIES}: one job is enough`
        : `${entries} entries is over ${ONE_SHOT_MAX_ENTRIES}: build first, then split the exports`
  return {
    route,
    shards: shards || Math.min(MAX_SHARDS, Math.max(2, Math.ceil(entries / ENTRIES_PER_SHARD))),
    // tens of thousands of tiny modules (flt-anthropic) want several modules per notation-expansion process
    expand_chunk: entries > 20000 ? 8 : 1,
    prime_minutes: 300,
    max_build_rounds: 6,
    max_rounds: 4,
    why,
  }
}

// Whether a build round did anything. The staged setup builds in rounds of at most 5 hours, each carrying on from the one before (.github/workflows/setup-sharded.yml); after a round the
// build-gate job dispatches the next while the build is incomplete. For flt-anthropic (30,662 modules) three rounds in a row exported nothing and nothing noticed: a person found it by
// reading the logs. So a round (not the first) that built fewer than `min` modules more than the round before it ends the chain instead of dispatching another.
//   round   1-based number of the round that just finished
//   prev    modules with an .olean after the round before it (null / "" when unknown: the first round, or a chain started by hand)
//   built   modules with an .olean after this round
//   min     modules a round must add (default 1: any progress; 0 turns the stop off)
// The shell of the build-gate job does the same arithmetic (it checks nothing out and runs no node); scripts/test-setup-workflows.mjs runs that shell against this function on random numbers.
export const MIN_PROGRESS_DEFAULT = 1
const count = (v, what) => {
  if (!Number.isInteger(v) || v < 0) throw new Error(`${what} must be a count, not ${v}`)
  return v
}
export function roundProgress({ round, prev = null, built, min = MIN_PROGRESS_DEFAULT }) {
  if (!Number.isInteger(round) || round < 1) throw new Error(`round is 1 or more, not ${round}`)
  count(built, "built")
  count(min, "min")
  if (round === 1) return { stop: false, added: null, why: "the first round has no round before it" }
  if (prev === null || prev === undefined || prev === "") return { stop: false, added: null, why: "the round before it left no count: nothing to compare with" }
  const added = built - count(prev, "prev")
  if (added < min) return { stop: true, added, why: `round ${round} added ${added} modules (${prev} -> ${built}), fewer than ${min}` }
  return { stop: false, added, why: `round ${round} added ${added} modules (${prev} -> ${built})` }
}

// Entries the setup will seed: the committed queue when there is one, else the tentative records of the tree.
export function countEntries(root, key, tentativeDir) {
  const queue = join(root, "data", `queue-${key}.json`)
  if (existsSync(queue)) return JSON.parse(readFileSync(queue, "utf8")).length
  const src = JSON.parse(readFileSync(join(root, "sources.json"), "utf8")).sources[key]
  const files = src.tentative || [`${key}.jsonl`]
  let n = 0
  for (const f of files) {
    const p = join(tentativeDir, f)
    if (!existsSync(p)) throw new Error(`no tentative file ${p}: the tree has no records for ${key}`)
    n += readFileSync(p, "utf8").split("\n").filter((l) => l.trim()).length
  }
  return n
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..")
  const key = process.argv[2]
  if (!key || !/^[a-z0-9][a-z0-9-]*$/.test(key)) throw new Error("usage: setup-plan.mjs <key> (a key of sources.json)")
  if (!JSON.parse(readFileSync(join(root, "sources.json"), "utf8")).sources[key]) throw new Error(`unknown source ${key}`)
  const tentativeDir = process.env.EMISSARY_TENTATIVE_DIR || join(root, "tengoku", "data", "tentative")
  const entries = countEntries(root, key, tentativeDir)
  const plan = decide({ entries, mode: process.env.MODE || "auto", shards: Number(process.env.SHARDS || 0) })
  for (const [k, v] of Object.entries({ entries, ...plan })) console.log(`${k}=${v}`)
}

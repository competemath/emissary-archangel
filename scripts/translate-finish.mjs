// Fold one cloud translation run's shard outputs into the library's state, committed in this repository:
//   data/translate/<key>.jsonl              the ledger: one line per entry outcome, every run appended (queue-server.mjs
//                                           reads it to skip what is settled)
//   data/translate/<key>.prefix-cache.json  the bridge's per-file prefix cache (the newest entry per file wins)
//   data/bank/<key>/<run>.jsonl             verified staging records not yet sent as a tengoku PR (bank-flush.mjs)
//   data/translate/<key>.status.json        per mode, the last run: what it selected and how much is left for that mode
//                                           (translate-all.yml stops dispatching a mode once nothing is left)
//
//   node scripts/translate-finish.mjs <key> <run id> <dir holding one sub-directory per shard> [mode] [agent attempts]
import { appendFileSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs"
import { join } from "node:path"

const [key, run, dir, mode = "mechanical", attemptsArg = "1"] = process.argv.slice(2)
if (!key || !run || !dir) {
  console.error("usage: translate-finish.mjs <key> <run id> <dir>")
  process.exit(2)
}
const ROOT = new URL("..", import.meta.url).pathname
const lines = (f) => (existsSync(f) ? readFileSync(f, "utf8").split("\n").filter((l) => l.trim()) : [])

const shards = readdirSync(dir, { withFileTypes: true }).filter((d) => d.isDirectory()).map((d) => join(dir, d.name))
const results = shards.flatMap((s) => lines(join(s, "results.jsonl")))
const bank = new Map()
for (const s of shards) for (const l of lines(join(s, "bank.jsonl"))) {
  const r = JSON.parse(l)
  if (!bank.has(r.name)) bank.set(r.name, l)
}

const tdir = join(ROOT, "data", "translate")
mkdirSync(tdir, { recursive: true })
if (results.length) appendFileSync(join(tdir, `${key}.jsonl`), results.map((l) => JSON.stringify({ ...JSON.parse(l), run })).join("\n") + "\n")

const cachePath = join(tdir, `${key}.prefix-cache.json`)
const cache = existsSync(cachePath) ? JSON.parse(readFileSync(cachePath, "utf8")) : {}
let cacheChanged = 0
for (const s of shards) {
  const f = join(s, "prefix-cache.json")
  if (!existsSync(f)) continue
  for (const [path, v] of Object.entries(JSON.parse(readFileSync(f, "utf8")))) {
    const cur = cache[path]
    if (!cur || String(v?.checkedAt || "") > String(cur?.checkedAt || "")) {
      cache[path] = v
      cacheChanged++
    }
  }
}
if (cacheChanged) writeFileSync(cachePath, JSON.stringify(cache, null, 2) + "\n")

if (bank.size) {
  const bdir = join(ROOT, "data", "bank", key)
  mkdirSync(bdir, { recursive: true })
  writeFileSync(join(bdir, `${run}.jsonl`), [...bank.values()].join("\n") + "\n")
}

const outcomes = {}
for (const l of results) {
  const o = JSON.parse(l).outcome
  outcomes[o] = (outcomes[o] || 0) + 1
}

// What is left for this mode: the entries the run selected that a run in the same mode would select again (the same
// rules as queue-server.mjs `settled`), plus any it never reached (a shard that timed out, a crash).
const plans = shards.map((s) => join(s, "plan.json")).filter(existsSync).map((f) => JSON.parse(readFileSync(f, "utf8")))
const todo = plans.reduce((n, p) => n + p.todo, 0)
const limited = plans.some((p) => p.limited)
const done = new Set(["mechanical", "cached-mechanical", "agentic", "bump", "untranslatable", "unbankable", "export-unavailable"])
if (mode === "mechanical") done.add("deferred-agent").add("unresolved")
const tries = new Map()
for (const l of lines(join(tdir, `${key}.jsonl`))) {
  const r = JSON.parse(l)
  if (r.outcome === "unresolved") tries.set(r.id, (tries.get(r.id) || 0) + 1)
}
const settledNow = results.filter((l) => {
  const r = JSON.parse(l)
  return done.has(r.outcome) || (r.outcome === "unresolved" && (tries.get(r.id) || 0) >= Number(attemptsArg))
}).length
const left = Math.max(0, todo - settledNow)
const statusPath = join(tdir, `${key}.status.json`)
const status = existsSync(statusPath) ? JSON.parse(readFileSync(statusPath, "utf8")) : {}
// consecutive runs that settled nothing though work was left (services that never came up, a library that always
// times out): translate-all.yml stops dispatching the mode after three
const stalls = left > 0 && settledNow === 0 ? (status[mode]?.stalls || 0) + 1 : 0
status[mode] = { run, at: new Date().toISOString(), shards: shards.length, todo, processed: results.length, left, limited, stalls, outcomes }
writeFileSync(statusPath, JSON.stringify(status, null, 2) + "\n")
console.log(`${key} run ${run} (${mode}): ${shards.length} shards, ${todo} selected, ${results.length} processed ${JSON.stringify(outcomes)}, ${left} left${limited ? " (limited run)" : ""}, ${bank.size} records banked, ${cacheChanged} prefix-cache entries updated`)

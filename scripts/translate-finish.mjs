// Fold one cloud translation run's shard outputs into the library's state, committed in this repository:
//   data/translate/<key>.jsonl              the ledger: one line per entry outcome, every run appended (queue-server.mjs
//                                           reads it to skip what is settled)
//   data/translate/<key>.prefix-cache.json  the bridge's per-file prefix cache (the newest entry per file wins)
//   data/bank/<key>/<run>.jsonl             verified staging records not yet sent as a tengoku PR (bank-flush.mjs)
//
//   node scripts/translate-finish.mjs <key> <run id> <dir holding one sub-directory per shard>
import { appendFileSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs"
import { join } from "node:path"

const [key, run, dir] = process.argv.slice(2)
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
console.log(`${key} run ${run}: ${shards.length} shards, ${results.length} entries ${JSON.stringify(outcomes)}, ${bank.size} records banked, ${cacheChanged} prefix-cache entries updated`)

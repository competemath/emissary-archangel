// A headless stand-in for the app's /api/queue, for translation runs without the Next.js app (the cloud).
//
//   node scripts/queue-server.mjs --source <key> --bank <file> [--port 3000] [--shard i/N] [--limit M]
//        [--tree <tengoku checkout>] [--ledger data/translate/<key>.jsonl] [--mode mechanical|agent] [--agent-attempts 1]
//        [--plan <file>]  (writes what this run selected, for translate-finish.mjs)
//
//   GET   /api/queue?source=<key>  this run's entries: pending, in the shard, not already on the tree's main, and
//                                   not settled by the ledger (see `settled`)
//   PATCH /api/queue?source=<key>  {id, ...}: merged into the entry; on status "verified" its staging record
//                                   (lib/stage-record.mjs, the same one the app banks) is appended to --bank
//
// The shard is a hash of the source file, so every entry of one file runs in the same job (the bridge's prefix cache
// is per file). The server owns its entries alone: no lock, no queue file writes; the ledger and the bank are the
// run's outputs.
import { createServer } from "node:http"
import { appendFileSync, existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs"
import { join } from "node:path"
import { stagingRecord } from "../lib/stage-record.mjs"

const argv = process.argv.slice(2)
const opt = (name, dflt = null) => {
  const i = argv.indexOf(`--${name}`)
  return i >= 0 ? argv[i + 1] : dflt
}
const SOURCE = opt("source")
const BANK = opt("bank")
if (!SOURCE || !BANK) {
  console.error("usage: queue-server.mjs --source <key> --bank <file> [--port 3000] [--shard i/N] [--limit M] [--tree dir] [--ledger file] [--mode mechanical|agent]")
  process.exit(2)
}
const ROOT = new URL("..", import.meta.url).pathname
const PORT = Number(opt("port", "3000"))
const [SHARD, SHARDS] = (opt("shard", "0/1")).split("/").map(Number)
const LIMIT = Number(opt("limit", "0")) || Infinity
const TREE = opt("tree")
const LEDGER = opt("ledger")
const MODE = opt("mode", "agent")
const AGENT_ATTEMPTS = Number(opt("agent-attempts", "1"))
const PLAN = opt("plan")

const sources = JSON.parse(readFileSync(join(ROOT, "sources.json"), "utf8"))
const spec = sources.sources[SOURCE]
if (!spec) throw new Error(`unknown source ${SOURCE}`)
const toolchain = spec.targetToolchain || sources.targetToolchain
const queuePath = join(ROOT, "data", spec.queueFile || `queue-${SOURCE}.json`)

// FNV-1a, 32 bit: a stable shard for a source file
const fnv = (s) => {
  let h = 0x811c9dc5
  for (const c of Buffer.from(s)) h = Math.imul(h ^ c, 0x01000193) >>> 0
  return h
}

// Names already on the tree's main for this library (staging, per-PR staging files, trusted): banking one again would
// be a duplicate declaration (lib/tengoku-pr.ts existingNames, same files).
function treeNames() {
  const names = new Set()
  if (!TREE) return names
  const files = [join(TREE, "data", "staging", `${SOURCE}.jsonl`), join(TREE, "data", "trusted", `${SOURCE}.jsonl`)]
  const nested = join(TREE, "data", "staging", SOURCE)
  if (existsSync(nested)) for (const f of readdirSync(nested)) if (f.endsWith(".jsonl")) files.push(join(nested, f))
  for (const f of files) {
    if (!existsSync(f)) continue
    for (const line of readFileSync(f, "utf8").split("\n")) {
      if (!line.trim()) continue
      try {
        const r = JSON.parse(line)
        if (typeof r.name === "string") names.add(r.name)
      } catch {
        /* the gate's problem, not ours */
      }
    }
  }
  return names
}

// The ledger: every outcome of every earlier run, one line each. An entry is settled when its latest outcome says there
// is nothing more to do in this mode.
const VERIFIED = new Set(["mechanical", "cached-mechanical", "agentic", "bump"]) // bump: scripts/bump/ (whole-library build + batched Gate 2)
const TERMINAL = new Set(["untranslatable", "unbankable", "export-unavailable"])
function ledger() {
  const last = new Map()
  const agentTries = new Map()
  if (LEDGER && existsSync(LEDGER)) {
    for (const line of readFileSync(LEDGER, "utf8").split("\n")) {
      if (!line.trim()) continue
      const r = JSON.parse(line)
      last.set(r.id, r.outcome)
      if (r.outcome === "unresolved") agentTries.set(r.id, (agentTries.get(r.id) || 0) + 1)
    }
  }
  return { last, agentTries }
}
function settled(id, { last, agentTries }) {
  const o = last.get(id)
  if (!o) return false
  if (VERIFIED.has(o) || TERMINAL.has(o)) return true
  if (o === "deferred-agent") return MODE === "mechanical" // known to need the agent: only an agent run takes it
  if (o === "unresolved") return MODE === "mechanical" || (agentTries.get(id) || 0) >= AGENT_ATTEMPTS
  return false // infra-blocked, failed: try again
}

const queue = JSON.parse(readFileSync(queuePath, "utf8"))
const onTree = treeNames()
const led = ledger()
const counts = { pending: 0, otherShards: 0, onTree: 0, settled: 0 }
const mine = queue
  .filter((e) => e.status === "pending" && typeof e.sourcePath === "string" && typeof e.sourceLine === "number")
  .filter((e) => (counts.pending++, fnv(e.sourcePath) % SHARDS === SHARD || (counts.otherShards++, false)))
  .filter((e) => !onTree.has(String(e.name ?? e.id)) || (counts.onTree++, false))
  .filter((e) => !settled(e.id, led) || (counts.settled++, false))
  .sort((a, b) => a.sourcePath.localeCompare(b.sourcePath) || a.sourceLine - b.sourceLine)
  .slice(0, LIMIT)
const byId = new Map(mine.map((e) => [e.id, e]))
if (PLAN) writeFileSync(PLAN, JSON.stringify({ todo: mine.length, limited: mine.length === LIMIT, ...counts }) + "\n")
console.log(`queue-server ${SOURCE} shard ${SHARD}/${SHARDS} (${MODE}): ${mine.length} to do — of ${counts.pending} pending, ${counts.otherShards} in other shards, ${counts.onTree} already on the tree, ${counts.settled} settled by the ledger`)

const reply = (res, code, obj) => {
  res.writeHead(code, { "content-type": "application/json" })
  res.end(JSON.stringify(obj))
}
createServer(async (req, res) => {
  const url = new URL(req.url, "http://localhost")
  if (url.pathname !== "/api/queue") return reply(res, 404, { error: "not_found" })
  if (url.searchParams.get("source") !== SOURCE) return reply(res, 400, { error: "unknown_source", detail: url.searchParams.get("source") })
  if (req.method === "GET") return reply(res, 200, mine)
  if (req.method === "PATCH") {
    const chunks = []
    for await (const c of req) chunks.push(c)
    const body = Buffer.concat(chunks).toString("utf8") // decoded once: a chunk boundary can split a character
    const update = JSON.parse(body || "{}")
    const entry = byId.get(update.id)
    if (!entry) return reply(res, 404, { error: "not_found" })
    Object.assign(entry, update)
    let staging
    if (update.status === "verified") {
      const built = stagingRecord(SOURCE, entry, toolchain)
      if (built.record) {
        appendFileSync(BANK, JSON.stringify(built.record) + "\n")
        staging = { staged: true, detail: `banked to ${BANK}` }
      } else staging = { staged: false, detail: built.error }
      console.log(`queue-server: #${entry.id} ${entry.name} verified — ${staging.detail}`)
    }
    return reply(res, 200, { ...entry, ...(staging ? { staging } : {}) })
  }
  return reply(res, 405, { error: "method_not_allowed" })
}).listen(PORT, "127.0.0.1", () => console.log(`queue-server listening on 127.0.0.1:${PORT}`))

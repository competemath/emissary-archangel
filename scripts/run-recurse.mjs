// Drive the recursion engine on a private bridge instance and log its stream.
//   node run-recurse.mjs <bridgePort> <token> [scopeJson]
import { appendFileSync, writeFileSync } from "node:fs"
const [port, token, scopeArg] = process.argv.slice(2)
const scope = scopeArg ? JSON.parse(scopeArg) : { type: "all" }
// Every service runs on the local Tengoku tree (Tengoku.All): no Mathlib anywhere.
const LEAK_IV = "http://127.0.0.1:7871/sse"
const LEAK_I = "http://127.0.0.1:7874/sse"
const ARCHANGEL = "http://127.0.0.1:7872/sse"
const LOG = new URL("../recurse-run.log", import.meta.url).pathname

const ts = () => new Date().toISOString().slice(11, 19)
const log = (line) => {
  const s = `[${ts()}] ${line}`
  console.log(s)
  appendFileSync(LOG, s + "\n")
}
writeFileSync(LOG, "")

// Leak I is optional: include it only if it answers tools/list within 20s.
async function reachable(sseUrl) {
  try {
    const res = await fetch(sseUrl, { headers: { Accept: "text/event-stream" }, signal: AbortSignal.timeout(20000) })
    const ok = res.ok && /text\/event-stream/.test(res.headers.get("content-type") || "")
    res.body?.cancel?.()
    return ok
  } catch {
    return false
  }
}
const mcpServers = [
  { id: "leak-iv", name: "Leak_IV", url: LEAK_IV, isActive: true },
  { id: "archangel", name: "Archangel_Emissary_0_0_1", url: ARCHANGEL, isActive: true },
]
if (await reachable(LEAK_I)) mcpServers.push({ id: "leak-i", name: "Leak_I", url: LEAK_I, isActive: true })
log(`servers: ${mcpServers.map((s) => s.name).join(", ")} | scope ${JSON.stringify(scope)}`)

const res = await fetch(`http://127.0.0.1:${port}/archangel-recurse`, {
  method: "POST",
  headers: { "content-type": "application/json", "x-bridge-token": token, Origin: "http://localhost:3000" },
  body: JSON.stringify({ source: "equational-theories", scope, archangelUrl: ARCHANGEL, verifyUrl: LEAK_IV, mcpServers, timeoutMs: 20 * 60 * 1000 }),
})
if (!res.ok || !res.body) {
  log(`HTTP ${res.status}: ${await res.text()}`)
  process.exit(1)
}
const reader = res.body.getReader()
const dec = new TextDecoder()
let buf = ""
for (;;) {
  const { done, value } = await reader.read()
  if (done) break
  buf += dec.decode(value, { stream: true })
  const chunks = buf.split("\n\n")
  buf = chunks.pop() || ""
  for (const chunk of chunks) {
    const line = chunk.split("\n").find((l) => l.startsWith("data: "))
    if (!line) continue
    let o
    try { o = JSON.parse(line.slice(6)) } catch { continue }
    if (o.type === "progress" || o.type === "done") log(`${o.type.toUpperCase()} ${o.processed}/${o.total} ${JSON.stringify(o.summary)}`)
    else if (o.type === "message-annotation") {
      const t = String(o.thought || "").replace(/\s+/g, " ")
      if (o.subtype === "tool_intent") log(`  → ${o.tool} ${String(o.input || "").slice(0, 160)}`)
      else if (o.subtype === "tool_result") log(`  ← ${String(o.output || "").replace(/\s+/g, " ").slice(0, 400)}`)
      else if (!/^⏳/.test(t)) log(`${t.slice(0, 600)}`)
    } else if (o.type === "error") log(`ERROR ${o.message}`)
  }
}
log("stream ended")

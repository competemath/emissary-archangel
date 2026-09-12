// Exercise the local Tengoku verifier (Leak IV on the tree) on the tree (default :7871).
const URL_ = process.argv[2] || "http://127.0.0.1:7871/sse"
async function mcp(sseUrl) {
  const res = await fetch(sseUrl, { headers: { Accept: "text/event-stream" } })
  const reader = res.body.getReader()
  const dec = new TextDecoder()
  let buf = "", postUrl = null, nextId = 1
  const pending = new Map()
  const origin = new URL(sseUrl).origin
  ;(async () => {
    for (;;) {
      const { done, value } = await reader.read()
      if (done) break
      buf += dec.decode(value, { stream: true }).replace(/\r\n/g, "\n")
      let idx
      while ((idx = buf.indexOf("\n\n")) !== -1) {
        const chunk = buf.slice(0, idx); buf = buf.slice(idx + 2)
        let evt = "message", lines = []
        for (const l of chunk.split("\n")) { if (l.startsWith("event:")) evt = l.slice(6).trim(); else if (l.startsWith("data:")) lines.push(l.slice(5).trimStart()) }
        if (!lines.length) continue
        const data = lines.join("\n")
        if (evt === "endpoint") { postUrl = new URL(data, origin).toString(); continue }
        try { const m = JSON.parse(data); if (m.id != null && pending.has(m.id)) { pending.get(m.id)(m); pending.delete(m.id) } } catch {}
      }
    }
  })().catch(() => {})
  const rpc = async (method, params, timeoutMs = 300000) => {
    const t0 = Date.now()
    while (!postUrl) { if (Date.now() - t0 > 20000) throw new Error("no endpoint"); await new Promise((r) => setTimeout(r, 50)) }
    const id = nextId++
    const p = new Promise((resolve, reject) => { pending.set(id, resolve); setTimeout(() => reject(new Error("rpc timeout")), timeoutMs) })
    await fetch(postUrl, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ jsonrpc: "2.0", id, method, params }) })
    return p
  }
  await rpc("initialize", { protocolVersion: "2024-11-05", capabilities: {}, clientInfo: { name: "verifier-test", version: "0" } })
  return { rpc, close: () => reader.cancel().catch(() => {}) }
}
const c = await mcp(URL_)
const tools = (await c.rpc("tools/list", {})).result?.tools?.map((t) => t.name)
console.log("tools:", tools)
const script = `open EquationalTheories in
theorem test_Equation3715_implies_Equation4470 (G : Type*) [Magma G] (h : Equation3715 G) : Equation4470 G := fun x y =>
  Eq.trans (Eq.trans (h x (Magma.op y y)) (congrArg₂ Magma.op (h x x) (Eq.symm (h y y)))) (Eq.symm (h (Magma.op x x) y))`
let t0 = Date.now()
const r1 = await c.rpc("tools/call", { name: "verify_full_script", arguments: { script } })
const text1 = r1.result?.content?.[0]?.text || JSON.stringify(r1)
console.log(`[${/100% verified/.test(text1) ? "OK " : "BAD"}] MagmaEgg theorem against the tree's own Equation abbrevs (${Math.round((Date.now() - t0) / 1000)}s) — ${text1.replace(/\s+/g, " ").slice(0, 300)}`)
t0 = Date.now()
const r2 = await c.rpc("tools/call", { name: "verify_full_script", arguments: { script: "theorem oops : (1 : Nat) = 2 := rfl" } })
const text2 = r2.result?.content?.[0]?.text || JSON.stringify(r2)
console.log(`[${/❌/.test(text2) ? "OK " : "BAD"}] a false theorem is rejected (${Math.round((Date.now() - t0) / 1000)}s) — ${text2.replace(/\s+/g, " ").slice(0, 200)}`)
t0 = Date.now()
const r3 = await c.rpc("tools/call", { name: "verify_full_script", arguments: { script: "import Mathlib\n\ntheorem legacy : 1 + 1 = 2 := rfl" } })
const text3 = r3.result?.content?.[0]?.text || JSON.stringify(r3)
console.log(`[${/100% verified/.test(text3) && /aW1wb3J0IFRlbmdva3U/.test(text3) ? "OK " : "BAD"}] legacy 'import Mathlib' is rewritten to the tree root (${Math.round((Date.now() - t0) / 1000)}s) — ${text3.replace(/\s+/g, " ").slice(0, 160)}`)
c.close()
process.exit(0)

// Which entries of a library a run still has to do, read from the ledger (data/translate/<key>.jsonl: every outcome of every earlier run, one line each).
// scripts/queue-server.mjs asks this; it was inline there, and is here so that the rules can be tested.
//
// An entry is SETTLED when its latest outcome says there is nothing more to do in this mode:
//   verified or terminal outcomes             always
//   deferred-agent, in a mechanical run       only when the mechanical pass that gave up on it was the current one (row.mechanics >= the version asked for). A row from before the
//                                             mechanics were stamped, or from an older generation, is not settled: the remedies have changed since, so the entry is tried again.
//                                             In an agent run a deferred-agent entry is exactly what the run is for.
//   unresolved                                mechanical runs leave it; an agent run takes it until it has had its attempts
//   infra-blocked, failed, anything else      tried again

export const VERIFIED = new Set(["mechanical", "cached-mechanical", "agentic", "bump"]) // bump: scripts/bump/ (whole-library build + batched Gate 2)
export const TERMINAL = new Set(["untranslatable", "unbankable", "export-unavailable"])

export function parseLedger(text) {
  const last = new Map()
  const mechanics = new Map()
  const agentTries = new Map()
  for (const line of String(text || "").split("\n")) {
    if (!line.trim()) continue
    let r
    try {
      r = JSON.parse(line)
    } catch {
      continue // a half-written last line must not stop a run
    }
    last.set(r.id, r.outcome)
    if (r.outcome === "deferred-agent") mechanics.set(r.id, Number.isInteger(r.mechanics) ? r.mechanics : 0)
    else mechanics.delete(r.id)
    if (r.outcome === "unresolved") agentTries.set(r.id, (agentTries.get(r.id) || 0) + 1)
  }
  return { last, mechanics, agentTries }
}

export function isSettled(id, led, { mode, agentAttempts = 1, mechanicsVersion }) {
  const o = led.last.get(id)
  if (!o) return false
  if (VERIFIED.has(o) || TERMINAL.has(o)) return true
  if (o === "deferred-agent") return mode === "mechanical" && (led.mechanics.get(id) ?? 0) >= mechanicsVersion
  if (o === "unresolved") return mode === "mechanical" || (led.agentTries.get(id) || 0) >= agentAttempts
  return false // infra-blocked, failed: try again
}

// Intake of nominated Leak memory into Tengoku. Pure functions plus a Leak IV client and the agent audit; scripts/memory-intake.mjs is the command line.
// A bundle (memory-intake/bundle.schema.json) passes three stages before anything is staged: preflight (shape, banned constructs, Leak IV compile),
// the agent audit (ten clean-room reviewers, rubrics in lib/memory-intake-rubrics.mjs) and, after staging in the sandbox, Jinshi on the nominated modules.
import { createHash } from "node:crypto"
import { spawn } from "node:child_process"
import { mkdtempSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join } from "node:path"
import { stagingRecord } from "./stage-record.mjs"
import { RUBRICS } from "./memory-intake-rubrics.mjs"

export const MIN_NOMINATED = 3
export const MAX_NOMINATED = 10
export const SCHEMA = "leak-memory-bundle/1"

const sha = (s) => createHash("sha256").update(s).digest("hex")
const stripComments = (s) => s.replace(/\/-[\s\S]*?-\//g, "").replace(/--.*$/gm, "")

export function validateBundle(b) {
  const errors = []
  if (!b || typeof b !== "object") return { ok: false, errors: ["not an object"] }
  if (b.schema !== SCHEMA) errors.push(`schema must be ${SCHEMA}`)
  if (!/^[a-z0-9][a-z0-9-]{1,62}$/.test(b.target?.id ?? "")) errors.push("target.id must be a lowercase slug")
  if (typeof b.target?.statement !== "string" || !b.target.statement.trim()) errors.push("target.statement is required")
  if (typeof b.author !== "string" || !b.author.trim()) errors.push("author is required (it is the attribution on every record)")
  if (!Array.isArray(b.entries)) errors.push("entries must be a list")
  else {
    if (b.entries.length < MIN_NOMINATED || b.entries.length > MAX_NOMINATED) errors.push(`nominate ${MIN_NOMINATED} to ${MAX_NOMINATED} theorems (got ${b.entries.length})`)
    const seen = new Set()
    for (const [i, e] of b.entries.entries()) {
      const at = `entries[${i}]`
      if (!/^[0-9a-f]{8,64}$/.test(e?.id ?? "")) errors.push(`${at}.id must be a hex hash`)
      if (typeof e?.name !== "string" || !/^[A-Za-z_][\w.'!?]*$/.test(e.name)) errors.push(`${at}.name must be a Lean identifier`)
      if (typeof e?.closure !== "string" || !e.closure.trim()) errors.push(`${at}.closure is required`)
      if (typeof e?.statement !== "string" || !e.statement.trim()) errors.push(`${at}.statement is required`)
      if (e?.origin === "seed") errors.push(`${at} is a seed lemma of the target (not something the run proved), so it cannot be nominated`)
      if (e?.id && seen.has(e.id)) errors.push(`${at} repeats id ${e.id}`)
      seen.add(e?.id)
    }
  }
  return { ok: errors.length === 0, errors }
}

// Constructs that make a compiled proof mean less than it looks, or that have no place in a library theorem.
const BANNED = [
  [/\bsorry\b|\badmit\b/, "contains sorry/admit"],
  [/\bnative_decide\b/, "uses native_decide (trusts the compiler, not the kernel)"],
  [/^\s*(?:unsafe|partial)\b/m, "unsafe/partial declaration"],
  [/^\s*axiom\b|\bopaque\b/m, "declares an axiom or opaque constant"],
  [/@\[\s*(?:implemented_by|extern|csimp)\b/, "implemented_by/extern/csimp attribute"],
  [/^\s*import\b/m, "import line (the tree supplies the root import)"],
  [/^\s*#(?:eval|print|check|reduce|exit)\b/m, "leftover command (#eval, #print, #check, #reduce, #exit)"],
  [/\bset_option\s+(?:maxHeartbeats\s+0|maxRecDepth\s+\d{5,})/, "lifts a resource limit"],
]
export function scanScript(closure) {
  const body = stripComments(closure)
  return BANNED.filter(([re]) => re.test(body)).map(([, why]) => why)
}

export const bundleId = (b) => sha(`${b.target.id}\n${b.entries.map((e) => e.id).sort().join("\n")}`).slice(0, 12)

// Minimal MCP-over-SSE client, the same protocol scripts/leak-iv-test.mjs speaks.
export async function mcpCall(sseUrl, tool, args, timeoutMs = 300000) {
  const ac = new AbortController()
  const res = await fetch(sseUrl, { headers: { Accept: "text/event-stream" }, signal: ac.signal })
  const reader = res.body.getReader()
  const dec = new TextDecoder()
  let buf = "", post = null, next = 1
  const pending = new Map()
  const origin = new URL(sseUrl).origin
  ;(async () => {
    for (;;) {
      const { done, value } = await reader.read().catch(() => ({ done: true }))
      if (done) return
      buf += dec.decode(value, { stream: true }).replace(/\r\n/g, "\n")
      let i
      while ((i = buf.indexOf("\n\n")) >= 0) {
        const chunk = buf.slice(0, i)
        buf = buf.slice(i + 2)
        let evt = "message"
        const lines = []
        for (const l of chunk.split("\n")) {
          if (l.startsWith("event:")) evt = l.slice(6).trim()
          else if (l.startsWith("data:")) lines.push(l.slice(5).trimStart())
        }
        if (!lines.length) continue
        const data = lines.join("\n")
        if (evt === "endpoint") post = new URL(data, origin).toString()
        else
          try {
            const m = JSON.parse(data)
            pending.get(m.id)?.(m)
          } catch {}
      }
    }
  })()
  const rpc = async (method, params) => {
    for (let t = 0; !post && t < 400; t++) await new Promise((r) => setTimeout(r, 50))
    if (!post) throw new Error("no endpoint")
    const id = next++
    const p = new Promise((resolve, reject) => {
      pending.set(id, resolve)
      setTimeout(() => reject(new Error("rpc timeout")), timeoutMs)
    })
    await fetch(post, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ jsonrpc: "2.0", id, method, params }) })
    return p
  }
  try {
    await rpc("initialize", { protocolVersion: "2024-11-05", capabilities: {}, clientInfo: { name: "memory-intake", version: "0" } })
    const r = await rpc("tools/call", { name: tool, arguments: args })
    return r.result?.content?.map((c) => c.text ?? "").join("\n") ?? JSON.stringify(r)
  } finally {
    ac.abort()
  }
}

export const compiles = (text) => /100% verified|Compilation Successful/.test(text) && !/Compilation Failed|❌/.test(text)

// Stage 1. Never throws on a bad entry: every problem is a line in the report, and `ok` is true only when there are none.
export async function preflight(bundle, { leakIvUrl, verify = (script) => mcpCall(leakIvUrl, "verify_full_script", { script }) } = {}) {
  const shape = validateBundle(bundle)
  const report = { stage: "preflight", bundle: shape.ok ? bundleId(bundle) : null, ok: false, errors: [...shape.errors], entries: [] }
  if (!shape.ok) return report
  const names = new Set()
  for (const e of bundle.entries) {
    const row = { id: e.id, name: e.name, problems: [] }
    if (names.has(e.name)) row.problems.push("name repeats within the bundle")
    names.add(e.name)
    row.problems.push(...scanScript(e.closure))
    if (!row.problems.length) {
      try {
        const text = await verify(e.closure)
        row.compiled = compiles(text)
        if (!row.compiled) row.problems.push(`does not compile on Leak IV: ${String(text).replace(/\s+/g, " ").slice(0, 200)}`)
      } catch (err) {
        row.problems.push(`Leak IV unreachable: ${String(err?.message ?? err).slice(0, 120)}`)
      }
    }
    report.entries.push(row)
  }
  report.ok = report.entries.every((r) => r.problems.length === 0)
  return report
}

// The reviewers' verdicts → the bundle's. Any blocking reviewer that rejects, or any reviewer that did not return a usable verdict, fails the bundle.
export function aggregate(results) {
  const blockingFailures = []
  const unusable = []
  for (const r of results) {
    if (!r.verdict || !["approve", "reject", "concern"].includes(r.verdict.verdict)) {
      unusable.push(r.id)
      continue
    }
    if (r.blocking && r.verdict.verdict === "reject") blockingFailures.push(r.id)
  }
  return { pass: blockingFailures.length === 0 && unusable.length === 0, blockingFailures, unusable }
}

const reviewerPrompt = (rubric, files) =>
  `You are one of ten independent reviewers of Lean 4 theorems that are proposed for the Tengoku library. You see only these files and your own rubric. Do not run anything; read the files and judge.

FILES (in the current directory): ${files.join(", ")}. bundle.json has the target, the author and every nominated theorem with the helper declarations it needs; entries/ has each as a .lean file.

YOUR RUBRIC: ${rubric.id}${rubric.blocking ? " (a reject from you blocks the bundle)" : " (advisory)"}
${rubric.prompt}

Be exact and sparing. A finding needs the entry name, what is wrong, how to fix it, and the evidence in the text. Do not flag things for the sake of it. Prefer "approve" when the rubric is met.

Reply with ONE JSON object and nothing else:
{"verdict":"approve"|"concern"|"reject","summary":"one or two sentences","findings":[{"file":"entry name","line":null,"issue":"…","fix":"…","evidence":"…"}]}`

function parseVerdict(text) {
  const m = String(text).match(/\{[\s\S]*\}/)
  if (!m) return null
  try {
    const v = JSON.parse(m[0])
    return v && typeof v === "object" ? v : null
  } catch {
    return null
  }
}

// Stage 2. Ten clean-room reviewers, each a read-only `claude -p` over a temp directory that holds only the bundle. Reuse and placement may also be given a
// Leak I search server (`mcpConfig`) so "does Tengoku already have this" is checked, not guessed.
export async function audit(bundle, { claudeBin = process.env.CLAUDE_BIN || "claude", model, mcpConfig, concurrency = 5, timeoutMs = 600000 } = {}) {
  const dir = mkdtempSync(join(tmpdir(), "memory-intake-"))
  try {
    writeFileSync(join(dir, "bundle.json"), JSON.stringify(bundle, null, 2))
    const files = ["bundle.json"]
    for (const e of bundle.entries) {
      writeFileSync(join(dir, `${e.name.replace(/[^\w.]/g, "_")}.lean`), `${e.closure}\n`)
      files.push(`${e.name.replace(/[^\w.]/g, "_")}.lean`)
    }
    const run = (rubric) =>
      new Promise((resolve) => {
        const args = ["-p", reviewerPrompt(rubric, files), "--output-format", "json", "--allowedTools", "Read,Grep,Glob", "--disallowedTools", "Bash,Edit,Write,WebFetch,WebSearch"]
        if (model) args.push("--model", model)
        if (mcpConfig && rubric.search) args.push("--mcp-config", mcpConfig)
        let out = ""
        const child = spawn(claudeBin, args, { cwd: dir, stdio: ["ignore", "pipe", "pipe"] })
        const timer = setTimeout(() => child.kill("SIGKILL"), timeoutMs)
        child.stdout.on("data", (d) => (out += d))
        child.on("error", () => resolve({ id: rubric.id, blocking: rubric.blocking, verdict: null }))
        child.on("close", () => {
          clearTimeout(timer)
          let text = out
          try {
            const j = JSON.parse(out)
            text = typeof j.result === "string" ? j.result : out
          } catch {}
          resolve({ id: rubric.id, blocking: rubric.blocking, verdict: parseVerdict(text) })
        })
      })
    const results = []
    for (let i = 0; i < RUBRICS.length; i += concurrency) results.push(...(await Promise.all(RUBRICS.slice(i, i + concurrency).map(run))))
    return { stage: "audit", bundle: bundleId(bundle), ...aggregate(results), results }
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

const pascal = (id) => id.split("-").map((w) => w[0].toUpperCase() + w.slice(1)).join("")

// Stage 3 input. One library per target: records go to data/staging/<library>/<UTC>-NNN.jsonl, the module is Tengoku/Target/<Pascal>.lean, and the
// nomination file lists the modules Jinshi is asked to attack (it takes modules, not theorems).
export function stageBundle(bundle, { toolchain = "leanprover/lean4:v4.29.1", now = new Date() } = {}) {
  const library = `target-${bundle.target.id}`
  const records = []
  const errors = []
  for (const e of bundle.entries) {
    const r = stagingRecord(library, { name: e.name, proof: e.closure, sourcePath: `Tengoku/Target/${pascal(bundle.target.id)}.lean`, sourceUrl: `https://competemath.com/leak?target=${bundle.target.id}` }, toolchain)
    if (r.error) errors.push(`${e.name}: ${r.error}`)
    else records.push({ ...r.record, source_url: `https://competemath.com/leak?target=${bundle.target.id}`, author: bundle.author, bundle: bundleId(bundle) })
  }
  const stamp = now.toISOString().replace(/[-:]/g, "").replace(/\.\d+Z$/, "Z")
  return {
    errors,
    library,
    stagingPath: `data/staging/${library}/${stamp}-001.jsonl`,
    jsonl: records.map((r) => JSON.stringify(r)).join("\n") + (records.length ? "\n" : ""),
    registration: { key: library, label: `Target: ${bundle.target.title ?? bundle.target.id}`, kind: "target", note: "theorems verified on the way to an open target; see memory-intake/README.md" },
    jinshi: { module: `Tengoku/Target/${pascal(bundle.target.id)}.lean`, theorems: records.map((r) => r.name), count: records.length },
  }
}

// node scripts/test-memory-intake.mjs — the memory intake end to end against a stub Leak IV and a stub `claude` (exits 1 on a failure)
import { createServer } from "node:http"
import { randomBytes } from "node:crypto"
import { writeFileSync, mkdtempSync, chmodSync, readFileSync, existsSync } from "node:fs"
import { tmpdir } from "node:os"
import { join, dirname } from "node:path"
import { fileURLToPath } from "node:url"
import { spawn } from "node:child_process"
import { aggregate, audit, bundleId, preflight, scanScript, stageBundle, validateBundle } from "../lib/memory-intake.mjs"
import { RUBRICS } from "../lib/memory-intake-rubrics.mjs"

const here = dirname(fileURLToPath(import.meta.url))
let bad = 0
const check = (name, cond, extra = "") => {
  if (!cond) { bad++; console.log("FAIL", name, extra) } else console.log("ok", name)
}

// a stub Leak IV: success unless the script has `sorry` or the word BROKEN
const sessions = new Map()
const server = createServer((req, res) => {
  const url = new URL(req.url, "http://x")
  if (req.method === "GET") {
    const sid = randomBytes(5).toString("hex")
    res.writeHead(200, { "content-type": "text/event-stream" })
    sessions.set(sid, res)
    res.write(`event: endpoint\ndata: /message?sessionId=${sid}\n\n`)
    return
  }
  let body = ""
  req.on("data", (c) => (body += c))
  req.on("end", () => {
    const m = JSON.parse(body)
    res.writeHead(202).end()
    const out = sessions.get(url.searchParams.get("sessionId"))
    if (m.id == null || !out) return
    const text = m.method === "tools/call" ? (/BROKEN/.test(m.params.arguments.script) ? "❌ Compilation Failed: Line 1 (Error)" : "✅ Compilation Successful! The proof is 100% verified.") : ""
    out.write(`event: message\ndata: ${JSON.stringify({ jsonrpc: "2.0", id: m.id, result: m.method === "tools/call" ? { content: [{ type: "text", text }] } : {} })}\n\n`)
  })
})
await new Promise((r) => server.listen(0, "127.0.0.1", r))
const leakIvUrl = `http://127.0.0.1:${server.address().port}/sse`

const id = (n) => n.repeat(8).slice(0, 8)
const entry = (n, name, extra = "") => ({ id: id(n), name, statement: `theorem ${name} (a b : ℕ) : a + b = b + a`, closure: `theorem ${name} (a b : ℕ) : a + b = b + a := by\n  ${extra || "omega"}` })
const good = () => ({
  schema: "leak-memory-bundle/1",
  target: { id: "erdos-396", title: "Erdős 396", statement: "theorem erdos_396 : True := by sorry" },
  author: "hacker",
  exportedAt: "2026-10-18T00:00:00Z",
  entries: [entry("1", "add_comm_a"), entry("2", "add_comm_b"), entry("3", "add_comm_c")],
})

// shape
check("valid bundle", validateBundle(good()).ok)
check("too few entries", !validateBundle({ ...good(), entries: good().entries.slice(0, 2) }).ok)
check("too many entries", !validateBundle({ ...good(), entries: Array.from({ length: 11 }, (_, i) => entry(i.toString(16), `t${i}`)).map((e, i) => ({ ...e, id: String(i).padStart(8, "a") })) }).ok)
check("author required", !validateBundle({ ...good(), author: "" }).ok)
check("repeated id", !validateBundle({ ...good(), entries: [good().entries[0], good().entries[0], good().entries[2]] }).ok)
check("a seed lemma cannot be nominated", !validateBundle({ ...good(), entries: [{ ...good().entries[0], origin: "seed" }, ...good().entries.slice(1)] }).ok)
check("bad name", !validateBundle({ ...good(), entries: [{ ...good().entries[0], name: "not a name" }, ...good().entries.slice(1)] }).ok)

// banned constructs
check("sorry", scanScript("theorem t : True := by sorry").length === 1)
check("native_decide", scanScript("theorem t : 2 + 2 = 4 := by native_decide").length === 1)
check("a comment is not code", scanScript("-- sorry later\ntheorem t : True := trivial").length === 0)
check("axiom", scanScript("axiom bad : False").length === 1)
check("import", scanScript("import Mathlib\ntheorem t : True := trivial").length === 1)
check("clean", scanScript("theorem t (n : ℕ) : n = n := rfl").length === 0)

// preflight against the stub
const p = await preflight(good(), { leakIvUrl })
check("preflight passes a good bundle", p.ok, JSON.stringify(p))
const broken = good()
broken.entries[1].closure += "\n-- BROKEN"
const pb = await preflight(broken, { leakIvUrl })
check("preflight names the entry that does not compile", !pb.ok && pb.entries[1].problems.length === 1 && pb.entries[0].problems.length === 0)
check("bundle id ignores entry order", bundleId(good()) === bundleId({ ...good(), entries: [...good().entries].reverse() }))

// aggregation
const v = (verdict) => ({ verdict })
check("approve all passes", aggregate(RUBRICS.map((r) => ({ id: r.id, blocking: r.blocking, verdict: v("approve") }))).pass)
check("blocking reject fails", !aggregate(RUBRICS.map((r) => ({ id: r.id, blocking: r.blocking, verdict: v(r.id === "reuse" ? "reject" : "approve") }))).pass)
check("advisory reject passes", aggregate(RUBRICS.map((r) => ({ id: r.id, blocking: r.blocking, verdict: v(r.id === "naming" ? "reject" : "approve") }))).pass)
check("no verdict fails closed", !aggregate(RUBRICS.map((r) => ({ id: r.id, blocking: r.blocking, verdict: r.id === "naming" ? null : v("approve") }))).pass)
check("ten reviewers, five block", RUBRICS.length === 10 && RUBRICS.filter((r) => r.blocking).length === 5)

// the audit with a stub claude that rejects on `generality` only when asked to
const dir = mkdtempSync(join(tmpdir(), "mi-test-"))
const stub = join(dir, "claude")
writeFileSync(stub, `#!/usr/bin/env node
const p = process.argv[process.argv.indexOf("-p") + 1]
const rubric = /YOUR RUBRIC: ([\\w-]+)/.exec(p)[1]
const reject = process.env.STUB_REJECT === rubric
const files = require("fs").readdirSync(".").sort().join(",")
console.log(JSON.stringify({ result: JSON.stringify({ verdict: reject ? "reject" : "approve", summary: rubric + " saw " + files, findings: reject ? [{ file: "add_comm_a", line: null, issue: "x", fix: "y", evidence: "z" }] : [] }) }))
`)
chmodSync(stub, 0o755)
writeFileSync(join(dir, "package.json"), '{"type":"commonjs"}')
const a = await audit(good(), { claudeBin: stub })
check("audit with all approvals passes", a.pass && a.results.length === 10, JSON.stringify(a.blockingFailures))
check("reviewers see only the bundle and its files", /add_comm_a\.lean/.test(a.results[0].verdict.summary) && /bundle\.json/.test(a.results[0].verdict.summary))
process.env.STUB_REJECT = "generality"
const ar = await audit(good(), { claudeBin: stub })
check("a blocking reject fails the audit", !ar.pass && ar.blockingFailures[0] === "generality")
delete process.env.STUB_REJECT
const none = await audit(good(), { claudeBin: join(dir, "does-not-exist") })
check("an unreachable CLI fails closed", !none.pass && none.unusable.length === 10)

// staging
const s = stageBundle(good(), { now: new Date("2026-10-18T12:00:00Z") })
const recs = s.jsonl.trim().split("\n").map((l) => JSON.parse(l))
check("staging path is per target", s.stagingPath === "data/staging/target-erdos-396/20261018T120000Z-001.jsonl", s.stagingPath)
check("one record per theorem, split into statement and proof", recs.length === 3 && recs[0].statement.startsWith("theorem add_comm_a") && recs[0].proof.startsWith(":="), JSON.stringify(recs[0]))
check("records carry library, author, status, toolchain", recs.every((r) => r.library === "target-erdos-396" && r.author === "hacker" && r.status === "staging" && r.toolchain === "leanprover/lean4:v4.29.1"))
check("jinshi gets the module and the names", s.jinshi.module === "Tengoku/Target/Erdos396.lean" && s.jinshi.count === 3)
const helper = good()
helper.entries[0].closure = "lemma helper_x (a : ℕ) : a = a := rfl\n\ntheorem add_comm_a (a b : ℕ) : a + b = b + a := by\n  omega"
const sh = stageBundle(helper)
check("helpers go to context", JSON.parse(sh.jsonl.split("\n")[0]).context.includes("helper_x"))

// spawnSync would block this process's event loop, and the stub Leak IV above lives in it
const run = (args, env) =>
  new Promise((resolve) => {
    const c = spawn("node", args, { env: { ...process.env, ...env } })
    let out = ""
    c.stdout.on("data", (d) => (out += d))
    c.stderr.on("data", (d) => (out += d))
    c.on("close", (status) => resolve({ status, stdout: out, stderr: "" }))
  })

// the command line, against the stub Leak IV and stub claude
const bundlePath = join(dir, "bundle.json")
writeFileSync(bundlePath, JSON.stringify(good()))
const outDir = join(dir, "out")
const cli = await run([join(here, "memory-intake.mjs"), "run", bundlePath, "--leak-iv", leakIvUrl, "--out", outDir], { CLAUDE_BIN: stub })
check("cli run passes and writes the staging files", cli.status === 0 && existsSync(join(outDir, "jinshi-nomination.json")) && existsSync(join(outDir, "registration.json")), cli.stdout + cli.stderr)
writeFileSync(bundlePath, JSON.stringify(broken))
const cli2 = await run([join(here, "memory-intake.mjs"), "run", bundlePath, "--leak-iv", leakIvUrl, "--out", join(dir, "out2")], { CLAUDE_BIN: stub })
check("cli stops at preflight and stages nothing", cli2.status === 1 && !existsSync(join(dir, "out2", "audit.json")), cli2.stdout)

server.close()
process.exit(bad ? 1 : 0)

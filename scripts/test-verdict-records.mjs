// node scripts/test-verdict-records.mjs — what a ledger row records about WHY an entry ended as it did (exits 1 on a failure)
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { ledgerRow } from "../lib/ledger-row.mjs"

const b = await import(new URL("../public/local-claude-bridge.mjs", import.meta.url).href)
const { gate2Detail, firstCompileError, mechanicalVerdict, verdictFields } = b
let failed = 0
const check = (name, fn) => {
  try {
    fn()
    console.log("ok  ", name)
  } catch (e) {
    failed++
    console.log("FAIL", name, "\n    ", String(e.message).split("\n").slice(0, 6).join("\n     "))
  }
}

// the text the bridge hands back for a Gate 2 failure: the header, Gate 2's own output, then guidance written for the agent
const GATE2_TEXT = [
  "🕊️ ARCHANGEL GATE 2 — run by the harness on the script Leak IV just accepted. You cannot call it and do not need to.",
  "GATE2_FAIL reason=name_collision names=FreeMagma — these names already exist in the target environment with a DIFFERENT definition than the original's export; the original cannot be replayed faithfully without renaming them. First differences: FreeMagma: export type = Type u → Type u | native type = Type u → Type u ;; FreeMagma.of: constructor missing",
  "tengoku_replay_entry: name collision with the target environment: FreeMagma",
  "",
  "WHAT TO DO NEXT (guidance for the agent, not part of the verdict): rename your declaration and try again.",
].join("\n")

check("gate2Detail keeps Gate 2's own words, with the first differences, and leaves out the header and the guidance", () => {
  const d = gate2Detail(GATE2_TEXT)
  assert.match(d, /^GATE2_FAIL reason=name_collision names=FreeMagma/)
  assert.match(d, /First differences: FreeMagma: export type = Type u → Type u \| native type/)
  assert.match(d, /name collision with the target environment/)
  assert.ok(!/ARCHANGEL GATE 2 — run by/.test(d), "the header is not the verdict")
  assert.ok(!/WHAT TO DO NEXT/.test(d), "the guidance is not the verdict")
  assert.ok(!/\n/.test(d), "one line")
})
check("gate2Detail is bounded and empty when there is no failure", () => {
  assert.ok(gate2Detail("GATE2_FAIL reason=kernel_error " + "x".repeat(5000)).length <= 900)
  assert.equal(gate2Detail("GATE2_PASS"), "")
  assert.equal(gate2Detail(""), "")
  assert.equal(gate2Detail(null), "")
})
check("firstCompileError takes the first diagnostic block of a Leak IV failure", () => {
  const t = "❌ Compilation Failed:\nLine 12 (Error): unknown identifier 'foo'\n  did you mean 'bar'?\nLine 30 (Error): type mismatch"
  assert.equal(firstCompileError(t), "Line 12 (Error): unknown identifier 'foo' did you mean 'bar'?")
  assert.ok(firstCompileError("x".repeat(2000)).length <= 300)
  assert.equal(firstCompileError(""), "")
})
check("mechanicalVerdict says why a mechanical attempt failed, in every way it can", () => {
  assert.deepEqual(mechanicalVerdict({ ok: true }), {})
  assert.deepEqual(mechanicalVerdict(null), {})
  assert.deepEqual(mechanicalVerdict({ ok: false, lint: ["native_decide", "unsafe"] }), { reason: "lint_refused", detail: "native_decide; unsafe" })
  assert.equal(mechanicalVerdict({ ok: false, gate2Reason: "kernel_error", gate2Text: GATE2_TEXT }).reason, "kernel_error")
  assert.match(mechanicalVerdict({ ok: false, gate2Reason: "name_collision", gate2Text: GATE2_TEXT }).detail, /First differences/)
  assert.match(mechanicalVerdict({ ok: false, gate2Reason: "kernel_error", gate2Detail: "GATE2_FAIL reason=kernel_error msg=boom" }).detail, /msg=boom/, "a detail already extracted is used as it is")
  assert.deepEqual(mechanicalVerdict({ ok: false, leakText: "❌ Compilation Failed:\nLine 3 (Error): nope" }), { reason: "compile_error", detail: "Line 3 (Error): nope" })
  assert.deepEqual(mechanicalVerdict({ ok: false, reason: "prefix_known_broken", detail: "A.lean" }), { reason: "prefix_known_broken", detail: "A.lean" })
})
check("verdictFields keeps what a row needs, bounded, and drops what is empty", () => {
  assert.deepEqual(verdictFields(undefined), {})
  assert.deepEqual(verdictFields({}), {})
  assert.deepEqual(verdictFields({ reason: "", detail: "", names: [], gate2Rejections: [] }), {})
  const f = verdictFields({ reason: "name_collision", detail: "d ".repeat(2000), names: Array.from({ length: 20 }, (_, i) => `N${i}`), gate2Rejections: Array.from({ length: 9 }, () => ({ reason: "kernel_error", detail: "y".repeat(2000) })), secret: "no", args: { big: 1 } })
  assert.equal(f.reason, "name_collision")
  assert.ok(f.detail.length <= 900)
  assert.equal(f.names.length, 8)
  assert.equal(f.gate2Rejections.length, 3)
  assert.ok(f.gate2Rejections.every((g) => g.detail.length <= 400))
  assert.deepEqual(Object.keys(f).sort(), ["detail", "gate2Rejections", "names", "reason"], "nothing else is carried")
})
check("ledgerRow is a whitelist: the outcome, why, and the text behind it; a bare outcome stays a bare row", () => {
  const at = "2026-10-21T00:00:00.000Z"
  assert.deepEqual(ledgerRow({ id: 7, name: "A.b", sourcePath: "A.lean", outcome: "mechanical" }, at), { id: 7, name: "A.b", sourcePath: "A.lean", outcome: "mechanical", at })
  const r = ledgerRow({ id: 8, name: "A.c", sourcePath: "A.lean", outcome: "untranslatable", reason: "name_collision", detail: gate2Detail(GATE2_TEXT), names: ["FreeMagma"], args: { x: 1 }, text: "full text", token: "t" }, at)
  assert.deepEqual(Object.keys(r), ["id", "name", "sourcePath", "outcome", "at", "reason", "detail", "names"])
  assert.match(r.detail, /First differences/)
  const g = ledgerRow({ id: 9, name: "A.d", sourcePath: "A.lean", outcome: "agentic", reason: "agent_banked", gate2Rejections: [{ reason: "kernel_error", detail: "GATE2_FAIL reason=kernel_error ..." }] }, at)
  assert.equal(g.gate2Rejections[0].reason, "kernel_error")
  assert.equal(ledgerRow({ id: 1, name: "n", sourcePath: "p", outcome: "failed", error: "e".repeat(999) }, at).error.length, 300)
})
check("rows written before this existed still parse as rows of the same shape", () => {
  const old = JSON.parse('{"id":292,"name":"Algolean.AddWriter.ret_pure","sourcePath":"Algolean/AddWriter/Basic.lean","outcome":"mechanical","at":"2026-09-27T10:21:18.903Z","run":"36312069197"}')
  assert.deepEqual(Object.keys(ledgerRow(old, old.at)), ["id", "name", "sourcePath", "outcome", "at"])
})

// every way out of the per-entry decision says why: no return may go back to a bare outcome, or the next mechanism added would
// silently stop being recorded
const src = readFileSync(new URL("../public/local-claude-bridge.mjs", import.meta.url), "utf8")
const fn = src.slice(src.indexOf("async function recurseOneEntry(entry, opts) {"), src.indexOf("async function recurseOneEntry(entry, opts) {") + 30000)
const body = fn.slice(0, fn.indexOf("\n}\n") + 3)
check("recurseOneEntry returns only through done(), which carries the verdict", () => {
  assert.ok(body.length > 5000, "found the function")
  assert.ok(!/return \{ id: entry\.id, outcome:/.test(body), "a bare outcome was returned")
  assert.ok((body.match(/return done\(/g) || []).length >= 14)
  for (const outcome of ["mechanical", "cached-mechanical", "untranslatable", "agentic", "unresolved", "deferred-agent", "unbankable", "gate2-unavailable", "infra-blocked", "export-unavailable"]) assert.match(body, new RegExp(`done\\("${outcome}"`), outcome)
})
check("the agent's Gate 2 refusals are collected and the entry-result frame and the ledger carry the verdict", () => {
  assert.match(body, /gate2Log: \[\]/)
  assert.match(src, /ctx\.gate2Log\.push\(\{ reason: r\.reason, detail: r\.detail \|\| gate2Detail\(r\.text\) \}\)/)
  assert.match(src, /outcome: r\.outcome, \.\.\.verdictFields\(r\)/)
  assert.match(readFileSync(new URL("./run-recurse.mjs", import.meta.url), "utf8"), /JSON\.stringify\(ledgerRow\(o\)\)/)
})
process.exit(failed ? 1 : 0)

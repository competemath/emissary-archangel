// node scripts/test-lean-repairs.mjs — the deterministic repairs of the mechanical pass (lib/lean-repairs.mjs) and the one content lint behind it (exits 1 on a failure).
//
// The tests check the INVARIANTS of each repair on enumerated and random inputs, not the case that was found (see scripts/bump/tests/CLASSES.md): a repair is only worth having if it cannot
// damage a text, and the compile and Gate 2 re-judge what comes out.
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { MECHANICS_VERSION, dropDuplicatedTailAttributes, policyCheck, policyRepair } from "../lib/lean-repairs.mjs"
import { ledgerRow } from "../lib/ledger-row.mjs"
import { TERMINAL, VERIFIED, isSettled, parseLedger } from "../lib/ledger-settle.mjs"

let failed = 0
const check = async (name, fn) => {
  try {
    await fn()
    console.log("ok  ", name)
  } catch (e) {
    failed++
    console.log("FAIL", name, "\n    ", String(e.message).split("\n").slice(0, 8).join("\n     "))
  }
}

// ---- the junction: an attribute line that ends the prefix and that the entry repeats -------------------------------------------------------------------------------------------
const J = dropDuplicatedTailAttributes

await check("the case found: a docstring, an attribute, a blank line, then the entry's own copy of the attribute", () => {
  const prefix = "def f := 1\n\n/-- doc\nmore -/\n@[simp]\n\n"
  const target = "@[simp]\ntheorem t : f = 1 := rfl\n"
  assert.equal(J(prefix, target), "def f := 1\n\n/-- doc\nmore -/\n\n")
})

await check("stacked attributes: each is taken out once, and only those the entry repeats", () => {
  assert.equal(J("x\n@[simp]\n@[reducible]\n", "@[simp]\n@[reducible]\ntheorem t : True := trivial"), "x\n")
  assert.equal(J("x\n@[simp]\n@[reducible]\n", "@[simp]\ntheorem t : True := trivial"), "x\n@[reducible]\n")
  assert.equal(J("x\n@[simp]\n", "@[reducible]\ntheorem t : True := trivial"), "x\n@[simp]\n")
})

await check("an attribute of the entry that is not at the end of the prefix is not touched", () => {
  const p = "@[simp]\ntheorem other : True := trivial\n\n"
  assert.equal(J(p, "@[simp]\ntheorem t : True := trivial"), p)
})

await check("a target without leading attributes, and a prefix without trailing ones, come back as they were", () => {
  assert.equal(J("x\n@[simp]\n", "theorem t : True := trivial"), "x\n@[simp]\n")
  assert.equal(J("x\n\n", "@[simp]\ntheorem t : True := trivial"), "x\n\n")
  assert.equal(J("", "@[simp]\ntheorem t : True := trivial"), "")
})

await check("an attribute that goes over several lines is not guessed at", () => {
  const p = "x\n@[simp,\n  reducible]\n"
  assert.equal(J(p, "@[simp,\n  reducible]\ntheorem t : True := trivial"), p)
})

await check("a CRLF source: the repeated attribute is found with its \\r", () => {
  assert.equal(J("x\r\n@[simp]\r\n", "@[simp]\r\ntheorem t : True := trivial"), "x\r\n")
  assert.equal(J("x\r\n@[simp]\r\n\r\n", "@[simp]\r\ntheorem t : True := trivial\r\n"), "x\r\n\r\n")
})

function rng(seed) {
  let s = seed >>> 0
  return () => ((s = (s * 1664525 + 1013904223) >>> 0) / 2 ** 32)
}
const ATTRS = ["@[simp]", "@[reducible]", "@[ext]", "@[simp, norm_cast]", "@[to_additive]"]

await check("random prefixes and entries: idempotent, only attribute lines go, the kept lines are in order, nothing is repeated across the junction", () => {
  const r = rng(7)
  const pick = (a) => a[Math.floor(r() * a.length)]
  for (let n = 0; n < 2000; n++) {
    const body = Array.from({ length: Math.floor(r() * 5) }, () => pick(["def a := 1", "/-- doc -/", "", "theorem u : True := trivial", "namespace X"]))
    const tail = Array.from({ length: Math.floor(r() * 4) }, () => pick([...ATTRS, ""]))
    const lead = Array.from({ length: Math.floor(r() * 4) }, () => pick(ATTRS))
    const prefix = [...body, ...tail].join("\n") + "\n"
    const target = [...lead, "theorem t : True := trivial"].join("\n")
    const out = J(prefix, target)
    const msg = JSON.stringify({ prefix, target, out })
    assert.equal(J(out, target), out, "idempotent " + msg)
    const inLines = prefix.split("\n"), outLines = out.split("\n")
    let i = 0
    for (const l of outLines) {
      while (i < inLines.length && inLines[i] !== l) i++
      assert.ok(i < inLines.length, "order " + msg)
      i++
    }
    // multiplicities: every line that is not an attribute line is still there as many times as it was written (`includes` alone would pass a repair that dropped one copy of a repeated line)
    const count = (a) => a.reduce((m, l) => m.set(l, (m.get(l) || 0) + 1), new Map())
    const ci = count(inLines), co = count(outLines)
    for (const [l, n] of ci) if (!/^\s*@\[.*\]\s*$/.test(l)) assert.ok((co.get(l) || 0) >= n, "a line was lost: " + JSON.stringify(l) + " " + msg)
    for (const [l, n] of co) assert.ok((ci.get(l) || 0) >= n, "a line was added " + msg)
    // nothing the entry carries is also at the end of the prefix
    const trailing = []
    const ol = out.split("\n")
    let e = ol.length
    while (e > 0 && ol[e - 1].trim() === "") e--
    while (e > 0 && /^\s*@\[.*\]\s*$/.test(ol[e - 1])) trailing.push(ol[--e].trim())
    for (const t of trailing) assert.ok(!lead.includes(t), "a repeated attribute is left " + msg)
  }
})

// ---- the worker: one Python process for the whole run ---------------------------------------------------------------------------------------------------------------------------------
await check("many requests at once are answered, each its own (one worker, answers matched by id)", async () => {
  const texts = Array.from({ length: 60 }, (_, i) => (i % 2 ? `theorem t${i} : True := trivial\n` : `theorem t${i} : True := trivial\n#print axioms t${i}\n`))
  const res = await Promise.all(texts.map((t) => policyCheck(t)))
  res.forEach((v, i) => assert.equal(v.length > 0, i % 2 === 0, `request ${i}`))
})

await check("a worker that dies is replaced by the next request, and the requests it held fail loudly", async () => {
  const lr = await import("../lib/lean-repairs.mjs?restart")
  assert.deepEqual(await lr.policyCheck("theorem a : True := trivial\n"), [])
  const pid = lr.workerPid()
  assert.ok(pid, "there is a worker")
  process.kill(pid, "SIGKILL")
  await new Promise((r) => setTimeout(r, 300))
  assert.notEqual(lr.workerPid(), pid)
  assert.deepEqual(await lr.policyCheck("theorem a : True := trivial\n#print axioms a\n").then((v) => v.length > 0), true)
})

// ---- the one lint -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
await check("the lint is the tree's: `#print axioms` is refused, a native_decide is refused, a plain theorem is not", async () => {
  assert.ok((await policyCheck("theorem a : True := trivial\n#print axioms a\n")).length)
  assert.ok((await policyCheck("theorem a : True := by native_decide\n")).length)
  assert.deepEqual(await policyCheck("theorem a : True := trivial\n"), [])
})

await check("the options the old hand-kept copy was missing are allowed (they are on the tree's list)", async () => {
  for (const o of ["linter.unusedSectionVars", "linter.flexible", "linter.unusedTactic", "linter.unnecessarySimpa", "linter.unnecessarySeqFocus", "linter.unusedSimpArgs", "linter.unreachableTactic", "linter.style.header"]) {
    assert.deepEqual(await policyCheck(`set_option ${o} false\ntheorem a : True := trivial\n`), [], o)
  }
})

await check("repair takes the author's #print/#check and a linter option the tree does not list, and says what", async () => {
  const text = "import Mathlib\nset_option linter.haveILetI false\ntheorem a : True := trivial\n#print axioms a\n"
  const r = await policyRepair(text)
  assert.equal(r.text, "import Mathlib\ntheorem a : True := trivial\n")
  assert.deepEqual(r.removed.map((x) => x.kind), ["set_option linter.haveILetI", "#print"])
  assert.deepEqual(r.violations, [])
})

await check("repair leaves a text with another reason for refusal refused, with that reason", async () => {
  const r = await policyRepair("#print axioms a\ntheorem a : True := by native_decide\n")
  assert.ok(r.violations.some((v) => /native_decide/.test(v)), JSON.stringify(r.violations))
})

await check("a text nobody could judge is an error, not an empty list (a missing interpreter must not bank anything)", async () => {
  process.env.EMISSARY_PYTHON = "/nonexistent/python"
  const lr = await import("../lib/lean-repairs.mjs?broken")
  await assert.rejects(lr.policyCheck("theorem a : True := trivial\n"), /content lint could not run/)
  delete process.env.EMISSARY_PYTHON
})


// ---- the ledger: an entry the mechanical pass gave up on is tried again when the remedies have improved -----------------------------------------------------------------------------
const row = (id, outcome, mechanics) => JSON.stringify({ id, outcome, ...(mechanics === undefined ? {} : { mechanics }) })
const ask = (lines, id, mode, v = MECHANICS_VERSION) => isSettled(id, parseLedger(lines.join("\n")), { mode, agentAttempts: 1, mechanicsVersion: v })

await check("a deferred-agent row of the current generation is settled for a mechanical run and open for an agent run", () => {
  assert.equal(ask([row(1, "deferred-agent", MECHANICS_VERSION)], 1, "mechanical"), true)
  assert.equal(ask([row(1, "deferred-agent", MECHANICS_VERSION)], 1, "agent"), false)
})

await check("a deferred-agent row from an older generation, or from before the stamp, is tried again by a mechanical run", () => {
  assert.equal(ask([row(1, "deferred-agent", MECHANICS_VERSION - 1)], 1, "mechanical"), false)
  assert.equal(ask([row(1, "deferred-agent")], 1, "mechanical"), false)
  assert.equal(ask([row(1, "deferred-agent", MECHANICS_VERSION)], 1, "mechanical", MECHANICS_VERSION + 1), false)
})

await check("verified and terminal outcomes are settled in every mode and every generation; the last row of an entry wins", () => {
  for (const o of [...VERIFIED, ...TERMINAL]) for (const mode of ["mechanical", "agent"]) assert.equal(ask([row(1, o)], 1, mode, 99), true, o)
  assert.equal(ask([row(1, "deferred-agent", 0), row(1, "mechanical")], 1, "mechanical"), true)
  assert.equal(ask([row(1, "mechanical"), row(1, "failed")], 1, "mechanical"), false)
  assert.equal(ask([], 1, "mechanical"), false)
})

await check("raising the generation reopens exactly the deferred-agent entries, nothing else (random ledgers)", () => {
  const r = rng(11)
  const outcomes = [...VERIFIED, ...TERMINAL, "deferred-agent", "unresolved", "failed", "infra-blocked"]
  for (let n = 0; n < 300; n++) {
    const lines = Array.from({ length: 12 }, (_, i) => row(i, outcomes[Math.floor(r() * outcomes.length)], MECHANICS_VERSION))
    const led = parseLedger(lines.join("\n"))
    for (let id = 0; id < 12; id++) {
      const a = isSettled(id, led, { mode: "mechanical", agentAttempts: 1, mechanicsVersion: MECHANICS_VERSION })
      const b = isSettled(id, led, { mode: "mechanical", agentAttempts: 1, mechanicsVersion: MECHANICS_VERSION + 1 })
      if (led.last.get(id) === "deferred-agent") assert.deepEqual([a, b], [true, false])
      else assert.equal(a, b)
    }
  }
})

await check("a half-written last line does not stop a run", () => {
  const led = parseLedger(row(1, "mechanical") + "\n" + '{"id":2,"outcome":"defer')
  assert.equal(led.last.get(1), "mechanical")
})

await check("ledgerRow stamps a deferred-agent row with the generation and no other row", () => {
  assert.equal(ledgerRow({ id: 1, name: "a", sourcePath: "p", outcome: "deferred-agent", reason: "lint_refused" }).mechanics, MECHANICS_VERSION)
  assert.equal("mechanics" in ledgerRow({ id: 1, name: "a", sourcePath: "p", outcome: "mechanical" }), false)
})

await check("the prefix cache is stamped with the generation, and a mark from an older one is not believed (the bridge)", () => {
  const b = readFileSync(new URL("../public/local-claude-bridge.mjs", import.meta.url), "utf8")
  assert.match(b, /status: "broken", mechanics: MECHANICS_VERSION/)
  assert.match(b, /\(raw\.mechanics \?\? 0\) < MECHANICS_VERSION/)
  assert.ok(b.indexOf("const staleBroken") < b.indexOf("const cached = staleBroken"))
})

await check("translate-finish stamps the mechanical status with the generation and translate-all dispatches again when it is older", () => {
  const f = readFileSync(new URL("./translate-finish.mjs", import.meta.url), "utf8")
  assert.match(f, /mode === "mechanical" \? \{ mechanics: MECHANICS_VERSION \}/)
  const w = readFileSync(new URL("../.github/workflows/translate-all.yml", import.meta.url), "utf8")
  assert.match(w, /m == "mechanical" and st\[m\]\.get\("mechanics", 0\) < MECHANICS/)
  assert.match(w, /MECHANICS = int\(re\.search\(r"export const MECHANICS_VERSION = \(\\d\+\)"/)
  assert.match(w, /sparse-checkout: "data\/translate\\nlib"/)  // the step reads lib/lean-repairs.mjs
})

await check("queue-server uses the shared rules and keeps no copy of them", () => {
  const q = readFileSync(new URL("./queue-server.mjs", import.meta.url), "utf8")
  assert.match(q, /isSettled\(id, led, \{[^}]*mechanicsVersion: MECHANICS_VERSION/)
  assert.doesNotMatch(q, /const VERIFIED\b|const TERMINAL\b/)
})

// ---- the bridge uses it, and keeps no copy -----------------------------------------------------------------------------------------------------------------------------------
const bridge = readFileSync(new URL("../public/local-claude-bridge.mjs", import.meta.url), "utf8")
await check("the bridge keeps no hand-written copy of the lint (the copy drifted by eight options)", () => {
  assert.doesNotMatch(bridge, /const BANK_FORBIDDEN\b/)
  assert.doesNotMatch(bridge, /const BANK_ALLOWED_OPTIONS\b/)
})

await check("every use of lintBankable in the bridge is awaited (a promise is truthy: an unawaited one would let everything through)", () => {
  const uses = [...bridge.matchAll(/(?<!function )\blintBankable\(/g)].filter((m) => !/^\s*\/\//.test(bridge.slice(bridge.lastIndexOf("\n", m.index) + 1, m.index) + "x"))
  assert.ok(uses.length >= 3, "expected the three call sites, found " + uses.length)
  for (const m of uses) {
    const before = bridge.slice(Math.max(0, m.index - 8), m.index)
    assert.match(before, /await $/, "not awaited: " + bridge.slice(m.index - 40, m.index + 30))
  }
})

await check("the bridge loads the helpers from the checkout it works in, not from beside itself (a downloaded copy has no ../lib)", () => {
  assert.doesNotMatch(bridge, /from "\.\.\/lib\/lean-repairs\.mjs"/)
  assert.match(bridge, /join\(APP_ROOT, "lib", "lean-repairs\.mjs"\)/)
})

console.log(failed ? `\n${failed} FAILED` : "\nall ok")
process.exit(failed ? 1 : 0)

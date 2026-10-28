// node scripts/test-lean-repairs.mjs — the deterministic repairs of the mechanical pass (lib/lean-repairs.mjs) and the one content lint behind it (exits 1 on a failure).
//
// The tests check the INVARIANTS of each repair on enumerated and random inputs, not the case that was found (see scripts/bump/tests/CLASSES.md): a repair is only worth having if it cannot
// damage a text, and the compile and Gate 2 re-judge what comes out.
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { dropDuplicatedTailAttributes, policyCheck, policyRepair } from "../lib/lean-repairs.mjs"

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
    for (const l of inLines) if (!outLines.includes(l)) assert.match(l, /^\s*@\[.*\]\s*$/, "only attribute lines go " + msg)
    // nothing the entry carries is also at the end of the prefix
    const trailing = []
    const ol = out.split("\n")
    let e = ol.length
    while (e > 0 && ol[e - 1].trim() === "") e--
    while (e > 0 && /^\s*@\[.*\]\s*$/.test(ol[e - 1])) trailing.push(ol[--e].trim())
    for (const t of trailing) assert.ok(!lead.includes(t), "a repeated attribute is left " + msg)
  }
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

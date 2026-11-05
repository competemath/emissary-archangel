// node scripts/test-bisect-property.mjs — the halving of a failed batch (scripts/bisect.mjs), on REAL module lists.
// The modules are the ones the pipeline has set up: every data/exports/<library>/<Module>.names.json in the repository is a real module of a real library (140 libraries,
// about 15,000 modules, names with dots, guillemets, long theorem names). For each library, many failure patterns (nothing fails, one module, 1 %, 10 %, half, all; the batch limit
// from none to 25 modules; the order of the modules shuffled) are run through the model of a closure or export process (a batch fails when it holds a poison module or is
// over the limit; a module alone fails when it is poison), and the invariants are checked:
//   1. every module that is not poison goes through exactly once, in exactly one successful batch or alone;
//   2. every poison module is handled alone exactly once, and ends as failed; it is never part of a successful batch;
//   3. no failing batch is run twice, and the number of runs is at most 2n - 1 (the halving tree), one run for a batch that goes through whole;
//   3b. one poison module costs a logarithmic number of runs, and with nothing poison and a limit of 4 or more no module is run alone (the old fallback ran every module alone);
//   4. a failed batch of k modules is followed by a run of its first half, ceil(k / 2) modules (the halving, not one process per module);
//   5. the outcome (which modules went through, which failed) does not depend on the order of the modules.
// Then the same checks are run on four broken versions of the halving, and each must be caught (a test that cannot fail proves nothing).
import { existsSync, readdirSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { bisectItems } from "./bisect.mjs"

const here = dirname(fileURLToPath(import.meta.url))
const exportsDir = join(here, "..", "data", "exports")

// real modules, by library
const libs = new Map()
for (const lib of existsSync(exportsDir) ? readdirSync(exportsDir) : []) {
  const dir = join(exportsDir, lib)
  let mods
  try {
    mods = readdirSync(dir).filter((f) => f.endsWith(".names.json")).map((f) => f.slice(0, -".names.json".length))
  } catch {
    continue
  }
  if (mods.length) libs.set(lib, mods.sort())
}
const realModules = [...libs.values()].reduce((a, m) => a + m.length, 0)
// violations are counted per suite; only the first few of the real halving are printed (a broken version is expected to break the invariants)
const state = { count: 0, print: false }
const fail = (what, detail) => {
  state.count++
  if (state.print && state.count <= 12) console.log("FAIL", what, detail ?? "")
}
if (libs.size < 100 || realModules < 10000) {
  console.log(`FAIL the real corpus is missing or too small: ${libs.size} libraries, ${realModules} modules (data/exports/*/*.names.json)`)
  process.exit(1)
}

// a small seeded generator: the cases are the same on every run
let seed = 20261105
const rnd = () => {
  seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0
  return seed / 4294967296
}
const shuffled = (a) => {
  const b = a.slice()
  for (let i = b.length - 1; i > 0; i--) {
    const j = Math.floor(rnd() * (i + 1))
    ;[b[i], b[j]] = [b[j], b[i]]
  }
  return b
}
const sample = (a, k) => shuffled(a).slice(0, Math.max(0, Math.min(k, a.length)))

// one case: returns what happened
async function run(bisect, items, poison, limit) {
  const batches = [] // { size, ok, first }
  const okIn = new Map() // module -> how many successful batches or single runs held it
  const aloneRuns = new Map()
  const failed = []
  const runBatch = async (batch) => {
    const ok = batch.length <= limit && !batch.some((m) => poison.has(m))
    batches.push({ size: batch.length, ok, first: batch[0], items: batch })
    if (ok) for (const m of batch) okIn.set(m, (okIn.get(m) || 0) + 1)
    return ok
  }
  const runOne = async (m) => {
    aloneRuns.set(m, (aloneRuns.get(m) || 0) + 1)
    if (poison.has(m)) failed.push(m)
    else okIn.set(m, (okIn.get(m) || 0) + 1)
  }
  await bisect(items, runBatch, runOne)
  return { batches, okIn, aloneRuns, failed }
}

function checkCase(label, items, poison, limit, res, other) {
  const n = items.length
  // 1 and 2
  for (const m of items) {
    if (poison.has(m)) {
      if (res.okIn.get(m)) fail(`${label}: poison module in a successful run`, m)
      if (res.aloneRuns.get(m) !== 1 || res.failed.filter((x) => x === m).length !== 1) fail(`${label}: poison module not handled alone exactly once`, `${m} ${res.aloneRuns.get(m)}`)
    } else if (res.okIn.get(m) !== 1) fail(`${label}: module went through ${res.okIn.get(m) || 0} times`, m)
  }
  if (res.failed.length !== poison.size) fail(`${label}: failed count`, `${res.failed.length} != ${poison.size}`)
  // 3
  const seen = new Set()
  for (const b of res.batches) {
    const key = b.items.join("\u0000")
    if (seen.has(key)) fail(`${label}: a batch was run twice`, b.size)
    seen.add(key)
  }
  const runs = res.batches.length + res.aloneRuns.size
  if (n > 1 && runs > 2 * n - 1) fail(`${label}: ${runs} runs for ${n} modules (limit ${2 * n - 1})`)
  if (n > 1 && poison.size === 0 && limit >= n && res.batches.length !== 1) fail(`${label}: a batch that fits was run ${res.batches.length} times`)
  // 3b: a single poison module costs a logarithmic number of runs, not one per module (the old fallback ran every module alone); alone: the poison module and, from the odd splits 3 -> 2+1 and 2 -> 1+1, at most two siblings
  if (poison.size === 1 && limit === Infinity && n > 2) {
    if (res.aloneRuns.size > 3) fail(`${label}: one poison module made ${res.aloneRuns.size} modules run alone`)
    if (res.batches.length > 2 * (Math.ceil(Math.log2(n)) + 1)) fail(`${label}: one poison module made ${res.batches.length} batch runs for ${n} modules`)
  }
  // 3c: when nothing is poison and the limit is 4 or more, a batch over the limit is halved until it fits: no module is ever run alone
  if (n > 1 && poison.size === 0 && limit >= 4 && res.aloneRuns.size > 0) fail(`${label}: ${res.aloneRuns.size} modules were run alone although none is poison`)
  // 4: after a failed batch of k modules, the next batch is its first half
  for (let i = 0; i + 1 < res.batches.length; i++) {
    const b = res.batches[i]
    if (!b.ok && b.size > 2) {
      const next = res.batches[i + 1]
      if (next.size !== Math.ceil(b.size / 2) || next.first !== b.first) fail(`${label}: after a failed batch of ${b.size} came one of ${next.size}`)
    }
  }
  // 5
  if (other) {
    const a = [...res.okIn.keys()].sort().join(",")
    const o = [...other.okIn.keys()].sort().join(",")
    if (a !== o || res.failed.slice().sort().join(",") !== other.failed.slice().sort().join(",")) fail(`${label}: the outcome depends on the order`)
  }
}

async function suite(bisect, print) {
  seed = 20261105
  state.count = 0
  state.print = print
  let cases = 0
  let modulesRun = 0
  for (const [lib, mods] of libs) {
    const n = mods.length
    const patterns = [
      ["none", () => new Set()],
      ["one", () => new Set(sample(mods, 1))],
      ["1%", () => new Set(sample(mods, Math.max(1, Math.round(n * 0.01))))],
      ["10%", () => new Set(sample(mods, Math.round(n * 0.1)))],
      ["half", () => new Set(sample(mods, Math.round(n / 2)))],
      ["all", () => new Set(mods)],
    ]
    for (const [pname, mk] of patterns) {
      for (const limit of [Infinity, Math.max(1, Math.floor(n / 2)), 100, 25]) {
        const poison = mk()
        const items = shuffled(mods)
        const res = await run(bisect, items, poison, limit)
        const again = await run(bisect, shuffled(mods), poison, limit)
        checkCase(`${lib} (${n} modules), poison ${pname}, limit ${limit}`, items, poison, limit, res, again)
        cases += 2
        modulesRun += 2 * n
      }
    }
  }
  return { cases, modulesRun, failures: state.count }
}

const good = await suite(bisectItems, true)
console.log(`bisect: ${good.cases} real cases over ${libs.size} libraries (${realModules} real modules, ${good.modulesRun} module runs): ${good.failures} violations`)

// broken versions of the halving: each must be caught
const mutants = {
  "the second half is never tried": async (items, runBatch, runOne) => {
    const go = async (it) => {
      if (it.length === 1) return runOne(it[0])
      if (await runBatch(it)) return
      await go(it.slice(0, Math.ceil(it.length / 2)))
    }
    return go(items)
  },
  "a failed batch falls to one run per module (the old fallback)": async (items, runBatch, runOne) => {
    if (items.length === 1) return runOne(items[0])
    if (await runBatch(items)) return
    for (const m of items) await runOne(m)
  },
  "a failing module is retried inside its batch (a batch run twice)": async (items, runBatch, runOne) => {
    const go = async (it) => {
      if (it.length === 1) return runOne(it[0])
      if (await runBatch(it)) return
      if (it.length > 1 && (await runBatch(it))) return
      const h = Math.ceil(it.length / 2)
      await go(it.slice(0, h))
      await go(it.slice(h))
    }
    return go(items)
  },
  "the halves are cut at a third": async (items, runBatch, runOne) => {
    const go = async (it) => {
      if (it.length === 1) return runOne(it[0])
      if (await runBatch(it)) return
      const h = Math.max(1, Math.floor(it.length / 3))
      await go(it.slice(0, h))
      await go(it.slice(h))
    }
    return go(items)
  },
}
let caught = 0
for (const [name, mutant] of Object.entries(mutants)) {
  const r = await suite(mutant, false)
  if (r.failures > 0) caught++
  console.log(`${r.failures > 0 ? "ok" : "FAIL"} the broken version "${name}" is caught: ${r.failures} violations in ${r.cases} cases`)
}
if (good.failures) {
  console.log(`${good.failures} violation(s) of the real halving`)
  process.exit(1)
}
if (caught !== Object.keys(mutants).length) {
  console.log("a broken version of the halving was not caught")
  process.exit(1)
}
console.log(`bisect-property: all invariants hold on ${good.cases} real cases; ${caught} of ${Object.keys(mutants).length} broken versions caught`)

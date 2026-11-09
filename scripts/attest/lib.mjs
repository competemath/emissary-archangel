// Pure helpers of the statement attestation (scripts/attest/attest-statements.mjs). No I/O to the network, no Lean, no bridge: everything here is
// tested by scripts/test-attest-statements.mjs.
//
// A STATEMENT ATTESTATION says: for each problem, Archangel (Gate 2, gate2/) found the kernel to accept `fun h => h : T_translated → T_original`, where T_original is
// the upstream statement replayed from an export made on its own toolchain, and T_translated is the statement as it was made to compile on the tree. The
// problems' proofs are `sorry`: these are statements, so Gate 1 (Leak IV: no `sorry`, no warning) cannot be run on them and is not. That is the whole difference
// from a translation, and it is why nothing here can be banked: see ADMISSION_DIRS and the `admissible: false` in every attestation.
import { createHash } from "node:crypto"
import { resolve, relative, sep } from "node:path"

export const SCHEMA = "emissary.statement-attestation/v1"
export const KIND = "statement-only"

// Where a verified translation goes to become a Tengoku record. A statement attestation is never written under any of them.
export const ADMISSION_DIRS = ["data/bank", "data/staging", "data/translate", "data/tentative", "data/intake"]

export const sha256 = (s) => createHash("sha256").update(s).digest("hex")

/** Throws if `outDir` is, or is inside, a directory a record could be banked from (relative to `root`). */
export function assertNotAdmissionPath(outDir, root) {
  const rel = relative(resolve(root), resolve(outDir))
  const inside = (d) => rel === d || rel.startsWith(d + sep) || rel.startsWith(d + "/")
  for (const d of ADMISSION_DIRS) if (inside(d)) throw new Error(`refusing to write a statement attestation under ${d}: a record banked from there reaches Tengoku`)
}

/** The module name of problem `index` as the exports are filed (`FATEX.«9»`, `FATEX.9`, with the library root and the key given). */
export function exportCandidates(root, index) {
  return [`${root}.«${index}»`, `${root}.${index}`]
}

/** Gate 2's verdict text -> { ok, reason, newStatement, oldStatement, identical }. `identical`: the two printed statements are the same text once whitespace is collapsed (a hint, not a proof: the kernel's check is the verdict). */
export function readVerdict(result) {
  const raw = String(result?.text || "")
  const ok = !!result?.ok
  const m = raw.match(/new_statement=([\s\S]*?)\s+old_statement=([\s\S]*?)(?:\n\n|$)/)
  const norm = (s) => String(s || "").replace(/\s+/g, " ").trim()
  const newStatement = m ? norm(m[1]) : null
  const oldStatement = m ? norm(m[2]) : null
  return {
    ok,
    reason: ok ? "pass" : result?.reason || "no_verdict",
    newStatement,
    oldStatement,
    identical: newStatement && oldStatement ? newStatement === oldStatement : null,
  }
}

const LIMITS_COMMON = [
  "The proofs are `sorry`: this is a check of STATEMENTS. Gate 1 (Leak IV: no sorry, no warning) is not run, so this is not a translation and is never admissible to Tengoku.",
  "Direction: the kernel accepted translated -> original (a proof of the translated statement proves the original one). The converse is not checked; `statementsIdentical` is a printed-text hint, not a proof of it.",
  "The original is replayed with the library's own definitions under their names; a definition of the translation that differs from the original's is a name collision and fails.",
]
const MATHLIB_LIMIT = {
  "library-only": "Constants of Mathlib are not in the original's export (setup-source exports only the library's own constants, --only-listed): a Mathlib name is taken to mean in the tree what it meant on the original's toolchain unless its type differs, in which case the kernel refuses the bridge.",
  "full-closure": "The original's export holds the Mathlib constants its statement reaches (lean4export without --only-listed, scripts/attest/export-full.mjs). Gate 2 replays those the tree does not have, under their old names, and refuses (name_collision) one the tree has with a different type; a Mathlib constant the tree has with the same type is taken to mean the same.",
}
export const EXPORT_MODES = Object.keys(MATHLIB_LIMIT)
const BATCH_LIMITS = [
  "The proofs are `sorry`: this is a check of STATEMENTS, never a translation, and never admissible to Tengoku. Gate 1 (Leak IV: no sorry, no warning) is not run. The statement-only rule lets `sorry` stand only in the PROOF of the theorem checked: the statement and every definition either side's statement reaches must stand on the three standard axioms.",
  "Gate 2's batch check: each definition the statements reach (library or Mathlib) must be identical, or the kernel must accept `native = original` by `Eq.refl` with the original's replayed beside it (definitional equality, universe and instance paths included); then the two statements are structurally equal (`via=equal`) or the bridge `fun h => h : T_translated -> T_original` is accepted (`via=entails`).",
  "Direction: translated -> original. A proof of the translated statement proves the original one; the converse is not checked, except where `via=equal`.",
  "A Mathlib constant the tree has with the same type and a different definition is accepted only if the kernel finds the two definitions definitionally equal.",
  "BRIDGE (`bridge`, only when it is not `fun h => h`): a problem the plain bridge refused was tried once more with the term named there. The kernel checks that term like any other; it is a different proof of the same implication.",
  "REPAIRED INSTANCE ARGUMENTS (`repairedInstanceArguments`): where the original's term applies a constant of the tree to an instance argument of a type the tree's constant no longer takes (a `Ring` where it now wants `NonAssocRing`, a renamed class), the tree re-synthesizes that argument. The count is per problem; the kernel still has to accept the bridge between the translation and the repaired original. A pass with a count above 0 is relative to the tree's choice of those instances.",
  "MIGRATION TABLE (`interpretation`): the original's exports hold the library's own constants only, and a handful of Mathlib instances its statements mention by name (Monoid.toNatPow, algebraMap, ...) no longer exist in the tree's Mathlib. They are defined by hand, for the check of one problem at a time, by the tree's own constants. A pass whose `migrated` list is not empty is RELATIVE to that table: it says the translated statement implies the original one reading those names as the table defines them. The table is hashed here and its text is in this file; it is reviewable, not kernel-derived.",
]
export const limitsFor = (exportMode, checker = "daemon") => (checker === "batch-statement-only" ? BATCH_LIMITS : [...LIMITS_COMMON, MATHLIB_LIMIT[exportMode] || MATHLIB_LIMIT["library-only"]])

/** One problem's entry in the attestation. */
export function problemEntry({ problem, qualifiedName, oldId, exportSha256, verdict, gate2Text }) {
  const migrated = verdict.migrated && verdict.migrated.length ? verdict.migrated : null
  return {
    id: problem.id,
    index: problem.index,
    name: qualifiedName || problem.name,
    verdict: verdict.ok ? "pass" : "fail",
    reason: verdict.reason,
    statementsIdentical: verdict.identical,
    translatedSha256: sha256(problem.statement),
    ...(verdict.via ? { via: verdict.via } : {}),
    ...(oldId ? { oldId } : {}),
    ...(exportSha256 ? { exportSha256 } : {}),
    ...(problem.port ? { port: problem.port.kind } : {}),
    ...(migrated ? { migrated } : {}),
    ...(verdict.bridge ? { bridge: verdict.bridge } : {}),
    ...(verdict.repaired ? { repairedInstanceArguments: verdict.repaired } : {}),
    ...(verdict.ok ? {} : { ...(verdict.missing && verdict.missing.length ? { missing: verdict.missing } : {}), detail: String(gate2Text || [verdict.msg, verdict.firstDiff ? `first difference: ${verdict.firstDiff}` : null, verdict.diff, ...(verdict.names ? [`names: ${verdict.names.join(",")}`] : []), ...(verdict.errors || [])].filter(Boolean).join(" | ")).replace(/\s+/g, " ").slice(0, 1800) }),
  }
}

export function buildAttestation({ subject, upstream, target, inputs, gate2, problems, run, exportMode = "library-only", checker = "daemon", interpretation = null }) {
  const counts = { total: problems.length, pass: 0, fail: 0 }
  const reasons = {}
  for (const p of problems) {
    counts[p.verdict]++
    if (p.verdict === "fail") reasons[p.reason] = (reasons[p.reason] || 0) + 1
  }
  return {
    schema: SCHEMA,
    kind: KIND,
    admissible: false,
    notice: "A statement attestation is evidence about statements. It is not a Tengoku record, carries no proof, and no bank, staging or intake step of Emissary reads it.",
    subject,
    upstream,
    target,
    inputs: { ...inputs, exportMode, checker },
    gate2,
    ...(interpretation ? { interpretation } : {}),
    run,
    counts: { ...counts, failReasons: reasons },
    limits: limitsFor(exportMode, checker),
    problems,
  }
}

/** Invariants every attestation this script writes must hold (the tests and the workflow's signing job both call it). Returns a list of what is wrong. */
export function checkAttestation(a) {
  const bad = []
  if (a?.schema !== SCHEMA) bad.push(`schema is ${a?.schema}`)
  if (a?.kind !== KIND) bad.push(`kind is ${a?.kind}`)
  if (a?.admissible !== false) bad.push("admissible is not false")
  if (!Array.isArray(a?.problems) || !a.problems.length) bad.push("no problems")
  const ids = new Set()
  for (const p of a?.problems || []) {
    if (ids.has(p.id)) bad.push(`${p.id} twice`)
    ids.add(p.id)
    if (!["pass", "fail"].includes(p.verdict)) bad.push(`${p.id}: verdict ${p.verdict}`)
    if (!/^[0-9a-f]{64}$/.test(p.translatedSha256 || "")) bad.push(`${p.id}: no translated hash`)
    if (p.verdict === "pass" && !/^[0-9a-f]{64}$/.test(p.exportSha256 || "")) bad.push(`${p.id}: a pass with no export hash`)
  }
  const table = new Set(a?.interpretation?.names || [])
  for (const p of a?.problems || []) {
    for (const n of p.migrated || []) if (!table.has(n)) bad.push(`${p.id}: migrated name ${n} is not in the interpretation table`)
  }
  if (a?.interpretation && !/^[0-9a-f]{64}$/.test(a.interpretation.sha256 || "")) bad.push("the interpretation table has no hash")
  if (a?.interpretation && typeof a.interpretation.text !== "string") bad.push("the interpretation table's text is not in the attestation")
  const pass = (a?.problems || []).filter((p) => p.verdict === "pass").length
  if (a?.counts?.pass !== pass) bad.push(`counts.pass ${a?.counts?.pass} != ${pass}`)
  if (a?.counts?.total !== (a?.problems || []).length) bad.push("counts.total differs from the problems")
  return bad
}

// ---- the batch checker (scripts/attest/attest-batch.mjs) ------------------------------------------------

const stripLeanComments = (text) => {
  let out = ""
  let depth = 0
  for (let i = 0; i < text.length; i++) {
    const two = text.slice(i, i + 2)
    if (two === "/-") (depth++, (i += 1))
    else if (two === "-/" && depth) (depth--, (i += 1))
    else if (depth) out += text[i] === "\n" ? "\n" : " "
    else if (two === "--") while (i < text.length && text[i] !== "\n") i++, (out += " ")
    else out += text[i]
  }
  return out
}

/** The qualified name of the theorem `bare` in a statement file, from its `namespace`/`end` lines; null when it is not declared exactly once. */
export function qualifiedTarget(statement, bare) {
  const ns = []
  const found = []
  for (const line of stripLeanComments(statement).split("\n")) {
    let m = line.match(/^\s*namespace\s+(\S+)/)
    if (m) {
      ns.push(m[1])
      continue
    }
    m = line.match(/^\s*end\s+(\S+)/)
    if (m && ns.length && ns[ns.length - 1] === m[1]) {
      ns.pop()
      continue
    }
    m = line.match(/^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s({[:]+)/)
    if (m && (m[1] === bare || m[1].endsWith(`.${bare}`))) found.push([...ns, m[1]].join("."))
  }
  return found.length === 1 ? found[0] : null
}

const leanString = (s) => s.replace(/\\/g, "\\\\").replace(/"/g, '\\"')

/** One problem's part of a check file: marker, the original's export, the translation in a section of its own (an `open` in it cannot reach the next problem), the check. */
export function problemBlock({ id, exportPath, statement, qualified, migration = null }) {
  // the migration table is elaborated AFTER the statement (its `algebraMap` would make the statement's own `algebraMap` ambiguous) and removed again before the next problem
  const mig = migration ? `#attest_env_save "${leanString(migration.names.join(","))}" "${leanString(Object.entries(migration.renames || {}).map(([a, b]) => `${a}=${b}`).join(","))}"\n${migration.text.trim()}\n` : ""
  const restore = migration ? `#attest_env_restore\n` : ""
  return `\n#attest_begin "${leanString(id)}"\n#tengoku_import_parse "${leanString(exportPath)}"\nsection\n${statement.trim()}\nend\n${mig}#gate2_statements "${leanString(qualified)}"\n${restore}`
}
export function checkFileText(treeImport, blocks, bridge = null) {
  return `import Lean\nimport ${treeImport}\nimport Vendor.Attest\n\nset_option maxErrors 100000\nset_option Elab.async false\n${bridge ? `#attest_bridge "${leanString(bridge)}"\n` : ""}${blocks.join("")}`
}

/** The log of one Lean process -> { id: text up to the next marker }. */
export function splitLog(text) {
  const out = {}
  const marks = [...text.matchAll(/ATTEST_BEGIN (\S+)/g)]
  marks.forEach((m, i) => {
    out[m[1]] = text.slice(m.index + m[0].length, i + 1 < marks.length ? marks[i + 1].index : undefined)
  })
  return out
}

/** One problem's segment -> { ok, reason, via, errors } (`ok: null` when the segment holds no verdict at all). */
export function readBatchVerdict(segment) {
  const flat = String(segment).replace(/\s+/g, " ")
  const errors = [...String(segment).matchAll(/^[^\n]*?: error: ([^\n]*)/gm)].map((m) => m[1].slice(0, 240)).slice(0, 3)
  const m = flat.match(/GATE2S_(PASS|FAIL) old=(\S+) new=(\S+)/)
  if (!m) return { ok: null, reason: errors.length ? "elaboration_error" : "no_verdict", via: null, errors }
  const kind = m[1]
  // the verdict's own words: up to the next marker of this message or of the next one
  const tail = flat.slice(m.index + m[0].length, m.index + m[0].length + 1500).split(/ GATE2[BS]_DIFF| GATE2S_| ATTEST_BEGIN/)[0]
  const via = (tail.match(/ via=(\w+)/) || [])[1]
  const reason = (tail.match(/ reason=(\w+)/) || [])[1]
  const msg = (tail.match(/ msg=(.*?)(?= names=|$)/) || [])[1]
  const names = (tail.match(/ names=(\S+)/) || [])[1]
  const diffAll = (flat.slice(m.index, m.index + 4000).match(/GATE2[BS]_DIFF (.*?) GATE2[BS]_END/) || [])[1]
  const [diff, firstDiff] = diffAll ? diffAll.split(" GATE2S_FIRSTDIFF ") : [undefined, undefined]
  const list = (tag) => ((flat.match(new RegExp(`GATE2S_${tag} old=\\S+ names=(\\S+) GATE2S_END`)) || [])[1] || "").split(",").filter(Boolean)
  const repaired = Number((flat.match(/GATE2S_REPAIRED old=\S+ count=(\d+) GATE2S_END/) || [])[1] || 0)
  const migrated = list("MIGRATED")
  const missing = list("MISSING")
  return { migrated, missing, repaired, ...(firstDiff && firstDiff !== "none" ? { firstDiff: firstDiff.slice(0, 1400) } : {}), ok: kind === "PASS", reason: kind === "PASS" ? "pass" : reason || "unspecified", via: via || null, errors, ...(msg ? { msg: msg.slice(0, 300) } : {}), ...(names ? { names: names.split(",").slice(0, 8) } : {}), ...(diff ? { diff: diff.slice(0, 500) } : {}) }
}

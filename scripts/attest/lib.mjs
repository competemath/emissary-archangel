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
export const limitsFor = (exportMode) => [...LIMITS_COMMON, MATHLIB_LIMIT[exportMode] || MATHLIB_LIMIT["library-only"]]

/** One problem's entry in the attestation. */
export function problemEntry({ problem, qualifiedName, oldId, exportSha256, verdict, gate2Text }) {
  return {
    id: problem.id,
    index: problem.index,
    name: qualifiedName || problem.name,
    verdict: verdict.ok ? "pass" : "fail",
    reason: verdict.reason,
    statementsIdentical: verdict.identical,
    translatedSha256: sha256(problem.statement),
    ...(oldId ? { oldId } : {}),
    ...(exportSha256 ? { exportSha256 } : {}),
    ...(problem.port ? { port: problem.port.kind } : {}),
    ...(verdict.ok ? {} : { detail: String(gate2Text || "").replace(/\s+/g, " ").slice(0, 600) }),
  }
}

export function buildAttestation({ subject, upstream, target, inputs, gate2, problems, run, exportMode = "library-only" }) {
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
    inputs: { ...inputs, exportMode },
    gate2,
    run,
    counts: { ...counts, failReasons: reasons },
    limits: limitsFor(exportMode),
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
  const pass = (a?.problems || []).filter((p) => p.verdict === "pass").length
  if (a?.counts?.pass !== pass) bad.push(`counts.pass ${a?.counts?.pass} != ${pass}`)
  if (a?.counts?.total !== (a?.problems || []).length) bad.push("counts.total differs from the problems")
  return bad
}

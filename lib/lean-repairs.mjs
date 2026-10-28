// What the mechanical pass does to an original's text before it is compiled, and asks of the tree's content lint.
//
// Everything here is deterministic and runs without a model. Nothing in it decides that a translation is right: the compiler (Leak IV) and Gate 2 do, on the bytes that come out.
//
//   policyCheck(text)           the violations of the tree's content lint (scripts/bump/lint/allowlist.py, the one the bundle lane runs), [] when the text may be banked
//   policyRepair(text)          the same, after the inert commands the lint refuses were taken out (scripts/bump/inert_commands.py): { text, removed, violations }
//   dropDuplicatedTailAttributes(prefix, target)
//                               the attribute lines that end `prefix` and that `target` repeats are taken out of the prefix
//
// The lint used to be a second, hand-kept copy in the bridge. It had drifted (eight options the tree allows were missing from it) and it could not see what the tree sees. There is one now.

// The generation of the mechanical pass's remedies. A ledger row of an entry that went to the agent says which generation tried it (lib/ledger-row.mjs), and a mechanical run takes
// again every such entry whose row is from an OLDER generation (lib/ledger-settle.mjs): when a remedy is added or improved here, the entries it could unlock are tried again by the next
// run, with nobody having to know which ones. Raise it with every change that lets an entry the mechanical pass used to give up on get through. 2: inert commands, the one lint,
// the repeated attribute at the junction (2026-10-28).
export const MECHANICS_VERSION = 2

import { execFile } from "node:child_process"
import { createHash } from "node:crypto"
import { fileURLToPath } from "node:url"

const CLI = fileURLToPath(new URL("../scripts/bump/lint_cli.py", import.meta.url))
const PYTHON = process.env.EMISSARY_PYTHON || "python3"
const TIMEOUT_MS = 10 * 60 * 1000 // a 3 MB candidate takes about 5 s; a hung interpreter must not hang the run
const CACHE_MAX = 64
const cache = new Map()

function run(mode, text) {
  return new Promise((resolve, reject) => {
    const child = execFile(PYTHON, ["-I", CLI, mode], { maxBuffer: 1 << 29, timeout: TIMEOUT_MS }, (err, stdout, stderr) => {
      if (err) return reject(new Error(`the content lint could not run (${PYTHON} ${CLI} ${mode}): ${String(stderr || err.message).slice(0, 400)}`))
      try {
        resolve(JSON.parse(stdout))
      } catch (e) {
        reject(new Error(`the content lint answered something that is not JSON: ${String(stdout).slice(0, 200)}`))
      }
    })
    child.stdin.on("error", () => {}) // the process may exit before it reads everything; the callback has the reason
    child.stdin.end(JSON.stringify({ text }))
  })
}

async function ask(mode, text) {
  const key = mode + ":" + createHash("sha256").update(text).digest("hex")
  if (cache.has(key)) return cache.get(key)
  const answer = await run(mode, text) // a failure to ask is an error, never an empty list of violations: a text nobody could judge must not be banked
  if (cache.size >= CACHE_MAX) cache.delete(cache.keys().next().value)
  cache.set(key, answer)
  return answer
}

export async function policyCheck(text) {
  return (await ask("check", String(text ?? ""))).violations
}

export async function policyRepair(text) {
  const a = await ask("repair", String(text ?? ""))
  return { text: a.text, removed: a.removed, violations: a.violations }
}

// ---- the junction between a file's prefix and the entry's own text -------------------------------------------------------------------------------------------------------------
// The prefix is the file as far as the line the entry starts at; the entry's recorded statement starts with its own attribute lines (`@[simp]`), and when those sit on the line(s)
// above the declaration they are in BOTH: `/-- doc -/ @[simp] <blank> @[simp] theorem …`. Lean refuses that ("unexpected token '/--'; expected 'lemma'"), and the refusal is at a
// line inside the prefix, so the file's shared prefix was marked broken and every later entry of the file went to the agent without a compile (stafford38-formal: 54 entries
// directly, and the cascade for the rest of their files).

const ATTR_LINE = /^[ \t]*@\[[^\n]*\][ \t]*$/

function balancedAttribute(line) {
  let depth = 0
  for (const ch of line) {
    if (ch === "[") depth++
    else if (ch === "]") depth--
    if (depth < 0) return false
  }
  return depth === 0
}

const isAttributeLine = (l) => ATTR_LINE.test(l) && balancedAttribute(l)

export function dropDuplicatedTailAttributes(prefix, target) {
  const lead = []
  for (const l of String(target).split("\n")) {
    if (!isAttributeLine(l)) break
    lead.push(l.trim())
  }
  if (!lead.length) return prefix
  const lines = String(prefix).split("\n")
  // the run of attribute and blank lines that ends the prefix (they all belong to the declaration that follows, which is the entry)
  let end = lines.length
  while (end > 0 && lines[end - 1].trim() === "") end--
  let start = end
  while (start > 0 && (isAttributeLine(lines[start - 1]) || lines[start - 1].trim() === "")) start--
  // every line of the run that the entry also carries goes (a set, not a count: the entry keeps its own, and a second copy in the prefix would make the result depend on how often the repair was applied)
  const carried = new Set(lead)
  const keep = []
  for (let i = start; i < end; i++) if (!(isAttributeLine(lines[i]) && carried.has(lines[i].trim()))) keep.push(lines[i])
  if (keep.length === end - start) return prefix
  return [...lines.slice(0, start), ...keep, ...lines.slice(end)].join("\n")
}

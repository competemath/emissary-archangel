// node scripts/check-lint-drift.mjs [--ref main] [--source auto|gh|raw] [--upstream-dir DIR] [--pinned-dir DIR] [--summary-file FILE]
//
// Is the content lint pinned in scripts/bump/lint/ still the one competemath/tengoku has on main? The pinned copy is four files; byte for byte they must be tengoku's:
//
//   pinned (scripts/bump/lint/)  tengoku
//   allowlist.py                 scripts/ci/allowlist.py
//   allowed-options.json         schemas/allowed-options.json
//   lean_lex.py                  scripts/ci/lean_lex.py
//   command-keywords.json        schemas/command-keywords.json
//
// A hand-kept copy has drifted before (stafford38-formal, 2026-10-27: it was missing 8 options the tree allows, and 2,089 of 2,467 entries were refused for it). This script is how the next
// drift is found by a machine instead: it prints which file differs and how (the options added or removed, the definitions added or removed, the lines), and exits
//   0  every file is identical            1  at least one differs (or is missing on one side)            2  tengoku could not be read (nothing is known)
// No AI and no network beyond the four reads: with a token in the environment (GH_TOKEN / GITHUB_TOKEN) they go through `gh api`, otherwise through raw.githubusercontent.com; both are
// pinned to the commit `ref` pointed at when the run began (no commit, no read), so the four files cannot come from two different commits. A file tengoku no longer has (404 at that commit) is drift. --upstream-dir compares with a folder laid out like tengoku (offline).
import { execFileSync } from "node:child_process"
import { createHash } from "node:crypto"
import { existsSync, readFileSync, statSync, writeFileSync } from "node:fs"
import { dirname, join, resolve } from "node:path"
import { fileURLToPath } from "node:url"

export const REPO = "competemath/tengoku"
export const FILES = [
  { name: "allowlist.py", upstream: "scripts/ci/allowlist.py", kind: "py" },
  { name: "allowed-options.json", upstream: "schemas/allowed-options.json", kind: "options" },
  { name: "lean_lex.py", upstream: "scripts/ci/lean_lex.py", kind: "py" },
  { name: "command-keywords.json", upstream: "schemas/command-keywords.json", kind: "keywords" },
]
const MAX_SUMMARY = 60000 // a GitHub issue body holds 65,536 characters
const MAX_LINES = 24 // changed lines shown per file

const bytes = (x) => (x === undefined || x === null ? null : Buffer.isBuffer(x) ? x : Buffer.from(x, "utf8"))
const sha = (b) => createHash("sha256").update(b).digest("hex").slice(0, 12)
const clip = (s, n = 160) => (s.length > n ? `${s.slice(0, n)}…` : s).replaceAll("```", "'''") // a fence in a changed line must not close the one it is shown in
const list = (xs) => xs.map((x) => `\`${x}\``).join(", ")

function jsonOf(b) {
  try {
    return { value: JSON.parse(b.toString("utf8")) }
  } catch (e) {
    return { error: e.message }
  }
}
const setDiff = (a, b) => [...b].filter((x) => !a.has(x)).sort() // in b, not in a

// the lines that differ, by the longest common subsequence of the two texts (files of a few hundred lines; a huge pair falls back to a comparison of the sets of lines)
export function lineDiff(a, b) {
  const x = a.split("\n"), y = b.split("\n")
  if (x.length * y.length > 4_000_000) {
    const sx = new Set(x), sy = new Set(y)
    return { removed: x.filter((l) => !sy.has(l)).map((l) => ({ text: l })), added: y.filter((l) => !sx.has(l)).map((l) => ({ text: l })) }
  }
  const n = x.length, m = y.length
  const t = Array.from({ length: n + 1 }, () => new Uint32Array(m + 1))
  for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) t[i][j] = x[i] === y[j] ? t[i + 1][j + 1] + 1 : Math.max(t[i + 1][j], t[i][j + 1])
  const removed = [], added = []
  let i = 0, j = 0
  while (i < n && j < m) {
    if (x[i] === y[j]) { i++; j++ } else if (t[i + 1][j] >= t[i][j + 1]) removed.push({ line: i + 1, text: x[i++] }); else added.push({ line: j + 1, text: y[j++] })
  }
  while (i < n) removed.push({ line: i + 1, text: x[i++] })
  while (j < m) added.push({ line: j + 1, text: y[j++] })
  return { removed, added }
}

const defsOf = (text) => new Set([...text.matchAll(/^(?:def|class) ([A-Za-z_][A-Za-z0-9_]*)|^([A-Z_][A-Z0-9_]*) *[:=]/gm)].map((m) => m[1] || m[2]))

// a parsed file of the shape the comparison reads: an object whose `field` (allowed / commands), when there, is a list. `null`, a number or a list parse as JSON and are not that.
function shapeProblem(parsed, field, who) {
  if (parsed.error) return `not valid JSON in ${who}: ${parsed.error}`
  const v = parsed.value
  if (v === null || typeof v !== "object" || Array.isArray(v)) return `${who} is JSON but not an object (${v === null ? "null" : Array.isArray(v) ? "a list" : typeof v}): the "${field}" list cannot be read`
  if (field in v && !Array.isArray(v[field])) return `"${field}" is not a list in ${who}`
  return null
}

function describe(kind, p, u) {
  const out = []
  if (kind === "options" || kind === "keywords") {
    const field = kind === "options" ? "allowed" : "commands"
    const a = jsonOf(p), b = jsonOf(u)
    const problem = shapeProblem(a, field, "the pinned copy") || shapeProblem(b, field, "tengoku")
    if (problem) return [problem, ...textDetails(p, u)]
  }
  if (kind === "options") {
    const a = jsonOf(p), b = jsonOf(u)
    const pa = new Set(a.value.allowed || []), ua = new Set(b.value.allowed || [])
    const added = setDiff(pa, ua), removed = setDiff(ua, pa)
    if (added.length) out.push(`options tengoku allows that the pinned copy lacks (${added.length}): ${list(added)}`)
    if (removed.length) out.push(`options the pinned copy allows that tengoku no longer has (${removed.length}): ${list(removed)}`)
    if (a.value.$comment !== b.value.$comment) out.push("the \"$comment\" differs")
    const other = Object.keys({ ...a.value, ...b.value }).filter((k) => !["allowed", "$comment"].includes(k) && JSON.stringify(a.value[k]) !== JSON.stringify(b.value[k]))
    if (other.length) out.push(`other fields differ: ${list(other)}`)
  } else if (kind === "keywords") {
    const a = jsonOf(p), b = jsonOf(u)
    const pa = new Set(a.value.commands || []), ua = new Set(b.value.commands || [])
    const added = setDiff(pa, ua), removed = setDiff(ua, pa)
    if (added.length) out.push(`command keywords tengoku has that the pinned copy lacks (${added.length}): ${list(added)}`)
    if (removed.length) out.push(`command keywords the pinned copy has that tengoku no longer has (${removed.length}): ${list(removed)}`)
    if (a.value.lean !== b.value.lean) out.push(`the Lean version differs: pinned ${a.value.lean}, tengoku ${b.value.lean}`)
    if (a.value.about !== b.value.about) out.push("the \"about\" text differs")
    const other = Object.keys({ ...a.value, ...b.value }).filter((k) => !["commands", "lean", "about"].includes(k) && JSON.stringify(a.value[k]) !== JSON.stringify(b.value[k]))
    if (other.length) out.push(`other fields differ: ${list(other)}`)
  } else {
    const pt = p.toString("utf8"), ut = u.toString("utf8")
    const pd = defsOf(pt), ud = defsOf(ut)
    const added = setDiff(pd, ud), removed = setDiff(ud, pd)
    if (added.length) out.push(`definitions in tengoku that the pinned copy lacks: ${list(added)}`)
    if (removed.length) out.push(`definitions in the pinned copy that tengoku no longer has: ${list(removed)}`)
  }
  out.push(...textDetails(p, u))
  return out
}

// whatever the kind: the lines (and the case where only the bytes between the lines differ)
function textDetails(p, u) {
  const out = []
  const pt = p.toString("utf8"), ut = u.toString("utf8")
  if (pt.replace(/\r\n/g, "\n").replace(/[ \t]+$/gm, "").trimEnd() === ut.replace(/\r\n/g, "\n").replace(/[ \t]+$/gm, "").trimEnd()) {
    out.push("differs only in line endings, trailing whitespace or the final newline")
  } else {
    const { removed, added } = lineDiff(pt, ut)
    out.push(`lines: ${added.length} only in tengoku (+), ${removed.length} only in the pinned copy (-)`)
    const shown = [...removed.map((r) => `- ${r.line ? `${r.line}: ` : ""}${clip(r.text)}`), ...added.map((r) => `+ ${r.line ? `${r.line}: ` : ""}${clip(r.text)}`)]
    out.push("```diff", ...shown.slice(0, MAX_LINES), ...(shown.length > MAX_LINES ? [`… ${shown.length - MAX_LINES} more changed lines`] : []), "```")
  }
  return out
}

// pinned, upstream: { name: Buffer | string | undefined }. Pure: no file, no network.
export function compare(pinned, upstream, files = FILES) {
  const results = files.map(({ name, upstream: path, kind }) => {
    const p = bytes(pinned[name]), u = bytes(upstream[name])
    if (p === null && u === null) return { name, path, status: "missing-both", details: ["absent on both sides"] }
    if (p === null) return { name, path, status: "missing-pinned", details: [`the pinned copy has no ${name}`] }
    if (u === null) return { name, path, status: "missing-upstream", details: [`tengoku has no ${path}`] }
    if (p.equals(u)) return { name, path, status: "same", details: [] }
    return { name, path, status: "differs", bytes: [p.length, u.length], sha: [sha(p), sha(u)], details: describe(kind, p, u) }
  })
  return { drift: results.some((r) => r.status !== "same"), files: results }
}

export function render(result, { ref = "main", commit = null } = {}) {
  const at = commit ? `${ref} (${commit})` : ref
  const head = result.drift
    ? `The content lint pinned in \`scripts/bump/lint/\` differs from \`${REPO}\` ${at}: ${result.files.filter((f) => f.status !== "same").length} of ${result.files.length} files.`
    : `The content lint pinned in \`scripts/bump/lint/\` is identical to \`${REPO}\` ${at} (${result.files.length} files, byte for byte).`
  const lines = [head, ""]
  for (const f of result.files) {
    lines.push(`### ${f.name} — ${f.status === "same" ? "identical" : f.status === "differs" ? `differs (${f.bytes[0]} -> ${f.bytes[1]} bytes, sha256 ${f.sha[0]} -> ${f.sha[1]})` : f.status.replace("-", " ")}`)
    if (f.status !== "same") lines.push(`tengoku: \`${f.path}\``, "", ...f.details.map((d) => (d.startsWith("```") || d.startsWith("- ") || d.startsWith("+ ") || /^[-+] \d+: /.test(d) || d.startsWith("…") ? d : `- ${d}`)))
    lines.push("")
  }
  if (result.drift) lines.push("Refresh: copy the four files again (see scripts/bump/lint/README.md), run the bump tests, and commit them together.")
  const text = lines.join("\n")
  return text.length > MAX_SUMMARY ? `${text.slice(0, MAX_SUMMARY)}\n\n… (cut: the summary is longer than an issue holds)` : text
}

// ---- reading tengoku ----------------------------------------------------------------
const REF_OK = /^[A-Za-z0-9._/-]+$/
const COMMIT_OK = /^[0-9a-f]{40}$/

// source: auto (gh api when a token is in the environment, else raw), gh, raw. `run` and `fetchImpl` are injectable for the tests.
export async function fetchUpstream({ ref = "main", source = "auto", env = process.env, run = execFileSync, fetchImpl = globalThis.fetch, files = FILES, warn = (m) => process.stderr.write(m) } = {}) {
  if (!REF_OK.test(ref) || ref.includes("..")) throw new Error(`ref is a branch, tag or commit name, not ${JSON.stringify(ref)}`)
  if (!["auto", "gh", "raw"].includes(source)) throw new Error(`source is auto, gh or raw, not ${source}`)
  const token = env.GH_TOKEN || env.GITHUB_TOKEN
  const viaGh = async () => {
    const gh = (args) => run("gh", args, { env: { ...env, GH_TOKEN: token }, maxBuffer: 64 * 1024 * 1024, stdio: ["ignore", "pipe", "pipe"] })
    const commit = String(gh(["api", `repos/${REPO}/commits/${ref}`, "--jq", ".sha"])).trim()
    if (!COMMIT_OK.test(commit)) throw new Error(`gh api gave no commit for ${ref}`)
    const out = {}
    for (const f of files) {
      try {
        out[f.name] = Buffer.from(gh(["api", `repos/${REPO}/contents/${f.upstream}?ref=${commit}`, "-H", "Accept: application/vnd.github.raw+json"]))
      } catch (e) {
        // the commit is resolved, so a 404 for the path is a file tengoku no longer has (drift); any other failure is a read error and says nothing about drift
        if (!/HTTP 404|Not Found/i.test(`${e.stderr || ""}${e.message || ""}`)) throw e
        out[f.name] = undefined
      }
    }
    return { commit, files: out, via: "gh api" }
  }
  const viaRaw = async () => {
    // the four files are read at ONE commit or not at all: a mutable ref could move between the requests, and the report could not say which snapshot it describes
    const lookup = async (auth) => {
      const r = await fetchImpl(`https://api.github.com/repos/${REPO}/commits/${encodeURIComponent(ref)}`, { headers: { Accept: "application/vnd.github.sha", ...(auth ? { Authorization: `Bearer ${token}` } : {}) } })
      const t = r.ok ? (await r.text()).trim() : ""
      return { commit: COMMIT_OK.test(t) ? t : null, why: r.ok ? "an answer that is not a commit" : `HTTP ${r.status}`, status: r.status }
    }
    let commit = null, why = ""
    try {
      let got = await lookup(Boolean(token))
      // the token that made gh fail (expired, wrong scope) is refused here too (401): the repository is public, so ask again as anyone
      if (!got.commit && token && got.status === 401) got = await lookup(false)
      ;({ commit, why } = got)
    } catch (e) {
      why = String(e.message).split("\n")[0]
    }
    if (!commit) throw new Error(`no commit for ${ref} could be resolved (${why}); the files are not read at a name that can move`)
    const out = {}
    for (const f of files) {
      const r = await fetchImpl(`https://raw.githubusercontent.com/${REPO}/${commit}/${f.upstream}`)
      if (r.status === 404) { out[f.name] = undefined; continue } // at a resolved commit a 404 is a file tengoku does not have: drift
      if (!r.ok) throw new Error(`${f.upstream}: HTTP ${r.status}`)
      out[f.name] = Buffer.from(await r.arrayBuffer())
    }
    return { commit, files: out, via: "raw.githubusercontent.com" }
  }
  if (source === "gh" || (source === "auto" && token)) {
    try {
      return await viaGh()
    } catch (e) {
      if (source === "gh") throw e
      warn(`gh api did not work (${String(e.message).split("\n")[0]}); reading raw.githubusercontent.com instead\n`)
    }
  }
  return viaRaw()
}

export function readDir(dir, files = FILES, key = "name") {
  const out = {}
  for (const f of files) {
    const p = join(dir, key === "name" ? f.name : f.upstream)
    if (existsSync(p)) out[f.name] = readFileSync(p)
  }
  return out
}

function parseArgs(argv) {
  const o = { ref: "main", source: "auto" }
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]
    const need = () => { if (argv[i + 1] === undefined) throw new Error(`${a} needs a value`); return argv[++i] }
    if (a === "--ref") o.ref = need()
    else if (a === "--source") o.source = need()
    else if (a === "--upstream-dir") o.upstreamDir = need()
    else if (a === "--pinned-dir") o.pinnedDir = need()
    else if (a === "--summary-file") o.summaryFile = need()
    else throw new Error(`unknown argument ${a}`)
  }
  return o
}

async function main() {
  const here = dirname(fileURLToPath(import.meta.url))
  let o, up
  try {
    o = parseArgs(process.argv.slice(2))
    if (o.upstreamDir && !statSync(resolve(o.upstreamDir), { throwIfNoEntry: false })?.isDirectory()) throw new Error(`${o.upstreamDir} is not a folder`)
    up = o.upstreamDir ? { files: readDir(resolve(o.upstreamDir), FILES, "upstream"), commit: null, via: `the folder ${o.upstreamDir}` } : await fetchUpstream({ ref: o.ref, source: o.source })
  } catch (e) {
    console.error(`::error::could not read tengoku's lint: ${e.message}`)
    process.exit(2)
  }
  const pinned = readDir(resolve(o.pinnedDir || join(here, "bump", "lint")))
  const result = compare(pinned, up.files)
  const text = render(result, { ref: o.ref, commit: up.commit })
  console.log(`(read through ${up.via})`)
  console.log(text)
  if (o.summaryFile) writeFileSync(o.summaryFile, text + "\n")
  if (result.drift) console.error(`::error::the pinned content lint differs from ${REPO} ${o.ref}: ${result.files.filter((f) => f.status !== "same").map((f) => f.name).join(", ")}`)
  process.exit(result.drift ? 1 : 0)
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) await main()

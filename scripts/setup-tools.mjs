// Which tools produced a library's setup record (data/exports/<key>/setup.ci.json, setup.json): the Lean and Lake of the library's toolchain, elan, the lean4export that wrote the
// exports (its commit and the patch put on it), node, and the runner image. Two runs of the same library that export differently now have a difference on file to explain them
// (the toolchain is pinned by the library, but elan, lean4export's patch, and the image under it are not part of the registry).
// Nothing here can fail a setup: a tool that cannot be asked, or whose answer is not plain text, is `null`.
//
//   collectTools({ exec, env, nodeVersion, toolchain, l4eDir, patchRecorded })  -> { lean, lake, elan, lean4export, node, runnerImage }
//   mergeTools([tools, ...])                                                  -> the same shape; a field the inputs disagree on holds every value, " | " apart
import { createHash } from "node:crypto"

export const TOOL_FIELDS = ["lean", "lake", "elan", "lean4export", "node", "runnerImage"]
const MAX = 200

// one printable line, no longer than a record needs
export function plain(s) {
  if (typeof s !== "string") return null
  const line = s.split("\n").map((l) => l.trim()).find(Boolean)
  if (!line) return null
  const clean = line.replace(/[^\x20-\x7e]/g, "?")
  return clean.length > MAX ? clean.slice(0, MAX) : clean
}

// "Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 1a2b3c4d5e6f, Release)" -> "4.34.0-rc2 (commit 1a2b3c4d5e6f, x86_64-unknown-linux-gnu)"
export function parseLean(out) {
  const line = plain(out)
  const m = line && line.match(/version ([0-9A-Za-z.+-]+), ([\w.-]+), commit ([0-9a-f]+)/)
  return m ? `${m[1]} (commit ${m[3]}, ${m[2]})` : line
}
// "Lake version 5.0.0-1a2b3c (Lean version 4.34.0-rc2)" -> "5.0.0-1a2b3c"
export function parseLake(out) {
  const line = plain(out)
  const m = line && line.match(/^Lake version (\S+)/)
  return m ? m[1] : line
}
// "elan 4.1.2 (a1b2c3d 2026-08-01)" -> "4.1.2 (a1b2c3d 2026-08-01)"
export function parseElan(out) {
  const line = plain(out)
  const m = line && line.match(/^elan (.+)$/)
  return m ? m[1] : line
}
// GitHub's runners set ImageOS (ubuntu26) and ImageVersion (20261012.163.1); anywhere else both are absent and the answer is null, not a guess
export function runnerImage(env) {
  const ok = (v) => (typeof v === "string" && /^[A-Za-z0-9._-]{1,60}$/.test(v) ? v : null)
  const os = ok(env.ImageOS), version = ok(env.ImageVersion)
  return os && version ? `${os}/${version}` : version || os || null
}

export async function collectTools({ exec, env = {}, nodeVersion = null, toolchain, l4eDir, patchRecorded = null }) {
  const ask = async (cmd, args) => {
    try {
      return await exec(cmd, args)
    } catch {
      return null
    }
  }
  const tc = typeof toolchain === "string" && /^[\w./:+-]+$/.test(toolchain) ? toolchain : null
  const [lean, lake, elan] = await Promise.all([
    tc ? ask("elan", ["run", tc, "lean", "--version"]) : null,
    tc ? ask("elan", ["run", tc, "lake", "--version"]) : null,
    ask("elan", ["--version"]),
  ])
  let l4e = null
  const head = l4eDir ? plain(await ask("git", ["-C", l4eDir, "rev-parse", "HEAD"])) : null
  if (head && /^[0-9a-f]{40}$/.test(head)) {
    // the fingerprint of the patch the exporter was BUILT with (recorded next to it when it was built), not of the patch file as it is now: a cached exporter outlives a change of the script
    const patch = typeof patchRecorded === "string" && /^[0-9a-f]{12}$/.test(patchRecorded.trim()) ? `batch patch ${patchRecorded.trim()}` : "patch not recorded"
    l4e = `${head.slice(0, 12)} + ${patch}`
  }
  return {
    lean: parseLean(lean),
    lake: parseLake(lake),
    elan: parseElan(elan),
    lean4export: l4e,
    node: plain(nodeVersion),
    runnerImage: runnerImage(env),
  }
}

// The first 12 hex digits of the sha256 of the patch script (scripts/patch-lean4export.py); null for no script
export const patchFingerprint = (text) => (typeof text === "string" ? createHash("sha256").update(text).digest("hex").slice(0, 12) : null)

// What to do with the lean4export a cache directory holds. `recorded` is the fingerprint written when it was built (null: built before it was recorded, or by hand), `current` that of the patch script now.
//   build          there is none
//   rebuild        it predates --batch (its exports would fall back to one process per module)
//   rebuild-clean  it was built with another patch than the script now has: from a fresh clone, since the patch is idempotent and would not replace the old one on a patched tree
//   reuse          otherwise (an unrecorded fingerprint is not a reason to spend 40 minutes; the record then says "patch not recorded")
export function exporterAction({ binExists, batchable, recorded, current }) {
  if (!binExists) return "build"
  if (!batchable) return "rebuild"
  if (typeof recorded === "string" && recorded.trim() && current && recorded.trim() !== current) return "rebuild-clean"
  return "reuse"
}

// The records of the shards of one library: where they agree the field is that value; where they do not (a shard on another image, say) every value is kept, so that the difference is on file.
export function mergeTools(list) {
  const have = list.filter((t) => t && typeof t === "object")
  if (!have.length) return null
  const out = {}
  for (const f of TOOL_FIELDS) {
    const values = [...new Set(have.map((t) => plain(t[f])).filter(Boolean))].sort()
    out[f] = values.length ? values.join(" | ") : null
  }
  return out
}

// The root a repository-relative source path belongs to: the first directory, or for a file at the top of the repository the module it is (`PrimeGaps186.lean`, the root
// `PrimeGaps186`). OpenAI's single-file proofs have every record in such a file; compared as `PrimeGaps186.lean` they all fell outside the roots.
export const rootOfRepoPath = (p) => {
  const parts = String(p).split("/")
  return parts.length > 1 ? parts[0] : parts[0].replace(/\.lean$/, "")
}

// A download that fails is tried again, each wait longer than the last: `attempt` answers { code }, and the last answer is returned. aintlib (9 Nov 2026): Lean's download server answered 504 once and the
// whole first build round of the setup ended after 25 seconds; a second such answer would have read as "no progress" and stopped the setup.
// Only `shouldRetry` answers are tried again: a toolchain that does not exist will not exist in a minute, and an install that hung for its 30 minutes must not hang five times inside a 300-minute build.
export const transientDownload = (r) => r.code !== 124 && /status code: 5\d\d|ssl|tls|connection|network|reset by peer|timed? ?out/i.test(r.tail ?? "")
export async function retrying(attempt, { tries = 5, waitMs = 20000, sleep = (ms) => new Promise((r) => setTimeout(r, ms)), warn = () => {}, shouldRetry = () => true } = {}) {
  let answer
  for (let i = 1; i <= tries; i++) {
    answer = await attempt()
    if (answer.code === 0 || !shouldRetry(answer)) return answer
    if (i < tries) {
      warn(`try ${i} of ${tries} failed: again in ${(i * waitMs) / 1000} s`)
      await sleep(i * waitMs)
    }
  }
  return answer
}

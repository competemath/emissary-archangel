// Which tools produced a library's setup record (data/exports/<key>/setup.ci.json, setup.json): the Lean and Lake of the library's toolchain, elan, the lean4export that wrote the
// exports (its commit and the patch put on it), node, and the runner image. Two runs of the same library that export differently now have a difference on file to explain them
// (the toolchain is pinned by the library, but elan, lean4export's patch, and the image under it are not part of the registry).
// Nothing here can fail a setup: a tool that cannot be asked, or whose answer is not plain text, is `null`.
//
//   collectTools({ exec, env, nodeVersion, toolchain, l4eDir, patchScript })  -> { lean, lake, elan, lean4export, node, runnerImage }
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

export async function collectTools({ exec, env = {}, nodeVersion = null, toolchain, l4eDir, patchScript = null }) {
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
    const patch = patchScript === null ? "no patch script" : `batch patch ${createHash("sha256").update(patchScript).digest("hex").slice(0, 12)}`
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

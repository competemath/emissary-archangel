// node scripts/test-setup-tools.mjs — the tools recorded in a setup record (scripts/setup-tools.mjs; exits 1 on a failure). No Lean, no network: the tools are asked through a stand-in.
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { TOOL_FIELDS, collectTools, mergeTools, parseElan, parseLake, parseLean, plain, runnerImage } from "./setup-tools.mjs"

let bad = 0
const check = (name, ok, got) => {
  if (!ok) { bad++; console.log("FAIL", name, JSON.stringify(got)) } else console.log("ok", name)
}
let seed = 99
const rnd = (n) => {
  seed = (seed + 0x6d2b79f5) | 0
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed)
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
  return ((t ^ (t >>> 14)) >>> 0) % n
}

check("lean: version, commit and platform from the one line Lean prints", parseLean("Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 1a2b3c4d5e6f, Release)\n") === "4.34.0-rc2 (commit 1a2b3c4d5e6f, x86_64-unknown-linux-gnu)", parseLean("Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 1a2b3c4d5e6f, Release)"))
check("lake and elan: the version; an answer in another shape is kept as the line it is", parseLake("Lake version 5.0.0-1a2b3c (Lean version 4.34.0-rc2)") === "5.0.0-1a2b3c" && parseElan("elan 4.1.2 (a1b2c3d 2026-08-01)") === "4.1.2 (a1b2c3d 2026-08-01)" && parseLake("something else\nsecond line") === "something else", [parseLake("something else"), parseElan("x")])
check("an answer that is not text, or empty, is null", plain(null) === null && plain(undefined) === null && plain(5) === null && plain("") === null && plain("\n  \n") === null && parseLean(null) === null && parseLake("") === null, null)
let sane = true
for (let i = 0; i < 300; i++) {
  const junk = Array.from({ length: rnd(500) }, () => String.fromCharCode(rnd(3) === 0 ? 0x4e00 + rnd(200) : rnd(128))).join("")
  const p = plain(junk)
  sane &&= p === null || (p.length <= 200 && !/[^\x20-\x7e]/.test(p) && !p.includes("\n"))
}
check("whatever a tool prints, what is recorded is one printable line of at most 200 characters (300 random outputs)", sane, null)
check("the runner image comes from ImageOS and ImageVersion, from nothing else, and null off a GitHub runner", runnerImage({ ImageOS: "ubuntu26", ImageVersion: "20261012.163.1" }) === "ubuntu26/20261012.163.1" && runnerImage({ ImageVersion: "1.2" }) === "1.2" && runnerImage({}) === null && runnerImage({ ImageVersion: "a b; rm -rf" }) === null && runnerImage({ ImageOS: "x".repeat(80), ImageVersion: "1" }) === "1", [runnerImage({ ImageVersion: "a b" })])

const TC = "leanprover/lean4:v4.34.0-rc2"
const SHA = "0123456789abcdef0123456789abcdef01234567"
const answers = (over = {}) => (cmd, args) => {
  const key = `${cmd} ${args.join(" ")}`
  const table = {
    [`elan run ${TC} lean --version`]: "Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 1a2b3c4d5e6f, Release)\n",
    [`elan run ${TC} lake --version`]: "Lake version 5.0.0-1a2b3c (Lean version 4.34.0-rc2)\n",
    "elan --version": "elan 4.1.2 (a1b2c3d 2026-08-01)\n",
    "git -C /l4e rev-parse HEAD": SHA + "\n",
    ...over,
  }
  if (!(key in table)) return Promise.reject(new Error(`unexpected ${key}`))
  if (table[key] instanceof Error) return Promise.reject(table[key])
  return Promise.resolve(table[key])
}
const all = await collectTools({ exec: answers(), env: { ImageOS: "ubuntu26", ImageVersion: "20261012.163.1" }, nodeVersion: "v22.15.0", toolchain: TC, l4eDir: "/l4e", patchScript: "patch text" })
check("collectTools: every field, and only the fields there are", JSON.stringify(Object.keys(all)) === JSON.stringify(TOOL_FIELDS) && all.lean.startsWith("4.34.0-rc2") && all.lake === "5.0.0-1a2b3c" && all.elan.startsWith("4.1.2") && all.node === "v22.15.0" && all.runnerImage === "ubuntu26/20261012.163.1", all)
check("lean4export: the first 12 characters of its commit and the hash of the patch put on it", /^0123456789ab \+ batch patch [0-9a-f]{12}$/.test(all.lean4export), all.lean4export)
const other = await collectTools({ exec: answers(), env: {}, nodeVersion: "v22.15.0", toolchain: TC, l4eDir: "/l4e", patchScript: "patch text, edited" })
check("a different patch script is a different record (so a change of the patch is on file)", other.lean4export !== all.lean4export && other.runnerImage === null, [other.lean4export, all.lean4export])
const nothing = await collectTools({ exec: () => Promise.reject(new Error("no such program")), env: {}, nodeVersion: undefined, toolchain: TC, l4eDir: "/l4e" })
check("tools that cannot be asked are null, nothing throws", Object.values(nothing).every((v) => v === null), nothing)
const partial = await collectTools({ exec: answers({ "elan --version": new Error("x") }), env: {}, nodeVersion: "v22", toolchain: TC, l4eDir: "/l4e" })
check("one tool failing does not take the others with it", partial.elan === null && partial.lean !== null && partial.lake !== null && partial.lean4export !== null, partial)
const hostile = await collectTools({ exec: answers({ [`elan run ${TC} lean --version`]: "x".repeat(5000) + "\n", "git -C /l4e rev-parse HEAD": "not a commit\n" }), env: {}, toolchain: TC, l4eDir: "/l4e" })
check("a long answer is cut, and a rev-parse that is not a commit records no lean4export", hostile.lean.length === 200 && hostile.lean4export === null, hostile.lean4export)
const badToolchain = []
for (const t of ["", "a b", "x;rm -rf /", "$(id)", undefined, null]) {
  let called = false
  const r = await collectTools({ exec: (c, a) => { called ||= a.includes("run"); return Promise.resolve("x") }, env: {}, toolchain: t, l4eDir: null })
  badToolchain.push(!called && r.lean === null && r.lake === null)
}
check("a toolchain name that is not a plain name is never passed to a program", badToolchain.every(Boolean), badToolchain)

// merging the records of the shards
const t1 = { lean: "A", lake: "L", elan: "E", lean4export: "X", node: "v22.1", runnerImage: "ubuntu26/1" }
check("merge: shards that agree give their values, unchanged", JSON.stringify(mergeTools([t1, { ...t1 }, { ...t1 }])) === JSON.stringify(t1), mergeTools([t1, t1]))
check("merge: shards that disagree leave every value, sorted and apart, in that field only", (() => { const m = mergeTools([t1, { ...t1, runnerImage: "ubuntu24/9", node: "v22.0" }]); return m.runnerImage === "ubuntu24/9 | ubuntu26/1" && m.node === "v22.0 | v22.1" && m.lean === "A" })(), mergeTools([t1, { ...t1, runnerImage: "ubuntu24/9" }]))
check("merge: nothing recorded gives null (no field is invented); a record without tools is ignored", mergeTools([]) === null && mergeTools([undefined, null]) === null && mergeTools([undefined, t1]).lean === "A", null)
let mergeOk = true
for (let i = 0; i < 200; i++) {
  const recs = Array.from({ length: 1 + rnd(6) }, () => Object.fromEntries(TOOL_FIELDS.map((f) => [f, rnd(4) === 0 ? null : `${f}${rnd(3)}`])))
  const m = mergeTools(recs)
  for (const f of TOOL_FIELDS) {
    const want = [...new Set(recs.map((r) => r[f]).filter(Boolean))].sort()
    mergeOk &&= (m[f] === null ? want.length === 0 : m[f].split(" | ").join() === want.join())
  }
}
check("merge: every field is exactly the set of the values the records hold (200 random sets)", mergeOk, null)

// the record is written where it has to be
const src = readFileSync(join(dirname(fileURLToPath(import.meta.url)), "setup-source.mjs"), "utf8")
check("setup-source.mjs asks for the tools in the shard record and in the one-shot record, and merges them in the finish record", (src.match(/tools: await toolsNow\(\)/g) || []).length === 2 && /tools: mergeTools\(records\.map/.test(src), (src.match(/toolsNow/g) || []).length)
process.exit(bad ? 1 : 0)

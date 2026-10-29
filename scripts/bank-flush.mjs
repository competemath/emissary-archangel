// Send banked records to the tree as content PRs. All of a library's pending data/bank/<key>/*.jsonl (the cloud
// translation's output, scripts/translate-finish.mjs) are pooled and sent as PRs of at most --batch records: each a per-PR staging file
// data/staging/<key>/<batch>.jsonl on a fresh branch of the tree, signed off, queued with auto-merge — the same PR
// the app opens in PR mode (lib/tengoku-pr.ts). Records whose names are already on the tree's main are dropped.
// A sent bank file moves to data/bank/<key>/sent/, with <file>.prs.json listing its PRs.
//
// Name clashes. A record whose name another library already has on main (trusted or staging), or that another
// library claims in this same run, is resolved before it is sent (the gate refuses a name already trusted, and one
// such record sank a whole PR):
//   - same statement apart from the declared name: a duplicate, not sent;
//   - otherwise renamed <name>__<library> (the last component gets the suffix), with original_name kept.
// Every clash is appended to data/translate/clashes.jsonl for the statistics.
//
//   GH_TOKEN=<a token that can push branches and open PRs on the tree> node scripts/bank-flush.mjs
//        [--repo competemath/tengoku] [--batch 500] [--key <key>] [--dry-run]
// The commits are authored and signed off by the token's own account (its GitHub noreply address).
//
// Before a branch is pushed, scripts/bank-guard.py (tengoku-warden, vendored in scripts/warden) checks it: the staged records are
// secret-scanned, the pull request carries a tengoku-target marker that validate_pr accepts, and the commit adds only what
// scripts/agent-paths.json lists (data/staging/<library>/<batch>.jsonl, mode 100644, nothing deleted). If any check fails
// nothing of that library is pushed and its bank files stay where they are; the next run tries again.
import { resplitRecord } from "../lib/stage-record.mjs"
import { execFileSync } from "node:child_process"
import { appendFileSync, existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, renameSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { join } from "node:path"

const argv = process.argv.slice(2)
const opt = (n, d = null) => (argv.includes(`--${n}`) ? argv[argv.indexOf(`--${n}`) + 1] : d)
const REPO = opt("repo", "competemath/tengoku")
const BATCH = Number(opt("batch", "500"))
const ONLY = opt("key")
const DRY = argv.includes("--dry-run")
const MAX_PRS = Number(opt("max-prs", "0")) || Infinity   // per run: a new account opening dozens of PRs at once gets flagged
const ROOT = new URL("..", import.meta.url).pathname
const BANK = join(ROOT, "data", "bank")
const sh = (cmd, args, cwd) => execFileSync(cmd, args, { cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024 }).trim()
// The guard runs with nothing of ours but PATH: no GH_TOKEN, no bridge token. A guard that cannot run (no python3) is a refusal.
const GUARD = join(ROOT, "scripts", "bank-guard.py")
const guardEnv = { PATH: process.env.PATH, LANG: "C.UTF-8", PYTHONDONTWRITEBYTECODE: "1" }
function guard(args) {
  try {
    execFileSync("python3", [GUARD, ...args], { env: guardEnv, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] })
    return null
  } catch (e) {
    return (String(e.stdout || "") + String(e.stderr || "")).trim() || `guard did not run: ${e.message}`
  }
}
const token = process.env.GH_TOKEN
if (!token && !DRY) {
  console.log("bank-flush: no GH_TOKEN — nothing sent (the bank stays committed until a token exists)")
  process.exit(0)
}

const keys = existsSync(BANK) ? readdirSync(BANK).filter((k) => (!ONLY || k === ONLY) && existsSync(join(BANK, k))) : []
const pending = keys
  .map((k) => ({ key: k, files: readdirSync(join(BANK, k)).filter((f) => f.endsWith(".jsonl")).sort() }))
  .filter((p) => p.files.length)
if (!pending.length) {
  console.log("bank-flush: nothing banked")
  process.exit(0)
}

// the tree's main: every record's name and statement, trusted and staging, of every library (the clash check)
const tree = mkdtempSync(join(os.tmpdir(), "tengoku-flush-"))
const remote = token ? `https://x-access-token:${token}@github.com/${REPO}.git` : `https://github.com/${REPO}.git`
sh("git", ["clone", "-q", "--filter=blob:none", "--no-checkout", remote, tree])
sh("git", ["-C", tree, "sparse-checkout", "set", "--no-cone", "data/staging/", "data/trusted/"])
sh("git", ["-C", tree, "checkout", "-q", "main"])
const everyName = new Map() // name -> [{ lib, statement }]
const claim = (name, lib, statement) => {
  if (!everyName.has(name)) everyName.set(name, [])
  everyName.get(name).push({ lib, statement })
}
for (const tier of ["trusted", "staging"]) {
  const dir = join(tree, "data", tier)
  if (!existsSync(dir)) continue
  const walk = (d, lib) => {
    for (const e of readdirSync(d, { withFileTypes: true })) {
      if (e.isDirectory()) walk(join(d, e.name), e.name)
      else if (e.name.endsWith(".jsonl")) {
        const l0 = lib || e.name.replace(/\.jsonl$/, "")
        for (const l of readFileSync(join(d, e.name), "utf8").split("\n")) {
          if (!l.trim()) continue
          try {
            const r = JSON.parse(l)
            if (typeof r.name === "string") claim(r.name, l0, String(r.statement || ""))
          } catch { /* the gate's problem */ }
        }
      }
    }
  }
  walk(dir, null)
}
const DECL_RE = /^(\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec|noncomputable)\s+)*(?:theorem|lemma)\s+)([^\s(:{[⦃]+)/
const bareStatement = (s) => String(s).replace(DECL_RE, "$1_").replace(/\s+/g, " ").trim()
const suffixed = (name, key) => {
  const cut = name.lastIndexOf(".")
  return `${name.slice(0, cut + 1)}${name.slice(cut + 1)}__${key.replace(/[^A-Za-z0-9]/g, "_")}`
}
const clashes = []
// returns the record to send (possibly renamed) or null when it must not be sent
function resolveClash(r, key) {
  const existing = everyName.get(r.name) || []
  if (!existing.length) return r
  if (existing.some((e) => e.lib === key)) return null // this library has it on main already: not a clash, just sent before
  const same = existing.find((e) => bareStatement(e.statement) === bareStatement(r.statement))
  if (same) {
    clashes.push({ library: key, name: r.name, kind: "duplicate", other: same.lib })
    return null
  }
  const name = suffixed(r.name, key)
  if ((everyName.get(name) || []).some((e) => e.lib === key)) return null // renamed and sent in an earlier run
  const decl = String(r.statement).match(DECL_RE)
  const cut = decl ? decl[2].lastIndexOf(".") : -1
  const statement = decl ? String(r.statement).replace(DECL_RE, `$1${decl[2].slice(0, cut + 1)}${decl[2].slice(cut + 1)}__${key.replace(/[^A-Za-z0-9]/g, "_")}`) : r.statement
  clashes.push({ library: key, name: r.name, kind: "renamed", renamed: name, other: [...new Set(existing.map((e) => e.lib))].join(",") })
  return { ...r, name, statement, original_name: r.name }
}
const onMain = (key) => {
  const names = new Set()
  const files = [join(tree, "data", "staging", `${key}.jsonl`), join(tree, "data", "trusted", `${key}.jsonl`)]
  if (existsSync(join(tree, "data", "staging", key))) for (const f of readdirSync(join(tree, "data", "staging", key))) files.push(join(tree, "data", "staging", key, f))
  for (const f of files) {
    if (!existsSync(f) || !f.endsWith(".jsonl")) continue
    for (const l of readFileSync(f, "utf8").split("\n")) if (l.trim()) try { names.add(JSON.parse(l).name) } catch { /* the gate's problem */ }
  }
  return names
}

let who = { name: "emissary-archangel", email: "emissary-archangel@users.noreply.github.com" }
if (token) {
  const u = JSON.parse(sh("gh", ["api", "user"]))
  who = { name: u.login, email: `${u.id}+${u.login}@users.noreply.github.com` }
}
const git = (...a) => sh("git", ["-C", tree, "-c", `user.name=${who.name}`, "-c", `user.email=${who.email}`, ...a])

const stamp = new Date().toISOString().replace(/[-:]/g, "").replace(/\.\d+Z$/, "Z")
let opened = 0
for (const { key, files } of pending) {
  const batchesNeeded = 1
  if (opened + batchesNeeded > MAX_PRS) {
    console.log(`bank-flush: ${MAX_PRS} PRs this run; the rest wait for the next run`)
    break
  }
  const clashMark = clashes.length
  const have = onMain(key)
  const records = files.flatMap((f) => readFileSync(join(BANK, key, f), "utf8").split("\n").filter((l) => l.trim()))
  const seen = new Set()
  const fresh = []
  for (const l of records) {
    const r0 = JSON.parse(l)
    if (have.has(r0.name) || seen.has(r0.name)) continue
    if (["statement", "proof", "context"].some((f) => String(r0[f] ?? "").includes("\ufffd"))) {
      // garbled when banked (a character split across two stream chunks, fixed in the queue server): not the text
      // that was verified, so never staged
      console.log(`bank-flush: ${key}/${r0.name} skipped: its text holds U+FFFD`)
      continue
    }
    seen.add(r0.name)
    const r = resolveClash(resplitRecord(r0), key) // statement = the header alone, even for a record banked before the split fix
    if (!r) continue
    claim(r.name, key, r.statement) // a later library in this run sees it
    fresh.push(JSON.stringify(r))
  }
  // Phase 1: build every batch's commit on a local branch and run the guard on it. Nothing leaves this machine yet, so a
  // refusal anywhere means nothing of this library was sent and the whole bank stays for the next run.
  const planned = []
  let refusal = null
  for (let i = 0; i < fresh.length && !refusal; i += BATCH) {
    const batch = fresh.slice(i, i + BATCH)
    const id = `${stamp}-${String(i / BATCH).padStart(3, "0")}`
    const branch = `bank/${key}/${id}`
    const title = `Stage ${key}: ${batch.length} record${batch.length === 1 ? "" : "s"} (${id})`
    const target = `emissary-archangel:stage/${key}/${id}`
    // the target marker (warden safegit.make_marker's canonical form: sorted keys, compact), checked by bank-guard.py
    const marker = `<!--tengoku-target:v1 ${JSON.stringify({ actor: "emissary-archangel", base: "main", target })}-->`
    const body = `Banked by Emissary-Archangel's cloud translation (runs ${files.map((f) => f.replace(/\.jsonl$/, "")).join(", ")}). One per-PR staging file; the merge queue compiles exactly these records.\n\n${marker}`
    const scratch = mkdtempSync(join(os.tmpdir(), "bank-guard-"))
    writeFileSync(join(scratch, "body.md"), body)
    const guardArgs = ["--title", title, "--body-file", join(scratch, "body.md"), "--branch", branch, "--base", "main", "--expect-target", target]
    if (DRY) {
      writeFileSync(join(scratch, "records.jsonl"), batch.join("\n") + "\n")
      refusal = guard([...guardArgs, "--file", join(scratch, "records.jsonl"), "--skip-scope"])
      rmSync(scratch, { recursive: true, force: true })
      console.log(`[dry-run] ${title}${refusal ? " — the guard would refuse it" : ""}`)
      if (refusal) console.log(refusal)
      continue
    }
    git("switch", "-q", "-C", branch, "origin/main")
    const rel = join("data", "staging", key, `${id}.jsonl`)
    mkdirSync(join(tree, "data", "staging", key), { recursive: true })
    writeFileSync(join(tree, rel), batch.join("\n") + "\n")
    git("add", "--sparse", "--", rel)
    git("commit", "-q", "-s", "-m", `${title}\n\n${body}`)
    refusal = guard([...guardArgs, "--file", join(tree, rel), "--repo-dir", tree, "--base-rev", "origin/main", "--head-rev", "HEAD", "--policy", join(ROOT, "scripts", "agent-paths.json"), "--class", "translator"])
    rmSync(scratch, { recursive: true, force: true })
    planned.push({ branch, title, body })
  }
  if (DRY) continue
  if (refusal) {
    console.log(`bank-flush: ${key} REFUSED by scripts/bank-guard.py; nothing was pushed and its bank files stay in place:\n${refusal}`)
    git("switch", "-q", "--detach", "origin/main")
    for (const p of planned) git("branch", "-q", "-D", p.branch)
    clashes.length = clashMark
    continue
  }
  // Phase 2: push and open.
  const prs = []
  for (const { branch, title, body } of planned) {
    git("push", "-q", "-f", "origin", branch)
    const url = sh("gh", ["pr", "create", "-R", REPO, "--head", branch, "--title", title, "--body", body]).split("\n").pop()
    try {
      sh("gh", ["pr", "merge", url, "-R", REPO, "--auto"])
    } catch (e) {
      console.log(`  (auto-merge not enabled for ${url}: ${String(e.message).split("\n")[0]})`)
    }
    prs.push(url)
    opened++
    console.log(`${title}: ${url}`)
  }
  mkdirSync(join(BANK, key, "sent"), { recursive: true })
  for (const f of files) renameSync(join(BANK, key, f), join(BANK, key, "sent", f))
  writeFileSync(join(BANK, key, "sent", `${stamp}.prs.json`), JSON.stringify({ files, records: records.length, duplicates: records.length - fresh.length, prs }, null, 2) + "\n")
  console.log(`${key}: ${fresh.length} of ${records.length} records from ${files.length} bank file(s) sent in ${prs.length} PR(s)`)
}
if (clashes.length && !DRY) {
  const at = new Date().toISOString()
  mkdirSync(join(ROOT, "data", "translate"), { recursive: true })
  appendFileSync(join(ROOT, "data", "translate", "clashes.jsonl"), clashes.map((c) => JSON.stringify({ at, ...c })).join("\n") + "\n")
}
const byKind = clashes.reduce((m, c) => ((m[c.kind] = (m[c.kind] || 0) + 1), m), {})
console.log(`bank-flush: name clashes this run ${JSON.stringify(byKind)}`)
rmSync(tree, { recursive: true, force: true })

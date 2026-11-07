// pinned-deps.mjs on real git repositories: a dependency pinned to a commit that no branch holds is fetched by its hash into Lake's clone.
//
// The real case: padic-l-functions (setup run 42383040195, 7 Nov 2026). Its manifest pins CBirkbeck/LeanModularForms at 512911ce1a93…; the commit is on GitHub but on no branch,
// Lake's clone lacked it and Lake printed the lines in REAL_LOG. Here an upstream repository is made with such a commit (a branch that held it was deleted; the upstream lets a fetch
// name a commit by hash, as GitHub does), Lake's clone is made the way Lake makes it (git clone), and the fixture is first shown to reproduce the failure: the clone cannot check
// the commit out. Invariants: the package and the commit are read from Lake's own lines (each package once, only commits git could not read); after the repair the clone checks
// the commit out; a commit the clone has is not fetched again; no clone, or a remote that refuses the hash, is reported as failed and never as fetched; setup-source runs the repair
// before anything else uses the dependencies.
import { execFileSync } from "node:child_process"
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"
import { packagesDir, repairPins, unreadablePins } from "./pinned-deps.mjs"

let failures = 0
const check = (name, ok, detail = "") => {
  console.log(`${ok ? "ok  " : "FAIL"} ${name}${ok ? "" : `  ${detail}`}`)
  if (!ok) failures++
}
const git = (args, cwd) => execFileSync("git", ["-c", "user.name=t", "-c", "user.email=t@t", "-c", "init.defaultBranch=main", ...args], { cwd, stdio: ["ignore", "pipe", "pipe"] }).toString().trim()
const has = (dir, rev) => {
  try {
    git(["cat-file", "-e", `${rev}^{commit}`], dir)
    return true
  } catch {
    return false
  }
}

const REAL_SHA = "512911ce1a936ac9054415c5c72701fbd5cd5ae5"
const REAL_LOG = `info: VersoBlueprint: cloning https://github.com/leanprover/verso-blueprint
info: VersoBlueprint: checking out revision '11c82ed5b84417b0aecc4a22b89ee536ee832ff4'
info: LeanModularForms: cloning https://github.com/CBirkbeck/LeanModularForms.git
info: LeanModularForms: checking out revision '${REAL_SHA}'
info: stderr:
fatal: unable to read tree (${REAL_SHA})
error: external command 'git' exited with code 128
`

// 1. reading Lake's lines
check("the real log names LeanModularForms at its pinned commit", JSON.stringify(unreadablePins(REAL_LOG)) === JSON.stringify([{ pkg: "LeanModularForms", rev: REAL_SHA }]), JSON.stringify(unreadablePins(REAL_LOG)))
check("a package checked out fine is not named", !unreadablePins(REAL_LOG).some((p) => p.pkg === "VersoBlueprint"))
check("the same failure printed three times names the package once", unreadablePins(REAL_LOG + REAL_LOG + REAL_LOG).length === 1)
check("a log with no unreadable tree names nothing", unreadablePins(REAL_LOG.replace(/fatal: .*\n/, "")).length === 0)
check("another failure of git names nothing", unreadablePins(REAL_LOG.replace(/fatal: .*\n/, "fatal: repository not found\n")).length === 0)

// 2. the real-git fixture
const tmp = mkdtempSync(join(tmpdir(), "pinned-"))
const up = join(tmp, "upstream")
mkdirSync(up)
git(["init", "-q"], up)
writeFileSync(join(up, "A.lean"), "def a := 1\n")
git(["add", "-A"], up)
git(["commit", "-qm", "on main"], up)
git(["checkout", "-qb", "work"], up)
writeFileSync(join(up, "B.lean"), "def b := 2\n")
git(["add", "-A"], up)
git(["commit", "-qm", "the pinned commit"], up)
const pinned = git(["rev-parse", "HEAD"], up)
git(["checkout", "-q", "main"], up)
git(["branch", "-qD", "work"], up) // the commit is now on no branch, as 512911ce is on GitHub
git(["config", "uploadpack.allowAnySHA1InWant", "true"], up) // GitHub serves a commit named by its hash

const repo = join(tmp, "lib")
mkdirSync(repo)
writeFileSync(join(repo, "lake-manifest.json"), JSON.stringify({ version: "1.1.0", packagesDir: ".lake/packages", packages: [{ type: "git", name: "LeanModularForms", url: up, rev: pinned }] }))
const pkg = join(packagesDir(repo), "LeanModularForms")
mkdirSync(dirname(pkg), { recursive: true })
git(["clone", "-q", "--no-local", up, pkg], tmp) // as Lake clones it: over the transport, which sends what a branch holds (a local clone would copy every object)
const log = REAL_LOG.replaceAll(REAL_SHA, pinned)
let reproduced = false
try {
  git(["checkout", "-q", "--detach", pinned], pkg)
} catch (e) {
  reproduced = /unable to read tree|reference is not a tree|did not match/.test(String(e.stderr))
}
check("the fixture reproduces the failure: Lake's clone cannot check the pinned commit out", reproduced && !has(pkg, pinned))

// 3. the repair
const msgs = []
const r = repairPins(repo, log, { log: (s) => msgs.push(s) })
check("the pinned commit is fetched by its hash", r.fetched.length === 1 && r.fetched[0].pkg === "LeanModularForms" && r.failed.length === 0, JSON.stringify(r))
let checkedOut = false
try {
  git(["checkout", "-q", "--detach", pinned], pkg)
  checkedOut = git(["rev-parse", "HEAD"], pkg) === pinned
} catch {}
check("after the repair the clone checks the pinned commit out (what Lake does next)", checkedOut)
check("the log says what was done", msgs.some((m) => m.includes("fetched it by its hash")), msgs.join("\n"))

// a commit the clone has is not fetched again: the remote is gone, so a fetch would fail
rmSync(up, { recursive: true, force: true })
const again = repairPins(repo, log)
check("a commit the clone already has is not fetched again", again.fetched.length === 1 && again.failed.length === 0, JSON.stringify(again))

// 4. what cannot be repaired is reported, never counted as fetched
const noClone = repairPins(repo, log.replaceAll("LeanModularForms", "Missing"))
check("no clone to fetch into: failed, not fetched", noClone.fetched.length === 0 && noClone.failed.length === 1 && /no clone/.test(noClone.failed[0].why), JSON.stringify(noClone))

const up2 = join(tmp, "upstream2")
mkdirSync(up2)
git(["init", "-q"], up2)
writeFileSync(join(up2, "A.lean"), "def a := 1\n")
git(["add", "-A"], up2)
git(["commit", "-qm", "main"], up2)
git(["checkout", "-qb", "w"], up2)
writeFileSync(join(up2, "B.lean"), "def b := 2\n")
git(["add", "-A"], up2)
git(["commit", "-qm", "gone"], up2)
const gone = git(["rev-parse", "HEAD"], up2)
git(["checkout", "-q", "main"], up2)
git(["branch", "-qD", "w"], up2)
const repo2 = join(tmp, "lib2")
const pkg2 = join(repo2, ".lake", "packages", "Other")
mkdirSync(dirname(pkg2), { recursive: true })
git(["clone", "-q", "--no-local", up2, pkg2], tmp)
// a remote that no longer has the commit at all (pruned): the fetch by hash is refused
git(["reflog", "expire", "--expire=now", "--all"], up2)
git(["gc", "-q", "--prune=now"], up2)
const refused = repairPins(repo2, REAL_LOG.replaceAll("LeanModularForms", "Other").replaceAll(REAL_SHA, gone))
check("a remote that no longer has the commit: failed with the reason, not fetched", refused.fetched.length === 0 && refused.failed.length === 1 && /refused/.test(refused.failed[0].why), JSON.stringify(refused))

// 5. setup-source runs the repair before the first use of the dependencies
const src = readFileSync(join(dirname(fileURLToPath(import.meta.url)), "setup-source.mjs"), "utf8")
const body = src.slice(src.indexOf("async function mathlibCache()"))
check("mathlibCache resolves the dependencies (with the repair) before `lake exe cache get`", body.indexOf("await ensureDeps()") > -1 && body.indexOf("await ensureDeps()") < body.indexOf('"cache", "get"'))
check("ensureDeps runs Lake again after a repair, and stops when nothing was fetched", /repairPins\(REPO, r\.tail/.test(src) && /if \(!fetched\.length\) return false/.test(src))

rmSync(tmp, { recursive: true, force: true })
if (failures) {
  console.log(`${failures} FAILED`)
  process.exit(1)
}
console.log("all pinned-deps checks passed")

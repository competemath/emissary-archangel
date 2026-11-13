// node scripts/test-setup-build.mjs — --phase build carries on from an earlier round's build (--restore) and
// --phase build-status says whether every module is compiled. Runs setup-source.mjs for real, in a throwaway
// root, against a local git repository and stand-in `elan` and `lake` programs (no Lean, no network).
import { execFileSync, spawnSync } from "node:child_process"
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join, relative, resolve } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const tmp = mkdtempSync(join(os.tmpdir(), "setup-build-test-"))
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name)
}
const sh = (cmd, args, opts = {}) => execFileSync(cmd, args, { stdio: ["ignore", "pipe", "pipe"], ...opts }).toString()

try {
  sh("tar", ["--zstd", "--version"])
} catch {
  console.log("skipped: tar has no --zstd here")
  process.exit(0)
}

// the library: two modules, one commit
const lib = join(tmp, "lib-src")
mkdirSync(join(lib, "Lib"), { recursive: true })
writeFileSync(join(lib, "Lib", "A.lean"), "theorem a : True := trivial\n")
writeFileSync(join(lib, "Lib", "B.lean"), "import Lib.A\ntheorem b : True := trivial\n")
const TC = "leanprover/lean4:v4.0.0"
writeFileSync(join(lib, "lean-toolchain"), TC + "\n")
const git = (...a) => sh("git", ["-c", "user.name=t", "-c", "user.email=t@t", ...a], { cwd: lib })
git("init", "-q")
git("add", ".")
git("commit", "-q", "-m", "lib")
const commit = git("rev-parse", "HEAD").trim()

// the root setup-source.mjs believes it lives in
const root = join(tmp, "root")
mkdirSync(join(root, "scripts"), { recursive: true })
mkdirSync(join(root, "data"), { recursive: true })
cpSync(join(here, "setup-source.mjs"), join(root, "scripts", "setup-source.mjs"))
cpSync(join(here, "setup-tools.mjs"), join(root, "scripts", "setup-tools.mjs"))
cpSync(join(here, "bisect.mjs"), join(root, "scripts", "bisect.mjs"))
cpSync(join(here, "memory-rules.mjs"), join(root, "scripts", "memory-rules.mjs"))
cpSync(join(here, "pinned-deps.mjs"), join(root, "scripts", "pinned-deps.mjs"))
cpSync(join(here, "add-swap.sh"), join(root, "scripts", "add-swap.sh"))
writeFileSync(join(root, "sources.json"), JSON.stringify({ sources: { t: { repo: lib, commit, toolchain: TC, roots: ["Lib"] } } }))
writeFileSync(join(root, "data", "queue-t.json"), JSON.stringify([
  { id: 1, name: "a", sourcePath: "Lib/A.lean", sourceLine: 1, status: "pending" },
  { id: 2, name: "b", sourcePath: "Lib/B.lean", sourceLine: 2, status: "pending" },
]))

// stand-ins on the PATH the script puts first: ~/.elan/bin
const home = join(tmp, "home")
const bin = join(home, ".elan", "bin")
mkdirSync(bin, { recursive: true })
writeFileSync(join(bin, "elan"), `#!/bin/sh\necho "${TC} (default)"\n`)
// lake: records its call; with FAKE_LAKE_MAKES set it "compiles" every module it is asked for
writeFileSync(join(bin, "lake"), `#!/bin/sh
echo "$@" >> "${tmp}/lake-calls"
echo "lake $@" >> "${tmp}/order"
if [ -n "$FAKE_LAKE_HANGS" ] && [ "$1" = build ]; then exec sleep 25; fi
if [ -n "$FAKE_LAKE_STORM" ] && [ "$1" = build ]; then
  echo "$LEAN_NUM_THREADS" >> "${tmp}/storm-threads"
  if [ "$LEAN_NUM_THREADS" != 1 ]; then for i in 1 2 3 4 5 6; do node -e "const b = Buffer.alloc(120 * 1024 * 1024, 1); setInterval(() => b.length, 1000)" "$FAKE_LAKE_SRC/M$i.lean" & done; wait; sleep 8; exit 1; fi
fi
if [ "$FAKE_LAKE_MAKES" = all ] && [ "$1" = build ]; then
  shift
  for m in "$@"; do
    f=".lake/build/lib/lean/$(echo "$m" | tr . /).olean"; mkdir -p "$(dirname "$f")"; : > "$f"
  done
fi
exit 0
`)
chmodSync(join(bin, "elan"), 0o755)
chmodSync(join(bin, "lake"), 0o755)

const repo = join(root, "infra", "t", "repo")
const olean = (m) => join(repo, ".lake", "build", "lib", "lean", "Lib", `${m}.olean`)
const setup = (args, env = {}, opts = {}) =>
  spawnSync("node", [join(root, "scripts", "setup-source.mjs"), "t", ...args], { env: { ...process.env, HOME: home, ...env }, encoding: "utf8", ...opts })
const statusOf = (r) => ({ word: (r.stdout.match(/^complete=(true|false)$/m) || [])[1], file: JSON.parse(readFileSync(join(root, "infra", "t", "build-status.json"), "utf8")) })

// a build that holds the .oleans of the first two modules, as an earlier round would have packed it
const packed = (names, out) => {
  const stage = mkdtempSync(join(tmp, "stage-"))
  for (const n of names) {
    mkdirSync(join(stage, ".lake", "build", "lib", "lean", "Lib"), { recursive: true })
    writeFileSync(join(stage, ".lake", "build", "lib", "lean", "Lib", `${n}.olean`), "")
    // as in a build packed before the setup files were left out: one per module, which unpacked to 7.6 MB each
    mkdirSync(join(stage, ".lake", "build", "ir", "Lib"), { recursive: true })
    writeFileSync(join(stage, ".lake", "build", "ir", "Lib", `${n}.setup.json`), "{}")
  }
  sh("tar", ["--zstd", "-cf", out, "-C", stage, ".lake/build"])
  return out
}

// 1. nothing built yet
let r = setup(["--phase", "build-status"])
let s = r.status === 0 ? statusOf(r) : null
check("status of an unbuilt library: incomplete, 0 of 2", s && s.word === "false" && s.file.built === 0 && s.file.modules === 2 && s.file.complete === false, r.stdout + r.stderr)
check("status also prints the two counts the next round's gate compares: built=0 and modules=2, each on its own line", /^built=0$/m.test(r.stdout) && /^modules=2$/m.test(r.stdout), r.stdout)
check("status runs no lake", !existsSync(join(tmp, "lake-calls")), existsSync(join(tmp, "lake-calls")) && readFileSync(join(tmp, "lake-calls"), "utf8"))

// 2. the earlier round got through everything: the build phase restores it and has nothing left to compile
r = setup(["--phase", "build", "--restore", packed(["A", "B"], join(tmp, "full.tar.zst"))])
check("--phase build with --restore unpacks the earlier build", r.status === 0 && existsSync(olean("A")) && existsSync(olean("B")), r.stdout + r.stderr)
r = setup(["--phase", "build-status"])
s = statusOf(r)
check("status after the restore: complete", s.word === "true" && s.file.built === 2 && s.file.complete === true, JSON.stringify(s))
check("status after the restore prints built=2", /^built=2$/m.test(r.stdout), r.stdout)

check(
  "the setup.json files of a packed build are not restored (they filled the runner's disk), the .oleans are",
  existsSync(olean("A")) && existsSync(olean("B")) && !existsSync(join(repo, ".lake", "build", "ir", "Lib", "A.setup.json")) && !existsSync(join(repo, ".lake", "build", "ir", "Lib", "B.setup.json")),
  "",
)

// 2b. EMISSARY_DROP_RESTORED=1 (the prime job) deletes the archive once it is unpacked, so that the swap of the big-memory round can be added from the space it frees; without it, and when the unpack fails, it stays
{
  const keep = packed(["A", "B"], join(tmp, "keep.tar.zst"))
  rmSync(join(repo, ".lake"), { recursive: true, force: true })
  r = setup(["--phase", "build", "--restore", keep])
  check("without EMISSARY_DROP_RESTORED the archive is kept", r.status === 0 && existsSync(keep), r.stdout + r.stderr)
  rmSync(join(repo, ".lake"), { recursive: true, force: true })
  r = setup(["--phase", "build", "--restore", keep], { EMISSARY_DROP_RESTORED: "1" })
  check("with EMISSARY_DROP_RESTORED=1 the archive is deleted after it is unpacked, and the build is there", r.status === 0 && !existsSync(keep) && existsSync(olean("A")) && existsSync(olean("B")) && /deleted to free its disk space/.test(r.stdout + r.stderr), r.stdout + r.stderr)
  const broken = join(tmp, "broken.tar.zst")
  writeFileSync(broken, "this is not an archive")
  rmSync(join(repo, ".lake"), { recursive: true, force: true })
  r = setup(["--phase", "build", "--restore", broken], { EMISSARY_DROP_RESTORED: "1" })
  check("an archive that cannot be unpacked is not deleted (and the phase fails)", r.status !== 0 && existsSync(broken), r.stdout + r.stderr)
  for (const v of ["0", "true", "yes", ""]) {
    const again = packed(["A"], join(tmp, `v${v || "empty"}.tar.zst`))
    rmSync(join(repo, ".lake"), { recursive: true, force: true })
    r = setup(["--phase", "build", "--restore", again], { EMISSARY_DROP_RESTORED: v })
    check(`EMISSARY_DROP_RESTORED=${JSON.stringify(v)} is not "1": the archive is kept`, existsSync(again), r.stdout + r.stderr)
  }
}

// 2c. EMISSARY_ADD_SWAP_GB (the big-memory round): the swap is added right after the earlier build is unpacked and its archive deleted, BEFORE any module is compiled, and a failure to add it stops the
// phase (cubic: a swap added in the background could come after the first compile, or never, and the round would run without the memory it was made for). df, sudo and free are recorders.
{
  const sb = join(tmp, "swapbin")
  mkdirSync(sb, { recursive: true })
  const order = join(tmp, "order")
  const GIB = 1073741824
  writeFileSync(join(sb, "df"), '#!/bin/sh\nprintf "Avail\\n%s\\n" "$FAKE_BYTES"\n')
  writeFileSync(join(sb, "sudo"), `#!/bin/sh\necho "sudo $*" >> "${order}"\n[ -e "$ARCHIVE" ] && echo "ARCHIVE-STILL-THERE" >> "${order}"\n[ "$1" = "$FAIL_ON" ] && exit 1\nexit 0\n`)
  writeFileSync(join(sb, "free"), "#!/bin/sh\nexit 0\n")
  for (const f of ["df", "sudo", "free"]) chmodSync(join(sb, f), 0o755)
  const withSwap = (archive, env) => {
    rmSync(join(repo, ".lake"), { recursive: true, force: true })
    writeFileSync(order, "")
    const r = setup(["--phase", "build", ...(archive ? ["--restore", archive] : [])], { PATH: `${sb}:${process.env.PATH}`, FAKE_BYTES: String(113 * GIB), ARCHIVE: archive || "/nonexistent", EMISSARY_DROP_RESTORED: "1", ...env })
    const log = readFileSync(order, "utf8").split("\n").filter(Boolean)
    return { r, log, first: (re) => log.findIndex((l) => re.test(l)) }
  }
  let a = withSwap(packed(["A"], join(tmp, "swap1.tar.zst")), { EMISSARY_ADD_SWAP_GB: "48" })
  check("the swap (48 GB of 113 free, 25 kept) is added after the unpack and before the first compile, with the archive already deleted", a.r.status === 0 && a.first(/fallocate -l 48G/) >= 0 && a.first(/swapon \/swapfile/) >= 0 && a.first(/^lake build/) > a.first(/swapon \/swapfile/) && !a.log.includes("ARCHIVE-STILL-THERE"), a.log.join("\n") + a.r.stderr)
  a = withSwap(packed(["A"], join(tmp, "swap2.tar.zst")), { EMISSARY_ADD_SWAP_GB: "999" })
  check("the swap is what the disk can spare (113 - 25 = 88 GB), not what was asked", a.r.status === 0 && a.first(/fallocate -l 88G/) >= 0, a.log.join("\n"))
  a = withSwap(null, { EMISSARY_ADD_SWAP_GB: "48", FAKE_LAKE_MAKES: "all" })
  check("an expired earlier build (nothing to restore): the swap is still added, before the build", a.r.status === 0 && a.first(/swapon \/swapfile/) >= 0 && a.first(/^lake build/) > a.first(/swapon \/swapfile/), a.log.join("\n") + a.r.stderr)
  a = withSwap(packed(["A"], join(tmp, "swap3.tar.zst")), { EMISSARY_ADD_SWAP_GB: "48", FAIL_ON: "fallocate" })
  check("a swap that cannot be added stops the phase before anything is compiled", a.r.status !== 0 && a.first(/^lake build/) < 0 && /could not add the swap/.test(a.r.stdout + a.r.stderr), a.log.join("\n") + a.r.stdout + a.r.stderr)
  for (const v of [undefined, "0", ""]) {
    a = withSwap(packed(["A"], join(tmp, "swap4.tar.zst")), v === undefined ? {} : { EMISSARY_ADD_SWAP_GB: v })
    check(`EMISSARY_ADD_SWAP_GB=${JSON.stringify(v)}: no swap is touched and the build goes on`, a.r.status === 0 && !a.log.some((l) => l.startsWith("sudo")) && a.first(/^lake build/) >= 0, a.log.join("\n"))
  }
  for (const v of ["4G", "0123", "1000", "48;id", "-1", "x"]) {
    a = withSwap(packed(["A"], join(tmp, "swap5.tar.zst")), { EMISSARY_ADD_SWAP_GB: v })
    check(`EMISSARY_ADD_SWAP_GB=${JSON.stringify(v)} is refused before anything is compiled`, a.r.status !== 0 && a.first(/^lake build/) < 0 && !a.log.some((l) => l.startsWith("sudo")) && /EMISSARY_ADD_SWAP_GB is a number/.test(a.r.stdout + a.r.stderr), a.log.join("\n") + a.r.stdout + a.r.stderr)
  }
}

// 2d. EMISSARY_ONLY_MODULES: only the named modules are built and judged, and the earlier build is unpacked for their closure only (the 16.5 GB archive of flt-anthropic's 30,000 modules did not fit
// next to its own unpacked files on a runner, twice, and the 86 modules that were wanted need a few thousand of them)
{
  const only = (names, env = {}, archiveNames = ["A", "B"]) => {
    rmSync(join(repo, ".lake"), { recursive: true, force: true })
    const arc = packed(archiveNames, join(tmp, `only-${Math.random().toString(36).slice(2)}.tar.zst`))
    const res = setup(["--phase", "build", "--restore", arc], { EMISSARY_ONLY_MODULES: names, ...env })
    return { res, arc }
  }
  let o = only("Lib.A")
  let st = statusOf(setup(["--phase", "build-status"], { EMISSARY_ONLY_MODULES: "Lib.A" }))
  check("ONLY=Lib.A: A (which imports nothing) is restored and B is not", o.res.status === 0 && existsSync(olean("A")) && !existsSync(olean("B")), o.res.stdout + o.res.stderr)
  check("ONLY=Lib.A: the status judges one module, and it is complete", st.file.modules === 1 && st.file.built === 1 && st.file.complete === true && st.word === "true", JSON.stringify(st))
  o = only("Lib.B")
  check("ONLY=Lib.B: B and what it imports (A) are restored", o.res.status === 0 && existsSync(olean("A")) && existsSync(olean("B")) && /restoring the closure of 1 modules only: 2 modules/.test(o.res.stdout + o.res.stderr), o.res.stdout + o.res.stderr)
  // unrelated members of the archive stay in the archive
  rmSync(join(repo, ".lake"), { recursive: true, force: true })
  const stage = mkdtempSync(join(tmp, "stage-"))
  mkdirSync(join(stage, ".lake", "build", "lib", "lean", "Lib"), { recursive: true })
  for (const n of ["A", "B", "Other"]) writeFileSync(join(stage, ".lake", "build", "lib", "lean", "Lib", `${n}.olean`), "")
  const arc2 = join(tmp, "only-other.tar.zst")
  sh("tar", ["--zstd", "-cf", arc2, "-C", stage, ".lake/build"])
  const r2 = setup(["--phase", "build", "--restore", arc2], { EMISSARY_ONLY_MODULES: "Lib.B" })
  check("a member of the archive that no named module imports is not unpacked", r2.status === 0 && existsSync(olean("B")) && !existsSync(join(repo, ".lake", "build", "lib", "lean", "Lib", "Other.olean")), r2.stdout + r2.stderr)
  // the archive is deleted after the restricted unpack too
  o = only("Lib.A", { EMISSARY_DROP_RESTORED: "1" })
  check("with EMISSARY_DROP_RESTORED=1 the archive is deleted after a restricted unpack", o.res.status === 0 && !existsSync(o.arc), o.res.stdout + o.res.stderr)
  // an archive that cannot be deleted: fatal when the swap is asked for (it is sized from the space the deletion frees), only a warning otherwise
  {
    const sb = join(tmp, "swapbin"), GIB = 1073741824   // the recorders of 2c
    const dir = mkdtempSync(join(tmp, "locked-"))
    const mk = () => { rmSync(join(repo, ".lake"), { recursive: true, force: true }); const a = packed(["A"], join(dir, "locked.tar.zst")); chmodSync(dir, 0o555); return a }
    let arc3 = mk()
    let rr = setup(["--phase", "build", "--restore", arc3], { PATH: `${sb}:${process.env.PATH}`, FAKE_BYTES: String(113 * GIB), EMISSARY_DROP_RESTORED: "1", EMISSARY_ADD_SWAP_GB: "48", FAKE_LAKE_MAKES: "all" })
    chmodSync(dir, 0o755)
    const asRoot = process.getuid && process.getuid() === 0   // root deletes anything: the case cannot be made
    if (asRoot) console.log("skipped: an archive that cannot be deleted stops a big-memory round (root deletes anything: the case cannot be made)")
    else check("an archive that cannot be deleted stops a big-memory round (its swap is sized from that space)", rr.status !== 0 && /could not delete/.test(rr.stdout + rr.stderr), rr.stdout + rr.stderr)
    rmSync(arc3, { force: true })
    arc3 = mk()
    rr = setup(["--phase", "build", "--restore", arc3], { EMISSARY_DROP_RESTORED: "1", FAKE_LAKE_MAKES: "all" })
    chmodSync(dir, 0o755)
    if (asRoot) console.log("skipped: without a swap asked for, an archive that cannot be deleted is only a warning (root deletes anything)")
    else check("without a swap asked for, an archive that cannot be deleted is only a warning", rr.status === 0 && /WARNING: could not delete/.test(rr.stdout + rr.stderr), rr.stdout + rr.stderr)
  }
  // names are checked before anything is built or unpacked
  for (const [name, v, re] of [["a module with no entries in the library", "Lib.Nope", /no entries/], ["a shell word", "Lib.A;id", /not a module name/], ["a space", "Lib.A Lib.B", /not a module name/], ["a name that starts with a digit", "1Lib", /not a module name/]]) {
    o = only(v)
    check(`ONLY with ${name} stops the phase and unpacks nothing`, o.res.status !== 0 && re.test(o.res.stdout + o.res.stderr) && !existsSync(olean("A")), o.res.stdout + o.res.stderr)
  }
  // nothing asked for: everything; a list with no name in it: an error, not "everything"
  o = only("")
  check(`ONLY="" means all modules: both are restored`, o.res.status === 0 && existsSync(olean("A")) && existsSync(olean("B")), o.res.stdout + o.res.stderr)
  for (const v of [",", ",,", ", ,"]) {
    o = only(v)
    check(`ONLY=${JSON.stringify(v)} holds no module name: the phase stops and nothing is unpacked or built`, o.res.status !== 0 && /holds no module name/.test(o.res.stdout + o.res.stderr) && !existsSync(olean("A")), o.res.stdout + o.res.stderr)
  }
  // the other phases ignore it
  const s0 = setup(["--phase", "build-status"])
  check("build-status without ONLY judges both modules", /^modules=2$/m.test(s0.stdout), s0.stdout)
}

// 3. the earlier round got through half: the build phase finishes the rest
rmSync(join(repo, ".lake"), { recursive: true, force: true })
r = setup(["--phase", "build", "--restore", packed(["A"], join(tmp, "half.tar.zst"))], { FAKE_LAKE_MAKES: "all" })
s = statusOf(setup(["--phase", "build-status"]))
check("half a build is restored and the rest is compiled", r.status === 0 && s.word === "true" && s.file.built === 2, r.stdout + r.stderr)

// 4. the same half build, and lake gets no further: the status says so
rmSync(join(repo, ".lake"), { recursive: true, force: true })
r = setup(["--phase", "build", "--restore", packed(["A"], join(tmp, "half.tar.zst"))])
s = statusOf(setup(["--phase", "build-status"]))
check("a build that stops half way is reported incomplete (1 of 2)", r.status === 0 && s.word === "false" && s.file.built === 1, r.stdout + r.stderr)

// 5. the earlier build is gone (an expired artifact): the build goes on without it, it does not fail
rmSync(join(repo, ".lake"), { recursive: true, force: true })
r = setup(["--phase", "build", "--restore", join(tmp, "expired.tar.zst")], { FAKE_LAKE_MAKES: "all" })
s = statusOf(setup(["--phase", "build-status"]))
check("a missing earlier build is not an error for the build phase", r.status === 0 && s.word === "true" && /no earlier build/.test(r.stdout), r.stdout + r.stderr)

// 6. a shard still insists on its build
r = setup(["--phase", "shard", "--shard", "0/2", "--restore", join(tmp, "expired.tar.zst")])
check("a shard without its build fails", r.status !== 0 && /no build to restore/.test(r.stderr + r.stdout), r.stdout + r.stderr)

// 7. an unknown phase is still refused
r = setup(["--phase", "bulid"])
check("an unknown phase is refused", r.status !== 0 && /build-status/.test(r.stderr), r.stderr)

// 7b. the finish phase writes the record, with the tools the shards say produced it (the finish job runs no Lean, so it can only pass on what they recorded)
{
  const exportsDir = join(root, "data", "exports", "t")
  const shardsDir = join(exportsDir, ".shards")
  mkdirSync(shardsDir, { recursive: true })
  for (const m of ["Lib.A", "Lib.B"]) writeFileSync(join(exportsDir, `${m}.ndjson`), "")
  const rec = (i, extra) => writeFileSync(join(shardsDir, `${i}-of-2.json`), JSON.stringify({ shard: i, shards: 2, commit, toolchain: TC, modules: 1, exported: 1, failed: [], expansion: {}, minutes: 1, ...extra }))
  const tools = (over = {}) => ({ lean: "4.0.0 (commit abc, x)", lake: "5.0.0", elan: "4.1.2", lean4export: "0123456789ab + batch patch aaaaaaaaaaaa", node: "v22.1.0", runnerImage: "ubuntu26/20261012.163.1", ...over })
  const record = () => JSON.parse(readFileSync(join(root, "infra", "t", "setup.json"), "utf8"))
  rec(0, { tools: tools() })
  rec(1, { tools: tools() })
  r = setup(["--phase", "finish"])
  let rec1 = r.status === 0 ? record() : null
  check("finish: the tools the shards agree on are in the record, field for field", rec1 && JSON.stringify(rec1.tools) === JSON.stringify(tools()), r.stdout + r.stderr)
  check("finish: the record keeps every field the readers use (key, repo, commit, toolchain, roots, modules, exported, failed)", rec1 && ["key", "repo", "commit", "toolchain", "roots", "modules", "exported", "failed"].every((k) => k in rec1) && rec1.exported === 2 && rec1.failed.length === 0, rec1 && Object.keys(rec1))
  rec(1, { tools: tools({ runnerImage: "ubuntu24/20261001.1.1", node: "v22.2.0" }) })
  r = setup(["--phase", "finish"])
  rec1 = record()
  check("finish: shards on different images or nodes leave both values on file", rec1.tools.runnerImage === "ubuntu24/20261001.1.1 | ubuntu26/20261012.163.1" && rec1.tools.node === "v22.1.0 | v22.2.0" && rec1.tools.lean === tools().lean, rec1.tools)
  rec(0, {})
  rec(1, {})
  r = setup(["--phase", "finish"])
  rec1 = record()
  check("finish: records from before the tools were written give a record without a tools field, not an invented one", r.status === 0 && !("tools" in rec1), rec1.tools)
  rmSync(shardsDir, { recursive: true, force: true })
  for (const m of ["Lib.A", "Lib.B"]) rmSync(join(exportsDir, `${m}.ndjson`), { force: true })
}

// 8. the machine's memory runs out (several processes each under the per-process limit): the biggest process is
// killed at once instead of the runner dying. Linux only (it reads /proc/meminfo); asking for more free memory than any
// machine has makes the shortage certain.
if (process.platform === "linux") {
  rmSync(join(repo, ".lake"), { recursive: true, force: true })
  const t0 = Date.now()
  r = setup(["--phase", "build"], { FAKE_LAKE_HANGS: "1", EMISSARY_MIN_AVAILABLE_MB: "999999999" })
  check("a shortage of the machine's memory kills the biggest process", /memory watchdog: killed \d+ at \d+ MB \(only \d+ MB left/.test(r.stdout + r.stderr) && Date.now() - t0 < 22000, r.stdout + r.stderr)
  r = setup(["--phase", "build"], { FAKE_LAKE_HANGS: "1", EMISSARY_MIN_AVAILABLE_MB: "1" })
  r = setup(["--phase", "build"], { FAKE_LAKE_HANGS: "1", EMISSARY_MIN_AVAILABLE_MB: "1536MB" })
  check("an unreadable threshold falls back to the default instead of killing everything", !/memory watchdog: killed/.test(r.stdout + r.stderr), r.stdout + r.stderr)
  check("with plenty of memory left nothing is killed", !/memory watchdog: killed/.test(r.stdout + r.stderr), r.stdout + r.stderr)
}

// 9. a kill storm (finite-simple-groups-lean, 13 Nov 2026: 610 kills in one 5-hour `lake build` chunk, 15 of 3,964 modules built): a lake build on several threads whose Lean processes are
// killed one after another is stopped after EMISSARY_STORM_KILLS kills and the rest of the build runs on ONE thread. The fake lake starts six node processes (~120 MB each) that the watchdog kills
// under a 20 MB limit (the per-process rule, which runs on macOS too) and, on one thread, compiles what it is asked for.
{
  const stormRun = (env = {}) => {
    rmSync(join(repo, ".lake"), { recursive: true, force: true })
    rmSync(join(tmp, "storm-threads"), { force: true })
    rmSync(join(tmp, "lake-calls"), { force: true })
    const t0 = Date.now()
    // a broken version may never end (that is what is being caught): 30 s, then everything under the test's temp directory is stopped
    const r = setup(["--phase", "build"], { FAKE_LAKE_STORM: "1", FAKE_LAKE_SRC: join(realpathSync(tmp), relative(tmp, repo), "Lib"), FAKE_LAKE_MAKES: "all", EMISSARY_FOOTPRINT_MB: "20", EMISSARY_WATCH_MS: "500", EMISSARY_STORM_KILLS: "3", ...env }, { timeout: 30000, killSignal: "SIGKILL" })
    spawnSync("pkill", ["-f", tmp])
    const threads = existsSync(join(tmp, "storm-threads")) ? readFileSync(join(tmp, "storm-threads"), "utf8").trim().split("\n") : []
    return { r, threads, secs: (Date.now() - t0) / 1000 }
  }
  // the first try runs on 4 threads and is stopped; every later `lake build` (each killed module alone, then the chunk again) runs on 1
  const lowered = (t) => t.length > 1 && t[0] === "4" && t.slice(1).every((x) => x === "1")
  let st = stormRun()
  check("a kill storm stops the lake build, and every later try runs on one thread", lowered(st.threads), st.threads.join(",") + "\n" + st.r.stdout.slice(-1500))
  check("the storm is said in the log with the number of kills and the new setting", /memory: \d+ modules were killed within one lake build on 4 threads: stopped, and the rest of this build runs one job at a time \(LEAN_NUM_THREADS=1\)/.test(st.r.stdout), st.r.stdout.slice(-1500))
  // cubic on #194: each killed process names its module (a `.lean` argument), so the watchdog records it and settle() builds it alone after the stop
  const calls = existsSync(join(tmp, "lake-calls")) ? readFileSync(join(tmp, "lake-calls"), "utf8") : ""
  check("the modules the storm killed are built alone, one by one, after the stop", /memory: Lib\.M\d was killed at \d+ MB .*building it alone/.test(st.r.stdout) && /^build Lib\.M\d$/m.test(calls) && /memory: Lib\.M\d built alone/.test(st.r.stdout), calls + "\n" + st.r.stdout.slice(-1500))
  check("the build then finishes: both modules have an .olean", existsSync(olean("A")) && existsSync(olean("B")), st.r.stdout.slice(-800))
  check("the storm costs seconds, not hours: the fake chunk would have run 8 s after the kills", st.secs < 20, `${st.secs}`)
  st = stormRun({ LEAN_NUM_THREADS: "1" })
  check("on one thread there is no storm rule: one try, no stop", st.threads.join(",") === "1" && !/kill storm|one job at a time/.test(st.r.stdout), st.threads.join(",") + st.r.stdout.slice(-600))
  st = stormRun({ EMISSARY_STORM_KILLS: "1000", EMISSARY_BUILD_ATTEMPTS: "1" })
  check("with the limit above the kills there is no stop either", !/one job at a time/.test(st.r.stdout), st.r.stdout.slice(-600))
  // the broken versions of the wiring: the threads are not lowered; the stop is never asked for
  const real = readFileSync(join(root, "scripts", "setup-source.mjs"), "utf8")
  for (const [name, from, to] of [
    ["the threads are not lowered after the stop", '        ENV.LEAN_NUM_THREADS = "1"\n', ""],
    ["the killed modules are not settled after the stop", "        ENV.LEAN_NUM_THREADS = \"1\"\n        await settle()\n", "        ENV.LEAN_NUM_THREADS = \"1\"\n"],
    ["the chunk is never stopped", "abortWhen: () => stormTripped({ kills: killsInRun, threads: Number(ENV.LEAN_NUM_THREADS), limit: STORM_KILLS }),", "abortWhen: null,"],
  ]) {
    if (real.split(from).length !== 2) { check(`mutant ${name}: the text to break is there once`, false, from); continue }
    writeFileSync(join(root, "scripts", "setup-source.mjs"), real.replace(from, to))
    try {
      const m = stormRun({ EMISSARY_BUILD_ATTEMPTS: "2" })
      check(`the broken version "${name}" is caught`, !lowered(m.threads) || m.secs >= 20 || !/one job at a time/.test(m.r.stdout) || !/building it alone/.test(m.r.stdout), m.threads.join(",") + ` ${m.secs}s`)
    } finally {
      writeFileSync(join(root, "scripts", "setup-source.mjs"), real)
    }
  }
}

rmSync(tmp, { recursive: true, force: true })
process.exit(bad ? 1 : 0)

// node scripts/test-setup-build.mjs — --phase build carries on from an earlier round's build (--restore) and
// --phase build-status says whether every module is compiled. Runs setup-source.mjs for real, in a throwaway
// root, against a local git repository and stand-in `elan` and `lake` programs (no Lean, no network).
import { execFileSync, spawnSync } from "node:child_process"
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import os from "node:os"
import { dirname, join, resolve } from "node:path"
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
const setup = (args, env = {}) =>
  spawnSync("node", [join(root, "scripts", "setup-source.mjs"), "t", ...args], { env: { ...process.env, HOME: home, ...env }, encoding: "utf8" })
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
check("status runs no lake", !existsSync(join(tmp, "lake-calls")), existsSync(join(tmp, "lake-calls")) && readFileSync(join(tmp, "lake-calls"), "utf8"))

// 2. the earlier round got through everything: the build phase restores it and has nothing left to compile
r = setup(["--phase", "build", "--restore", packed(["A", "B"], join(tmp, "full.tar.zst"))])
check("--phase build with --restore unpacks the earlier build", r.status === 0 && existsSync(olean("A")) && existsSync(olean("B")), r.stdout + r.stderr)
r = setup(["--phase", "build-status"])
s = statusOf(r)
check("status after the restore: complete", s.word === "true" && s.file.built === 2 && s.file.complete === true, JSON.stringify(s))

check(
  "the setup.json files of a packed build are not restored (they filled the runner's disk), the .oleans are",
  existsSync(olean("A")) && existsSync(olean("B")) && !existsSync(join(repo, ".lake", "build", "ir", "Lib", "A.setup.json")) && !existsSync(join(repo, ".lake", "build", "ir", "Lib", "B.setup.json")),
  "",
)

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

rmSync(tmp, { recursive: true, force: true })
process.exit(bad ? 1 : 0)

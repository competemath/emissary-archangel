// node scripts/test-setup-workflows.mjs — what the setup workflows may and may not do (exits 1 on a violation).
// Textual, no YAML library: the checks are on the job blocks of .github/workflows/setup-sharded.yml and setup-auto.yml.
//   - a job that runs the library's own code (prime: lake build; shard: lake build and lean) holds no write permission;
//   - the one job that dispatches the next build round runs no code from the library: it checks nothing out;
//   - the shards and the finish job start only on a complete build (or the legacy no-prime flow, or a bank_run);
//   - setup-auto.yml dispatches and writes nothing else, and its values reach the shell through env, never inline.
import { readFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const wf = join(dirname(fileURLToPath(import.meta.url)), "..", ".github", "workflows")
let bad = 0
const check = (name, ok, detail) => {
  if (!ok) { bad++; console.log("FAIL", name, detail ?? "") } else console.log("ok", name)
}
const jobsOf = (file) => {
  const text = readFileSync(join(wf, file), "utf8")
  const after = text.slice(text.indexOf("\njobs:\n") + 6)
  const jobs = {}
  let name = null
  for (const line of after.split("\n")) {
    const m = line.match(/^  ([a-z][a-z-]*):\s*$/)
    if (m) { name = m[1]; jobs[name] = []; continue }
    if (name) jobs[name].push(line)
  }
  return Object.fromEntries(Object.entries(jobs).map(([k, v]) => [k, v.join("\n")]))
}
const permissionsOf = (block) => (block.match(/^    permissions:\s*(.*)$/m) || [])[1] ?? null
const writes = (perm) => perm == null || /write/.test(perm)

const sharded = jobsOf("setup-sharded.yml")
check("setup-sharded has prime, build-gate, shard and finish", ["prime", "build-gate", "shard", "finish"].every((j) => j in sharded), Object.keys(sharded))
check("prime runs the library's build and holds no write permission", /lake|setup-source\.mjs/.test(sharded.prime) && !writes(permissionsOf(sharded.prime)) , permissionsOf(sharded.prime))
check("shard runs the library's build and holds no write permission", /--phase shard/.test(sharded.shard) && !writes(permissionsOf(sharded.shard)), permissionsOf(sharded.shard))
check("build-gate may dispatch (actions: write) and nothing else", /actions:\s*write/.test(permissionsOf(sharded["build-gate"]) || "") && !/contents/.test(permissionsOf(sharded["build-gate"]) || ""), permissionsOf(sharded["build-gate"]))
check("build-gate checks nothing out and runs no node, lake or lean", !/actions\/checkout|setup-node|setup-source|\blake\b|\blean\b|elan/.test(sharded["build-gate"].replace(/#.*$/gm, "")), "")
check("build-gate sends only numbers to the dispatch, checked first", /\^\[0-9\]\+\$/.test(sharded["build-gate"]) && !/\$\{\{\s*needs\.prime\.outputs[^}]*\}\}[^\n]*gh workflow run/.test(sharded["build-gate"]), "")
check("build-gate stops at max_build_rounds", /BUILD_ROUND" -ge "\$MAX_BUILD_ROUNDS"/.test(sharded["build-gate"]), "")
check("build-gate runs only when the build is incomplete", /needs\.prime\.outputs\.complete != 'true'/.test(sharded["build-gate"]), "")
check("shard starts only on a complete build (or without a prime)", /prime_minutes == '0' \|\| needs\.prime\.outputs\.complete == 'true'/.test(sharded.shard.split("runs-on")[0]), "")
check("finish starts only on a complete build (or a bank_run, or without a prime)", /inputs\.bank_run != '' \|\| inputs\.prime_minutes == '0' \|\| needs\.prime\.outputs\.complete == 'true'/.test(sharded.finish.split("runs-on")[0]), "")
check("the complete word is cut down to true or false before it is an output", /grep -E '\^complete=\(true\|false\)\$'/.test(sharded.prime), "")
check("the prime job restores the previous build and goes on if it has expired", /continue-on-error: true/.test(sharded.prime.split("Build what fits")[0].split("The previous round's build")[1] || ""), "")
check("the next export round carries max_build_rounds on", /-f max_build_rounds="\$MAX_BUILD_ROUNDS"/.test(sharded.finish), "")

const auto = jobsOf("setup-auto.yml")
const planBlock = auto.plan || ""
check("setup-auto has one job, which dispatches and only reads contents", /actions:\s*write/.test(permissionsOf(planBlock) || "") && /contents:\s*read/.test(permissionsOf(planBlock) || "") && !/contents:\s*write/.test(permissionsOf(planBlock) || ""), permissionsOf(planBlock))
check("setup-auto never builds or runs the library", !/\blake\b|elan|setup-source\.mjs/.test(planBlock.replace(/#.*$/gm, "")), "")
check("setup-auto checks the key before using it", /\^\[a-z0-9\]\[a-z0-9-\]\*\$/.test(planBlock), "")
const runBodies = [...planBlock.matchAll(/run: \|\n((?: {10}.*\n?|\n)+)/g)].map((m) => m[1]).join("\n")
check("no ${{ }} expression sits inside a shell script of setup-auto", !/\$\{\{/.test(runBodies), runBodies.match(/.*\$\{\{.*/)?.[0])
process.exit(bad ? 1 : 0)

// node scripts/memory-intake.mjs <command> <bundle.json> [options]
//   check   shape, banned constructs, and a Leak IV compile of every closure       --leak-iv <sse url>   (default http://127.0.0.1:7871/sse)
//   audit   the ten clean-room reviewers (needs the `claude` CLI)                  --model <id> --mcp-config <file with Leak I>
//   stage   write the staging file, the library registration and the Jinshi nomination under --out (default ./memory-intake-out)
//   run     check, then audit, then stage; stops at the first stage that fails
// Exit code 0 only when the stage(s) passed. See memory-intake/README.md.
import { readFileSync, writeFileSync, mkdirSync } from "node:fs"
import { dirname, join } from "node:path"
import { audit, preflight, stageBundle } from "../lib/memory-intake.mjs"

const [cmd, file, ...rest] = process.argv.slice(2)
const opt = (name, dflt) => {
  const i = rest.indexOf(`--${name}`)
  return i >= 0 ? rest[i + 1] : dflt
}
if (!["check", "audit", "stage", "run"].includes(cmd) || !file) {
  console.error("usage: node scripts/memory-intake.mjs check|audit|stage|run <bundle.json> [--leak-iv URL] [--model ID] [--mcp-config FILE] [--out DIR] [--toolchain T]")
  process.exit(2)
}
const bundle = JSON.parse(readFileSync(file, "utf8"))
const out = opt("out", "memory-intake-out")
mkdirSync(out, { recursive: true })
const save = (name, obj) => writeFileSync(join(out, name), typeof obj === "string" ? obj : JSON.stringify(obj, null, 2) + "\n")

let ok = true
if (cmd === "check" || cmd === "run") {
  const r = await preflight(bundle, { leakIvUrl: opt("leak-iv", "http://127.0.0.1:7871/sse") })
  save("preflight.json", r)
  console.log(`preflight: ${r.ok ? "pass" : "FAIL"}`)
  for (const e of r.errors) console.log(`  ${e}`)
  for (const row of r.entries) for (const p of row.problems) console.log(`  ${row.name}: ${p}`)
  ok = r.ok
}
if (ok && (cmd === "audit" || cmd === "run")) {
  const r = await audit(bundle, { model: opt("model"), mcpConfig: opt("mcp-config") })
  save("audit.json", r)
  console.log(`audit: ${r.pass ? "pass" : "FAIL"}${r.blockingFailures.length ? ` (blocking: ${r.blockingFailures.join(", ")})` : ""}${r.unusable.length ? ` (no verdict: ${r.unusable.join(", ")})` : ""}`)
  for (const x of r.results) console.log(`  ${x.id.padEnd(14)} ${x.verdict?.verdict ?? "—"}  ${x.verdict?.summary ?? ""}`)
  ok = r.pass
}
if (ok && (cmd === "stage" || cmd === "run")) {
  const s = stageBundle(bundle, { toolchain: opt("toolchain") })
  if (s.errors.length) {
    console.log(`stage: FAIL\n  ${s.errors.join("\n  ")}`)
    ok = false
  } else {
    mkdirSync(dirname(join(out, s.stagingPath)), { recursive: true })
    save(s.stagingPath, s.jsonl)
    save("registration.json", s.registration)
    save("jinshi-nomination.json", s.jinshi)
    console.log(`stage: wrote ${s.stagingPath} (${s.jinshi.count} records), registration.json, jinshi-nomination.json under ${out}`)
  }
}
process.exit(ok ? 0 : 1)

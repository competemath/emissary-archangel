// stage-records.mjs composed.jsonl --source <library key> --toolchain <toolchain> --out bank.jsonl
// Turns scripts/bump/records.py's composed records ({name, sourcePath, sourceUrl, proof = the whole text}) into Tengoku staging
// records with lib/stage-record.mjs, the code every other banked record went through (statement / proof / context split).
import { readFileSync, writeFileSync } from "node:fs"
import { stagingRecord } from "../../lib/stage-record.mjs"

const argv = process.argv.slice(2)
const opt = (n, d = null) => (argv.includes(`--${n}`) ? argv[argv.indexOf(`--${n}`) + 1] : d)
const input = argv.find((a) => !a.startsWith("--") && argv[argv.indexOf(a) - 1]?.startsWith("--") === false) ?? argv[0]
const source = opt("source")
const toolchain = opt("toolchain")
const out = opt("out")
if (!input || !source || !toolchain || !out) {
  console.error("usage: stage-records.mjs composed.jsonl --source KEY --toolchain TC --out bank.jsonl")
  process.exit(2)
}
const records = []
const errors = {}
for (const line of readFileSync(input, "utf8").split("\n")) {
  if (!line.trim()) continue
  const e = JSON.parse(line)
  const r = stagingRecord(source, { name: e.name, proof: e.proof, sourcePath: e.sourcePath, sourceUrl: e.sourceUrl }, toolchain)
  if (r.error) errors[r.error] = (errors[r.error] ?? 0) + 1
  else records.push(r.record)
}
writeFileSync(out, records.map((r) => JSON.stringify(r)).join("\n") + (records.length ? "\n" : ""))
console.log(JSON.stringify({ records: records.length, errors }))

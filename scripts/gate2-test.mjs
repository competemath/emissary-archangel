// Gate 2 on the tree with the resident elaborator (:7872): two consecutive
// calls on a real MagmaEgg entry (second call must be much faster), then a
// tampered body (must be name_collision).
import { pathToFileURL } from "node:url"
import { readFileSync } from "node:fs"
const b = await import(new URL("../public/local-claude-bridge.mjs", import.meta.url).href)
const REPO = process.env.CORPUS_ROOT_EQUATIONAL_THEORIES || new URL("../infra/equational-theories-4291/repo", import.meta.url).pathname
const ARCHANGEL = process.argv[2] || "http://127.0.0.1:7872/sse"
const q = JSON.parse(readFileSync(new URL("../data/queue-equational-theories.json", import.meta.url), "utf8"))
const entries = q.filter((e) => e.sourcePath === "equational_theories/Generated/MagmaEgg/small/_000.lean" && e.oldStatement).slice(0, 2)
let failures = 0
const check = (label, cond, detail = "") => { console.log(`[${cond ? "OK " : "BAD"}] ${label}${detail ? " — " + String(detail).replace(/\s+/g, " ").slice(0, 400) : ""}`); if (!cond) failures++ }
const mod = "equational_theories.Generated.MagmaEgg.small._000"
for (const [i, e] of entries.entries()) {
  const rec = await b.reconstructOldTheoremText(REPO, e)
  const t = Date.now()
  const g = await b.gate2ForScript(rec.oldTheoremText, { old_id: null, old_export_names: e.name, bare_name: e.name, repo_root: REPO, module_name: mod }, { archangelUrl: ARCHANGEL })
  check(`call ${i + 1} (#${e.id} ${e.name}) -> ${g.reason} in ${((Date.now() - t) / 1000).toFixed(1)}s`, g.ok === true, g.text)
}
const e = entries[0]
const rec = await b.reconstructOldTheoremText(REPO, e)
const wrong = rec.oldTheoremText.replace(/(abbrev Equation\d+ \(G : Type uEq\) \[Magma G\] : Prop := ∀ [^,]+, )(.+)/, (m, head, law) => `${head}${law.replace(/=/, "= x ◇ x ◇")}`)
const t = Date.now()
const w = await b.gate2ForScript(wrong, { old_id: null, old_export_names: e.name, bare_name: e.name, repo_root: REPO, module_name: mod }, { archangelUrl: ARCHANGEL })
check(`tampered body -> ${w.reason} in ${((Date.now() - t) / 1000).toFixed(1)}s`, w.ok === false && w.reason === "name_collision", w.text)
console.log(failures ? `${failures} FAILED` : "ALL_GATE2_TREE_TESTS_PASSED")
process.exit(0)

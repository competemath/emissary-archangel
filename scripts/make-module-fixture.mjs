// node scripts/make-module-fixture.mjs — rewrites scripts/fixtures/real-module-lists.json from the real exports in data/exports/<library>/<Module>.names.json
// (a module that was set up has a names.json; the names are real module names of real libraries). The fixture is what the property tests run on in CI, where
// the 2 GB of exports are not checked out; regenerate it when libraries are added.
import { existsSync, readdirSync, statSync, writeFileSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const here = dirname(fileURLToPath(import.meta.url))
const root = join(here, "..", "data", "exports")
const libs = {}
for (const lib of readdirSync(root).sort()) {
  const dir = join(root, lib)
  if (!existsSync(dir) || !statSync(dir).isDirectory()) continue
  const mods = readdirSync(dir).filter((f) => f.endsWith(".names.json")).map((f) => f.slice(0, -".names.json".length)).sort()
  if (mods.length) libs[lib] = mods
}
writeFileSync(join(here, "fixtures", "real-module-lists.json"), JSON.stringify(libs))
console.log(`${Object.keys(libs).length} libraries, ${Object.values(libs).reduce((a, m) => a + m.length, 0)} modules`)

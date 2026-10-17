// Loads the agent-jail region of public/local-claude-bridge.mjs (between the agent-jail:begin and agent-jail:end markers) as
// a module of its own, so the tests can call claudeToolArgs, agentEnv and spawnClaude without starting the bridge.
// The imports and the CLAUDE_BIN line are copied from the bridge itself, so the region sees what it sees there.
//
//   import { loadRegion } from "./bridge-region.mjs";  const r = await loadRegion({ CLAUDE_BIN: "/x/agent-run.py" })
//   node bridge-region.mjs tool-args   prints, as JSON, the tool flags of every kind under every combination of the shell switches
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from "node:fs"
import { tmpdir } from "node:os"
import { join, dirname } from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"

const HERE = dirname(fileURLToPath(import.meta.url))
export const BRIDGE = process.env.BRIDGE_PATH || join(HERE, "..", "..", "public", "local-claude-bridge.mjs")

export function regionSource(bridgeText = readFileSync(BRIDGE, "utf8")) {
  const begin = bridgeText.indexOf("// agent-jail:begin")
  const end = bridgeText.indexOf("// agent-jail:end")
  if (begin < 0 || end < begin) throw new Error("the bridge has no agent-jail region")
  const imports = bridgeText.split("\n").filter((l) => /^import .* from "node:[a-z_]+"$/.test(l)).join("\n")
  const claudeBin = bridgeText.split("\n").find((l) => /^const CLAUDE_BIN = /.test(l))
  if (!claudeBin) throw new Error("the bridge has no CLAUDE_BIN line")
  return `${imports}\n${claudeBin}\n${bridgeText.slice(begin, end)}\nexport { claudeToolArgs, claudeCapArgs, agentCaps, agentEnv, spawnClaude, bashGranted, AGENT_MAX_USD_DEFAULT, AGENT_MAX_TURNS_DEFAULT }\n`
}

let counter = 0
// `env` entries are set on process.env before the module is evaluated (CLAUDE_BIN is read then); undefined deletes the variable.
export async function loadRegion(env = {}) {
  for (const [k, v] of Object.entries(env)) {
    if (v === undefined) delete process.env[k]
    else process.env[k] = v
  }
  const dir = mkdtempSync(join(tmpdir(), "bridge-region-"))
  const file = join(dir, `region-${++counter}.mjs`)
  writeFileSync(file, regionSource())
  try {
    return await import(pathToFileURL(file).href + `?n=${counter}`)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1] && process.argv[2] === "tool-args") {
  const out = {}
  const savedWarn = console.error
  console.error = () => {}
  for (const [name, env] of Object.entries({
    plain: { EMISSARY_JAIL: undefined, EMISSARY_ALLOW_BASH: undefined, CLAUDE_BIN: "claude" },
    allow_bash: { EMISSARY_JAIL: undefined, EMISSARY_ALLOW_BASH: "1", CLAUDE_BIN: "claude" },
    jail_with_wrapper: { EMISSARY_JAIL: "1", EMISSARY_ALLOW_BASH: undefined, CLAUDE_BIN: "/repo/scripts/agent-run.py" },
    jail_without_wrapper: { EMISSARY_JAIL: "1", EMISSARY_ALLOW_BASH: undefined, CLAUDE_BIN: "claude" },
  })) {
    const r = await loadRegion(env)
    out[name] = Object.fromEntries(["prover", "blind", "architect", "none"].map((k) => [k, r.claudeToolArgs(k)]))
    out[name].caps = r.claudeCapArgs(0)
  }
  console.error = savedWarn
  process.stdout.write(JSON.stringify(out))
}

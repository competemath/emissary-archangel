// node --test scripts/agent-tests/bridge-jail.test.mjs
// The jail region of the bridge: tool flags per kind, the environment of a spawned CLI, caps, the trace. No bridge, no CLI, no network.
import { test } from "node:test"
import assert from "node:assert/strict"
import { chmodSync, existsSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { join, dirname } from "node:path"
import { fileURLToPath } from "node:url"
import { loadRegion } from "./bridge-region.mjs"

const HERE = dirname(fileURLToPath(import.meta.url))
const quiet = () => {
  const saved = console.error
  const lines = []
  console.error = (...a) => lines.push(a.join(" "))
  return { lines, restore: () => (console.error = saved) }
}
const SWITCHES = { EMISSARY_JAIL: undefined, EMISSARY_ALLOW_BASH: undefined, EMISSARY_AGENT_ENV_PASS: undefined, EMISSARY_TRACE_DIR: undefined, EMISSARY_MAX_USD: undefined, EMISSARY_MAX_TURNS: undefined }

test("every kind gets a --tools set and --strict-mcp-config; the bypass only next to a set", async () => {
  const r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude" })
  for (const kind of ["prover", "blind", "architect", "none"]) {
    const args = r.claudeToolArgs(kind)
    assert.ok(args.some((a) => a.startsWith("--tools=")), `${kind}: --tools=`)
    assert.ok(args.includes("--strict-mcp-config"), `${kind}: --strict-mcp-config`)
    assert.ok(!args.some((a) => /allowedTools|disallowedTools/i.test(a)), `${kind}: no permission rules`)
  }
  assert.deepEqual(r.claudeToolArgs("prover"), ["--tools=", "--strict-mcp-config", "--dangerously-skip-permissions"])
  assert.ok(!r.claudeToolArgs("none").includes("--dangerously-skip-permissions"), "a tool-less completion needs no bypass")
  assert.throws(() => r.claudeToolArgs("anything-else"), /unknown agent kind/)
})

test("a shell only inside the proven jail, or on the operator's explicit say-so, and never for the architect", async () => {
  const q = quiet()
  try {
    let r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude" })
    assert.equal(r.claudeToolArgs("prover")[0], "--tools=")
    r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "/repo/scripts/agent-run.py", EMISSARY_JAIL: "1" })
    assert.equal(r.claudeToolArgs("prover")[0], "--tools=Bash")
    assert.equal(r.claudeToolArgs("blind")[0], "--tools=Bash")
    assert.equal(r.claudeToolArgs("architect")[0], "--tools=")
    assert.equal(r.claudeToolArgs("none")[0], "--tools=")
    r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude", EMISSARY_JAIL: "1" })
    assert.equal(r.claudeToolArgs("prover")[0], "--tools=", "EMISSARY_JAIL=1 without the wrapper grants nothing")
    assert.ok(q.lines.some((l) => /EMISSARY_JAIL=1 ignored/.test(l)))
    q.lines.length = 0
    r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude", EMISSARY_ALLOW_BASH: "1" })
    assert.equal(r.claudeToolArgs("prover")[0], "--tools=Bash")
    assert.equal(r.claudeToolArgs("architect")[0], "--tools=")
    assert.ok(q.lines.some((l) => /EMISSARY_ALLOW_BASH=1/.test(l) && /SHELL/.test(l)), "the override is logged loudly")
  } finally {
    q.restore()
  }
})

test("the environment of the CLI holds only the allowlist; the bridge's secrets stay behind", async () => {
  const hostile = {
    BRIDGE_TOKEN: "bridge-secret", GH_TOKEN: "ghs_" + "a".repeat(36), TENGOKU_BOT_TOKEN: "bot-secret", GITHUB_TOKEN: "x", RELAY_TOKEN: "r",
    WORKER_SECRET: "w", XAI_API_KEY: "xai", SOMETHING_ELSE: "1", AWS_SECRET_ACCESS_KEY: "aws", NODE_OPTIONS: "--require /tmp/evil.js",
    LD_PRELOAD: "/tmp/evil.so", HTTPS_PROXY: "http://example.invalid",
  }
  const r = await loadRegion({ ...SWITCHES, ...hostile, CLAUDE_BIN: "claude", CLAUDE_CODE_OAUTH_TOKEN: "tok-oauth", ANTHROPIC_API_KEY: "tok-api", HOME: "/Users/someone", LANG: "C", TZ: "UTC", TERM: "dumb", LC_ALL: "C", TMPDIR: "/tmp" })
  const env = r.agentEnv({ CLAUDE_CODE_MAX_OUTPUT_TOKENS: "64000" })
  const names = Object.keys(env).sort()
  assert.deepEqual(names, ["ANTHROPIC_API_KEY", "CLAUDE_CODE_MAX_OUTPUT_TOKENS", "CLAUDE_CODE_OAUTH_TOKEN", "HOME", "LANG", "LC_ALL", "PATH", "TERM", "TMPDIR", "TZ"].sort())
  assert.equal(env.CLAUDE_CODE_OAUTH_TOKEN, "tok-oauth")
  assert.notEqual(env.HOME, "/Users/someone", "with an explicit credential the agent gets a throwaway HOME")
  assert.ok(existsSync(env.HOME))
  for (const k of Object.keys(hostile)) assert.ok(!(k in env), `${k} must not reach the agent`)
  assert.throws(() => r.agentEnv({ BRIDGE_TOKEN: "x" }), /may not be passed/)
  assert.throws(() => r.agentEnv({ NODE_OPTIONS: "--require x" }), /may not be passed/)
})

test("a developer who relies on `claude login` keeps their HOME; the operator can opt more variables in, but not the secrets", async () => {
  const q = quiet()
  try {
    let r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude", CLAUDE_CODE_OAUTH_TOKEN: undefined, ANTHROPIC_API_KEY: undefined, HOME: "/Users/dev" })
    assert.equal(r.agentEnv().HOME, "/Users/dev")
    r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude", CLAUDE_CODE_OAUTH_TOKEN: undefined, ANTHROPIC_API_KEY: undefined, HOME: "/Users/dev", EMISSARY_AGENT_ENV_PASS: "FOO_CA,GH_TOKEN,GITHUB_ACTIONS", FOO_CA: "/ca.pem", GH_TOKEN: "ghs_" + "b".repeat(36), GITHUB_ACTIONS: "true" })
    const env = r.agentEnv()
    assert.equal(env.FOO_CA, "/ca.pem")
    assert.ok(!("GH_TOKEN" in env) && !("GITHUB_ACTIONS" in env))
    assert.ok(q.lines.some((l) => /GH_TOKEN refused/.test(l)))
  } finally {
    q.restore()
  }
})

test("caps: defaults, environment overrides, the caller's lower turn limit; and the defaults are the wrapper's", async () => {
  let r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude" })
  const py = readFileSync(join(HERE, "..", "agent_policy.py"), "utf8")
  assert.equal(r.AGENT_MAX_USD_DEFAULT, Number(py.match(/DEFAULT_MAX_USD = ([0-9.]+)/)[1]))
  assert.equal(r.AGENT_MAX_TURNS_DEFAULT, Number(py.match(/DEFAULT_MAX_TURNS = ([0-9]+)/)[1]))
  assert.deepEqual(r.claudeCapArgs(0), ["--max-turns", String(r.AGENT_MAX_TURNS_DEFAULT), "--max-budget-usd", String(r.AGENT_MAX_USD_DEFAULT)])
  assert.deepEqual(r.claudeCapArgs(12), ["--max-turns", "12", "--max-budget-usd", String(r.AGENT_MAX_USD_DEFAULT)])
  r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude", EMISSARY_MAX_USD: "3.5", EMISSARY_MAX_TURNS: "50" })
  assert.deepEqual(r.claudeCapArgs(0), ["--max-turns", "50", "--max-budget-usd", "3.5"])
  assert.deepEqual(r.claudeCapArgs(500), ["--max-turns", "50", "--max-budget-usd", "3.5"], "a caller cannot raise the ceiling")
  r = await loadRegion({ ...SWITCHES, CLAUDE_BIN: "claude", EMISSARY_MAX_USD: "nonsense", EMISSARY_MAX_TURNS: "-4" })
  assert.equal(r.agentCaps().maxUsd, r.AGENT_MAX_USD_DEFAULT)
  assert.equal(r.agentCaps().maxTurns, r.AGENT_MAX_TURNS_DEFAULT)
})

test("spawnClaude starts the CLI with that environment, no shell, and tees stdout to a trace file", async () => {
  const dir = mkdtempSync(join(tmpdir(), "fake-claude-"))
  const fake = join(dir, "claude")
  writeFileSync(fake, '#!/bin/sh\necho "ARGS:$*"\nenv\n')
  chmodSync(fake, 0o755)
  const traces = join(dir, "traces")
  const q = quiet()
  try {
    const r = await loadRegion({
      ...SWITCHES, CLAUDE_BIN: fake, EMISSARY_TRACE_DIR: traces, BRIDGE_TOKEN: "bridge-secret", GH_TOKEN: "ghs_" + "c".repeat(36),
      CLAUDE_CODE_OAUTH_TOKEN: "tok-oauth", ANTHROPIC_API_KEY: undefined, SOME_OTHER: "1",
    })
    const child = r.spawnClaude(["-p", "hello; touch /tmp/should-not-exist", ...r.claudeToolArgs("none")], { kind: "none", stdio: ["ignore", "pipe", "pipe"], extraEnv: { CLAUDE_CODE_MAX_OUTPUT_TOKENS: "123" } })
    let out = ""
    child.stdout.setEncoding("utf8")
    child.stdout.on("data", (c) => (out += c))
    await new Promise((resolve) => child.on("close", resolve))
    assert.match(out, /ARGS:-p hello; touch \/tmp\/should-not-exist --tools= --strict-mcp-config/)
    assert.ok(!/BRIDGE_TOKEN|GH_TOKEN|SOME_OTHER/.test(out), "none of the bridge's variables reach the CLI")
    assert.match(out, /CLAUDE_CODE_OAUTH_TOKEN=tok-oauth/)
    assert.match(out, /CLAUDE_CODE_MAX_OUTPUT_TOKENS=123/)
    assert.ok(!existsSync("/tmp/should-not-exist"), "no shell interpreted the prompt")
    const files = readdirSync(traces)
    assert.equal(files.length, 1)
    assert.match(files[0], /^\d+-\d+-none-[0-9a-f]{8}\.jsonl$/)
    assert.equal(readFileSync(join(traces, files[0]), "utf8"), out, "the trace is the CLI's stdout, byte for byte")
  } finally {
    q.restore()
    rmSync(dir, { recursive: true, force: true })
  }
})

// The translation pipeline as a set of local processes the console can start,
// stop and watch: the three tree-based Leak/Gate services, a private bridge,
// the promote loop in the working tree, and the recursion run itself
// (scripts/run-recurse.mjs against that bridge). Every process is spawned
// detached with its own pid file and log under data/pipeline/, so it survives
// the console tab, a dev-server reload, and a closed laptop lid. Server-only.
import { spawn, execFile } from "node:child_process";
import { promisify } from "node:util";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";

const execFileAsync = promisify(execFile);
const APP_ROOT = process.cwd();
const HOME = os.homedir();
const STATE_DIR = path.join(APP_ROOT, "data", "pipeline");
const CONFIG_PATH = path.join(APP_ROOT, "data", "pipeline-config.json");
// Spawned processes need lake/lean (elan) and node/python on PATH even when the
// dev server was started from a minimal environment.
const TOOL_PATH = [path.join(HOME, ".elan", "bin"), "/opt/homebrew/bin", "/usr/local/bin", process.env.PATH || ""].join(":");

export type ServiceName = "leak-iv" | "gate2" | "leak-i" | "bridge";
export type ProcName = ServiceName | "promote" | "run" | "tree-refresh";
export const SERVICE_NAMES: ServiceName[] = ["leak-iv", "gate2", "leak-i", "bridge"];

export type RunScope = { type: "all" } | { type: "file"; sourcePath: string } | { type: "one"; id: number };

export interface PipelineConfig {
  /** Cache-pinned clone the Leak services run on. Never built: scripts/pin.sh only. */
  treeDir: string;
  /** The working tree the promote loop compiles newly promoted modules into. */
  workTree: string;
  /** Corpus checkout promote.py reads source files from. */
  corpusRoot: string;
  leakIv: { dir: string; python: string; port: number };
  gate2: { dir: string; python: string; port: number };
  leakI: { dir: string; python: string; port: number; loogleDir: string };
  bridge: { port: number; token: string };
  promote: { library: string; intervalS: number; quiescentS: number; viaPrs: boolean };
  run: { source: string; timeoutMin: number };
}

export const DEFAULT_CONFIG: PipelineConfig = {
  treeDir: path.join(HOME, "tengoku-cache"),
  workTree: process.env.TENGOKU_STAGING_REPO || path.join(APP_ROOT, "..", "compete-math", "tengoku"),
  corpusRoot: path.join(APP_ROOT, "infra", "equational-theories-4291", "repo"),
  leakIv: { dir: path.join(HOME, "Downloads", "Leak-IV"), python: ".venv/bin/python", port: 7871 },
  gate2: { dir: path.join(HOME, "emissary-gate2-tengoku"), python: path.join(HOME, "emissary-gate2", "venv", "bin", "python"), port: 7872 },
  leakI: { dir: path.join(HOME, "Leak-I"), python: ".venv-tree/bin/python", port: 7874, loogleDir: path.join(HOME, "loogle") },
  bridge: { port: 4125, token: "archangel-run-token" },
  promote: { library: "equational-theories", intervalS: 300, quiescentS: 300, viaPrs: false },
  run: { source: "equational-theories", timeoutMin: 20 },
};

function ensureStateDir() {
  fs.mkdirSync(STATE_DIR, { recursive: true });
}

export function loadConfig(): PipelineConfig {
  try {
    const saved = JSON.parse(fs.readFileSync(CONFIG_PATH, "utf8")) as Partial<PipelineConfig>;
    const merged: PipelineConfig = { ...DEFAULT_CONFIG, ...saved } as PipelineConfig;
    for (const k of ["leakIv", "gate2", "leakI", "bridge", "promote", "run"] as const) {
      merged[k] = { ...DEFAULT_CONFIG[k], ...(saved[k] as object | undefined) } as never;
    }
    return merged;
  } catch {
    return DEFAULT_CONFIG;
  }
}

export function saveConfig(patch: Partial<PipelineConfig>): PipelineConfig {
  ensureStateDir();
  const next = { ...loadConfig(), ...patch } as PipelineConfig;
  fs.writeFileSync(CONFIG_PATH, JSON.stringify(next, null, 2) + "\n");
  return next;
}

// ---- process registry --------------------------------------------------------
const pidFile = (name: ProcName) => path.join(STATE_DIR, `${name}.pid`);
export const logFile = (name: ProcName) => path.join(STATE_DIR, `${name}.log`);

function alive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

export interface ProcState {
  pid: number | null;
  alive: boolean;
  startedAt: string | null;
}

export function procState(name: ProcName): ProcState {
  try {
    const { pid, startedAt } = JSON.parse(fs.readFileSync(pidFile(name), "utf8")) as { pid: number; startedAt: string };
    return { pid, alive: alive(pid), startedAt };
  } catch {
    return { pid: null, alive: false, startedAt: null };
  }
}

function startProc(name: ProcName, cmd: string, args: string[], cwd: string, env: Record<string, string>, truncateLog = false) {
  ensureStateDir();
  const st = procState(name);
  if (st.alive) throw new Error(`${name} is already running (pid ${st.pid})`);
  if (!fs.existsSync(cwd)) throw new Error(`${name}: directory not found: ${cwd}`);
  const out = fs.openSync(logFile(name), truncateLog ? "w" : "a");
  fs.writeSync(out, `\n===== ${new Date().toISOString()} start: ${cmd} ${args.join(" ")} (cwd ${cwd}) =====\n`);
  const child = spawn(cmd, args, {
    cwd,
    env: { ...process.env, PATH: TOOL_PATH, HOME, ...env },
    detached: true,
    stdio: ["ignore", out, out],
  });
  child.on("error", (e) => fs.appendFileSync(logFile(name), `spawn error: ${e.message}\n`));
  child.unref();
  fs.closeSync(out);
  fs.writeFileSync(pidFile(name), JSON.stringify({ pid: child.pid, startedAt: new Date().toISOString() }));
  return child.pid;
}

export async function stopProc(name: ProcName): Promise<boolean> {
  const st = procState(name);
  if (!st.pid || !st.alive) {
    try { fs.unlinkSync(pidFile(name)); } catch { /* none */ }
    return false;
  }
  // Detached children lead their own process group: signal the group so a
  // loop's children (python, lake) go with it.
  const sig = (s: NodeJS.Signals) => { try { process.kill(-st.pid!, s); } catch { try { process.kill(st.pid!, s); } catch { /* gone */ } } };
  sig("SIGTERM");
  for (let i = 0; i < 25 && alive(st.pid); i++) await new Promise((r) => setTimeout(r, 200));
  if (alive(st.pid)) sig("SIGKILL");
  try { fs.unlinkSync(pidFile(name)); } catch { /* none */ }
  fs.appendFileSync(logFile(name), `===== ${new Date().toISOString()} stopped by the console =====\n`);
  return true;
}

export function tailLog(name: ProcName, lines = 40): string[] {
  try {
    const buf = fs.readFileSync(logFile(name), "utf8");
    const all = buf.split("\n");
    if (all[all.length - 1] === "") all.pop();
    return all.slice(-lines);
  } catch {
    return [];
  }
}

// ---- the processes -------------------------------------------------------------
async function leanPath(loogleDir: string): Promise<string> {
  const { stdout } = await execFileAsync("lake", ["env", "printenv", "LEAN_PATH"], { cwd: loogleDir, env: { ...process.env, PATH: TOOL_PATH, HOME } });
  return stdout.trim();
}

export async function startService(name: ServiceName, cfg = loadConfig()): Promise<number | undefined> {
  const p = (dir: string, exe: string) => (path.isAbsolute(exe) ? exe : path.join(dir, exe));
  switch (name) {
    case "leak-iv":
      return startProc(name, p(cfg.leakIv.dir, cfg.leakIv.python), ["server.py"], cfg.leakIv.dir, {
        PORT: String(cfg.leakIv.port),
        LEAN_PROJECT_PATH: cfg.treeDir,
        TENGOKU_IMPORTS: "import Tengoku.All",
        TENGOKU_AUTO_REFRESH: "0", // the console refreshes the clone explicitly (Tree → Refresh cache)
      });
    case "gate2":
      return startProc(name, p(cfg.gate2.dir, cfg.gate2.python), ["server.py"], cfg.gate2.dir, {
        PORT: String(cfg.gate2.port),
        GATE2_TREE_IMPORT: "Tengoku.All",
        EMISSARY_OLD_EXPORT: path.join(APP_ROOT, "data", "export.ndjson"),
      });
    case "leak-i":
      return startProc(name, p(cfg.leakI.dir, cfg.leakI.python), ["server.py"], cfg.leakI.dir, {
        PORT: String(cfg.leakI.port),
        TENGOKU_DIR: cfg.treeDir,
        TENGOKU_AUTO_REFRESH: "0",
        LEAN_PATH: await leanPath(cfg.leakI.loogleDir),
      });
    case "bridge":
      return startProc(name, "node", ["public/local-claude-bridge.mjs"], APP_ROOT, {
        PORT: String(cfg.bridge.port),
        BRIDGE_TOKEN: cfg.bridge.token,
        EMISSARY_APP_ROOT: APP_ROOT,
      });
  }
}

export function startPromote(cfg = loadConfig()) {
  // PR mode: the loop opens one promotion PR per source file instead of pushing main (scripts/promote-loop.sh in the tree).
  return startProc("promote", "bash", ["scripts/promote-loop.sh", cfg.corpusRoot, cfg.promote.library, String(cfg.promote.intervalS), String(cfg.promote.quiescentS)], cfg.workTree, cfg.promote.viaPrs ? { TENGOKU_VIA_PRS: "1" } : {});
}

export function startRun(scope: RunScope, cfg = loadConfig()) {
  const sse = (port: number) => `http://127.0.0.1:${port}/sse`;
  return startProc("run", "node", ["scripts/run-recurse.mjs", String(cfg.bridge.port), cfg.bridge.token, JSON.stringify(scope)], APP_ROOT, {
    EMISSARY_LEAK_IV_URL: sse(cfg.leakIv.port),
    EMISSARY_LEAK_I_URL: sse(cfg.leakI.port),
    EMISSARY_GATE2_URL: sse(cfg.gate2.port),
    EMISSARY_RUN_TIMEOUT_MS: String(Math.max(1, cfg.run.timeoutMin) * 60 * 1000),
    RECURSE_LOG: "", // stdout is the log (data/pipeline/run.log)
  }, true);
}

/** Move the cache-pinned clone to the newest published cache (download only, never a build). */
export function startTreeRefresh(cfg = loadConfig()) {
  return startProc("tree-refresh", "bash", ["scripts/pin.sh"], cfg.treeDir, {}, true);
}

// ---- status ---------------------------------------------------------------------
async function portHealth(port: number, timeoutMs = 2500): Promise<number> {
  const ctl = new AbortController();
  const t = setTimeout(() => ctl.abort(), timeoutMs);
  try {
    const res = await fetch(`http://127.0.0.1:${port}/sse`, { headers: { Accept: "text/event-stream" }, signal: ctl.signal });
    res.body?.cancel().catch(() => {});
    return res.status;
  } catch {
    return 0;
  } finally {
    clearTimeout(t);
  }
}

export interface RunProgress {
  state: "running" | "done" | "stopped" | "idle";
  processed: number;
  total: number;
  summary: Record<string, number>;
  inScope: number | null;
  startedAt: string | null;
}

function parseRun(lines: string[], st: ProcState): RunProgress {
  let processed = 0, total = 0, summary: Record<string, number> = {}, inScope: number | null = null, done = false;
  for (const l of lines) {
    const m = l.match(/\] (PROGRESS|DONE) (\d+)\/(\d+) (\{.*\})/);
    if (m) {
      processed = Number(m[2]); total = Number(m[3]);
      try { summary = JSON.parse(m[4]); } catch { /* keep */ }
      if (m[1] === "DONE") done = true;
    }
    const s = l.match(/Recursive translation: (\d+) pending/);
    if (s) inScope = Number(s[1]);
    if (/\] stream ended/.test(l)) done = true;
  }
  const state: RunProgress["state"] = st.alive ? "running" : done ? "done" : lines.length ? "stopped" : "idle";
  return { state, processed, total, summary, inScope, startedAt: st.startedAt };
}

export interface QueueSummary {
  counts: Record<string, number>;
  files: { sourcePath: string; pending: number }[];
}

export function queueSummary(source: string): QueueSummary {
  try {
    const raw = JSON.parse(fs.readFileSync(path.join(APP_ROOT, "data", `queue-${source}.json`), "utf8"));
    const items: { status?: string; sourcePath?: string }[] = Array.isArray(raw) ? raw : raw.items ?? raw.entries ?? [];
    const counts: Record<string, number> = {};
    const perFile = new Map<string, number>();
    for (const e of items) {
      const s = e.status || "unknown";
      counts[s] = (counts[s] || 0) + 1;
      if (s === "pending" && typeof e.sourcePath === "string") perFile.set(e.sourcePath, (perFile.get(e.sourcePath) || 0) + 1);
    }
    const files = [...perFile.entries()].map(([sourcePath, pending]) => ({ sourcePath, pending })).sort((a, b) => b.pending - a.pending || a.sourcePath.localeCompare(b.sourcePath));
    return { counts, files };
  } catch {
    return { counts: {}, files: [] };
  }
}

export async function treeState(cfg = loadConfig()) {
  const exists = fs.existsSync(cfg.treeDir);
  let head = "";
  if (exists) {
    try { head = (await execFileAsync("git", ["rev-parse", "--short=12", "HEAD"], { cwd: cfg.treeDir })).stdout.trim(); } catch { /* not a repo */ }
  }
  const built = exists && fs.existsSync(path.join(cfg.treeDir, ".lake", "build", "lib", "lean", "Tengoku", "All.olean"));
  return { dir: cfg.treeDir, exists, head, built, refresh: procState("tree-refresh"), refreshLog: tailLog("tree-refresh", 6) };
}

/** Ask GitHub whether a newer cache than the clone's commit is published (changes nothing). */
export async function checkTree(cfg = loadConfig()): Promise<{ status: string; detail: string }> {
  try {
    const { stdout } = await execFileAsync("bash", ["scripts/pin.sh", "--check"], { cwd: cfg.treeDir, env: { ...process.env, PATH: TOOL_PATH, HOME }, timeout: 120_000 });
    const [status, sha] = stdout.trim().split(/\s+/);
    return { status, detail: sha || "" };
  } catch (e) {
    const err = e as { stdout?: string; code?: number; message?: string };
    const line = (err.stdout || "").trim().split("\n").pop() || "";
    if (err.code === 3 && line.startsWith("newer")) return { status: "newer", detail: line.split(/\s+/)[1] || "" };
    return { status: "error", detail: line || err.message || "check failed" };
  }
}

export async function status(logLines = 60) {
  const cfg = loadConfig();
  const services = await Promise.all(SERVICE_NAMES.map(async (name) => {
    const port = name === "leak-iv" ? cfg.leakIv.port : name === "gate2" ? cfg.gate2.port : name === "leak-i" ? cfg.leakI.port : cfg.bridge.port;
    const st = procState(name);
    const http = await portHealth(port);
    // The bridge answers /sse with 403 for a foreign origin — any answer means up.
    const up = name === "bridge" ? http > 0 : http === 200;
    return { name, port, ...st, http, up, log: tailLog(name, 12) };
  }));
  const promote = { ...procState("promote"), log: tailLog("promote", 8) };
  const runLog = tailLog("run", logLines);
  const run = { ...parseRun(tailLog("run", 4000), procState("run")), log: runLog };
  return { config: cfg, services, promote, run, queue: queueSummary(cfg.run.source), tree: await treeState(cfg), now: new Date().toISOString() };
}

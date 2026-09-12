// Emissary-Archangel queue driver. Reads data/queue.json, runs each pending
// entry through the SAME proveControl() the modified Control-II harness uses
// (public/local-claude-bridge.mjs) — dual-gate enforcement (Leak IV +
// Archangel Gate 2) lives there, unchanged, not duplicated here. This script
// only does orchestration: pick the next entry, build a ctx, run it, persist
// the result, move on.

import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { proveControl } from "../public/local-claude-bridge.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const QUEUE_PATH = path.join(__dirname, "..", "data", "queue.json");

const VERIFY_URL = process.env.EMISSARY_LEAK_IV_URL || "https://barkingtree-leak-iv.hf.space/sse";
const ARCHANGEL_URL = process.env.EMISSARY_GATE2_URL || "http://localhost:7861/sse";
const LEAK_I_URL = process.env.EMISSARY_LEAK_I_URL || ""; // optional — Control-II's search tool
const NODE_TIMEOUT_MS = Number(process.env.EMISSARY_NODE_TIMEOUT_MS || 20 * 60 * 1000);
const MODEL = process.env.EMISSARY_MODEL || undefined;

function loadQueue() {
  return JSON.parse(readFileSync(QUEUE_PATH, "utf8"));
}
function saveQueue(queue) {
  writeFileSync(QUEUE_PATH, JSON.stringify(queue, null, 2));
}

function buildMcpServers() {
  const servers = [{ name: "Leak_IV", url: VERIFY_URL, tools: ["verify_full_script"] }];
  if (LEAK_I_URL) servers.push({ name: "Leak_I", url: LEAK_I_URL, tools: ["loogle_search", "moogle_search"] });
  // Archangel's own MCP server is NOT listed here deliberately at first glance
  // — but the agent DOES need to call gate2_verify_entailment, so it must be
  // a connected MCP server too, exposed to the agent like any other tool.
  servers.push({ name: "Archangel", url: ARCHANGEL_URL, tools: ["gate2_verify_entailment"] });
  return servers;
}

async function runOne(entry) {
  const deadline = Date.now() + NODE_TIMEOUT_MS;
  const ctx = {
    signal: undefined,
    mcpServers: buildMcpServers(),
    verifyUrl: VERIFY_URL,
    verifyTimeoutMs: 180000,
    model: MODEL,
    nodeTimeoutMs: NODE_TIMEOUT_MS,
    getDeadline: () => deadline,
    metrics: {},
    searchBudget: { remaining: 0, initial: 0 }, // Control-II search governance; 0 = search disabled unless Leak I is wired
    emit: (obj) => {
      const t = obj?.thought || obj?.type || "";
      if (t) console.log(`[${entry.id}] ${t}`);
    },
    archangelUrl: ARCHANGEL_URL,
    archangelOldRef: { old_id: String(entry.id), old_export_names: entry.oldExportNames },
  };
  return proveControl(entry.oldTheoremText, ctx, 2);
}

async function main() {
  const onlyId = process.argv[2] ? Number(process.argv[2]) : null;
  const queue = loadQueue();
  const targets = onlyId ? queue.filter((e) => e.id === onlyId) : queue.filter((e) => e.status === "pending");
  if (targets.length === 0) {
    console.log("Nothing to do (no pending entries, or --id matched nothing).");
    return;
  }
  console.log(`Running ${targets.length} entr${targets.length === 1 ? "y" : "ies"}...`);
  for (const entry of targets) {
    console.log(`\n=== id=${entry.id} name=${entry.name} ===`);
    entry.status = "running";
    saveQueue(queue);
    try {
      const result = await runOne(entry);
      entry.status = result.verified ? "verified" : "failed";
      entry.proof = result.verified ? result.proof : undefined;
      entry.finishedAt = new Date().toISOString();
      console.log(`=== id=${entry.id} -> ${entry.status} ===`);
    } catch (e) {
      entry.status = "error";
      entry.error = e?.message || String(e);
      console.error(`=== id=${entry.id} -> error: ${entry.error} ===`);
    }
    saveQueue(queue);
  }
}

main();

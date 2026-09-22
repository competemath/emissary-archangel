'use client';

import { useEffect, useRef, useState } from 'react';
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Label } from '@/components/ui/label';
import { Badge } from '@/components/ui/badge';
import { MCPServerDialog } from '@/components/mcp-server-dialog';
import { ProverConsole } from '@/components/prover/prover-console';
import { listMcpServers } from '@/lib/mcp/local-mcp-store';
import type { MCPServer } from '@/lib/types/mcp';
import type { ProverEvent, ProverEventKind } from '@/lib/prover/types';

interface QueueEntry {
  id: number;
  name: string;
  // Optional: CompeteMath's entries carry this directly (small enough that
  // redundancy is fine). Equational Theories' don't — theirs is constructed
  // on demand from sourcePath/sourceLine via /api/queue/theorem-text right
  // before a run dispatches (see executeEntry), since baking it in per-entry
  // blew that queue file up to 524MB (many theorems share one source file).
  oldTheoremText?: string;
  sourcePath?: string;
  sourceLine?: number;
  oldExportNames: string;
  status: 'pending' | 'queued' | 'running' | 'verified' | 'failed' | 'error';
  proof?: string;
  error?: string;
  exportNamesConfirmed: boolean;
  // Present on non-CompeteMath sources — which corpus this row came from,
  // its file-structure category (e.g. "ManuallyProved" vs a Generated/*
  // search strategy), and the exact upstream location for traceability.
  source?: string;
  category?: string;
  sourceRef?: string;
}

// Every distinct translation corpus this app can run, each backed by its own
// queue file (see app/api/queue/route.ts's SOURCES allowlist) — never
// merged into one file, so switching sources never risks one corpus's queue
// corrupting another's.
// Shown until /api/sources answers (sources.json is the real list).
const DEFAULT_QUEUE_SOURCES: { key: string; label: string }[] = [
  { key: 'competemath', label: 'CompeteMath' },
  { key: 'equational-theories', label: 'Equational Theories' },
];
const PAGE_SIZE = 50;

interface ServerStatus {
  connected: boolean;
  tools: string[];
  checking: boolean;
  error?: string;
}

const BRIDGE_KEY = 'emissary.bridgeUrl';
const TOKEN_KEY = 'emissary.bridgeToken';
// The recursion engine's live log lives under this synthetic id in `events`
// (real queue ids are positive), so it shares the ProverConsole below.
const RECURSE_LOG_ID = -1;

interface RecurseRun {
  running: boolean;
  scope: string;
  processed: number;
  total: number;
  summary: Record<string, number>;
}
const DEFAULT_MAX_PARALLEL = 3;
const LEAK_IV_TOOL = 'verify_full_script';
const ARCHANGEL_TOOL = 'gate2_verify_entailment';

// Same generator compete-math's own local-claude-agent-management.tsx uses —
// the bridge is always started via a copy-pasted terminal command carrying a
// token this app generated itself, never one the user has to type in by hand.
function generateToken(): string {
  const bytes = new Uint8Array(24);
  crypto.getRandomValues(bytes);
  let binary = '';
  for (const b of bytes) binary += String.fromCharCode(b);
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

export function QueueConsole() {
  const [source, setSource] = useState<string>('competemath');
  const [queueSources, setQueueSources] = useState<{ key: string; label: string }[]>(DEFAULT_QUEUE_SOURCES);
  useEffect(() => {
    fetch('/api/sources', { cache: 'no-store' })
      .then((r) => (r.ok ? r.json() : null))
      .then((body: { sources?: { key: string; label: string; ready: boolean }[] } | null) => {
        const ready = (body?.sources || []).filter((s) => s.ready).map((s) => ({ key: s.key, label: s.label }));
        if (ready.length) setQueueSources(ready);
      })
      .catch(() => undefined);
  }, []);
  const [queue, setQueue] = useState<QueueEntry[]>([]);
  // Table-only view controls — the underlying queue/active/queued/events
  // state is untouched by these; a 13,164-row source needs filtering and
  // pagination to stay usable, a 232-row one doesn't but isn't hurt by it.
  const [nameFilter, setNameFilter] = useState('');
  const [categoryFilter, setCategoryFilter] = useState('all');
  const [statusFilter, setStatusFilter] = useState('all');
  const [page, setPage] = useState(0);
  const [servers, setServers] = useState<MCPServer[]>([]);
  const [serverStatus, setServerStatus] = useState<Record<string, ServerStatus>>({});
  const [bridgeUrl, setBridgeUrl] = useState('http://127.0.0.1:4123');
  const [bridgeToken, setBridgeToken] = useState('');
  const [origin, setOrigin] = useState('');
  const [copied, setCopied] = useState(false);
  const [maxParallel, setMaxParallel] = useState(DEFAULT_MAX_PARALLEL);

  // Real worker-pool queue: `queuedIds` is a FIFO of ids waiting for a free
  // slot, `activeIds` is who currently holds one. Clicking Run always just
  // enqueues — it never blocks on anything else finishing first. `pump()` is
  // the only thing that starts new work, called whenever the queue changes
  // or a slot frees up.
  const [queuedIds, setQueuedIds] = useState<number[]>([]);
  const [activeIds, setActiveIds] = useState<number[]>([]);
  // Real ProverEvent[] per run — not a flat string log. Rendered by the same
  // <ProverConsole> the benchmark/playground routes use, so tool calls, tool
  // results, and thinking blocks are actually visible, not collapsed into an
  // opaque "thought" line.
  const [events, setEvents] = useState<Record<number, ProverEvent[]>>({});
  const [selectedLogId, setSelectedLogId] = useState<number | null>(null);
  const eventIdSeq = useRef(0);
  const abortControllers = useRef<Map<number, AbortController>>(new Map());
  // One recursion run at a time — the bridge's per-file prefix cache and the
  // Gate 2 daemon are both single-flight, so a second concurrent run would
  // only fight the first for the same export parse.
  const recurseAbort = useRef<AbortController | null>(null);
  const [recurseRun, setRecurseRun] = useState<RecurseRun | null>(null);
  // Race-guard for connection checks — same pattern as MCPServerList's
  // connectingServers ref: prevents a re-render (or a manual "Test" click
  // while an automatic check is already in flight) from firing a duplicate
  // handshake against the same server.
  const checkingRef = useRef<Set<string>>(new Set());
  // Refs mirroring the state above, so the async pump/executor loop always
  // reads the LATEST queue/active sets rather than a stale closure — React
  // state updates inside an async chain would otherwise race each other.
  const queuedRef = useRef<number[]>([]);
  const activeRef = useRef<number[]>([]);
  const queueEntriesRef = useRef<QueueEntry[]>([]);
  const serverStatusRef = useRef<Record<string, ServerStatus>>({});
  const bridgeRef = useRef({ url: bridgeUrl, token: bridgeToken });

  // Re-fetches whenever `source` changes — switching corpora just swaps
  // which queue file backs the table. Any run already active/queued keeps
  // going regardless of which source is currently displayed (activeIds/
  // queuedIds/events are keyed by id, and ids are disjoint across sources by
  // construction — see route.ts's SOURCES comment), it just won't show a row
  // in the table until you switch back; the "active runs" tab strip at the
  // bottom still finds it.
  const loadQueue = (src: string) => {
    fetch(`/api/queue?source=${encodeURIComponent(src)}`)
      .then(async (r) => {
        if (!r.ok) {
          const body = await r.json().catch(() => ({ error: 'unknown', detail: r.statusText }));
          throw new Error(`GET /api/queue failed: ${body.error || r.status} — ${body.detail || ''}`);
        }
        return r.json();
      })
      .then((q: QueueEntry[]) => {
        // Reconcile stale state: `running`/`queued` in the persisted file can
        // only mean a PREVIOUS page session's process was tracking them — this
        // component's own activeIds/queuedIds always start empty on mount, so
        // there is, definitionally, no live run behind either status right
        // now (a page reload, a killed bridge, a crashed tab — the file
        // doesn't know the difference, and shouldn't keep claiming otherwise).
        // Found live: entries stuck showing "running" with 0 active/0 queued
        // in the UI's own counter, right after a fresh reload.
        const stale = q.filter((e) => e.status === 'running' || e.status === 'queued');
        const reconciled = q.map((e) =>
          e.status === 'running' || e.status === 'queued' ? { ...e, status: 'pending' as const } : e,
        );
        setQueue(reconciled);
        queueEntriesRef.current = reconciled;
        setPage(0);
        for (const e of stale) updateEntry(e.id, { status: 'pending' }, src);
      })
      .catch((e) => {
        // eslint-disable-next-line no-console
        console.error(e);
      });
  };

  useEffect(() => {
    loadQueue(source);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [source]);

  useEffect(() => {
    const s = listMcpServers();
    setServers(s);
    setOrigin(window.location.origin);
    const savedUrl = localStorage.getItem(BRIDGE_KEY);
    let savedToken = localStorage.getItem(TOKEN_KEY);
    if (!savedToken) {
      savedToken = generateToken();
      localStorage.setItem(TOKEN_KEY, savedToken);
    }
    if (savedUrl) setBridgeUrl(savedUrl);
    setBridgeToken(savedToken);
  }, []);

  useEffect(() => {
    bridgeRef.current = { url: bridgeUrl, token: bridgeToken };
  }, [bridgeUrl, bridgeToken]);

  // Auto-check every active server once the bridge connection is known —
  // mirrors MCPServerList's on-mount auto-reconnect, just without a backend
  // to persist "was connected last time" across page loads.
  useEffect(() => {
    if (bridgeToken) testAllServers();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [bridgeToken, servers.length]);

  const persistConnection = () => {
    localStorage.setItem(BRIDGE_KEY, bridgeUrl);
    localStorage.setItem(TOKEN_KEY, bridgeToken);
  };

  // Derive the port from the Bridge URL field so PORT= only appears in the
  // command when it isn't the bridge's own default — same convention as the
  // source component, so multiple bridges (multiple ports/tokens) can run
  // side by side if you ever need that.
  let bridgePort = '';
  try {
    bridgePort = new URL(bridgeUrl).port;
  } catch {
    /* malformed URL — fall back to no PORT= override */
  }
  const portEnv = bridgePort && bridgePort !== '4123' ? `PORT='${bridgePort}' ` : '';
  const appRoot = process.env.NEXT_PUBLIC_EMISSARY_APP_ROOT || '';
  const appRootEnv = appRoot ? `EMISSARY_APP_ROOT='${appRoot.replace(/'/g, "'\\''")}' ` : '';
  const setupCommand =
    origin && bridgeToken
      ? `curl -fsSL '${origin}/local-claude-bridge.mjs' -o claude-bridge.mjs && ${portEnv}${appRootEnv}BRIDGE_TOKEN='${bridgeToken}' ALLOWED_ORIGINS='${origin}' node claude-bridge.mjs`
      : '';

  const copyCommand = async () => {
    if (!setupCommand) return;
    try {
      await navigator.clipboard.writeText(setupCommand);
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    } catch {
      /* clipboard unavailable — the command is still visible to select by hand */
    }
  };

  const refreshServers = () => {
    const s = listMcpServers();
    setServers(s);
    testAllServers(s);
  };

  // Real connect-and-verify, routed through the bridge (avoids CORS and
  // reuses its already-proven MCP-SSE client instead of a browser-side
  // reimplementation) — this is what "Connected" actually means here: the
  // server answered tools/list moments ago, not a stored flag nobody checked.
  const testServer = async (server: MCPServer) => {
    if (checkingRef.current.has(server.id)) return;
    checkingRef.current.add(server.id);
    setServerStatus((s) => {
      const next = { ...s, [server.id]: { ...(s[server.id] || { connected: false, tools: [] }), checking: true } };
      serverStatusRef.current = next;
      return next;
    });
    try {
      const res = await fetch(`${bridgeRef.current.url.replace(/\/$/, '')}/mcp-list-tools`, {
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-bridge-token': bridgeRef.current.token },
        body: JSON.stringify({ url: server.url }),
      });
      const data = await res.json();
      setServerStatus((s) => {
        const next = {
          ...s,
          [server.id]: {
            connected: !!data.ok,
            tools: Array.isArray(data.tools) ? data.tools.map((t: { name: string }) => t.name) : [],
            checking: false,
            error: data.error,
          },
        };
        serverStatusRef.current = next;
        return next;
      });
    } catch (e) {
      setServerStatus((s) => {
        const next = {
          ...s,
          [server.id]: { connected: false, tools: [], checking: false, error: e instanceof Error ? e.message : String(e) },
        };
        serverStatusRef.current = next;
        return next;
      });
    } finally {
      checkingRef.current.delete(server.id);
    }
  };

  const testAllServers = (list?: MCPServer[]) => {
    for (const s of (list ?? servers).filter((x) => x.isActive)) testServer(s);
  };

  // Resolve "the Leak IV server" / "the Archangel server" by which tool a
  // CONNECTED server actually exposes — not by guessing from its name. A
  // server named "Leak_IV" that's actually unreachable, or exposes nothing
  // useful, is correctly not picked.
  const resolveByTool = (toolName: string): MCPServer | undefined =>
    servers.find((s) => serverStatusRef.current[s.id]?.connected && serverStatusRef.current[s.id]?.tools.includes(toolName));

  // `entrySource`, when given, is authoritative — callers that already hold
  // the full entry (executeEntry, enqueue) always pass entry.source so a
  // background run for one corpus is patched into ITS OWN file even if the
  // table has since switched to viewing a different source. Only the
  // fallback lookup (queueEntriesRef, then the 'competemath' default) is
  // used when a caller has nothing but the bare id (cancelQueued).
  const updateEntry = async (id: number, patch: Partial<QueueEntry>, entrySource?: string) => {
    const src = entrySource ?? queueEntriesRef.current.find((e) => e.id === id)?.source ?? 'competemath';
    setQueue((q) => {
      const next = q.map((e) => (e.id === id ? { ...e, ...patch } : e));
      queueEntriesRef.current = next;
      return next;
    });
    try {
      const res = await fetch(`/api/queue?source=${encodeURIComponent(src)}`, {
        method: 'PATCH',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ id, ...patch }),
      });
      if (!res.ok) {
        const body = await res.json().catch(() => ({ error: 'unknown' }));
        // eslint-disable-next-line no-console
        console.error(`PATCH /api/queue failed for #${id}:`, body);
      }
    } catch (e) {
      // The local (optimistic) state already updated above — this only means
      // the on-disk copy didn't. Surfaced so a real persistence gap isn't
      // silently invisible, without blocking the UI on it.
      // eslint-disable-next-line no-console
      console.error(`PATCH /api/queue network error for #${id}:`, e);
    }
  };

  const appendEvent = (id: number, kind: ProverEventKind, label: string, extra: Partial<ProverEvent> = {}) => {
    const ev: ProverEvent = { id: ++eventIdSeq.current, ts: Date.now(), kind, label, ...extra };
    setEvents((e) => ({ ...e, [id]: [...(e[id] || []), ev] }));
  };

  // Same raw-object -> ProverEvent mapping run-prover-stream.ts uses for the
  // benchmark/playground consoles — Control-II's stream already carries
  // tool_intent/tool_result/thinking frames (mapObjectToEvents, bridge-side),
  // this was just never being read on this end.
  const handleStreamObject = (id: number, d: Record<string, unknown>) => {
    switch (d.type) {
      case 'thinking':
        appendEvent(id, 'thinking', 'Thinking…', { detail: String(d.text ?? d.content ?? '') });
        break;
      case 'text-delta':
        if (typeof d.content === 'string' && d.content.trim()) {
          appendEvent(id, 'text', 'Output', { detail: d.content });
        }
        break;
      case 'message-annotation': {
        const subtype = d.subtype;
        const thought = typeof d.thought === 'string' ? d.thought : undefined;
        if (subtype === 'tool_intent') {
          appendEvent(id, 'tool_call', `Tool → ${d.tool}`, {
            tool: typeof d.tool === 'string' ? d.tool : undefined,
            input: typeof d.input === 'string' ? d.input : undefined,
          });
        } else if (subtype === 'tool_result') {
          const out = String(d.output ?? '');
          const looksLikeError = /error|failed|exception/i.test(out.slice(0, 200));
          appendEvent(id, looksLikeError ? 'tool_error' : 'tool_result', looksLikeError ? 'Tool error' : 'Tool result', { detail: out });
        } else if (subtype === 'error') {
          appendEvent(id, 'rejected', thought || 'Rejected');
        } else if (subtype === 'formalising') {
          appendEvent(id, 'formalising', thought || 'Formalising the statement…');
        } else if (thought) {
          appendEvent(id, 'text', thought.slice(0, 200), { detail: thought });
        }
        break;
      }
      case 'error':
        appendEvent(id, 'error', typeof d.message === 'string' ? d.message : 'Prover error');
        break;
      default:
        break;
    }
  };

  // The actual per-theorem run — unchanged from before except it no longer
  // owns any global "is something running" state. Whoever calls this has
  // already reserved a slot; this function's only job on exit is to free it.
  const executeEntry = async (entry: QueueEntry) => {
    const leakIv = resolveByTool(LEAK_IV_TOOL);
    const archangel = resolveByTool(ARCHANGEL_TOOL);
    if (!leakIv || !archangel) {
      appendEvent(
        entry.id,
        'error',
        `No connected server exposes ${!leakIv ? LEAK_IV_TOOL : ARCHANGEL_TOOL} — check the connection panel and hit Test.`,
      );
      await updateEntry(entry.id, { status: 'error', error: 'missing_mcp_server' }, entry.source);
      return;
    }
    const { url: bridgeUrl, token: bridgeToken } = bridgeRef.current;
    appendEvent(entry.id, 'received', `Starting translation for #${entry.id} (${entry.name})`);

    // Constructed on demand for sources that don't pre-bake it (see the
    // QueueEntry.oldTheoremText comment) — one small server round trip,
    // done right before dispatch, never for the whole queue at once.
    let oldTheoremText = entry.oldTheoremText;
    if (!oldTheoremText) {
      try {
        const r = await fetch(`/api/queue/theorem-text?source=${encodeURIComponent(entry.source ?? 'competemath')}&id=${entry.id}`);
        const body = await r.json();
        if (!r.ok || typeof body.oldTheoremText !== 'string') {
          throw new Error(body.detail || body.error || `HTTP ${r.status}`);
        }
        oldTheoremText = body.oldTheoremText;
      } catch (e) {
        const msg = e instanceof Error ? e.message : String(e);
        appendEvent(entry.id, 'error', `Failed to construct theorem text: ${msg}`);
        await updateEntry(entry.id, { status: 'error', error: `theorem_text_failed: ${msg}` }, entry.source);
        return;
      }
    }

    await updateEntry(entry.id, { status: 'running' }, entry.source);

    const controller = new AbortController();
    abortControllers.current.set(entry.id, controller);

    try {
      const res = await fetch(`${bridgeUrl.replace(/\/$/, '')}/archangel-translate`, {
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-bridge-token': bridgeToken },
        signal: controller.signal,
        body: JSON.stringify({
          oldTheoremText,
          oldId: entry.id,
          oldExportNames: entry.oldExportNames,
          // Lets the bridge derive the namespace-qualified name and generate
          // the per-module Gate 2 export — without these, the numeric id and
          // bare name resolve to nothing and the entailment check is void.
          source: entry.source,
          sourcePath: entry.sourcePath,
          sourceLine: entry.sourceLine,
          archangelUrl: archangel.url,
          verifyUrl: leakIv.url,
          mcpServers: [leakIv, archangel, ...servers.filter((s) => s !== leakIv && s !== archangel && s.isActive)],
          timeoutMs: 20 * 60 * 1000,
        }),
      });
      if (!res.body) throw new Error('No response stream from bridge');
      const reader = res.body.getReader();
      const decoder = new TextDecoder();
      let buf = '';
      let finalResult: { verified: boolean; proof: string } | null = null;
      for (;;) {
        const { done, value } = await reader.read();
        if (done) break;
        buf += decoder.decode(value, { stream: true });
        const chunks = buf.split('\n\n');
        buf = chunks.pop() || '';
        for (const chunk of chunks) {
          const line = chunk.split('\n').find((l) => l.startsWith('data: '));
          if (!line) continue;
          const obj = JSON.parse(line.slice(6));
          if (obj.type === 'done') {
            finalResult = { verified: !!obj.verified, proof: obj.proof || '' };
          } else {
            handleStreamObject(entry.id, obj);
          }
        }
      }
      if (finalResult) {
        await updateEntry(
          entry.id,
          {
            status: finalResult.verified ? 'verified' : 'failed',
            proof: finalResult.verified ? finalResult.proof : undefined,
          },
          entry.source,
        );
        appendEvent(
          entry.id,
          finalResult.verified ? 'verified' : 'rejected',
          finalResult.verified ? 'Both gates passed' : 'Run ended without both gates passing',
          { verified: finalResult.verified, proof: finalResult.proof },
        );
      } else {
        await updateEntry(entry.id, { status: 'error', error: 'stream ended with no result' }, entry.source);
        appendEvent(entry.id, 'error', 'Stream ended without a result');
      }
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      await updateEntry(entry.id, { status: 'error', error: msg }, entry.source);
      appendEvent(entry.id, 'error', msg);
    } finally {
      abortControllers.current.delete(entry.id);
      activeRef.current = activeRef.current.filter((x) => x !== entry.id);
      setActiveIds([...activeRef.current]);
      pump();
    }
  };

  // Promotes queued ids into active slots up to maxParallel, fired whenever
  // the queue changes or a run finishes. This — not the Run button — is the
  // only place execution actually starts.
  const pump = () => {
    while (activeRef.current.length < maxParallel && queuedRef.current.length > 0) {
      const id = queuedRef.current.shift()!;
      const entry = queueEntriesRef.current.find((e) => e.id === id);
      if (!entry) continue;
      activeRef.current = [...activeRef.current, id];
      setActiveIds([...activeRef.current]);
      setQueuedIds([...queuedRef.current]);
      setSelectedLogId((cur) => cur ?? id);
      setEvents((e) => ({ ...e, [id]: [] }));
      executeEntry(entry);
    }
  };

  const enqueue = (entry: QueueEntry) => {
    if (activeRef.current.includes(entry.id) || queuedRef.current.includes(entry.id)) return;
    persistConnection();
    queuedRef.current = [...queuedRef.current, entry.id];
    setQueuedIds([...queuedRef.current]);
    updateEntry(entry.id, { status: 'queued' }, entry.source);
    pump();
  };

  // Scoped to the FILTERED set, not the whole source — at 13,164 rows,
  // "queue all pending" on the unfiltered list would instantly dispatch
  // thousands of runs. Filter down to what you actually mean first (a
  // category, a name search), then this only affects that subset.
  const enqueueAllPending = () => {
    for (const e of filteredQueue) {
      if (e.status === 'pending' || e.status === 'error' || e.status === 'failed') enqueue(e);
    }
  };

  const cancelQueued = (id: number) => {
    queuedRef.current = queuedRef.current.filter((x) => x !== id);
    setQueuedIds([...queuedRef.current]);
    updateEntry(id, { status: 'pending' });
  };

  const stopRun = (id: number) => abortControllers.current.get(id)?.abort();

  // ---- Recursion engine (bridge POST /archangel-recurse) ----
  // Entries that carry sourcePath/sourceLine are reconstructible from their
  // repo checkout, which is what the bridge's recursion loop needs (file by
  // file, mechanical attempt first, agent only on failure). Sources that
  // pre-bake oldTheoremText (plain CompeteMath) keep the per-entry loop.
  const recursable = (e: QueueEntry) => typeof e.sourcePath === 'string' && typeof e.sourceLine === 'number';

  // Status refresh that leaves paging/filters/reconciliation alone — the
  // bridge PATCHes /api/queue itself as it banks, the table only needs to
  // catch up with what is already on disk.
  const refreshQueue = async (src: string) => {
    try {
      const r = await fetch(`/api/queue?source=${encodeURIComponent(src)}`);
      if (!r.ok) return;
      const fresh: QueueEntry[] = await r.json();
      const byId = new Map(fresh.map((e) => [e.id, e]));
      setQueue((q) => {
        const next = q.map((e) => {
          const n = byId.get(e.id);
          return n && (n.status !== e.status || n.proof !== e.proof) ? { ...e, status: n.status, proof: n.proof } : e;
        });
        queueEntriesRef.current = next;
        return next;
      });
    } catch {
      /* transient — the next progress event retries */
    }
  };

  const startRecursion = async (scope: { type: 'all' } | { type: 'one'; id: number }) => {
    if (recurseAbort.current) return;
    const label = scope.type === 'one' ? `#${scope.id}` : 'all pending';
    setEvents((e) => ({ ...e, [RECURSE_LOG_ID]: [] }));
    setSelectedLogId(RECURSE_LOG_ID);
    const leakIv = resolveByTool(LEAK_IV_TOOL);
    const archangel = resolveByTool(ARCHANGEL_TOOL);
    if (!leakIv || !archangel) {
      appendEvent(
        RECURSE_LOG_ID,
        'error',
        `No connected server exposes ${!leakIv ? LEAK_IV_TOOL : ARCHANGEL_TOOL} — check the connection panel and hit Test.`,
      );
      return;
    }
    persistConnection();
    const controller = new AbortController();
    recurseAbort.current = controller;
    const src = source;
    setRecurseRun({ running: true, scope: label, processed: 0, total: 0, summary: {} });
    appendEvent(RECURSE_LOG_ID, 'received', `Recursive translation of ${label} (${src}) — mechanical attempt first, agent only on failure`);
    const { url: bridgeUrl, token: bridgeToken } = bridgeRef.current;
    try {
      const res = await fetch(`${bridgeUrl.replace(/\/$/, '')}/archangel-recurse`, {
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-bridge-token': bridgeToken },
        signal: controller.signal,
        body: JSON.stringify({
          source: src,
          scope,
          archangelUrl: archangel.url,
          verifyUrl: leakIv.url,
          mcpServers: [leakIv, archangel, ...servers.filter((s) => s !== leakIv && s !== archangel && s.isActive)],
          timeoutMs: 20 * 60 * 1000,
        }),
      });
      if (!res.ok) {
        const body = await res.json().catch(() => ({ error: `HTTP ${res.status}` }));
        throw new Error(`${body.error || res.status}${body.detail ? ` — ${body.detail}` : ''}`);
      }
      if (!res.body) throw new Error('No response stream from bridge');
      const reader = res.body.getReader();
      const decoder = new TextDecoder();
      let buf = '';
      for (;;) {
        const { done, value } = await reader.read();
        if (done) break;
        buf += decoder.decode(value, { stream: true });
        const chunks = buf.split('\n\n');
        buf = chunks.pop() || '';
        for (const chunk of chunks) {
          const line = chunk.split('\n').find((l) => l.startsWith('data: '));
          if (!line) continue;
          const obj = JSON.parse(line.slice(6));
          if (obj.type === 'progress' || obj.type === 'done') {
            const summary: Record<string, number> = obj.summary && typeof obj.summary === 'object' ? obj.summary : {};
            setRecurseRun({
              running: obj.type !== 'done',
              scope: label,
              processed: Number(obj.processed) || 0,
              total: Number(obj.total) || 0,
              summary,
            });
            await refreshQueue(src);
            if (obj.type === 'done') {
              const parts = Object.entries(summary).filter(([, v]) => v > 0).map(([k, v]) => `${k} ${v}`);
              appendEvent(RECURSE_LOG_ID, 'verified', `Done: ${obj.processed}/${obj.total} processed${parts.length ? ` — ${parts.join(' · ')}` : ''}`);
            }
          } else {
            handleStreamObject(RECURSE_LOG_ID, obj);
          }
        }
      }
    } catch (e) {
      const aborted = controller.signal.aborted;
      appendEvent(RECURSE_LOG_ID, aborted ? 'rejected' : 'error', aborted ? 'Stopped' : e instanceof Error ? e.message : String(e));
    } finally {
      recurseAbort.current = null;
      setRecurseRun((r) => (r ? { ...r, running: false } : r));
      refreshQueue(src);
    }
  };

  const stopRecursion = () => recurseAbort.current?.abort();

  const rowState = (id: number): 'active' | 'queued' | 'idle' =>
    activeIds.includes(id) ? 'active' : queuedIds.includes(id) ? 'queued' : 'idle';

  const leakIvReady = !!resolveByTool(LEAK_IV_TOOL);
  const archangelReady = !!resolveByTool(ARCHANGEL_TOOL);
  const sourceRecursable = queue.some(recursable);
  const pendingCount = queue.filter((e) => e.status === 'pending').length;

  // Progress fraction — processed (verified/failed/error, i.e. no longer
  // pending) out of the whole currently-loaded source. This IS the
  // "streamed progress" for corpus-level runs management: not a claim about
  // dependency-closure internals (that needs the recursion engine itself),
  // just an honest, real count of what's actually settled in this queue.
  const processedCount = queue.filter((e) => e.status === 'verified' || e.status === 'failed' || e.status === 'error').length;
  const verifiedCount = queue.filter((e) => e.status === 'verified').length;

  // Distinct categories present in the currently loaded source, for the
  // filter dropdown — empty/absent on sources (like CompeteMath) that don't
  // set `category` at all.
  const categories = Array.from(new Set(queue.map((e) => e.category).filter((c): c is string => !!c))).sort();

  const filteredQueue = queue.filter((e) => {
    if (nameFilter && !e.name.toLowerCase().includes(nameFilter.toLowerCase())) return false;
    if (categoryFilter !== 'all' && e.category !== categoryFilter) return false;
    if (statusFilter !== 'all' && e.status !== statusFilter) return false;
    return true;
  });
  const pageCount = Math.max(1, Math.ceil(filteredQueue.length / PAGE_SIZE));
  const currentPage = Math.min(page, pageCount - 1);
  const pageRows = filteredQueue.slice(currentPage * PAGE_SIZE, currentPage * PAGE_SIZE + PAGE_SIZE);

  return (
    <div style={{ display: 'flex', flexDirection: 'column', gap: 16 }}>
      <section style={{ border: '1px solid var(--border, #333)', borderRadius: 8, padding: 12 }}>
        <div style={{ fontSize: 13, fontWeight: 600, marginBottom: 8 }}>Source</div>
        <div style={{ display: 'flex', gap: 8, flexWrap: 'wrap', alignItems: 'center' }}>
          {queueSources.map((s) => (
            <Button
              key={s.key}
              size="sm"
              variant={source === s.key ? 'default' : 'outline'}
              onClick={() => setSource(s.key)}
            >
              {s.label}
            </Button>
          ))}
          <div style={{ fontSize: 12, opacity: 0.7, marginLeft: 8 }}>
            {processedCount} / {queue.length} processed ({verifiedCount} verified)
          </div>
          {recurseRun && (
            <div style={{ fontSize: 12, opacity: 0.85, marginLeft: 8 }}>
              🔁 {recurseRun.running ? 'Recursing' : 'Recursion finished'} ({recurseRun.scope}): {recurseRun.processed}/{recurseRun.total}
              {Object.values(recurseRun.summary).some((v) => v > 0) &&
                ` — ${Object.entries(recurseRun.summary).filter(([, v]) => v > 0).map(([k, v]) => `${k} ${v}`).join(' · ')}`}
            </div>
          )}
        </div>
      </section>

      <section style={{ border: '1px solid var(--border, #333)', borderRadius: 8, padding: 12 }}>
        <div style={{ fontSize: 13, fontWeight: 600, marginBottom: 8 }}>Connection</div>
        <div style={{ display: 'flex', gap: 12, flexWrap: 'wrap', alignItems: 'end' }}>
          <div>
            <Label htmlFor="bridge-url">Bridge URL</Label>
            <Input id="bridge-url" value={bridgeUrl} onChange={(e) => setBridgeUrl(e.target.value)} style={{ width: 220 }} />
          </div>
          <div>
            <Label htmlFor="max-parallel">Concurrent runs</Label>
            <Input
              id="max-parallel"
              type="number"
              min={1}
              max={8}
              value={maxParallel}
              onChange={(e) => setMaxParallel(Math.max(1, Math.min(8, Number(e.target.value) || 1)))}
              style={{ width: 90 }}
            />
          </div>
          <Button variant="outline" size="sm" onClick={persistConnection}>Save</Button>
        </div>
        <p style={{ fontSize: 12, opacity: 0.7, marginTop: 10, marginBottom: 4 }}>
          Run this in a terminal to start the bridge — the token is generated
          by this app and already baked in, exactly like the CompeteMath
          prover panel does it. Only re-copy it if you change the port above.
        </p>
        <div style={{ position: 'relative' }}>
          <pre style={{ overflowX: 'auto', whiteSpace: 'pre-wrap', wordBreak: 'break-all', borderRadius: 6, padding: 8, paddingRight: 64, fontSize: 12, background: 'var(--muted, #1a1a1a)' }}>
            {setupCommand || 'Loading…'}
          </pre>
          <Button
            variant="outline"
            size="sm"
            onClick={copyCommand}
            disabled={!setupCommand}
            style={{ position: 'absolute', top: 6, right: 6 }}
          >
            {copied ? 'Copied' : 'Copy'}
          </Button>
        </div>

        <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginTop: 14, marginBottom: 6 }}>
          <div style={{ fontSize: 13, fontWeight: 600 }}>
            MCP servers
            {' — '}
            <span style={{ fontWeight: 400, color: leakIvReady ? undefined : '#e05555' }}>
              Leak IV {leakIvReady ? '✓' : '✗'}
            </span>
            {'  '}
            <span style={{ fontWeight: 400, color: archangelReady ? undefined : '#e05555' }}>
              Archangel {archangelReady ? '✓' : '✗'}
            </span>
          </div>
          <div style={{ display: 'flex', gap: 8 }}>
            <Button size="sm" variant="outline" onClick={() => testAllServers()}>Test all</Button>
            <MCPServerDialog onServerAdded={refreshServers} />
          </div>
        </div>
        {activeIds.length > 0 && (
          <div style={{ fontSize: 12, color: '#e0a038', background: 'rgba(224,160,56,0.1)', border: '1px solid rgba(224,160,56,0.3)', borderRadius: 6, padding: '6px 8px', marginBottom: 8 }}>
            ⚠ {activeIds.length} translation{activeIds.length === 1 ? '' : 's'} currently running — each one holds its own live
            connection to every configured server. A Test click right now competes with those for the same machine
            resources and may be slow or time out; that is not this panel capping anything.
          </div>
        )}
        <div style={{ display: 'flex', flexDirection: 'column', gap: 6 }}>
          {servers.length === 0 && (
            <p style={{ fontSize: 12, opacity: 0.6 }}>No MCP servers configured yet — add Leak IV and Archangel above.</p>
          )}
          {servers.map((s) => {
            const st = serverStatus[s.id];
            return (
              <div
                key={s.id}
                style={{ display: 'flex', alignItems: 'center', justifyContent: 'space-between', gap: 8, border: '1px solid var(--border, #2a2a2a)', borderRadius: 6, padding: '6px 8px' }}
              >
                <div style={{ minWidth: 0 }}>
                  <div style={{ fontSize: 13, fontWeight: 500 }}>{s.name}</div>
                  <div style={{ fontSize: 11, opacity: 0.6, overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' }}>{s.url}</div>
                  {st?.tools && st.tools.length > 0 && (
                    <div style={{ display: 'flex', gap: 4, flexWrap: 'wrap', marginTop: 4 }}>
                      {st.tools.map((t) => (
                        <Badge key={t} variant="outline" style={{ fontSize: 10 }}>{t}</Badge>
                      ))}
                    </div>
                  )}
                  {st?.error && !st.checking && (
                    <div style={{ fontSize: 11, color: '#e05555', marginTop: 2 }}>{st.error}</div>
                  )}
                </div>
                <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexShrink: 0 }}>
                  <Badge variant={st?.connected ? 'default' : 'outline'}>
                    {st?.checking ? 'checking…' : st?.connected ? 'Connected' : 'Disconnected'}
                  </Badge>
                  <Button size="sm" variant="outline" onClick={() => testServer(s)} disabled={st?.checking}>
                    Test
                  </Button>
                </div>
              </div>
            );
          })}
        </div>
      </section>

      <section>
        <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', marginBottom: 8, flexWrap: 'wrap', gap: 8 }}>
          <div style={{ fontSize: 12, opacity: 0.7 }}>
            {activeIds.length} running / {queuedIds.length} queued (max {maxParallel} concurrent)
          </div>
          {sourceRecursable ? (
            recurseRun?.running ? (
              <Button size="sm" variant="outline" onClick={stopRecursion}>
                Stop recursion ({recurseRun.processed}/{recurseRun.total})
              </Button>
            ) : (
              <Button
                size="sm"
                variant="outline"
                onClick={() => startRecursion({ type: 'all' })}
                disabled={!leakIvReady || !archangelReady}
                title="Whole source in file order (filters don't apply) — mechanical attempt first, the agent only when that fails"
              >
                🔁 Recurse all pending ({pendingCount})
              </Button>
            )
          ) : (
            <Button size="sm" variant="outline" onClick={enqueueAllPending}>
              Queue all pending ({filteredQueue.length} filtered)
            </Button>
          )}
        </div>
        <div style={{ display: 'flex', gap: 8, flexWrap: 'wrap', marginBottom: 8 }}>
          <Input
            placeholder="Filter by name…"
            value={nameFilter}
            onChange={(e) => { setNameFilter(e.target.value); setPage(0); }}
            style={{ width: 220 }}
          />
          {categories.length > 0 && (
            <select
              value={categoryFilter}
              onChange={(e) => { setCategoryFilter(e.target.value); setPage(0); }}
              style={{ fontSize: 13, padding: '4px 6px', borderRadius: 6 }}
            >
              <option value="all">All categories</option>
              {categories.map((c) => (
                <option key={c} value={c}>{c}</option>
              ))}
            </select>
          )}
          <select
            value={statusFilter}
            onChange={(e) => { setStatusFilter(e.target.value); setPage(0); }}
            style={{ fontSize: 13, padding: '4px 6px', borderRadius: 6 }}
          >
            <option value="all">All statuses</option>
            <option value="pending">pending</option>
            <option value="queued">queued</option>
            <option value="running">running</option>
            <option value="verified">verified</option>
            <option value="failed">failed</option>
            <option value="error">error</option>
          </select>
        </div>
        <table style={{ width: '100%', borderCollapse: 'collapse', fontSize: 13 }}>
          <thead>
            <tr style={{ textAlign: 'left', borderBottom: '1px solid var(--border, #333)' }}>
              <th style={{ padding: 6 }}>ID</th>
              <th style={{ padding: 6 }}>Name</th>
              {categories.length > 0 && <th style={{ padding: 6 }}>Category</th>}
              <th style={{ padding: 6 }}>Status</th>
              <th style={{ padding: 6 }} />
            </tr>
          </thead>
          <tbody>
            {pageRows.map((e) => {
              const state = rowState(e.id);
              return (
                <tr
                  key={e.id}
                  style={{ borderBottom: '1px solid var(--border, #222)', cursor: state === 'active' ? 'pointer' : 'default' }}
                  onClick={() => state === 'active' && setSelectedLogId(e.id)}
                >
                  <td style={{ padding: 6 }}>{e.id}</td>
                  <td style={{ padding: 6 }}>
                    {e.name}
                    {!e.exportNamesConfirmed && (
                      <Badge variant="outline" style={{ marginLeft: 6 }}>unconfirmed export</Badge>
                    )}
                  </td>
                  {categories.length > 0 && (
                    <td style={{ padding: 6, fontSize: 11, opacity: 0.75 }}>{e.category}</td>
                  )}
                  <td style={{ padding: 6 }}>
                    <Badge variant="outline">{e.status}</Badge>
                  </td>
                  <td style={{ padding: 6 }}>
                    {state === 'active' ? (
                      <Button size="sm" variant="outline" onClick={() => stopRun(e.id)}>Stop</Button>
                    ) : state === 'queued' ? (
                      <Button size="sm" variant="outline" onClick={() => cancelQueued(e.id)}>Cancel</Button>
                    ) : recursable(e) ? (
                      <Button
                        size="sm"
                        onClick={() => startRecursion({ type: 'one', id: e.id })}
                        disabled={!leakIvReady || !archangelReady || !!recurseRun?.running}
                        title="Runs through the recursion engine (mechanical attempt first)"
                      >
                        Run
                      </Button>
                    ) : (
                      <Button size="sm" onClick={() => enqueue(e)} disabled={!leakIvReady || !archangelReady}>
                        Run
                      </Button>
                    )}
                  </td>
                </tr>
              );
            })}
          </tbody>
        </table>
        {pageCount > 1 && (
          <div style={{ display: 'flex', alignItems: 'center', gap: 8, marginTop: 8 }}>
            <Button size="sm" variant="outline" disabled={currentPage === 0} onClick={() => setPage(currentPage - 1)}>
              Prev
            </Button>
            <span style={{ fontSize: 12, opacity: 0.7 }}>
              Page {currentPage + 1} / {pageCount} ({filteredQueue.length} rows)
            </span>
            <Button size="sm" variant="outline" disabled={currentPage >= pageCount - 1} onClick={() => setPage(currentPage + 1)}>
              Next
            </Button>
          </div>
        )}
      </section>

      {(activeIds.length > 0 || recurseRun) && (
        <section>
          <div style={{ display: 'flex', gap: 8, marginBottom: 8, flexWrap: 'wrap' }}>
            {recurseRun && (
              <Button
                size="sm"
                variant={selectedLogId === RECURSE_LOG_ID ? 'default' : 'outline'}
                onClick={() => setSelectedLogId(RECURSE_LOG_ID)}
              >
                🔁 recursion
              </Button>
            )}
            {activeIds.map((id) => (
              <Button
                key={id}
                size="sm"
                variant={selectedLogId === id ? 'default' : 'outline'}
                onClick={() => setSelectedLogId(id)}
              >
                #{id}
              </Button>
            ))}
          </div>
          <ProverConsole
            events={selectedLogId != null ? events[selectedLogId] || [] : []}
            running={
              selectedLogId === RECURSE_LOG_ID
                ? !!recurseRun?.running
                : selectedLogId != null && activeIds.includes(selectedLogId)
            }
            title={selectedLogId === RECURSE_LOG_ID ? `Recursive run — ${source}` : `Translation run — #${selectedLogId}`}
            emptyHint="Waiting for the first event…"
          />
        </section>
      )}
    </div>
  );
}

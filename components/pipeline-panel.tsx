'use client';
// Full control of the local translation pipeline from the console: the three
// tree-based services + private bridge, the cache-pinned tree they run on, the
// promote loop, and the recursion run. Everything here talks to
// /api/pipeline (lib/pipeline.ts); the processes it starts outlive this tab.
import { useCallback, useEffect, useRef, useState } from 'react';
import { Button } from '@/components/ui/button';

type Proc = { pid: number | null; alive: boolean; startedAt: string | null };
type Service = Proc & { name: string; port: number; http: number; up: boolean; log: string[] };
type Run = { state: 'running' | 'done' | 'stopped' | 'idle'; processed: number; total: number; summary: Record<string, number>; inScope: number | null; startedAt: string | null; log: string[] };
type Tree = { dir: string; exists: boolean; head: string; built: boolean; refresh: Proc; refreshLog: string[] };
type Config = {
  treeDir: string; workTree: string; corpusRoot: string;
  leakIv: { dir: string; python: string; port: number };
  gate2: { dir: string; python: string; port: number };
  leakI: { dir: string; python: string; port: number; loogleDir: string };
  bridge: { port: number; token: string };
  promote: { library: string; intervalS: number; quiescentS: number; viaPrs: boolean };
  run: { source: string; timeoutMin: number };
};
type Status = {
  config: Config; services: Service[]; promote: Proc & { log: string[] }; run: Run;
  queue: { counts: Record<string, number>; files: { sourcePath: string; pending: number }[] };
  tree: Tree; now: string;
};

const LABEL: Record<string, string> = { 'leak-iv': 'Leak IV — verifier', gate2: 'Gate 2 — Archangel', 'leak-i': 'Leak I — loogle', bridge: 'Private bridge' };
const SUMMARY_ORDER = ['mechanical', 'cached-mechanical', 'agentic', 'unresolved', 'infra-blocked', 'failed', 'untranslatable'];

function since(iso: string | null) {
  if (!iso) return '';
  const s = Math.max(0, (Date.now() - new Date(iso).getTime()) / 1000);
  if (s < 90) return `${Math.round(s)}s`;
  if (s < 5400) return `${Math.round(s / 60)}m`;
  return `${(s / 3600).toFixed(1)}h`;
}

function Dot({ color }: { color: 'green' | 'amber' | 'red' | 'grey' }) {
  const c = { green: '#22c55e', amber: '#f59e0b', red: '#ef4444', grey: '#9ca3af' }[color];
  return <span style={{ display: 'inline-block', width: 9, height: 9, borderRadius: 9, background: c, marginRight: 6, verticalAlign: 'middle' }} />;
}

function Card({ title, right, children }: { title: string; right?: React.ReactNode; children: React.ReactNode }) {
  return (
    <section style={{ border: '1px solid rgba(127,127,127,.35)', borderRadius: 8, padding: '10px 12px', marginBottom: 12 }}>
      <div style={{ display: 'flex', alignItems: 'center', justifyContent: 'space-between', marginBottom: 8, gap: 8, flexWrap: 'wrap' }}>
        <h3 style={{ fontSize: 14, fontWeight: 600, margin: 0 }}>{title}</h3>
        <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap' }}>{right}</div>
      </div>
      {children}
    </section>
  );
}

function LogBox({ lines, height = 140 }: { lines: string[]; height?: number }) {
  const ref = useRef<HTMLPreElement>(null);
  const stick = useRef(true);
  useEffect(() => {
    const el = ref.current;
    if (el && stick.current) el.scrollTop = el.scrollHeight;
  }, [lines]);
  return (
    <pre
      ref={ref}
      onScroll={(e) => { const el = e.currentTarget; stick.current = el.scrollHeight - el.scrollTop - el.clientHeight < 24; }}
      style={{ fontSize: 11, lineHeight: 1.35, maxHeight: height, overflow: 'auto', margin: 0, padding: 8, borderRadius: 6, background: 'rgba(127,127,127,.12)', whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}
    >
      {lines.length ? lines.join('\n') : '(no output yet)'}
    </pre>
  );
}

export function PipelinePanel() {
  const [st, setSt] = useState<Status | null>(null);
  const [err, setErr] = useState<string | null>(null);
  const [busy, setBusy] = useState<string | null>(null);
  const [openLogs, setOpenLogs] = useState<Record<string, boolean>>({});
  const [scopeMode, setScopeMode] = useState<'all' | 'file' | 'one'>('all');
  const [scopeFile, setScopeFile] = useState('');
  const [scopeId, setScopeId] = useState('');
  const [runLines, setRunLines] = useState(80);
  const [treeCheck, setTreeCheck] = useState<string | null>(null);
  const [cfgOpen, setCfgOpen] = useState(false);
  const [cfgDraft, setCfgDraft] = useState<Config | null>(null);

  const refresh = useCallback(async () => {
    try {
      const r = await fetch(`/api/pipeline?lines=${runLines}`, { cache: 'no-store' });
      if (!r.ok) throw new Error(`${r.status} ${(await r.json().catch(() => ({}))).error || ''}`);
      setSt(await r.json());
      setErr(null);
    } catch (e) {
      setErr(`status: ${(e as Error).message}`);
    }
  }, [runLines]);

  useEffect(() => {
    refresh();
    const t = setInterval(() => { if (!document.hidden) refresh(); }, 3000);
    return () => clearInterval(t);
  }, [refresh]);

  const act = async (action: string, extra: Record<string, unknown> = {}) => {
    setBusy(action + (extra.name ? `:${extra.name}` : ''));
    try {
      const r = await fetch('/api/pipeline', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ action, ...extra }) });
      const body = await r.json().catch(() => ({}));
      if (!r.ok) throw new Error(body.detail || body.error || r.status);
      setErr(null);
      return body;
    } catch (e) {
      setErr(`${action}: ${(e as Error).message}`);
    } finally {
      setBusy(null);
      refresh();
    }
  };

  if (!st) return <div style={{ fontSize: 13, opacity: 0.7 }}>{err ? `Pipeline: ${err}` : 'Loading pipeline status…'}</div>;

  const { services, promote, run, queue, tree, config } = st;
  const allUp = services.every((s) => s.up);
  const runScope = scopeMode === 'all' ? { type: 'all' } : scopeMode === 'file' ? { type: 'file', sourcePath: scopeFile } : { type: 'one', id: Number(scopeId) };
  const scopeValid = scopeMode === 'all' || (scopeMode === 'file' && !!scopeFile) || (scopeMode === 'one' && Number.isFinite(Number(scopeId)) && scopeId !== '');
  const pct = run.total ? Math.round((100 * run.processed) / run.total) : 0;
  const pending = queue.counts.pending ?? 0;

  return (
    <div style={{ marginBottom: 28 }}>
      <div style={{ display: 'flex', alignItems: 'baseline', justifyContent: 'space-between', gap: 8, flexWrap: 'wrap', marginBottom: 8 }}>
        <h2 style={{ fontSize: 16, fontWeight: 600, margin: 0 }}>
          <Dot color={allUp ? 'green' : services.some((s) => s.up) ? 'amber' : 'red'} />
          Pipeline
          <span style={{ fontSize: 12, fontWeight: 400, opacity: 0.7, marginLeft: 8 }}>
            {run.state === 'running' ? `run in progress ${run.processed}/${run.total}` : promote.alive ? 'promote loop running' : 'idle'} · queue: {pending} pending, {queue.counts.verified ?? 0} verified
          </span>
        </h2>
        {err && <span style={{ fontSize: 12, color: '#ef4444' }}>{err}</span>}
      </div>

      <Card
        title="Local services (on the cache-pinned tree)"
        right={
          <>
            <Button size="sm" variant="outline" disabled={!!busy || allUp} onClick={() => act('start-all-services')}>Start all</Button>
            <Button size="sm" variant="outline" disabled={!!busy || !services.some((s) => s.alive)} onClick={() => act('stop-all-services')}>Stop all</Button>
          </>
        }
      >
        <table style={{ width: '100%', fontSize: 13, borderCollapse: 'collapse' }}>
          <tbody>
            {services.map((s) => {
              const color = s.up ? 'green' : s.alive ? 'amber' : 'red';
              const text = s.up ? 'up' : s.alive ? 'starting (port not answering yet)' : 'down';
              return (
                <FragmentRow key={s.name}>
                  <tr style={{ borderTop: '1px solid rgba(127,127,127,.2)' }}>
                    <td style={{ padding: '6px 4px', width: 210 }}><Dot color={color} />{LABEL[s.name] || s.name}</td>
                    <td style={{ padding: '6px 4px', opacity: 0.8 }}>:{s.port} · {text}{s.alive && s.pid ? ` · pid ${s.pid} · ${since(s.startedAt)}` : ''}</td>
                    <td style={{ padding: '6px 4px', textAlign: 'right', whiteSpace: 'nowrap' }}>
                      {s.alive ? (
                        <Button size="sm" variant="outline" disabled={!!busy} onClick={() => act('stop-service', { name: s.name })}>Stop</Button>
                      ) : (
                        <Button size="sm" disabled={!!busy} onClick={() => act('start-service', { name: s.name })}>Start</Button>
                      )}
                      <Button size="sm" variant="ghost" onClick={() => setOpenLogs((o) => ({ ...o, [s.name]: !o[s.name] }))}>{openLogs[s.name] ? 'Hide log' : 'Log'}</Button>
                    </td>
                  </tr>
                  {openLogs[s.name] && (
                    <tr><td colSpan={3} style={{ padding: '0 4px 8px' }}><LogBox lines={s.log} /></td></tr>
                  )}
                </FragmentRow>
              );
            })}
          </tbody>
        </table>
        <p style={{ fontSize: 11, opacity: 0.6, margin: '8px 0 0' }}>
          Leak IV, Leak I and Gate 2 import <code>Tengoku.All</code> from <code>{tree.dir}</code>, a clone pinned to the newest published cache. Nothing there is ever compiled.
        </p>
      </Card>

      <Card
        title="Tree cache"
        right={
          <>
            <Button size="sm" variant="outline" disabled={!!busy || tree.refresh.alive} onClick={async () => { setTreeCheck('checking…'); const r = await act('check-tree'); setTreeCheck(r ? `${r.status} ${r.detail || ''}` : null); }}>Check for newer cache</Button>
            {tree.refresh.alive ? (
              <Button size="sm" variant="outline" disabled={!!busy} onClick={() => act('stop-tree-refresh')}>Stop refresh</Button>
            ) : (
              <Button size="sm" variant="outline" disabled={!!busy || run.state === 'running'} onClick={() => act('refresh-tree')}>Refresh cache</Button>
            )}
          </>
        }
      >
        <div style={{ fontSize: 13 }}>
          <Dot color={tree.built ? 'green' : tree.exists ? 'amber' : 'red'} />
          {tree.exists ? <>pinned at <code>{tree.head || '?'}</code>{tree.built ? ', build present' : ', build MISSING'}</> : <>clone not found at <code>{tree.dir}</code></>}
          {treeCheck && <span style={{ marginLeft: 10, opacity: 0.8 }}>· newest published: {treeCheck}</span>}
          {tree.refresh.alive && <span style={{ marginLeft: 10 }}>· refreshing (pid {tree.refresh.pid}, {since(tree.refresh.startedAt)}) — downloads the newest cache, then restart the services</span>}
        </div>
        {(tree.refresh.alive || tree.refreshLog.length > 0) && <div style={{ marginTop: 6 }}><LogBox lines={tree.refreshLog} height={90} /></div>}
      </Card>

      <Card
        title="Promote loop (working tree)"
        right={
          promote.alive ? (
            <Button size="sm" variant="outline" disabled={!!busy} onClick={() => act('stop-promote')}>Stop</Button>
          ) : (
            <Button size="sm" disabled={!!busy} onClick={() => act('start-promote')}>Start</Button>
          )
        }
      >
        <div style={{ fontSize: 13, marginBottom: 6 }}>
          <Dot color={promote.alive ? 'green' : 'grey'} />
          {promote.alive ? `running · pid ${promote.pid} · ${since(promote.startedAt)}` : 'stopped'} · every {config.promote.intervalS}s, files quiet for {config.promote.quiescentS}s · {config.promote.viaPrs ? <>opens promotion PRs from <code>{config.workTree}</code> (main untouched)</> : <>commits and pushes <code>{config.workTree}</code></>}
        </div>
        <LogBox lines={promote.log} height={90} />
      </Card>

      <Card
        title="Recursion run"
        right={
          run.state === 'running' ? (
            <Button size="sm" variant="destructive" disabled={!!busy} onClick={() => act('stop-run')}>Stop run ({run.processed}/{run.total})</Button>
          ) : (
            <Button size="sm" disabled={!!busy || !scopeValid || !allUp} title={!allUp ? 'start the services first' : ''} onClick={() => act('start-run', { scope: runScope })}>Start run</Button>
          )
        }
      >
        <div style={{ display: 'flex', gap: 14, flexWrap: 'wrap', alignItems: 'center', fontSize: 13, marginBottom: 8 }}>
          <label><input type="radio" checked={scopeMode === 'all'} onChange={() => setScopeMode('all')} /> all pending ({pending})</label>
          <label>
            <input type="radio" checked={scopeMode === 'file'} onChange={() => setScopeMode('file')} /> one file{' '}
            <select value={scopeFile} onChange={(e) => { setScopeFile(e.target.value); setScopeMode('file'); }} style={{ fontSize: 12, maxWidth: 380 }}>
              <option value="">choose…</option>
              {queue.files.slice(0, 300).map((f) => <option key={f.sourcePath} value={f.sourcePath}>{f.sourcePath} ({f.pending})</option>)}
            </select>
          </label>
          <label>
            <input type="radio" checked={scopeMode === 'one'} onChange={() => setScopeMode('one')} /> one entry #
            <input value={scopeId} onChange={(e) => { setScopeId(e.target.value); setScopeMode('one'); }} placeholder="id" style={{ width: 80, fontSize: 12, marginLeft: 4 }} />
          </label>
          <span style={{ opacity: 0.7 }}>· {config.run.timeoutMin} min per entry · bridge :{config.bridge.port}</span>
        </div>
        <div style={{ height: 8, borderRadius: 4, background: 'rgba(127,127,127,.2)', overflow: 'hidden', marginBottom: 6 }}>
          <div style={{ width: `${pct}%`, height: '100%', background: run.state === 'running' ? '#22c55e' : '#9ca3af', transition: 'width .5s' }} />
        </div>
        <div style={{ fontSize: 12, display: 'flex', gap: 10, flexWrap: 'wrap', marginBottom: 6 }}>
          <span><Dot color={run.state === 'running' ? 'green' : run.state === 'done' ? 'grey' : run.state === 'stopped' ? 'amber' : 'grey'} />{run.state}{run.startedAt && run.state === 'running' ? ` · ${since(run.startedAt)}` : ''}</span>
          <span>{run.processed}/{run.total}{run.inScope != null ? ` (${run.inScope} in scope)` : ''}</span>
          {SUMMARY_ORDER.filter((k) => run.summary[k]).map((k) => <span key={k} style={{ padding: '1px 6px', borderRadius: 10, background: 'rgba(127,127,127,.18)' }}>{k} {run.summary[k]}</span>)}
          <span style={{ marginLeft: 'auto' }}>
            log lines{' '}
            <select value={runLines} onChange={(e) => setRunLines(Number(e.target.value))} style={{ fontSize: 12 }}>
              {[80, 300, 1000].map((n) => <option key={n} value={n}>{n}</option>)}
            </select>
          </span>
        </div>
        <LogBox lines={run.log} height={260} />
      </Card>

      <div style={{ fontSize: 12 }}>
        <button onClick={() => { setCfgOpen((o) => !o); setCfgDraft(config); }} style={{ background: 'none', border: 'none', padding: 0, cursor: 'pointer', textDecoration: 'underline', opacity: 0.8 }}>
          {cfgOpen ? 'Hide configuration' : 'Configuration (paths, ports, token)'}
        </button>
        {cfgOpen && cfgDraft && (
          <div style={{ marginTop: 8, display: 'grid', gridTemplateColumns: 'max-content 1fr', gap: '4px 10px', alignItems: 'center', maxWidth: 820 }}>
            {([
              ['Cache-pinned tree (services)', cfgDraft.treeDir, (v: string) => ({ ...cfgDraft, treeDir: v })],
              ['Working tree (promote loop)', cfgDraft.workTree, (v: string) => ({ ...cfgDraft, workTree: v })],
              ['Corpus checkout', cfgDraft.corpusRoot, (v: string) => ({ ...cfgDraft, corpusRoot: v })],
              ['Leak IV dir', cfgDraft.leakIv.dir, (v: string) => ({ ...cfgDraft, leakIv: { ...cfgDraft.leakIv, dir: v } })],
              ['Leak IV port', String(cfgDraft.leakIv.port), (v: string) => ({ ...cfgDraft, leakIv: { ...cfgDraft.leakIv, port: Number(v) } })],
              ['Gate 2 dir', cfgDraft.gate2.dir, (v: string) => ({ ...cfgDraft, gate2: { ...cfgDraft.gate2, dir: v } })],
              ['Gate 2 python', cfgDraft.gate2.python, (v: string) => ({ ...cfgDraft, gate2: { ...cfgDraft.gate2, python: v } })],
              ['Gate 2 port', String(cfgDraft.gate2.port), (v: string) => ({ ...cfgDraft, gate2: { ...cfgDraft.gate2, port: Number(v) } })],
              ['Leak I dir', cfgDraft.leakI.dir, (v: string) => ({ ...cfgDraft, leakI: { ...cfgDraft.leakI, dir: v } })],
              ['loogle dir', cfgDraft.leakI.loogleDir, (v: string) => ({ ...cfgDraft, leakI: { ...cfgDraft.leakI, loogleDir: v } })],
              ['Leak I port', String(cfgDraft.leakI.port), (v: string) => ({ ...cfgDraft, leakI: { ...cfgDraft.leakI, port: Number(v) } })],
              ['Bridge port', String(cfgDraft.bridge.port), (v: string) => ({ ...cfgDraft, bridge: { ...cfgDraft.bridge, port: Number(v) } })],
              ['Bridge token', cfgDraft.bridge.token, (v: string) => ({ ...cfgDraft, bridge: { ...cfgDraft.bridge, token: v } })],
              ['Promote every (s)', String(cfgDraft.promote.intervalS), (v: string) => ({ ...cfgDraft, promote: { ...cfgDraft.promote, intervalS: Number(v) } })],
              ['Promote quiescent (s)', String(cfgDraft.promote.quiescentS), (v: string) => ({ ...cfgDraft, promote: { ...cfgDraft.promote, quiescentS: Number(v) } })],
              ['Via pull requests (1 = never push main)', cfgDraft.promote.viaPrs ? '1' : '0', (v: string) => ({ ...cfgDraft, promote: { ...cfgDraft.promote, viaPrs: v.trim() === '1' } })],
              ['Run timeout per entry (min)', String(cfgDraft.run.timeoutMin), (v: string) => ({ ...cfgDraft, run: { ...cfgDraft.run, timeoutMin: Number(v) } })],
            ] as [string, string, (v: string) => Config][]).map(([label, value, set]) => (
              <FragmentRow key={label}>
                <label style={{ opacity: 0.8 }}>{label}</label>
                <input value={value} onChange={(e) => setCfgDraft(set(e.target.value))} style={{ fontSize: 12, fontFamily: 'monospace', padding: '2px 6px', border: '1px solid rgba(127,127,127,.4)', borderRadius: 4, background: 'transparent' }} />
              </FragmentRow>
            ))}
            <span />
            <div style={{ display: 'flex', gap: 6 }}>
              <Button size="sm" disabled={!!busy} onClick={() => act('save-config', { config: cfgDraft })}>Save</Button>
              <Button size="sm" variant="ghost" onClick={() => setCfgDraft(config)}>Reset</Button>
              <span style={{ opacity: 0.6, alignSelf: 'center' }}>saved to data/pipeline-config.json · applies to processes started after saving</span>
            </div>
          </div>
        )}
      </div>
    </div>
  );
}

// React.Fragment with a key, kept readable in the tables above.
function FragmentRow({ children }: { children: React.ReactNode }) {
  return <>{children}</>;
}

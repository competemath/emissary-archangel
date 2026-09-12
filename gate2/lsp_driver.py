"""Resident Lean elaborator for Gate 2, driven over `lake serve`'s LSP.

Ported from Leak IV's verifier. One long-lived `lake serve` keeps the tree's
imports resident; every Gate 2 check is a didOpen/didChange of ONE sandbox
file followed by waitForDiagnostics, so a call costs the elaboration of the
file's commands — not a fresh process re-importing Mathlib (~100 s). Lean's
LSP is incremental by command: the import header is reused across calls, and
`#tengoku_import_parse` of the same export is reused across consecutive
calls for the same module.

`elaborate(text)` returns the file's diagnostics as one text — information
messages (the `GATE2_PASS`/`GATE2_FAIL` markers `logInfo` produces) and
errors, in file order — the same shape `lake env lean` printed, so the
daemon's verdict regexes are unchanged.
"""
import asyncio
import json
import logging
import os
import time
from pathlib import Path

logger = logging.getLogger("gate2.lsp")

_CRASH_MARKERS = ("stack overflow", "aborting", "panic", "segmentation fault", "libc++abi")
_WORKER_DEAD_CODES = (-32902, -32900)


class WorkerCrashed(Exception):
    pass


class ResidentElaborator:
    def __init__(self, project_dir: str, sandbox_name: str = "gate2_sandbox.lean"):
        self.project_dir = project_dir
        self.process: asyncio.subprocess.Process | None = None
        self.lock = asyncio.Lock()
        self._crash_event = asyncio.Event()
        self.version = 1
        self.request_id = 1000
        self.count = 0
        self.sandbox_path = Path(project_dir).resolve() / sandbox_name
        self.uri = self.sandbox_path.as_uri()
        self._is_file_open = False
        with open(self.sandbox_path, "a"):
            pass

    # ---- lifecycle ---------------------------------------------------------
    async def boot(self):
        if self.process and self.process.returncode is None:
            return
        logger.info("starting `lake serve` in %s", self.project_dir)
        self.process = await asyncio.create_subprocess_exec(
            "lake", "serve", cwd=self.project_dir,
            stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
        asyncio.create_task(self._log_stderr())
        await self._send("initialize", {
            "processId": os.getpid(),
            "rootUri": Path(self.project_dir).resolve().as_uri(),
            "capabilities": {"textDocument": {"synchronization": {"change": 1}}},
        }, msg_id=0)
        while True:
            msg = await asyncio.wait_for(self._read(), timeout=60.0)
            if msg.get("id") == 0:
                break
        await self._send("initialized", {})
        self._is_file_open = False
        logger.info("resident elaborator online")

    async def restart(self):
        if self.process and self.process.returncode is None:
            self.process.kill()
            await self.process.wait()
        self.process = None
        self._is_file_open = False
        await self.boot()

    async def _log_stderr(self):
        if not self.process or not self.process.stderr:
            return
        while True:
            try:
                line = await self.process.stderr.readline()
                if not line:
                    break
                text = line.decode("utf-8", "replace").rstrip()
                logger.info("[lake serve] %s", text)
                if any(k in text.lower() for k in _CRASH_MARKERS):
                    self._crash_event.set()
            except Exception:
                break

    # ---- JSON-RPC over stdio -----------------------------------------------
    async def _send(self, method: str, params: dict, msg_id: int | None = None):
        if not self.process or not self.process.stdin:
            raise BrokenPipeError("LSP stdin is dead")
        msg = {"jsonrpc": "2.0", "method": method, "params": params}
        if msg_id is not None:
            msg["id"] = msg_id
        body = json.dumps(msg).encode("utf-8")
        self.process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("utf-8") + body)
        await self.process.stdin.drain()

    async def _read(self) -> dict:
        if not self.process or not self.process.stdout:
            raise EOFError("LSP stdout is dead")
        content_length = 0
        while True:
            line_bytes = await self.process.stdout.readline()
            if not line_bytes:
                raise EOFError("LSP EOF (subprocess exited)")
            line = line_bytes.decode("utf-8", "replace").strip()
            if not line and content_length > 0:
                break
            if line.lower().startswith("content-length:"):
                content_length = int(line.split(":")[1].strip())
        body = await self.process.stdout.readexactly(content_length)
        return json.loads(body.decode("utf-8"))

    async def _await_message(self, timeout: float) -> dict:
        read_fut = asyncio.ensure_future(self._read())
        crash_fut = asyncio.ensure_future(self._crash_event.wait())
        try:
            done, _ = await asyncio.wait({read_fut, crash_fut}, timeout=timeout, return_when=asyncio.FIRST_COMPLETED)
            if read_fut in done:
                return read_fut.result()
            if crash_fut in done:
                raise WorkerCrashed("file worker aborted")
            raise TimeoutError(f"elaboration exceeded {timeout:.0f}s")
        finally:
            for f in (read_fut, crash_fut):
                if not f.done():
                    f.cancel()
                try:
                    await f
                except BaseException:
                    pass

    async def _recover_worker(self):
        self._crash_event.clear()
        if not self.process or self.process.returncode is not None:
            self.process = None
            self._is_file_open = False
            return
        try:
            if self._is_file_open:
                await self._send("textDocument/didClose", {"textDocument": {"uri": self.uri}})
        except Exception:
            self.process = None
        self._is_file_open = False

    # ---- the one operation ---------------------------------------------------
    async def elaborate(self, text: str, timeout: float) -> tuple[int, str]:
        """Elaborate `text` as the sandbox file; return (rc, diagnostics text).
        rc 0 = elaborated (verdict is in the text), -1 = infrastructure failure."""
        async with self.lock:
            self.count += 1
            n = self.count
            t0 = time.time()
            if not self.process or self.process.returncode is not None:
                await self.boot()
            self.version += 1
            ver = self.version
            self._crash_event.clear()
            try:
                if not self._is_file_open:
                    await self._send("textDocument/didOpen", {"textDocument": {
                        "uri": self.uri, "languageId": "lean", "version": ver, "text": text}})
                    self._is_file_open = True
                else:
                    await self._send("textDocument/didChange", {
                        "textDocument": {"uri": self.uri, "version": ver},
                        "contentChanges": [{"text": text}]})
                self.request_id += 1
                wf_id = self.request_id
                await self._send("textDocument/waitForDiagnostics", {"uri": self.uri, "version": ver}, msg_id=wf_id)
                merged: list | None = None
                while True:
                    if time.time() - t0 > timeout:
                        raise TimeoutError(f"elaboration exceeded {timeout:.0f}s")
                    msg = await self._await_message(timeout)
                    if msg.get("id") == wf_id and "method" not in msg:
                        if "error" in msg:
                            err = msg["error"] or {}
                            if err.get("code") in _WORKER_DEAD_CODES:
                                raise WorkerCrashed(f"waitForDiagnostics: {err}")
                            raise RuntimeError(f"waitForDiagnostics error: {msg['error']}")
                        break
                    method = msg.get("method")
                    if method == "textDocument/publishDiagnostics":
                        p = msg.get("params", {})
                        if p.get("uri") == self.uri:
                            diags = p.get("diagnostics", [])
                            if merged is None or not bool(p.get("isIncremental", False)):
                                merged = list(diags)
                            else:
                                merged = merged + list(diags)
                diags = sorted(merged or [], key=lambda d: (d.get("range", {}).get("start", {}).get("line", 0), d.get("range", {}).get("start", {}).get("character", 0)))
                # An error inside the import block means `lake setup-file` could
                # not provide the imports (tree not built / build failed). The
                # worker then keeps that failed header for every later edit, so
                # close the file: the next call reopens it and setup runs again.
                n_header = 0
                for l in text.splitlines():
                    if not l.strip():
                        break
                    n_header += 1
                hdr_err = [d for d in diags if d.get("severity") == 1 and d.get("range", {}).get("start", {}).get("line", 0) < n_header]
                if hdr_err:
                    msg = " ".join(str(hdr_err[0].get("message", "")).split())
                    logger.error("[#%d] import failure: %s", n, msg[-600:])
                    await self._recover_worker()
                    return -1, f"GATE2_FAIL reason=call_failed detail=imports_failed {msg[-800:]}\n"
                lines = []
                for d in diags:
                    sev = {1: "error", 2: "warning", 3: "info", 4: "hint"}.get(d.get("severity", 3), "info")
                    ln = d.get("range", {}).get("start", {}).get("line", 0) + 1
                    lines.append(f"{self.sandbox_path}:{ln}:0: {sev}: {d.get('message', '')}")
                logger.info("[#%d] elaborated in %dms (%d diagnostics)", n, int((time.time() - t0) * 1000), len(diags))
                return 0, "\n".join(lines) + "\n"
            except WorkerCrashed as e:
                logger.error("[#%d] worker crash: %s", n, e)
                await self._recover_worker()
                return -1, f"GATE2_FAIL reason=call_failed detail=worker_crashed {e}\n"
            except TimeoutError as e:
                logger.error("[#%d] %s", n, e)
                await self._recover_worker()
                return -1, "GATE2_FAIL reason=timeout\n"
            except Exception as e:
                logger.error("[#%d] %s", n, e)
                if isinstance(e, (EOFError, BrokenPipeError)):
                    self.process = None
                    self._is_file_open = False
                return -1, f"GATE2_FAIL reason=call_failed detail={e}\n"

#!/usr/bin/env python3
"""Runs ONE agent process as the unprivileged agent user, and makes sure nothing of it outlives its launcher.

Started by scripts/agent-run.py as `sudo -n -u agent env -i PATH=... /usr/bin/python3 /opt/emissary-jail/agent-supervise.py`,
installed root-owned by `agent-jail.py setup`. Everything arrives on stdin, so no secret is ever on a command line:

    line 1      a JSON header {"run_dir", "argv", "env", "wall", "tar_len"}
    next bytes  tar_len bytes of tar: the run's staged files (the MCP config, the settings file and the hook scripts)
    then        left open. When the launcher goes away for any reason, SIGKILL included, stdin reaches end of file and the
                whole process group is killed; a launcher that is killed cannot leave a running, paying agent behind.

It creates the run directory (home/, work/, tmp/ in it, mode 0700), extracts the staged files into work/ (regular files with a
plain name only, nothing else), runs argv with exactly the given environment in a new session with work/ as its directory,
forwards SIGINT and SIGTERM to the group, enforces a wall-clock limit, and removes the run directory at the end. Its exit status
is the process's (128 + signal when it was killed).

It judges nothing about the argv: agent-run.py has already checked it against the tool policy. The directory must be named
<workspace>/run.<16 hex digits> and must not exist yet, so a header cannot make it write somewhere else.
"""
from __future__ import annotations

import argparse
import io
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import threading

MAX_FILE = 512 * 1024
MAX_TOTAL = 4 * 1024 * 1024
MAX_HEADER = 4 * 1024 * 1024
NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,100}$")
RUN_RE = re.compile(r"^run\.[0-9a-f]{16}$")


class Refused(Exception):
    pass


def read_exact(stream, n: int) -> bytes:
    chunks = []
    left = n
    while left > 0:
        chunk = stream.read(min(left, 1 << 20))
        if not chunk:
            raise Refused("the launcher closed the pipe before the staged files arrived")
        chunks.append(chunk)
        left -= len(chunk)
    return b"".join(chunks)


def check_header(header, workspace: str) -> None:
    if not isinstance(header, dict):
        raise Refused("header is not an object")
    run_dir = header.get("run_dir")
    if not isinstance(run_dir, str) or os.path.dirname(run_dir) != workspace or not RUN_RE.match(os.path.basename(run_dir)):
        raise Refused("run_dir must be %s/run.<16 hex digits>" % workspace)
    argv = header.get("argv")
    if not isinstance(argv, list) or not argv or not all(isinstance(a, str) and "\x00" not in a for a in argv):
        raise Refused("argv must be a non-empty list of strings")
    env = header.get("env")
    if not isinstance(env, dict) or not all(isinstance(k, str) and isinstance(v, str) and "\x00" not in k + v and "=" not in k for k, v in env.items()):
        raise Refused("env must map names to strings")
    wall = header.get("wall")
    if isinstance(wall, bool) or not isinstance(wall, int) or not 1 <= wall <= 7 * 24 * 3600:
        raise Refused("wall must be a number of seconds")
    tar_len = header.get("tar_len")
    if isinstance(tar_len, bool) or not isinstance(tar_len, int) or not 0 <= tar_len <= MAX_TOTAL * 2:
        raise Refused("tar_len is out of range")


def extract_staged(blob: bytes, dest: str) -> int:
    """Write the staged files into ``dest``. Regular files with a plain single-component name only; sizes capped."""
    total = 0
    count = 0
    if not blob:
        return 0
    with tarfile.open(fileobj=io.BytesIO(blob), mode="r:") as tar:
        for member in tar.getmembers():
            if not member.isreg():
                raise Refused("staged entry %r is not a regular file" % member.name)
            if not NAME_RE.match(member.name):
                raise Refused("staged entry name %r is not a plain file name" % member.name)
            if member.size > MAX_FILE:
                raise Refused("staged file %r is too large" % member.name)
            total += member.size
            if total > MAX_TOTAL:
                raise Refused("staged files are too large")
            src = tar.extractfile(member)
            if src is None:
                raise Refused("staged entry %r cannot be read" % member.name)
            fd = os.open(os.path.join(dest, member.name), os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            with os.fdopen(fd, "wb") as out:
                out.write(src.read())
            count += 1
    return count


def kill_group(pgid: int, sig: int) -> None:
    try:
        os.killpg(pgid, sig)
    except (ProcessLookupError, PermissionError):
        pass


def supervise(header, blob: bytes, stdin, workspace: str) -> int:
    run_dir = header["run_dir"]
    os.mkdir(run_dir, 0o700)
    try:
        for sub in ("home", "work", "tmp"):
            os.mkdir(os.path.join(run_dir, sub), 0o700)
        extract_staged(blob, os.path.join(run_dir, "work"))
        env = dict(header["env"])
        proc = subprocess.Popen(
            header["argv"], cwd=os.path.join(run_dir, "work"), env=env, stdin=subprocess.DEVNULL, start_new_session=True,
        )
        pgid = proc.pid
        done = threading.Event()

        def watch_launcher() -> None:
            try:
                while stdin.read(65536):
                    pass
            except (OSError, ValueError):
                pass
            if not done.is_set():
                kill_group(pgid, signal.SIGKILL)

        threading.Thread(target=watch_launcher, daemon=True).start()
        for sig in (signal.SIGINT, signal.SIGTERM):
            signal.signal(sig, lambda s, _f: kill_group(pgid, s))

        def too_long() -> None:
            sys.stderr.write("agent-supervise: wall-clock limit (%ds) reached\n" % header["wall"])
            kill_group(pgid, signal.SIGTERM)
            threading.Timer(15, kill_group, (pgid, signal.SIGKILL)).start()

        timer = threading.Timer(header["wall"], too_long)
        timer.daemon = True
        timer.start()
        try:
            rc = proc.wait()
        finally:
            done.set()
            timer.cancel()
            kill_group(pgid, signal.SIGKILL)  # whatever the process left behind (shell children, hook processes)
        return 128 - rc if rc < 0 else rc
    finally:
        shutil.rmtree(run_dir, ignore_errors=True)


def main(argv=None, stdin=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--workspace", help="the agent's workspace (default: the account's home directory)")
    ns = ap.parse_args(argv)
    stdin = stdin if stdin is not None else sys.stdin.buffer
    try:
        if ns.workspace:
            workspace = os.path.abspath(ns.workspace)
        else:
            import pwd

            workspace = pwd.getpwuid(os.getuid()).pw_dir
        line = stdin.readline(MAX_HEADER)
        try:
            header = json.loads(line)
        except ValueError:
            raise Refused("header is not JSON")
        check_header(header, workspace)
        blob = read_exact(stdin, header["tar_len"])
        return supervise(header, blob, stdin, workspace)
    except Refused as exc:
        sys.stderr.write("agent-supervise: refused: %s\n" % exc)
        return 97
    except OSError as exc:
        sys.stderr.write("agent-supervise: %s\n" % exc)
        return 98


if __name__ == "__main__":
    status = main()
    sys.stdout.flush()
    sys.stderr.flush()
    # A thread may still be blocked reading stdin; leaving through the normal shutdown path can abort the interpreter on it.
    os._exit(status)

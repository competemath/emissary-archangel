#!/usr/bin/env python3
"""The jail wrapper: the bridge's CLAUDE_BIN when the translation workflow has proven its jail.

The bridge (public/local-claude-bridge.mjs) starts this file where it would start `claude`, with the same argv. This file
never trusts that argv and never lets the CLI run as the bridge's user:

1. It refuses to start unless the escape battery passed on this runner: /opt/emissary-jail/ready.json must exist, belong to
   root and not be writable by anyone else (scripts/agent-jail.py writes it only after `warden selftest` passed as the agent
   user). That file is also the only configuration: nothing the environment says can widen it.
2. It stages the bridge's run directory (the MCP config, the settings file, the hook scripts) for the agent user, because the
   agent cannot read the bridge's temp files, and rewrites the paths in argv to the staged copies. The MCP config may name only
   loopback ports the jail allows, and only plain `sse` servers: a `command` entry would run a program as the agent.
3. It judges the rewritten argv with warden.toolpolicy.check_claude_argv against the translator policy (MCP tools only; Bash
   only if the jail was proven; a permission bypass only next to a restricted --tools set; --strict-mcp-config always).
4. It clamps --max-turns and --max-budget-usd to the ceilings in ready.json (adding them when missing).
5. It rebuilds the environment with warden.envscrub.build_env: no variable of the bridge reaches the agent except its model
   credential and CLAUDE_CODE_MAX_OUTPUT_TOKENS. The agent's HTTPS_PROXY is the allowlist proxy; its HOME is a throwaway.
6. It runs `sudo -n -u agent env -i ... agent-supervise.py` and hands it everything on stdin, so no secret is ever on a command
   line. The supervisor kills the agent if this process dies.

`--version` alone is answered directly, without the agent user.

Exit status: the agent process's, or 2 when this wrapper refused to start it (the reason goes to stderr, never a secret).
"""
from __future__ import annotations

import io
import json
import os
import re
import secrets
import signal
import subprocess
import sys
import tarfile
import tempfile
from urllib.parse import urlparse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import agent_policy  # noqa: E402
from warden import envscrub  # noqa: E402
from warden.jail import run_as_argv  # noqa: E402
from warden.toolpolicy import parse_claude_argv, check_claude_argv  # noqa: E402

READY_PATH = "/opt/emissary-jail/ready.json"
SUPERVISOR = "/opt/emissary-jail/agent-supervise.py"
PYTHON = "/usr/bin/python3"
SECRETS = ("CLAUDE_CODE_OAUTH_TOKEN", "ANTHROPIC_API_KEY")
ALLOW_ENV = ("LANG", "LC_ALL", "TZ", "TERM") + SECRETS + ("CLAUDE_CODE_MAX_OUTPUT_TOKENS",)
MAX_STAGED_FILE = 256 * 1024
MAX_STAGED_TOTAL = 1024 * 1024
_USER_RE = re.compile(r"^[a-z_][a-z0-9_-]{0,30}$")
_FILE_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,100}$")


class Refused(Exception):
    """The launch is refused; the message is safe to print."""


# ---------------------------------------------------------------------------------------------------------------------------
# the ready file
# ---------------------------------------------------------------------------------------------------------------------------


def load_ready(path: str = READY_PATH, trusted_uid: int = 0) -> dict:
    """Read and validate the ready file. It must be owned by ``trusted_uid`` (root), and neither it nor its directory may be
    writable by group or others; anything else, or any missing field, refuses."""
    try:
        st = os.lstat(path)
        dst = os.stat(os.path.dirname(path))
    except OSError:
        raise Refused("the jail is not ready: %s is missing (the escape battery has not passed on this runner)" % path)
    import stat as _stat

    if not _stat.S_ISREG(st.st_mode) or st.st_uid != trusted_uid or st.st_mode & 0o022:
        raise Refused("%s is not a root-owned regular file that only root can write" % path)
    if dst.st_uid != trusted_uid or dst.st_mode & 0o022:
        raise Refused("the directory of %s is writable by someone other than root" % path)
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
    except (OSError, ValueError):
        raise Refused("%s is not readable JSON" % path)
    problems = []
    if not isinstance(data, dict) or data.get("version") != 1 or data.get("ok") is not True:
        problems.append("version/ok")
    else:
        if not isinstance(data.get("agent_user"), str) or not _USER_RE.match(data["agent_user"]) or data["agent_user"] == "root":
            problems.append("agent_user")
        for key in ("workspace", "real_claude", "path"):
            if not isinstance(data.get(key), str) or not data[key].startswith("/"):
                problems.append(key)
        if not isinstance(data.get("ports"), list) or not all(isinstance(p, int) and not isinstance(p, bool) and 0 < p < 65536 for p in data["ports"]):
            problems.append("ports")
        if not isinstance(data.get("proxy"), str) or urlparse(data["proxy"]).hostname not in ("127.0.0.1", "localhost"):
            problems.append("proxy")
        for key in ("max_usd",):
            if isinstance(data.get(key), bool) or not isinstance(data.get(key), (int, float)) or data[key] <= 0:
                problems.append(key)
        for key in ("max_turns", "wall_seconds"):
            if isinstance(data.get(key), bool) or not isinstance(data.get(key), int) or data[key] <= 0:
                problems.append(key)
        if not isinstance(data.get("bash"), bool):
            problems.append("bash")
    if problems:
        raise Refused("%s is malformed (%s)" % (path, ", ".join(problems)))
    return data


# ---------------------------------------------------------------------------------------------------------------------------
# staging
# ---------------------------------------------------------------------------------------------------------------------------


def check_mcp_config(text: str, ports) -> None:
    """Only plain SSE servers on allowed loopback ports. A stdio server (``command``) would run a program as the agent."""
    try:
        cfg = json.loads(text)
    except ValueError:
        raise Refused("the MCP config is not JSON")
    servers = cfg.get("mcpServers") if isinstance(cfg, dict) else None
    if not isinstance(servers, dict):
        raise Refused("the MCP config has no mcpServers object")
    for name, spec in servers.items():
        if not isinstance(spec, dict) or set(spec) - {"type", "url"} or spec.get("type") != "sse" or not isinstance(spec.get("url"), str):
            raise Refused("MCP server %r is not a plain {type: sse, url} entry" % name)
        u = urlparse(spec["url"])
        if u.scheme != "http" or u.hostname not in ("127.0.0.1", "localhost") or u.port not in ports or u.username or u.password:
            raise Refused("MCP server %r is not on an allowed loopback port (%s)" % (name, ",".join(str(p) for p in ports)))


def stage_directory(src: str, dst: str):
    """Tar the flat directory ``src`` for the agent, rewriting ``src`` to ``dst`` inside .json and .mjs files. Returns
    (tar bytes, {file name: text}). Refuses anything that is not a small regular file with a plain name."""
    real_src = os.path.realpath(src)
    tmp = os.path.realpath(tempfile.gettempdir())
    if not os.path.isdir(real_src) or os.path.commonpath([real_src, tmp]) != tmp or real_src == tmp:
        raise Refused("the run directory %s is not a directory of its own under the temp directory" % src)
    buf = io.BytesIO()
    texts = {}
    total = 0
    with tarfile.open(fileobj=buf, mode="w") as tar:
        for name in sorted(os.listdir(real_src)):
            path = os.path.join(real_src, name)
            if not _FILE_RE.match(name) or os.path.islink(path) or not os.path.isfile(path):
                raise Refused("%s in the run directory is not a plain regular file" % name)
            size = os.path.getsize(path)
            total += size
            if size > MAX_STAGED_FILE or total > MAX_STAGED_TOTAL:
                raise Refused("the run directory holds more than a run needs")
            with open(path, "rb") as fh:
                data = fh.read()
            if name.endswith((".json", ".mjs")):
                data = data.decode("utf-8").replace(src, dst).replace(real_src, dst).encode("utf-8")
                texts[name] = data.decode("utf-8")
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o600
            info.mtime = 0
            tar.addfile(info, io.BytesIO(data))
    return buf.getvalue(), texts


def rewrite_argv(argv, mapping):
    """Replace a token equal to a mapped path, or ``--flag=<path>``, by its staged path."""
    out = []
    for tok in argv:
        if tok in mapping:
            out.append(mapping[tok])
        elif tok.startswith("--") and "=" in tok and tok.split("=", 1)[1] in mapping:
            flag, val = tok.split("=", 1)
            out.append(flag + "=" + mapping[val])
        else:
            out.append(tok)
    return out


def clamp_caps(argv, max_turns: int, max_usd: float):
    """Remove any --max-turns / --max-budget-usd and append them clamped to the ceilings (the ceiling when absent or invalid)."""
    turns, usd = max_turns, max_usd
    out = []
    i = 0
    while i < len(argv):
        tok = argv[i]
        name, eq, inline = tok.partition("=") if tok.startswith("--") else (tok, "", "")
        if name in ("--max-turns", "--max-budget-usd"):
            if eq:
                value = inline
            elif i + 1 < len(argv):
                value = argv[i + 1]
                i += 1
            else:
                value = ""
            try:
                num = float(value)
            except ValueError:
                num = -1.0
            if name == "--max-turns" and 0 < num < turns:
                turns = int(num)
            if name == "--max-budget-usd" and 0 < num < usd:
                usd = num
        else:
            out.append(tok)
        i += 1
    return out + ["--max-turns", str(turns), "--max-budget-usd", repr(float(usd))]


# ---------------------------------------------------------------------------------------------------------------------------
# the plan: everything decided before anything runs
# ---------------------------------------------------------------------------------------------------------------------------


def plan_launch(argv, ready: dict, environ, run_name: str = None):
    """Judge ``argv`` and build the launch. Returns a dict: ``sudo`` (argv), ``header`` (what the supervisor reads first),
    ``tar`` (bytes), ``env_names`` (names only, for the log). Raises Refused. Runs no process."""
    run_name = run_name or "run." + secrets.token_hex(8)
    run_dir = ready["workspace"].rstrip("/") + "/" + run_name
    work = run_dir + "/work"
    parsed = parse_claude_argv(argv)

    mapping = {}
    tar_bytes = b""
    src = None
    if len(parsed.mcp_config) > 1:
        raise Refused("more than one --mcp-config")
    if parsed.mcp_config:
        cfg = parsed.mcp_config[0]
        if cfg.lstrip().startswith("{"):
            raise Refused("an inline --mcp-config cannot be staged; the bridge writes a file")
        src = os.path.dirname(os.path.abspath(cfg))
        mapping[cfg] = work + "/" + os.path.basename(cfg)
    for s in parsed.settings:
        if s.lstrip().startswith("{"):
            raise Refused("inline --settings is not auditable; the bridge writes a file")
        if src is None:
            src = os.path.dirname(os.path.abspath(s))
        if os.path.dirname(os.path.abspath(s)) != src:
            raise Refused("--settings must sit in the same run directory as --mcp-config")
        mapping[s] = work + "/" + os.path.basename(s)
    if src is not None:
        tar_bytes, texts = stage_directory(src, work)
        for cfg in parsed.mcp_config:
            check_mcp_config(texts.get(os.path.basename(cfg), ""), ready["ports"])
    rewritten = clamp_caps(rewrite_argv(list(argv), mapping), ready["max_turns"], ready["max_usd"])

    if not any(t in ("-p", "--print") for t in rewritten):
        raise Refused("the agent runs non-interactively (-p) only")
    violations = check_claude_argv(rewritten, agent_policy.argv_policy(bash=bool(ready["bash"])), run_dir=work)
    if violations:
        raise Refused("argv refused by the tool policy: " + "; ".join(str(v) for v in violations))

    proxy = ready["proxy"]
    extra = {
        "PATH": ready["path"],
        "TMPDIR": run_dir + "/tmp",
        "HTTPS_PROXY": proxy, "https_proxy": proxy, "HTTP_PROXY": proxy, "http_proxy": proxy,
        "NO_PROXY": "127.0.0.1,localhost,::1", "no_proxy": "127.0.0.1,localhost,::1",
        "CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC": "1", "DISABLE_AUTOUPDATER": "1", "DISABLE_TELEMETRY": "1",
        "DISABLE_ERROR_REPORTING": "1", "CLAUDE_CODE_DISABLE_AUTO_MEMORY": "1",
    }
    source = dict(environ)
    if not re.fullmatch(r"[0-9]{1,7}", source.get("CLAUDE_CODE_MAX_OUTPUT_TOKENS", "0")):
        source.pop("CLAUDE_CODE_MAX_OUTPUT_TOKENS", None)
    try:
        env = envscrub.build_env(ALLOW_ENV, extra, source, secret_ok=SECRETS + ("CLAUDE_CODE_MAX_OUTPUT_TOKENS",), home=run_dir + "/home")
    except envscrub.EnvRefused as exc:
        raise Refused("environment refused: %s" % exc)

    header = {"run_dir": run_dir, "argv": [ready["real_claude"]] + rewritten, "env": env, "wall": int(ready["wall_seconds"]), "tar_len": len(tar_bytes)}
    sudo = run_as_argv(ready["agent_user"], [PYTHON, SUPERVISOR], env={"PATH": "/usr/bin:/bin"})
    return {"sudo": sudo, "header": header, "tar": tar_bytes, "env_names": sorted(env), "argv": rewritten}


# ---------------------------------------------------------------------------------------------------------------------------
# run
# ---------------------------------------------------------------------------------------------------------------------------


def run_version(ready_path: str = READY_PATH) -> int:
    """``--version`` needs no agent user; run it with an empty environment."""
    try:
        real = load_ready(ready_path)["real_claude"]
    except Refused:
        real = os.environ.get("EMISSARY_REAL_CLAUDE", "")
    if not real:
        print("agent-run: no claude to ask", file=sys.stderr)
        return 2
    return subprocess.call([real, "--version"], env={"PATH": "/usr/bin:/bin"}, stdin=subprocess.DEVNULL)


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv == ["--version"]:
        return run_version()
    try:
        ready = load_ready()
        plan = plan_launch(argv, ready, os.environ)
    except Refused as exc:
        print("agent-run: refused: %s" % exc, file=sys.stderr)
        return 2
    print("agent-run: starting as %s with %d environment variables (%s)" % (ready["agent_user"], len(plan["env_names"]), ",".join(plan["env_names"])), file=sys.stderr)
    proc = subprocess.Popen(plan["sudo"], stdin=subprocess.PIPE, cwd="/")  # the agent user cannot search the bridge's directory
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda s, _f: proc.send_signal(s))
    try:
        proc.stdin.write((json.dumps(plan["header"]) + "\n").encode("utf-8"))
        proc.stdin.write(plan["tar"])
        proc.stdin.flush()
    except (BrokenPipeError, OSError):
        pass  # the supervisor refused or died; its exit status says which
    rc = proc.wait()
    try:
        proc.stdin.close()
    except (BrokenPipeError, OSError):
        pass
    return rc


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Build the agent's jail on a CI runner, prove it, and take it down. Used by translate.yml and agent-selftest.yml.

    sudo python3 scripts/agent-jail.py setup [--print]     the agent user, per-user egress rules, the egress proxy
    python3 scripts/agent-jail.py ready                    run the escape battery as the agent; on a pass, write the marker
    sudo python3 scripts/agent-jail.py teardown            kill the agent's processes, remove rules and marker

What the jail is (docs/agent-security.md has the long version). An unprivileged account `agent` that has no sudo, no
privileged group and no way into the runner's home (warden.jail.agent_user_script, which also remounts /proc with hidepid=2).
The kernel refuses everything it sends except TCP to a few loopback ports: the Lean services, the bridge's governor, and an
allowlist CONNECT proxy that runs as a third account and tunnels to the model API host and nothing else (warden.jail.
uid_egress_rules; warden egress-proxy). User namespaces are switched off, so the agent cannot build a sandbox of its own.
`ready` then runs `warden selftest` AS the agent (through scripts/agent-selftest-inner.py) against a host canary file, a
runner-owned decoy process standing in for the bridge, a listener outside the jail and the allowed ports; only when every probe
is denied does it write /opt/emissary-jail/ready.json, root-owned, which scripts/agent-run.py insists on and reads its
configuration from.

Every command that changes the machine is built by a pure function (setup_script, selftest_argv, ready_marker) and run by a
thin function, so tests read the commands without running them. Python 3.9 compatible, standard library and scripts/warden only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shlex
import socket
import subprocess
import sys
import tempfile
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import agent_policy  # noqa: E402
from warden import jail  # noqa: E402

JAIL_DIR = "/opt/emissary-jail"
MARKER = JAIL_DIR + "/ready.json"
# No /usr/local/bin: the hosted runner image leaves it writable by everyone, and a PATH the agent can write is a PATH it can plant a program in.
AGENT_PATH = "/opt/agent-tools/bin:/usr/bin:/bin"
DEFAULT_PORTS = (4125, 7871, 7872)  # the bridge's governor, Leak IV, Archangel (translate.yml)
PROXY_PORT = 8899
PROXY_USER = "egress"
MODEL_API = ("api.anthropic.com:443",)
INSTALLED_FILES = ("agent-supervise.py", "agent-selftest-inner.py")
# Probes the battery cannot answer for a uid jail, with the reason; scripts/agent-selftest-inner.py leaves them out and says so.
SKIPPED_PROBES = {
    "userns_differs_from_host": "the agent shares the host's user namespace by design (uid isolation, no namespace jail); the "
    "nested_userns_denied probe, with user namespaces switched off, is what covers this vector",
}


# ---------------------------------------------------------------------------------------------------------------------------
# pure builders
# ---------------------------------------------------------------------------------------------------------------------------


def setup_script(
    *, agent_user: str = "agent", workspace: str = "/home/agent", runner_user: str = "runner", runner_home: str = "/home/runner",
    ports=DEFAULT_PORTS, proxy_port: int = PROXY_PORT, proxy_user: str = PROXY_USER, allow=MODEL_API, scripts_dir: str = HERE,
    traverse=(), harden_path: str = "",
) -> str:
    """Bash (run as root) that creates the jail. Fails closed: any unmet guarantee exits non-zero.

    ``traverse`` names accounts (the Lean services' user) that must still walk through the runner's home, which the agent user
    script closes to everyone else: each gets an ACL entry that allows search (x) on the home directory and nothing more.

    ``harden_path`` is the runner's PATH. The hosted image leaves /opt, /usr/local/bin and the tool cache writable by everyone, so
    the agent could replace a program the runner starts later, with the runner's tokens (Tau Ceti finding F-21). The script
    takes write permission for group and others off the system directories, off every directory of that PATH outside the runner's
    home, off the executables in them, and off the directories above their real locations. It also closes the system D-Bus socket,
    which any local account can otherwise connect to."""
    all_ports = sorted(set(int(p) for p in ports) | {int(proxy_port)})
    q = shlex.quote
    body = jail.agent_user_script(agent_user, workspace, runner_user=runner_user, runner_home=runner_home)
    lines = [l for l in body.rstrip("\n").split("\n") if not l.startswith("#!")]
    for user in traverse:
        if not jail._USER_RE.match(user) or user in (agent_user, "root"):
            raise jail.JailSpecError(["traverse user %r is not a plain account other than the agent and root" % (user,)])
        lines += [
            "# %s keeps its way through the runner's home (search permission only); the agent has none" % user,
            "command -v setfacl >/dev/null 2>&1 || { apt-get update -qq && apt-get install -y -qq acl; }",
            "setfacl -m u:%s:x %s" % (q(user), q(runner_home)),
        ]
    lines += [
        "# the image leaves some directories and programs writable by everyone; the agent must not be able to replace what the runner runs later",
        'harden() { local p; p="$(realpath -m -- "$1" 2>/dev/null)" || return 0; while [ -n "$p" ] && [ "$p" != / ]; do chmod go-w -- "$p" 2>/dev/null || true; p="$(dirname -- "$p")"; done; }',
        "for d in /opt /usr/local /usr/local/bin /usr/local/sbin /usr/local/lib /srv /home; do if [ -d \"$d\" ]; then harden \"$d\"; fi; done",
    ]
    if harden_path:
        lines += [
            "RUNNER_PATH=%s" % q(harden_path),
            'IFS=: read -r -a runner_path_dirs <<< "$RUNNER_PATH"',
            'for d in "${runner_path_dirs[@]}"; do',
            '  [ -d "$d" ] || continue',
            '  case "$d" in "$RUNNER_HOME"|"$RUNNER_HOME"/*) continue ;; esac',
            '  harden "$d"',
            '  while IFS= read -r f; do harden "$f"; chmod go-w -- "$f" 2>/dev/null || true; done < <(find -L "$d" -maxdepth 1 -type f -perm /go+w 2>/dev/null)',
            "done",
        ]
    lines += [
        "# the system bus socket is connectable by every local account; the agent has no business there",
        'if [ -S /run/dbus/system_bus_socket ]; then chmod o-rwx /run/dbus/system_bus_socket; fi',
        "# user namespaces off: the agent cannot build a sandbox of its own (the nested_userns_denied probe checks it)",
        "sysctl -w user.max_user_namespaces=0 >/dev/null",
        "# the kernel refuses everything the agent sends except TCP to these loopback ports",
    ]
    lines += jail.uid_egress_rules("$AGENT_UID", all_ports)
    lines += [
        "# code and configuration the agent and the proxy run from: root-owned, in a place the runner's closed home does not hide",
        "install -d -m 0755 -o root -g root %s" % q(JAIL_DIR),
        "rm -rf %s/py" % q(JAIL_DIR),
        "install -d -m 0755 -o root -g root %s/py" % q(JAIL_DIR),
        "cp -R %s %s/py/warden" % (q(os.path.join(scripts_dir, "warden")), q(JAIL_DIR)),
        "find %s/py -name __pycache__ -prune -exec rm -rf {} +" % q(JAIL_DIR),
    ]
    for name in INSTALLED_FILES:
        lines.append("install -m 0644 -o root -g root %s %s/%s" % (q(os.path.join(scripts_dir, name)), q(JAIL_DIR), name))
    lines += [
        "chown -R root:root %s && chmod -R go-w %s" % (q(JAIL_DIR), q(JAIL_DIR)),
        "# the allowlist proxy: its own account, loopback only, the model API host and nothing else",
        'id -u %s >/dev/null 2>&1 || useradd --system --no-create-home --shell /usr/sbin/nologin %s' % (q(proxy_user), q(proxy_user)),
        "install -d -m 0755 -o %s -g %s /var/log/emissary" % (q(proxy_user), q(proxy_user)),
        "cd /",
        "setsid nohup sudo -n -u %s env -i PATH=/usr/bin:/bin LANG=C.UTF-8 PYTHONPATH=%s/py /usr/bin/python3 -m warden egress-proxy "
        "--listen 127.0.0.1:%d %s --log /var/log/emissary/egress.jsonl >/var/log/emissary/egress.err 2>&1 </dev/null &"
        % (q(proxy_user), q(JAIL_DIR), proxy_port, " ".join("--allow " + q(a) for a in allow)),
        'for _ in $(seq 1 40); do (exec 3<>/dev/tcp/127.0.0.1/%d) 2>/dev/null && break; sleep 0.5; done' % proxy_port,
        '(exec 3<>/dev/tcp/127.0.0.1/%d) 2>/dev/null || fail "the egress proxy did not start: $(cat /var/log/emissary/egress.err)"' % proxy_port,
        'echo "warden-jail: egress proxy on 127.0.0.1:%d allows %s"' % (proxy_port, ", ".join(allow)),
    ]
    return "#!/usr/bin/env bash\n" + "\n".join(lines) + "\n"


def teardown_script(*, agent_user: str = "agent", proxy_user: str = PROXY_USER) -> str:
    q = shlex.quote
    lines = [
        "#!/usr/bin/env bash",
        "set -u",
        "rm -f %s" % q(MARKER),
        "pkill -KILL -u %s 2>/dev/null || true" % q(agent_user),
        "pkill -TERM -u %s 2>/dev/null || true" % q(proxy_user),
        'AGENT_UID="$(id -u %s 2>/dev/null || true)"' % q(agent_user),
        'if [ -n "$AGENT_UID" ]; then',
    ]
    lines += ["  " + l for l in jail.uid_egress_teardown("$AGENT_UID")]
    lines += ["fi", "exit 0"]
    return "\n".join(lines) + "\n"


def agent_env(workspace: str, proxy_port: int = PROXY_PORT, path: str = AGENT_PATH):
    """The environment the battery runs under: the one a real run's supervisor starts from (it adds the credential)."""
    proxy = "http://127.0.0.1:%d" % proxy_port
    return {
        "PATH": path, "HOME": workspace, "LANG": "C.UTF-8", "HTTPS_PROXY": proxy, "HTTP_PROXY": proxy,
        "NO_PROXY": "127.0.0.1,localhost,::1",
    }


def selftest_argv(
    *, agent_user: str, agent_uid: int, workspace: str, runner_home: str, canaries, decoy_pid: int, egress_canary: str,
    ports, report: str, github_files=(), path: str = AGENT_PATH, proxy_port: int = PROXY_PORT,
):
    """The command (sudo, as the agent, empty environment but the agent's own) that runs the escape battery."""
    inner = [
        "/usr/bin/python3", JAIL_DIR + "/agent-selftest-inner.py",
        "--require-linux", "--expect-uid", str(agent_uid), "--workspace", workspace, "--home", runner_home,
        "--bridge-pid", str(decoy_pid), "--egress-canary", egress_canary, "--json", report,
    ]
    for c in canaries:
        inner += ["--canary-file", c]
    for p in sorted(set(int(x) for x in ports) | {proxy_port}):
        inner += ["--allow-port", str(p)]
    for g in github_files:
        inner += ["--github-file", g]
    for b in ("node", "claude", "sh", "env"):
        inner += ["--binary", b]
    return jail.run_as_argv(agent_user, inner, env=agent_env(workspace, proxy_port, path))


def ready_marker(
    *, agent_user: str, agent_uid: int, workspace: str, real_claude: str, path: str, ports, proxy_port: int, report_sha256: str,
    max_usd: float, max_turns: int, wall_seconds: int, created: str,
):
    """What agent-run.py reads. Written only after the battery passed."""
    return {
        "version": 1, "ok": True, "created": created, "agent_user": agent_user, "agent_uid": agent_uid, "workspace": workspace,
        "real_claude": real_claude, "path": path, "ports": sorted(set(int(p) for p in ports) | {proxy_port}),
        "proxy": "http://127.0.0.1:%d" % proxy_port, "bash": True, "max_usd": max_usd, "max_turns": max_turns,
        "wall_seconds": wall_seconds, "selftest_report_sha256": report_sha256, "skipped_probes": sorted(SKIPPED_PROBES),
    }


# ---------------------------------------------------------------------------------------------------------------------------
# things that touch the machine
# ---------------------------------------------------------------------------------------------------------------------------


def run(argv, *, input_text=None, timeout=300, check=False):
    # cwd is /, not the workspace: the agent user cannot enter the runner's home, and a process that starts in a directory it
    # cannot search fails in surprising places.
    return subprocess.run(argv, input=input_text, universal_newlines=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, check=check, cwd="/")


def default_runner_home() -> str:
    """The home of the user who started the job (sudo hides it in $HOME), for the workflows that do not pass --runner-home."""
    user = os.environ.get("SUDO_USER")
    return "/home/" + user if user else os.path.expanduser("~")


def primary_ip() -> str:
    """This machine's address on its default route, which a listener on 0.0.0.0 is reachable at from inside it. A UDP connect
    sends nothing; it only asks the kernel which address it would use."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("192.0.2.1", 9))
        return s.getsockname()[0]
    finally:
        s.close()


class Canaries:
    """What the battery is told must be unreachable: files only this user can read, a decoy process holding secret-looking
    environment, and a TCP listener outside the jail. Used as a context manager so that nothing is left behind."""

    def __init__(self) -> None:
        self.files = []
        self.decoy = None
        self.listener = None
        self.port = 0
        self._stop = threading.Event()

    def __enter__(self):
        for base in (os.environ.get("RUNNER_TEMP") or tempfile.gettempdir(), "/tmp"):
            fd, path = tempfile.mkstemp(prefix="emissary-canary-", dir=base)
            os.write(fd, b"host canary: the agent must not be able to read this\n")
            os.close(fd)
            os.chmod(path, 0o600)
            self.files.append(path)
        env = {"PATH": "/usr/bin:/bin", "BRIDGE_TOKEN": "decoy-" + os.urandom(8).hex(), "CLAUDE_CODE_OAUTH_TOKEN": "decoy-" + os.urandom(8).hex()}
        self.decoy = subprocess.Popen(["sleep", "900"], env=env, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        self.listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener.bind(("0.0.0.0", 0))
        self.listener.listen(8)
        self.port = self.listener.getsockname()[1]
        threading.Thread(target=self._accept, daemon=True).start()
        return self

    def _accept(self) -> None:
        self.listener.settimeout(0.5)
        while not self._stop.is_set():
            try:
                conn, _ = self.listener.accept()
                conn.close()
            except (socket.timeout, OSError):
                continue

    def __exit__(self, *exc) -> None:
        self._stop.set()
        if self.decoy is not None:
            self.decoy.kill()
            self.decoy.wait()
        if self.listener is not None:
            self.listener.close()
        for f in self.files:
            try:
                os.unlink(f)
            except OSError:
                pass


def cmd_setup(ns) -> int:
    script = setup_script(
        agent_user=ns.agent_user, workspace=ns.workspace, runner_user=ns.runner_user, runner_home=ns.runner_home,
        ports=[int(p) for p in ns.ports.split(",") if p], proxy_port=ns.proxy_port, allow=ns.allow or MODEL_API, traverse=ns.traverse or (),
        harden_path=ns.harden_path or "",
    )
    if ns.print:
        sys.stdout.write(script)
        return 0
    if os.geteuid() != 0:
        print("agent-jail: setup must run as root (sudo)", file=sys.stderr)
        return 2
    return subprocess.call(["bash", "-euo", "pipefail", "-c", script])


def cmd_teardown(ns) -> int:
    return subprocess.call(["bash", "-c", teardown_script(agent_user=ns.agent_user)])


def cmd_ready(ns, runner=run) -> int:
    """Run the battery as the agent; write the marker only if it passed. Exit 0 jail ready, 1 not."""
    runner(["sudo", "-n", "rm", "-f", MARKER])
    uid = int(runner(["id", "-u", ns.agent_user]).stdout.strip())
    real_claude = ns.real_claude
    if not os.path.isfile(real_claude) or not os.access(real_claude, os.X_OK):
        print("agent-jail: %s is not an executable; install the agent first" % real_claude, file=sys.stderr)
        return 1
    ports = [int(p) for p in ns.ports.split(",") if p]
    report = ns.workspace.rstrip("/") + "/selftest.json"
    github = [os.environ[v] for v in ("GITHUB_ENV", "GITHUB_PATH", "GITHUB_OUTPUT", "GITHUB_STATE", "GITHUB_STEP_SUMMARY") if os.environ.get(v)]
    with Canaries() as canary:
        argv = selftest_argv(
            agent_user=ns.agent_user, agent_uid=uid, workspace=ns.workspace, runner_home=ns.runner_home, canaries=canary.files,
            decoy_pid=canary.decoy.pid, egress_canary="%s:%d" % (primary_ip(), canary.port), ports=ports, report=report,
            github_files=github, proxy_port=ns.proxy_port,
        )
        res = runner(argv, timeout=600)
    sys.stdout.write(res.stdout)
    raw = runner(["sudo", "-n", "-u", ns.agent_user, "cat", report])
    runner(["sudo", "-n", "-u", ns.agent_user, "rm", "-f", report])
    try:
        rep = json.loads(raw.stdout)
    except ValueError:
        rep = {}
    if ns.report:
        with open(ns.report, "w", encoding="utf-8") as fh:
            fh.write(raw.stdout if rep else "{}")
    if res.returncode != 0 or rep.get("ok") is not True or rep.get("linux") is not True or rep.get("uid") != uid:
        why = ", ".join(rep.get("failed", [])) or ("battery exit status %d" % res.returncode if res.returncode else "no usable report")
        print("agent-jail: the escape battery did not pass (%s): no marker written" % why, file=sys.stderr)
        return 1
    marker = ready_marker(
        agent_user=ns.agent_user, agent_uid=uid, workspace=ns.workspace, real_claude=real_claude, path=ns.agent_path, ports=ports,
        proxy_port=ns.proxy_port, report_sha256=hashlib.sha256(raw.stdout.encode("utf-8")).hexdigest(), max_usd=ns.max_usd,
        max_turns=ns.max_turns, wall_seconds=ns.wall_seconds, created=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    )
    written = runner(["sudo", "-n", "tee", MARKER], input_text=json.dumps(marker, sort_keys=True, indent=2) + "\n")
    runner(["sudo", "-n", "chown", "root:root", MARKER])
    runner(["sudo", "-n", "chmod", "0644", MARKER])
    if written.returncode != 0:
        print("agent-jail: could not write %s" % MARKER, file=sys.stderr)
        return 1
    print("agent-jail: ready (%d probes denied); wrote %s" % (len(rep.get("results", [])), MARKER))
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd")

    def common(p, ready=False):
        p.add_argument("--agent-user", default="agent")
        p.add_argument("--workspace", default="/home/agent", help="the agent's home and only writable place")
        p.add_argument("--ports", default=",".join(str(p) for p in DEFAULT_PORTS), help="loopback ports the agent may reach (the proxy's is added)")
        p.add_argument("--proxy-port", type=int, default=PROXY_PORT)
        p.add_argument("--runner-home", default=default_runner_home(), help="the CI user's home, closed to the agent")

    s = sub.add_parser("setup", help="create the agent user, the egress rules and the proxy (root)")
    common(s)
    s.add_argument("--runner-user", default=os.environ.get("SUDO_USER") or os.environ.get("USER") or "runner")
    s.add_argument("--allow", action="append", help="HOST:PORT the proxy may tunnel to (default: %s)" % ", ".join(MODEL_API))
    s.add_argument("--traverse", action="append", help="an account that must keep walking through the runner's home (the Lean services' user)")
    s.add_argument("--harden-path", metavar="PATH", help="the runner's PATH: take write permission for others off its directories and programs")
    s.add_argument("--print", action="store_true", help="print the script instead of running it")
    s.set_defaults(fn=cmd_setup)
    r = sub.add_parser("ready", help="run the escape battery as the agent and write the marker")
    common(r)
    r.add_argument("--real-claude", default="/opt/agent-tools/bin/claude")
    r.add_argument("--agent-path", default=AGENT_PATH)
    r.add_argument("--max-usd", type=float, default=agent_policy.DEFAULT_MAX_USD)
    r.add_argument("--max-turns", type=int, default=agent_policy.DEFAULT_MAX_TURNS)
    r.add_argument("--wall-seconds", type=int, default=agent_policy.DEFAULT_WALL_SECONDS)
    r.add_argument("--report", help="copy the battery's JSON report here")
    r.set_defaults(fn=cmd_ready)
    t = sub.add_parser("teardown", help="kill the agent's processes, remove the marker and the egress rules (root)")
    t.add_argument("--agent-user", default="agent")
    t.set_defaults(fn=cmd_teardown)
    ns = ap.parse_args(argv)
    if not getattr(ns, "fn", None):
        ap.print_usage(sys.stderr)
        return 2
    try:
        return ns.fn(ns)
    except jail.JailSpecError as exc:
        print("agent-jail: refused: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env bash
# What the escape battery cannot show: the whole launch chain, with a stand-in for the model CLI, on a runner that has been through
# `agent-jail.py setup` and `ready`. Used by .github/workflows/agent-selftest.yml; needs the stand-in installed as the real claude.
#
#   1. scripts/agent-run.py starts the stand-in as the agent user, in a fresh work directory, with the allowlisted environment
#      only (the credential yes; BRIDGE_TOKEN, GH_TOKEN and everything else of ours no), the proxy variables and the tool flags
#   2. killing the wrapper with SIGKILL takes the agent process with it
#   3. as the agent user, the model API host is reachable through the proxy and nothing else is: another host through the proxy,
#      and any host directly, fail
set -euo pipefail
cd "$(dirname "$0")/.."
fail() { echo "::error::smoke: $*"; exit 1; }

run_dir=$(mktemp -d /tmp/claude-tree-XXXXXX)
# the stand-in (running as the agent) writes its pid into the sticky /tmp, where only root may remove it
trap 'rm -rf "$run_dir"; sudo -n rm -f /tmp/agent-smoke-pid' EXIT
echo '{"mcpServers":{"Leak_IV":{"type":"sse","url":"http://127.0.0.1:7871/sse"}}}' > "$run_dir/mcp.json"
echo '{}' > "$run_dir/settings.json"
argv=(-p "prove it" --output-format stream-json --verbose --mcp-config "$run_dir/mcp.json" --tools=Bash --strict-mcp-config
      --dangerously-skip-permissions --max-turns 5 --max-budget-usd 1 --settings "$run_dir/settings.json")

echo "== 1. the launch"
out=$(BRIDGE_TOKEN=bridge-secret GH_TOKEN=gh-secret SOME_VARIABLE=1 CLAUDE_CODE_OAUTH_TOKEN=smoke-credential python3 scripts/agent-run.py "${argv[@]}")
echo "$out"
grep -qx 'user=agent' <<<"$out" || fail "the stand-in did not run as the agent user"
grep -q '^cwd=/home/agent/run\.[0-9a-f]*/work$' <<<"$out" || fail "unexpected working directory"
grep -qx 'CLAUDE_CODE_OAUTH_TOKEN=smoke-credential' <<<"$out" || fail "the credential did not arrive"
grep -qx 'HTTPS_PROXY=http://127.0.0.1:8899' <<<"$out" || fail "no proxy variable"
for leaked in BRIDGE_TOKEN GH_TOKEN SOME_VARIABLE; do ! grep -q "^$leaked=" <<<"$out" || fail "$leaked reached the agent"; done
grep -q '^args=-p prove it .*--tools=Bash --strict-mcp-config --dangerously-skip-permissions .*--max-turns 5 --max-budget-usd 1.0' <<<"$out" || fail "unexpected argv"
[ -z "$(sudo -n -u agent sh -c 'ls -d /home/agent/run.* 2>/dev/null' || true)" ] || fail "the run directory was not removed"

echo "== 2. killing the wrapper kills the agent"
sudo -n rm -f /tmp/agent-smoke-pid
python3 scripts/agent-run.py "${argv[@]/prove it/SLEEP}" > /dev/null 2>&1 &
wrapper=$!
for _ in $(seq 1 50); do [ -s /tmp/agent-smoke-pid ] && break; sleep 0.2; done
[ -s /tmp/agent-smoke-pid ] || fail "the stand-in never started"
pid=$(cat /tmp/agent-smoke-pid)
sudo -n kill -0 "$pid" || fail "the stand-in is not running"
kill -KILL "$wrapper"
for _ in $(seq 1 50); do sudo -n kill -0 "$pid" 2>/dev/null || break; sleep 0.2; done
! sudo -n kill -0 "$pid" 2>/dev/null || fail "the agent outlived its wrapper"
echo "the agent died with its wrapper"

echo "== 3. the network, as the agent"
as_agent() { sudo -n -u agent env -i PATH=/usr/bin:/bin "$@"; }
code=$(as_agent curl -sS -m 20 -o /dev/null -w '%{http_code}' --proxy http://127.0.0.1:8899 https://api.anthropic.com/ || true)
echo "api.anthropic.com through the proxy: HTTP $code"
[[ "$code" =~ ^[1-5][0-9][0-9]$ ]] || fail "the model API host is not reachable through the proxy"
if as_agent curl -sS -m 20 -o /dev/null --proxy http://127.0.0.1:8899 https://example.com/ 2>/dev/null; then fail "another host was reachable through the proxy"; fi
echo "example.com through the proxy: refused"
if as_agent curl -sS -m 10 -o /dev/null https://api.anthropic.com/ 2>/dev/null; then fail "the model API host was reachable without the proxy"; fi
echo "api.anthropic.com without the proxy: refused"
echo "smoke ok"

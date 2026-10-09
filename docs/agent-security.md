# Agent security: the translation agent runs contained

The agent that translates a theorem is an AI model with a shell, a network and a credential, and it reads Lean source that other people wrote. Anything in that source can talk to it. This page says what the exposure was, what changed, how to run and tune the new parts, and what is still a risk.

The toolkit behind it is [tengoku-warden](https://github.com/competemath/tengoku-warden), vendored in `scripts/warden/`. It treats every AI agent as an untrusted party and is modelled on what the [Tau Ceti Project](https://github.com/TauCetiProject) does and found. The credit and the comparison are in [docs/TAU-CETI.md](https://github.com/competemath/tengoku-warden/blob/main/docs/TAU-CETI.md) of that repository. We copied none of their code.

## What the exposure was

Read from the code before this change.

- **A deny-list, not a tool set.** `public/local-claude-bridge.mjs` started the Claude CLI with `--dangerously-skip-permissions` and `--disallowedTools WebSearch WebFetch`. Every other built-in tool existed, including `Bash`, `Write` and `Edit`. The architect used a longer deny-list and the single completions used none. Tau Ceti's reviewer ran for 79 days with a shell for the same reason: a flag that removes some tools does not define the tools.
- **The whole environment.** The spawns passed no `env`, so the CLI and every shell command it ran inherited the bridge's variables: `CLAUDE_CODE_OAUTH_TOKEN`, `BRIDGE_TOKEN`, and in a workflow anything else the job held.
- **Flags chosen by a web page.** `/run` and `/run-stream` took `permissionMode`, `allowedTools` and `disallowedTools` from the request body.
- **Open network, runner user.** In `translate.yml` the agent ran as the runner user, which can read the runner's home and the job's files, with unrestricted network.
- **Unpinned installers.** The elan installer was piped from `master` into `sh`, and `npm install -g @anthropic-ai/claude-code` took whatever was newest, in the job that later held the Claude token.
- **Unscanned artifacts and a blind push.** `out/`, which holds the bridge log, the recursion log and the bank, was uploaded for seven days without a secret scan, and the `finish` job retried `git pull --rebase` and `git push` in a loop.
- **A bank that opened pull requests unchecked.** `scripts/bank-flush.mjs` opened pull requests into the tree with the bot token and checked neither the content nor the paths.

## What changed

**In the bridge.**

- `claudeToolArgs(kind)` is the only place that decides tool flags. It returns a `--tools=` set and `--strict-mcp-config`, and the permission bypass only next to a set. The kinds are `prover` and `blind`, which get MCP tools and `Bash` only when allowed, `architect`, which gets MCP tools and never a shell, and `none`, for single completions, which gets no tools and no bypass.
- `Bash` exists only when `EMISSARY_JAIL=1` and `CLAUDE_BIN` is the jail wrapper, or when an operator sets `EMISSARY_ALLOW_BASH=1`, which is logged loudly on every spawn.
- `spawnClaude` is the only place that starts the CLI. It passes an environment built by `agentEnv()`: `PATH`, `LANG`, `LC_ALL`, `TZ`, `TMPDIR`, `TERM`, a `HOME`, the model credential, and `CLAUDE_CODE_MAX_OUTPUT_TOKENS` when a run asks for it. Nothing else.
- `--max-turns` and `--max-budget-usd` go on every spawn.
- `/run` and `/run-stream` no longer take tool or permission options from the page. A single completion gets no tools.
- When `EMISSARY_TRACE_DIR` is set, the CLI's stdout is written to a file there for each run.
- The hook scripts and the settings file are written into the run's own directory, so that what the agent was given can be read afterwards and staged for another user.

A regression test, `scripts/agent-tests/test_bridge_tools.py`, runs warden's `toolpolicy scan-source` on the bridge, checks that every spawn goes through `spawnClaude` and every argv through `claudeToolArgs`, and judges the argv the bridge really builds with warden's argv checker. Run on the bridge as it was before this change, every group of checks fails, and the scanner alone reports 12 violations.

**In the cloud run, `translate.yml`, agent mode.**

1. `step-security/harden-runner` runs first, in audit mode.
2. The elan installer is fetched at a commit and checked against its sha256 before it runs. The same is now true in every workflow that installed elan. The agent is installed at one exact version into `/opt/agent-tools`, owned by root.
3. `scripts/agent-jail.py setup` creates an unprivileged user `agent` with no sudo, no privileged group, no way into the runner's home and `/proc` mounted with `hidepid=2`. It also switches user namespaces off, and installs per-user kernel firewall rules. The agent can open TCP connections to the bridge, the two Lean services and one proxy, and to nothing else, on IPv4 and IPv6. The proxy runs as a third user and tunnels only to `api.anthropic.com:443`.
4. `scripts/agent-jail.py ready` runs the escape battery, `warden selftest`, as the agent against a host canary file, a decoy process, a listener outside the jail and the allowed ports. Only if every probe is denied does it write `/opt/emissary-jail/ready.json`, owned by root. If anything fails, the shard runs mechanically, `EMISSARY_NO_AGENT=1`, and the log says why.
5. The bridge starts `scripts/agent-run.py` in place of `claude`. The wrapper refuses without the ready file, judges the argv with warden's argv checker, accepts only plain loopback MCP servers, clamps the caps to the ceilings in the ready file, rebuilds the environment from an allowlist, and starts the agent as the `agent` user through `sudo -u agent env -i`. The credential travels on a pipe, never on a command line. A supervisor on the other side kills the agent and its children if the wrapper dies, even by SIGKILL, and removes the run's directory.
6. After the agent step, `scripts/agent-trace-gate.py` audits every trace against the translator policy. A tool outside the policy, a web or write tool, or a shell without the jail makes the shard fail, and the shard's bank, results and prefix cache are moved to `out/quarantine/`. `translate-finish.mjs` skips such a shard, so it banks nothing, and its entries stay unsettled for the next run.
7. `scripts/agent-artifacts.py` redacts secrets from `out/` with warden's secret scanner, and the upload does not happen if one would remain. A bank record that trips the scanner is set aside instead of banked. Artifacts are kept three days.
8. The `finish` job pushes with `scripts/safe-push.py`: fetch, rebase, and push with an expected-old-sha lease, `warden.safegit.push_cas`.

**In `scripts/bank-flush.mjs`.** Before a branch is pushed, `scripts/bank-guard.py` secret-scans the staged records, checks the pull request with `validate_pr` against a target marker the script writes, and checks the commit with `warden scope` against `scripts/agent-paths.json`. That file lists one allowed path, `data/staging/<library>/<batch>.jsonl`, as mode 100644 with no deletion, no binary file and one file per pull request. All batches of a library are built and checked before any is pushed. If any check fails, nothing of that library is pushed and its bank files stay where they are.

## Environment variables

| Variable | Read by | Meaning |
| --- | --- | --- |
| `EMISSARY_JAIL=1` | bridge, trace gate | The CLI runs in the proven jail. Gives `prover` and `blind` agents a shell. Ignored unless `CLAUDE_BIN` is `scripts/agent-run.py`. The workflow sets it only after the battery passed. |
| `EMISSARY_ALLOW_BASH=1` | bridge | Gives `prover` and `blind` agents a shell without the jail. The CLI then runs commands as the bridge's own user. Use it only on a machine you would let a stranger use. |
| `EMISSARY_MAX_USD` | bridge | Ceiling for `--max-budget-usd` on each CLI run. Default 20. |
| `EMISSARY_MAX_TURNS` | bridge | Ceiling for `--max-turns` on each CLI run. Default 400. A caller's lower limit wins. |
| `EMISSARY_TRACE_DIR` | bridge | Directory for one trace file per CLI run. The workflow uses `out/trace`. |
| `EMISSARY_AGENT_ENV_PASS` | bridge | Comma-separated extra variable names to pass to the CLI. Names of known secrets are refused. Each name is logged. |

The defaults of the two caps are in `AGENT_MAX_USD_DEFAULT` and `AGENT_MAX_TURNS_DEFAULT` in the bridge and in `scripts/agent_policy.py`, and a test keeps them equal.

A developer who runs the bridge on a laptop and relies on `claude login` gets no shell and keeps their own `HOME`, because the login lives there. With `CLAUDE_CODE_OAUTH_TOKEN` or `ANTHROPIC_API_KEY` set, every run gets a throwaway `HOME`.

## Proving the jail without spending anything

`agent-selftest.yml` is manual only, has a ten-minute limit, and holds no secret, no Lean and no model. It builds the same user, firewall and proxy on a fresh runner, runs the battery, then starts a stand-in program through the real wrapper and supervisor and checks the result: it ran as `agent`, in a fresh directory, with the credential and none of the bridge's variables, and it dies when the wrapper is killed. As the agent it then checks that the model API host is reachable through the proxy, another host is not, and nothing is reachable without it.

```bash
gh workflow run agent-selftest.yml --ref <branch>
```

Run it after any change to `scripts/agent-*.py`, `scripts/warden`, or the runner image the jobs use. Its log lists every probe.

The battery leaves out one probe, `userns_differs_from_host`, because this is a user jail and not a namespace jail: the agent shares the host's user namespace by design. The probe that covers that vector here is `nested_userns_denied`, which passes because user namespaces are switched off. The omission is printed in the log and recorded in the ready file.

## Turning harden-runner from audit to block

Audit mode records every outbound connection of the job and changes nothing. We do not guess the list of hosts a translation job needs.

1. Run `translate.yml` once, in either mode. Open the run, then the harden-runner step, and copy the network events table from its summary.
2. Save it to a file and turn it into an allowlist. `--render` prints it in the form the workflow takes, and refuses cloud metadata, link-local, loopback and private addresses.

   ```bash
   PYTHONPATH=scripts python3 -m warden egress-proxy --from-audit events.txt --render
   ```
3. Read the list. Remove anything you would not allow on purpose.
4. In `translate.yml`, change `egress-policy: audit` to `egress-policy: block` and add the list as `allowed-endpoints`. Do the same for the `finish` job, which needs far fewer hosts.
5. Run once more and watch for a blocked connection.

The agent does not depend on this step. Its own network is fenced by the kernel rules and the proxy whether harden-runner is in audit or block.

## Updating pinned things

- **Claude Code.** The version is `CLAUDE_CODE_VERSION` in `translate.yml` and in `goals-suggest.yml`. A test requires one exact version in both. To bump, read the release notes, change both, and run `agent-selftest.yml` and a small `translate.yml` run in agent mode. The launch flags the wrapper and the bridge rely on are `--tools`, `--strict-mcp-config`, `--mcp-config`, `--settings`, `--max-turns`, `--max-budget-usd` and `--dangerously-skip-permissions`.
- **tengoku-warden.** `scripts/warden/` is a byte-for-byte copy. `scripts/warden/PIN` records the commit and the sha256 of each file, and a test fails if they differ. To update, change tengoku-warden, then `python3 scripts/warden/refresh.py <checkout>`, then run the tests.
- **elan.** The commit and sha256 are written in each workflow that installs it. To bump, take a new commit of `leanprover/elan`, compute `sha256sum elan-init.sh` for that commit, and change every occurrence together. The tests find stragglers.

## Residual risks

Written down on purpose.

1. **The agent holds its model credential.** To call the model it needs the token, and nothing here stops it from sending that token to the one host it may reach. With an API key and warden's auth proxy the agent's process would never hold the key. A subscription token may not work through such a proxy. Rotate `CLAUDE_CODE_OAUTH_TOKEN` after the first run of the jailed agent, and prefer an API key with a spend limit set in the provider console.
2. **Shared kernel.** The agent is a different user on the same machine, not a virtual machine. A kernel bug defeats the jail. The battery proves the vectors it probes are closed on this runner today, not that no other exists.
3. **A shell with network to a proxy.** Inside the jail the agent can run commands as `agent`. It can use the CPU, fill its own home, and talk to the Lean services and the bridge's governor on loopback. The governor's `/gov/...` routes need no token, so the agent can reach other runs' governors on the same shard.
4. **A persuaded model can still produce bad output.** The containment limits what it can reach and publish. What it writes is still checked only by the two gates and by the checks in this page, and those cannot prove that a translation says what the original meant.
5. **Heuristic scanners.** The secret scanner finds credential shapes, not encoded or split secrets.
6. **Audit mode is observation.** Until harden-runner is switched to block, the runner itself can reach any host. Only the agent is fenced.
7. **The tool policy depends on the CLI.** `--tools=` with an empty value and the names of the tools the CLI lists in a session are as documented for Claude Code 2.1.218. The trace gate fails closed on a name it does not know, and says which; add a legitimate one to `AUDIT_EXTRA_TOOLS` in `scripts/agent_policy.py`.
8. **Continuous sessions do not survive.** Control III in the bridge resumes one conversation across calls. Each run now gets a fresh `HOME`, so a resumed session is not found and the arm starts again each time. The cloud run's driver, `scripts/run-recurse.mjs`, does not ask for it.
9. **Other workflows.** `goals-suggest.yml` runs the Claude CLI with `--allowedTools` and no tool set, on text from another repository. It has the same shape as the bug fixed here and is not yet moved into the jail. `trial-library-build.yml` runs a Python script it downloads from the `master` branch of mathlib4.

## Credit

The design follows what the [Tau Ceti Project](https://github.com/TauCetiProject) published about running a library that AI agents write and review, above all its tool restriction for reviewers, its self-tested sandbox with host canaries, its scoped proxy, its pinned installers and its habit of writing down residual risks. The record of what we took from them, where their own history shows a gap, and how each module differs is in [docs/TAU-CETI.md](https://github.com/competemath/tengoku-warden/blob/main/docs/TAU-CETI.md) of tengoku-warden.

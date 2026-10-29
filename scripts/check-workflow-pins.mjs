// node scripts/check-workflow-pins.mjs — nothing a workflow installs or runs on may move under it (exits 1 on a violation). Text checks on .github/workflows/*.yml, comments left out:
//   - an action is `uses:` a full commit (a local ./ workflow is fine);
//   - `npm install -g` names an exact version of every package (no tag, no range, none): the Claude CLI that translates is one;
//   - `pip install` names `==` for every requirement;
//   - a script piped into a shell (`curl ... | sh`) is fetched from raw.githubusercontent.com at a full commit, never a branch;
//   - nothing says `@latest`, `@next`, `@stable`;
//   - the heavy workflows (setup-*, bump-*, translate*) run on a concrete image (ubuntu-26.04), written out (no `runs-on: ${{ matrix.os }}`), not on a `-latest` label that moves on GitHub's schedule: a run that exports differently
//     than the one before it should not be explained by an operating system nobody changed.
// Not covered, said here so nobody thinks they are: `apt-get install` (the distribution's version of the pinned image), the elan binary the pinned elan-init.sh downloads (it takes the latest
// release), and the toolchains, which each library pins itself.
import { readFileSync, readdirSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

export const HEAVY = /^(setup-|bump-|translate)/
const SHA = /^[0-9a-f]{40}$/
const EXACT = /^(?:@[\w.-]+\/)?[\w.-]+@\d+\.\d+\.\d+(?:[-+][\w.+-]+)?$/

// the active lines of a workflow: comments left out, and a shell command continued with a trailing backslash joined onto the line it starts on (the lines it continues are left empty, so
// that a finding keeps the line number of the source). `curl URL \` followed by `| sh` is one command.
export function stripComments(text, join = true) {
  const lines = text.split("\n").map((l) => (/^\s*#/.test(l) ? "" : l.replace(/\s#\s.*$/, "")))
  for (let i = 0; join && i < lines.length; i++) {
    let k = i
    while (/\\\s*$/.test(lines[i]) && k + 1 < lines.length) {
      k++
      lines[i] = lines[i].replace(/\\\s*$/, " ") + lines[k].trim()
      lines[k] = ""
    }
    i = k
  }
  return lines
}

// the command words after `npm install -g` / `pip install`, up to the end of that command
const argsAfter = (line, re) => {
  const m = line.match(re)
  if (!m) return null
  return line.slice(m.index + m[0].length).split(/&&|\|\||;|\||\)|`/)[0].trim().split(/\s+/).filter(Boolean)
}

export const RULES = ["actions", "npm", "pip", "curl", "moving", "runner", "continuation"]
// `skip`: rules left out (the tests leave each out in turn to see that the checks notice)
export function findUnpinned(text, file, skip = []) {
  const out = []
  const on = (rule) => !skip.includes(rule)
  const add = (n, why, line) => out.push({ file, line: n + 1, why, text: line.trim().slice(0, 140) })
  stripComments(text, on("continuation")).forEach((line, n) => {
    const use = line.match(/^\s*(?:-\s+)?uses:\s*(\S+)/)
    if (on("actions") && use && !use[1].startsWith("./") && !SHA.test(use[1].split("@")[1] || "")) add(n, "an action not pinned to a full commit", line)
    const npm = argsAfter(line, /\bnpm\s+(?:install|i|add)\b/)
    if (on("npm") && npm && /(?:^|\s)(?:-g|--global)\b/.test(line)) {
      const pkgs = npm.filter((a) => !a.startsWith("-"))
      if (!pkgs.length) add(n, "npm install -g names no package", line)
      for (const p of pkgs) if (!EXACT.test(p)) add(n, `npm install -g ${p}: not an exact version (name@1.2.3)`, line)
    }
    const pip = argsAfter(line, /\bpip3?\s+install\b/) || argsAfter(line, /\bpython3?\s+-m\s+pip\s+install\b/)
    if (on("pip") && pip) {
      for (const p of pip.filter((a) => !a.startsWith("-")).map((a) => a.replace(/^["']|["']$/g, ""))) if (!/^[\w.-]+(?:\[[\w,]+\])?==[\w.!+-]+$/.test(p)) add(n, `pip install ${p}: not pinned with ==`, line)
    }
    if (on("curl") && /\bcurl\b[^|]*\|\s*(?:sudo\s+)?(?:sh|bash)\b/.test(line)) {
      const url = (line.match(/https?:\/\/[^\s"']+/) || [""])[0]
      const m = url.match(/^https:\/\/raw\.githubusercontent\.com\/[\w.-]+\/[\w.-]+\/([^/]+)\//)
      if (!m || !SHA.test(m[1])) add(n, `a script piped into a shell is not fetched at a full commit (${url || "no URL"})`, line)
    }
    if (on("moving") && /@(?:latest|next|stable)\b/.test(line)) add(n, "a moving tag (@latest, @next, @stable)", line)
    if (on("runner") && HEAVY.test(file) && /\bruns-on:/.test(line)) {
      if (/-latest\b/.test(line)) add(n, "a heavy workflow on a -latest runner label", line)
      else if (/\$\{\{/.test(line)) add(n, "a heavy workflow whose runner is an expression (a matrix value or an input can be -latest): write the label", line)
    }
  })
  return out
}

export function checkDir(dir) {
  return readdirSync(dir).filter((f) => /\.ya?ml$/.test(f)).sort().flatMap((f) => findUnpinned(readFileSync(join(dir, f), "utf8"), f))
}

if (process.argv[1] && process.argv[1] === fileURLToPath(import.meta.url)) {
  const bad = checkDir(join(dirname(fileURLToPath(import.meta.url)), "..", ".github", "workflows"))
  for (const v of bad) console.log(`${v.file}:${v.line}: ${v.why}\n    ${v.text}`)
  console.log(bad.length ? `${bad.length} unpinned` : "ok: everything the workflows install or run on is pinned")
  process.exit(bad.length ? 1 : 0)
}

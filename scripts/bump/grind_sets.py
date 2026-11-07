#!/usr/bin/env python3
"""grind_sets.py — rewrite a library's custom grind sets and its inert lines away, so that the module can go to the tree with what it says unchanged.

A CUSTOM GRIND SET. `register_grind_attr modal` makes an attribute `modal`; `@[modal] theorem foo` puts `foo` in it; `grind [modal]` (or `grind only [modal, bar]`) asks
grind to use every lemma in it. Registering the attribute runs the library's code when the module loads, which the tree's content lint refuses: cslib (2026-11-06) has its
one set in Cslib/Tactic/GrindAttrs.lean, which every module imports through Cslib/Init, so all 251 modules were refused with 2,522 declarations that passed Gate 2.
Rewritten:
  `register_grind_attr X`           removed;
  `X` in `@[...]`, `attribute [X] a` removed from the list (strip_attrs.py then removes an empty one, as for any refused attribute);
  `X` in the list of a grind call     replaced by the lemmas tagged X that the call can see (in a module it imports, or earlier in its own file), each with the
                                      modifier its tag had (`@[X =] theorem a` gives `= N.a`).
What a declaration SAYS never changes (attributes and tactic arguments are not part of a statement). A proof that grind no longer closes is found by the tree's own
build of the module (bundle.py verify), and the module is left out as before. Only lemmas the bundle keeps are listed: one the pruning left out would be an unknown name.

INERT LINES. `#adaptation_note /-- ... -/` (a note for the library's maintainers; a command or a tactic, it does nothing) and `set_option linter.<x> <v>` (a linter only
reports, it changes no declaration) are removed: the lint refuses both, cslib has them in about 400 modules.

Only code is touched (adapters.code_mask: not comments or strings).
"""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from adapters import code_mask  # noqa: E402

IDENT = r"[A-Za-z_][\w'.!?]*"
REGISTER = re.compile(rf"^[ \t]*register_grind_attr[ \t]+({IDENT})[ \t]*\n?", re.M)
ATTR_BLOCK = re.compile(r"@\[")
ATTR_CMD = re.compile(rf"^[ \t]*(?:(?:local|scoped)[ \t]+)?attribute[ \t]*\[", re.M)
DECL = re.compile(
    rf"\s*(?:/--.*?-/\s*)?(?:(?:private|protected|noncomputable|nonrec|public|partial|unsafe|meta)\s+)*(?:theorem|lemma|def|abbrev|instance|axiom)\s+({IDENT})", re.S
)
NAMESPACE = re.compile(rf"^[ \t]*(namespace|section|end)\b[ \t]*({IDENT})?", re.M)
GRIND_CALL = re.compile(r"\bgrind(?:\?|_)?\b(?:[ \t]+(?:only\b|\([^)\n]*\)|[ \t]))*[ \t]*\[")
ADAPTATION = re.compile(r"#adaptation_note\b[ \t]*(?:/--.*?-/)?[ \t]*\n?", re.S)
LINTER_IN = re.compile(r"set_option[ \t]+linter\.[\w.]+[ \t]+\S+[ \t]+in\b[ \t]*\n?[ \t]*")
LINTER_LINE = re.compile(r"^[ \t]*set_option[ \t]+linter\.[\w.]+[ \t]+\S+[ \t]*(?:\n|$)", re.M)


_MASKS: dict[str, list[bool]] = {}


def _mask(text: str) -> list[bool]:
    """code_mask of `text`, kept for the last text asked about (the scanners ask about the same text many times)"""
    m = _MASKS.get(text)
    if m is None:
        m = code_mask(text)
        _MASKS.clear()
        _MASKS[text] = m
    return m


def _close(text: str, i: int) -> int:
    """the index just past the `]` that closes the bracket opened right before i (nested brackets counted; a bracket in a comment or a string is not one)"""
    mask = _mask(text)
    depth = 1
    while i < len(text) and depth:
        if mask[i]:
            depth += {"[": 1, "]": -1}.get(text[i], 0)
        i += 1
    return i


def _items(body: str) -> list[str]:
    """the comma-separated items of a bracket's content, at the top level (a comma or bracket in a comment or a string does not count)"""
    mask = code_mask(body)
    out, depth, cur = [], 0, ""
    for k, ch in enumerate(body):
        if not mask[k]:
            cur += ch
            continue
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


def _namespace_at(text: str, mask: list[bool], pos: int) -> str:
    stack: list[tuple[str, str]] = []
    for m in NAMESPACE.finditer(text, 0, pos):
        if not mask[m.start(1)]:
            continue
        kind, name = m.group(1), m.group(2) or ""
        if kind == "end":
            if stack:
                stack.pop()
        else:
            stack.append((kind, name))
    return ".".join(n for k, n in stack if k == "namespace" and n)


def _set_item(item: str, names: set[str], local_cmd: bool = False) -> tuple[str, str, bool, bool] | None:
    """(set, modifier, removal, local) when an attribute item names one of `names`: `X`, `X =`, `scoped X`, `local X =`, `-X` (a removal); None otherwise. `local`: the tag holds
    in its own file only (`local X`, or a `local attribute [...]` command), so a call in another module does not see it"""
    parts = item.split()
    local = local_cmd
    while parts and parts[0] in ("scoped", "local"):
        local = local or parts[0] == "local"
        parts = parts[1:]
    if not parts:
        return None
    head, removal = parts[0], False
    if head.startswith("-") and head[1:] in names:
        head, removal = head[1:], True
    if head not in names:
        return None
    return head, " ".join(parts[1:]), removal, local


def sets_of(texts: dict[str, str]) -> dict[str, str]:
    """custom grind set -> the module that registers it"""
    out = {}
    for mod, t in texts.items():
        mask = code_mask(t)
        for m in REGISTER.finditer(t):
            if mask[m.start(1)]:
                out.setdefault(m.group(1).split(".")[-1], mod)
    return out


def tags_of(text: str, names: set[str]) -> list[tuple[int, str, str, bool, str, bool]]:
    """(position, set, modifier, private, lemma name, local) for every lemma the module puts in one of `names`; the name is qualified with the namespace it is declared in.
    A removal (`attribute [-X] foo`) is listed with the modifier "-" (see removed_of)."""
    mask = code_mask(text)
    out = []
    for m in ATTR_BLOCK.finditer(text):
        if not mask[m.start()]:
            continue
        end = _close(text, m.end())
        for item in _items(text[m.end() : end - 1]):
            hit = _set_item(item, names)
            if hit and not hit[2]:
                d = DECL.match(text, end)
                if d:
                    ns = _namespace_at(text, mask, m.start())
                    name = d.group(1)
                    full = name if name.startswith("_root_.") or not ns else f"{ns}.{name}"
                    private = re.match(r"\s*(?:/--.*?-/\s*)?(?:\w+\s+)*?private\b", text[end : d.start(1)], re.S) is not None
                    out.append((m.start(), hit[0], hit[1], private, full.removeprefix("_root_."), hit[3]))
    for m in ATTR_CMD.finditer(text):
        if not mask[m.end() - 1]:
            continue
        end = _close(text, m.end())
        line_end = text.find("\n", end)
        targets = text[end : len(text) if line_end < 0 else line_end].split()
        ns = _namespace_at(text, mask, m.start())
        local_cmd = re.match(r"[ \t]*local\b", text[m.start() : m.end()]) is not None
        for item in _items(text[m.end() : end - 1]):
            hit = _set_item(item, names, local_cmd)
            if hit:
                for tgt in targets:
                    full = tgt if ("." in tgt or not ns) else f"{ns}.{tgt}"
                    # a private declaration (its name is mangled) can only be named in its own module
                    private = re.search(rf"\bprivate\s+(?:\w+\s+)*?(?:theorem|lemma|def|abbrev|instance)\s+{re.escape(tgt.split('.')[-1])}\b", text) is not None
                    out.append((m.start(), hit[0], "-" if hit[2] else hit[1], private, full, hit[3]))
    return sorted(out)


def _drop_from_lists(text: str, names: set[str]) -> tuple[str, int]:
    """`X` taken out of every `@[...]` and `attribute [...]` list; an emptied `@[]` or `attribute [] a` is removed by strip_attrs.strip_attributes afterwards"""
    mask = code_mask(text)
    edits = []
    for rx in (ATTR_BLOCK, ATTR_CMD):
        for m in rx.finditer(text):
            if not mask[m.end() - 1]:
                continue
            end = _close(text, m.end())
            items = _items(text[m.end() : end - 1])
            kept = [it for it in items if not _set_item(it, names)]
            if len(kept) == len(items):
                continue
            if kept:
                edits.append((m.end(), end - 1, ", ".join(k.strip() for k in kept)))
            elif rx is ATTR_BLOCK:  # `@[X]` alone: the whole `@[...]` goes, with the space after it
                stop = end
                while stop < len(text) and text[stop] in " \t":
                    stop += 1
                if stop < len(text) and text[stop] == "\n" and text[m.start() - 1 : m.start()] in ("", "\n"):
                    stop += 1
                edits.append((m.start(), stop, ""))
            else:  # `attribute [X] a b`: the whole command, to the end of its line
                line_end = text.find("\n", end)
                edits.append((m.start(), len(text) if line_end < 0 else line_end + 1, ""))
    for a, b, new in sorted(edits, reverse=True):
        text = text[:a] + new + text[b:]
    return text, len(edits)


def rewrite_grind_sets(texts: dict[str, str], imports: dict[str, list[str]]) -> tuple[dict[str, str], dict[str, dict[str, int]]]:
    """See the module's doc. `imports`: module -> the library modules it imports directly. Returns the new texts and, per module, its counts (rewrite() adds up those of the
    modules the guard lets through)."""
    sets = sets_of(texts)
    per: dict[str, dict[str, int]] = {}
    if not sets:
        return texts, per
    names = set(sets)
    tags = {mod: tags_of(t, names) for mod, t in texts.items()}
    # which lemmas the bundle keeps: a name it declares in its pruned text
    declared = {mod: {d.group(1) for d in re.finditer(rf"(?:theorem|lemma|def|abbrev|instance)\s+({IDENT})", t)} for mod, t in texts.items()}

    def kept(mod: str, full: str) -> bool:
        return full.split(".")[-1] in {n.split(".")[-1] for n in declared.get(mod, ())}

    seen: dict[str, set[str]] = {}

    def below(mod: str) -> set[str]:
        if mod not in seen:
            out, todo = set(), list(imports.get(mod, []))
            while todo:
                x = todo.pop()
                if x not in out:
                    out.add(x)
                    todo.extend(imports.get(x, []))
            seen[mod] = out
        return seen[mod]

    out = {}
    for mod, text in texts.items():
        st = per.setdefault(mod, {"set tags removed": 0, "grind calls rewritten": 0, "lemmas listed": 0, "set registrations removed": 0})
        mask = code_mask(text)
        edits = []
        for m in GRIND_CALL.finditer(text):
            if not mask[m.start()]:
                continue
            end = _close(text, m.end())
            items = _items(text[m.end() : end - 1])
            if not any(it.strip() in names for it in items):
                continue
            new_items = []
            for it in items:
                s = it.strip()
                if s not in names:
                    new_items.append(s)
                    continue
                # another module's tag is seen unless it is private (a mangled name) or local (it holds in its own file only)
                visible = [(md, t) for md in sorted(below(mod)) for t in tags.get(md, []) if t[1] == s and not t[3] and not t[5]]
                visible += [(mod, t) for t in tags.get(mod, []) if t[1] == s and t[0] < m.start()]
                # `attribute [-X] foo` takes foo out of the set (anywhere the call sees: an imported module, or earlier in its own file)
                removed = {t[4] for _, t in visible if t[2] == "-"}
                for md, (_, _, modifier, private, full, _) in visible:
                    if modifier != "-" and full not in removed and kept(md, full):
                        new_items.append(f"{modifier} {full.split('.')[-1] if private else full}".strip())
                        st["lemmas listed"] += 1
            edits.append((m.end(), end - 1, ", ".join(dict.fromkeys(new_items))))
            st["grind calls rewritten"] += 1
        for a, b, new in sorted(edits, reverse=True):
            text = text[:a] + new + text[b:]
        text, n = _drop_from_lists(text, names)
        st["set tags removed"] += n
        mask = code_mask(text)
        regs = [(_with_doc(text, r.start()), r.end()) for r in REGISTER.finditer(text) if mask[r.start(1)]]
        st["set registrations removed"] += len(regs)
        text = "".join(piece for piece in _cut(text, regs))
        out[mod] = text
    return out, per


def _with_doc(text: str, start: int) -> int:
    """`start`, moved back over the doc comment right before it (`/-- ... -/` and whitespace): a doc comment left without its command does not compile"""
    head = text[:start].rstrip()
    if head.endswith("-/"):
        open_ = head.rfind("/--")
        if open_ >= 0 and "-/" not in head[open_ + 3 : -2]:
            return open_
    return start


def _cut(text: str, spans: list[tuple[int, int]]):
    last = 0
    for a, b in sorted(spans):
        yield text[last:a]
        last = b
    yield text[last:]


def strip_inert_lines(text: str) -> tuple[str, int]:
    """`#adaptation_note` (with its note) and `set_option linter.*` (a line of its own, or `... in` before a command) removed; the count removed"""
    n = 0
    for rx in (ADAPTATION, LINTER_IN, LINTER_LINE):
        mask = code_mask(text)
        spans = [(m.start(), m.end()) for m in rx.finditer(text) if mask[m.start()]]
        n += len(spans)
        text = "".join(_cut(text, spans))
    return text, n


def _skeleton(text: str) -> str:
    """The text with everything the rewrite may touch taken out: attribute lists, `attribute [...]` commands, the argument lists of grind calls, the registration and the
    inert lines; whitespace collapsed. Two texts with the same skeleton say the same things and prove them the same way, up to grind's lemma lists."""
    mask = code_mask(text)
    spans = []
    for rx in (ATTR_BLOCK, GRIND_CALL):
        for m in rx.finditer(text):
            if mask[m.start()]:
                spans.append((m.start(), _close(text, m.end())))
    for rx in (ATTR_CMD, REGISTER, LINTER_LINE):
        for m in rx.finditer(text):
            if mask[m.start()]:
                start = _with_doc(text, m.start()) if rx is REGISTER else m.start()  # a registration goes with its doc comment
                if rx is ATTR_CMD:  # to the end of its line (the targets); the other two patterns end with their line already
                    line_end = text.find("\n", m.end())
                    spans.append((start, len(text) if line_end < 0 else line_end))
                else:
                    spans.append((start, m.end()))
    for rx in (ADAPTATION, LINTER_IN):
        for m in rx.finditer(text):
            if mask[m.start()]:
                spans.append((m.start(), m.end()))
    merged: list[tuple[int, int]] = []
    for a, b in sorted(spans):
        if merged and a <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(b, merged[-1][1]))
        else:
            merged.append((a, b))
    return re.sub(r"\s+", " ", "".join(_cut(text, merged))).strip()


def notice(upstream: str, path: str, what: list[str]) -> str:
    """The change notice a changed module carries (a module docstring): where it came from and what the factory changed. The licences of the libraries the tree takes
    (Apache-2.0 section 4(b), and the like) ask for a prominent notice in every changed file; it also tells a reader why the file differs from upstream."""
    return (f"/-! Tengoku change notice: this file was changed by the Tengoku factory from {upstream}, `{path}`: " + "; ".join(what)
            + ". What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/")


def rewrite(texts: dict[str, str], imports: dict[str, list[str]]) -> tuple[dict[str, str], dict[str, list[str]], dict[str, int]]:
    """Custom grind sets rewritten away (rewrite_grind_sets) and inert lines removed (strip_inert_lines), module by module, under a GUARD: a module whose skeleton (_skeleton)
    is not the same before and after is shipped as it was (and the lint refuses it as before), so the rewrite can never change anything but attribute lists, grind's lemma
    lists and the removed lines. Returns the texts, what was changed in each changed module (for its notice), and counts."""
    new, per = rewrite_grind_sets(texts, imports)
    sets = sets_of(texts)
    out: dict[str, str] = {}
    changes: dict[str, list[str]] = {}
    # counts of the changes that SHIP: a module the guard keeps as it was adds nothing to them
    stats = {"grind sets": len(sets), "set registrations removed": 0, "set tags removed": 0, "grind calls rewritten": 0, "lemmas listed": 0, "inert lines removed": 0,
             "modules changed": 0, "modules kept as they were (guard)": 0}
    for mod, before in texts.items():
        after, inert = strip_inert_lines(new[mod])
        if after == before:
            out[mod] = before
            continue
        if _skeleton(after) != _skeleton(before):
            out[mod] = before
            stats["modules kept as they were (guard)"] += 1
            continue
        what = []
        reg = [s for s, m in sets.items() if m == mod]
        if reg:
            what.append("removed the registration of the grind set" + ("s " if len(reg) > 1 else " ") + ", ".join(f"`{s}`" for s in sorted(reg)) + " (it runs code when the module loads)")
        tags_here = len(tags_of(before, set(sets)))
        if tags_here:
            what.append(f"removed {tags_here} tag(s) of the custom grind set(s) {', '.join(f'`{s}`' for s in sorted(sets))} from declarations")
        calls = sum(1 for m in GRIND_CALL.finditer(before) if any(it.strip() in sets for it in _items(before[m.end() : _close(before, m.end()) - 1])))
        if calls:
            what.append(f"wrote out the lemmas of those sets in {calls} `grind` call(s)")
        if inert:
            what.append(f"removed {inert} `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them)")
        stats["inert lines removed"] += inert
        stats["modules changed"] += 1
        for k, v in per.get(mod, {}).items():
            stats[k] += v
        out[mod] = after
        changes[mod] = what
    return out, changes, stats

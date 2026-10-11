"""lean_names.py — the Lean names a module declares, as the tree's environment sees them (for the clash that `import X failed, environment already contains 'f' from Y` reports).

`names(text)` is the set of fully qualified names of the module's non-private declarations (theorem, lemma, def, abbrev, instance, structure, class, inductive, opaque, axiom): the
`namespace` / `section` / `end` nesting is tracked, a `_root_.` name is taken as written, and only code counts (comments and strings are masked). It is the same reading as the
merge queue's clash check by hand (scan/clash_tree.py): the tree loads every module into one environment, so two namespaces of the tree declaring one name cannot both be imported.
"""

from __future__ import annotations

import re

from adapters import code_mask

DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:protected|noncomputable|unsafe|partial|nonrec|public|meta)[ \t]+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)[ \t]+([^\s:({\[⦃]+)",
    re.M,
)
PRIVATE = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:protected|noncomputable|unsafe|partial|nonrec|public|meta)[ \t]+)*private\b")
NS = re.compile(r"^[ \t]*namespace[ \t]+(\S+)", re.M)
END = re.compile(r"^[ \t]*end(?:[ \t]+(\S+))?[ \t]*$", re.M)
SECTION = re.compile(r"^[ \t]*(?:noncomputable[ \t]+)?section(?:[ \t]+(\S+))?[ \t]*$", re.M)


def names(text: str) -> set[str]:
    mask = code_mask(text)
    code = "".join(c if k else (" " if c != "\n" else "\n") for c, k in zip(text, mask))
    events: list[tuple[int, str, str]] = []
    for m in NS.finditer(code):
        events.append((m.start(), "ns", m.group(1)))
    for m in SECTION.finditer(code):
        events.append((m.start(), "sec", m.group(1) or ""))
    for m in END.finditer(code):
        events.append((m.start(), "end", m.group(1) or ""))
    for m in DECL.finditer(code):
        line_start = code.rfind("\n", 0, m.start()) + 1
        line_end = code.find("\n", m.end())
        if PRIVATE.match(code[line_start : line_end if line_end >= 0 else len(code)]):
            continue
        events.append((m.start(), "decl", m.group(2)))
    events.sort(key=lambda e: e[0])
    stack: list[tuple[str, str]] = []  # (kind, name)
    out: set[str] = set()
    for _, kind, val in events:
        if kind == "ns":
            stack.append(("ns", val))
        elif kind == "sec":
            stack.append(("sec", val))
        elif kind == "end":
            if stack:
                stack.pop()
        elif val.startswith("_root_."):
            out.add(val[len("_root_.") :])
        else:
            prefix = ".".join(v for k, v in stack if k == "ns")
            out.add(f"{prefix}.{val}" if prefix else val)
    return out

#!/usr/bin/env python3
"""Compact the generated Challenge to fit Palomar's single-file size limit (< 1000 lines, < 100 KiB).

Meaning-preserving text transforms only (Comparator re-checks every constant):
* the Mathlib import list becomes `public import Mathlib` (non-Mathlib imports are kept);
* blank lines, full-line `--` comments and non-doc block comments (`/-! -/`, `/- -/`) are
  dropped; declaration docstrings (`/-- -/`) are kept;
* every source module opened `@[expose] public section` (and often `noncomputable section`);
  these are hoisted to the top of the file once, and the per-module copies and their `end`s
  are dropped.
Usage: compact_challenge.py FILE  (rewrites FILE in place)
"""
import os, re, sys

path = sys.argv[1]
RESET = "run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}"
RESET_LIST = os.path.join(os.path.dirname(os.path.abspath(__file__)), "challenge_reset_modules.txt")
CTX = re.compile(r"^(open|variable|include|omit|set_option|local |scoped )")


GLOBAL_OPEN = ["MeasureTheory", "Filter", "Topology", "Set"]
GLOBAL_SCOPED = ["NNReal", "ENNReal", "Topology", "BigOperators"]


def targets():
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "ComparatorClosure.lean.in"), encoding="utf-8").read()
    body = re.search(r"def targets : List Name := \[(.*?)\]", src, flags=re.S).group(1)
    return {n.split(".")[-1] for n in re.findall(r"`(\S+?)[,\s]", body + " ")}


def drop_aux_docs(lines):
    """Theorems that are not compared targets are lemma holes (`by sorry`) that only fix the
    statement of a lemma a copied definition refers to; their docstrings are dropped (every
    definition keeps its docstring)."""
    keep = targets()
    res, i = [], 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("/--"):
            j = i
            while not lines[j].rstrip().endswith("-/"):
                j += 1
            nxt = j + 1
            while nxt < len(lines) and re.match(r"^@\[[^\]]*\]\s*$", lines[nxt]):
                nxt += 1
            m = re.match(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec) )*(?:theorem|lemma)\s+(\S+)",
                         lines[nxt] if nxt < len(lines) else "")
            if m and m.group(1).split(".")[-1] not in keep:
                i = j + 1
                continue
        res.append(l)
        i += 1
    return res


def hoist_opens(lines):
    """Open the namespaces almost every source module opens once, at the top of the file, and
    drop them from the per-module `open` lines (Comparator re-checks every elaborated value)."""
    res = []
    for l in lines:
        if l == "set_option warn.sorry false":
            res.append(l)
            res.append("open " + " ".join(GLOBAL_OPEN))
            res.append("open scoped " + " ".join(GLOBAL_SCOPED))
            continue
        m = re.match(r"^open (scoped )?([A-Za-z0-9_. ]+)$", l)
        if m:
            drop = GLOBAL_SCOPED if m.group(1) else GLOBAL_OPEN + GLOBAL_SCOPED * 0
            if m.group(1):
                rest = [x for x in m.group(2).split() if x not in GLOBAL_SCOPED]
            else:
                rest = [x for x in m.group(2).split() if x not in GLOBAL_OPEN]
            if not rest:
                continue
            l = "open " + (m.group(1) or "") + " ".join(rest)
        res.append(l)
    return res


def flatten(lines):
    """Drop the per-module `section ... end` wrapper and merge consecutive modules that live in
    the same namespace. A module that has scoped context (`open`, `variable`, ...) keeps its own
    `section ... end` inside that namespace, so that context does not reach later modules.
    The aux-lemma cache reset (see gen_challenge.py) is kept only for the modules listed in
    scripts/challenge_reset_modules.txt (those whose generated `_proof_N` names would otherwise
    collide with an earlier module's; Comparator detects any mismatch)."""
    resets = None
    if os.path.exists(RESET_LIST):
        resets = {x.strip() for x in open(RESET_LIST) if x.strip() and not x.startswith("#")}
    head, mods, cur = [], [], None
    i = 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("-- source module: "):
            assert lines[i + 1] == "section" or lines[i - 1] == "section", lines[i - 1:i + 2]
            if head and head[-1] == "section":
                head.pop()
            elif mods and mods[-1][1] and mods[-1][1][-1] == "section":
                mods[-1][1].pop()
            cur = (l.split(": ", 1)[1], [])
            mods.append(cur)
            i += 1
            continue
        (cur[1] if cur else head).append(l)
        i += 1
    res = list(head)
    path = []  # currently open namespace components (outside any module section)

    def goto(target):
        k = 0
        while k < len(path) and k < len(target) and path[k] == target[k]:
            k += 1
        while len(path) > k:
            res.append(f"end {path.pop()}")
        for c in target[k:]:
            res.append(f"namespace {c}")
            path.append(c)

    for name, body in mods:
        assert body and body[-1] == "end", (name, body[-3:])
        body = body[:-1]
        if body and body[0] == RESET:
            body = body[1:]
        # parse: namespace transitions at module top level
        items, stack, p = [], [], []
        for l in body:
            m = re.match(r"^namespace (\S+)$", l)
            if m and all(k == "ns" for k, _ in stack):
                parts = m.group(1).split(".")
                stack.append(("ns", parts)); p = p + parts
                items.append(("goto", list(p)))
                continue
            if re.match(r"^(section|noncomputable section)\b", l):
                stack.append(("sec", l)); items.append(("line", l, list(p))); continue
            if re.match(r"^end\b", l):
                k, parts = stack.pop()
                if k == "ns":
                    p = p[:len(p) - len(parts)]
                    items.append(("goto", list(p)))
                else:
                    items.append(("line", l, list(p)))
                continue
            items.append(("line", l, list(p)))
        assert not stack, (name, stack)
        ctx = any(it[0] == "line" and CTX.match(it[1]) for it in items)
        paths = [it[1] for it in items if it[0] == "goto"] + [it[2] for it in items if it[0] == "line"]
        nonempty = [it[2] for it in items if it[0] == "line" and not CTX.match(it[1])]
        base = nonempty[0] if nonempty else []
        for q in nonempty:
            k = 0
            while k < len(base) and k < len(q) and base[k] == q[k]:
                k += 1
            base = base[:k]
        need_reset = resets is None or name in resets
        if ctx or need_reset:
            goto(base)
        if ctx:
            res.append("section")
        if need_reset:
            res.append(RESET)
        outer = list(path)
        local = list(path)
        pending = []  # context lines seen before the module's first namespace (relocated)
        for it in items:
            if it[0] == "goto":
                continue
            _, l, q = it
            if not ctx:
                goto(q)
                res.append(l)
                continue
            tgt = q if len(q) >= len(outer) and q[:len(outer)] == outer else None
            if tgt is None:
                # context written outside the module's namespaces: keep it at the base level
                assert CTX.match(l), (name, l, q, outer)
                res.append(l)
                continue
            if True:
                # inside the module section: move relative to `outer`
                k = 0
                while k < len(local) and k < len(q) and local[k] == q[k]:
                    k += 1
                while len(local) > max(k, len(outer)):
                    res.append(f"end {local.pop()}")
                for c in q[len(local):]:
                    res.append(f"namespace {c}"); local.append(c)
            res.append(l)
        if ctx:
            while len(local) > len(outer):
                res.append(f"end {local.pop()}")
            res.append("end")
    goto([])
    return res

lines = open(path, encoding="utf-8").read().split("\n")
HOIST = ("@[expose] public section", "noncomputable section")
out, stack, depth, keep_block = [], [], 0, False
header_done = False
saw_mathlib = False
for i, l in enumerate(lines):
    s = l.strip()
    if depth > 0:  # inside a block comment
        depth += len(re.findall(r"/-", l)) - len(re.findall(r"-/", l))
        if keep_block:
            out.append(l)
        continue
    if s.startswith("/-"):
        d = len(re.findall(r"/-", l)) - len(re.findall(r"-/", l))
        keep_block = s.startswith("/--") or (not header_done and s == "/-")
        if keep_block:
            out.append(l)
        depth = d
        continue
    if s.startswith("-- source module: "):
        out.append(s)
        continue
    if not s or s.startswith("--"):
        continue
    if l.startswith("public import Mathlib"):
        if not saw_mathlib:
            out.append("public import Mathlib")
            saw_mathlib = True
        continue
    if l.startswith("module"):
        header_done = True
    if l == "meta import Lean.Meta.Tactic.AuxLemma":
        out.append(l)
        out.extend(HOIST)
        continue
    if not l[:1].isspace():
        if l in HOIST:
            stack.append(None)
            continue
        m = re.match(r"^(?:noncomputable )?(?:section|namespace)\b(.*)$", l)
        if m:
            stack.append(l)
        elif re.match(r"^end\b", l):
            top = stack.pop()
            if top is None:
                continue
    out.append(l)
assert not stack, stack
out = drop_aux_docs(out)
out = hoist_opens(out)
out = flatten(out)
out.append("end")
out.append("end")
open(path, "w", encoding="utf-8").write("\n".join(out) + "\n")

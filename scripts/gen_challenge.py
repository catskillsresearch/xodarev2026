#!/usr/bin/env python3
"""Generate SignatureVolatilityComparator/Challenge.lean from the repo sources.

Input: a TSV closure (kind, name, parent, modIdx, module, startLine, endLine) produced by
scripts/ComparatorClosure.lean. Needed source declarations are copied verbatim; compared
theorems (kind `thm`) get their proof replaced by `sorry`. Context commands (namespace, section,
open, variable, ...) of each source file are kept so copied declarations elaborate identically.
"""
import re, sys, collections, json

closure, out_path, json_path = sys.argv[1], sys.argv[2], sys.argv[3]
rows = [l.rstrip("\n").split("\t") for l in open(closure) if l.count("\t") == 6]
need = {}  # module -> {startLine: kind}
ranges = {}
modidx = {}
thm_names = []
for kind, name, parent, idx, mod, sl, el in rows:
    if kind == "aux":
        k = None
    else:
        k = kind
    d = need.setdefault(mod, {})
    sl = int(sl); el = int(el)
    ranges.setdefault(mod, {})[sl] = el
    if k is not None or sl not in d:
        if k is not None or sl not in d:
            d[sl] = k if k is not None else d.get(sl, "copy")
    if d.get(sl) is None:
        d[sl] = "copy"
    modidx[mod] = int(idx)
    if kind == "thm":
        thm_names.append(name)

INSTANCE_SKIP = ["finiteDimensional_span_coordSet", "finiteDimensional_sigSpan"]  # substrings identifying instances whose proofs need non-copied lemmas
CTX = re.compile(r"^(open |namespace |section|end\b|variable|universe|set_option |noncomputable section|"
                 r"@\[expose\] public section|public section|notation|infix|infixl|infixr|prefix|postfix|"
                 r"local notation|scoped notation|local infix|scoped infix|include |omit |macro|syntax)")
DROP = re.compile(r"^(module\b|public import|import|example|#|attribute|/-!|/-[^-]|--)")

def chunks(lines):
    """Split into top-level commands: list of (startIdx, endIdx exclusive)."""
    res = []
    depth = 0
    start = None
    for i, line in enumerate(lines):
        at_cmd = depth == 0 and line and not line[0].isspace() and line.strip() != ""
        if at_cmd and not line.startswith("-/"):
            if start is not None:
                res.append((start, i))
            start = i
        # update block comment depth
        j = 0
        while j < len(line):
            if line.startswith("--", j) and depth == 0:
                break
            if line.startswith("/-", j):
                depth += 1; j += 2; continue
            if line.startswith("-/", j):
                depth -= 1; j += 2; continue
            j += 1
    if start is not None:
        res.append((start, len(lines)))
    # merge doc comments and `... in` prefixes with following chunk
    merged = []
    i = 0
    while i < len(res):
        s, e = res[i]
        txt = "".join(lines[s:e]).strip()
        while i + 1 < len(res) and (txt.startswith("/--") and txt.endswith("-/") and txt.count("-/") == 1
                                     or re.match(r"^(/--.*?-/\s*)?(@\[[^\]]*\]\s*)+$", txt, flags=re.S)
                                     or re.match(r"^(open|omit|include|set_option)\b.*\bin$", txt)):
            i += 1
            e = res[i][1]
            txt = "".join(lines[s:e]).strip()
        merged.append((s, e))
        i += 1
    return merged

def strip_proof(text):
    """Replace a theorem's proof by `sorry`."""
    depth = 0
    i = 0
    n = len(text)
    opens, closes = "([{⟨", ")]}⟩"
    in_comment = 0
    while i < n:
        c = text[i]
        if text.startswith("/-", i): in_comment += 1; i += 2; continue
        if text.startswith("-/", i): in_comment -= 1; i += 2; continue
        if in_comment: i += 1; continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n": i += 1
            continue
        if c in opens: depth += 1
        elif c in closes: depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            line_start = text.rfind("\n", 0, i) + 1
            before = text[line_start:i]
            if not re.search(r"\b(let|have)\s", before):
                return text[:i] + ":= by\n  sorry\n"
        elif depth == 0 and c == "\n" and re.match(r"\n\s+\| ", text[i:]):
            return text[:i] + " := by\n  sorry\n"
        i += 1
    raise ValueError("no proof found in: " + text[:200])

ext_imports = []
blocks = []
for mod in sorted(need, key=lambda m: modidx[m]):
    path = mod.replace(".", "/") + ".lean"
    lines = open(path).read().splitlines(keepends=True)
    for l in lines:
        m = re.match(r"^public import (\S+)", l) or re.match(r"^import (\S+)", l)
        if m and not m.group(1).startswith("SignatureVolatility") and m.group(1) not in ext_imports:
            ext_imports.append(m.group(1))
    wanted = need[mod]
    out = [f"\n/-! ## from `{mod}` -/\n"]
    stack = []  # entries: (name, out_index_at_push, emitted_flag_list)
    emitted = [False]
    for s, e in chunks(lines):
        txt = "".join(lines[s:e])
        head = txt.lstrip()
        # strip leading doc comment for classification
        body = re.sub(r"^/--.*?-/\s*", "", head, flags=re.S)
        hits = [k for ln, k in wanted.items() if ln <= e and ranges[mod][ln] >= s + 1]
        if hits:
            k = "thm" if "thm" in hits else "copy"
            if k == "thm":
                txt = strip_proof(txt)
            out.append(txt if txt.endswith("\n") else txt + "\n")
            for st in stack: st[2][0] = True
            emitted[0] = True
            continue
        if re.match(r"^(@\[[^\]]*\]\s*)*((noncomputable|scoped|local|protected) )*instance\b", body, flags=re.S) \
                and not any(x in body for x in INSTANCE_SKIP):
            out.append(txt if txt.endswith("\n") else txt + "\n")
            continue
        if DROP.match(body):
            continue
        if CTX.match(body) and not re.match(r"^(open|omit|include|set_option)\b[^\n]*\bin\n", body):
            first = body.split("\n")[0]
            m = re.match(r"^namespace (\S+)", first)
            if m:
                stack.append([m.group(1), len(out), [False]])
            elif re.match(r"^(noncomputable section|@\[expose\] public section|public section|section)\b", first):
                mm = re.match(r"^.*section\s*(\S*)", first)
                stack.append([mm.group(1) if mm else "", len(out), [False]])
            elif re.match(r"^end\b", first):
                if stack:
                    nm, idx, fl = stack.pop()
                    if not fl[0]:
                        del out[idx:]
                        continue
            out.append(txt if txt.endswith("\n") else txt + "\n")
    while stack:
        nm = stack.pop()[0]
        out.append(f"end {nm}\n" if nm else "end\n")
    blocks.append((mod, "".join(out)))

import os, shutil
PART = "SignatureVolatilityComparator.ChallengeParts"
def imports_of(mod):
    src = open(mod.replace(".", "/") + ".lean").read()
    return re.findall(r"^(?:public )?import (\S+)", src, flags=re.M)
memo = {}
def resolve(mod):
    """(challenge parts, external imports) standing in for an import of `mod`."""
    if mod in memo: return memo[mod]
    parts, ext = [], []
    if mod in need:
        parts.append(PART + "." + mod)
    else:
        for m in imports_of(mod):
            if m.startswith("SignatureVolatility"):
                p2, e2 = resolve(m)
                parts += [x for x in p2 if x not in parts]; ext += [x for x in e2 if x not in ext]
            elif m not in ext:
                ext.append(m)
    memo[mod] = (parts, ext)
    return memo[mod]
part_dir = "SignatureVolatilityComparator/ChallengeParts"
if os.path.isdir(part_dir): shutil.rmtree(part_dir)
header = "/-\nCopyright (c) 2026 Lars Warren Ericson\nReleased under Apache-2.0 license as described in file LICENSE.\n-/\n"
for mod, text in blocks:
    imps = []
    for m in imports_of(mod):
        if m.startswith("SignatureVolatility"):
            p2, e2 = resolve(m); imps += [x for x in e2 + p2 if x not in imps]
        elif m not in imps:
            imps.append(m)
    path = part_dir + "/" + mod.replace(".", "/") + ".lean"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write(header + "module\n\n" + "".join(f"public import {m}\n" for m in imps)
        + f"\n/-! GENERATED by `scripts/gen_challenge.py` from `{mod}`: needed declarations copied verbatim,"
        + " compared theorems with proofs replaced by `sorry`. Do not edit by hand. -/\n\n"
        + "set_option warn.sorry false\n" + text)
hdr = [header, "module\n\n"] + [f"public import {PART}.{mod}\n" for mod, _ in blocks] + [
       "\n/-!\n# Palomar Challenge (statement of record)\n\n"
       "GENERATED by `scripts/gen_challenge.py`. The statement files under `ChallengeParts/` mirror the\n"
       "`SignatureVolatility/` modules one-to-one: every declaration the compared statements depend on is\n"
       "copied verbatim, and the compared theorems (`comparator.json` `theorem_names`) have their proofs\n"
       "replaced by `sorry`. Do not edit by hand; regenerate with `scripts/gen_challenge.sh`.\n"
       "See `COMPARATOR.md` for what each compared theorem says about the paper (proved, refuted,\n"
       "or counterexample) and why `theorem_B` itself is not compared.\n-/\n"]
open(out_path, "w").write("".join(hdr))
cfg = json.load(open(json_path))
cfg["theorem_names"] = thm_names
cfg["definition_names"] = []
json.dump(cfg, open(json_path, "w"), indent=2, ensure_ascii=False)
open(json_path, "a").write("\n")
print(f"wrote {out_path}: {len(blocks)} source modules, {len(thm_names)} compared theorems")

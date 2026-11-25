#!/usr/bin/env python3
"""Generate the single-file SignatureVolatilityComparator/Challenge.lean from the repo sources.

Palomar (CONTRIBUTING §2.4) allows only Lean core / Mathlib (and a few approved libraries) in the
Challenge's import closure, so every needed declaration from `SignatureVolatility/` and from the
vendored `MathFin` / `BrownianMotion` libraries is copied verbatim into one file that imports only
Mathlib modules.

Input: a TSV closure (kind, name, parent, modIdx, module, startLine, endLine) produced by
scripts/ComparatorClosure.lean.in. Needed source declarations are copied verbatim; compared
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
all_short = {r[1].split(".")[-1] for r in rows} | {r[2].split(".")[-1] for r in rows}
privates = collections.defaultdict(set)  # module -> short names of private decls to copy
for kind, name, parent, idx, mod, sl, el in rows:
    if idx == "NA":
        m = re.match(r"^_private\.(.+?)\.0\.(.+)$", parent)
        if m:
            privates[m.group(1)].add(m.group(2).split(".")[-1])
        continue
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

# Lean also caches `match_N` matchers per file (`Lean.Meta.Match.mkMatcherAuxDefinition`, key
# includes the `bootstrap.genMatcherCode` option). A later def in another source module whose
# matcher has the same value would otherwise reuse this one's name in the single-file Challenge,
# while the Solution (one module each) gets its own `match_1`. Elaborating these defs with
# matcher code generation off gives them a distinct cache key; they are noncomputable, so the
# kernel declarations (type and value) are unchanged.
MATCHER_FRESH = ("itoWordIntegral_le1",)
MATCHER_FRESH_PREFIX = "set_option bootstrap.genMatcherCode false in\n"

LOCAL = ("SignatureVolatility", "MathFin", "BrownianMotion", "KolmogorovExtension4")
ROOTS = {"SignatureVolatility": ".", "MathFin": "vendor/formal-mathfin",
         "BrownianMotion": "vendor/brownian-motion"}

def is_local(m):
    return m.split(".")[0] in LOCAL

def src_path(mod):
    root = ROOTS.get(mod.split(".")[0])
    if root is None:
        raise ValueError(f"no source root for {mod}")
    return f"{root}/{mod.replace('.', '/')}.lean"

def imports_of(mod):
    try:
        src = open(src_path(mod)).read()
    except (OSError, ValueError):
        return []
    return re.findall(r"^(?:public )?import (\S+)", src, flags=re.M)

# Mathlib-level imports: union over the local import closure of every copied module, so the
# Challenge sees the same instances and notation as the sources.
ext_imports, seen_mods = [], set()
stack_m = list(need)
while stack_m:
    m = stack_m.pop()
    if m in seen_mods: continue
    seen_mods.add(m)
    for i in imports_of(m):
        if is_local(i): stack_m.append(i)
        elif i not in ext_imports: ext_imports.append(i)

blocks = []
for mod in sorted(need, key=lambda m: modidx[m]):
    lines = open(src_path(mod)).read().splitlines(keepends=True)
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
        if not hits and any(re.search(rf"\bprivate\s+(noncomputable\s+)?(def|abbrev|theorem|lemma)\s+{re.escape(x)}\b", body)
                            for x in privates.get(mod, ())):
            hits = ["copy"]
        if re.match(r"^end\b", body):
            hits = []  # a declaration range may end on the closing `end` line
        if hits:
            is_thm_cmd = re.match(r"^(@\[[^\]]*\]\s*)*((private|protected|nonrec) )*(theorem|lemma)\b",
                                  body, flags=re.S)
            k = "thm" if "thm" in hits and is_thm_cmd else "copy"
            if k == "thm":
                txt = strip_proof(txt)
            if any(re.search(rf"\bdef\s+{re.escape(x)}\b", body) for x in MATCHER_FRESH):
                txt = MATCHER_FRESH_PREFIX + txt
            out.append(txt if txt.endswith("\n") else txt + "\n")
            for st in stack: st[2][0] = True
            emitted[0] = True
            continue
        if re.match(r"^(@\[[^\]]*\]\s*)*((noncomputable|scoped|local|protected) )*instance\b", body, flags=re.S) \
                and not any(x in body for x in INSTANCE_SKIP) and (mod.startswith("SignatureVolatility") or re.search(r"\b(CoeFun|CoeOut|CoeSort|Coe|FunLike|DFunLike)\b", body.split(":=")[0].split(" where")[0])):
            out.append(txt if txt.endswith("\n") else txt + "\n")
            continue
        ma = re.match(r"^attribute\s*\[[^\]]*\]\s*(.+)$", body.strip(), flags=re.S)
        if ma and all(x.split(".")[-1] in all_short for x in ma.group(1).split()):
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

RESET = "run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}"
AUXDOC = ("\n/-! Lean caches auxiliary `_proof_N` lemmas per file (`Lean.Meta.mkAuxLemma`, cache not stored in\n"
          ".olean files). In the Solution each source module starts with an empty cache; here all modules\n"
          "share one file, so each section below first empties that cache. This adds no declarations and\n"
          "only makes auxiliary proof names match the Solution exactly, as Comparator compares bodies. -/\n")
header = "/-\nCopyright (c) 2026 Lars Warren Ericson\nReleased under Apache-2.0 license as described in file LICENSE.\n-/\n"
doc = ("\n/-!\n# Palomar Challenge (statement of record)\n\n"
       "GENERATED by `scripts/gen_challenge.py` (run `scripts/gen_challenge.sh`); do not edit by hand.\n"
       "Imports only Mathlib. Every declaration the compared statements depend on is copied verbatim\n"
       "from `SignatureVolatility/` and from the vendored `MathFin` / `BrownianMotion` libraries, each\n"
       "source module in its own section; the compared theorems (`comparator.json` `theorem_names`)\n"
       "have their proofs replaced by `sorry`. See `COMPARATOR.md` for what each compared theorem says\n"
       "about the paper (proved, refuted, or counterexample). No open problems remain; the\n"
       "refutations are explained in `Writeup/narratives/`.\n-/\n\n"
       "set_option warn.sorry false\n")
text = (header + "module\n\n" + "".join(f"public import {m}\n" for m in ext_imports)
        + "meta import Lean.Meta.Tactic.AuxLemma\n" + doc + AUXDOC)
for mod, t in blocks:
    text += f"\nsection\n-- source module: {mod}\n{RESET}\n{t}\nend\n"
open(out_path, "w").write(text)
import os, shutil
if os.path.isdir("SignatureVolatilityComparator/ChallengeParts"):
    shutil.rmtree("SignatureVolatilityComparator/ChallengeParts")
cfg = json.load(open(json_path))
cfg["theorem_names"] = thm_names
cfg["definition_names"] = []
json.dump(cfg, open(json_path, "w"), indent=2, ensure_ascii=False)
open(json_path, "a").write("\n")
print(f"wrote {out_path}: {len(blocks)} source modules, {len(thm_names)} compared theorems, "
      f"{len(ext_imports)} Mathlib imports")

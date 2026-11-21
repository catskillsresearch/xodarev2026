#!/usr/bin/env python3
"""Split SignatureVolatility.lean into per-decl modules with namespace elision."""
from __future__ import annotations

import json
import re
from pathlib import Path
from collections import defaultdict

ROOT = Path("/home/catskills/Desktop/xodarev2026")
SRC = ROOT / "SignatureVolatility.lean"
OUT = ROOT / "SignatureVolatility"

PRELIM = {
    "finset_sum_mul_sq_le", "abs_finset_sum_mul_le_sqrt", "sqrt_sum_add_sq_le",
    "sqrt_sum_finset_sum_sq_le", "sum_sq_le_sq_sum", "cauchy_range_sum_le",
    "abs_tsum_le_of_summable_abs", "gronwall_zero_of_continuousOn",
}

STANDALONE_THEOREMS = {
    "banach_algebra_concat_bound", "weighted_truncation_estimates",
    "tail_norm2wInv_le_ratio_mul_normW", "dualPairing_le_normWDual_mul_normW",
    "remark_2_19_black_scholes_riccati", "lemma_3_2_signature_in_Tw",
    "corollary_3_6_sigma_well_defined", "theorem_A", "proposition_3_11_sharpness_of_H1",
    "nflvr_of_martingale_measure", "theorem_B", "theorem_C", "lemma_6_1_gram_pos_def",
    "proposition_6_5_normal_equations", "theorem_D", "section_7_1_black_scholes_completeness",
    "chen_identity", "shuffle_identity", "signature_filtration_eq_brownian_filtration",
}

# Structure fields -> stay with structure (file ExtTensorAlgebra.lean etc.)
STRUCTURE_FILES = {
    "ExtTensorAlgebra": "ExtTensorAlgebra/ExtTensorAlgebra",
    "IndexedFiltration": "IndexedFiltration",
    "ProlongedBrownianSetup": "ProlongedBrownianSetup",
    "Weight": "Weight",
    "HypH1": "HypH1",
    "HypH2": "HypH2",
    "HypH3": "HypH3",
    "SignatureVolatilityModel": "SignatureVolatilityModel",
    "ItoCalculusKit": "ItoCalculusKit",
    "SignaturePriceSolution": "SignaturePriceSolution",
    "IsSpecialSemimartingale": "IsSpecialSemimartingale",
    "SignatureRiccatiKit": "SignatureRiccatiKit",
    "PriceFiltrationSignatureSpace": "PriceFiltrationSignatureSpace",
    "GKWDecompositionSetup": "GKWDecompositionSetup",
    "ClassicalRiccatiSolution": "ClassicalRiccatiSolution",
}


def to_pascal(ident: str) -> str:
    if "_" in ident:
        return "".join(p[:1].upper() + p[1:] for p in ident.split("_"))
    out = []
    cur = ""
    for ch in ident:
        if ch.isupper() and cur:
            out.append(cur[:1].upper() + cur[1:])
            cur = ch
        else:
            cur += ch
    if cur:
        out.append(cur[:1].upper() + cur[1:])
    return "".join(out)


def decl_name_from_line(line: str) -> str | None:
    m = re.match(
        r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s+(\S+)",
        line.strip(),
    )
    return m.group(2) if m else None


def parse_decls(text: str) -> list[dict]:
    lines = text.splitlines()
    i = 0
    while i < len(lines) and "namespace SignatureVolatility" not in lines[i]:
        i += 1
    i += 1

    ns_stack: list[str] = []
    decls: list[dict] = []
    pending_docs: list[str] = []

    def at_decl_start(idx: int) -> bool:
        s = lines[idx].strip()
        if s.startswith("namespace ") or s.startswith("end "):
            return True
        if s.startswith("/-! ##"):
            return True
        return bool(re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl|@[a-z])", s))

    while i < len(lines):
        s = lines[i].strip()
        if s == "end SignatureVolatility":
            break
        if s.startswith("namespace "):
            ns_stack.append(s.replace("namespace ", "").strip())
            i += 1
            continue
        if s.startswith("end "):
            end = s.replace("end ", "").strip()
            if ns_stack and ns_stack[-1] == end:
                ns_stack.pop()
            i += 1
            continue
        if s.startswith("/-!"):
            pending_docs.append(lines[i])
            i += 1
            while i < len(lines) and not lines[i].strip().endswith("-/"):
                pending_docs.append(lines[i])
                i += 1
            if i < len(lines):
                pending_docs.append(lines[i])
                i += 1
            continue

        if re.match(r"^@[a-zA-Z]", s) or re.match(r"^/--", s):
            block = []
            while i < len(lines):
                block.append(lines[i])
                if i + 1 >= len(lines):
                    i += 1
                    break
                nxt = lines[i + 1].strip()
                if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", lines[i].strip()):
                    if i > 0 and not block[-1].strip().endswith("-/"):
                        pass
                if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", block[0].strip()) is None:
                    if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", nxt):
                        i += 1
                        break
                else:
                    if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl|namespace |end |/-!)", nxt) and not nxt.startswith("@"):
                        if not (nxt.startswith("/-!") and len(block) == 1):
                            break
                i += 1
            # Unwrap: find actual decl line
            decl_line = next((l for l in block if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", l.strip())), None)
            if not decl_line:
                i += 1
                continue
            kind = decl_line.strip().split()[0]
            name = decl_name_from_line(decl_line.strip())
            if kind == "infixl":
                name = "_infix_concat"
            decls.append({
                "kind": kind,
                "name": name,
                "ns": list(ns_stack),
                "docs": list(pending_docs),
                "text": "\n".join(block),
            })
            pending_docs = []
            continue

        if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", s):
            block = [lines[i]]
            i += 1
            while i < len(lines):
                nxt = lines[i].strip()
                if nxt.startswith("namespace ") or nxt.startswith("end "):
                    break
                if nxt.startswith("/-! ##"):
                    break
                if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", nxt):
                    break
                block.append(lines[i])
                i += 1
            kind = s.split()[0]
            name = decl_name_from_line(s)
            if kind == "infixl":
                name = "_infix_concat"
            decls.append({
                "kind": kind,
                "name": name,
                "ns": list(ns_stack),
                "docs": list(pending_docs),
                "text": "\n".join(block),
            })
            pending_docs = []
            continue
        i += 1
    return decls


def file_key(defn: dict) -> str:
    kind, name, ns = defn["kind"], defn["name"], defn["ns"]
    if kind == "lemma" and name in PRELIM:
        return "Preliminaries"
    if kind in ("theorem", "lemma") and name in STANDALONE_THEOREMS:
        return to_pascal(name)
    if kind == "structure" and name in STRUCTURE_FILES:
        return STRUCTURE_FILES[name]
    if name == "ExtTensorAlgebra" and kind == "structure":
        return "ExtTensorAlgebra/ExtTensorAlgebra"
    if kind == "instance":
        return None  # merge
    if name == "_infix_concat":
        return "ExtTensorAlgebra/Concat"
    base = to_pascal(name) if name else "Unknown"
    if ns:
        return "/".join(to_pascal(x) for x in ns) + "/" + base
    return base


def find_parent_lemma(name: str, defined: set[str]) -> tuple[str, str] | None:
    for d in sorted(defined, key=len, reverse=True):
        if name.startswith(d + "_"):
            return d, name[len(d) + 1 :]
        if name.endswith("_" + d):
            return d, name[: -(len(d) + 1)]
    return None


def parent_file_path(parent: str, parent_decl: dict | None) -> str:
    if parent_decl:
        return file_key(parent_decl)
    if parent in STRUCTURE_FILES:
        return STRUCTURE_FILES[parent]
    # guess
    return to_pascal(parent)


def rewrite_lemma_name(text: str, old: str, new: str) -> str:
    return re.sub(rf"\b(lemma|theorem)\s+{re.escape(old)}\b", rf"\1 {new}", text, count=1)


def wrap_module(rel_key: str, chunks: list[str], ns_stack: list[str]) -> str:
    imports = ["import SignatureVolatility.Basic"]
    parts = rel_key.split("/")
    mod_path = ".".join(parts)
    lines = imports + ["", "namespace SignatureVolatility", ""]
    open_ns = []
    for n in ns_stack:
        if n not in open_ns:
            lines.append(f"namespace {n}")
            open_ns.append(n)
    for ch in chunks:
        s = ch["text"] if isinstance(ch, dict) else ch
        lines.append(s.rstrip())
        lines.append("")
    for n in reversed(open_ns):
        lines.append(f"end {n}")
    lines.append("end SignatureVolatility")
    return "\n".join(lines) + "\n"


def main():
    text = SRC.read_text()
    decls = parse_decls(text)
    print(f"Parsed {len(decls)} declarations")

    primaries = [d for d in decls if d["kind"] in ("def", "abbrev", "structure", "theorem") and d["name"]]
    defined = {d["name"] for d in primaries}
    decl_by_name = {d["name"]: d for d in primaries if d["name"]}

    groups: dict[str, list] = defaultdict(list)
    elision: dict[str, str] = {}

    # Attach instances/infix to structure
    pending_instance: list[dict] = []
    for d in decls:
        if d["kind"] == "instance" or d["name"] == "_infix_concat":
            pending_instance.append(d)
            continue
        if d["kind"] in ("def", "abbrev", "structure", "theorem"):
            key = file_key(d)
            if pending_instance and d["name"] == "ExtTensorAlgebra":
                groups[key].extend(x["text"] for x in pending_instance)
                pending_instance = []
            elif pending_instance and d["name"] == "Weight":
                groups[key].extend(x["text"] for x in pending_instance)
                pending_instance = []
            if d["docs"]:
                groups[key].append("\n".join(d["docs"]))
            groups[key].append(d["text"])
            continue
        if d["kind"] == "lemma":
            name = d["name"]
            if name in PRELIM:
                if d["docs"]:
                    groups["Preliminaries"].append("\n".join(d["docs"]))
                groups["Preliminaries"].append(d["text"])
                continue
            if name in STANDALONE_THEOREMS:
                key = to_pascal(name)
                if d["docs"]:
                    groups[key].append("\n".join(d["docs"]))
                groups[key].append(d["text"])
                continue
            par = find_parent_lemma(name, defined)
            if par:
                parent, suffix = par
                key = parent_file_path(parent, decl_by_name.get(parent))
                qual_ns = d["ns"]
                qual = ".".join(qual_ns + [parent, suffix]) if qual_ns else f"{parent}.{suffix}"
                elision[name] = qual
                txt = rewrite_lemma_name(d["text"], name, suffix)
                ns_wrapped = f"namespace {parent}\n\n{txt}\n\nend {parent}"
                if d["docs"]:
                    groups[key].append("\n".join(d["docs"]))
                groups[key].append(ns_wrapped)
            else:
                # orphan lemma -> Preliminaries or own file
                key = to_pascal(name) if len(d["text"]) > 200 else "Preliminaries"
                if d["docs"]:
                    groups[key].append("\n".join(d["docs"]))
                groups[key].append(d["text"])
            continue

    if pending_instance:
        groups["ExtTensorAlgebra/ExtTensorAlgebra"].extend(
            [x["text"] if isinstance(x, dict) else x for x in pending_instance]
        )

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "Basic.lean").write_text(
        '''import Mathlib

/-!
# On the Structural Foundations of Signature Volatility Models
Formalization of arXiv:2605.17142v1 by Akmal Xodarev.

No `axiom`s and no `sorry`s are used anywhere in this development.
-/

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

end SignatureVolatility
'''
    )

    modules: list[str] = []
    ns_for_path: dict[str, list[str]] = {}

    for rel, chunks in sorted(groups.items()):
        dest = OUT / f"{rel}.lean"
        dest.parent.mkdir(parents=True, exist_ok=True)
        # infer ns from first decl in group
        sample = next((d for d in decls if file_key(d) == rel or (d.get("name") and to_pascal(d["name"]) == rel.split("/")[-1])), None)
        ns = sample["ns"] if sample else (rel.split("/")[:-1] if "/" in rel else [])
        # dedupe consecutive namespace blocks in chunks - simplify: don't wrap outer ns if path includes it
        outer = [to_pascal(x) for x in ns] if ns else []
        path_parts = rel.split("/")
        if outer and path_parts[: len(ns)] == [to_pascal(x) for x in ns]:
            wrap_ns = []
        else:
            wrap_ns = ns
        content = wrap_module(rel, chunks, wrap_ns)
        dest.write_text(content)
        modules.append("SignatureVolatility." + rel.replace("/", "."))

    # Global rename in all files
    for old, new in sorted(elision.items(), key=lambda x: -len(x[0])):
        for f in OUT.rglob("*.lean"):
            t = f.read_text()
            t2 = re.sub(rf"\b{re.escape(old)}\b", new, t)
            # Also ExtTensorAlgebra-prefixed calls
            t2 = re.sub(rf"\bExtTensorAlgebra\.{re.escape(old)}\b", new, t2)
            f.write_text(t2)

    # barrel
    barrel = '''/-!
# Signature Volatility (root module)

Aggregates all submodules. See `SignatureVolatility.Basic` for shared imports and notation.
-/

'''
    for m in sorted(modules):
        barrel += f"import {m}\n"
    barrel += "\nnamespace SignatureVolatility\n\nend SignatureVolatility\n"
    SRC.write_text(barrel)

  # lakefile
    lake = ROOT / "lakefile.toml"
    lt = lake.read_text()
    if "globs" not in lt:
        lt = lt.replace(
            'roots = ["SignatureVolatility"]',
            'globs = ["SignatureVolatility", "SignatureVolatility.+"]',
        )
        lake.write_text(lt)

    (ROOT / "scripts" / "elision_map.json").write_text(json.dumps(elision, indent=2))
    (ROOT / "scripts" / "module_paths.json").write_text(json.dumps(sorted(modules), indent=2))
    print(f"Wrote {len(modules)} modules, {len(elision)} renames")


if __name__ == "__main__":
    main()
#!/usr/bin/env python3
"""Robust split of SignatureVolatility.lean — one primary decl per file, lemmas nested."""
from __future__ import annotations

import json
import re
from pathlib import Path
from collections import defaultdict

ROOT = Path("/home/catskills/Desktop/xodarev2026")
SRC = ROOT / "SignatureVolatility.monolith.backup.lean"
OUT = ROOT / "SignatureVolatility"

PRELIM = {
    "finset_sum_mul_sq_le", "abs_finset_sum_mul_le_sqrt", "sqrt_sum_add_sq_le",
    "sqrt_sum_finset_sum_sq_le", "sum_sq_le_sq_sum", "cauchy_range_sum_le",
    "abs_tsum_le_of_summable_abs", "gronwall_zero_of_continuousOn",
}

STANDALONE = {
    "banach_algebra_concat_bound", "weighted_truncation_estimates",
    "tail_norm2wInv_le_ratio_mul_normW", "dualPairing_le_normWDual_mul_normW",
    "remark_2_19_black_scholes_riccati", "lemma_3_2_signature_in_Tw",
    "corollary_3_6_sigma_well_defined", "theorem_A", "proposition_3_11_sharpness_of_H1",
    "nflvr_of_martingale_measure", "theorem_B", "theorem_C", "lemma_6_1_gram_pos_def",
    "proposition_6_5_normal_equations", "theorem_D", "section_7_1_black_scholes_completeness",
    "chen_identity", "shuffle_identity", "signature_filtration_eq_brownian_filtration",
}

STRUCTURE_PATH = {
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

DECL_HEAD = re.compile(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s+(\S+)")


def pascal(s: str) -> str:
    if "_" in s:
        return "".join(w[:1].upper() + w[1:] for w in s.split("_"))
    return s[:1].upper() + s[1:]


def is_top_decl_line(line: str) -> bool:
    return bool(DECL_HEAD.match(line.strip())) and not line.startswith(" ")


def parse_decls(text: str) -> list[dict]:
    lines = text.splitlines()
    start = next(i for i, l in enumerate(lines) if l.strip() == "namespace SignatureVolatility") + 1
    end = next(i for i in range(start, len(lines)) if lines[i].strip() == "end SignatureVolatility")
    body = "\n".join(lines[start:end])

    raw = re.split(
        r"(?=^(?:/--|@[a-zA-Z]+|(?:abbrev|structure|def|lemma|theorem|instance|infixl)\s))",
        body,
        flags=re.MULTILINE,
    )
    ns: list[str] = []
    decls: list[dict] = []
    for chunk in raw:
        chunk = chunk.strip("\n")
        if not chunk.strip():
            continue
        for line in chunk.splitlines():
            st = line.strip()
            if st.startswith("namespace "):
                ns.append(st.split()[1])
            elif st.startswith("end "):
                en = st.split()[1]
                if ns and ns[-1] == en:
                    ns.pop()
        if chunk.strip().startswith("namespace ") or chunk.strip().startswith("end "):
            if not DECL_HEAD.search(chunk):
                continue
        m = None
        for line in chunk.splitlines():
            if is_top_decl_line(line):
                m = DECL_HEAD.match(line.strip())
                break
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if kind == "infixl":
            name = "infix_concat"
        # namespace at time of decl (exclude ns lines from chunk text)
        clean_lines = [
            l for l in chunk.splitlines()
            if not l.strip().startswith("namespace ") and not l.strip().startswith("end ")
        ]
        decls.append({"kind": kind, "name": name, "ns": list(ns), "text": "\n".join(clean_lines)})
    return decls


def lemma_parent(name: str, defined: set[str]) -> tuple[str, str] | None:
    if name == "mem_wordsOfLength":
        return "wordsOfLength", "mem"
    if name.startswith("sum_wordsOfLength_"):
        return "wordsOfLength", name[len("sum_wordsOfLength_") :]
    # Prefer suffix match (e.g. `levelNorm_div_le_normWDual` → `normWDual.levelNorm_div_le`)
    for d in sorted(defined, key=len, reverse=True):
        if name.endswith("_" + d):
            pref = name[: -(len(d) + 1)]
            if pref in defined:
                return pref, d
            if pref:
                return d, pref
    for d in sorted(defined, key=len, reverse=True):
        if name.startswith(d + "_"):
            return d, name[len(d) + 1 :]
    return None


def file_path(d: dict) -> str:
    k, name, ns = d["kind"], d["name"], d["ns"]
    if k == "lemma" and name in PRELIM:
        return "Preliminaries"
    if name in STANDALONE and k in ("lemma", "theorem"):
        return pascal(name)
    if k == "structure" and name in STRUCTURE_PATH:
        return STRUCTURE_PATH[name]
    if name == "infix_concat":
        return "ExtTensorAlgebra/Concat"
    b = pascal(name)
    if ns:
        return "/".join(pascal(x) for x in ns) + "/" + b
    return b


def main():
    text = SRC.read_text()
    decls = parse_decls(text)
    print(f"Parsed {len(decls)} decls")

    primary_names = {d["name"] for d in decls if d["kind"] in ("def", "abbrev", "structure", "theorem")}
    prim_by_name = {d["name"]: d for d in decls if d["kind"] in ("def", "abbrev", "structure", "theorem")}

    groups: dict[str, dict] = defaultdict(lambda: {"ns": [], "texts": [], "nested": defaultdict(list)})

    elision: dict[str, str] = {}
    last_structure: str | None = None
    last_structure_path: str | None = None

    for d in decls:
        k, name = d["kind"], d["name"]
        if k == "instance":
            target = last_structure_path or (
                "ExtTensorAlgebra/ExtTensorAlgebra" if last_structure == "ExtTensorAlgebra" else
                "Weight" if last_structure == "Weight" else None
            )
            if target:
                groups[target]["texts"].append(d["text"])
            continue
        if k in ("def", "abbrev", "structure", "theorem"):
            path = file_path(d)
            g = groups[path]
            g["ns"] = d["ns"]
            g["texts"].append(d["text"])
            if k == "structure":
                last_structure = name
                last_structure_path = path
            continue
        if k == "lemma":
            if name in PRELIM:
                groups["Preliminaries"]["texts"].append(d["text"])
                continue
            if name in STANDALONE:
                groups[pascal(name)]["texts"].append(d["text"])
                groups[pascal(name)]["ns"] = d["ns"]
                continue
            HUB_NS = {"Weight", "HypH2", "PriceFiltrationSignatureSpace", "ProlongedBrownianSetup",
                      "SignatureVolatilityModel"}
            if d["ns"]:
                hub = d["ns"][-1]
                if hub in HUB_NS and hub in STRUCTURE_PATH:
                    groups[STRUCTURE_PATH[hub]]["texts"].append(d["text"])
                    groups[STRUCTURE_PATH[hub]]["ns"] = d["ns"]
                    continue
            par = lemma_parent(name, primary_names)
            if par:
                parent, suffix = par
                pdecl = prim_by_name.get(parent)
                if pdecl and pdecl["ns"] != d["ns"] and d["ns"]:
                    path = "/".join(pascal(x) for x in d["ns"])
                    groups[path]["texts"].append(d["text"])
                    groups[path]["ns"] = d["ns"]
                    continue
                path = file_path(pdecl) if pdecl else pascal(parent)
                qual = ".".join(d["ns"] + [parent, suffix]) if d["ns"] else f"{parent}.{suffix}"
                elision[name] = qual
                txt = re.sub(rf"\b(lemma|theorem)\s+{re.escape(name)}\b", rf"\1 {suffix}", d["text"], count=1)
                groups[path]["nested"][parent].append(txt)
                groups[path]["ns"] = d["ns"] or groups[path]["ns"]
            else:
                path = pascal(name)
                groups[path]["texts"].append(d["text"])
                groups[path]["ns"] = d["ns"]
            continue
        if k == "infixl":
            target = last_structure_path or "ExtTensorAlgebra/Concat"
            groups[target]["texts"].append(d["text"])

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
    for path, g in sorted(groups.items()):
        dest = OUT / f"{path}.lean"
        dest.parent.mkdir(parents=True, exist_ok=True)
        lines = ["import SignatureVolatility.Basic", "", "namespace SignatureVolatility", ""]
        for n in g["ns"]:
            lines += [f"namespace {n}", ""]
        for t in g["texts"]:
            lines += [t, ""]
        for parent, lems in sorted(g["nested"].items()):
            lines += [f"namespace {parent}", ""]
            lines += [x + "\n" for x in lems]
            lines += [f"end {parent}", ""]
        for n in reversed(g["ns"]):
            lines += [f"end {n}", ""]
        lines += ["end SignatureVolatility", ""]
        dest.write_text("\n".join(lines))
        modules.append("SignatureVolatility." + path.replace("/", "."))

    def repl(old: str, new: str, t: str) -> str:
        pat = rf"(?<![\.\w]){re.escape(old)}\b"
        return re.sub(pat, new, t)

    for old, new in sorted(elision.items(), key=lambda x: -len(x[0])):
        for f in OUT.rglob("*.lean"):
            t = repl(old, new, f.read_text())
            f.write_text(t)
    # common renames not caught by prefix rules

    barrel = ""
    for m in sorted(modules):
        barrel += f"import {m}\n"
    barrel += """
/-!
# Signature Volatility (root module)

Aggregates all submodules. See `SignatureVolatility.Basic` for shared imports and notation.
-/

namespace SignatureVolatility

end SignatureVolatility
"""
    # regenerate barrel from disk (covers all modules)
    all_mods = []
    for f in sorted(OUT.rglob("*.lean")):
        if f.name == "Basic.lean":
            continue
        rel = f.relative_to(OUT).with_suffix("").as_posix().replace("/", ".")
        all_mods.append(f"SignatureVolatility.{rel}")
    barrel = "".join(f"import {m}\n" for m in all_mods) + """
/-!
# Signature Volatility (root module)

Aggregates all submodules. See `SignatureVolatility.Basic` for shared imports and notation.
-/

namespace SignatureVolatility

end SignatureVolatility
"""
    (ROOT / "SignatureVolatility.lean").write_text(barrel)

    (ROOT / "scripts" / "elision_map.json").write_text(json.dumps(elision, indent=2))
    print(f"Modules: {len(modules)}, elisions: {len(elision)}")


if __name__ == "__main__":
    if OUT.exists():
        import shutil
        shutil.rmtree(OUT)
    main()
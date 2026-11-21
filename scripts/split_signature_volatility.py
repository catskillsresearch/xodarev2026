#!/usr/bin/env python3
"""Split SignatureVolatility.lean into multiple files with namespace elision."""
import re
import os
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

ROOT = Path("/home/catskills/Desktop/xodarev2026")
SRC = ROOT / "SignatureVolatility.lean"
OUT = ROOT / "SignatureVolatility"

PRELIM_LEMMAS = {
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
    "proposition_6_5_normal_equations", "theorem_D",
    "section_7_1_black_scholes_completeness",
}

# Outer namespaces that stay in split files
OUTER_NAMESPACES = {
    "ExtTensorAlgebra": "ExtTensorAlgebra",
    "ProlongedBrownianSetup": "ProlongedBrownianSetup",
    "Weight": "Weight",
    "HypH2": "HypH2",
    "SignatureVolatilityModel": "SignatureVolatilityModel",
    "PriceFiltrationSignatureSpace": "PriceFiltrationSignatureSpace",
}

DECL_START = re.compile(
    r"^(?P<attrs>(?:@[^\n]+\n)*)"
    r"(?P<kind>/--.*?--/\s*\n)?"
    r"(?P<doc>/[-!].*?\n)?"
    r"(?P<decl>(abbrev|structure|def|lemma|theorem|instance|infixl|end|namespace)\b[^\n]*)",
    re.MULTILINE | re.DOTALL,
)

def pascal_case(name: str) -> str:
    if name.startswith("theorem_") or name.startswith("lemma_") or name.startswith("proposition_"):
        parts = re.split(r"_", name)
        return "".join(p.capitalize() if i > 0 else p.capitalize() for i, p in enumerate(parts))
    # snake to PascalCase
    return "".join(w.capitalize() for w in name.split("_"))

def decl_name(line: str) -> Optional[str]:
    m = re.match(
        r"(abbrev|structure|def|lemma|theorem|instance|infixl)\s+([\w\.']+)",
        line.strip(),
    )
    if m:
        return m.group(2).split(".")[-1]
    return None

def parse_blocks(text: str):
    """Parse file into blocks: namespace markers and declarations."""
    lines = text.split("\n")
    i = 0
    # Skip header until namespace SignatureVolatility
    while i < len(lines) and not lines[i].strip().startswith("namespace SignatureVolatility"):
        i += 1
    i += 1  # skip namespace line

    blocks = []
    current_ns = []  # stack inside SignatureVolatility
    buf = []
    buf_kind = None
    buf_name = None

    def flush():
        nonlocal buf, buf_kind, buf_name
        if buf:
            blocks.append({
                "ns_stack": list(current_ns),
                "kind": buf_kind,
                "name": buf_name,
                "text": "\n".join(buf).rstrip() + "\n",
            })
        buf = []
        buf_kind = None
        buf_name = None

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        if stripped == "end SignatureVolatility":
            flush()
            break

        if stripped.startswith("namespace ") and not stripped.startswith("namespace SignatureVolatility"):
            flush()
            ns = stripped.replace("namespace ", "").strip()
            current_ns.append(ns)
            i += 1
            continue

        if stripped.startswith("end ") and stripped != "end SignatureVolatility":
            flush()
            end_ns = stripped.replace("end ", "").strip()
            if current_ns and current_ns[-1] == end_ns:
                current_ns.pop()
            i += 1
            continue

        # Section comments between decls
        if stripped.startswith("/-!") and not buf:
            # accumulate module/section doc until decl
            doc_lines = [line]
            i += 1
            while i < len(lines):
                doc_lines.append(lines[i])
                if lines[i].strip().endswith("-/"):
                    i += 1
                    break
                i += 1
            blocks.append({
                "ns_stack": list(current_ns),
                "kind": "section_doc",
                "name": None,
                "text": "\n".join(doc_lines) + "\n",
            })
            continue

        decl_match = re.match(
            r"^(@[^\n]+\n)*"
            r"(/(?:--|!)[\s\S]*?--/\s*\n)?"
            r"(abbrev|structure|def|lemma|theorem|instance|infixl)\s",
            line if not stripped.startswith("/-") else "",
        )

        # Detect start of declaration (line by line for reliability)
        is_decl = False
        kind = None
        if re.match(r"^/\[-!]", stripped):
            pass  # handled above
        elif re.match(r"^@", stripped) and buf:
            pass
        elif re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", stripped):
            is_decl = True
            kind = stripped.split()[0]
        elif re.match(r"^/@", stripped) or re.match(r"^/--", stripped):
            if not buf:
                # start doc for decl
                buf = [line]
                i += 1
                continue

        if is_decl and kind:
            flush()
            name = decl_name(stripped)
            buf = [line]
            buf_kind = kind
            buf_name = name
            i += 1
            # continue until next top-level decl at same indent (no namespace)
            while i < len(lines):
                nl = lines[i]
                ns = nl.strip()
                if ns.startswith("namespace ") or ns.startswith("end "):
                    break
                if ns.startswith("/-! ##"):
                    break
                if re.match(r"^(abbrev|structure|def|lemma|theorem|instance|infixl)\s", ns):
                    # next decl
                    break
                buf.append(nl)
                i += 1
            flush()
            continue

        if buf:
            buf.append(line)
        i += 1

    return blocks

def assign_file(block, all_defs: set[str]) -> tuple[str, Optional[str], Optional[str]]:
    """Returns (relative_path, parent_ns_for_elision, elided_suffix)."""
    kind = block["kind"]
    name = block["name"]
    ns = block["ns_stack"]

    if kind == "section_doc":
        return ("_section_docs", None, None)

    if kind == "lemma" and name in PRELIM_LEMMAS:
        return ("Preliminaries.lean", None, None)

    if kind == "theorem" and name in STANDALONE_THEOREMS:
        return (f"{pascal_case(name)}.lean", None, None)

    if kind == "lemma" and name:
        # Try namespace elision: longest matching def/abbrev/structure name
        best = None
        for d in sorted(all_defs, key=len, reverse=True):
            if name.startswith(d + "_"):
                best = (d, name[len(d) + 1:])
                break
            if name.endswith("_" + d):
                best = (d, name[: -(len(d) + 1)])
                break
        if best:
            parent, suffix = best
            parent_file = def_file_path(parent, ns, all_defs)
            return (parent_file, parent, suffix)

    if kind in ("abbrev", "structure", "def", "theorem") and name:
        if kind == "lemma":
            pass
        fp = def_file_path(name, ns, all_defs, kind)
        return (fp, None, None)

    if kind == "instance" or kind == "infixl":
        # attach to last structure in same ns - handled by merging into structure file
        return ("_instances", None, None)

    return (f"Misc/{name or 'unknown'}.lean", None, None)

def def_file_path(name: str, ns_stack: list[str], all_defs: set, kind: str = "def") -> str:
    base = pascal_case(name) + ".lean"
    if name == "ExtTensorAlgebra" and kind == "structure":
        return f"ExtTensorAlgebra/ExtTensorAlgebra.lean"
    if ns_stack:
        sub = "/".join(ns_stack)
        if name == ns_stack[-1] and kind == "structure":
            return f"{sub}/{pascal_case(name)}.lean"
        return f"{sub}/{pascal_case(name)}.lean"
    return base

def main():
    text = SRC.read_text()
    blocks = parse_blocks(text)

    all_defs = set()
    for b in blocks:
        if b["kind"] in ("def", "abbrev", "structure", "theorem") and b["name"]:
            all_defs.add(b["name"])

    # Group blocks by file
    files: dict[str, list] = {}
    elision_map: dict[str, str] = {}  # old_name -> new qualified name (within SignatureVolatility)

    for b in blocks:
        if b["kind"] == "section_doc":
            key = "_orphan_docs"
            files.setdefault(key, []).append(b)
            continue

        path, parent, suffix = assign_file(b, all_defs)

        if parent and suffix and b["name"]:
            # rewrite declaration name inside block
            old_name = b["name"]
            new_decl_name = suffix
            b["elision_parent"] = parent
            b["elision_suffix"] = suffix
            # Build qualified reference name for renames
            ns_parts = ["SignatureVolatility"] + b["ns_stack"] + [parent, new_decl_name]
            # ExtTensorAlgebra defs use ExtTensorAlgebra.levelNorm.nonneg not SignatureVolatility prefix in calls?
            # User wants call sites: ExtTensorAlgebra.levelNorm.nonneg a n
            qual = ".".join(b["ns_stack"] + [parent, new_decl_name]) if b["ns_stack"] else f"{parent}.{new_decl_name}"
            elision_map[old_name] = qual

            # Rewrite lemma/theorem header
            txt = b["text"]
            txt = re.sub(
                rf"\b(lemma|theorem)\s+{re.escape(old_name)}\b",
                rf"\1 {new_decl_name}",
                txt,
                count=1,
            )
            b["text"] = txt

        files.setdefault(path, []).append(b)

    # Merge instances/infix into ExtTensorAlgebra structure file
    if "_instances" in files:
        files.setdefault("ExtTensorAlgebra/ExtTensorAlgebra.lean", []).extend(files.pop("_instances"))

    # Attach section docs to following thematic files - dump prelim doc to Preliminaries
    if "_orphan_docs" in files:
        docs = files.pop("_orphan_docs")
        files.setdefault("Preliminaries.lean", [])
        files["Preliminaries.lean"] = docs + files["Preliminaries.lean"]

    # Generate rename map for common patterns used with namespace prefix ExtTensorAlgebra.
    for old, qual in list(elision_map.items()):
        # also map ExtTensorAlgebra.old style if in ETA
        if qual.startswith("ExtTensorAlgebra."):
            elision_map[f"ExtTensorAlgebra.{old}"] = qual

    # Additional manual elisions for lemmas in files with their def
    manual_elisions = {
        "mem_wordsOfLength": ("wordsOfLength", "mem"),
        "sum_wordsOfLength_succ": ("wordsOfLength", "sum_succ"),
        "sum_wordsOfLength_take_drop_sq": ("wordsOfLength", "sum_take_drop_sq"),
    }

    OUT.mkdir(exist_ok=True)

    # Write Basic.lean
    basic = """import Mathlib

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
"""
    (OUT / "Basic.lean").write_text(basic)

    # Collect all module paths for barrel
    module_paths = []

    def wrap_file(rel_path: str, chunks: list) -> str:
        parts = rel_path.replace(".lean", "").split("/")
        mod_suffix = ".".join(parts)

        inner_ns = []
        # detect common outer ns from path
        if len(parts) > 1:
            inner_ns = parts[:-1]

        out_lines = ["import SignatureVolatility.Basic"]
        # TODO: add imports - will fix in second pass
        out_lines.append("")
        out_lines.append("namespace SignatureVolatility")
        out_lines.append("")

        current_elision_ns = None
        for b in chunks:
            ns = b["ns_stack"]
            # open namespaces if needed
            for n in ns:
                if n not in inner_ns:
                    continue
                out_lines.append(f"namespace {n}")

            if b.get("elision_parent"):
                p = b["elision_parent"]
                if current_elision_ns != p:
                    if current_elision_ns:
                        out_lines.append(f"end {current_elision_ns}")
                    out_lines.append(f"namespace {p}")
                    current_elision_ns = p
            else:
                if current_elision_ns:
                    out_lines.append(f"end {current_elision_ns}")
                    current_elision_ns = None

            out_lines.append(b["text"].rstrip())
            out_lines.append("")

        if current_elision_ns:
            out_lines.append(f"end {current_elision_ns}")

        for n in reversed(inner_ns):
            out_lines.append(f"end {n}")

        out_lines.append("")
        out_lines.append("end SignatureVolatility")
        return "\n".join(out_lines)

    for rel_path, chunks in sorted(files.items()):
        if rel_path.startswith("_"):
            continue
        dest = OUT / rel_path
        dest.parent.mkdir(parents=True, exist_ok=True)
        content = wrap_file(rel_path, chunks)
        dest.write_text(content)
        mod = "SignatureVolatility." + rel_path.replace("/", ".").replace(".lean", "")
        module_paths.append(mod)

    # Save elision map for rename pass
    import json
    (ROOT / "scripts" / "elision_map.json").write_text(json.dumps(elision_map, indent=2))
    (ROOT / "scripts" / "module_paths.json").write_text(json.dumps(sorted(module_paths), indent=2))
    print(f"Created {len(module_paths)} modules, {len(elision_map)} elision renames")

if __name__ == "__main__":
    main()
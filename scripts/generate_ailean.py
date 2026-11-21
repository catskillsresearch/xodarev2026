#!/usr/bin/env python3
"""Extract Lean decls and (re)wire Writeup leaves to import *_ailean.txt sidecars.

Does not invent proof prose: writes a structured stub with statement/signature
and the raw Lean proof body for an agent to summarize, OR fills defs/structures
from docstrings. Use ``--fill-defs-only`` to emit English for def/abbrev/structure
and leave lemma/theorem proof sections as ``PROOF_TODO`` markers.

Usage (repo root)::

    python3 scripts/generate_ailean.py --wire
    python3 scripts/generate_ailean.py --fill-defs-only --wire
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "SignatureVolatility"
WRITEUP = ROOT / "Writeup"

IMPORT_RE = re.compile(r'@import\s+"([^"]+\.lean)"')
AILEAN_IMPORT_RE = re.compile(
    r'^@import\s+"[^"]*_ailean\.txt"\s*\{code_block=false\}\s*\n*', re.M
)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|nonrec)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|axiom|class|inductive|instance)\s+"
    r"(?P<name>[A-Za-z0-9_'.«»₀-₉]+)",
    re.MULTILINE,
)
_COMMENT_RE = re.compile(r"/-[\s\S]*?-/")
_DOC_RE = re.compile(r"/--([\s\S]*?)-/")

_KIND_LABEL = {
    "def": "Definition",
    "abbrev": "Abbreviation",
    "structure": "Structure",
    "theorem": "Theorem",
    "lemma": "Lemma",
    "instance": "Instance",
    "class": "Class",
    "inductive": "Inductive type",
    "axiom": "Axiom",
}


def comment_spans(text: str) -> list[tuple[int, int]]:
    return [(m.start(), m.end()) for m in _COMMENT_RE.finditer(text)]


def in_spans(pos: int, spans: list[tuple[int, int]]) -> bool:
    return any(a <= pos < b for a, b in spans)


def strip_block_comments(text: str) -> str:
    return _COMMENT_RE.sub(lambda m: "\n" * m.group(0).count("\n"), text)


def leaf_map() -> dict[str, Path]:
    out: dict[str, Path] = {}
    for md in WRITEUP.rglob("*.md"):
        for rel in IMPORT_RE.findall(md.read_text(encoding="utf-8")):
            target = (md.parent / rel).resolve()
            lean_rel = target.relative_to(LEAN_DIR.resolve()).as_posix()
            out[lean_rel] = md
    return out


def nearest_doc(text: str, pos: int) -> str:
    before = text[:pos].rstrip()
    if not before.endswith("-/"):
        return ""
    # Prefer /-- doc comments
    k = before.rfind("/--")
    if k >= 0 and "-/" not in before[k:-2]:
        return re.sub(r"\s+", " ", before[k + 3 : -2]).strip()
    return ""


def extract_decls(lean_text: str) -> list[dict]:
    spans = comment_spans(lean_text)
    decls: list[dict] = []
    matches = [m for m in DECL_RE.finditer(lean_text) if not in_spans(m.start(), spans)]
    for i, m in enumerate(matches):
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(lean_text)
        chunk = lean_text[start:end]
        # Split type / proof at := by / := / where
        proof = ""
        sig = chunk
        # First ``:= by`` starts the main proof; later ones are nested ``have``.
        by_m = re.search(r":=\s*by\b", chunk)
        where_m = re.search(r"\bwhere\b", chunk)
        rhs = ""
        if by_m:
            sig = chunk[: by_m.start()].rstrip()
            proof = chunk[by_m.end() :].strip()
            # Truncate at next top-level decl already handled by chunk end.
        elif where_m and m.group("kind") == "structure":
            sig = chunk[: where_m.start()].rstrip()
            proof = chunk[where_m.end() :].strip()  # fields
        else:
            # One-line ``:= expr`` (application / definitional proof).
            am = re.search(r":=", chunk)
            if am and m.group("kind") in {
                "theorem",
                "lemma",
                "def",
                "abbrev",
                "instance",
            }:
                sig = chunk[: am.start()].rstrip()
                rhs = chunk[am.end() :].strip()
                if m.group("kind") in {"theorem", "lemma"}:
                    proof = ""  # summarized from rhs
        # Clean signature: drop trailing ``end`` / namespace noise if any.
        sig = re.sub(r"\s+", " ", sig).strip()
        sig = re.sub(r"\s+end\s+\S+\s*$", "", sig).strip()
        if rhs:
            rhs = re.sub(r"\s+end\s+\S+\s*$", "", rhs).strip()
        decls.append(
            {
                "kind": m.group("kind"),
                "name": m.group("name"),
                "doc": nearest_doc(lean_text, start),
                "sig": sig[:800],
                "proof": proof,
                "rhs": rhs,
                "raw": chunk.strip(),
            }
        )
    return decls


def camel_to_spaced(name: str) -> str:
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", name)
    s = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", s)
    return s.replace("_", " ").replace(".", " ").strip()


def structure_fields(proof: str) -> list[str]:
    fields: list[str] = []
    for m in re.finditer(
        r"(?m)^(?:  )?([A-Za-zℓσ][A-Za-z0-9_']*|s₀|hs₀|hd|hT|h1|h2|h3)\s*:",
        proof or "",
    ):
        line_start = (proof or "").rfind("\n", 0, m.start()) + 1
        if m.start() - line_start <= 2:
            fields.append(m.group(1))
    return fields


def english_for_def(d: dict) -> str:
    """Fallback stub only — prefer agent-written literate math English.

    Structures: ``A *foo* has these properties:`` + bullets.
    Definitions: ``We define … as …``.
    Never emit the old ``packages the following data. Fields:`` voice.
    """
    name = d["name"]
    spoken = camel_to_spaced(name)
    if d["kind"] == "structure":
        fields = structure_fields(d.get("proof") or "")
        bullets = "\n".join(f"- `{f}`" for f in fields) if fields else "- (see Lean)"
        return (
            f"A *{spoken.lower()}* (`{name}`) has these properties:\n\n"
            f"{bullets}\n"
        )
    if d["kind"] == "abbrev" and d.get("rhs"):
        rhs = re.sub(r"\s+", " ", d["rhs"].splitlines()[0]).strip()[:160]
        return f"We write `{name}` for {rhs}.\n"
    if d.get("doc"):
        return f"We define `{name}` as follows: {d['doc'].rstrip('.')}.\n"
    if d.get("rhs"):
        rhs = re.sub(r"\s+", " ", d["rhs"].splitlines()[0]).strip()[:200]
        return f"We define `{name}` as `{rhs}`.\n"
    return f"We define `{name}` as in Lean (`{d['sig'][:200]}`).\n"


def summarize_tactics(proof: str) -> str:
    """Heuristic math-English proof summary from Lean tactic script."""
    lines = [ln.rstrip() for ln in proof.splitlines()]
    steps: list[str] = []
    for ln in lines:
        s = ln.strip()
        if not s or s.startswith("--"):
            continue
        # Skip pure punctuation / closers
        if s in {"}", ")", "]", "·"}:
            continue
        if s.startswith("intro "):
            steps.append(f"Introduce {s[len('intro '):].strip()}.")
        elif s.startswith("intros"):
            steps.append("Introduce the remaining binders.")
        elif s.startswith("have "):
            # have name : type := ...
            hm = re.match(r"have\s+([^:\s]+)\s*:", s)
            if hm:
                steps.append(f"Establish auxiliary claim `{hm.group(1)}`.")
            else:
                steps.append(f"Establish an auxiliary claim (`{s[:80]}`).")
        elif s.startswith("obtain "):
            steps.append(f"Destructure a hypothesis via `{s[:100]}`.")
        elif s.startswith("let "):
            lm = re.match(r"let\s+([^:\s]+)", s)
            if lm:
                steps.append(f"Define `{lm.group(1)}`.")
            else:
                steps.append(f"Introduce a local definition (`{s[:80]}`).")
        elif s.startswith("refine "):
            steps.append(f"Refine the goal with `{s[len('refine '):][:100]}`.")
        elif s.startswith("exact "):
            steps.append(f"Conclude by `{s[len('exact '):][:120]}`.")
        elif s.startswith("apply "):
            steps.append(f"Apply `{s[len('apply '):][:120]}`.")
        elif s.startswith("rw ") or s.startswith("rewrite "):
            steps.append(f"Rewrite using `{s[:120]}`.")
        elif s.startswith("simp"):
            steps.append(f"Simplify (`{s[:100]}`).")
        elif s.startswith("calc"):
            steps.append("Argue by a calculation chain.")
        elif s.startswith("cases ") or s.startswith("rcases "):
            steps.append(f"Case-split via `{s[:100]}`.")
        elif s.startswith("induction "):
            steps.append(f"Induct via `{s[:100]}`.")
        elif s.startswith("constructor"):
            steps.append("Split into constructor goals.")
        elif s.startswith("funext") or s.startswith("ext"):
            steps.append("Extend by pointwise equality.")
        elif s.startswith("convert "):
            steps.append(f"Convert the goal using `{s[len('convert '):][:100]}`.")
        elif s.startswith("change "):
            steps.append(f"Change the goal to `{s[len('change '):][:100]}`.")
        elif s.startswith("suffices "):
            steps.append(f"It suffices to show `{s[len('suffices '):][:100]}`.")
        elif s.startswith("by_cases "):
            steps.append(f"Case on `{s[len('by_cases '):][:80]}`.")
        elif s.startswith("specialize "):
            steps.append(f"Specialize `{s[len('specialize '):][:100]}`.")
        elif s.startswith("simpa"):
            steps.append(f"Finish with `simpa` (`{s[:100]}`).")
        elif s.startswith("aesop") or s.startswith("linarith") or s.startswith("ring") or s.startswith("norm_num") or s.startswith("positivity") or s.startswith("omega"):
            steps.append(f"Discharge by automation (`{s.split()[0]}`).")
        elif s.startswith("exact?") or s.startswith("apply?"):
            steps.append("Search and apply a library lemma.")
        elif s.startswith("·") or s.startswith("."):
            continue
        elif s.startswith("{") or s.endswith("=>"):
            continue
        else:
            # Keep short leftover tactic lines as terse steps
            if len(s) < 100 and not s.startswith("end"):
                steps.append(f"Use `{s}`.")
    # Deduplicate consecutive identical steps; cap length
    dedup: list[str] = []
    for st in steps:
        if not dedup or dedup[-1] != st:
            dedup.append(st)
    if len(dedup) > 40:
        dedup = dedup[:40] + ["…"]
    if not dedup:
        return "Proof. The Lean proof is a short tactic script; see the source listing."
    return "Proof. " + " ".join(dedup)


def english_for_theorem_stub(d: dict) -> str:
    label = _KIND_LABEL.get(d["kind"], d["kind"].capitalize())
    name = d["name"]
    if d["doc"]:
        stmt = d["doc"].rstrip(".") + "."
    else:
        stmt = f"Statement as in Lean: `{d['sig'][:400]}`."
    proof = (d.get("proof") or "").strip()
    rhs = (d.get("rhs") or "").strip()
    if proof:
        summary = summarize_tactics(proof)
    elif rhs:
        rhs1 = re.sub(r"\s+", " ", rhs.splitlines()[0]).strip()
        summary = (
            f"Proof. Immediate from `{rhs1}` "
            f"(definitional reduction / direct application in Lean)."
        )
    else:
        summary = "Proof. (No proof body extracted; see the Lean source.)"
    return f"**{label}** (`{name}`). {stmt}\n\n{summary}\n"


def render_ailean(stem: str, decls: list[dict], *, fill_defs_only: bool) -> str:
    # No boilerplate header — prose starts with the mathematics.
    parts: list[str] = []
    if not decls:
        return ""
    for d in decls:
        if d["kind"] in {"def", "abbrev", "structure", "class", "inductive", "instance", "axiom"}:
            parts.append(english_for_def(d))
        elif fill_defs_only:
            parts.append(english_for_theorem_stub(d))
        else:
            parts.append(english_for_theorem_stub(d))
    return "\n".join(parts).rstrip() + "\n"


def wire_leaf(md: Path, ailean_name: str) -> None:
    text = md.read_text(encoding="utf-8")
    text = AILEAN_IMPORT_RE.sub("", text)
    lines = text.splitlines(keepends=True)
    # Insert ailean import after the H1 heading block
    out: list[str] = []
    inserted = False
    i = 0
    while i < len(lines):
        out.append(lines[i])
        if not inserted and lines[i].startswith("# "):
            # skip blank lines after title, then insert
            j = i + 1
            while j < len(lines) and lines[j].strip() == "":
                out.append(lines[j])
                j += 1
            out.append(f'@import "{ailean_name}" {{code_block=false}}\n\n')
            inserted = True
            i = j - 1
        i += 1
    if not inserted:
        out.insert(0, f'@import "{ailean_name}" {{code_block=false}}\n\n')
    md.write_text("".join(out), encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--wire", action="store_true", help="insert @import of ailean into leaves")
    ap.add_argument(
        "--fill-defs-only",
        action="store_true",
        help="emit def/structure English; theorems get PROOF_TODO stubs",
    )
    ap.add_argument(
        "--only",
        nargs="*",
        help="optional lean rel paths to process",
    )
    ap.add_argument(
        "--force",
        action="store_true",
        help="overwrite existing *_ailean.txt even if already polished",
    )
    args = ap.parse_args()
    leaves = leaf_map()
    if args.only:
        leaves = {k: v for k, v in leaves.items() if k in args.only}
    n = 0
    skipped = 0
    for lean_rel, md in sorted(leaves.items()):
        lean_path = LEAN_DIR / lean_rel
        stem = Path(lean_rel).stem
        decls = extract_decls(lean_path.read_text(encoding="utf-8"))
        ailean_name = f"{stem}_ailean.txt"
        ailean_path = md.with_name(ailean_name)
        existing = ailean_path.read_text(encoding="utf-8") if ailean_path.is_file() else ""
        # Preserve agent-polished prose unless --force.
        polished = (
            existing
            and "PROOF_TODO" not in existing
            and "Immediate from" not in existing
            and "Use `" not in existing  # heuristic tactic laundry list
        )
        if polished and not args.force:
            text = existing
            skipped += 1
        else:
            text = render_ailean(stem, decls, fill_defs_only=args.fill_defs_only)
            ailean_path.write_text(text, encoding="utf-8")
        if args.wire:
            wire_leaf(md, ailean_name)
        n += 1
        todos = text.count("PROOF_TODO")
        print(f"{lean_rel}: {len(decls)} decls, PROOF_TODO={todos} → {ailean_path.relative_to(ROOT)}")
    print(f"processed {n} modules (preserved {skipped} polished ailean files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

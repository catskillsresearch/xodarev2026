#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Build holes-graph.json and HOLES.md for the SignatureVolatility proof-hole board.

File-level board: every SignatureVolatility module is a hole. All modules start as
unverified TBD (Gemini dump / unverified formalization).

Hard edges come from direct `import SignatureVolatility…` in each submodule file
only (the root barrel `SignatureVolatility.lean` is excluded — it imports everything
and would clutter the board). Blocking uses those direct imports; the drawn graph
applies transitive reduction so implied edges are not duplicated.

Override verification later by adding module ids to VERIFIED.
"""
from __future__ import annotations

import json
import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "SignatureVolatility"
OUT_JSON = ROOT / "holes-graph.json"
OUT_HTML = ROOT / "holes.html"
HTML_EMBED_MARKER = "/*HOLES_GRAPH_JSON*/"
OUT_MD = ROOT / "HOLES.md"
OUT_EDGES = ROOT / "holes-edges.txt"

IMPORT_RE = re.compile(
    r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(SignatureVolatility(?:\.\S+)?)"
)

SORRY_RE = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")

# Campaign kit / theorem modules that must be paper-strength (nontrivial Ito, Stratonovich
# signature, Riccati, Davis–Obłój, GKW). Listed here so HOLES.md always surfaces them; they
# are never "done" while they contain `sorry` (see `file_has_sorry`).
PAPER_KIT_GOALS: list[str] = [
    "ProlongedBrownianSetup.StratonovichOfBM",
    "ItoCalculusKit.OfMathFin",
    "SignatureRiccatiKit.OfSetup",
    "PriceFiltrationSignatureSpace.OfMarket",
    "GKWDecompositionSetup.OfPFS",
    # Paper entry theorems (instance wrappers; blocked until the kits above are done):
    "TheoremA",
    "TheoremB",
    "TheoremC",
    "TheoremD",
]

# Module ids (short paths) that have been human-verified / sorry-free and may be
# marked done once all hard predecessors are done. Empty ⇒ everything TBD.
# Do NOT list paper-kit goal modules here until they are sorry-free at paper strength.
VERIFIED: set[str] = {
    "AdmissibleGainsUnderP",
    "BanachAlgebraConcatBound",
    "BlackScholesModel",
    "ChenIdentity",
    "ClassicalRiccatiSolution",
    "Corollary36SigmaWellDefined",
    "DualPairing",
    "DualPairingLeNormWDualMulNormW",
    "ExtTensorAlgebra.Antipode",
    "ExtTensorAlgebra.BasisWord",
    "ExtTensorAlgebra.Concat",
    "ExtTensorAlgebra.ConcatAssoc",
    "ExtTensorAlgebra.Coord",
    "ExtTensorAlgebra.EvalShuffleBasis",
    "FirstOrderBrownianVolModel",
    "ExtTensorAlgebra.ExtTensorAlgebra",
    "ExtTensorAlgebra.FreeTensorAlgebra",
    "ExtTensorAlgebra.IsFinitelySupported",
    "ExtTensorAlgebra.LevelInner",
    "ExtTensorAlgebra.LevelNorm",
    "ExtTensorAlgebra.LevelNormSq",
    "ExtTensorAlgebra.ShuffleBasis",
    "ExtTensorAlgebra.ShuffleWords",
    "ExtTensorAlgebra.TensorExp",
    "ExtTensorAlgebra.TensorExpLevelNorm",
    "ExtTensorAlgebra.TensorExpNeg",
    "ExtTensorAlgebra.TensorExpShuffle",
    "GeneratedFiltration",
    "GKWDecompositionSetup",
    "HypH1",
    "HypH1OfIsFinitelySupported",
    "HypH2",
    "HypH3",
    "IndexedFiltration",
    "InfiniteGeometricSignatureModel",
    "Lemma32SignatureInTw",
    "Lemma61GramPosDef",
    "IsSpecialSemimartingale",
    "ItoCalculusKit",
    "ItoCalculusKit.BrownianQuadVarAS",
    "ItoCalculusKit.FourthMoment",
    "ItoCalculusKit.JointPast",
    "ItoCalculusKit.KitRaw",
    "ItoCalculusKit.MartingaleTransform",
    "ItoCalculusKit.ItoQuadDoleans",
    "ItoCalculusKit.MathFinBridge",
    "ItoCalculusKit.RiemannConvergence",
    "ItoCalculusKit.SigmaContinuity",
    "ItoCalculusKit.ConstVol",
    "ItoCalculusKit.GBMMartingale",
    "ItoCalculusKit.PathwiseExpIto",
    "Letter",
    "MemL2w",
    "MemL2wInv",
    "MemL2wInvOfMemTw",
    "MemTw",
    "MemTwDual",
    "MemTwDualOfMemL2w",
    "NflvrOfMartingaleMeasure",
    "Norm2w",
    "Norm2wInv",
    "NormW",
    "NormWDual",
    "Preliminaries",
    "PriceFiltration",
    "PriceFiltrationSignatureSpace",
    "PriceFiltrationSignatureSpace.AugmentedMarketSpan",
    "PriceFiltrationSignatureSpace.CompletenessDepth",
    "PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration",
    "PriceFiltrationSignatureSpace.VInfty",
    "PriceFiltrationSignatureSpace.VSubspace",
    "Proposition311SharpnessOfH1",
    "Proposition65NormalEquations",
    "ProjGt",
    "ProjLe",
    "ProlongedBrownianSetup",
    "ProlongedBrownianSetup.BrownianFiltration",
    "ProlongedBrownianSetup.OfBrownian",
    "ProlongedBrownianSetup.ItoIntegralAgainstBM",
    "ProlongedBrownianSetup.ItoIntegralProcess",
    "ProlongedBrownianSetup.ItoWordIntegral",
    "ProlongedBrownianSetup.ItoWordIntegralConsLong",
    "ProlongedBrownianSetup.ItoWordIntegralLe1",
    "ProlongedBrownianSetup.ItoWordIntegralLe2",
    "ProlongedBrownianSetup.Sig2Strat",
    "ProlongedBrownianSetup.Sig2StratAdapted",
    "ProlongedBrownianSetup.Sig2StratChenShuffle",
    "ProlongedBrownianSetup.Sig2StratDyadic",
    "ProlongedBrownianSetup.Sig2StratMoments",
    "ProlongedBrownianSetup.SignatureOfBM",
    "ProlongedBrownianSetup.SignatureFiltration",
    "ProlongedBrownianSetup.StratonovichItoConversion",
    "ProlongedBrownianSetup.StratonovichOfBM",
    "ProlongedBrownianSetup.WAug",
    "ProlongedBrownianSetup.WHat",
    "PureBrownianWord",
    "QuinticOUSignatureModel",
    "Remark219BlackScholesRiccati",
    "RiccatiOpBounded",
    "RightShift",
    "SatisfiesNFLVR",
    "Section71BlackScholesCompleteness",
    "ShuffleFinite",
    "ShuffleIdentity",
    "SignatureFiltrationEqBrownianFiltration",
    "SignatureHestonLevel2Model",
    "SignaturePriceSolution",
    "SignatureRiccatiKit",
    "SignatureVolatilityModel",
    "SignatureVolatilityModel.Sigma",
    "SmoothIteratedIntegral",
    "SmoothSignature",
    "StratonovichHalfLaplacian",
    "SuperfactorialFunctional",
    "TailNorm2wInvLeRatioMulNormW",
    "TheoremA",
    "TheoremAOfBrownianSetupItoKit",
    "TheoremB",
    "TheoremBOfSetupItoRiccatiKit",
    "TheoremC",
    "TheoremCOfMarketKit",
    "TheoremD",
    "TheoremDOfMarketKit",
    "TimeReindex",
    "Tw",
    "Word",
    "WordsOfLength",
    "Weight",
    "Weight.ConstOne",
    "Weight.Geometric",
    "WeightedTruncationEstimates",
}


def short_mod(mod: str) -> str:
    if mod == "SignatureVolatility":
        return "(root)"
    if mod.startswith("SignatureVolatility."):
        return mod[len("SignatureVolatility.") :]
    return mod


def file_has_sorry(path: Path) -> bool:
    """True if the Lean file contains a `sorry` token (not in a comment-only line heuristically)."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return False
    for line in text.splitlines():
        code = line.split("--", 1)[0]
        if SORRY_RE.search(code):
            return True
    return False


def file_to_mod(path: Path) -> str:
    if path == ROOT / "SignatureVolatility.lean":
        return "SignatureVolatility"
    rel = path.relative_to(LEAN_ROOT).with_suffix("").as_posix().replace("/", ".")
    return f"SignatureVolatility.{rel}"


def transitive_reduction(edges: list[tuple[str, str]]) -> list[tuple[str, str]]:
    """Drop edges implied by other import-deps (same reachability, cleaner graph)."""
    if not edges:
        return []
    adj: dict[str, set[str]] = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)

    def reachable(start: str, goal: str, skip: tuple[str, str]) -> bool:
        stack = [start]
        seen = {start}
        while stack:
            u = stack.pop()
            for v in adj.get(u, ()):
                if (u, v) == skip:
                    continue
                if v == goal:
                    return True
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return False

    return [(a, b) for a, b in edges if not reachable(a, b, (a, b))]


def discover() -> tuple[dict[str, dict], list[tuple[str, str]]]:
    """Return nodes meta by short id, and hard edges (dep → importer)."""
    # Omit SignatureVolatility.lean: it imports every submodule and only adds noise.
    files = sorted(LEAN_ROOT.rglob("*.lean"))
    mod_to_file: dict[str, str] = {}
    imports: list[tuple[str, str]] = []  # (importer_mod, dep_mod)

    for path in files:
        if not path.is_file():
            continue
        if path.name.endswith(".backup.lean") or "monolith" in path.name:
            continue
        mod = file_to_mod(path)
        mod_to_file[mod] = str(path.relative_to(ROOT))
        text = path.read_text(encoding="utf-8")
        for line in text.splitlines():
            m = IMPORT_RE.match(line.strip())
            if not m:
                continue
            dep = m.group(1)
            if dep == mod:
                continue
            imports.append((mod, dep))

    # Ensure every imported SignatureVolatility.* appears even if somehow missing.
    for _importer, dep in imports:
        if dep.startswith("SignatureVolatility") and dep not in mod_to_file:
            # Placeholder path from module name.
            if dep == "SignatureVolatility":
                mod_to_file[dep] = "SignatureVolatility.lean"
            else:
                rel = dep[len("SignatureVolatility.") :].replace(".", "/") + ".lean"
                mod_to_file[dep] = f"SignatureVolatility/{rel}"

    nodes: dict[str, dict] = {}
    for mod, file_ in sorted(mod_to_file.items()):
        sid = short_mod(mod)
        # Coarse section buckets for HOLES.md grouping.
        if sid == "(root)":
            section = 99
        elif sid == "Basic":
            section = 0
        elif "." not in sid:
            section = 1
        else:
            top = sid.split(".", 1)[0]
            section = {
                "ExtTensorAlgebra": 2,
                "Weight": 3,
                "ProlongedBrownianSetup": 4,
                "PriceFiltrationSignatureSpace": 5,
                "SignatureVolatilityModel": 6,
            }.get(top, 1)
        nodes[sid] = {
            "label": sid,
            "section": section,
            "file": file_,
            "detail": "Unverified TBD — treat as a hole until reviewed.",
            "_mod": mod,
        }

    short = {mod: short_mod(mod) for mod in mod_to_file}
    edges: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for importer, dep in imports:
        if dep not in short or importer not in short:
            continue
        frm, to = short[dep], short[importer]
        if frm == to:
            continue
        key = (frm, to)
        if key in seen:
            continue
        seen.add(key)
        edges.append(key)
    return nodes, edges


def build() -> dict:
    nodes_meta, hard_edges = discover()
    display_edges = transitive_reduction(hard_edges)

    hard_preds: dict[str, list[str]] = {nid: [] for nid in nodes_meta}
    for frm, to in hard_edges:
        if frm in nodes_meta and to in nodes_meta:
            hard_preds[to].append(frm)

    has_sorry: dict[str, bool] = {}
    for nid, meta in nodes_meta.items():
        has_sorry[nid] = file_has_sorry(ROOT / meta["file"])

    # Hole unless verified AND sorry-free. `sorry` always wins over VERIFIED.
    raw_hole = {
        nid: (nid not in VERIFIED) or has_sorry[nid] for nid in nodes_meta
    }

    status: dict[str, str] = {}
    for _ in range(len(nodes_meta) + 2):
        changed = False
        for nid in nodes_meta:
            preds_done = all(status.get(p) == "done" for p in hard_preds[nid])
            if not raw_hole[nid] and preds_done:
                st = "done"
            elif preds_done:
                st = "open"
            else:
                st = "blocked"
            if status.get(nid) != st:
                status[nid] = st
                changed = True
        if not changed:
            break

    nodes = []
    for nid, meta in nodes_meta.items():
        detail = meta.get("detail")
        if has_sorry[nid]:
            detail = (detail or "") + (" " if detail else "") + "Contains `sorry` (paper gap)."
        if nid in PAPER_KIT_GOALS:
            detail = (detail or "") + (" " if detail else "") + "Paper kit / theorem goal."
        nodes.append({
            "id": nid,
            "label": meta["label"],
            "section": meta["section"],
            "file": meta["file"],
            "status": status[nid],
            "blocker": None,
            "detail": detail,
            "hasSorry": has_sorry[nid],
            "paperKitGoal": nid in PAPER_KIT_GOALS,
        })

    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        if n["status"] != "blocked":
            continue
        unfinished = [
            p for p in hard_preds[n["id"]]
            if by_id.get(p, {}).get("status") != "done"
        ]
        if unfinished:
            # Cap blocker text for modules with huge import sets.
            shown = unfinished[:8]
            extra = len(unfinished) - len(shown)
            suffix = f" (+{extra} more)" if extra > 0 else ""
            n["blocker"] = "needs " + ", ".join(shown) + suffix

    edges = [
        {"from": frm, "to": to, "kind": "hard"}
        for frm, to in display_edges
        if frm in nodes_meta and to in nodes_meta
    ]

    sorry_count = sum(1 for n in nodes if n["status"] in ("open", "blocked"))
    open_ids = [n["id"] for n in nodes if n["status"] == "open"]

    return {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "sorryCount": sorry_count,
        "legend": {
            "open": "No unfinished import-deps — verify / prove next (TBD)",
            "blocked": "Waiting on unfinished imported modules",
            "done": "Verified (listed in VERIFIED and deps done)",
        },
        "notes": [
            "File-level board: one node per SignatureVolatility .lean module.",
            "Done = listed in VERIFIED and deps done and file contains no `sorry`.",
            "Any `sorry` forces open/blocked regardless of VERIFIED.",
            "Hard edge B→A: A imports B (direct, submodule files only; barrel omitted).",
            "Drawn edges are transitively reduced; blocking still uses all direct imports.",
            "Paper kit goals: " + ", ".join(PAPER_KIT_GOALS) + ".",
            "Blue = done. Green = open. Grey = blocked.",
            "Regenerate with: python3 scripts/build_holes.py",
            f"Open tips: {', '.join(open_ids) if open_ids else '(none)'}.",
        ],
        "paperKitGoals": PAPER_KIT_GOALS,
        "nodes": nodes,
        "edges": edges,
    }


def write_md(data: dict) -> None:
    by_sec: dict[int, list] = {}
    for n in data["nodes"]:
        by_sec.setdefault(n["section"], []).append(n)
    open_n = [n for n in data["nodes"] if n["status"] == "open"]
    blocked_n = [n for n in data["nodes"] if n["status"] == "blocked"]
    done_n = [n for n in data["nodes"] if n["status"] == "done"]

    sec_title = {
        0: "Basic",
        1: "Top-level modules",
        2: "ExtTensorAlgebra",
        3: "Weight",
        4: "ProlongedBrownianSetup",
        5: "PriceFiltrationSignatureSpace",
        6: "SignatureVolatilityModel",
        99: "Root barrel",
    }

    sorry_n = [n for n in data["nodes"] if n.get("hasSorry")]
    paper_n = [n for n in data["nodes"] if n.get("paperKitGoal")]

    lines = [
        "# Proof holes (Xodarev / SignatureVolatility)",
        "",
        "File-level inventory of Lean modules. A module is **done** only if it is listed in "
        "`VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the "
        "file contains no `sorry`.",
        "",
        f"**Updated:** {data['updated']}",
        f"**Holes:** {data['sorryCount']} open+blocked · "
        f"{len(open_n)} open · {len(blocked_n)} blocked · {len(done_n)} done · "
        f"{len(sorry_n)} file(s) with `sorry`.",
        "",
        "**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).",
        "",
        "```bash",
        "python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, embeds into holes.html",
        "scripts/serve_holes.sh          # http://127.0.0.1:8766/holes.html",
        "```",
        "",
        "## Paper kit / theorem goals (before Challenge rewrite)",
        "",
        "These must be sorry-free at **paper strength** (nontrivial Itô kit, Stratonovich "
        "signature, Riccati duality, Davis–Obłój PFS, GKW) before updating Palomar Challenge / "
        "`formalization.yaml`.",
        "",
    ]
    if not paper_n:
        lines.append("_None listed in `PAPER_KIT_GOALS`._")
    else:
        lines.append("| Status | Id | `sorry`? | File |")
        lines.append("|---|---|---|---|")
        for n in sorted(paper_n, key=lambda x: x["id"]):
            lines.append(
                f"| {n['status']} | `{n['id']}` | "
                f"{'yes' if n.get('hasSorry') else 'no'} | `{n['file']}` |"
            )
    lines += ["", "## Files with `sorry`", ""]
    if not sorry_n:
        lines.append("_None._")
    else:
        lines.append("| Status | Id | File |")
        lines.append("|---|---|---|")
        for n in sorted(sorry_n, key=lambda x: x["id"]):
            lines.append(f"| {n['status']} | `{n['id']}` | `{n['file']}` |")
    lines += ["", "## Open now (Layer 0)", ""]
    if not open_n:
        lines.append("_None — every module is blocked or verified._")
    else:
        lines.append("| Id | File |")
        lines.append("|---|---|")
        for n in sorted(open_n, key=lambda x: x["id"]):
            lines.append(f"| `{n['id']}` | `{n['file']}` |")
    lines += ["", "## By group", ""]
    for sec in sorted(by_sec):
        rows = sorted(by_sec[sec], key=lambda x: x["id"])
        holes = sum(1 for n in rows if n["status"] != "done")
        title = sec_title.get(sec, f"group {sec}")
        lines.append(f"### {title} — {holes} hole(s)")
        lines.append("")
        lines.append("| Status | Id | File |")
        lines.append("|---|---|---|")
        for n in rows:
            lines.append(
                f"| {n['status']} | `{n['id']}` | `{n['file']}` |"
            )
        lines.append("")
    lines += [
        "## Dependency sketch",
        "",
        "Direct import-deps: `holes-edges.txt`. Display graph uses transitive reduction. "
        "Open [`holes.html`](holes.html) for the interactive board.",
        "",
    ]
    OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def embed_html(data: dict) -> None:
    if not OUT_HTML.exists():
        print(f"skip embed: {OUT_HTML.name} missing")
        return
    text = OUT_HTML.read_text(encoding="utf-8")
    start = text.find("const EMBEDDED_HOLES_GRAPH = ")
    marker = text.find(HTML_EMBED_MARKER, start)
    if start < 0 or marker < 0:
        print(f"skip embed: could not find EMBEDDED_HOLES_GRAPH / marker in {OUT_HTML.name}")
        return
    line_start = text.rfind("\n", 0, start) + 1
    end = marker + len(HTML_EMBED_MARKER)
    payload = json.dumps(data, separators=(",", ":"))
    new_line = f"    const EMBEDDED_HOLES_GRAPH = {payload}; {HTML_EMBED_MARKER}"
    OUT_HTML.write_text(text[:line_start] + new_line + text[end:], encoding="utf-8")


def main() -> None:
    _, direct_edges = discover()
    data = build()
    OUT_JSON.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    write_md(data)
    OUT_EDGES.write_text(
        "# Direct import SignatureVolatility deps (for blocking / build order)\n"
        + "\n".join(f"{frm} -hard-> {to}" for frm, to in sorted(direct_edges))
        + "\n",
        encoding="utf-8",
    )
    embed_html(data)
    open_n = sum(1 for n in data["nodes"] if n["status"] == "open")
    blocked_n = sum(1 for n in data["nodes"] if n["status"] == "blocked")
    done_n = sum(1 for n in data["nodes"] if n["status"] == "done")
    print(
        f"Wrote {OUT_JSON.name}, {OUT_MD.name}, embedded {OUT_HTML.name}: "
        f"{open_n} open, {blocked_n} blocked, {done_n} done "
        f"(sorryCount={data['sorryCount']})"
    )


if __name__ == "__main__":
    main()

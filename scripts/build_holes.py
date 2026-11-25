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
    r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?((?:SignatureVolatility)(?:\.\S+)?)"
)

SORRY_RE = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")

# Campaign kit / theorem modules that must be paper-strength (nontrivial Ito, Stratonovich
# signature, Riccati, Davis–Obłój, GKW). Listed here so HOLES.md always surfaces them; they
# are never "done" while they contain `sorry` (see `file_has_sorry`).
PAPER_KIT_GOALS: list[str] = [
    "ProlongedBrownianSetup.StratonovichOfBM",
    "ItoCalculusKit.OfMathFin",
    "PriceFiltrationSignatureSpace.OfMarket",
    "GKWDecompositionSetup.OfPFS",
    # Paper entry theorems (instance wrappers; blocked until the kits above are done):
    "TheoremA",
    "TheoremB",
    "TheoremC",
    "TheoremD",
]

# Modules that REFUTE a paper claim (Lean counterexample to the paper's English statement).
# Shown with status "counterexample" once verified and sorry-free. Any future module whose id
# ends in "False" or contains "Counterexample" is picked up automatically.
COUNTEREXAMPLES: dict[str, str] = {
    "Lemma77ShuffleEstimateFalse":
        "CounterExample_Lemma77: refutes paper Lemma 77 (weighted shuffle estimate) for every "
        "(H2) weight.",
    "Lemma78RiccatiLipschitzFalse":
        "CounterExample_Lemma78: refutes paper Lemma 78 (local Lipschitz bound for the Riccati "
        "operator); for w = 1 the operator is unbounded on the unit ball of T_w.",
    "TheoremDCounterExample":
        "CounterExample_TheoremD (theorem_D_residual_hypothesis_fails): the residual-expansion "
        "clause of Theorem 66 assumes N*_S < infinity, which fails for Black-Scholes (vacuous).",
    "Prop58BlackScholesDepthFalse":
        "CounterExample_Prop58: refutes paper Prop. 58 / PDF Prop. 5.5 (Black-Scholes has completeness "
        "depth 0); Black-Scholes depth is infinite under Definition 55.",
    "TheoremCCounterExample":
        "CounterExample_TheoremC (proved, not_theorem_C): Black-Scholes is complete on F^S_T "
        "(vendored MathFin martingale representation, F^S = F^W) for every finite strike set, "
        "while N*_S = infinity; so the paper's 'complete iff N*_S < infinity' is false.",
}

# Headline theorem modules whose paper statement is (partly) refuted. Value: (status, detail).
REFUTED_THEOREMS: dict[str, tuple[str, str]] = {
    "TheoremC": ("refuted",
        "REFUTED (CounterExample_TheoremC, theorem_C_refuted := not_theorem_C): Black-Scholes is "
        "complete with any finite set of calls but has N*_S = infinity, so 'complete iff N*_S < "
        "infinity' fails. Also: depth is infinite in every non-degenerate model; Prop. 58 refuted."),
    "TheoremD": ("half-proved",
        "Half_TheoremD: GKW projection part proved (theorem_D). The residual-expansion clause is "
        "refuted separately by CounterExample_TheoremD (TheoremDCounterExample)."),
}


# Documented headline notes. Palomar has no open-problem category; keep this empty.
# Unfinished follow-on work is recorded as ordinary open nodes (never this map).
OPEN_PROBLEMS: dict[str, str] = {}


# Labels shown on unfinished nodes (always applied).
STATUS_LABELS: dict[str, str] = {
    "SignatureRiccatiKit.AffineRiccatiDuality": "not_affine_riccati_duality",
    "TheoremBMpr": "not_theorem_B_mpr, not_theorem_B",
    "SignatureRiccatiKit.AffineRiccatiDualityMp": "affine_riccati_duality_mp",
    "TheoremB": "theorem_B_mp",
    "NflvrDefs": "NflvrDefs",
    "NflvrCone": "NflvrCone",
    "NflvrDoubling": "NflvrDoubling",
    "SignatureRiccatiKit.FawcettHermite": "C1 Hermite combinatorial core",
    "SignatureRiccatiKit.ComplexTilt": "C2a complex tilt E_t(ξ)",
    "SignatureRiccatiKit.ItoWordTiltClosedForm": "C2 tilted Itô-word closed form",
    "SignatureRiccatiKit.CondSigPoly": "C2b condSigPoly via contractions",
    "SignatureRiccatiKit.CondSigPolyIdentification": "C2c paperSig2 = condSigPoly under tilt",
    "SignatureRiccatiKit.SummableNormTermAndBound": "C1b contraction sum bound, type ≤ 1",
    "SignatureRiccatiKit.DifferentiableAtTsum": "C3a tsum of entire functions is entire",
    "SignatureRiccatiKit.FourierUniquenessGaussian": "C3b Fourier uniqueness vs Gaussian",
    "SignatureRiccatiKit.IteratedDerivGaussian": "C3c Gaussian product derivatives",
    "SignatureRiccatiKit.EntireTransfer": "C3 transfer to f (Pillar C)",
    "SignatureRiccatiKit.CounterexampleV1": "v₁ (shared)",
    "SignatureRiccatiKit.LintegralExpShifted": "B1a shifted Doléans bound ≤ 1",
    "SignatureRiccatiKit.CounterexampleV1PosLe": "B1 0 < v₁ ≤ 1",
    "SignatureRiccatiKit.CounterexampleV1LogBound": "B2 quartic log lower bound",
    "SignatureRiccatiKit.CameronMartinC2Shift": "B3a deterministic Cameron–Martin shift",
    "SignatureRiccatiKit.CounterexampleV1LogNonpos": "B3 log lower bound on (-∞, 0]",
    "SignatureRiccatiKit.BarrierU": "B4a barrier PDE",
    "SignatureRiccatiKit.IntegralExpBarrier": "B4b Itô + barrier bound",
    "SignatureRiccatiKit.CounterexampleV1Decay": "B4 decay to 0",
    "SignatureRiccatiKit.BrownianScalingShiftedExponent": "B5a Brownian scaling of Φ",
    "SignatureRiccatiKit.CondExpMulIndepDisintegrate": "B5b condExp disintegration",
    "SignatureRiccatiKit.CounterexampleV1CondExp": "B5 cond. exp. factorisation",
    "SignatureRiccatiKit.Poly4ConstOfLogBdd": "poly4 constant under log lower bound",
    "SignatureRiccatiKit.CounterexampleTensor": "u₀^(λ) tensor family",
    "SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample":
        "not_affine_riccati_duality_mpr (proved)",
}
STATUS_DETAILS: dict[str, str] = {
    "TheoremB":
        "theorem_B_mp (proved, compared): martingale on the signature filtration, the "
        "price-independent AdmissibleGainsUnderP NFLVR conjunct (any integrable G with E[G]≤0; "
        "the Palomar editorial audit flagged this as close to trivial), special semimartingale "
        "coordinates, and the -> direction of the Riccati transform equivalence. The paper's "
        "<- direction and the full iff are false; their negations are in TheoremBMpr. The "
        "compared NFLVR conjunct is AdmissibleGainsUnderP, not SatisfiesNFLVR_DS.",
    "NflvrDefs":
        "Paper NFLVR definitions (Mathlib-only, for later exact copy into the Challenge): "
        "S-admissible strategies, the three gain cones (literal / terminal-bounded-below / "
        "uniformly bounded-below), and SatisfiesNFLVR_DS. Definitions only; no compared "
        "theorems in this file.",
    "NflvrCone":
        "If every uniformly bounded-below gain has integrable nonpositive mean, then "
        "SatisfiesNFLVR_DS holds (weak-* pairing with 1; no H3). Fatou gives nonpositive mean "
        "for an a.s. limit of mean-zero variables with a uniform lower bound.",
    "NflvrDoubling":
        "Geometric-grid doubling construction for the literal and terminal-only NFLVR "
        "refutations. theorem_literal_nflvr_fails is proved (024652f): the doubling "
        "strategy is S-admissible and V_T=1 a.s., so literal NFLVR fails for Brownian "
        "motion. Subtask nodes below record the internal port. Still to come, as ordinary "
        "open follow-on nodes: Black–Scholes transfer H=K/(Sσ₀), the terminal-only "
        "refutation, Challenge compared theorems, and the writeup (Carbon/Gemini).",
    "SignatureRiccatiKit.AffineRiccatiDualityMp":
        "Proved -> direction of the affine / Riccati duality (paper Thm 4.2(ii)): an exponential-"
        "affine conditional transform through a classical Riccati solution gives a solution. "
        "Compared in comparator.json. The <- direction is false "
        "(`not_affine_riccati_duality_mpr`).",
    "SignatureRiccatiKit.AffineRiccatiDuality":
        "not_affine_riccati_duality: the paper iff fails as a statement over all finitely "
        "supported u0 with finite signature transform. Proved from "
        "not_affine_riccati_duality_mpr. The kit constructor signatureRiccatiKit_of_setup has "
        "been dropped. No `sorry` in this file.",
    "TheoremBMpr":
        "not_theorem_B_mpr and not_theorem_B: the paper's <- Riccati clause and the full "
        "Theorem B conjunction are false as universal statements. Proved from "
        "not_affine_riccati_duality_mpr / not_affine_riccati_duality. No `sorry` in this file.",
}


# Board labels (exact strings requested by Lars) for refuting modules / headline theorems.
REFUTATION_LABELS: dict[str, str] = {
    "Lemma77ShuffleEstimateFalse": "CounterExample_Lemma77",
    "Lemma78RiccatiLipschitzFalse": "CounterExample_Lemma78",
    "TheoremDCounterExample": "CounterExample_TheoremD",
    "Prop58BlackScholesDepthFalse": "CounterExample_Prop58",
    "TheoremC": "TheoremC: refuted by CounterExample_TheoremC",
    "TheoremCCounterExample": "CounterExample_TheoremC",
    "TheoremD": "Half_TheoremD",
}



# Internal structure of NflvrDoubling, shown as synthetic precursor / follow-on
# nodes so progress is visible on the board. These are not Lean modules and are
# not an "open problems" category: finished items are ordinary done nodes,
# remaining work is ordinary open (or blocked) nodes.
SYNTHETIC_NODES: list[dict] = [
    {
        "id": "NflvrDoubling.tauHit",
        "label": "isStoppingTime_tauHit (047b221)",
        "status": "done",
        "detail": "Geometric grid t_n=T(1-2^{-n}) and hitting-time stopping lemma "
                  "isStoppingTime_tauHit. Grid foundations in 99d7748; stopping lemma "
                  "in 047b221.",
        "commits": "047b221, 99d7748",
    },
    {
        "id": "NflvrDoubling.incrDecay",
        "label": "increment independence & geometric decay (b74bd01)",
        "status": "done",
        "detail": "Independence of the standardized increments Z_n and geometric decay "
                  "P(E_n)≤q^n, plus the early V_T=1 a.s. identity. Done in b74bd01.",
        "commits": "b74bd01",
    },
    {
        "id": "NflvrDoubling.l2Bound",
        "label": "doublingC_sq_integral_le (b63d981)",
        "status": "done",
        "detail": "L² bound on the doubling weights, E[∏_{j<m}(1-Z_j)²]=2^m, and the "
                  "integrand / localizing-time packaging in bf9c194. Done in b63d981.",
        "commits": "b63d981, bf9c194",
    },
    {
        "id": "NflvrDoubling.wealthProcess",
        "label": "doublingWealth V_0=0, V_T=1, continuity (4c102ea)",
        "status": "done",
        "detail": "Explicit wealth process: starts at 0, ends at 1 almost surely, and "
                  "almost every path is continuous on [0,T]. Done in 4c102ea.",
        "commits": "4c102ea",
    },
    {
        "id": "NflvrDoubling.riemannSums",
        "label": "Riemann-sum tools + pathwise convergence (5a32c82, b7cfba5)",
        "status": "done",
        "detail": "Left-point Riemann-sum tools for the doubling integrand (5a32c82) and "
                  "pathwise convergence of indicator partition sums to the matching "
                  "Brownian increment (b7cfba5).",
        "commits": "5a32c82, b7cfba5",
    },
    {
        "id": "NflvrDoubling.itoIntegral",
        "label": "isItoIntegral_doublingWealth (3fc4c9e)",
        "status": "done",
        "detail": "The doubling wealth is the Itô integral of K, with no glue parameters. "
                  "Done in 3fc4c9e.",
        "commits": "3fc4c9e",
    },
    {
        "id": "NflvrDoubling.evalAdapted",
        "label": "measurable_bmCoord_eval_le / adaptedness (024652f)",
        "status": "done",
        "detail": "B evaluated at a stopping time τ≤t is F_t-measurable "
                  "(Mathlib stronglyMeasurable_stoppedValue_of_le); X_n and c_n are "
                  "F_{t_n}-adapted. Dyadic helpers in f457b1e; lemma and adaptedness "
                  "in 024652f.",
        "commits": "024652f, f457b1e",
    },
    {
        "id": "NflvrDoubling.predictableK",
        "label": "predictability of K (024652f)",
        "status": "done",
        "detail": "Left-open stochastic intervals (t_n,τ_n] are predictable (1d57446); "
                  "uncurry doublingK is a pointwise limit of those stopped blocks, hence "
                  "predictable (024652f).",
        "commits": "024652f, 1d57446",
    },
    {
        "id": "NflvrDoubling.sAdmissible",
        "label": "SAdmissible (024652f)",
        "status": "done",
        "detail": "IntegrableOn of K² on [0,T] a.s., hence the doubling strategy is "
                  "S-admissible for S=σ=1. Done in 024652f.",
        "commits": "024652f",
    },
    {
        "id": "NflvrDoubling.literalFails",
        "label": "theorem_literal_nflvr_fails (024652f)",
        "status": "done",
        "detail": "Literal NFLVR fails: the doubling strategy is admissible, V_T=1 a.s., "
                  "and this is a nontrivial free lunch in the Delbaen–Schachermayer cone. "
                  "Done in 024652f.",
        "commits": "024652f",
    },
    {
        "id": "NflvrDoubling.bsPrice",
        "label": "bsPrice continuous, positive, adapted (4d9d645)",
        "status": "done",
        "detail": "Closed-form Black–Scholes price s₀ exp(σ₀ B_t - ½ σ₀² t) is "
                  "continuous, strictly positive, and F_t-adapted. Done in 4d9d645.",
        "file": "SignatureVolatility/NflvrDoubling.lean",
        "commits": "4d9d645",
    },
    {
        "id": "NflvrDoubling.cutoffPred",
        "label": "predictable cutoff of a continuous adapted process (4d9d645)",
        "status": "done",
        "detail": "Dyadic left-endpoint approximations converge pathwise to the "
                  "(0,T] cutoff of a continuous adapted process, hence that cutoff "
                  "is predictable. Done in 4d9d645.",
        "file": "SignatureVolatility/NflvrDoubling.lean",
        "commits": "4d9d645",
    },
    {
        "id": "NflvrDoubling.doublingH",
        "label": "sAdmissible_doublingH, H S σ₀ = K (4d9d645)",
        "status": "done",
        "detail": "The transferred integrand H=K/(Sσ₀) is predictable and "
                  "S-admissible for the closed-form BS price, and H S σ₀ equals K. "
                  "Done in 4d9d645.",
        "file": "SignatureVolatility/NflvrDoubling.lean",
        "commits": "4d9d645",
    },
    {
        "id": "NflvrDoubling.bsTransfer",
        "label": "not_literal_nflvr / not_terminal_bdd_nflvr (4d9d645)",
        "status": "done",
        "detail": "Black–Scholes transfer H=K/(Sσ₀): the same doubling wealth is "
                  "an admissible Itô integral in the BS market and ends at V_T=1 a.s., "
                  "so both literal NFLVR and the terminal-only bounded-below version "
                  "fail. Done in 4d9d645.",
        "file": "SignatureVolatility/NflvrDoubling.lean",
        "commits": "4d9d645",
    },
    {
        "id": "NflvrDoubling.terminalBdd",
        "label": "theorem_terminal_bdd_nflvr_fails (b8ea73f)",
        "status": "done",
        "detail": "The same admissible doubling wealth ends at V_T=1≥0 a.s., so the "
                  "terminal-only bounded-below cone also contains a nontrivial free "
                  "lunch. Done in b8ea73f.",
        "file": "SignatureVolatility/NflvrDoubling.lean",
        "commits": "b8ea73f",
    },
    {
        "id": "NflvrDoubling.challengeRefutations",
        "label": "Challenge not_literal_nflvr / not_terminal_bdd_nflvr",
        "status": "open",
        "detail": "Library theorems not_literal_nflvr and not_terminal_bdd_nflvr, unwrapped "
                  "forms in Challenge (≤1000 lines) and comparator.json, yaml main_results "
                  "v0.4, and the strict compare.",
        "file": "SignatureVolatilityComparator/Challenge.lean",
        "commits": "",
    },
    {
        "id": "NflvrDoubling.writeup",
        "label": "NFLVR writeup (Carbon/Gemini)",
        "status": "open",
        "detail": "Writeup pass using Carbon's notes: narratives, PROVENANCE.md Comparator "
                  "section, COMPARATOR.md, PalomarRegistration.md, and project.description, "
                  "crediting Carbon (Gemini).",
        "file": "Writeup/PalomarRegistration.md",
        "commits": "",
    },
]

# Edges are dep → dependent (the dependent uses / follows the dep).
# Done precursors chain into NflvrDoubling; remaining work follows it.
SYNTHETIC_EDGES: list[tuple[str, str]] = [
    ("NflvrDoubling.tauHit", "NflvrDoubling.incrDecay"),
    ("NflvrDoubling.incrDecay", "NflvrDoubling.l2Bound"),
    ("NflvrDoubling.l2Bound", "NflvrDoubling.wealthProcess"),
    ("NflvrDoubling.wealthProcess", "NflvrDoubling.riemannSums"),
    ("NflvrDoubling.riemannSums", "NflvrDoubling.itoIntegral"),
    ("NflvrDoubling.itoIntegral", "NflvrDoubling.evalAdapted"),
    ("NflvrDoubling.evalAdapted", "NflvrDoubling.predictableK"),
    ("NflvrDoubling.predictableK", "NflvrDoubling.sAdmissible"),
    ("NflvrDoubling.sAdmissible", "NflvrDoubling.literalFails"),
    ("NflvrDoubling.literalFails", "NflvrDoubling"),
    ("NflvrDoubling", "NflvrDoubling.bsPrice"),
    ("NflvrDoubling.bsPrice", "NflvrDoubling.cutoffPred"),
    ("NflvrDoubling.cutoffPred", "NflvrDoubling.doublingH"),
    ("NflvrDoubling.doublingH", "NflvrDoubling.bsTransfer"),
    ("NflvrDoubling", "NflvrDoubling.terminalBdd"),
    ("NflvrDoubling.bsTransfer", "NflvrDoubling.challengeRefutations"),
    ("NflvrDoubling.terminalBdd", "NflvrDoubling.challengeRefutations"),
    ("NflvrDoubling.challengeRefutations", "NflvrDoubling.writeup"),
]


def apply_synthetic(
    nodes_meta: dict[str, dict], hard_edges: list[tuple[str, str]]
) -> tuple[dict[str, dict], list[tuple[str, str]]]:
    """Inject synthetic precursor / follow-on nodes and their edges."""
    for item in SYNTHETIC_NODES:
        nid = item["id"]
        if nid in nodes_meta:
            raise RuntimeError(f"synthetic node id collides with a Lean module: {nid}")
        nodes_meta[nid] = {
            "label": item["label"],
            "section": 10,
            "file": item.get("file", "SignatureVolatility/NflvrDoubling.lean"),
            "detail": item["detail"],
            "_mod": nid,
            "_synthetic": True,
            "_forced_status": item["status"],
            "_commits": item.get("commits", ""),
        }
    hard_edges = list(hard_edges) + list(SYNTHETIC_EDGES)
    return nodes_meta, hard_edges


def is_counterexample(nid: str) -> bool:
    return (nid in COUNTEREXAMPLES or nid.endswith("False")
            or nid.endswith("Counterexample") or nid.endswith("CounterExample"))


# Module ids (short paths) that have been human-verified / sorry-free and may be
# marked done once all hard predecessors are done. Empty ⇒ everything TBD.
# Do NOT list paper-kit goal modules here until they are sorry-free at paper strength.
VERIFIED: set[str] = {
    "SignatureRiccatiKit.AffineRiccatiDualityMp",
    "SignatureRiccatiKit.AffineRiccatiDuality",
    "SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample",
    "SignatureRiccatiKit.FawcettHermite",
    "SignatureRiccatiKit.Poly4ConstOfLogBdd",
    "SignatureRiccatiKit.LintegralExpShifted",
    "SignatureRiccatiKit.CounterexampleV1PosLe",
    "SignatureRiccatiKit.CounterexampleV1LogBound",
    "SignatureRiccatiKit.DifferentiableAtTsum",
    "SignatureRiccatiKit.FourierUniquenessGaussian",
    "SignatureRiccatiKit.ComplexTilt",
    "SignatureRiccatiKit.IteratedDerivGaussian",
    "SignatureRiccatiKit.CondSigPoly",
    "SignatureRiccatiKit.CondSigPolyIdentification",
    "SignatureRiccatiKit.EntireTransfer",
    "SignatureRiccatiKit.CondExpMulIndepDisintegrate",
    "SignatureRiccatiKit.CounterexampleV1CondExp",
    "SignatureRiccatiKit.BrownianScalingShiftedExponent",
    "SignatureRiccatiKit.SummableNormTermAndBound",
    "SignatureRiccatiKit.ItoWordTiltClosedForm",
    "SignatureRiccatiKit.CameronMartinC2Shift",
    "SignatureRiccatiKit.CounterexampleV1LogNonpos",
    "SignatureRiccatiKit.IntegralExpBarrier",
    "SignatureRiccatiKit.CounterexampleV1Decay",
    "SignatureRiccatiKit.BarrierU",
    "SignatureRiccatiKit.CounterexampleTensor",
    "SignatureRiccatiKit.CounterexampleV1",
    "TheoremBMpr",
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
    "HypH1",
    "HypH1OfIsFinitelySupported",
    "HypH2",
    "HypH3",
    "IndexedFiltration",
    "InfiniteGeometricSignatureModel",
    "Lemma32SignatureInTw",
    "Lemma61GramPosDef",
    "Prop58BlackScholesDepthFalse",
    "TheoremCCounterExample",
    "PriceFiltrationSignatureSpace.OfMarket",
    "GKWDecompositionSetup.OfPFS",
    "Lemma77ShuffleEstimateFalse",
    "Lemma78RiccatiLipschitzFalse",
    "IsSpecialSemimartingale",
    "ItoCalculusKit",
    "ItoCalculusKit.BrownianQuadVarAS",
    "ItoCalculusKit.FourthMoment",
    "ItoCalculusKit.JointPast",
    "ItoCalculusKit.KitRaw",
    "ItoCalculusKit.MartingaleTransform",
    "ItoCalculusKit.ItoQuadDoleans",
    "ItoCalculusKit.MathFinBridge",
    "ItoCalculusKit.MathFinBridgeSetup",
    "ItoCalculusKit.RiemannConvergence",
    "ItoCalculusKit.SigmaContinuity",
    "ItoCalculusKit.ConstVol",
    "ItoCalculusKit.GBMMartingale",
    "ItoCalculusKit.GBMEnvelope",
    "ItoCalculusKit.SigmaHolder",
    "ItoCalculusKit.ExpSupermartingale",
    "ItoCalculusKit.DoleansMoments",
    "ItoCalculusKit.ItoIncrement",
    "ItoCalculusKit.EighthMoment",
    "ItoCalculusKit.EighthTransform",
    "ItoCalculusKit.ItoIncrement8",
    "ItoCalculusKit.SigmaHolder8",
    "ItoCalculusKit.EvenMoment",
    "ItoCalculusKit.EvenTransform",
    "ItoCalculusKit.ItoIncrementEven",
    "ItoCalculusKit.LebIncrementEven",
    "ItoCalculusKit.LevelBounds",
    "ItoCalculusKit.LevelDecay",
    "ItoCalculusKit.SigmaBounds",
    "ItoCalculusKit.QuadIncrement",
    "ItoCalculusKit.LogDoleansIncrement",
    "ItoCalculusKit.GridChange",
    "ItoCalculusKit.ItoOrthogonal",
    "ItoCalculusKit.FrozenIncrement8",
    "ItoCalculusKit.FrozenOrthogonal",
    "ItoCalculusKit.QVTransform",
    "ItoCalculusKit.GridDoob",
    "ItoCalculusKit.DoleansErrorPathwise",
    "ItoCalculusKit.DoleansSigma",
    "ItoCalculusKit.DoleansInputs",
    "ItoCalculusKit.DoleansIdentify",
    "ItoCalculusKit.KolmogorovIto",
    "ItoCalculusKit.DoleansQV",
    "ItoCalculusKit.DoleansSDE",
    "ItoCalculusKit.NovikovMartingale",
    "ItoCalculusKit.RiemannRate8",
    "ItoCalculusKit.HolderPath",
    "ItoCalculusKit.SubseqUniform",
    "ItoCalculusKit.DoobEnvelope",
    "ItoCalculusKit.DoleansEnvelope",
    "ItoCalculusKit.NovikovDoob",
    "ItoCalculusKit.DoleansStrongClass",
    "ItoCalculusKit.FrozenIncrement4",
    "ItoCalculusKit.CrossVariation",
    "ItoCalculusKit.StoppedRaw",
    "ItoCalculusKit.StoppedStep",
    "ItoCalculusKit.StoppedKit",
    "ItoCalculusKit.StoppedL2",
    "ItoCalculusKit.OfMathFin",
    "SignatureRiccatiKit.RiccatiOp",
    "SignatureRiccatiKit.CoordSemimartingale",
    "SignatureRiccatiKit.RiccatiExpProcess",
    "ItoCalculusKit.PathwiseExpIto",
    "Letter",
    "MemL2w",
    "MemL2wInv",
    "MemL2wInvOfMemTw",
    "MemTw",
    "MemTwDual",
    "MemTwDualOfMemL2w",
    "NflvrCone",
    "NflvrDefs",
    "NflvrDoubling",
    "NflvrOfMartingaleMeasure",
    "Norm2w",
    "Norm2wInv",
    "NormW",
    "NormWDual",
    "Preliminaries",
    "PriceFiltration",
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
    "ProlongedBrownianSetup.ContVersion",
    "ProlongedBrownianSetup.ContVersionKolmogorov",
    "ProlongedBrownianSetup.StratItoCoeffBounds",
    "ProlongedBrownianSetup.PaperSig",
    "ProlongedBrownianSetup.PaperSigDynamics",
    "ProlongedBrownianSetup.ShiftedWordIntegral",
    "ProlongedBrownianSetup.PaperSigChen",
    "ProlongedBrownianSetup.Sig2StratAdapted",
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
    "TheoremD",
    "TheoremDCounterExample",
    "Unwrapped",
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


def strip_lean_comments(text: str) -> str:
    """Remove nested `/- ... -/` block comments (incl. docstrings), `--` line comments and
    string literals, so only real code remains."""
    out: list[str] = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); i = n if j < 0 else j; continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1; continue
        out.append(text[i]); i += 1
    return "".join(out)


def file_sorry_count(path: Path) -> int:
    """Number of real `sorry` tokens in a Lean file (comments, docstrings, strings ignored)."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return 0
    return len(SORRY_RE.findall(strip_lean_comments(text)))


def file_has_sorry(path: Path) -> bool:
    return file_sorry_count(path) > 0


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
    nodes_meta, hard_edges = apply_synthetic(nodes_meta, hard_edges)
    display_edges = transitive_reduction(hard_edges)

    hard_preds: dict[str, list[str]] = {nid: [] for nid in nodes_meta}
    for frm, to in hard_edges:
        if frm in nodes_meta and to in nodes_meta:
            hard_preds[to].append(frm)

    has_sorry: dict[str, bool] = {}
    for nid, meta in nodes_meta.items():
        if meta.get("_synthetic"):
            has_sorry[nid] = False
        else:
            has_sorry[nid] = file_has_sorry(ROOT / meta["file"])

    # Hole unless verified AND sorry-free. `sorry` always wins over VERIFIED.
    # Synthetic nodes use an explicit forced status instead of VERIFIED.
    raw_hole = {}
    for nid, meta in nodes_meta.items():
        forced = meta.get("_forced_status")
        if forced == "done":
            raw_hole[nid] = False
        elif forced == "open":
            raw_hole[nid] = True
        else:
            raw_hole[nid] = (nid not in VERIFIED) or has_sorry[nid]

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

    # Display status: verified counterexample modules and refuted headline theorems get their
    # own status. Dependency logic above keeps using the internal "done".
    # Lars: every finished node is plain blue ("done"); the kind is kept as text only.
    display: dict[str, str] = dict(status)
    kind: dict[str, str | None] = {nid: None for nid in nodes_meta}
    for nid in nodes_meta:
        if status[nid] != "done":
            continue
        if is_counterexample(nid):
            kind[nid] = "counterexample"
        elif nid in REFUTED_THEOREMS:
            kind[nid] = REFUTED_THEOREMS[nid][0]

    nodes = []
    for nid, meta in nodes_meta.items():
        detail = meta.get("detail")
        if kind[nid] == "counterexample":
            detail = COUNTEREXAMPLES.get(nid, "COUNTEREXAMPLE to a paper claim.")
        elif kind[nid] is not None:
            detail = REFUTED_THEOREMS[nid][1]
        if nid in OPEN_PROBLEMS:
            detail = OPEN_PROBLEMS[nid]
        if nid in STATUS_DETAILS:
            detail = STATUS_DETAILS[nid]
        if has_sorry[nid]:
            detail = (detail or "") + (" " if detail else "") + "Contains `sorry` (paper gap)."
        if nid in PAPER_KIT_GOALS:
            detail = (detail or "") + (" " if detail else "") + "Paper kit / theorem goal."
        nodes.append({
            "id": nid,
            "label": STATUS_LABELS[nid] if nid in STATUS_LABELS
            else REFUTATION_LABELS.get(nid, meta["label"])
            if kind[nid] is not None else meta["label"],
            "section": meta["section"],
            "file": meta["file"],
            "status": display[nid],
            "kind": kind[nid],
            "blocker": None,
            "detail": detail,
            "hasSorry": has_sorry[nid],
            "paperKitGoal": nid in PAPER_KIT_GOALS,
            "synthetic": bool(meta.get("_synthetic")),
            "commits": meta.get("_commits") or None,
        })

    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        if n["status"] != "blocked":
            continue
        unfinished = [
            p for p in hard_preds[n["id"]]
            if status.get(p) != "done"
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

    # True number of `sorry` occurrences in the library (not the number of unfinished modules).
    # Deduplicate files so synthetic subtasks pointing at a parent module are not recounted.
    sorry_count = sum(
        file_sorry_count(ROOT / f)
        for f in {n["file"] for n in nodes if not n.get("synthetic")}
    )
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
            "File-level board: one node per SignatureVolatility .lean module, plus "
            "synthetic subtask nodes under NflvrDoubling (internal progress, not a "
            "separate Lean module and not an open-problems category).",
            "Done = listed in VERIFIED and deps done and file contains no `sorry`.",
            "Any `sorry` forces open/blocked regardless of VERIFIED.",
            "Hard edge B→A: A imports B (direct, submodule files only; barrel omitted).",
            "Drawn edges are transitively reduced; blocking still uses all direct imports.",
            "Paper kit goals: " + ", ".join(PAPER_KIT_GOALS) + ".",
            "Blue = done (proved, counterexample or refuted; no sorry). Green = open. Grey = blocked. "
            "Counterexample / refutation labels are shown as text on the node.",
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
    refute_n = [n for n in data["nodes"] if n.get("kind")]

    sec_title = {
        0: "Basic",
        1: "Top-level modules",
        2: "ExtTensorAlgebra",
        3: "Weight",
        4: "ProlongedBrownianSetup",
        5: "PriceFiltrationSignatureSpace",
        6: "SignatureVolatilityModel",
        99: "Root barrel",
        10: "NflvrDoubling subtasks",
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
        f"**`sorry` occurrences:** {data['sorryCount']} · "
        f"{len(open_n)} open · {len(blocked_n)} blocked · {len(done_n)} done · "
        f"{len(sorry_n)} file(s) with `sorry`.",
        f"**Paper claims refuted:** "
        f"{sum(1 for n in refute_n if n['kind'] == 'counterexample')} counterexample module(s) · "
        f"{sum(1 for n in refute_n if n['kind'] == 'refuted')} refuted theorem(s) · "
        f"{sum(1 for n in refute_n if n['kind'] == 'half-proved')} half-proved theorem(s). "
        "All are finished (no `sorry`) and counted as done.",
        "",
        "## The affine / Riccati `<-` direction is refuted",
        "",
        "The false theorem `affine_riccati_duality_mpr` has been removed from the library. "
        "Its negation `not_affine_riccati_duality_mpr` is proved sorry-free in "
        "`SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample`; "
        "`not_affine_riccati_duality`, `not_theorem_B_mpr` and `not_theorem_B` follow from it. "
        "All four are compared in `comparator.json` in unwrapped form (`…_unwrapped` in "
        "`Unwrapped`; see `Writeup/narratives/`). "
        "`Solution.lean` has **0** `sorry` (the Challenge's compared proofs are `sorry` by design). "
        "`theorem_B_mp` (martingale, the price-independent `AdmissibleGainsUnderP` NFLVR "
        "conjunct, special semimartingale, `->` Riccati direction) is sorry-free and compared "
        "as `theorem_B_mp_unwrapped`; `affine_riccati_duality_mp` is sorry-free and not compared.",
        "",
        *[f"- **`{nid}`**: {txt}" for nid, txt in OPEN_PROBLEMS.items()],
        "",
        "## Counterexamples and refuted paper claims",
        "",
        "| Kind | Label (module) | What is refuted | File |",
        "|---|---|---|---|",
        *[f"| **{n['kind']}** | **{n['label']}** (`{n['id']}`) | {n['detail']} | `{n['file']}` |"
          for n in sorted(refute_n, key=lambda x: (x['kind'], x['id']))],
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
    synth_n = [n for n in data["nodes"] if n.get("synthetic")]
    if synth_n:
        lines += [
            "",
            "## NflvrDoubling subtasks",
            "",
            "Internal structure of the doubling counterexample. These are not separate "
            "Lean modules. Finished pieces are ordinary done nodes with the landing "
            "commit; remaining work is ordinary open or blocked follow-on nodes.",
            "",
            "| Status | Id | Commit(s) | What |",
            "|---|---|---|---|",
        ]
        order = {item["id"]: i for i, item in enumerate(SYNTHETIC_NODES)}
        for n in sorted(synth_n, key=lambda x: order.get(x["id"], 10_000)):
            commits = n.get("commits") or "—"
            lines.append(
                f"| {n['status']} | `{n['id']}` | `{commits}` | {n['detail']} |"
            )
    lines += ["", "## By group", ""]
    for sec in sorted(by_sec):
        rows = sorted(by_sec[sec], key=lambda x: x["id"])
        holes = sum(1 for n in rows if n["status"] in ("open", "blocked"))
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
        + "\n# Synthetic NflvrDoubling subtask edges\n"
        + "\n".join(f"{frm} -hard-> {to}" for frm, to in SYNTHETIC_EDGES)
        + "\n",
        encoding="utf-8",
    )
    embed_html(data)
    open_n = sum(1 for n in data["nodes"] if n["status"] == "open")
    blocked_n = sum(1 for n in data["nodes"] if n["status"] == "blocked")
    done_n = sum(1 for n in data["nodes"] if n["status"] == "done")
    print(
        f"Wrote {OUT_JSON.name}, {OUT_MD.name}, embedded {OUT_HTML.name}: "
        f"{open_n} open, {blocked_n} blocked, {done_n} done, "
        f"({sum(1 for n in data['nodes'] if n.get('kind'))} labelled counterexample/refuted/half) "
        f"(sorryCount={data['sorryCount']})"
    )


if __name__ == "__main__":
    main()

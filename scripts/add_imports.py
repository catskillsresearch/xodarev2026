#!/usr/bin/env python3
"""Heuristic import injection for SignatureVolatility submodules."""
from pathlib import Path
import re

ROOT = Path("/home/catskills/Desktop/xodarev2026/SignatureVolatility")

# symbol -> module (without SignatureVolatility. prefix)
SYMBOL_MODULE: dict[str, str] = {}

DECL = re.compile(
    r"^(?:abbrev|structure|def|lemma|theorem|instance)\s+(\w+)|"
    r"^namespace\s+(\w+)",
    re.MULTILINE,
)


def collect_symbols():
    for f in sorted(ROOT.rglob("*.lean")):
        if f.name == "Basic.lean":
            continue
        rel = f.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
        text = f.read_text()
        for m in DECL.finditer(text):
            name = m.group(1) or m.group(2)
            if name and name not in SYMBOL_MODULE:
                SYMBOL_MODULE[name] = rel


# Extra tokens used in prose / dot notation
EXTRA = {
    "ExtTensorAlgebra": "ExtTensorAlgebra.ExtTensorAlgebra",
    "Weight": "Weight",
    "wordsOfLength": "WordsOfLength",
    "Word": "Word",
    "Letter": "Letter",
    "MemTw": "MemTw",
    "normW": "NormW",
    "normWDual": "NormWDual",
    "levelNormSq": "ExtTensorAlgebra.LevelNormSq",
    "levelNorm": "ExtTensorAlgebra.LevelNorm",
    "levelInner": "ExtTensorAlgebra.LevelInner",
    "basisWord": "ExtTensorAlgebra.BasisWord",
    "concat": "ExtTensorAlgebra.Concat",
    "projLe": "ProjLe",
    "projGt": "ProjGt",
    "dualPairing": "DualPairing",
    "generatedFiltration": "GeneratedFiltration",
    "smoothSignature": "SmoothSignature",
    "ProlongedBrownianSetup": "ProlongedBrownianSetup",
    "HypH2": "HypH2",
    "HypH1": "HypH1",
    "SignatureVolatilityModel": "SignatureVolatilityModel",
}
SYMBOL_MODULE.update(EXTRA)

# Topological tiers — import all lower tiers (crude but works for first compile)
TIERS = [
    ["Basic", "Preliminaries", "Letter", "Word", "WordsOfLength"],
    ["ExtTensorAlgebra.ExtTensorAlgebra"],
    [
        "ExtTensorAlgebra.BasisWord", "ExtTensorAlgebra.Coord", "ExtTensorAlgebra.LevelNormSq",
        "ExtTensorAlgebra.LevelNorm", "ExtTensorAlgebra.LevelInner", "ExtTensorAlgebra.IsFinitelySupported",
        "ExtTensorAlgebra.FreeTensorAlgebra", "ExtTensorAlgebra.Concat", "ExtTensorAlgebra.ShuffleWords",
        "ExtTensorAlgebra.ShuffleBasis", "ExtTensorAlgebra.EvalShuffleBasis", "ExtTensorAlgebra.Antipode",
    ],
    ["SmoothIteratedIntegral", "SmoothSignature", "IndexedFiltration", "GeneratedFiltration"],
    ["ProlongedBrownianSetup", "ProlongedBrownianSetup.WHat", "ProlongedBrownianSetup.WAug",
     "ProlongedBrownianSetup.BrownianFiltration", "ProlongedBrownianSetup.SignatureFiltration",
     "ChenIdentity", "ShuffleIdentity", "SignatureFiltrationEqBrownianFiltration"],
    ["Weight", "Weight.ConstOne", "Weight.Geometric"],
    ["MemTw", "NormW", "Tw", "MemTwDual", "NormWDual", "MemL2w", "Norm2w", "MemL2wInv", "Norm2wInv", "DualPairing"],
    ["ProjLe", "ProjGt", "HypH1", "HypH2", "HypH3", "SignatureVolatilityModel", "SignatureVolatilityModel.Sigma",
     "PriceFiltration"],
    [
        "RightShift", "StratonovichHalfLaplacian", "ShuffleFinite", "RiccatiOpBounded", "ClassicalRiccatiSolution",
        "Remark219BlackScholesRiccati", "ItoCalculusKit", "Lemma32SignatureInTw", "Corollary36SigmaWellDefined",
        "SignaturePriceSolution", "TheoremA", "PureBrownianWord", "SuperfactorialFunctional",
        "Proposition311SharpnessOfH1", "SatisfiesNFLVR", "AdmissibleGainsUnderP", "NflvrOfMartingaleMeasure",
        "IsSpecialSemimartingale", "SignatureRiccatiKit", "TheoremB",
    ],
    ["PriceFiltrationSignatureSpace", "PriceFiltrationSignatureSpace.VSubspace", "PriceFiltrationSignatureSpace.VInfty",
     "PriceFiltrationSignatureSpace.CompletenessDepth", "PriceFiltrationSignatureSpace.AugmentedMarketSpan",
     "PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration", "TheoremC", "GKWDecompositionSetup",
     "Lemma61GramPosDef", "Proposition65NormalEquations", "TheoremD", "HypH1OfIsFinitelySupported"],
    ["BlackScholesModel", "FirstOrderBrownianVolModel", "SignatureHestonLevel2Model", "QuinticOUSignatureModel",
     "InfiniteGeometricSignatureModel", "Section71BlackScholesCompleteness"],
    [
        "BanachAlgebraConcatBound", "DualPairingLeNormWDualMulNormW", "WeightedTruncationEstimates",
        "TailNorm2wInvLeRatioMulNormW", "MemTwDualOfMemL2w", "MemL2wInvOfMemTw",
        "PriceFiltrationLeSignatureFiltration", "HypH2.GeometricAdmissible", "HypH2.ConstOneAdmissible",
        "HypH2.SubfactorialNonneg", "Weight.InvLeOne", "Weight.OneLe",
    ],
]

MODULE_TIER = {}
for i, tier in enumerate(TIERS):
    for m in tier:
        MODULE_TIER[m] = i


def module_name(f: Path) -> str:
    return f.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def main():
    collect_symbols()
    for f in sorted(ROOT.rglob("*.lean")):
        if f.name == "Basic.lean":
            continue
        mod = module_name(f)
        tier = MODULE_TIER.get(mod, 5)
        imports = {"SignatureVolatility.Basic"}
        for m, t in MODULE_TIER.items():
            if t < tier and m != mod:
                imports.add(f"SignatureVolatility.{m}")
        if mod != "Preliminaries":
            imports.add("SignatureVolatility.Preliminaries")
        text = f.read_text()
        lines = text.splitlines()
        start = 0
        while start < len(lines) and (
            lines[start].startswith("import ") or lines[start].startswith("SignatureVolatility.")
        ):
            start += 1
        body = "\n".join(lines[start:]).lstrip("\n")
        header = "\n".join(f"import {x}" for x in sorted(imports)) + "\n\n"
        f.write_text(header + body)
    print("Imports injected.")


if __name__ == "__main__":
    main()
# Proof holes (Xodarev / SignatureVolatility)

File-level inventory of Lean modules. **Everything is unverified TBD** until listed in `VERIFIED` in `scripts/build_holes.py`.

**Updated:** 2026-11-21T03:28:08Z
**Holes:** 5 open+blocked · 5 open · 0 blocked · 89 done.

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, embeds into holes.html
scripts/serve_holes.sh          # http://127.0.0.1:8766/holes.html
```

## Open now (Layer 0)

| Id | File |
|---|---|
| `Corollary36SigmaWellDefined` | `SignatureVolatility/Corollary36SigmaWellDefined.lean` |
| `TheoremA` | `SignatureVolatility/TheoremA.lean` |
| `TheoremB` | `SignatureVolatility/TheoremB.lean` |
| `TheoremC` | `SignatureVolatility/TheoremC.lean` |
| `TheoremD` | `SignatureVolatility/TheoremD.lean` |

## By group

### Top-level modules — 5 hole(s)

| Status | Id | File |
|---|---|---|
| done | `AdmissibleGainsUnderP` | `SignatureVolatility/AdmissibleGainsUnderP.lean` |
| done | `BanachAlgebraConcatBound` | `SignatureVolatility/BanachAlgebraConcatBound.lean` |
| done | `BlackScholesModel` | `SignatureVolatility/BlackScholesModel.lean` |
| done | `ChenIdentity` | `SignatureVolatility/ChenIdentity.lean` |
| done | `ClassicalRiccatiSolution` | `SignatureVolatility/ClassicalRiccatiSolution.lean` |
| open | `Corollary36SigmaWellDefined` | `SignatureVolatility/Corollary36SigmaWellDefined.lean` |
| done | `DualPairing` | `SignatureVolatility/DualPairing.lean` |
| done | `DualPairingLeNormWDualMulNormW` | `SignatureVolatility/DualPairingLeNormWDualMulNormW.lean` |
| done | `FirstOrderBrownianVolModel` | `SignatureVolatility/FirstOrderBrownianVolModel.lean` |
| done | `GKWDecompositionSetup` | `SignatureVolatility/GKWDecompositionSetup.lean` |
| done | `GeneratedFiltration` | `SignatureVolatility/GeneratedFiltration.lean` |
| done | `HypH1` | `SignatureVolatility/HypH1.lean` |
| done | `HypH1OfIsFinitelySupported` | `SignatureVolatility/HypH1OfIsFinitelySupported.lean` |
| done | `HypH2` | `SignatureVolatility/HypH2.lean` |
| done | `HypH3` | `SignatureVolatility/HypH3.lean` |
| done | `IndexedFiltration` | `SignatureVolatility/IndexedFiltration.lean` |
| done | `InfiniteGeometricSignatureModel` | `SignatureVolatility/InfiniteGeometricSignatureModel.lean` |
| done | `IsSpecialSemimartingale` | `SignatureVolatility/IsSpecialSemimartingale.lean` |
| done | `ItoCalculusKit` | `SignatureVolatility/ItoCalculusKit.lean` |
| done | `Lemma32SignatureInTw` | `SignatureVolatility/Lemma32SignatureInTw.lean` |
| done | `Lemma61GramPosDef` | `SignatureVolatility/Lemma61GramPosDef.lean` |
| done | `Letter` | `SignatureVolatility/Letter.lean` |
| done | `MemL2w` | `SignatureVolatility/MemL2w.lean` |
| done | `MemL2wInv` | `SignatureVolatility/MemL2wInv.lean` |
| done | `MemL2wInvOfMemTw` | `SignatureVolatility/MemL2wInvOfMemTw.lean` |
| done | `MemTw` | `SignatureVolatility/MemTw.lean` |
| done | `MemTwDual` | `SignatureVolatility/MemTwDual.lean` |
| done | `MemTwDualOfMemL2w` | `SignatureVolatility/MemTwDualOfMemL2w.lean` |
| done | `NflvrOfMartingaleMeasure` | `SignatureVolatility/NflvrOfMartingaleMeasure.lean` |
| done | `Norm2w` | `SignatureVolatility/Norm2w.lean` |
| done | `Norm2wInv` | `SignatureVolatility/Norm2wInv.lean` |
| done | `NormW` | `SignatureVolatility/NormW.lean` |
| done | `NormWDual` | `SignatureVolatility/NormWDual.lean` |
| done | `Preliminaries` | `SignatureVolatility/Preliminaries.lean` |
| done | `PriceFiltration` | `SignatureVolatility/PriceFiltration.lean` |
| done | `PriceFiltrationSignatureSpace` | `SignatureVolatility/PriceFiltrationSignatureSpace.lean` |
| done | `ProjGt` | `SignatureVolatility/ProjGt.lean` |
| done | `ProjLe` | `SignatureVolatility/ProjLe.lean` |
| done | `ProlongedBrownianSetup` | `SignatureVolatility/ProlongedBrownianSetup.lean` |
| done | `Proposition311SharpnessOfH1` | `SignatureVolatility/Proposition311SharpnessOfH1.lean` |
| done | `Proposition65NormalEquations` | `SignatureVolatility/Proposition65NormalEquations.lean` |
| done | `PureBrownianWord` | `SignatureVolatility/PureBrownianWord.lean` |
| done | `QuinticOUSignatureModel` | `SignatureVolatility/QuinticOUSignatureModel.lean` |
| done | `Remark219BlackScholesRiccati` | `SignatureVolatility/Remark219BlackScholesRiccati.lean` |
| done | `RiccatiOpBounded` | `SignatureVolatility/RiccatiOpBounded.lean` |
| done | `RightShift` | `SignatureVolatility/RightShift.lean` |
| done | `SatisfiesNFLVR` | `SignatureVolatility/SatisfiesNFLVR.lean` |
| done | `Section71BlackScholesCompleteness` | `SignatureVolatility/Section71BlackScholesCompleteness.lean` |
| done | `ShuffleFinite` | `SignatureVolatility/ShuffleFinite.lean` |
| done | `ShuffleIdentity` | `SignatureVolatility/ShuffleIdentity.lean` |
| done | `SignatureFiltrationEqBrownianFiltration` | `SignatureVolatility/SignatureFiltrationEqBrownianFiltration.lean` |
| done | `SignatureHestonLevel2Model` | `SignatureVolatility/SignatureHestonLevel2Model.lean` |
| done | `SignaturePriceSolution` | `SignatureVolatility/SignaturePriceSolution.lean` |
| done | `SignatureRiccatiKit` | `SignatureVolatility/SignatureRiccatiKit.lean` |
| done | `SignatureVolatilityModel` | `SignatureVolatility/SignatureVolatilityModel.lean` |
| done | `SmoothIteratedIntegral` | `SignatureVolatility/SmoothIteratedIntegral.lean` |
| done | `SmoothSignature` | `SignatureVolatility/SmoothSignature.lean` |
| done | `StratonovichHalfLaplacian` | `SignatureVolatility/StratonovichHalfLaplacian.lean` |
| done | `SuperfactorialFunctional` | `SignatureVolatility/SuperfactorialFunctional.lean` |
| done | `TailNorm2wInvLeRatioMulNormW` | `SignatureVolatility/TailNorm2wInvLeRatioMulNormW.lean` |
| open | `TheoremA` | `SignatureVolatility/TheoremA.lean` |
| open | `TheoremB` | `SignatureVolatility/TheoremB.lean` |
| open | `TheoremC` | `SignatureVolatility/TheoremC.lean` |
| open | `TheoremD` | `SignatureVolatility/TheoremD.lean` |
| done | `Tw` | `SignatureVolatility/Tw.lean` |
| done | `Weight` | `SignatureVolatility/Weight.lean` |
| done | `WeightedTruncationEstimates` | `SignatureVolatility/WeightedTruncationEstimates.lean` |
| done | `Word` | `SignatureVolatility/Word.lean` |
| done | `WordsOfLength` | `SignatureVolatility/WordsOfLength.lean` |

### ExtTensorAlgebra — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `ExtTensorAlgebra.Antipode` | `SignatureVolatility/ExtTensorAlgebra/Antipode.lean` |
| done | `ExtTensorAlgebra.BasisWord` | `SignatureVolatility/ExtTensorAlgebra/BasisWord.lean` |
| done | `ExtTensorAlgebra.Concat` | `SignatureVolatility/ExtTensorAlgebra/Concat.lean` |
| done | `ExtTensorAlgebra.Coord` | `SignatureVolatility/ExtTensorAlgebra/Coord.lean` |
| done | `ExtTensorAlgebra.EvalShuffleBasis` | `SignatureVolatility/ExtTensorAlgebra/EvalShuffleBasis.lean` |
| done | `ExtTensorAlgebra.ExtTensorAlgebra` | `SignatureVolatility/ExtTensorAlgebra/ExtTensorAlgebra.lean` |
| done | `ExtTensorAlgebra.FreeTensorAlgebra` | `SignatureVolatility/ExtTensorAlgebra/FreeTensorAlgebra.lean` |
| done | `ExtTensorAlgebra.IsFinitelySupported` | `SignatureVolatility/ExtTensorAlgebra/IsFinitelySupported.lean` |
| done | `ExtTensorAlgebra.LevelInner` | `SignatureVolatility/ExtTensorAlgebra/LevelInner.lean` |
| done | `ExtTensorAlgebra.LevelNorm` | `SignatureVolatility/ExtTensorAlgebra/LevelNorm.lean` |
| done | `ExtTensorAlgebra.LevelNormSq` | `SignatureVolatility/ExtTensorAlgebra/LevelNormSq.lean` |
| done | `ExtTensorAlgebra.ShuffleBasis` | `SignatureVolatility/ExtTensorAlgebra/ShuffleBasis.lean` |
| done | `ExtTensorAlgebra.ShuffleWords` | `SignatureVolatility/ExtTensorAlgebra/ShuffleWords.lean` |

### Weight — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `Weight.ConstOne` | `SignatureVolatility/Weight/ConstOne.lean` |
| done | `Weight.Geometric` | `SignatureVolatility/Weight/Geometric.lean` |

### ProlongedBrownianSetup — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `ProlongedBrownianSetup.BrownianFiltration` | `SignatureVolatility/ProlongedBrownianSetup/BrownianFiltration.lean` |
| done | `ProlongedBrownianSetup.SignatureFiltration` | `SignatureVolatility/ProlongedBrownianSetup/SignatureFiltration.lean` |
| done | `ProlongedBrownianSetup.WAug` | `SignatureVolatility/ProlongedBrownianSetup/WAug.lean` |
| done | `ProlongedBrownianSetup.WHat` | `SignatureVolatility/ProlongedBrownianSetup/WHat.lean` |

### PriceFiltrationSignatureSpace — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `PriceFiltrationSignatureSpace.AugmentedMarketSpan` | `SignatureVolatility/PriceFiltrationSignatureSpace/AugmentedMarketSpan.lean` |
| done | `PriceFiltrationSignatureSpace.CompletenessDepth` | `SignatureVolatility/PriceFiltrationSignatureSpace/CompletenessDepth.lean` |
| done | `PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration` | `SignatureVolatility/PriceFiltrationSignatureSpace/IsCompleteOnPriceFiltration.lean` |
| done | `PriceFiltrationSignatureSpace.VInfty` | `SignatureVolatility/PriceFiltrationSignatureSpace/VInfty.lean` |
| done | `PriceFiltrationSignatureSpace.VSubspace` | `SignatureVolatility/PriceFiltrationSignatureSpace/VSubspace.lean` |

### SignatureVolatilityModel — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `SignatureVolatilityModel.Sigma` | `SignatureVolatility/SignatureVolatilityModel/Sigma.lean` |

## Dependency sketch

Direct import-deps: `holes-edges.txt`. Display graph uses transitive reduction. Open [`holes.html`](holes.html) for the interactive board.


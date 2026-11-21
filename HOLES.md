# Proof holes (Xodarev / SignatureVolatility)

File-level inventory of Lean modules. **Everything is unverified TBD** until listed in `VERIFIED` in `scripts/build_holes.py`.

**Updated:** 2026-11-21T01:50:36Z
**Holes:** 93 open+blocked · 5 open · 88 blocked · 2 done.

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, embeds into holes.html
scripts/serve_holes.sh          # http://127.0.0.1:8766/holes.html
```

## Open now (Layer 0)

| Id | File |
|---|---|
| `IndexedFiltration` | `SignatureVolatility/IndexedFiltration.lean` |
| `Letter` | `SignatureVolatility/Letter.lean` |
| `NflvrOfMartingaleMeasure` | `SignatureVolatility/NflvrOfMartingaleMeasure.lean` |
| `Preliminaries` | `SignatureVolatility/Preliminaries.lean` |
| `Weight` | `SignatureVolatility/Weight.lean` |

## By group

### Top-level modules — 67 hole(s)

| Status | Id | File |
|---|---|---|
| done | `AdmissibleGainsUnderP` | `SignatureVolatility/AdmissibleGainsUnderP.lean` |
| blocked | `BanachAlgebraConcatBound` | `SignatureVolatility/BanachAlgebraConcatBound.lean` |
| blocked | `BlackScholesModel` | `SignatureVolatility/BlackScholesModel.lean` |
| blocked | `ChenIdentity` | `SignatureVolatility/ChenIdentity.lean` |
| blocked | `ClassicalRiccatiSolution` | `SignatureVolatility/ClassicalRiccatiSolution.lean` |
| blocked | `Corollary36SigmaWellDefined` | `SignatureVolatility/Corollary36SigmaWellDefined.lean` |
| blocked | `DualPairing` | `SignatureVolatility/DualPairing.lean` |
| blocked | `DualPairingLeNormWDualMulNormW` | `SignatureVolatility/DualPairingLeNormWDualMulNormW.lean` |
| blocked | `FirstOrderBrownianVolModel` | `SignatureVolatility/FirstOrderBrownianVolModel.lean` |
| blocked | `GKWDecompositionSetup` | `SignatureVolatility/GKWDecompositionSetup.lean` |
| blocked | `GeneratedFiltration` | `SignatureVolatility/GeneratedFiltration.lean` |
| blocked | `HypH1` | `SignatureVolatility/HypH1.lean` |
| blocked | `HypH1OfIsFinitelySupported` | `SignatureVolatility/HypH1OfIsFinitelySupported.lean` |
| blocked | `HypH2` | `SignatureVolatility/HypH2.lean` |
| blocked | `HypH3` | `SignatureVolatility/HypH3.lean` |
| open | `IndexedFiltration` | `SignatureVolatility/IndexedFiltration.lean` |
| blocked | `InfiniteGeometricSignatureModel` | `SignatureVolatility/InfiniteGeometricSignatureModel.lean` |
| blocked | `IsSpecialSemimartingale` | `SignatureVolatility/IsSpecialSemimartingale.lean` |
| blocked | `ItoCalculusKit` | `SignatureVolatility/ItoCalculusKit.lean` |
| blocked | `Lemma32SignatureInTw` | `SignatureVolatility/Lemma32SignatureInTw.lean` |
| blocked | `Lemma61GramPosDef` | `SignatureVolatility/Lemma61GramPosDef.lean` |
| open | `Letter` | `SignatureVolatility/Letter.lean` |
| blocked | `MemL2w` | `SignatureVolatility/MemL2w.lean` |
| blocked | `MemL2wInv` | `SignatureVolatility/MemL2wInv.lean` |
| blocked | `MemL2wInvOfMemTw` | `SignatureVolatility/MemL2wInvOfMemTw.lean` |
| blocked | `MemTw` | `SignatureVolatility/MemTw.lean` |
| blocked | `MemTwDual` | `SignatureVolatility/MemTwDual.lean` |
| blocked | `MemTwDualOfMemL2w` | `SignatureVolatility/MemTwDualOfMemL2w.lean` |
| open | `NflvrOfMartingaleMeasure` | `SignatureVolatility/NflvrOfMartingaleMeasure.lean` |
| blocked | `Norm2w` | `SignatureVolatility/Norm2w.lean` |
| blocked | `Norm2wInv` | `SignatureVolatility/Norm2wInv.lean` |
| blocked | `NormW` | `SignatureVolatility/NormW.lean` |
| blocked | `NormWDual` | `SignatureVolatility/NormWDual.lean` |
| open | `Preliminaries` | `SignatureVolatility/Preliminaries.lean` |
| blocked | `PriceFiltration` | `SignatureVolatility/PriceFiltration.lean` |
| blocked | `PriceFiltrationSignatureSpace` | `SignatureVolatility/PriceFiltrationSignatureSpace.lean` |
| blocked | `ProjGt` | `SignatureVolatility/ProjGt.lean` |
| blocked | `ProjLe` | `SignatureVolatility/ProjLe.lean` |
| blocked | `ProlongedBrownianSetup` | `SignatureVolatility/ProlongedBrownianSetup.lean` |
| blocked | `Proposition311SharpnessOfH1` | `SignatureVolatility/Proposition311SharpnessOfH1.lean` |
| blocked | `Proposition65NormalEquations` | `SignatureVolatility/Proposition65NormalEquations.lean` |
| blocked | `PureBrownianWord` | `SignatureVolatility/PureBrownianWord.lean` |
| blocked | `QuinticOUSignatureModel` | `SignatureVolatility/QuinticOUSignatureModel.lean` |
| blocked | `Remark219BlackScholesRiccati` | `SignatureVolatility/Remark219BlackScholesRiccati.lean` |
| blocked | `RiccatiOpBounded` | `SignatureVolatility/RiccatiOpBounded.lean` |
| blocked | `RightShift` | `SignatureVolatility/RightShift.lean` |
| done | `SatisfiesNFLVR` | `SignatureVolatility/SatisfiesNFLVR.lean` |
| blocked | `Section71BlackScholesCompleteness` | `SignatureVolatility/Section71BlackScholesCompleteness.lean` |
| blocked | `ShuffleFinite` | `SignatureVolatility/ShuffleFinite.lean` |
| blocked | `ShuffleIdentity` | `SignatureVolatility/ShuffleIdentity.lean` |
| blocked | `SignatureFiltrationEqBrownianFiltration` | `SignatureVolatility/SignatureFiltrationEqBrownianFiltration.lean` |
| blocked | `SignatureHestonLevel2Model` | `SignatureVolatility/SignatureHestonLevel2Model.lean` |
| blocked | `SignaturePriceSolution` | `SignatureVolatility/SignaturePriceSolution.lean` |
| blocked | `SignatureRiccatiKit` | `SignatureVolatility/SignatureRiccatiKit.lean` |
| blocked | `SignatureVolatilityModel` | `SignatureVolatility/SignatureVolatilityModel.lean` |
| blocked | `SmoothIteratedIntegral` | `SignatureVolatility/SmoothIteratedIntegral.lean` |
| blocked | `SmoothSignature` | `SignatureVolatility/SmoothSignature.lean` |
| blocked | `StratonovichHalfLaplacian` | `SignatureVolatility/StratonovichHalfLaplacian.lean` |
| blocked | `SuperfactorialFunctional` | `SignatureVolatility/SuperfactorialFunctional.lean` |
| blocked | `TailNorm2wInvLeRatioMulNormW` | `SignatureVolatility/TailNorm2wInvLeRatioMulNormW.lean` |
| blocked | `TheoremA` | `SignatureVolatility/TheoremA.lean` |
| blocked | `TheoremB` | `SignatureVolatility/TheoremB.lean` |
| blocked | `TheoremC` | `SignatureVolatility/TheoremC.lean` |
| blocked | `TheoremD` | `SignatureVolatility/TheoremD.lean` |
| blocked | `Tw` | `SignatureVolatility/Tw.lean` |
| open | `Weight` | `SignatureVolatility/Weight.lean` |
| blocked | `WeightedTruncationEstimates` | `SignatureVolatility/WeightedTruncationEstimates.lean` |
| blocked | `Word` | `SignatureVolatility/Word.lean` |
| blocked | `WordsOfLength` | `SignatureVolatility/WordsOfLength.lean` |

### ExtTensorAlgebra — 13 hole(s)

| Status | Id | File |
|---|---|---|
| blocked | `ExtTensorAlgebra.Antipode` | `SignatureVolatility/ExtTensorAlgebra/Antipode.lean` |
| blocked | `ExtTensorAlgebra.BasisWord` | `SignatureVolatility/ExtTensorAlgebra/BasisWord.lean` |
| blocked | `ExtTensorAlgebra.Concat` | `SignatureVolatility/ExtTensorAlgebra/Concat.lean` |
| blocked | `ExtTensorAlgebra.Coord` | `SignatureVolatility/ExtTensorAlgebra/Coord.lean` |
| blocked | `ExtTensorAlgebra.EvalShuffleBasis` | `SignatureVolatility/ExtTensorAlgebra/EvalShuffleBasis.lean` |
| blocked | `ExtTensorAlgebra.ExtTensorAlgebra` | `SignatureVolatility/ExtTensorAlgebra/ExtTensorAlgebra.lean` |
| blocked | `ExtTensorAlgebra.FreeTensorAlgebra` | `SignatureVolatility/ExtTensorAlgebra/FreeTensorAlgebra.lean` |
| blocked | `ExtTensorAlgebra.IsFinitelySupported` | `SignatureVolatility/ExtTensorAlgebra/IsFinitelySupported.lean` |
| blocked | `ExtTensorAlgebra.LevelInner` | `SignatureVolatility/ExtTensorAlgebra/LevelInner.lean` |
| blocked | `ExtTensorAlgebra.LevelNorm` | `SignatureVolatility/ExtTensorAlgebra/LevelNorm.lean` |
| blocked | `ExtTensorAlgebra.LevelNormSq` | `SignatureVolatility/ExtTensorAlgebra/LevelNormSq.lean` |
| blocked | `ExtTensorAlgebra.ShuffleBasis` | `SignatureVolatility/ExtTensorAlgebra/ShuffleBasis.lean` |
| blocked | `ExtTensorAlgebra.ShuffleWords` | `SignatureVolatility/ExtTensorAlgebra/ShuffleWords.lean` |

### Weight — 2 hole(s)

| Status | Id | File |
|---|---|---|
| blocked | `Weight.ConstOne` | `SignatureVolatility/Weight/ConstOne.lean` |
| blocked | `Weight.Geometric` | `SignatureVolatility/Weight/Geometric.lean` |

### ProlongedBrownianSetup — 4 hole(s)

| Status | Id | File |
|---|---|---|
| blocked | `ProlongedBrownianSetup.BrownianFiltration` | `SignatureVolatility/ProlongedBrownianSetup/BrownianFiltration.lean` |
| blocked | `ProlongedBrownianSetup.SignatureFiltration` | `SignatureVolatility/ProlongedBrownianSetup/SignatureFiltration.lean` |
| blocked | `ProlongedBrownianSetup.WAug` | `SignatureVolatility/ProlongedBrownianSetup/WAug.lean` |
| blocked | `ProlongedBrownianSetup.WHat` | `SignatureVolatility/ProlongedBrownianSetup/WHat.lean` |

### PriceFiltrationSignatureSpace — 5 hole(s)

| Status | Id | File |
|---|---|---|
| blocked | `PriceFiltrationSignatureSpace.AugmentedMarketSpan` | `SignatureVolatility/PriceFiltrationSignatureSpace/AugmentedMarketSpan.lean` |
| blocked | `PriceFiltrationSignatureSpace.CompletenessDepth` | `SignatureVolatility/PriceFiltrationSignatureSpace/CompletenessDepth.lean` |
| blocked | `PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration` | `SignatureVolatility/PriceFiltrationSignatureSpace/IsCompleteOnPriceFiltration.lean` |
| blocked | `PriceFiltrationSignatureSpace.VInfty` | `SignatureVolatility/PriceFiltrationSignatureSpace/VInfty.lean` |
| blocked | `PriceFiltrationSignatureSpace.VSubspace` | `SignatureVolatility/PriceFiltrationSignatureSpace/VSubspace.lean` |

### SignatureVolatilityModel — 1 hole(s)

| Status | Id | File |
|---|---|---|
| blocked | `SignatureVolatilityModel.Sigma` | `SignatureVolatility/SignatureVolatilityModel/Sigma.lean` |

### Root barrel — 1 hole(s)

| Status | Id | File |
|---|---|---|
| blocked | `(root)` | `SignatureVolatility.lean` |

## Dependency sketch

Hard edges follow Lean `import SignatureVolatility…` (see `holes-edges.txt`). Open [`holes.html`](holes.html) for the interactive board.


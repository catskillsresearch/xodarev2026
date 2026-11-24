# Proof holes (Xodarev / SignatureVolatility)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`.

**Updated:** 2026-11-24T09:09:57Z
**Holes:** 42 open+blocked · 1 open · 41 blocked · 144 done · 4 file(s) with `sorry`.

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, embeds into holes.html
scripts/serve_holes.sh          # http://127.0.0.1:8766/holes.html
```

## Paper kit / theorem goals (before Challenge rewrite)

These must be sorry-free at **paper strength** (nontrivial Itô kit, Stratonovich signature, Riccati duality, Davis–Obłój PFS, GKW) before updating Palomar Challenge / `formalization.yaml`.

| Status | Id | `sorry`? | File |
|---|---|---|---|
| blocked | `GKWDecompositionSetup.OfPFS` | yes | `SignatureVolatility/GKWDecompositionSetup/OfPFS.lean` |
| blocked | `ItoCalculusKit.OfMathFin` | no | `SignatureVolatility/ItoCalculusKit/OfMathFin.lean` |
| blocked | `PriceFiltrationSignatureSpace.OfMarket` | yes | `SignatureVolatility/PriceFiltrationSignatureSpace/OfMarket.lean` |
| blocked | `ProlongedBrownianSetup.StratonovichOfBM` | no | `SignatureVolatility/ProlongedBrownianSetup/StratonovichOfBM.lean` |
| blocked | `SignatureRiccatiKit.OfSetup` | yes | `SignatureVolatility/SignatureRiccatiKit/OfSetup.lean` |
| blocked | `TheoremA` | no | `SignatureVolatility/TheoremA.lean` |
| blocked | `TheoremB` | no | `SignatureVolatility/TheoremB.lean` |
| blocked | `TheoremC` | no | `SignatureVolatility/TheoremC.lean` |
| blocked | `TheoremD` | no | `SignatureVolatility/TheoremD.lean` |

## Files with `sorry`

| Status | Id | File |
|---|---|---|
| blocked | `GKWDecompositionSetup.OfPFS` | `SignatureVolatility/GKWDecompositionSetup/OfPFS.lean` |
| blocked | `PriceFiltrationSignatureSpace.OfMarket` | `SignatureVolatility/PriceFiltrationSignatureSpace/OfMarket.lean` |
| open | `ProlongedBrownianSetup.PaperSigChen` | `SignatureVolatility/ProlongedBrownianSetup/PaperSigChen.lean` |
| blocked | `SignatureRiccatiKit.OfSetup` | `SignatureVolatility/SignatureRiccatiKit/OfSetup.lean` |

## Open now (Layer 0)

| Id | File |
|---|---|
| `ProlongedBrownianSetup.PaperSigChen` | `SignatureVolatility/ProlongedBrownianSetup/PaperSigChen.lean` |

## By group

### Top-level modules — 39 hole(s)

| Status | Id | File |
|---|---|---|
| done | `AdmissibleGainsUnderP` | `SignatureVolatility/AdmissibleGainsUnderP.lean` |
| done | `BanachAlgebraConcatBound` | `SignatureVolatility/BanachAlgebraConcatBound.lean` |
| done | `BlackScholesModel` | `SignatureVolatility/BlackScholesModel.lean` |
| done | `ChenIdentity` | `SignatureVolatility/ChenIdentity.lean` |
| done | `ClassicalRiccatiSolution` | `SignatureVolatility/ClassicalRiccatiSolution.lean` |
| done | `Corollary36SigmaWellDefined` | `SignatureVolatility/Corollary36SigmaWellDefined.lean` |
| done | `DualPairing` | `SignatureVolatility/DualPairing.lean` |
| done | `DualPairingLeNormWDualMulNormW` | `SignatureVolatility/DualPairingLeNormWDualMulNormW.lean` |
| done | `FirstOrderBrownianVolModel` | `SignatureVolatility/FirstOrderBrownianVolModel.lean` |
| done | `GKWDecompositionSetup` | `SignatureVolatility/GKWDecompositionSetup.lean` |
| blocked | `GKWDecompositionSetup.OfPFS` | `SignatureVolatility/GKWDecompositionSetup/OfPFS.lean` |
| done | `GeneratedFiltration` | `SignatureVolatility/GeneratedFiltration.lean` |
| done | `HypH1` | `SignatureVolatility/HypH1.lean` |
| done | `HypH1OfIsFinitelySupported` | `SignatureVolatility/HypH1OfIsFinitelySupported.lean` |
| done | `HypH2` | `SignatureVolatility/HypH2.lean` |
| done | `HypH3` | `SignatureVolatility/HypH3.lean` |
| done | `IndexedFiltration` | `SignatureVolatility/IndexedFiltration.lean` |
| done | `InfiniteGeometricSignatureModel` | `SignatureVolatility/InfiniteGeometricSignatureModel.lean` |
| done | `IsSpecialSemimartingale` | `SignatureVolatility/IsSpecialSemimartingale.lean` |
| done | `ItoCalculusKit` | `SignatureVolatility/ItoCalculusKit.lean` |
| done | `ItoCalculusKit.BrownianQuadVarAS` | `SignatureVolatility/ItoCalculusKit/BrownianQuadVarAS.lean` |
| done | `ItoCalculusKit.ConstVol` | `SignatureVolatility/ItoCalculusKit/ConstVol.lean` |
| done | `ItoCalculusKit.CrossVariation` | `SignatureVolatility/ItoCalculusKit/CrossVariation.lean` |
| blocked | `ItoCalculusKit.DoleansEnvelope` | `SignatureVolatility/ItoCalculusKit/DoleansEnvelope.lean` |
| blocked | `ItoCalculusKit.DoleansErrorPathwise` | `SignatureVolatility/ItoCalculusKit/DoleansErrorPathwise.lean` |
| blocked | `ItoCalculusKit.DoleansIdentify` | `SignatureVolatility/ItoCalculusKit/DoleansIdentify.lean` |
| blocked | `ItoCalculusKit.DoleansInputs` | `SignatureVolatility/ItoCalculusKit/DoleansInputs.lean` |
| blocked | `ItoCalculusKit.DoleansMoments` | `SignatureVolatility/ItoCalculusKit/DoleansMoments.lean` |
| blocked | `ItoCalculusKit.DoleansQV` | `SignatureVolatility/ItoCalculusKit/DoleansQV.lean` |
| blocked | `ItoCalculusKit.DoleansSDE` | `SignatureVolatility/ItoCalculusKit/DoleansSDE.lean` |
| blocked | `ItoCalculusKit.DoleansSigma` | `SignatureVolatility/ItoCalculusKit/DoleansSigma.lean` |
| blocked | `ItoCalculusKit.DoleansStrongClass` | `SignatureVolatility/ItoCalculusKit/DoleansStrongClass.lean` |
| done | `ItoCalculusKit.DoobEnvelope` | `SignatureVolatility/ItoCalculusKit/DoobEnvelope.lean` |
| done | `ItoCalculusKit.EighthMoment` | `SignatureVolatility/ItoCalculusKit/EighthMoment.lean` |
| blocked | `ItoCalculusKit.EighthTransform` | `SignatureVolatility/ItoCalculusKit/EighthTransform.lean` |
| done | `ItoCalculusKit.EvenMoment` | `SignatureVolatility/ItoCalculusKit/EvenMoment.lean` |
| done | `ItoCalculusKit.EvenTransform` | `SignatureVolatility/ItoCalculusKit/EvenTransform.lean` |
| done | `ItoCalculusKit.ExpSupermartingale` | `SignatureVolatility/ItoCalculusKit/ExpSupermartingale.lean` |
| done | `ItoCalculusKit.FourthMoment` | `SignatureVolatility/ItoCalculusKit/FourthMoment.lean` |
| done | `ItoCalculusKit.FrozenIncrement4` | `SignatureVolatility/ItoCalculusKit/FrozenIncrement4.lean` |
| blocked | `ItoCalculusKit.FrozenIncrement8` | `SignatureVolatility/ItoCalculusKit/FrozenIncrement8.lean` |
| blocked | `ItoCalculusKit.FrozenOrthogonal` | `SignatureVolatility/ItoCalculusKit/FrozenOrthogonal.lean` |
| done | `ItoCalculusKit.GBMEnvelope` | `SignatureVolatility/ItoCalculusKit/GBMEnvelope.lean` |
| done | `ItoCalculusKit.GBMMartingale` | `SignatureVolatility/ItoCalculusKit/GBMMartingale.lean` |
| done | `ItoCalculusKit.GridChange` | `SignatureVolatility/ItoCalculusKit/GridChange.lean` |
| blocked | `ItoCalculusKit.GridDoob` | `SignatureVolatility/ItoCalculusKit/GridDoob.lean` |
| blocked | `ItoCalculusKit.HolderPath` | `SignatureVolatility/ItoCalculusKit/HolderPath.lean` |
| done | `ItoCalculusKit.ItoIncrement` | `SignatureVolatility/ItoCalculusKit/ItoIncrement.lean` |
| blocked | `ItoCalculusKit.ItoIncrement8` | `SignatureVolatility/ItoCalculusKit/ItoIncrement8.lean` |
| done | `ItoCalculusKit.ItoIncrementEven` | `SignatureVolatility/ItoCalculusKit/ItoIncrementEven.lean` |
| done | `ItoCalculusKit.ItoOrthogonal` | `SignatureVolatility/ItoCalculusKit/ItoOrthogonal.lean` |
| blocked | `ItoCalculusKit.ItoQuadDoleans` | `SignatureVolatility/ItoCalculusKit/ItoQuadDoleans.lean` |
| done | `ItoCalculusKit.JointPast` | `SignatureVolatility/ItoCalculusKit/JointPast.lean` |
| done | `ItoCalculusKit.KitRaw` | `SignatureVolatility/ItoCalculusKit/KitRaw.lean` |
| blocked | `ItoCalculusKit.KolmogorovIto` | `SignatureVolatility/ItoCalculusKit/KolmogorovIto.lean` |
| done | `ItoCalculusKit.LebIncrementEven` | `SignatureVolatility/ItoCalculusKit/LebIncrementEven.lean` |
| done | `ItoCalculusKit.LevelBounds` | `SignatureVolatility/ItoCalculusKit/LevelBounds.lean` |
| done | `ItoCalculusKit.LevelDecay` | `SignatureVolatility/ItoCalculusKit/LevelDecay.lean` |
| blocked | `ItoCalculusKit.LogDoleansIncrement` | `SignatureVolatility/ItoCalculusKit/LogDoleansIncrement.lean` |
| done | `ItoCalculusKit.MartingaleTransform` | `SignatureVolatility/ItoCalculusKit/MartingaleTransform.lean` |
| done | `ItoCalculusKit.MathFinBridge` | `SignatureVolatility/ItoCalculusKit/MathFinBridge.lean` |
| blocked | `ItoCalculusKit.MathFinBridgeSetup` | `SignatureVolatility/ItoCalculusKit/MathFinBridgeSetup.lean` |
| blocked | `ItoCalculusKit.NovikovDoob` | `SignatureVolatility/ItoCalculusKit/NovikovDoob.lean` |
| blocked | `ItoCalculusKit.NovikovMartingale` | `SignatureVolatility/ItoCalculusKit/NovikovMartingale.lean` |
| blocked | `ItoCalculusKit.OfMathFin` | `SignatureVolatility/ItoCalculusKit/OfMathFin.lean` |
| done | `ItoCalculusKit.PathwiseExpIto` | `SignatureVolatility/ItoCalculusKit/PathwiseExpIto.lean` |
| blocked | `ItoCalculusKit.QVTransform` | `SignatureVolatility/ItoCalculusKit/QVTransform.lean` |
| blocked | `ItoCalculusKit.QuadIncrement` | `SignatureVolatility/ItoCalculusKit/QuadIncrement.lean` |
| done | `ItoCalculusKit.RiemannConvergence` | `SignatureVolatility/ItoCalculusKit/RiemannConvergence.lean` |
| blocked | `ItoCalculusKit.RiemannRate8` | `SignatureVolatility/ItoCalculusKit/RiemannRate8.lean` |
| done | `ItoCalculusKit.SigmaBounds` | `SignatureVolatility/ItoCalculusKit/SigmaBounds.lean` |
| blocked | `ItoCalculusKit.SigmaContinuity` | `SignatureVolatility/ItoCalculusKit/SigmaContinuity.lean` |
| blocked | `ItoCalculusKit.SigmaHolder` | `SignatureVolatility/ItoCalculusKit/SigmaHolder.lean` |
| blocked | `ItoCalculusKit.SigmaHolder8` | `SignatureVolatility/ItoCalculusKit/SigmaHolder8.lean` |
| blocked | `ItoCalculusKit.StoppedKit` | `SignatureVolatility/ItoCalculusKit/StoppedKit.lean` |
| blocked | `ItoCalculusKit.StoppedL2` | `SignatureVolatility/ItoCalculusKit/StoppedL2.lean` |
| blocked | `ItoCalculusKit.StoppedRaw` | `SignatureVolatility/ItoCalculusKit/StoppedRaw.lean` |
| blocked | `ItoCalculusKit.StoppedStep` | `SignatureVolatility/ItoCalculusKit/StoppedStep.lean` |
| blocked | `ItoCalculusKit.SubseqUniform` | `SignatureVolatility/ItoCalculusKit/SubseqUniform.lean` |
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
| blocked | `SignatureRiccatiKit.OfSetup` | `SignatureVolatility/SignatureRiccatiKit/OfSetup.lean` |
| done | `SignatureRiccatiKit.RiccatiOp` | `SignatureVolatility/SignatureRiccatiKit/RiccatiOp.lean` |
| done | `SignatureVolatilityModel` | `SignatureVolatility/SignatureVolatilityModel.lean` |
| done | `SmoothIteratedIntegral` | `SignatureVolatility/SmoothIteratedIntegral.lean` |
| done | `SmoothSignature` | `SignatureVolatility/SmoothSignature.lean` |
| done | `StratonovichHalfLaplacian` | `SignatureVolatility/StratonovichHalfLaplacian.lean` |
| done | `SuperfactorialFunctional` | `SignatureVolatility/SuperfactorialFunctional.lean` |
| done | `TailNorm2wInvLeRatioMulNormW` | `SignatureVolatility/TailNorm2wInvLeRatioMulNormW.lean` |
| blocked | `TheoremA` | `SignatureVolatility/TheoremA.lean` |
| done | `TheoremAOfBrownianSetupItoKit` | `SignatureVolatility/TheoremAOfBrownianSetupItoKit.lean` |
| blocked | `TheoremB` | `SignatureVolatility/TheoremB.lean` |
| done | `TheoremBOfSetupItoRiccatiKit` | `SignatureVolatility/TheoremBOfSetupItoRiccatiKit.lean` |
| blocked | `TheoremC` | `SignatureVolatility/TheoremC.lean` |
| done | `TheoremCOfMarketKit` | `SignatureVolatility/TheoremCOfMarketKit.lean` |
| blocked | `TheoremD` | `SignatureVolatility/TheoremD.lean` |
| done | `TheoremDOfMarketKit` | `SignatureVolatility/TheoremDOfMarketKit.lean` |
| done | `TimeReindex` | `SignatureVolatility/TimeReindex.lean` |
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
| done | `ExtTensorAlgebra.ConcatAssoc` | `SignatureVolatility/ExtTensorAlgebra/ConcatAssoc.lean` |
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
| done | `ExtTensorAlgebra.TensorExp` | `SignatureVolatility/ExtTensorAlgebra/TensorExp.lean` |
| done | `ExtTensorAlgebra.TensorExpLevelNorm` | `SignatureVolatility/ExtTensorAlgebra/TensorExpLevelNorm.lean` |
| done | `ExtTensorAlgebra.TensorExpLipschitz` | `SignatureVolatility/ExtTensorAlgebra/TensorExpLipschitz.lean` |
| done | `ExtTensorAlgebra.TensorExpNeg` | `SignatureVolatility/ExtTensorAlgebra/TensorExpNeg.lean` |
| done | `ExtTensorAlgebra.TensorExpShuffle` | `SignatureVolatility/ExtTensorAlgebra/TensorExpShuffle.lean` |

### Weight — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `Weight.ConstOne` | `SignatureVolatility/Weight/ConstOne.lean` |
| done | `Weight.Geometric` | `SignatureVolatility/Weight/Geometric.lean` |

### ProlongedBrownianSetup — 2 hole(s)

| Status | Id | File |
|---|---|---|
| done | `ProlongedBrownianSetup.BrownianFiltration` | `SignatureVolatility/ProlongedBrownianSetup/BrownianFiltration.lean` |
| done | `ProlongedBrownianSetup.ContVersion` | `SignatureVolatility/ProlongedBrownianSetup/ContVersion.lean` |
| done | `ProlongedBrownianSetup.ContVersionKolmogorov` | `SignatureVolatility/ProlongedBrownianSetup/ContVersionKolmogorov.lean` |
| done | `ProlongedBrownianSetup.ItoIntegralAgainstBM` | `SignatureVolatility/ProlongedBrownianSetup/ItoIntegralAgainstBM.lean` |
| done | `ProlongedBrownianSetup.ItoIntegralProcess` | `SignatureVolatility/ProlongedBrownianSetup/ItoIntegralProcess.lean` |
| done | `ProlongedBrownianSetup.ItoWordIntegral` | `SignatureVolatility/ProlongedBrownianSetup/ItoWordIntegral.lean` |
| done | `ProlongedBrownianSetup.ItoWordIntegralConsLong` | `SignatureVolatility/ProlongedBrownianSetup/ItoWordIntegralConsLong.lean` |
| done | `ProlongedBrownianSetup.ItoWordIntegralLe1` | `SignatureVolatility/ProlongedBrownianSetup/ItoWordIntegralLe1.lean` |
| done | `ProlongedBrownianSetup.OfBrownian` | `SignatureVolatility/ProlongedBrownianSetup/OfBrownian.lean` |
| done | `ProlongedBrownianSetup.PaperSig` | `SignatureVolatility/ProlongedBrownianSetup/PaperSig.lean` |
| open | `ProlongedBrownianSetup.PaperSigChen` | `SignatureVolatility/ProlongedBrownianSetup/PaperSigChen.lean` |
| done | `ProlongedBrownianSetup.PaperSigDynamics` | `SignatureVolatility/ProlongedBrownianSetup/PaperSigDynamics.lean` |
| done | `ProlongedBrownianSetup.ShiftedWordIntegral` | `SignatureVolatility/ProlongedBrownianSetup/ShiftedWordIntegral.lean` |
| done | `ProlongedBrownianSetup.Sig2StratAdapted` | `SignatureVolatility/ProlongedBrownianSetup/Sig2StratAdapted.lean` |
| done | `ProlongedBrownianSetup.Sig2StratDyadic` | `SignatureVolatility/ProlongedBrownianSetup/Sig2StratDyadic.lean` |
| done | `ProlongedBrownianSetup.SignatureFiltration` | `SignatureVolatility/ProlongedBrownianSetup/SignatureFiltration.lean` |
| done | `ProlongedBrownianSetup.SignatureOfBM` | `SignatureVolatility/ProlongedBrownianSetup/SignatureOfBM.lean` |
| done | `ProlongedBrownianSetup.StratItoCoeffBounds` | `SignatureVolatility/ProlongedBrownianSetup/StratItoCoeffBounds.lean` |
| done | `ProlongedBrownianSetup.StratonovichItoConversion` | `SignatureVolatility/ProlongedBrownianSetup/StratonovichItoConversion.lean` |
| blocked | `ProlongedBrownianSetup.StratonovichOfBM` | `SignatureVolatility/ProlongedBrownianSetup/StratonovichOfBM.lean` |
| done | `ProlongedBrownianSetup.WAug` | `SignatureVolatility/ProlongedBrownianSetup/WAug.lean` |
| done | `ProlongedBrownianSetup.WHat` | `SignatureVolatility/ProlongedBrownianSetup/WHat.lean` |

### PriceFiltrationSignatureSpace — 1 hole(s)

| Status | Id | File |
|---|---|---|
| done | `PriceFiltrationSignatureSpace.AugmentedMarketSpan` | `SignatureVolatility/PriceFiltrationSignatureSpace/AugmentedMarketSpan.lean` |
| done | `PriceFiltrationSignatureSpace.CompletenessDepth` | `SignatureVolatility/PriceFiltrationSignatureSpace/CompletenessDepth.lean` |
| done | `PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration` | `SignatureVolatility/PriceFiltrationSignatureSpace/IsCompleteOnPriceFiltration.lean` |
| blocked | `PriceFiltrationSignatureSpace.OfMarket` | `SignatureVolatility/PriceFiltrationSignatureSpace/OfMarket.lean` |
| done | `PriceFiltrationSignatureSpace.VInfty` | `SignatureVolatility/PriceFiltrationSignatureSpace/VInfty.lean` |
| done | `PriceFiltrationSignatureSpace.VSubspace` | `SignatureVolatility/PriceFiltrationSignatureSpace/VSubspace.lean` |

### SignatureVolatilityModel — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `SignatureVolatilityModel.Sigma` | `SignatureVolatility/SignatureVolatilityModel/Sigma.lean` |

## Dependency sketch

Direct import-deps: `holes-edges.txt`. Display graph uses transitive reduction. Open [`holes.html`](holes.html) for the interactive board.


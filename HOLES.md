# Proof holes (Xodarev / SignatureVolatility)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`.

**Updated:** 2026-11-25T14:30:45Z
**`sorry` occurrences:** 0 · 1 open · 0 blocked · 211 done · 0 file(s) with `sorry`.
**Paper claims refuted:** 6 counterexample module(s) · 1 refuted theorem(s) · 1 half-proved theorem(s). All are finished (no `sorry`) and counted as done.

## The affine / Riccati `<-` direction is refuted

The false theorem `affine_riccati_duality_mpr` has been removed from the library. Its negation `not_affine_riccati_duality_mpr` is proved sorry-free in `SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample`; `not_affine_riccati_duality`, `not_theorem_B_mpr` and `not_theorem_B` follow from it. All four are compared in `comparator.json` in unwrapped form (`…_unwrapped` in `Unwrapped`; see `Writeup/narratives/`). `Solution.lean` has **0** `sorry` (the Challenge's compared proofs are `sorry` by design). `theorem_B_mp` (martingale, the price-independent `AdmissibleGainsUnderP` NFLVR conjunct, special semimartingale, `->` Riccati direction) is sorry-free and compared as `theorem_B_mp_unwrapped`; `affine_riccati_duality_mp` is sorry-free and not compared.


## Counterexamples and refuted paper claims

| Kind | Label (module) | What is refuted | File |
|---|---|---|---|
| **counterexample** | **CounterExample_Lemma77** (`Lemma77ShuffleEstimateFalse`) | CounterExample_Lemma77: refutes paper Lemma 77 (weighted shuffle estimate) for every (H2) weight. | `SignatureVolatility/Lemma77ShuffleEstimateFalse.lean` |
| **counterexample** | **CounterExample_Lemma78** (`Lemma78RiccatiLipschitzFalse`) | CounterExample_Lemma78: refutes paper Lemma 78 (local Lipschitz bound for the Riccati operator); for w = 1 the operator is unbounded on the unit ball of T_w. | `SignatureVolatility/Lemma78RiccatiLipschitzFalse.lean` |
| **counterexample** | **CounterExample_Prop58** (`Prop58BlackScholesDepthFalse`) | CounterExample_Prop58: refutes paper Prop. 58 / PDF Prop. 5.5 (Black-Scholes has completeness depth 0); Black-Scholes depth is infinite under Definition 55. | `SignatureVolatility/Prop58BlackScholesDepthFalse.lean` |
| **counterexample** | **not_affine_riccati_duality_mpr (proved)** (`SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample`) | COUNTEREXAMPLE to a paper claim. | `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean` |
| **counterexample** | **CounterExample_TheoremC** (`TheoremCCounterExample`) | CounterExample_TheoremC (proved, not_theorem_C): Black-Scholes is complete on F^S_T (vendored MathFin martingale representation, F^S = F^W) for every finite strike set, while N*_S = infinity; so the paper's 'complete iff N*_S < infinity' is false. | `SignatureVolatility/TheoremCCounterExample.lean` |
| **counterexample** | **CounterExample_TheoremD** (`TheoremDCounterExample`) | CounterExample_TheoremD (theorem_D_residual_hypothesis_fails): the residual-expansion clause of Theorem 66 assumes N*_S < infinity, which fails for Black-Scholes (vacuous). | `SignatureVolatility/TheoremDCounterExample.lean` |
| **half-proved** | **Half_TheoremD** (`TheoremD`) | Half_TheoremD: GKW projection part proved (theorem_D). The residual-expansion clause is refuted separately by CounterExample_TheoremD (TheoremDCounterExample). Paper kit / theorem goal. | `SignatureVolatility/TheoremD.lean` |
| **refuted** | **TheoremC: refuted by CounterExample_TheoremC** (`TheoremC`) | REFUTED (CounterExample_TheoremC, theorem_C_refuted := not_theorem_C): Black-Scholes is complete with any finite set of calls but has N*_S = infinity, so 'complete iff N*_S < infinity' fails. Also: depth is infinite in every non-degenerate model; Prop. 58 refuted. Paper kit / theorem goal. | `SignatureVolatility/TheoremC.lean` |

**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, embeds into holes.html
scripts/serve_holes.sh          # http://127.0.0.1:8766/holes.html
```

## Paper kit / theorem goals (before Challenge rewrite)

These must be sorry-free at **paper strength** (nontrivial Itô kit, Stratonovich signature, Riccati duality, Davis–Obłój PFS, GKW) before updating Palomar Challenge / `formalization.yaml`.

| Status | Id | `sorry`? | File |
|---|---|---|---|
| done | `GKWDecompositionSetup.OfPFS` | no | `SignatureVolatility/GKWDecompositionSetup/OfPFS.lean` |
| done | `ItoCalculusKit.OfMathFin` | no | `SignatureVolatility/ItoCalculusKit/OfMathFin.lean` |
| done | `PriceFiltrationSignatureSpace.OfMarket` | no | `SignatureVolatility/PriceFiltrationSignatureSpace/OfMarket.lean` |
| done | `ProlongedBrownianSetup.StratonovichOfBM` | no | `SignatureVolatility/ProlongedBrownianSetup/StratonovichOfBM.lean` |
| done | `TheoremA` | no | `SignatureVolatility/TheoremA.lean` |
| done | `TheoremB` | no | `SignatureVolatility/TheoremB.lean` |
| done | `TheoremC` | no | `SignatureVolatility/TheoremC.lean` |
| done | `TheoremD` | no | `SignatureVolatility/TheoremD.lean` |

## Files with `sorry`

_None._

## Open now (Layer 0)

| Id | File |
|---|---|
| `NflvrDoubling` | `SignatureVolatility/NflvrDoubling.lean` |

## By group

### Top-level modules — 1 hole(s)

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
| done | `GKWDecompositionSetup.OfPFS` | `SignatureVolatility/GKWDecompositionSetup/OfPFS.lean` |
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
| done | `ItoCalculusKit.DoleansEnvelope` | `SignatureVolatility/ItoCalculusKit/DoleansEnvelope.lean` |
| done | `ItoCalculusKit.DoleansErrorPathwise` | `SignatureVolatility/ItoCalculusKit/DoleansErrorPathwise.lean` |
| done | `ItoCalculusKit.DoleansIdentify` | `SignatureVolatility/ItoCalculusKit/DoleansIdentify.lean` |
| done | `ItoCalculusKit.DoleansInputs` | `SignatureVolatility/ItoCalculusKit/DoleansInputs.lean` |
| done | `ItoCalculusKit.DoleansMoments` | `SignatureVolatility/ItoCalculusKit/DoleansMoments.lean` |
| done | `ItoCalculusKit.DoleansQV` | `SignatureVolatility/ItoCalculusKit/DoleansQV.lean` |
| done | `ItoCalculusKit.DoleansSDE` | `SignatureVolatility/ItoCalculusKit/DoleansSDE.lean` |
| done | `ItoCalculusKit.DoleansSigma` | `SignatureVolatility/ItoCalculusKit/DoleansSigma.lean` |
| done | `ItoCalculusKit.DoleansStrongClass` | `SignatureVolatility/ItoCalculusKit/DoleansStrongClass.lean` |
| done | `ItoCalculusKit.DoobEnvelope` | `SignatureVolatility/ItoCalculusKit/DoobEnvelope.lean` |
| done | `ItoCalculusKit.EighthMoment` | `SignatureVolatility/ItoCalculusKit/EighthMoment.lean` |
| done | `ItoCalculusKit.EighthTransform` | `SignatureVolatility/ItoCalculusKit/EighthTransform.lean` |
| done | `ItoCalculusKit.EvenMoment` | `SignatureVolatility/ItoCalculusKit/EvenMoment.lean` |
| done | `ItoCalculusKit.EvenTransform` | `SignatureVolatility/ItoCalculusKit/EvenTransform.lean` |
| done | `ItoCalculusKit.ExpSupermartingale` | `SignatureVolatility/ItoCalculusKit/ExpSupermartingale.lean` |
| done | `ItoCalculusKit.FourthMoment` | `SignatureVolatility/ItoCalculusKit/FourthMoment.lean` |
| done | `ItoCalculusKit.FrozenIncrement4` | `SignatureVolatility/ItoCalculusKit/FrozenIncrement4.lean` |
| done | `ItoCalculusKit.FrozenIncrement8` | `SignatureVolatility/ItoCalculusKit/FrozenIncrement8.lean` |
| done | `ItoCalculusKit.FrozenOrthogonal` | `SignatureVolatility/ItoCalculusKit/FrozenOrthogonal.lean` |
| done | `ItoCalculusKit.GBMEnvelope` | `SignatureVolatility/ItoCalculusKit/GBMEnvelope.lean` |
| done | `ItoCalculusKit.GBMMartingale` | `SignatureVolatility/ItoCalculusKit/GBMMartingale.lean` |
| done | `ItoCalculusKit.GridChange` | `SignatureVolatility/ItoCalculusKit/GridChange.lean` |
| done | `ItoCalculusKit.GridDoob` | `SignatureVolatility/ItoCalculusKit/GridDoob.lean` |
| done | `ItoCalculusKit.HolderPath` | `SignatureVolatility/ItoCalculusKit/HolderPath.lean` |
| done | `ItoCalculusKit.ItoIncrement` | `SignatureVolatility/ItoCalculusKit/ItoIncrement.lean` |
| done | `ItoCalculusKit.ItoIncrement8` | `SignatureVolatility/ItoCalculusKit/ItoIncrement8.lean` |
| done | `ItoCalculusKit.ItoIncrementEven` | `SignatureVolatility/ItoCalculusKit/ItoIncrementEven.lean` |
| done | `ItoCalculusKit.ItoOrthogonal` | `SignatureVolatility/ItoCalculusKit/ItoOrthogonal.lean` |
| done | `ItoCalculusKit.ItoQuadDoleans` | `SignatureVolatility/ItoCalculusKit/ItoQuadDoleans.lean` |
| done | `ItoCalculusKit.JointPast` | `SignatureVolatility/ItoCalculusKit/JointPast.lean` |
| done | `ItoCalculusKit.KitRaw` | `SignatureVolatility/ItoCalculusKit/KitRaw.lean` |
| done | `ItoCalculusKit.KolmogorovIto` | `SignatureVolatility/ItoCalculusKit/KolmogorovIto.lean` |
| done | `ItoCalculusKit.LebIncrementEven` | `SignatureVolatility/ItoCalculusKit/LebIncrementEven.lean` |
| done | `ItoCalculusKit.LevelBounds` | `SignatureVolatility/ItoCalculusKit/LevelBounds.lean` |
| done | `ItoCalculusKit.LevelDecay` | `SignatureVolatility/ItoCalculusKit/LevelDecay.lean` |
| done | `ItoCalculusKit.LogDoleansIncrement` | `SignatureVolatility/ItoCalculusKit/LogDoleansIncrement.lean` |
| done | `ItoCalculusKit.MartingaleTransform` | `SignatureVolatility/ItoCalculusKit/MartingaleTransform.lean` |
| done | `ItoCalculusKit.MathFinBridge` | `SignatureVolatility/ItoCalculusKit/MathFinBridge.lean` |
| done | `ItoCalculusKit.MathFinBridgeSetup` | `SignatureVolatility/ItoCalculusKit/MathFinBridgeSetup.lean` |
| done | `ItoCalculusKit.NovikovDoob` | `SignatureVolatility/ItoCalculusKit/NovikovDoob.lean` |
| done | `ItoCalculusKit.NovikovMartingale` | `SignatureVolatility/ItoCalculusKit/NovikovMartingale.lean` |
| done | `ItoCalculusKit.OfMathFin` | `SignatureVolatility/ItoCalculusKit/OfMathFin.lean` |
| done | `ItoCalculusKit.PathwiseExpIto` | `SignatureVolatility/ItoCalculusKit/PathwiseExpIto.lean` |
| done | `ItoCalculusKit.QVTransform` | `SignatureVolatility/ItoCalculusKit/QVTransform.lean` |
| done | `ItoCalculusKit.QuadIncrement` | `SignatureVolatility/ItoCalculusKit/QuadIncrement.lean` |
| done | `ItoCalculusKit.RiemannConvergence` | `SignatureVolatility/ItoCalculusKit/RiemannConvergence.lean` |
| done | `ItoCalculusKit.RiemannRate8` | `SignatureVolatility/ItoCalculusKit/RiemannRate8.lean` |
| done | `ItoCalculusKit.SigmaBounds` | `SignatureVolatility/ItoCalculusKit/SigmaBounds.lean` |
| done | `ItoCalculusKit.SigmaContinuity` | `SignatureVolatility/ItoCalculusKit/SigmaContinuity.lean` |
| done | `ItoCalculusKit.SigmaHolder` | `SignatureVolatility/ItoCalculusKit/SigmaHolder.lean` |
| done | `ItoCalculusKit.SigmaHolder8` | `SignatureVolatility/ItoCalculusKit/SigmaHolder8.lean` |
| done | `ItoCalculusKit.StoppedKit` | `SignatureVolatility/ItoCalculusKit/StoppedKit.lean` |
| done | `ItoCalculusKit.StoppedL2` | `SignatureVolatility/ItoCalculusKit/StoppedL2.lean` |
| done | `ItoCalculusKit.StoppedRaw` | `SignatureVolatility/ItoCalculusKit/StoppedRaw.lean` |
| done | `ItoCalculusKit.StoppedStep` | `SignatureVolatility/ItoCalculusKit/StoppedStep.lean` |
| done | `ItoCalculusKit.SubseqUniform` | `SignatureVolatility/ItoCalculusKit/SubseqUniform.lean` |
| done | `Lemma32SignatureInTw` | `SignatureVolatility/Lemma32SignatureInTw.lean` |
| done | `Lemma61GramPosDef` | `SignatureVolatility/Lemma61GramPosDef.lean` |
| done | `Lemma77ShuffleEstimateFalse` | `SignatureVolatility/Lemma77ShuffleEstimateFalse.lean` |
| done | `Lemma78RiccatiLipschitzFalse` | `SignatureVolatility/Lemma78RiccatiLipschitzFalse.lean` |
| done | `Letter` | `SignatureVolatility/Letter.lean` |
| done | `MemL2w` | `SignatureVolatility/MemL2w.lean` |
| done | `MemL2wInv` | `SignatureVolatility/MemL2wInv.lean` |
| done | `MemL2wInvOfMemTw` | `SignatureVolatility/MemL2wInvOfMemTw.lean` |
| done | `MemTw` | `SignatureVolatility/MemTw.lean` |
| done | `MemTwDual` | `SignatureVolatility/MemTwDual.lean` |
| done | `MemTwDualOfMemL2w` | `SignatureVolatility/MemTwDualOfMemL2w.lean` |
| done | `NflvrCone` | `SignatureVolatility/NflvrCone.lean` |
| done | `NflvrDefs` | `SignatureVolatility/NflvrDefs.lean` |
| open | `NflvrDoubling` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrOfMartingaleMeasure` | `SignatureVolatility/NflvrOfMartingaleMeasure.lean` |
| done | `Norm2w` | `SignatureVolatility/Norm2w.lean` |
| done | `Norm2wInv` | `SignatureVolatility/Norm2wInv.lean` |
| done | `NormW` | `SignatureVolatility/NormW.lean` |
| done | `NormWDual` | `SignatureVolatility/NormWDual.lean` |
| done | `Preliminaries` | `SignatureVolatility/Preliminaries.lean` |
| done | `PriceFiltration` | `SignatureVolatility/PriceFiltration.lean` |
| done | `ProjGt` | `SignatureVolatility/ProjGt.lean` |
| done | `ProjLe` | `SignatureVolatility/ProjLe.lean` |
| done | `ProlongedBrownianSetup` | `SignatureVolatility/ProlongedBrownianSetup.lean` |
| done | `Prop58BlackScholesDepthFalse` | `SignatureVolatility/Prop58BlackScholesDepthFalse.lean` |
| done | `Proposition311SharpnessOfH1` | `SignatureVolatility/Proposition311SharpnessOfH1.lean` |
| done | `Proposition65NormalEquations` | `SignatureVolatility/Proposition65NormalEquations.lean` |
| done | `PureBrownianWord` | `SignatureVolatility/PureBrownianWord.lean` |
| done | `QuinticOUSignatureModel` | `SignatureVolatility/QuinticOUSignatureModel.lean` |
| done | `Remark219BlackScholesRiccati` | `SignatureVolatility/Remark219BlackScholesRiccati.lean` |
| done | `RiccatiOpBounded` | `SignatureVolatility/RiccatiOpBounded.lean` |
| done | `RightShift` | `SignatureVolatility/RightShift.lean` |
| done | `SatisfiesNFLVR` | `SignatureVolatility/SatisfiesNFLVR.lean` |
| done | `ShuffleFinite` | `SignatureVolatility/ShuffleFinite.lean` |
| done | `ShuffleIdentity` | `SignatureVolatility/ShuffleIdentity.lean` |
| done | `SignatureFiltrationEqBrownianFiltration` | `SignatureVolatility/SignatureFiltrationEqBrownianFiltration.lean` |
| done | `SignatureHestonLevel2Model` | `SignatureVolatility/SignatureHestonLevel2Model.lean` |
| done | `SignaturePriceSolution` | `SignatureVolatility/SignaturePriceSolution.lean` |
| done | `SignatureRiccatiKit` | `SignatureVolatility/SignatureRiccatiKit.lean` |
| done | `SignatureRiccatiKit.AffineRiccatiDuality` | `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDuality.lean` |
| done | `SignatureRiccatiKit.AffineRiccatiDualityMp` | `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMp.lean` |
| done | `SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample` | `SignatureVolatility/SignatureRiccatiKit/AffineRiccatiDualityMprCounterexample.lean` |
| done | `SignatureRiccatiKit.BarrierU` | `SignatureVolatility/SignatureRiccatiKit/BarrierU.lean` |
| done | `SignatureRiccatiKit.BrownianScalingShiftedExponent` | `SignatureVolatility/SignatureRiccatiKit/BrownianScalingShiftedExponent.lean` |
| done | `SignatureRiccatiKit.CameronMartinC2Shift` | `SignatureVolatility/SignatureRiccatiKit/CameronMartinC2Shift.lean` |
| done | `SignatureRiccatiKit.ComplexTilt` | `SignatureVolatility/SignatureRiccatiKit/ComplexTilt.lean` |
| done | `SignatureRiccatiKit.CondExpMulIndepDisintegrate` | `SignatureVolatility/SignatureRiccatiKit/CondExpMulIndepDisintegrate.lean` |
| done | `SignatureRiccatiKit.CondSigPoly` | `SignatureVolatility/SignatureRiccatiKit/CondSigPoly.lean` |
| done | `SignatureRiccatiKit.CondSigPolyIdentification` | `SignatureVolatility/SignatureRiccatiKit/CondSigPolyIdentification.lean` |
| done | `SignatureRiccatiKit.CoordSemimartingale` | `SignatureVolatility/SignatureRiccatiKit/CoordSemimartingale.lean` |
| done | `SignatureRiccatiKit.CounterexampleTensor` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleTensor.lean` |
| done | `SignatureRiccatiKit.CounterexampleV1` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleV1.lean` |
| done | `SignatureRiccatiKit.CounterexampleV1CondExp` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleV1CondExp.lean` |
| done | `SignatureRiccatiKit.CounterexampleV1Decay` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleV1Decay.lean` |
| done | `SignatureRiccatiKit.CounterexampleV1LogBound` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleV1LogBound.lean` |
| done | `SignatureRiccatiKit.CounterexampleV1LogNonpos` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleV1LogNonpos.lean` |
| done | `SignatureRiccatiKit.CounterexampleV1PosLe` | `SignatureVolatility/SignatureRiccatiKit/CounterexampleV1PosLe.lean` |
| done | `SignatureRiccatiKit.DifferentiableAtTsum` | `SignatureVolatility/SignatureRiccatiKit/DifferentiableAtTsum.lean` |
| done | `SignatureRiccatiKit.EntireTransfer` | `SignatureVolatility/SignatureRiccatiKit/EntireTransfer.lean` |
| done | `SignatureRiccatiKit.FawcettHermite` | `SignatureVolatility/SignatureRiccatiKit/FawcettHermite.lean` |
| done | `SignatureRiccatiKit.FourierUniquenessGaussian` | `SignatureVolatility/SignatureRiccatiKit/FourierUniquenessGaussian.lean` |
| done | `SignatureRiccatiKit.IntegralExpBarrier` | `SignatureVolatility/SignatureRiccatiKit/IntegralExpBarrier.lean` |
| done | `SignatureRiccatiKit.IteratedDerivGaussian` | `SignatureVolatility/SignatureRiccatiKit/IteratedDerivGaussian.lean` |
| done | `SignatureRiccatiKit.ItoWordTiltClosedForm` | `SignatureVolatility/SignatureRiccatiKit/ItoWordTiltClosedForm.lean` |
| done | `SignatureRiccatiKit.LintegralExpShifted` | `SignatureVolatility/SignatureRiccatiKit/LintegralExpShifted.lean` |
| done | `SignatureRiccatiKit.Poly4ConstOfLogBdd` | `SignatureVolatility/SignatureRiccatiKit/Poly4ConstOfLogBdd.lean` |
| done | `SignatureRiccatiKit.RiccatiExpProcess` | `SignatureVolatility/SignatureRiccatiKit/RiccatiExpProcess.lean` |
| done | `SignatureRiccatiKit.RiccatiOp` | `SignatureVolatility/SignatureRiccatiKit/RiccatiOp.lean` |
| done | `SignatureRiccatiKit.SummableNormTermAndBound` | `SignatureVolatility/SignatureRiccatiKit/SummableNormTermAndBound.lean` |
| done | `SignatureVolatilityModel` | `SignatureVolatility/SignatureVolatilityModel.lean` |
| done | `SmoothIteratedIntegral` | `SignatureVolatility/SmoothIteratedIntegral.lean` |
| done | `SmoothSignature` | `SignatureVolatility/SmoothSignature.lean` |
| done | `StratonovichHalfLaplacian` | `SignatureVolatility/StratonovichHalfLaplacian.lean` |
| done | `SuperfactorialFunctional` | `SignatureVolatility/SuperfactorialFunctional.lean` |
| done | `TailNorm2wInvLeRatioMulNormW` | `SignatureVolatility/TailNorm2wInvLeRatioMulNormW.lean` |
| done | `TheoremA` | `SignatureVolatility/TheoremA.lean` |
| done | `TheoremAOfBrownianSetupItoKit` | `SignatureVolatility/TheoremAOfBrownianSetupItoKit.lean` |
| done | `TheoremB` | `SignatureVolatility/TheoremB.lean` |
| done | `TheoremBMpr` | `SignatureVolatility/TheoremBMpr.lean` |
| done | `TheoremBOfSetupItoRiccatiKit` | `SignatureVolatility/TheoremBOfSetupItoRiccatiKit.lean` |
| done | `TheoremC` | `SignatureVolatility/TheoremC.lean` |
| done | `TheoremCCounterExample` | `SignatureVolatility/TheoremCCounterExample.lean` |
| done | `TheoremD` | `SignatureVolatility/TheoremD.lean` |
| done | `TheoremDCounterExample` | `SignatureVolatility/TheoremDCounterExample.lean` |
| done | `TimeReindex` | `SignatureVolatility/TimeReindex.lean` |
| done | `Tw` | `SignatureVolatility/Tw.lean` |
| done | `Unwrapped` | `SignatureVolatility/Unwrapped.lean` |
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
| done | `ExtTensorAlgebra.TensorExpNeg` | `SignatureVolatility/ExtTensorAlgebra/TensorExpNeg.lean` |
| done | `ExtTensorAlgebra.TensorExpShuffle` | `SignatureVolatility/ExtTensorAlgebra/TensorExpShuffle.lean` |

### Weight — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `Weight.ConstOne` | `SignatureVolatility/Weight/ConstOne.lean` |
| done | `Weight.Geometric` | `SignatureVolatility/Weight/Geometric.lean` |

### ProlongedBrownianSetup — 0 hole(s)

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
| done | `ProlongedBrownianSetup.PaperSigChen` | `SignatureVolatility/ProlongedBrownianSetup/PaperSigChen.lean` |
| done | `ProlongedBrownianSetup.PaperSigDynamics` | `SignatureVolatility/ProlongedBrownianSetup/PaperSigDynamics.lean` |
| done | `ProlongedBrownianSetup.ShiftedWordIntegral` | `SignatureVolatility/ProlongedBrownianSetup/ShiftedWordIntegral.lean` |
| done | `ProlongedBrownianSetup.Sig2StratAdapted` | `SignatureVolatility/ProlongedBrownianSetup/Sig2StratAdapted.lean` |
| done | `ProlongedBrownianSetup.SignatureFiltration` | `SignatureVolatility/ProlongedBrownianSetup/SignatureFiltration.lean` |
| done | `ProlongedBrownianSetup.SignatureOfBM` | `SignatureVolatility/ProlongedBrownianSetup/SignatureOfBM.lean` |
| done | `ProlongedBrownianSetup.StratItoCoeffBounds` | `SignatureVolatility/ProlongedBrownianSetup/StratItoCoeffBounds.lean` |
| done | `ProlongedBrownianSetup.StratonovichItoConversion` | `SignatureVolatility/ProlongedBrownianSetup/StratonovichItoConversion.lean` |
| done | `ProlongedBrownianSetup.StratonovichOfBM` | `SignatureVolatility/ProlongedBrownianSetup/StratonovichOfBM.lean` |
| done | `ProlongedBrownianSetup.WAug` | `SignatureVolatility/ProlongedBrownianSetup/WAug.lean` |
| done | `ProlongedBrownianSetup.WHat` | `SignatureVolatility/ProlongedBrownianSetup/WHat.lean` |

### PriceFiltrationSignatureSpace — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `PriceFiltrationSignatureSpace.OfMarket` | `SignatureVolatility/PriceFiltrationSignatureSpace/OfMarket.lean` |

### SignatureVolatilityModel — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `SignatureVolatilityModel.Sigma` | `SignatureVolatility/SignatureVolatilityModel/Sigma.lean` |

## Dependency sketch

Direct import-deps: `holes-edges.txt`. Display graph uses transitive reduction. Open [`holes.html`](holes.html) for the interactive board.


# Proof holes (Xodarev / SignatureVolatility)

File-level inventory of Lean modules. A module is **done** only if it is listed in `VERIFIED` in `scripts/build_holes.py`, all hard import-deps are done, **and** the file contains no `sorry`.

**Updated:** 2026-11-26T00:16:11Z
**`sorry` occurrences:** 0 · 1 open · 0 blocked · 243 done · 0 file(s) with `sorry`.
**Paper claims refuted:** 6 counterexample module(s) · 1 refuted theorem(s) · 1 half-proved theorem(s). All are finished (no `sorry`) and counted as done.

## The affine / Riccati `<-` direction is refuted

The false theorem `affine_riccati_duality_mpr` has been removed from the library. Its negation `not_affine_riccati_duality_mpr` is proved sorry-free in `SignatureRiccatiKit.AffineRiccatiDualityMprCounterexample`; `not_affine_riccati_duality`, `not_theorem_B_mpr` and `not_theorem_B` follow from it. All four are compared in `comparator.json` in unwrapped form (`…_unwrapped` in `Unwrapped`; see `Writeup/narratives/`). `Solution.lean` has **0** `sorry` (the Challenge's compared proofs are `sorry` by design). `theorem_B_mp` (martingale, the price-independent `AdmissibleGainsUnderP` NFLVR conjunct, special semimartingale, `->` Riccati direction) is sorry-free and compared as `theorem_B_mp_unwrapped`; `affine_riccati_duality_mp` is sorry-free and not compared. Upgrading that NFLVR conjunct to `SatisfiesNFLVR_DS` is tracked as ordinary open and blocked nodes under TheoremB_DS (not an open-problems category).


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
| `TheoremB_DS.writeup` | `Writeup/COMPARATOR.md` |

## NflvrDoubling subtasks

Internal structure of the doubling counterexample. These are not separate Lean modules. Finished pieces are ordinary done nodes with the landing commit; remaining work is ordinary open or blocked follow-on nodes.

| Status | Id | Commit(s) | What |
|---|---|---|---|
| done | `NflvrDoubling.tauHit` | `047b221, 99d7748` | Geometric grid t_n=T(1-2^{-n}) and hitting-time stopping lemma isStoppingTime_tauHit. Grid foundations in 99d7748; stopping lemma in 047b221. |
| done | `NflvrDoubling.incrDecay` | `b74bd01` | Independence of the standardized increments Z_n and geometric decay P(E_n)≤q^n, plus the early V_T=1 a.s. identity. Done in b74bd01. |
| done | `NflvrDoubling.l2Bound` | `b63d981, bf9c194` | L² bound on the doubling weights, E[∏_{j<m}(1-Z_j)²]=2^m, and the integrand / localizing-time packaging in bf9c194. Done in b63d981. |
| done | `NflvrDoubling.wealthProcess` | `4c102ea` | Explicit wealth process: starts at 0, ends at 1 almost surely, and almost every path is continuous on [0,T]. Done in 4c102ea. |
| done | `NflvrDoubling.riemannSums` | `5a32c82, b7cfba5` | Left-point Riemann-sum tools for the doubling integrand (5a32c82) and pathwise convergence of indicator partition sums to the matching Brownian increment (b7cfba5). |
| done | `NflvrDoubling.itoIntegral` | `3fc4c9e` | The doubling wealth is the Itô integral of K, with no glue parameters. Done in 3fc4c9e. |
| done | `NflvrDoubling.evalAdapted` | `024652f, f457b1e` | B evaluated at a stopping time τ≤t is F_t-measurable (Mathlib stronglyMeasurable_stoppedValue_of_le); X_n and c_n are F_{t_n}-adapted. Dyadic helpers in f457b1e; lemma and adaptedness in 024652f. |
| done | `NflvrDoubling.predictableK` | `024652f, 1d57446` | Left-open stochastic intervals (t_n,τ_n] are predictable (1d57446); uncurry doublingK is a pointwise limit of those stopped blocks, hence predictable (024652f). |
| done | `NflvrDoubling.sAdmissible` | `024652f` | IntegrableOn of K² on [0,T] a.s., hence the doubling strategy is S-admissible for S=σ=1. Done in 024652f. |
| done | `NflvrDoubling.literalFails` | `024652f` | Literal NFLVR fails: the doubling strategy is admissible, V_T=1 a.s., and this is a nontrivial free lunch in the Delbaen–Schachermayer cone. Done in 024652f. |
| done | `NflvrDoubling.bsPrice` | `4d9d645` | Closed-form Black–Scholes price s₀ exp(σ₀ B_t - ½ σ₀² t) is continuous, strictly positive, and F_t-adapted. Done in 4d9d645. |
| done | `NflvrDoubling.cutoffPred` | `4d9d645` | Dyadic left-endpoint approximations converge pathwise to the (0,T] cutoff of a continuous adapted process, hence that cutoff is predictable. Done in 4d9d645. |
| done | `NflvrDoubling.doublingH` | `4d9d645` | The transferred integrand H=K/(Sσ₀) is predictable and S-admissible for the closed-form BS price, and H S σ₀ equals K. Done in 4d9d645. |
| done | `NflvrDoubling.bsTransfer` | `4d9d645` | Black–Scholes transfer H=K/(Sσ₀): the same doubling wealth is an admissible Itô integral in the BS market and ends at V_T=1 a.s., so both literal NFLVR and the terminal-only bounded-below version fail. Done in 4d9d645. |
| done | `NflvrDoubling.terminalBdd` | `b8ea73f` | The same admissible doubling wealth ends at V_T=1≥0 a.s., so the terminal-only bounded-below cone also contains a nontrivial free lunch. Done in b8ea73f. |
| done | `NflvrDoubling.unwrappedRefs` | `7377f12` | Unwrapped compared theorems use sigPrice of blackScholesModel, which agrees with the closed-form bsPrice on [0,T]. Done in 7377f12. |
| done | `NflvrDoubling.challengeRefutations` | `7377f12` | Challenge copies of the NFLVR defs and two sorry compared theorems, still 1000 lines; comparator.json and yaml main_results list 11 unwrapped theorems; strict compare matches 44831 constants. Done in 7377f12. |
| done | `NflvrDoubling.writeup` | `ef49eff` | Writeup pass using Carbon's notes: narratives/nflvr_literal.md, Carbon appendix excerpt, PROVENANCE.md Comparator section, COMPARATOR.md, PalomarRegistration.md, and project.description, crediting Carbon (Gemini). Board, abstract and yaml scope updated to 11 compared theorems. |

## Theorem B DS NFLVR

Upgrade of `theorem_B_mp`'s NFLVR conjunct from `AdmissibleGainsUnderP` to `SatisfiesNFLVR_DS`. These are not separate Lean modules and not an open-problems category. Finished pieces will be ordinary done nodes with the landing commit; remaining work is ordinary open or blocked follow-on nodes.

| Status | Id | Commit(s) | What |
|---|---|---|---|
| done | `TheoremB_DS.kitItoIntContVersion` | `54fc9c8` | kitItoIntCont and kitQuadVarCont sit beside the existing kitItoInt and kitQuadVar (Carbon/Gemini). When kitItoIntRaw is already pathFiltration-adapted, the continuous version uses contVersion; kitItoInt itself is unchanged so StoppedKit and ConstVol still build. |
| done | `TheoremB_DS.jointL2Ito` | `54fc9c8` | L² Itô integral on the joint d-dimensional raw pathFiltration, built from JointElem / SortedElem, with the Itô isometry and π-λ density of elementary processes (Carbon/Gemini). MathFin's itoIntegralCLM is 1-D natFiltration only. |
| done | `TheoremB_DS.riemannL2` | `54fc9c8` | u-cancellation inequality lintegral_riemann_sq_le and L² convergence of itoRiemannPrime to the joint integral on any JointElem (Carbon/Gemini). |
| done | `TheoremB_DS.contIto` | `b246755` | exists_contIto_and_riemann_subseq: for predictable Z in L²(dtP), a version M of the joint-filtration Itô integral that is adapted and integrable, has mean zero, is a.s. continuous on [0,T] with M 0 = 0, is constant after q on {Z=0} after q, and is the in-probability limit of itoRiemannPrime along a subsequence (Carbon/Gemini, Mathlib 4.35 repairs). |
| done | `TheoremB_DS.localization` | `8ced7b0` | Left-continuous raw-filtration localization K^(m)=K 1_{Q≤m} of an S-admissible integrand (pathwise ∫K²<∞, not necessarily L²(dt⊗P)): localizedK is predSigma-measurable, lies in L²(dtP), and localizedQuad at τ_m is at most m (Carbon/Gemini, Mathlib 4.35 repairs). |
| done | `TheoremB_DS.superMartingale` | `8ced7b0` | A uniformly bounded-below local martingale is a supermartingale on [0,T]. Localize V at τ_m, apply the continuous L² integral, and use Fatou (expectation_le_zero_of_bounded_below_local_martingale in NflvrCone) to get E[V_T]≤0. Proved as expectation_le_zero_of_boundedBelowGain (Carbon/Gemini, Mathlib 4.35 repairs). |
| done | `TheoremB_DS.nflvrDs` | `8ced7b0` | Every G in BoundedBelowGains is integrable with E[G]≤0, hence SatisfiesNFLVR_DS holds by nflvr_ds_of_nonpos_mean. No H3. Proved for adapted, a.s.-continuous S and σ on the raw path filtration (Carbon/Gemini, Mathlib 4.35 repairs). |
| done | `TheoremB_DS` | `5516ccf` | Way A: IsSignaturePrice.doleans_repr is a.s. path-continuity on [0, T] and a.s. equality at each t to the Doléans exponential (kitItoInt / kitQuadVar). theorem_B_mp_unwrapped asserts SatisfiesNFLVR_DS for BoundedBelowGains of that S itself (witness sigPriceCont). Bundled theorem_B_mp keeps the pointwise SignaturePriceSolution from theorem_A and asserts DS NFLVR for sigPriceCont, which equals sol.S a.s. at each t. theorem_B_of_Setup_Ito_Riccati_Kit is unchanged (no MultiBrownian). not_theorem_B and not_theorem_B_unwrapped negate the same conjuncts. SignaturePriceSolution and theorem_A are unchanged. |
| done | `TheoremB_DS.challenge` | `5516ccf` | IsUniformlyBoundedBelow and BoundedBelowGains copied into the Challenge; IsSignaturePrice.doleans_repr and the NFLVR conjuncts of theorem_B_mp_unwrapped and not_theorem_B_unwrapped match the solution. Still sorry, 1000 lines / 54955 bytes, 11 theorem names, definition_names empty. Strict compare matched 44832 constants. |
| open | `TheoremB_DS.writeup` | `—` | Update the Theorem B narrative, PROVENANCE.md and COMPARATOR.md so the compared conjunct is full Delbaen–Schachermayer NFLVR, crediting Carbon (Gemini). English must match Lean 100%. |

## By group

### Top-level modules — 0 hole(s)

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
| done | `NflvrBoundedBelow` | `SignatureVolatility/NflvrBoundedBelow.lean` |
| done | `NflvrCone` | `SignatureVolatility/NflvrCone.lean` |
| done | `NflvrContIto` | `SignatureVolatility/NflvrContIto.lean` |
| done | `NflvrDS` | `SignatureVolatility/NflvrDS.lean` |
| done | `NflvrDefs` | `SignatureVolatility/NflvrDefs.lean` |
| done | `NflvrDoubling` | `SignatureVolatility/NflvrDoubling.lean` |
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
| done | `SigPriceCont` | `SignatureVolatility/SigPriceCont.lean` |
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

### NflvrDoubling subtasks — 0 hole(s)

| Status | Id | File |
|---|---|---|
| done | `NflvrDoubling.bsPrice` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.bsTransfer` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.challengeRefutations` | `SignatureVolatilityComparator/Challenge.lean` |
| done | `NflvrDoubling.cutoffPred` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.doublingH` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.evalAdapted` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.incrDecay` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.itoIntegral` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.l2Bound` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.literalFails` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.predictableK` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.riemannSums` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.sAdmissible` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.tauHit` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.terminalBdd` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.unwrappedRefs` | `SignatureVolatility/Unwrapped.lean` |
| done | `NflvrDoubling.wealthProcess` | `SignatureVolatility/NflvrDoubling.lean` |
| done | `NflvrDoubling.writeup` | `Writeup/PalomarRegistration.md` |

### Theorem B DS NFLVR — 1 hole(s)

| Status | Id | File |
|---|---|---|
| done | `TheoremB_DS` | `SignatureVolatility/TheoremB.lean` |
| done | `TheoremB_DS.challenge` | `SignatureVolatilityComparator/Challenge.lean` |
| done | `TheoremB_DS.contIto` | `SignatureVolatility/NflvrContIto.lean` |
| done | `TheoremB_DS.jointL2Ito` | `SignatureVolatility/NflvrBoundedBelow.lean` |
| done | `TheoremB_DS.kitItoIntContVersion` | `SignatureVolatility/ItoCalculusKit/MathFinBridge.lean` |
| done | `TheoremB_DS.localization` | `SignatureVolatility/NflvrDS.lean` |
| done | `TheoremB_DS.nflvrDs` | `SignatureVolatility/NflvrDS.lean` |
| done | `TheoremB_DS.riemannL2` | `SignatureVolatility/NflvrBoundedBelow.lean` |
| done | `TheoremB_DS.superMartingale` | `SignatureVolatility/NflvrDS.lean` |
| open | `TheoremB_DS.writeup` | `Writeup/COMPARATOR.md` |

## Dependency sketch

Direct import-deps: `holes-edges.txt`. Display graph uses transitive reduction. Open [`holes.html`](holes.html) for the interactive board.


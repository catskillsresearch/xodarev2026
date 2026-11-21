# Source map

This ledger records the complete disposition of the normative Klenke Chapters 01-08 handoff.
Klenke is the mathematical coverage source; the book is not distributed in this repository.
`Implemented` means kernel-checked StochLean code, `Upstream` means pinned Mathlib v4.33.0 is the
canonical implementation, and `Deferred` is an explicit non-blocking destination authorized by the
handoff.

## Chapters 1, 2, and 4: compatibility coverage

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 1.1-1.23 | Upstream | Mathlib set, measurable-space, topology/Borel, generated-space, and product APIs. Real generators use `Mathlib.MeasureTheory.Constructions.BorelSpace.Real`; no chapter wrapper was needed. |
| 1.27-1.61 | Upstream | Mathlib measure construction, continuity, extensionality, Stieltjes/CDF, and product-measure APIs. `Measure.ext_of_generateFrom_of_cover` is the generator uniqueness anchor. |
| 1.65 | Upstream | Exact pinned declaration `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` in `MeasureTheory/Measure/MeasuredSets.lean`. |
| 1.68-1.106 | Upstream | Mathlib completion/restriction, measurability, `FactorsThrough`, `Measure.map`, `IdentDistrib`, CDF, density, and change-of-variables infrastructure. Random variables remain functions. |
| 2.3-2.39 | Upstream | Mathlib `Indep`, `iIndep`, `IndepFun`, `iIndepFun`, Borel-Cantelli, zero-one, convolution, and regrouping APIs. Exact downstream anchors include `iIndepSet.indep_generateFrom_of_disjoint`, `IndepFun.hasLaw_add`, and `IndepFun.map_add_eq_map_conv_map₀`. |
| 2.40-2.45, 2.47 | Application | Percolation is recorded as textbook coverage and is not part of the stochastic-process foundation. |
| 2.46 | Deferred external | Kesten's theorem is cited rather than proved by Klenke; it is not imported into the trust boundary. |
| Exercise 2.2.3 | Implemented | `Probability/Distributions/Multinomial.lean`: `PMF.multinomial`, categorical counts, and `iIndepFun.hasLaw_categoricalCounts`. |
| 4.1-4.26 | Upstream | Mathlib simple/Bochner/Lebesgue integration, monotone convergence, Fatou, `Lp`, density, and `MeasureTheory/Integral/Layercake.lean`. No Chapter 4 project module was created. |

## Chapter 3: generating functions and branching

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 3.1 | Implemented | `Probability/GeneratingFunction/Basic.lean`: law-first `PMF.pgf` on `unitInterval`, real mass API, and measure/law bridge. |
| 3.2 | Implemented | `Analytic.lean`: continuity, interior smoothness, analytic uniqueness, `factorialMoment`, exact arbitrary-order derivative series, and the extended-value left-boundary theorem `PMF.tendsto_factorialDerivativeSeries`. |
| 3.3 | Implemented / bridge | Law-level `PMF.pgf_convolution`; random-variable bridge `ProbabilityTheory.IndepFun.integral_pow_add_eq_pgf_mul`; upstream `IndepFun.hasLaw_add` remains the canonical sum-law theorem. |
| 3.5 | Upstream | Mathlib generalized binomial/power-series analysis; no probability-specific duplicate. |
| 3.6 | Implemented | `Probability/Convergence/Discrete.lean`: atomwise-to-PGF, PGF-to-atomwise, their equivalence, and the discrete Scheffé bridge `PMF.tendsto_setMassReal_of_tendsto_mass` for arbitrary sets. |
| 3.7 | Implemented | `Probability/LimitTheorems/PoissonApproximation.lean`: non-i.i.d. Bernoulli triangular arrays under square-smallness or maximum-smallness, reusing Mathlib `PoissonLimitThm` for the i.i.d. binomial case. |
| 3.8 | Implemented | `Probability/GeneratingFunction/RandomSum.lean`: generic convolution powers, law-level random sums, and PGF composition. |
| 3.9-3.11 | Implemented | `Probability/Branching/Basic.lean` and `Extinction.lean`: generation-law iteration, finite extinction laws, and the corrected least-fixed-point theorem. |

## Chapter 5: moments, LLN, and Poisson processes

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 5.1, 5.3-5.8 | Upstream / implemented gap | Mathlib moments and independence integration are reused. `Probability/Moments/RandomSum.lean` supplies the absent Wald identity `integrable_stoppedSum_and_integral_eq_mul`. |
| 5.10 | Implemented | `Probability/Moments/RandomSum.lean`: `memLp_stoppedSum_and_variance_eq`, the Blackwell-Girshick variance identity with its `L²` conclusion. |
| 5.11-5.20 | Upstream | Mathlib Markov/Chebyshev and `Probability/StrongLaw.lean`, including `strong_law_ae`; no parallel LLN predicate. The quantitative weak-law specialization is a direct variance/Chebyshev reuse. |
| 5.22-5.23 | Implemented | `Probability/EmpiricalProcess/{CDF,StrongLaw,GlivenkoCantelli}.lean`: finite-sample APIs, common-event threshold laws, and full arbitrary-CDF Glivenko-Cantelli, including jump laws. |
| 5.25-5.27 | Deferred | Entropy/source coding belongs to a future `InformationTheory` package. |
| 5.28 | Implemented after audit | `Probability/MaximalInequality/Kolmogorov.lean`: square-submartingale core and independent centered square-integrable specialization. |
| 5.29 | Implemented | `Probability/MaximalInequality/StrongLawRate.lean`: dyadic Borel-Cantelli proof and the exact Klenke logarithmic rate. |
| 5.30, 5.32 | Deferred external | Rademacher-Menshov and Baum-Katz are cited external results and have no hidden dependency. |
| 5.33 | Implemented | `Probability/Process/{Path/Monotone,Path/RightContinuous,StationaryIncrements}.lean` and `Process/Poisson/Basic.lean`; the corrected common-a.s. monotone/right-continuous path condition is part of `IsPoissonProcess`. |
| 5.34 | Implemented | `Process/Poisson/{IntervalAxioms,IntervalAxiomsConverse,IntervalAxiomsConverseLaw}.lean`: P1-P5 forward direction and the full dyadic Bernoulli/Poisson-binomial converse. |
| 5.35 | Implemented | `Probability/Distributions/{Multinomial,Poissonization}.lean` and `Process/Poisson/UniformPoint.lean`: generic categorical-count laws and Poisson mixing yield joint independent Poisson counts for every finite interval partition of `[0,1]`. |
| 5.36 | Implemented | `ForMathlib/MeasureTheory/{SimplexVolume,CumulativeSumVolume,WithDensityEquiv}.lean` and `Process/Poisson/{ExponentialArrivalLaw,ArrivalTimes,FiniteIncrementLaw}.lean`: arbitrary finite ordered partitions, boundary-nullity, exact product law, and `isPoissonProcess_arrivalCountProcess_of_iid_exp`. |
| Exercise 5.1.1 | Implemented | `Probability/Moments/PaleyZygmund.lean`, including multiplicative and quotient forms. |
| Exercise 5.2.1 | Deferred | Bernstein-Chernoff is a concentration extension, not a Ch01-08 blocker. |
| Exercise 5.5.1 | Application | Recorded as the later successive-unit-interval consumer; no extra foundation declaration is required. |

## Chapters 6 and 7: convergence and `Lp`

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 6.1, 6.8, 6.20-6.23, 6.26-6.28 | Upstream / bridge | Mathlib measurable-distance, `L1`/`Lp`, Egorov, dominated convergence, and parametric-integral APIs. The 6.28 domain correction is recorded; no erroneous wrapper was added. |
| 6.2 | Implemented | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureLocal.lean`: all finite restrictions and finite-measure compatibility. |
| 6.7, Ex. 6.2.1 | Implemented | `LocalConvergenceMetric.lean`: exhaustion pseudometric on raw maps and genuine metric on `AEEqFun`, both characterizing local convergence. |
| 6.12-6.15 | Implemented | `FastConvergenceLocal.lean`, `ConvergenceInMeasureLocal.lean`, and `CauchyInMeasureLocal.lean`: Borel-Cantelli, subsequence, every-subsequence, and complete-target Cauchy theorems. |
| 6.16-6.18 | Implemented | `UniformIntegrableEnvelope.lean`, `DeLaValleePoussin.lean`, and `UniformIntegrableEnvelopeCompatibility.lean`: literal envelope/tail forms, finite compatibility, algebra, finite-family, and domination closure. |
| 6.19 | Implemented | `DeLaValleePoussin.lean`: both sufficient direction and finite-measure converse `UniformIntegrable.exists_superlinearEnvelope`. |
| 6.24 | Implemented | `uniformIntegrableByTailEnvelope_iff_klenkeUniformIntegrableByDensity` and the uniform-absolute-continuity/tightness characterization. |
| 6.25 | Implemented | `Probability/Convergence/LocalVitali.lean`: exact sigma-finite Vitali equivalence for local convergence plus envelope UI. |
| 7.1-7.2, 7.4-7.46 | Upstream | Mathlib `Lp`, Holder/Minkowski/Jensen, Fischer-Riesz, Hilbert projection, Radon-Nikodym, Lebesgue decomposition, signed-measure, and variation APIs. The 7.25 sign erratum is avoided by canonical reuse. |
| 7.3 | Implemented bridge | `LpLocalConvergence.lean`: `tendstoLocallyInMeasure_and_poweredEnvelope_iff_tendsto_eLpNorm`. |
| 7.47, 7.49, 7.50 | Deferred after audit | No exact general `Lp` dual representation theorem was found in pinned Mathlib. Per the handoff, this moves to general functional-analysis/ForMathlib work and does not block the stochastic-process foundation. |

## Chapter 8 and semantic regression gate

| Reference | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| 8.2-8.22 | Upstream / thin guard | Mathlib conditional expectation, conditional Jensen/contraction, kernels, Bayes/total probability, and independence APIs. `Probability/Conditional/SemanticGuard.lean` adds positive-mass `ConditionableEvent` instead of exposing a zero-mass fallback. |
| 8.24-8.38 | Upstream / thin guard | Mathlib `Kernel`, `condDistrib`, `StandardBorelSpace`, and `condExp_ae_eq_integral_condDistrib`. `conditionalKernel_ae_eq_of_compProd_eq` records law-a.e. version uniqueness. |
| Exercises 8.2.5-8.2.6 | Upstream | Conditional Markov/Cauchy-Schwarz follow canonical conditional Jensen/`Lp` APIs; no duplicate theorem survived the audit. |

Mandatory regressions compile in `Probability/GeneratingFunction/SemanticRegression.lean`,
`Probability/Convergence/SemanticRegression.lean`, `Probability/Conditional/SemanticGuard.lean`,
`Probability/EmpiricalProcess/GlivenkoCantelli.lean`, `Process/Poisson/Basic.lean`,
`FiniteIncrementLaw.lean`, and `ArrivalTimes.lean`. In particular, the exponential-arrival
construction has the explicit four-increment application
`fourIncrementLaw_arrivalCountProcess_of_iid_exp`.

# Process Core and Information Flow

This ledger is the complete disposition of the Process Core handoff. The package continues to use
functions `X : T → Ω → E`; it introduces no parallel process structure.

## Process laws, equivalence, and stationarity

| Source / function | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Klenke 9.6 process law | Upstream | `Measure.map`, `IdentDistrib`, and `Mathlib.Probability.Process.FiniteDimensionalLaws`; no local law structure. |
| Klenke 9.7(ii)-(iv) | Upstream | `HasIndepIncrements`, Mathlib Gaussian-process modules, and coordinatewise `Integrable`/`MemLp`; no wrapper predicates. |
| Klenke 9.7(v) stationary process | Implemented | `Probability/Process/Stationarity.lean`: `IsStationary` is equality of the full coordinate-product law under every shift, with coordinate and finite-coordinate consequences. |
| Klenke 9.7(vi) stationary increments | Inherited | `Probability/Process/StationaryIncrements.lean`, completed in the Ch01-08 milestone. |
| Klenke 21.1 modification / indistinguishability | Implemented | `Probability/Process/Equivalence.lean`: distinct quantifier orders, relation API, finite-coordinate law and coordinate-product law bridges. |
| Klenke 21.5(i) countable collapse | Implemented | `IsModification.indistinguishable_of_countable`, using Mathlib's `ae_all_iff`. |
| Klenke 21.5(ii) right-continuous collapse | Implemented | `IsModification.indistinguishable_of_rightContinuous`, using one countable dense sequence and right limits. |

## Paths, filtrations, and information flow

| Source / function | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Continuous/right/left path predicates | Implemented / inherited | `Path/Continuous.lean`, `Path/RightContinuous.lean`, and `Path/Cadlag.lean`; every a.s. property uses one common full-measure trajectory event. |
| Klenke 21.21 cadlag | Implemented | `IsCadlagPath` and `HasCadlagPaths`: right continuity plus an existential finite strict-left limit at every `t ≠ ⊥`; no totalized left-limit value. |
| Full Skorokhod topology | Deferred | Assigned to Functional Weak Convergence and Path-Space Limits; no topology is implied by the cadlag predicate. |
| Klenke 9.9-9.10 filtration/adaptedness | Upstream | `MeasureTheory.Filtration`, `Adapted`, and `StronglyAdapted`. |
| Klenke 9.11 natural filtration | Upstream / thin bridge | Mathlib `Filtration.natural` and `Filtration.stronglyAdapted_natural`; local `natural_le_of_stronglyAdapted` records exact minimality. |
| Klenke 9.12 / 25.5 predictable | Upstream | `Filtration.predictable`, `IsStronglyPredictable.isStronglyProgressive`, `.stronglyAdapted`, and `.iff_measurable_add_one`. |
| Klenke 21.22 right continuation | Upstream | `Filtration.rightCont`, `le_rightCont`, and `Filtration.IsRightContinuous`. |
| Klenke 21.22 usual conditions | Implemented | `Filtration.IsUsual`: right continuity plus containment of every ambient null set in the initial sigma-algebra. |
| Klenke 21.23 usual augmentation | Implemented | `Filtration/Augmentation.lean`: adjoin all null sets, move to `NullMeasurableSpace Ω P` with `P.completion`, then apply `rightCont`; `usualAugmentation_isUsual` proves both conditions. |
| Klenke 25.5(i) product measurable | Implemented | `IsProductMeasurable` is exactly measurability of `Function.uncurry X`, with coordinate/path/process bridges. |
| Klenke 25.5(ii) progressive | Upstream | Mathlib `IsProgressive` and `IsStronglyProgressive`. |
| Klenke 25.5(iii), Thm. 25.8 predictable chain | Upstream | Mathlib's predictable-to-progressive and predictable-to-adapted theorems; compile-time regression checks both and the discrete `n+1`/`n` characterization. |
| Klenke Remark 25.7 | Deferred external after audit | No approved theorem for adapted plus product-measurable implying a progressive modification was found. Klenke cites an external source; no unsupported converse is claimed. |
| Klenke Thm. 25.8 regular paths | Implemented bridge | `StronglyAdapted.isStronglyProgressive_of_rightContinuous` and `_of_leftContinuous`, proved by countable-range ceiling/floor grids. The right-continuous theorem also supplies global joint measurability. |
| Klenke Thm. 25.8 a.s. regular paths | Implemented | Under `Filtration.IsUsual`, the two `exists_isStronglyProgressive_modification_of_has...Paths` theorems replace the process by zero on the one common null event of bad trajectories. |

## Random times and stopping

| Source / function | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Klenke 9.15 stopping time | Upstream | Mathlib `IsStoppingTime` with codomain `WithTop T`; infinity is never represented by a finite sentinel. |
| Klenke 9.16 countable characterization | Upstream | `IsStoppingTime.measurableSet_eq` and `isStoppingTime_of_measurableSet_eq`. |
| Klenke 9.18 closure operations | Upstream | `IsStoppingTime.min`, `.max`, `.add_const`, and `.add` with their exact order/countability hypotheses. |
| Klenke 9.19 / 9.21 stopped information | Upstream | `IsStoppingTime.measurableSpace`, `measurableSpace_mono`, and related bound theorems. |
| Klenke 9.22-9.23 stopped value/process | Upstream / thin bridge | Mathlib `stoppedValue`, `stoppedProcess`, and `measurable_stoppedValue`; local `measurable_stoppedValue_of_rightContinuous` exposes the regular-path information-flow chain. |
| Hitting times | Upstream | `Mathlib.Probability.Process.HittingTime`: `hittingBtwn`, `hittingAfter`, and the adaptedness-to-stopping-time theorems with their required discrete/order assumptions. |
| Doob regularization | Deferred | Assigned to the later martingale/path-regularity package, as required by the handoff. |

## Process Core semantic regression gate

`Probability/Process/SemanticRegression.lean` formally checks the diagonal-spike modification that
is not indistinguishable, equality of its coordinate-product law with zero, the Boolean
Rademacher counterexample with equal one-time marginals but nonstationary pair law, natural
filtration minimality, predictable/progressive/adapted chains, a right-continuous filtration that
is not usual, an always-infinite stopping time on a probability-one event, and common-event cadlag
semantics. The right/left grid theorems, stopping-value bridge, and completed usual augmentation
provide the remaining positive acceptance chains.

# Discrete Martingale Calculus and Exchangeability

This is the complete disposition of the third handoff. All `BUILD` rows are kernel-checked; no
item is represented by a conclusion-shaped premise or a weakened surrogate statement.

## Part I: discrete martingale calculus

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Martingale/submartingale adapters | Implemented / upstream | `Martingale/Adapters.lean` retains Mathlib's canonical predicates and supplies only exact conversion bridges. |
| Discrete stochastic integral | Implemented | `Martingale/DiscreteIntegral.lean`: named transform, zero/successor/sum formulas, predictability interface, integrability, and martingale preservation. |
| Pathwise quadratic variation and predictable bracket | Implemented | `Martingale/QuadraticVariation.lean`: square increments, conditional bracket increments, square-minus-bracket martingale, and stopped-process compatibility. |
| Optional sampling | Implemented / upstream | Canonical bounded optional sampling is reused; `OptionalSampling/UniformIntegrable.lean` proves UI stopped values and the a.s.-finite conditional-expectation identity. |
| Doob inequalities | Implemented / upstream | Mathlib maximal inequality is reused; `Inequalities/DoobLp.lean` exposes the sharp `p/(p-1)` real-valued norm form with `1 < p`. |
| Martingale representation | Implemented with structural domain | `Representation/Binary.lean` proves representation from explicit binary splitting data; no unrestricted false representation theorem is claimed. |
| Reverse martingales | Implemented | `Martingale/Reverse.lean`: reverse conditional expectations and a.e./`L¹` convergence to the infimum sigma-field. |
| Klenke 11.14 | Implemented | `Convergence/QuadraticVariation.lean`: predictable cutoff localization proves a.s. convergence on the event of finite predictable quadratic variation. |

## Part II: exchangeability and de Finetti

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Exchangeability | Implemented | `Exchangeability/Basic.lean`: equality of every ordered finite-dimensional law at distinct indices, plus finite-permutation and reindexing bridges. |
| Finite symmetrization | Implemented | `Symmetrization.lean`: linear idempotent averaging projection and exact permutation invariance. |
| Exchangeable and tail sigma-fields | Implemented | `SigmaFields.lean`: decreasing prefix-invariant fields, their infimum, tail fields, and the raw inclusion `T ≤ E`. |
| Conditional expectation and means | Implemented | `ConditionalExpectation.lean` and `Means.lean`: symmetric conditional expectations, reverse-martingale sample means, a.e./`L¹` limits, prefix symmetrization, and exchangeable LLNs. |
| Empirical probability measure | Implemented | `EmpiricalMeasure.lean`: nonempty finite samples, multiplicities, integral/CDF bridges, and recovery of the unordered tuple from its empirical measure. |
| Symmetric-statistic factorization | Implemented | `IsPermutationInvariant.exists_factorThrough_empiricalProbabilityMeasure` gives the plain set-theoretic factorization; measurable factorization remains explicitly a separate Doob-Dynkin question. |
| Conditional iid / de Finetti | Implemented internally | `StochLean/Internal/Exchangeability` owns the reverse-martingale and directing-measure proof chain; `ConditionalIID.lean` exposes the structural product-mixture equivalence and `Bernoulli.lean` gives the Boolean specialization. |
| Invariant field equals tail modulo law | Implemented | `InvariantTail.lean`: finite-coordinate conditional expectations are moved beyond every cutoff and closed in `L¹`, yielding `exchangeableMeasurableSpace_eq_tail_modulo`. |
| Hewitt-Savage | Implemented | `hewittSavage_zero_one` combines the modulo-tail theorem with Mathlib's Kolmogorov zero-one law. |

## Third-milestone regression gate

`Martingale/SemanticRegression.lean` checks predictability indexing, transform recursion,
`WithTop` stopping, sharp Doob hypotheses, structural binary representation, and the finite-bracket
criterion. `Exchangeability/SemanticRegression.lean` checks exchangeable-but-dependent and
equal-marginal-but-nonexchangeable models, nonempty empirical measures, empirical factorization,
modulo-tail equality, Hewitt-Savage, and the Bernoulli de Finetti facade.

# Measure Convergence and Projective Construction

This is the complete disposition of the fourth handoff. Weak convergence is Mathlib's ordinary
topology on `ProbabilityMeasure`; no local synonym such as `Weak` or `WeaklyConverges` is defined.
Likewise, projective families and limits use only Mathlib's `IsProjectiveMeasureFamily` and
`IsProjectiveLimit` vocabulary.

## Part I: convergence of probability and locally finite measures

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Weak convergence | Upstream | Ordinary `Tendsto` in `ProbabilityMeasure`, characterized by `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. |
| Portmanteau | Upstream | Reuse open/closed liminf/limsup criteria and `tendsto_measure_of_null_frontier_of_tendsto`; no local duplicate. |
| Tightness and Prokhorov | Upstream | Reuse `IsTightMeasureSet`, `isCompact_closure_of_isTightMeasureSet`, and `isTightMeasureSet_of_isCompact_closure`. |
| Convergence in distribution | Upstream | Reuse `TendstoInDistribution`, `TendstoInMeasure.tendstoInDistribution`, continuous mapping, and Slutsky theorems. |
| A.e.-continuous mapping | Implemented gap | `Probability/MeasureConvergence/Mapping.lean`: Portmanteau bridge `ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous`. |
| Vague convergence | Implemented distinct gap | `ForMathlib/MeasureTheory/Measure/VagueConvergence.lean`: locally finite `TendstoVaguely`, weak-to-vague, compact-space equivalence, and escaping-Dirac convergence. |
| Weak/vague boundary | Implemented regression | `escapingDirac_tendstoVaguely_zero`, `escapingDirac_not_isTightMeasureSet`, and `escapingDirac_not_tendsto_probabilityMeasure` formally exhibit loss of mass at infinity. |
| CDF convergence criterion | Upstream / implemented consumer | Mathlib's rational `Ioo` convergence-determining pi-system is consumed by `tendsto_empiricalProbabilityMeasurePM_ae`. |
| Empirical weak convergence | Implemented | `Probability/MeasureConvergence/Empirical.lean` bundles the milestone-three empirical measure and proves almost-sure weak convergence to the common law from the strict and non-strict empirical CDF laws. |
| Levy continuity and characteristic functions | Upstream | Reuse `MeasureTheory/Measure/LevyConvergence.lean`; no parallel characteristic-function convergence theorem. |
| Functional/path-space weak convergence | Deferred | Assigned to the later Skorokhod/path-space package; the present milestone makes no topology on path predicates. |

## Part II: products, kernels, and projective extension

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Product coordinates and cylinders | Upstream | `measurable_pi_apply`, `measurableCylinders`, `cylinder`, and `generateFrom_measurableCylinders`. |
| Arbitrary probability products | Upstream | `Measure.infinitePi`, `isProjectiveMeasureFamily_pi`, `isProjectiveLimit_infinitePi`, `infinitePi_map_restrict`, and `infinitePi_cylinder`. |
| Kernels and Ionescu--Tulcea | Upstream | Reuse `Kernel.traj`, `Kernel.trajMeasure`, their Markov/probability instances, finite-trajectory recovery, and conditional-distribution theorem. |
| Projective vocabulary | Upstream | Only `IsProjectiveMeasureFamily` and `IsProjectiveLimit`; the regression pins the direction `P J = (P I).map (Finset.restrict₂ hJI)`. |
| Arbitrary-index standard-Borel extension | Implemented internally from an audited reference | `StochLean/Internal/KolmogorovExtension` contains the project-owned proof, and `MeasureTheory/Constructions/KolmogorovExtension.lean` exposes `projectiveLimitOfStandardBorel`, finite/probability instances, finite-dimensional recovery, uniqueness, and the `∃!` theorem. No external package is imported or linked. |
| Public domain | Implemented | The facade requires only measurable spaces plus `StandardBorelSpace`; temporary Polish topologies from `upgradeStandardBorel` remain proof-local and no topology occurs in public types. |
| Empty index type | Implemented and tested | Probability preservation and unique existence compile for `ι = Empty`; no `Nonempty ι` assumption is introduced. |
| Canonical process | Reused representation | The process is exactly `fun i ω ↦ ω i` on the product space; no process structure or path topology is added. |
| Probability vs finite mass | Implemented regression | `twoMassFiniteFamily` and `twoMassLimit` form a finite projective system of mass two and formally fail `IsProbabilityMeasure`. |
| Downstream de Finetti | Regression reuse | The already completed `IsExchangeable.hasDeFinettiRepresentation` remains part of the full build and axiom audit after the new projective dependency is added. |

## Mandatory semantic regressions

| # | Acceptance case | Formal resolution |
| ---: | --- | --- |
| 1 | `δ_n` tends vaguely to zero but has no probability weak limit | `escapingDirac_tendstoVaguely_zero`; non-tightness and no weak probability limit are separate theorems. |
| 2 | `δ_(1/(n+1)) ⇒ δ_0`, while mass of `{0}` does not converge | `shrinkingDirac_tendsto_dirac_zero` and `shrinkingDirac_singleton_mass_not_tendsto`. |
| 3 | Measurable discontinuous mapping can destroy weak convergence | `zeroDetector_not_continuousAt_zero` and `zeroDetector_mapped_shrinkingDirac_not_tendsto`. |
| 4 | Convergence in probability implies convergence in distribution, not conversely | Canonical implication compiles; `boolFlip_tendstoInDistribution` plus `boolFlip_not_tendstoInMeasure` proves the converse false. |
| 5 | Weakly convergent sequences are controlled by tightness/Prokhorov | The escaping-Dirac contradiction invokes `isTightMeasureSet_of_isCompact_closure`. |
| 6 | Weak and vague convergence stay distinct, with an exact compact bridge | `ProbabilityMeasure.tendstoVaguely_of_tendsto` and `tendsto_iff_tendstoVaguely`. |
| 7 | Empirical CDF results feed an actual empirical weak limit | `tendsto_empiricalProbabilityMeasurePM_ae`; `empiricalProbabilityMeasure_Iic` and `_Iio` are the reused interfaces. |
| 8 | Coordinate maps are measurable and cylinders generate the product sigma-field | Compile-time examples in `MeasureTheory/Constructions/SemanticRegression.lean`. |
| 9 | Projectivity direction is not reversed | Direct typed example of `hP I J hJI`. |
| 10 | A concrete three-coordinate system recovers all prescribed marginals | `threeCoinFamily_isProjective` and `threeCoin_projectiveLimit_recovers`. |
| 11 | Empty index type needs no `Nonempty` assumption | `emptyIndex_projectiveLimit_isProbability` and `emptyIndex_existsUnique_projectiveLimit`. |
| 12 | Singleton and arbitrary finite marginals are recovered | Generic `projectiveLimitOfStandardBorel_map_restrict`, instantiated by the three-coordinate regression. |
| 13 | Independent arbitrary products use the canonical product measure | Direct regressions for `infinitePi_map_restrict` and `infinitePi_cylinder`. |
| 14 | Abstract standard-Borel coordinates require no chosen topology | A public-domain compile example has only `MeasurableSpace` and `StandardBorelSpace` assumptions. |
| 15 | Reference implementation names do not leak into public declarations | Facade declarations and axiom audit expose only StochLean/`MeasureTheory` names; the adapted proof is owned by `StochLean.Internal.KolmogorovExtension`, with no external import boundary. |
| 16 | Different compatible Polish upgrades cannot change the result | `IsProjectiveLimit.eq_projectiveLimitOfStandardBorel` reduces any candidate to Mathlib's unique finite projective limit. |
| 17 | Arbitrary-index extension internalizes the audited reference proof | The implementation adapted from audited commit `7d76e184c3d2138a2741baf923b57e9a01b9cf25` is compiled under project namespaces; the exact reference revision and provenance remain in the audit ledger. |
| 18 | Extension is not inferred from finite products or Ionescu--Tulcea | The proof boundary is explicit: the arbitrary-index facade uses the project-owned internal extension theorem; product and sequential-kernel examples remain separate. |
| 19 | A finite projective family is not automatically probabilistic | `twoMassLimit_not_isProbabilityMeasure`. |
| 20 | A probability projective family infers a probability limit | Facade probability instance and the three-coordinate/empty-index instance checks. |
| 21 | Reference revision, license, holes, and build are audited | Exact Git revision, Apache-2.0 license, empty `sorry`/`admit`/`axiom`/`unsafe` scan, and 1773-job reference build are recorded in `MATHLIB_AUDIT.md`; the adapted StochLean sources also pass the ordinary project build. |
| 22 | Existing de Finetti work remains compatible | Full `StochLean` build and `Audit/Axioms.lean` recheck `IsExchangeable.hasDeFinettiRepresentation`. |
| 23 | No path regularity is manufactured by a coordinate product law | Public output is only a raw product-space measure and coordinate recovery; path topology remains deferred. |

The mandatory cases compile in `Probability/MeasureConvergence/SemanticRegression.lean` and
`MeasureTheory/Constructions/SemanticRegression.lean`. All new milestone declarations are also
listed in `Audit/Axioms.lean`.

# Markov Processes, Kernels, Semigroups, and Convergence

This section is the complete joint disposition of the two Markov handoffs. Public APIs use raw
process functions and Mathlib kernels. No bundled Markov-chain/process type, duplicate kernel,
duplicate irreducibility predicate, or duplicate projective-limit construction is introduced.

## Information, transitions, and canonical laws

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Future information | Implemented | `Process/Filtration/Future.lean`: `futureMeasurableSpace`, antitonicity, the discrete `tailFromMeasurableSpace` bridge, and the infimum identity for the canonical tail sigma-field. |
| Forward transition systems | Implemented | `Markov/TransitionSystem.lean`: proof-indexed kernels exist only for `r <= s`; diagonal identity and `K r t = K s t comp K r s` use Mathlib's chronological composition order. |
| Homogeneous semigroups | Implemented | `Markov/Semigroup.lean`: `IsMarkovSemigroup`, commuting/opposite-order laws, kernel powers, and the natural-time transition-system bridge. |
| Kernel-free Markov property | Implemented | `Markov/Transition.lean`: event conditional expectations are primary; integrable future functions, bounded state tests, finite cylinders, and conditional-independence bridges are derived. |
| Transition representation | Implemented | `HasTransitionSystem` remains separate from `HasMarkovProperty`; it implies the kernel-free property and supports the exact countable-time strong-Markov event theorem. |
| Discrete canonical path law | Implemented / upstream | `Chain/PathLaw.lean` is a thin homogeneous specialization of Mathlib `Kernel.traj`; finite histories, one-time kernel-power marginals, adjacent-coordinate laws, and measurable state-map functoriality are proved. |
| General canonical coordinate law | Reused | Arbitrary-index Standard-Borel existence and uniqueness are the previous milestone's `projectiveLimitOfStandardBorel` and `existsUnique_isProjectiveLimit_of_standardBorel`; the process is the raw coordinate map. No Markov-private KET wrapper is added. |

## Countable chains, recurrence, invariance, and periodicity

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Reachability | Implemented bridge | Mathlib `Kernel.IsIrreducible Measure.count` remains canonical; `CanReach` is bridged to positive kernel powers without confusing its zero-time diagonal case with positive return. |
| Hitting and return times | Implemented | `Countable/Hitting.lean` uses `hittingAfter ... 1`, preserves `WithTop` infinity, and defines extended mean return time. |
| Recurrence / transience | Implemented | `Countable/Recurrence.lean` defines statewise recurrence, transience, positive and null recurrence and proves communication propagation. |
| Green kernel | Implemented | `Countable/Green.lean`: the ENNReal occupation series, path-law occupation identity, and recurrence criteria. |
| Renewal and hitting probabilities | Implemented | `Renewal.lean`, `HittingProbability.lean`, and `SetHitting.lean` prove first-return renewal equations, killed/safe kernel recursions, and almost-sure hitting under irreducibility plus an invariant probability. |
| Excursion occupation | Implemented | `Excursion.lean` and `Invariant.lean` construct the occupation measure, prove its singleton/mass formulas and invariance, and normalize it in the positive recurrent case. |
| Invariant probability and Kac | Implemented | Invariant probability implies positive recurrence, is unique under irreducibility, satisfies Kac's formula, and exists exactly in the irreducible positive recurrent case. |
| Periodicity | Implemented | `Periodicity.lean`: return-time gcd, communication invariance of period, eventual positivity on admissible residue classes, and the global aperiodicity interface. |

## Coupling and Klenke 18.11--18.13

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Generic coupling | Implemented | `Probability/Coupling/Basic.lean` defines only the marginal relation and event/full-TV bounds. |
| TV normalization correction | Implemented | `Coupling/TotalVariation.lean` uses the full signed-measure convention and proves the factor-2 mismatch bound; mutually singular Boolean Dirac laws regress to distance `2`. |
| Path coupling | Implemented | Couplings are measures on pairs of canonical path laws; successful coupling is the tail-mismatch condition and is equivalent to a.s. eventual equality. |
| Independent coalescent | Implemented semantically | `Coalescent.lean` uses the product kernel away from the diagonal and an absorbing diagonal, avoiding the corrupted OCR case split. |
| Klenke 18.11 | Implemented | `Klenke.lean` proves diagonal hitting for the independent product and semantic coalescent chains from irreducibility, aperiodicity, and an invariant probability. |
| Klenke 18.12 | Implemented | `Convergence.lean` turns successful coalescence into full-TV convergence between arbitrary rows, with the corrected factor `2`. |
| Klenke 18.13 | Implemented | `Equilibrium.lean` proves the full equivalence among aperiodicity, convergence from every state, convergence from some state, and convergence from every initial probability. |

## Bounded Q-matrices and Feller semigroups

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Q-matrix | Implemented | `Generator/QMatrix.lean` uses off-diagonal nonnegativity and summability, diagonal row balance, `exitRate`, and singleton right derivatives in `HasQMatrix`. |
| Uniformization | Implemented | `Generator/Uniformization.lean` constructs the one-step kernel and Poisson-mixture semigroup, including the mandatory safe `Lambda = 0` identity branch, semigroup law, and generator recovery. |
| Rate independence / canonical uniqueness | Implemented | `Generator/Uniqueness.lean` proves the exact lazy-kernel relation, Poisson Cauchy convolution, independence from any two valid dominating rates, and unique existence of `IsCanonicalBoundedQSemigroup`. This is law-level uniqueness of the canonical bounded-Q construction, not raw equality of processes on unrelated sample spaces. |
| Poisson acceptance | Implemented | `Generator/Poisson.lean` proves the pure-birth Q-matrix, recovers `poissonMeasure (rate * t)` from zero at positive rate, checks the zero-rate law, and recovers the generator. |
| Klenke Feller predicate | Implemented | `Feller.lean` uses Mathlib `ZeroAtInftyContinuousMap`, includes the Markov semigroup laws, pointwise continuity at zero, C0 preservation, contraction operators, and correct operator composition order. |
| Weak/stochastic continuity | Implemented | The Feller interface reuses the measure-convergence layer for vague transition measures, weak probability laws on compact spaces, state-variable weak continuity, and convergence to `dirac x` at time zero. |
| Feller pointwise-to-sup-norm equivalence | Deferred by source protocol | Klenke 21.26 points outward; Revuz--Yor, Chapter III, Proposition 2.4 is the locator to audit. The proof text was not available in the local source set, so no original substitute is attempted. |
| Klenke 21.27 RCLL strong-Markov realization | Deferred by source protocol | Klenke points to Rogers--Williams Vol. 1, Chapter III.7ff/8ff and Revuz--Yor Chapter III, Theorem 2.7. Those proof texts were not locally accessible, so realization is not claimed. |

## Markov source corrections and semantic regressions

- Kernel orientation is pinned by an explicit noncommuting deterministic-kernel regression:
  `eta comp kappa` means first `kappa`, then `eta`.
- `CanReach x x` uses time zero, while positive return and recurrence use `hittingAfter ... 1`.
- The coalescent kernel is defined by product/absorbing semantics, not the OCR piecewise formula.
- Full TV has diameter `2`; coupling mismatch bounds therefore carry a factor `2`.
- The Poisson Q-matrix regression has a positive successor entry and a negative diagonal entry,
  pinning the OCR-sensitive `x != y` condition.
- Zero-rate domination forces the zero Q-matrix and gives the identity semigroup; no division by
  zero is used.
- Two distinct valid domination rates give definitionally different construction inputs but the
  same semigroup by `uniformizedSemigroup_rate_independent`.
- `IsFellerSemigroup` remains Klenke's pointwise-at-zero predicate; no second strong-continuity
  definition is introduced.

## Blocker and deferred-dependency ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| MK-B01 | RESOLVED | Process Core supplied natural/usual filtrations, common-event path predicates, progressive measurability, and stopping-time APIs consumed by the Markov layer. |
| MK-B02 | RESOLVED | Measure Convergence and Projective Construction supplied weak/vague convergence, Ionescu--Tulcea, and the Standard-Borel projective-limit facade. |
| MK-B03 | RESOLVED | Bounded-Q construction and canonical semigroup uniqueness are proved by uniformization and rate independence, including `Lambda = 0`; Poisson is the cross-package acceptance case. |
| MK-B04 | DEFERRED | Future Feller/functional-analysis owner. Revuz--Yor III, Proposition 2.4 must be concretely retrieved and audited before the pointwise-to-sup-norm theorem is added. Current C0 preservation, contraction, operator, weak, and stochastic-continuity APIs are unaffected. |
| MK-B05 | DEFERRED | Future path-regularization owner. Retrieve/audit Rogers--Williams III.7ff/8ff or Revuz--Yor III, Theorem 2.7 before adding the RCLL strong-Markov realization. No current theorem claims every realization is RCLL. |
| MK-D01 | DEFERRED | Semimartingales and stochastic integration belong to the later package planned in this repository. |
| MK-D02 | DEFERRED | Stochastic differentials and SDEs belong to the separate package stated in `README.md`. |
| MK-D03 | DEFERRED | MCMC applications and spectral rates belong to a future application/finite-state layer and do not block the foundation. |

All implemented Markov declarations are included in the full build and representative
load-bearing results are inspected in `Audit/Axioms.lean`. The authorized external rows are the
only deferred items; neither is replaced by a placeholder declaration.

# Fourier Probability and Classical Limit Theorems

This is the final implementation disposition of
`StochLean_FourierProbability_ClassicalLimitTheorems_Design_v0.1.pdf`. All package-owned mandatory
`BUILD` rows are implemented. Audit-only external results remain explicitly deferred, and the two
generic `BUILD-CANDIDATE` moment/Pólya gaps remain recorded rather than being replaced by stronger
or surrogate statements.

## Characteristic functions and classical limits

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Characteristic functions and independent sums | Reused | Mathlib's measure-first `charFun`, `IndepFun.charFun_map_add_eq_mul`, and finite-family characteristic-function product API. No StochLean characteristic-function object was added. |
| Weak convergence and Levy continuity | Reused | Ordinary `Tendsto` on `ProbabilityMeasure` and `ProbabilityMeasure.tendsto_iff_tendsto_charFun` from `Mathlib.MeasureTheory.Measure.LevyConvergence`. |
| Scalar iid CLT | Reused | `tendstoInDistribution_inv_sqrt_mul_sum` and its centered form from `Mathlib.Probability.CentralLimitTheorem`. |
| Multivariate Gaussian laws | Reused | Mathlib's positive-semidefinite covariance Gaussian construction, including singular covariance. |
| Cramer--Wold / multivariate iid CLT bridge | Implemented | `LimitTheorems/MultivariateCLT.lean` proves the iid vector CLT by scalar projections, Mathlib's scalar iid CLT, characteristic-function weak convergence, and the canonical `multivariateGaussian`; merely positive-semidefinite, including singular, covariance is accepted. |
| Polya criterion | STILL-BLOCKED candidate | No exact active-pin/local theorem with the frozen continuity/evenness/range/convexity assumptions was found. The candidate is not required by the downstream LSII interface and no differentiability surrogate is exported. |
| Moment determinacy and even-derivative converse | STILL-BLOCKED candidate | Mathlib supplies moment-to-characteristic-function derivatives, but the converse/determinacy declarations with the exact source hypotheses are absent. They remain generic analysis candidates rather than probability-private approximations. |
| Bochner theorem | DEFERRED | Klenke delegates the proof and neither cited source was recovered. The independent Apache-2.0 `mrdouglasny/bochner` implementation was audited at `58405ecd328cf8383a1c0b53d37605fe61a0b3f6`, but is not the cited proof and targets a different Mathlib revision, so it is reference-only and is not a dependency or copied API. |
| Berry--Esseen | DEFERRED | Klenke's external source has not been recovered and audited; no independent replacement is declared. |

## Triangular arrays, Lindeberg, and ordered series

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Raw triangular arrays and nonempty rows | Implemented foundation | `LimitTheorems/TriangularArray.lean`: `TriangularArray` and the separate `HasNonemptyRows` predicate. |
| Measurability, row independence, centering, normalization | Implemented foundation | Separate predicates; no cross-row independence or hidden centering/normalization. |
| Row-sum variance | Implemented | `variance_triangularRowSum_eq_sum` and `variance_triangularRowSum_eq_one`. |
| Null arrays | Implemented | Finite-row maximum-tail definition, entry bound, eventual-uniform formulation, and `isNullArray_iff_eventual`. A sum of tail probabilities is not used as the definition. |
| Positive-scale Lindeberg/Lyapunov predicates | Implemented foundation | `LimitTheorems/Lindeberg.lean`; ENNReal nonnegative expectations and explicit positive scales avoid division by zero. |
| Lyapunov implies Lindeberg | Implemented | Both exponent and source-style positive-`delta` formulations prove the matching positive-scale Lindeberg condition in `LimitTheorems/Lindeberg.lean`. |
| Lindeberg implies null array | Implemented | `SatisfiesUnitLindeberg.isNullArray` proves the unit-scale result by a restricted-measure Markov bound; `SatisfiesLindeberg.isNullArray` applies it to independent normalized rows. |
| Lindeberg--Feller forward CLT | Implemented | `SatisfiesLindeberg.tendsto_map_triangularRowSum_standardGaussian` closes the forward theorem through the attribution-preserving internal characteristic-function proof. No converse or false `iff` is exported. |
| Lindeberg--Feller converse | DEFERRED | Klenke cites source [155], Theorem III.4.3; its proof has not been recovered and audited. |
| Ordered series semantics | Implemented foundation | `Series/ThreeSeries.lean`: ordinary prefix sums, common-event a.s. random convergence, exact `abs <= K` truncation, and the three source conditions. |
| Kolmogorov three-series theorem | Implemented | `kolmogorovThreeSeries_iff` proves both directions with inclusive truncation and ordered convergence on one common a.s. event; `orderedRandomSeriesConvergesAE_of_variance_tsum_lt_top` discharges Exercise 6.1.4 inside the project. |

## FP-LT blocker and deferred ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| FP-B01 | RESOLVED | Active-pin characteristic-function, Levy-continuity, scalar-CLT, Gaussian, independence, and weak-topology APIs were mapped to Mathlib. |
| FP-B02 | RESOLVED | No local overlap was found; final raw triangular-array public names are implemented. |
| FP-B03 | STILL-BLOCKED candidate | Exact Pólya and moment-converse statements are confirmed genuine generic gaps. Their status is explicit and they are not hidden prerequisites of any exported milestone theorem. |
| FP-B04 | DEFERRED | Recover and audit [155], Theorem III.4.3 before any Lindeberg--Feller converse. |
| FP-B05 | DEFERRED | Recover and audit Klenke's cited Bochner proof before adding a theorem. |
| FP-B06 | DEFERRED | Recover and audit [155], Chapter III, Section 11 before Berry--Esseen. |
| FP-B07 | RESOLVED | The full ordered Kolmogorov three-series equivalence and finite-variance helper are proved locally. |
| FP-B08 | RESOLVED | The multivariate iid CLT bridge is proved for all finite-dimensional PSD covariance matrices. |
| FP-D01 | DEFERRED | Infinite divisibility and Levy--Khintchine are owned by LSII below. |
| FP-D02 | DEFERRED | Convolution semigroups and SII are owned by LSII below. |
| FP-D03 | DEFERRED | Donsker and topological path-space weak convergence belong to Functional Weak Convergence. |
| FP-D04 | DEFERRED | Brownian construction/path regularity belongs to BM-PR below. |

`LimitTheorems/SemanticRegression.lean` pins the package semantics: predicate separation, nonempty
rows, maximum rather than sum nullness, positive scales, Lyapunov and Lindeberg bridges, unit row
variance, absence of a converse `iff`, canonical weak topology, singular PSD multivariate limits,
ordered conditional convergence, common-event random-series convergence, ordered expectation
series, inclusive truncation, and the internal Exercise 6.1.4 dependency.

# Levy and Stationary Independent Increments Foundations

This is the current disposition of
`StochLean_Levy_StationaryIndependentIncrements_Design_v0.1.pdf`. The implementation below is
entirely project-owned and links only Mathlib.  The general and nonnegative real
Levy--Khintchine chains, SII construction, weak closure, and real stable classification are
closed. The package is not fully complete: the corrected Remark 16.23 closed form still needs
its Gamma/trigonometric integral identification with the actual Levy exponent. The necessary
location correction and the closed-form definitions alone do not prove that theorem.

## Law and process foundations

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Probability-law convolution and powers | Implemented | `Convolution/Semigroup.lean` closes Mathlib measure convolution in `ProbabilityMeasure` and proves associativity, commutativity, Dirac laws, and additive convolution powers. |
| Basic/continuous convolution semigroups | Implemented foundation | The basic predicate contains only the semigroup law; the positive-time weak limit at zero is a separate refinement. |
| Exercises 14.4.1--14.4.4 | Implemented | Exact semigroup roots, weak convergence to `δ₀`, continuity propagation, and nonnegative-support closure are proved. |
| SII predicate | Implemented | `Process/StationaryIndependentIncrements.lean` combines the existing `HasStationaryIncrements` and Mathlib `HasIndepIncrements` without a bundled Levy-process type. |
| SII to convolution semigroup | Implemented | `HasStationaryIndependentIncrements.isConvolutionSemigroup` uses genuine increment independence and stationary laws. |
| Semigroup to coordinate SII process | Implemented | Project-owned finite-law consistency, KET projective construction, and genuine finite-family increment independence are in the three `StationaryIndependentIncrements*` construction modules. |
| Infinite divisibility | Implemented foundation | Law-first positive-integer roots; every full-time convolution-semigroup marginal is infinitely divisible without a continuity assumption. |
| Compound Poisson | Implemented foundation | Genuine Poisson mixture over convolution powers, explicit zero-rate law, and zero-safe `ofFiniteMeasure`; the latter recovers the rate/jump presentation on `r • μ`. |
| Compound-Poisson intensity addition and ID | Implemented | `CompoundPoisson.law_add` proves the convolution law by Tonelli and Poisson addition; the induced convolution semigroup proves `CompoundPoisson.isInfinitelyDivisible`, including zero intensity. |
| Compound-Poisson characteristic function | Implemented | The exponential characteristic-function formula and zero-safe finite-measure form are proved internally. |
| Compound-Poisson approximation of ID laws | Implemented | `Approximation.lean` proves the triplet and canonical-root compound-Poisson approximations and Theorem 16.5 forward direction. |

## Levy measures, triplets, and stable laws

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Minimal Levy measure | Implemented foundation | Atom zero plus finite `lintegral (min 1 (x^2))`; `IsLevyMeasure.sigmaFinite` is derived from finite level sets and is not installed globally. |
| Infinite-activity acceptance example | Implemented | `geometricLevyMeasure` is an explicit countable atomic measure with atoms tending to zero; `isLevyMeasure_geometricLevyMeasure` proves the truncated second moment is finite, while `geometricLevyMeasure_univ` proves its total mass is infinite. |
| Fixed truncation and triplet data | Implemented foundation | `levyTruncation x = x` exactly on `abs x < 1`; `LevyTriplet` contains only Gaussian variance, drift, jump measure, and its Levy-measure proof. |
| Levy exponent integrability | Implemented | Internal complex Taylor bounds, small/large-jump integrability, truncation changes, finite restrictions, and convergence are proved. |
| Real Levy--Khintchine existence and uniqueness | Implemented | `LevyKhintchine.lean` constructs laws from triplets; weighted-root and sine-truncation extraction prove the converse and uniqueness in `LevyKhintchineConverse.lean`. |
| Nonnegative Levy--Khintchine | Implemented | `NonnegativeExtraction.lean` proves Prokhorov extraction, reconstructs the deterministic/positive-jump pair, preserves the complete exponent, and proves the source-facing unique-pair equivalence. |
| ID to continuous semigroup and SII | Implemented | Time-scaled triplets yield continuous convolution semigroups and the projective coordinate SII law. |
| Stable predicates | Implemented foundation | Non-Dirac broad, strict, and indexed predicates with genuinely positive affine scale; indexed-to-unindexed and strict-to-broad bridges; and zero-safe `signedLogAbs`. |
| Broad stable implies ID | Implemented | `IsStableInBroadSense.isInfinitelyDivisible` explicitly inverts the positive affine witness and divides the translation among the positive number of convolution roots. |
| Triplet affine transformation | Implemented | Positive affine maps include the exact truncation drift correction; representation, convolution-power scaling, Gaussian, jump, and drift identities follow from triplet uniqueness. |
| Weak closure (Corollary 16.9) | Implemented | `WeakClosure.lean` constructs a continuous limiting exponent, realizes every positive-integer root by Levy continuity, and proves `isInfinitelyDivisible_of_tendsto`. |
| Stable classification (Theorem 16.22) | Implemented | Broad stability yields an index in `(0,2]`; the Levy measure has the exact two-sided power-law density; `alpha = 2` is Gaussian; and `0 < alpha < 2` has a nontrivial jump coefficient. Exact affine centerings give the `alpha != 1` strict shift and the symmetric `alpha = 1` branch. |
| Explicit stable exponent (Remark 16.23) | PARTIAL; corrected integral identity still missing | `StableExponent.lean` defines the two Gamma/trigonometric expressions and an explicit location parameter, handles zero safely, and proves continuity and the translation obstruction. No theorem identifies this expression with `LevyTriplet.exponent` for the classified stable jump measure. Source correction is necessary but does not close the missing analytic proof. |
| Bounded-support ID law (Exercise 16.1.1) | Implemented | `BoundedSupport.lean` proves that an infinitely divisible real law carried by a bounded interval is a point mass. |
| Null-array ID limit theorems 16.12--16.13 | DEFERRED | Klenke's cited external proof has not been recovered and audited. |
| Domains of attraction 16.26--16.30 | DEFERRED | Entire block belongs to `StableLimitTheory`; no orphan predicate was added. |

## LSII blocker and deferred ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| LS-B01 | RESOLVED | Canonical Mathlib measure convolution was reused and the probability-law closure/powers were added. |
| LS-B02 | RESOLVED | Existing stationary- and independent-increment predicates were reused. |
| LS-B03 | RESOLVED | Correct `NNReal` projective construction and finite-family increment independence are implemented. |
| LS-B04 | RESOLVED | No exact active/local compound-Poisson law existed; the zero-safe finite-intensity foundation, intensity-addition law, and infinite divisibility are implemented. |
| LS-B05 | RESOLVED | Real Levy--Khintchine existence, converse extraction, and uniqueness compile internally. |
| LS-B06 | RESOLVED | Complex Taylor and Levy-integrand domination are implemented. |
| LS-B07 | RESOLVED | Affine-triplet scaling, index existence in `(0,2]`, homogeneous jump tails/density, Gaussian endpoint, and nontrivial jump branch are implemented. |
| LS-B08 | STILL-BLOCKED analytic proof | The source correction and zero-safe expression are implemented. The corrected oscillatory Gamma/trigonometric integral identity, including location/truncation normalization, remains unproved. The previous RESOLVED wording incorrectly treated identifying the source defect as implementing the corrected theorem. |
| LS-D01--LS-D05 | DEFERRED | Cadlag Levy realization, PPP/Levy--Ito, Skorokhod weak convergence, Levy stochastic integration, and multidimensional/LCA Levy--Khintchine retain their later owners. |
| LS-D06 | DEFERRED | External null-array ID theorem proof not available. |
| LS-D07 | DEFERRED | Stable domains of attraction move together to `StableLimitTheory`. |

# Brownian Motion and Path Regularity Foundations

This is the final disposition of `StochLean_BrownianMotion_PathRegularity_Design_v0.2.pdf`.
The package is **complete** at the document boundary. It reuses Mathlib's canonical Brownian
predicates and owns the missing construction, regularity, stopping, path-functional, Schauder, and
deterministic-Wiener layers.

## Canonical reuse and implemented bridges

| Design topic | Disposition | Canonical implementation or decision |
| --- | --- | --- |
| Pre-Brownian/Brownian predicates | Reused | Mathlib `IsPreBrownianReal` and `IsBrownianReal`; no StochLean Brownian structure was added. |
| Gaussian laws, covariance, independent increments | Reused | Active Mathlib Brownian and Gaussian modules, including `eval_zero_ae_eq_zero`, increment laws, covariance, shift independence, negation, scaling, shift, and upstream inversion. |
| Brownian SII and marginal ID | Implemented bridge | `Brownian/Transformations.lean` proves SII, the Gaussian increment-law convolution semigroup, and infinite divisibility. |
| Time inversion natural-domain bridge | Implemented | Explicit piecewise value at zero, positive-time formula, equality to upstream, and pre-Brownian preservation. |
| Kolmogorov--Chentsov conclusion | Implemented | The audited Apache-2.0 proof architecture was internalized under `StochLean/Internal/Brownian`; duplicate active-pin declarations were removed and the public facade is `Process/Regularity/KolmogorovChentsov.lean`. |
| Continuous/Holder Brownian representative | Implemented | `Brownian/Construction.lean` builds the canonical coordinate law through the existing projective-limit facade and regularizes it; `PathProperties.lean` proves one common-event local Holder statement for every exponent below one half. |
| Gaussian covariance characterization | Reused and bridged | Mathlib's centered-Gaussian covariance characterization is reused, with the full Brownian iff statement in `Characterization.lean`, including continuous paths. |
| Brownian bridge | Implemented | The bridge has its Gaussian, endpoint, covariance, marginal, conditional endpoint, and deterministic-Wiener representations, with the corrected variance `t*(1-t)`. |
| Blumenthal zero--one law | Implemented | `Blumenthal.lean` proves probability triviality for the canonical continuous representative's germ sigma-field. |
| Strong Markov property | Implemented | `StrongMarkov.lean` proves deterministic-time and finite-stopping-time conditional identities for bounded continuous finite future-cylinder functionals, using genuine upper dyadic stopping-time approximation. |
| Reflection principle | Implemented | `Reflection.lean` contains the dyadic first-passage construction and strict- and closed-barrier forms, with Gaussian atomlessness handling the boundary. |
| Levy arcsine law | Implemented | `Arcsine.lean` defines and proves measurability of the last-zero functional and establishes the full CDF, including both deterministic endpoints and transfer from the canonical representative. |
| Paley--Wiener--Zygmund path theorem | Implemented | `PaleyWienerZygmund*.lean` gives pointwise failure of supercritical Holder control and almost-sure nowhere finite differentiation. |
| Haar/Schauder Brownian construction | Implemented | `Schauder.lean` proves almost-sure uniform convergence of the special dyadic Schauder approximants, kept distinct from arbitrary-Hilbert-basis `L2` convergence. |
| Deterministic Wiener integral | Implemented | `DeterministicWienerIntegral.lean` constructs a basis-independent linear isometry on the `L2` quotient and proves indicator, covariance, Gaussian-law, step-function, and arbitrary Hilbert expansion theorems. |

## Exact external audit and blocker ledger

| ID | Status | Owner, reason, unlock condition, and downstream impact |
| --- | --- | --- |
| BM-X01 | RESOLVED | The useful Apache-2.0 proof closure from `RemyDegenne/brownian-motion` at `314f04a34ff75e18fd383917ae7fe7d77beb1b6f` was audited, internalized, renamed under `StochLean.Internal.Brownian`, stripped of active-pin duplicates, and rebuilt without importing or linking the external package. Provenance is recorded in `StochLean/Internal/Brownian/README.md`. |
| BM-B01 | RESOLVED | Active Mathlib v4.33 supplies canonical `IsPreBrownianReal`/`IsBrownianReal` and the basic transformation layer. |
| BM-B02 | RESOLVED | The full KC conclusion is internal and exported through the public regularity facade. |
| BM-B03 | RESOLVED | The covering/chaining API and simultaneous subcritical Holder monotonicity result compile against the active pin. |
| BM-B04 | RESOLVED | Dyadic stopping-time approximation, finite-cylinder strong Markov, and canonical-germ Blumenthal zero--one results are implemented. |
| BM-B05 | RESOLVED | Measurable running supremum and last-zero APIs support the strict/closed reflection principles and full arcsine CDF. |
| BM-B06 | RESOLVED | The `L2` quotient, linear isometry, ONB expansion, Schauder-specific uniform convergence, bridge kernel, and conditional bridge layers are separated and implemented. |
| BM-B07 | RESOLVED | Sections 21.1--21.3 and 21.5 source boundary is frozen by the handoff. |
| BM-D01--BM-D07 | DEFERRED | Doob/general SII regularization, Feller realization, functional weak convergence/Donsker, continuous quadratic variation, LIL/Skorohod, and Ito integration retain the owners specified by the design. |

The Brownian semantic regression checks the canonical continuous realization, common-event Holder
regularity, pointwise PWZ and nowhere differentiability, covariance characterization, bridge and
conditional bridge laws, Schauder uniform convergence, measurable path functionals, reflection,
full arcsine CDF, finite-stopping-time strong Markov identity, Blumenthal zero--one law, and the
deterministic Wiener linear isometry/covariance API.

# Cross-milestone reproducibility status

## Semimartingale implementation and current gaps

SP-03 `StochLean_Semimartingale_Core_Design_v0.1.pdf` supersedes the old CM-QV
contract. It is **IN PROGRESS**, not complete. Exact implemented foundations,
remaining Klenke/Protter blocks, source corrections, regressions and blocker
statuses are in [SEMIMARTINGALE_STATUS.md](docs/SEMIMARTINGALE_STATUS.md).
The working inventory of all 11 design PDFs is [DESIGN_GAPS.md](docs/DESIGN_GAPS.md).

Continuation source rows (2026-09-07):

| Source | Implemented statement / remaining boundary | Owner |
| --- | --- | --- |
| Klenke 21.59 | Positive exponent comparison; a finite lower-exponent limit, or merely bounded lower-exponent sums, forces zero higher variation for continuous paths with vanishing mesh. | `Analysis/PathVariation/Exponent.lean` |
| Klenke 21.60 | One-variation increases under endpoint refinement and tends to Mathlib total variation, including infinity. Finite square-sum refinement inequalities have counterexamples; a full-sequence partition-dependent/nonexistent-QV example remains open. | `Analysis/PathVariation/TotalVariation.lean`, `Semimartingale/SemanticRegression.lean` |
| Klenke 21.61(i) | Source polarization from square variations of `f+g` and `f-g`; it does not assume separate QV limits for `f` and `g`. | `Analysis/PathVariation/Algebra.lean` |
| Klenke 21.61(ii) | Limiting covariation has total variation at most `sqrt(a)*sqrt(b)`, both for fixed-enclosing-horizon stopped-path sums and for the exact infinite-partition restriction convention. | `Analysis/PathVariation/{CovariationVariation,Restriction,RestrictionConvergence}.lean` |
| Klenke 21.71 proof repair | Completed square sums are monotone; partial-cell error vanishes uniformly. Exact restriction transport and dense-to-all-times convergence are proved and used for the native Brownian theorem. The general continuous-local-martingale bracket specialization remains open. | `Analysis/PathVariation/{CompletedSums,PartialSums,DenseConvergence,RestrictionConvergence}.lean` |
| Klenke 21.69(i), Protter I.6 Example 1 | Actual deterministic unmasked UI localizer for any martingale; cadlag/continuous martingale-to-local bridges. | `Process/LocalMartingale/DeterministicStopping.lean` |
| Protter I.51 | Compact integrable-envelope martingale criterion; global integrable-envelope UI criterion. Bounds use one event per horizon before random stopped evaluation. | `Process/LocalMartingale/Bounded.lean` |
| Protter I.3 Brownian martingale examples | Brownian and `B_t^2-t` martingales in the natural filtration from independent increments and Gaussian moments; finite-time L2 and CLM bridges. | `Brownian/Martingale.lean` |
| Protter Brownian source-filtration transfer | Actual laws and paths on `P.completion`; adaptation and independent future increments in the genuine usual augmentation; Brownian and square-minus-time martingales, CLM/semimartingale status and the canonical time bracket. A natural-filtration entry point derives past independence. No arbitrary information enlargement is allowed. | `Brownian/UsualAugmentation.lean`, `Process/Filtration/IndependentIncrementsAugmentation.lean`, `Probability/Independence/Completion.lean` |
| Protter I.17 | Bounded martingale sampling and minimum formulas; general submartingale/supermartingale conditional inequalities from decreasing dyadic upper approximations and Vitali. Usual-condition interfaces also allow AE ordering and AE deterministic bounds. | `Martingale/OptionalSampling/{ContinuousTime,ContinuousStopping,ContinuousUsual,OneSidedUpperApprox,ContinuousOneSided,ContinuousOneSidedUsual}.lean` |
| Protter I.13, closed/UI equivalence | An actual integrable closing variable is constructed from integer-time convergence, then closes every finite real-time coordinate by the tower property. The full half-line path-limit assertion is not claimed. | `Martingale/Convergence/ContinuousClosure.lean` |
| Protter I.18 and its corollary | Arbitrary stopping preserves a UI right-continuous martingale under usual conditions; an arbitrary stopped right-continuous martingale is still a martingale. All stopped-process coordinates are evaluated at finite `min(t,T)`. | `Martingale/OptionalSampling/{ContinuousUniformIntegrable,ContinuousUsual}.lean`, `Process/Path/Stopping.lean` |
| Protter I.48(a--e), vector-space corollary | Actual common minimum fundamental sequences, linear/stopping/masked stability, AE-ordered smaller reducing times, maximum reducing times, and locally-local idempotence with an explicit pointwise-monotone tail-infimum witness. | `Process/LocalMartingale/{Stability,Reducing,Localization}.lean` |
| Protter I.49--I.50 | On the source cadlag domain, localization by finite-time square-integrable or merely true martingales implies the canonical Protter local-martingale predicate. Adaptedness follows from actual localizations and usual completeness. | `Process/LocalMartingale/Localization.lean` |
| Protter I.16, AE-finite terminal case | Unbounded UI optional sampling via L1 truncation and conditional-expectation contraction; AE order is sufficient. The possibly-infinite terminal-value case is still open. | `Martingale/OptionalSampling/ContinuousUnbounded.lean` |
| Klenke 21.67, corrected bounded localization | Continuous adapted closed-level hitting and an everywhere-continuous indistinguishable version give actual bounded stopping sequences. Continuous local martingales with bounded initial value have bounded unmasked UI/L2 localizations; arbitrary initial values are handled by centering. True-martingale witnesses up to any random lifetime are refined without changing that lifetime, including AE-monotone source witnesses. | `Process/Stopping/{ContinuousHitting,BoundedLocalization,Usual}.lean`, `Process/Measurability/ContinuousVersion.lean`, `Process/LocalMartingale/{BoundedLocalization,LocalizationUpTo}.lean` |
| Continuous local martingales, local L2 construction | Intersect the centered level sequence with the initial-value 0/infinity sequence. The actual masked fundamental sequence consists of bounded UI, finite-time L2 martingales, even when the initial value is not integrable. The converse uses I.49 on the continuous path domain. | `Process/LocalMartingale/ContinuousSquareLocalization.lean` |
| Protter I.17 / II.1--II.3 integration prerequisites | Bounded stopping values satisfy Lp contraction for p >= 1; arbitrary stopping preserves finite-time L2. UI permits ordered AE-finite, unbounded endpoint sampling. The original endpoint sigma-field gives the conditional expectation of the deterministic terminal value for a stopped integrator. Empty-interval coefficient normalization preserves the process and integral. | `Martingale/OptionalSampling/{ContinuousLp,ContinuousReindex,ContinuousTerminalLp}.lean`, `Process/Partition/Sampling.lean`, `Process/Semimartingale/SimplePredictable/Normalization.lean` |
| Protter II.8 and Corollaries 1--2 (printed p.55, PDF p.66) | The source elementary integral is exactly the existing discrete predictable transform plus its initial term. Initial/future orthogonality and terminal conditional contraction give `E[(H dot X^T)^2] <= C^2 E[X_T^2]`. Markov's inequality proves the good-integrator property. Finite-time L2, locally L2 cadlag, and continuous local martingales are ordinary semimartingales; the last case has no unmasked initial-integrability premise. | `Martingale/DiscreteIntegral/InitialL2.lean`, `Moments/L2.lean`, `Process/Semimartingale/SimplePredictable/{Sampling,L2}.lean`, `Process/Semimartingale/{L2Martingale,LocalL2Martingale}.lean` |
| Protter II.2 (printed p.53, PDF p.64) | Total/ordinary semimartingales survive absolutely continuous changes to a finite target measure. Source usualness gives measurable elementary integrals; target usualness is not asserted or assumed. Neither equivalence nor a bounded density is needed. | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureAbsoluteContinuity.lean`, `Process/Semimartingale/AbsoluteContinuity.lean` |
| Protter II.3 (printed p.53, PDF p.64) | Countable probability mixtures, including zero weights, preserve semimartingales. The proof gives the stronger finite-total-mass sum statement via componentwise convergence in measure and dominated convergence on the counting measure, without uniform componentwise rates. | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasureMixture.lean`, `Process/Semimartingale/Mixture.lean` |
| Protter II.4, Stricker (printed p.53, PDF p.64) | Stopping sigma-fields and source representations embed into a larger filtration without changing elementary integrals. A semimartingale remains one for any smaller filtration to which it is adapted. | `Process/Stopping/Filtration.lean`, `Process/Semimartingale/Stricker.lean` |
| Protter II.7 (printed p.55, PDF p.66) | Source elementary integrals are measurable and bounded pathwise by the process bound times initial absolute value plus total variation. Globally finite variation gives a total semimartingale; locally finite variation gives an ordinary one. Random variation need not be measurable or integrable for this pathwise convergence argument. Agreement with the separately constructed pathwise Stieltjes integral remains open. | `Process/Path/FiniteVariation.lean`, `Process/Semimartingale/SimplePredictable/{Measurability,VariationBound}.lean`, `Process/Semimartingale/FiniteVariation.lean` |
| Protter I.7 foundation (printed pp.39--40, PDF pp.51--52) | Actual dyadic sums prove adapted extended total variation for right-continuous paths. Usual completeness handles AE cadlag paths. Canonical increasing Jordan components and random locally finite Stieltjes measures are constructed, with F_T-measurable finite-horizon restrictions. Their pathwise integral has the source initial term, linearity, variation bound, dominated convergence, measurability and progressive-integrand adaptedness. Integral path regularity, elementary agreement, C1 calculus and I.52 density remain open. | `Analysis/PathVariation/{Stieltjes,StieltjesIntegral,TotalVariation}.lean`, `ForMathlib/{MeasurableStieltjesNNReal,MeasurableIntegralFiniteFibers}.lean`, `Process/FiniteVariation/{Variation,Jordan,Stieltjes,Integral}.lean` |
| Protter II.3 Poisson example (printed p.54, PDF p.65) | The existing natural-number-valued Poisson predicate supplies monotone real-valued cadlag paths and local finite variation. Adaptation to a chosen usual filtration then gives an ordinary semimartingale. | `Process/Poisson/Semimartingale.lean` |
| Protter II.9, easy direction (printed p.55, PDF p.66) | The source decomposable predicate retains a separate initial value, a locally L2 local martingale and an adapted cadlag FV component. Their sum is a good-integrator semimartingale. No predictability, uniqueness, converse or fundamental local-martingale decomposition is claimed. | `Process/Semimartingale/Decomposable.lean` |
| Protter II.6 and localization corollary (printed p.54, PDF p.65) | Agreement outside sets of vanishing probability preserves good integrators, also with common-event AE agreement. The source `T-` process has the explicit zero-time and infinite-lifetime conventions. Equality or indistinguishability after `T_n-` stopping implies ordinary semimartingale patching. Measurable AE-divergent lifetimes suffice; stopping-time, positivity and monotonicity assumptions are unnecessary. Masked pre-localization and locally-semimartingale forms are proved on the adapted cadlag domain. | `Process/Stopping/{LocalizingTail,Before}.lean`, `Process/Semimartingale/{Localization,StoppingBefore}.lean` |
| Protter source left limits and jumps | Mathlib strict-left limits are reused at positive times, with `X_(0-)=0`. A cadlag path has a caglad left-limit path; under usual conditions adapted cadlag processes have adapted left-limit and jump processes. Continuous paths have zero jumps at positive times, but their source time-zero jump is `X_0`. | `ForMathlib/Topology/Order/LeftLimitRight.lean`, `Process/Path/LeftLimit.lean`, `Process/Measurability/LeftLimit.lean` |
| Protter III.1 predictable definition (printed p.102, PDF p.113) | Strict-past grids prove predictability of everywhere-left-continuous adapted real processes. The sigma-field generated by adapted everywhere-caglad real processes equals Mathlib's rectangle-generated predictable sigma-field. Merely AE regularity gives an indistinguishable predictable version; arbitrary exceptional paths are not asserted predictable. | `Process/Measurability/{PredictableGrid,Predictable,PredictableGenerators}.lean`, `Process/Path/Step.lean` |
| Protter II.1 source simple-process regularity (printed p.51, PDF p.62) | Original F_T-measurable coefficients become measurable strictly after the left endpoint. Every source simple predictable process is adapted, has everywhere-caglad paths and is predictable in the canonical Mathlib sense, without coefficient bounds or distinct-endpoint assumptions. Common refinement and algebra are now implemented below; UCP density remains separate. | `Process/Stopping/Coefficient.lean`, `Process/Semimartingale/SimplePredictable/Regularity.lean` |
| Klenke 21.64--21.65, Exercise 21.10.1 / Protter I.28 | Deterministic Brownian reflection and joint-law symmetry construct the actual reverse martingale of terminal-square conditional expectations. Arbitrary admissible nested sequences give strong QV equal to time on one all-times event. A proved normalized-sum Brownian law and polarization give independent cross-QV zero on one all-times event. Events may depend on the prescribed partition sequence. | `Analysis/PathVariation/Reflection.lean`, `Conditional/Symmetry.lean`, `Brownian/{DeterministicReflection,ReflectionLaw,QuadraticVariationConditional,QuadraticVariationStrong,QuadraticVariationPaths,IndependentCombination,CrossQuadraticVariation}.lean` |
| Protter I.29 | Explicit uniform/dyadic admissible endpoint sets and strong QV imply infinite variation on every nondegenerate compact interval, on one event. Countably many Brownian shifts cover arbitrary subintervals. | `Analysis/PathVariation/UniformPartition.lean`, `Brownian/InfiniteVariation.lean` |

Further I.7 continuation (2026-09-08): local pathwise integrability against total
variation now gives actual cadlag and locally BV integral paths, hence a
semimartingale for progressive integrands under usual conditions. General measure
primitives have right-continuous closed-endpoint integrals and open-endpoint left
limits, with jump equal to the atom mass times the integrand. These results do not
assume atomless measures or expected-variation integrability. Owners:
`ForMathlib/{VariationAlgebra,StieltjesPrimitiveRegularity}.lean`,
`Analysis/PathVariation/StieltjesIntegralRegularity.lean`, and
`Process/FiniteVariation/IntegralRegularity.lean`. Source elementary agreement,
change of variables and I.52 density remain open.

The subsequent finite-step agreement increment closes the elementary-agreement
gap above: `Analysis/PathVariation/StieltjesIntegralSimple.lean` and
`Process/FiniteVariation/SimpleAgreement.lean` prove local pathwise integrability
and equality with the existing source finite sum, at every finite horizon and
at the representation's random terminal endpoint. Coefficients may be any finite
real random variables and endpoints may repeat. Future intervals contribute zero.

The source adapted-caglad FV-integrand domain is now connected without an extra
integrability premise. `Process/Path/CagladBounded.lean` derives compact bounds
from left continuity and right limits; `Process/FiniteVariation/CagladIntegral.lean`
proves local Stieltjes integrability and progressive/semimartingale FV integrals.
These pathwise bounds need not be uniform over samples or integrable in probability.

The FV jump increment proves `Delta(H . X) = H Delta X` from the actual Jordan
measure atoms at positive times and the separate initial term at zero. It includes
the adapted-caglad source class and common-event, all-times AE statements. Owners:
`Analysis/PathVariation/StieltjesIntegralJump.lean` and
`Process/FiniteVariation/Jump.lean`. This is not the general Chapter II integral jump theorem.

The FV instances of Protter II.12--II.13 (printed p.60, PDF p.71) are now proved.
`Analysis/PathVariation/StieltjesIntegralStopping.lean` identifies all three stopped
variation measures with their closed-horizon restrictions. `Process/Stopping/Integrand.lean`
keeps the adapted-caglad/predictable source domain after cutoff. The two exact integral
stopping identities are in `Process/FiniteVariation/Stopping.lean`, with no finite-time
restriction on the random lifetime. The general stochastic-integral versions remain open.

The FV continuity increment supplies path-locality/indistinguishability and
compact-uniform convergence with bound `|X_0| + Var(X)`. The source adapted-caglad
integral is UCP-continuous: actual common-event subsequences and measurable output
deviations prove probability convergence. Given source simple approximations,
their elementary integrals converge to this FV integral (the FV side of II.17).
This does not supply the simple-density construction or the general integral.
Owners: `Analysis/PathVariation/StieltjesIntegralContinuity.lean`,
`Process/FiniteVariation/{Continuity,UCP}.lean`, and `Process/UCP/UniformConvergence.lean`.
The latter also proves indistinguishable uniqueness of right-continuous UCP limits.

Protter I.54 and its substitution corollary (printed pp.41--42, PDF pp.53--54)
are now proved for continuous FV paths/processes. Compact-uniform left Riemann
approximation and a first-order remainder estimate identify the actual Stieltjes
integral. C1 composition preserves local BV; the process versions use one common
event and include a semimartingale corollary. Source Chapter II initial terms are
not discarded: the full self-integral is `(X_t^2 + X_0^2)/2`. Owners:
`Analysis/PathVariation/{LeftStepApproximation,StieltjesIntegralRiemann,C1ChangeOfVariables}.lean`
and `Process/FiniteVariation/ChangeOfVariables.lean`. The later right-continuous
FV extension is proved in the II.31 implementation. Klenke 21.62's distinct C1
quadratic-variation identity is now proved in
`Analysis/PathVariation/{CumulativeIntegralLimit,QuadraticVariationStieltjes,QuadraticVariationComposition}.lean`.
The actual weighted square sums converge to the existing Stieltjes integral;
the continuous increasing zero-starting limit and C1 closure are proved from
all-time square-sum convergence. Only local mesh convergence is needed, without
an assumed weighted identity, finite variation of the input, or a C2 hypothesis.
Full-sequence partition dependence is now proved in
`Analysis/PathVariation/{MidpointRefinement,CommonRefinement,SmallVariationPartitions,FiniteExtension}.lean`
and `Brownian/PartitionDependence.lean`: IVT value-midpoint refinements halve the
square sum and retain endpoints; actual nested vanishing-mesh infinite sequences
give zero, while a continuous path extracted from the internal Brownian law has
dyadic QV one at the same horizon. The quantifier-swapped universal Brownian
event is disproved. The separate nested-sequence nonconvergence example is also
proved in `Analysis/PathVariation/{CellInsertion,FiniteInsertionLimit}.lean` and
`Brownian/QuadraticVariationNonconvergence.lean`. A fixed finite insertion has
vanishing product error on a continuous path. High dyadic/common-refinement
steps and low value-refinement steps therefore retain all old endpoints while
keeping even square sums below `1/4` and odd square sums above `3/4`. The global
sequence is genuinely nested and admissible, and has no real QV limit at horizon
one. This closes the remaining deterministic 21.56--21.63 construction gaps.

The subsequent tagged increment closes Protter I.53 (printed p.41, PDF p.53):
tags may be any point of each closed cell, and both partitions and tags may
depend on the sample. Their assumptions are intersected on one common event;
convergence is uniform over partial terminal times on the fixed horizon. The
terminal increment statement excludes the initial term exactly as in I.53.
Owners: `Analysis/PathVariation/{TaggedStepApproximation,StieltjesIntegralTagged}.lean`
and `Process/FiniteVariation/Riemann.lean`. Future tags are not asserted stopping
times and their step functions are not asserted adapted.

The source simple-predictable class (Protter II.1, printed p.51, PDF p.62) now has
actual common finite stopping-time refinements. Min/max splitting gives pathwise
endpoint inclusion; coefficients on the refined partition are measurable at its
left stopping endpoints. Repartitioning preserves every path and every elementary
integral, including independent initial values and repeated endpoints. Binary
Borel operations fixing `(0, 0)` preserve the class, yielding addition and
multiplication; scalar multiplication, negation, subtraction and elementary
bilinearity are available. No boundedness, usual-filtration or finite-measure
assumption is introduced. The refinement witness is nonminimal, not an efficient
sorting algorithm. Owners: `Process/Partition/Refinement.lean`,
`Process/Stopping/CoefficientAtStopping.lean` and
`Process/Semimartingale/SimplePredictable/{Refinement,Algebra,IntegratorAlgebra}.lean`.
The later II.10 construction below supplies density; UCP completeness and the general integral
remain open.

Source cutoff closure and the elementary stopping identity are now proved:
`I_X(H 1_[0,τ]) = I_(X^τ)(H)` for arbitrary integrators and arbitrary stopping
times, including infinity. Finite source endpoints are split at a capped stopping
time; pure interval-sum invariance supplies the integral identity path by path.
Consequently good integrators are stable under stopping. Under usual conditions
the same holds for total and ordinary semimartingales. A total semimartingale is
ordinary even without usual conditions, and stopping an ordinary semimartingale
at a deterministically bounded stopping time gives a total one. Owners:
`Process/Semimartingale/{SimplePredictable/Stopping,Stopping}.lean`.
These are elementary/source stability results, not the still-open general-integral
version of Protter II.12. No initial value is discarded and no integral at infinity
is evaluated.

The elementary source operator of Protter II.1 (printed p.52, PDF p.63) is now
bundled as `elementaryIntegralLinearMap`, with `simplePredictableSubmodule` having
exactly the original `IsSimplePredictable` carrier. Negation/subtraction laws are
proved for the representation-independent integral. Good-integrator zero-continuity
gives one epsilon/delta bound for differences of any two simple inputs, sends
uniformly Cauchy source sequences to Cauchy families in measure, and proves
convergence in measure at every simple limit. Owners:
`Process/Semimartingale/SimplePredictable/LinearMap.lean` and
`Process/Semimartingale/Continuity.lean`. The codomain of the algebraic linear map
is raw random variables; no unproved L0 measurability or general-integral limit
is built into its definition. These estimates use uniform convergence in `(t,ω)`,
not UCP convergence.

For the hitting-time prerequisites of Protter II.10--II.11 (printed pp.57--58,
PDF pp.68--69), Mathlib's existing `hittingAfter` now has open-target stopping
theorems for right-continuous adapted paths, countable dense detection, and a
usual-completeness version for one common exceptional path event. Finite hits lie
in the target's closure. Norm first exits have an upper bound strictly before
the hit and a lower bound at a finite hit; jumps may overshoot. Owners:
`Process/Stopping/{RightContinuousHitting,FirstExit}.lean`. These prerequisites
do not alone prove source density or UCP-input integral continuity.

**Source correction, Protter II.10:** direct rendering of printed p.57 confirms
that the final finite sum starts at `i = 1` despite `T_0 = 0`. For the constant-one
path all positive-index oscillation times are infinite, so all those capped
intervals are `(n,n]`; the printed approximant vanishes at every positive time.
The corrected construction must include the first interval, e.g. indices
`i = 0,...,n-1`. The constant no-hit and omitted-interval expressions are Lean
regressions; the corrected full construction is now proved below.

The source elementary process `J_X(H)` from printed p.58 (PDF p.69) is now the
existing representation-independent elementary integral against each deterministic
stop of `X`. Its finite-sum formula, time-zero value, terminal stabilization,
linearity, adaptedness under usual conditions and common-event cadlag regularity
are proved without coefficient bounds or integrability. Pathwise stopping holds
for arbitrary raw random times, including infinity; source integrand cutoff needs
a stopping time. It agrees with the existing pathwise FV integral, without a new
selector. Owners: `Process/Semimartingale/SimplePredictable/IntegralProcess*.lean`
and `Process/FiniteVariation/SimpleAgreement.lean`.

The first, uniform-input half of Protter II.11 is now proved: a strict compact
maximum event is bounded by a finite first-exit stopped-value event; the existing
terminal good-integrator estimate applies to the actual source cutoff. This gives
uniform-input maximal bounds for total and ordinary semimartingales under usual
conditions. The strict real-threshold event criterion is proved equivalent to the
canonical ENNReal-deviation UCP definition, including infinite thresholds. Thus
uniform convergence in `(t,ω)` to any source simple process gives UCP convergence
of its elementary integral process. Owners: `Process/Stopping/FirstExitMaximal.lean`,
`Process/UCP/DeviationEvents.lean`, `Process/Semimartingale/{Maximal,UniformUCP}.lean`.
The second half of II.11 is also proved. Left-continuous open-target detection
explicitly includes the initial time; its positive first-exit norm upper bound
gives an actual bounded source truncation, masked on `{tau > 0}`. The mask commutes
with elementary integration. Comparing on any larger input horizon `S > T`
controls exit events without falsely treating a boundary/right jump as an attained
open hit. This yields full S_UCP-to-D_UCP continuity at any simple limit and
UCP-Cauchy estimates, with arbitrary finite coefficients and initial values.
Owners: `Process/Stopping/LeftContinuousHitting.lean`,
`Process/Semimartingale/SimplePredictable/{InitialMask,FirstExitTruncation}.lean`
and `Process/Semimartingale/UCP.lean`. UCP completeness and the general integral
extension remain open; source density is supplied by the following construction.

Further II.10 prerequisites are now proved: the canonical Mathlib right-limit
process of a caglad input is cadlag, its positive-time left limits recover the
original input, and the independent time-zero value is retained in reconstruction.
Adaptedness follows from limits measurable in every later sigma-field and right
continuity of the filtration; usual completeness handles one common exceptional
path event. Strictly increasing samples of a cadlag path with uniformly positive
consecutive oscillations cannot accumulate at a finite time, including the
extended-time form with possible infinity. Owners: `ForMathlib/Topology/Order/RightLimitLeft.lean`,
`Process/Path/{RightLimit,Oscillation}.lean`, `Process/Measurability/RightLimit.lean`.
The actual recursive oscillation times are now constructed from `X - X^tau` using
the same hitting-time owner. Finite successive times are strictly increasing,
their sampled values are separated, and they tend to infinity on the common cadlag
event. Finite capped partitions include all cells starting at index zero. The
representation's coefficients sample the right-limit process at finite capped
left endpoints, and its initial coefficient is the original `H_0`.

**Protter II.10 is implemented with the source correction:** for a finite measure
and usual filtration, every adapted process with common-event caglad paths has an
actual sequence of source simple predictable processes converging UCP. The proof
uses the cell error estimate and selects finite cell counts from vanishing early-exit
probabilities as thresholds shrink. No global coefficient bound or density premise
is assumed. A regression proves that the actual corrected one-cell construction
reproduces the constant-one process on the full cap. Owners:
`Process/Stopping/Oscillation.lean`, `Process/Partition/TruncateSequence.lean`,
`Process/Semimartingale/SimplePredictable/{OscillationApproximation,Density}.lean`.
Protter II.4, printed p.59 (PDF p.70), UCP-completeness substrate is now proved.
Geometric consecutive-error control gives a common-event locally uniform Cauchy
subsequence. Real completeness constructs pointwise limits; locally uniform closure
preserves cadlag paths, and one initial-measurable null-set reset preserves adaptedness.
The original Cauchy sequence then converges in UCP. Owners:
`ForMathlib/Topology/{UniformCauchy,UniformLimit}.lean`,
`Process/Path/UniformLimit.lean`, `Process/UCP/{Cauchy,Complete}.lean`.
The actual construction retains nonzero constants up to indistinguishability.
The Chapter II stochastic-integral definition on printed p.59 (PDF p.70) is now
implemented by `Semimartingale/StochasticIntegral.lean` and
`StochasticIntegral/{Construction,Algebra,Continuity,InitialValue}.lean`.
Density and source continuity construct Cauchy elementary integrals; the actual
completion theorem provides a limit. Source linearity then proves convergence
for every simple UCP approximation. The selected integral is adapted and cadlag,
unique up to indistinguishability, proof-irrelevant, linear and UCP-continuous on
the full adapted/common-event-caglad domain. A simultaneous diagonal proves the
last continuity claim without assuming uniform rates across integrands. The
initial value is `H_0 X_0` AE, without integrability premises. Regressions use the
selected general integral on a closed unit interval and an isolated initial spike.
Protter II.17 (printed p.61, PDF p.72) is proved by source approximation and the
existing FV UCP-continuity theorem. An initial null-set reset first handles
common-event caglad integrands, then common-event finite-variation integrators.
The final theorem compares the general integral with the actual Stieltjes
integral of the original path, with the finite-variation and cadlag witnesses
constructed on one common full-measure event. General-integral invariance under
indistinguishable integrators is proved separately from source integral invariance.
Owners: `SimplePredictable/IntegralProcessCongr.lean` and
`StochasticIntegral/{IntegratorInvariance,FiniteVariation}.lean`.
The continuous-FV self-integral regression gives `(X_t^2 + X_0^2) / 2`.
Protter II.12 (printed p.60, PDF p.71) is proved for arbitrary possibly infinite
stopping times: stopping the general integral, stopping the integrator and cutting
off the integrand on the closed stochastic interval give indistinguishable
processes. The proof uses source identities, UCP contraction under stopping/cutoff,
and uniqueness; source initial values survive at a zero stopping time. The infinite
cutoff regression never evaluates the integrator at infinity. Owners:
`Process/Stopping/IntegrandAE.lean`, `Process/UCP/Stopping.lean`,
`Process/Semimartingale/StochasticIntegral/Stopping.lean`.
Protter II.13 (printed p.60, PDF p.71) is proved on one common full-measure event:
`Delta(H . X)_t = H_t Delta(X)_t` for all times, including zero. Actual strict-left
limits of each finite stopped summand first prove the source elementary identity.
Locally uniform convergence controls left-limit values, so two actual subsequences
transfer the identity to the general integral. No path regularity is incorrectly
ascribed to the jump process itself. Owners: `ForMathlib/Topology/UniformLimitValues.lean`,
`Process/Path/{LeftLimitUniform,LeftLimitStopping}.lean`,
`SimplePredictable/IntegralProcessJump.lean`, `StochasticIntegral/Jump.lean`.
Regressions cover the source interval's right endpoint and the original initial product.
Protter II.14 (printed pp.60--61, PDF pp.71--72) is proved for an absolutely
continuous finite target measure, with no equivalence or bounded-density premise.
The target semimartingale property is derived from the existing source example.
Actual measurable covers and a summable subsequence prove transfer of vanishing
event measures even for nonmeasurable events, so UCP transfers without extra
path assumptions. Source simple approximation and uniqueness identify the two
integrals under the target measure. Target usualness is explicit, not incorrectly
deduced from source completeness; a zero-target-measure regression records that
safeguard, and another regression transports the original initial product.
Owners: `ForMathlib/MeasureTheory/Measure/AbsolutelyContinuousConvergence.lean`,
`Process/UCP/AbsoluteContinuity.lean`, `StochasticIntegral/AbsoluteContinuity.lean`.
Protter II.15 and its corollary (printed p.61, PDF p.72) are proved for countable
probability mixtures, including zero weights. The canonical mixture integral agrees
with each positive-weight component integral. Mixture probability mass, usualness,
semimartingale status and caglad input paths are derived. The two-probability version
uses the actual two half-weights and constructs a common adapted, everywhere-cadlag
integral. A concrete Dirac-measure regression shows why a zero-weight component must
be excluded from the domination conclusion. Owners: `Measure/ProbabilityMixture.lean`,
`Process/Filtration/MeasureChange.lean`, `StochasticIntegral/Mixture.lean`.
Protter II.16 (same page) is proved by source approximation in the intersection of
the two filtrations. The intersection is proved usual and the integrand adapted to it;
its source simple approximants transport to both filtrations with identical elementary
integrals. UCP uniqueness proves indistinguishability without any filtration ordering
or an assumption on a generated union filtration. Owners: `Process/Filtration/Intersection.lean`,
`SimplePredictable/IntegralProcessFiltration.lean`, `StochasticIntegral/FiltrationInvariance.lean`.
The source remark about arbitrary predictable integrands remains outside this Chapter II
domain; no Chapter IV invariance claim is made.
Protter II.18 (printed pp.61--62, PDF pp.72--73) is proved for both whole-path
agreement and local finite-variation events. The latter follows directly from two
actual uniform subsequences and pathwise FV continuity, with finite variation required
only at the selected sample. For integrand locality, the corrected oscillation
approximants are proved to preserve every zero input path; density is strengthened
without changing the previous public density interface. Subtraction then yields
agreement on identical-integrand paths, and common simple approximants give identical-
integrator locality. No measurability at time zero, positive event probability or usual
conditions for a conditioned measure is assumed. Owners: `Process/Path/Subtraction.lean`,
`Process/FiniteVariation/PathwiseSimpleAgreement.lean`,
`SimplePredictable/{ZeroPathApproximation,PathwiseIntegral,Density}.lean`,
`StochasticIntegral/{Subtraction,Locality,FiniteVariationLocality}.lean`.
The path-agreement assertion of the II.18 corollary (printed p.62, PDF p.73) is
proved. Cutoff differences transfer integrand locality on `(S,T]`; stopped-integrator
differences transfer integrator locality. Right continuity recovers the integrator's
left-endpoint value from agreement strictly to its right. The integrand's value there
need not agree. Outputs are stopped processes even when `T = infinity`; there is no
unprovided infinite-time value. Owners: `Stopping/IntervalLocality.lean`,
`StochasticIntegral/{StoppedDifference,StoppingIntervalLocality}.lean`. Regressions
check different initial integrand values and an intentionally non-right-continuous
path showing why the integrator regularity cannot be omitted.
The FV assertion of the II.18 corollary is also proved. For a finite upper endpoint,
BV on `(S,T)` suffices. Mathlib's one-sided variation identity adds the actual
right-endpoint jump; right continuity adds the left endpoint without artificial
variation. Clamping and centering give BV of `X^T - X^S`, whose canonical Stieltjes
integral is the local interval integral. No global FV of `X` is assumed. The infinite
upper-end version uses open-interval BV on every finite subhorizon and never evaluates
`X_infinity`. Owners: `Path/FiniteVariationInterval.lean`,
`StochasticIntegral/StoppingIntervalFiniteVariation.lean`. Regressions show zero
open-interval variation can coexist with a unit right-endpoint jump, and admit the
linear time path on the entire half-line.
Protter II.19 and its FV remark (printed pp.62--63, PDF pp.73--74) are proved.
Actual source common partitions yield elementary associativity, including initial
products and empty cells. Fixed-simple-integrand continuity in the integrator,
caglad multiplication in UCP, and the existing general-integral continuity prove
semimartingale preservation from the good-integrator definition. The outer general
integral is selected only after that property is established; its associativity
then follows from approximation and indistinguishability uniqueness. Pathwise
Stieltjes agreement gives FV preservation on individual FV paths up to one null set.
Owners: `SimplePredictable/{IntegralProcessCell,Associativity,IntegratorContinuity}.lean`,
`Process/UCP/{LeftContinuousDeviation,Multiplication,UniformInput}.lean`,
`Process/Path/Multiplication.lean`, and
`StochasticIntegral/{SimpleAssociativity,SemimartingalePreservation,Associativity,FiniteVariationPreservation}.lean`.
The bounded-integrand step of Protter II.20 (printed p.63, PDF p.74) is proved.
Nonexpansive clipping supplies actual simple approximants with the original
bound, even when the input bound is only on a common AE path event. Bounded
simple integrands preserve martingales, using weighted random-stopping increments
and normalization of coefficients on empty cells. For finite-time L2 martingales,
the general bounded-integrand result follows from the sharp elementary L2 estimate,
the square-envelope uniform-integrability theorem and actual probability-limit
martingale closure. The initial value is not set to zero. Owners:
`Process/UCP/Nonexpansive.lean`, `SimplePredictable/{BoundedDensity,Martingale}.lean`,
`Martingale/OptionalSampling/ContinuousWeightedIncrement.lean`,
`Martingale/Convergence/InMeasure.lean`,
`ForMathlib/MeasureTheory/Function/UniformIntegrableL2.lean`, and
`StochasticIntegral/BoundedL2.lean`.
The general locally square-integrable case of II.20 is also proved. A common-null
reset gives an everywhere-caglad adapted version; open norm exits form an increasing
sequence tending to infinity. Closed cutoffs masked by `{tau > 0}` are bounded.
Initial masks commute with source/general integration in both variables. Combining
the integrator's L2 localizers with the integrand's exit sequence by their minimum
produces actual L2 localizations of the original integral, including its initial
product. Owners: `Measurability/{CagladVersion,InitialMask}.lean`,
`Stopping/{CagladLocalization,InitialMask}.lean`, `UCP/InitialMask.lean`,
`LocalMartingale/SquareStability.lean`, `Semimartingale/InitialMask.lean`,
`SimplePredictable/IntegratorInitialMask.lean`, and
`StochasticIntegral/{InitialMask,LocalL2}.lean` (process-relative paths).
General local-martingale preservation beyond locally-L2 remains open.
For II.21 (printed pp.64--65, PDF pp.75--76), the continuous-integrand case is
proved for random partitions tending to the identity on a common event. Sampled
processes reuse pathwise deterministic left steps and the existing source simple
integral; their increment-only sums subtract `Y_0 X_0`. Usual completeness gives
stopping-value measurability for AE left-continuous paths. Sampling is a compact
deviation contraction uniform over arbitrary random partitions; continuous
paths admit actual locally uniform approximation with varying horizons.
The resulting UCP limit equals both the general integral minus its initial
product and the integral of the source left-limit process. A cell-interior jump
regression explains why this integrand approximation is not asserted on cadlag
paths. Continuous-case owners:
`Analysis/PathVariation/LeftStepBounds.lean`,
`Process/Stopping/LeftContinuousSampling.lean`, `Process/Partition/LeftSampling.lean`,
`Process/UCP/{LeftSampling,ContinuousLeftSampling}.lean`, and
`StochasticIntegral/{InitialIncrement,ContinuousRiemann}.lean`.
The full cadlag/caglad II.21 theorem is now proved. Right limits preserve UCP on
caglad paths using a slightly larger horizon, and the right limit of a cadlag
process's source left limit recovers the original process even at zero.
Exact endpoint projection rewrites sampled interval steps: ordinary ceilings
for right-limit `Ico` steps, strictly upper ceilings for source `Ioc` steps, with
a separate first-cell term for the initial spike. Right continuity of the
integrator controls the displaced stopping endpoints uniformly in time.
Source good-integrator continuity is uniform over arbitrary sampling partitions;
a proved sequential-to-uniform outer-measure bound closes the double-limit argument.
The target is precisely `(Y_-) . X`, and no assumption `X_0 = 0` is added.
General-case owners (process-relative paths unless stated otherwise):
`UCP/{RightLimit,InitialIncrement,UniformApproximation}.lean`,
`Path/{LeftRightReconstruction,StepRightLimit,StoppingConvergence,LeftLimitNormalization}.lean`,
`Measurability/CagladLeftLimit.lean`,
`Partition/{LeftSamplingRegularity,LeftSamplingAlgebra}.lean`,
`Analysis/PathVariation/{LeftStepCeiling,StrictApproximation,LeftStepStrictCeiling}.lean`,
`SimplePredictable/{RightLimit,RiemannCeiling,RiemannConvergence,RiemannStrictCeiling,
RiemannSourceConvergence,RiemannUniformContinuity}.lean`, and
`StochasticIntegral/{CadlagRiemann,CagladInitialIncrement,CagladRiemann}.lean`.
Integrator bilinearity of the Chapter II extension is also proved: one common simple
approximation and elementary integrator algebra give addition, real scaling and
subtraction, up to indistinguishability. This is linearity for fixed integrators,
not a claim that arbitrary UCP-convergent semimartingales have convergent integrals.
Owners: `Semimartingale/Subtraction.lean`,
`SimplePredictable/IntegralProcessIntegratorAlgebra.lean`,
`StochasticIntegral/IntegratorAlgebra.lean`. Regressions retain both initial values
under addition and cancel the shared initial value under a stopped-integrator difference.

In particular, a definition of good-integrator semimartingales is not the BD
theorem, elementary integration is not the constructed Chapter II caglad
integral, and the now-proved native Brownian all-times QV theorem is not the general
semimartingale bracket or its random-partition UCP theorem.
The general raw square bracket has now been constructed separately from the
canonical Chapter II integral, as required by the design, not by a second
Brownian or continuous-martingale construction. Protter II.22 (printed pp.66--67,
PDF pp.77--78): its adaptedness, cadlag paths, initial square, jump-square
identity, UCP square-sum approximation and increasing paths are proved.
Partial-cell square sums are not monotone. The proof instead evaluates them
at upper partition endpoints, where they are monotone completed-cell sums,
and uses locally uniform UCP subsequences and right continuity to pass to
the limit on one all-times event. Local FV and the semimartingale property
follow. Exact stopping of the square sums proves `[X^T,X^T] = [X,X]^T` for
zero, finite or infinite stopping times. The mixed identities in II.22(iii)
are now proved as well, through the polarized mixed owner described below.
Owners: `Process/Semimartingale/QuadraticVariation.lean` and
`QuadraticVariation/{Riemann,Increasing,Stopping}.lean`, supported by
`Process/Path/{LeftLimitOperations,UniformRightEvaluation}.lean`,
`Process/UCP/ExhaustingStopping.lean`,
`Process/Partition/{SquareSums,SquareSumsStopping}.lean`, and
`Analysis/PathVariation/CeilingSquareSums.lean`.
Protter II.22--II.23 (printed pp.66--68, PDF pp.77--79) now have the raw mixed
covariation owner, initial product, cadlag/FV paths, bilinearity, jump product,
random-partition mixed-sum UCP convergence, integration by parts and the
semimartingale algebra corollaries. Exact simultaneous stopping of finite sums
gives simultaneous bracket stopping. The common-event interval bound in the
proof of II.25 makes mixed brackets constant where one square bracket is
constant; this proves stopping in either single argument, including zero and
infinity, without an invalid finite-cell identity.
Owners: `Process/Semimartingale/QuadraticCovariation.lean` and
`QuadraticCovariation/{Riemann,Algebra,Jump,Stopping,IntegrationByParts,IncrementBound,OneSidedStopping}.lean`,
`QuadraticVariation/Algebra.lean`, `Process/Path/LeftLimitAddition.lean`, and
`Process/Partition/{CrossSums,CrossSumsStopping,CrossSumsProduct}.lean`.
II.24 and the weighted II.25 inequality are now proved. The interval estimate
is first upgraded to a total-variation bound, then to quadratic domination on
all measurable sets. Radon--Nikodym density order, a countable rational-scalar
argument and Holder's inequality give the weighted theorem for sigma-finite
measures, arbitrary measurable extended nonnegative weights and possibly
infinite energies. The variation measure is absolutely continuous with respect
to both increasing component measures. Actual Stieltjes realizations of the
canonical square brackets provide one full-measure event for every pair of
measurable weights. Separate initial-atom interfaces retain the initial absolute
product and both initial squares; the increment measures themselves still have
zero mass at time zero. No arbitrary-process or competing-bracket definition is used.
The expectation/Lp corollary on printed p.70 is now proved. Actual adapted
Stieltjes realizations are obtained by initial null-event resets, with all-times
identification with the unique raw brackets. Simple-function approximation and
finite-measure exhaustion prove measurability of their weighted lower integrals;
random masses need not be uniformly bounded. The outer Holder inequality covers
finite conjugate exponents and both L1/L-infinity endpoints. The initial atoms
are retained, and the resulting energies and expectations are independent of
the null-event realization. Weights need only be jointly measurable.
Expectation owners: `ForMathlib/MeasureTheory/{LocallyFiniteKernelIntegral,MeasurableStieltjesLIntegral,ExpectedCauchySchwarz}.lean`,
`Process/FiniteVariation/StieltjesRealization.lean`, and
`Process/Semimartingale/QuadraticCovariation/{StieltjesRealization,WeightedEnergy,KunitaWatanabeExpectation}.lean`.
The continuous-part definition following II.25 (printed p.70) now has its
deterministic increasing-path foundation: countable point-atomic restriction,
point-diffuse restriction, exact Stieltjes realization of dominated measures,
continuity of the diffuse cumulative function and the actual summable series
over all jumps in `(0,t]`. The original initial value is separate. The raw square
bracket's stochastic continuous component is now constructed from this same
owner. It is adapted by joint singleton-mass measurability and finite-time
restriction, everywhere continuous and increasing, zero-starting and an FV
semimartingale. The common-event decomposition uses the actual squared jumps
of the original process and proves their summability. Version invariance and
normalization for continuous processes are proved. Mixed continuous covariation
is now polarized from those same continuous components: adaptedness, continuous
FV paths, zero initial value, symmetry, diagonal identity, version invariance
and bilinearity are proved. Square-jump summability gives absolute summability
of mixed jumps, and polarization of their actual convergent series gives the
raw mixed decomposition with the initial product separate. Continuous square and
mixed brackets commute with simultaneous or one-sided stopping. The deterministic
proof identifies stopped Stieltjes measures with closed-endpoint restriction and
commutes point-diffuse restriction; the one-sided mixed proof uses the exact
closed-endpoint jump cutoff and the already-proved raw stopping identity.
Zero and infinite stopping are included without evaluating a process at infinity.
Stopping owners: `Analysis/PathVariation/{StieltjesStopping,StoppedJumpSum}.lean`,
`Process/Path/{JumpStopping,JumpSumStopping}.lean`,
`Process/Semimartingale/QuadraticVariation/ContinuousPartStopping.lean` and
`Process/Semimartingale/QuadraticCovariation/{ContinuousPartStopping,ContinuousPartOneSidedStopping}.lean`.
Owners: `ForMathlib/MeasureTheory/PointAtomicDecomposition.lean` and
`Analysis/PathVariation/Stieltjes{Submeasure,ContinuousPart,JumpSum}.lean`.
Random owners: `ForMathlib/MeasureTheory/{MeasurablePointDiffusePart,PointDiffuseRestriction,MeasurableStieltjesContinuousPart}.lean`,
`Process/FiniteVariation/ContinuousPart.lean`, and
`Process/Semimartingale/QuadraticVariation/{ContinuousPart,ContinuousPartAlgebra}.lean`.
Mixed owners: `ForMathlib/Analysis/SummableSquarePolarization.lean` and
`Process/Semimartingale/QuadraticCovariation/{ContinuousPart,ContinuousPartAlgebra}.lean`.
Owners: `Analysis/PathVariation/Stieltjes{CovariationBound,CovariationDomination,KunitaWatanabe,KunitaWatanabeInitial}.lean`,
`ForMathlib/MeasureTheory/{StieltjesOrder,RNDerivativeOrder,RNDerivativeQuadraticDomination,RNDerivativeCauchySchwarz,WeightedDensityCauchySchwarz,QuadraticMeasureCauchySchwarz,QuadraticMeasureAlgebra,WeightedMeasureInitialAtom}.lean`,
and `Process/Semimartingale/QuadraticCovariation/{KunitaWatanabe,KunitaWatanabeInitial}.lean`.
Source correction: II.25's proof, printed p.69/PDF p.80, says the discriminant
is nonnegative; it must be nonpositive for an everywhere-nonnegative quadratic.
The formal proof uses the correct sign and a countable rational-scalar event.
Protter II.30 (printed p.77, PDF p.88) is proved. Actual left-weighted mixed
increment sums equal the difference of three Riemann sums, including moving
partial cells and repeated endpoints. The full cadlag II.21 theorem gives their
UCP limits. Integrator linearity, associativity and the source left-limit product
identity identify the limit as the existing integral of `H_-` against `[X,Y]`.
Its initial value is zero, although the raw bracket retains `X_0 Y_0`.
No moment, boundedness, deterministic-partition or continuity assumption is added.
Owners: `Process/Partition/WeightedCrossSums.lean`,
`Process/Path/LeftLimitMultiplication.lean` and
`Process/Semimartingale/QuadraticCovariation/{IntegralAlgebra,WeightedRiemann}.lean`.
Protter II.29 (printed pp.75--76, PDF pp.86--87) is also proved on the entire
adapted-caglad Chapter II domain. Exact finite random-coefficient mixed-sum
algebra, stopped bracket limits and UCP multiplication prove the simple case.
Actual simple approximation and the product formula prove continuity along
integrals of a fixed semimartingale; this is not continuity for arbitrary varying
integrators. Symmetry and associativity give `[H.X,K.Y] = (HK).[X,Y]`, and the
same raw diagonal gives `[H.X,H.X] = (H^2).[X,X]`. Arbitrary initial values and
unbounded finite coefficients are retained, with no moment assumption.
Owners: `Process/Path/CadlagBounded.lean`, `Process/UCP/{LeftLimit,CadlagMultiplication}.lean`,
`Process/Partition/{CrossSumsLinear,CrossSumsRegularity}.lean`,
`Process/Semimartingale/SimplePredictable/{CrossSums,CrossSumsConvergence}.lean`,
`Process/Semimartingale/QuadraticCovariation/{IntegralContinuity,SimpleIntegral,Integral}.lean`
and `Process/Semimartingale/QuadraticVariation/Integral.lean`.
Outstanding items are not hidden assumptions of the presently exported proofs.
Protter II.27's main theorem (printed pp.71--72, PDF pp.82--83) is proved:
continuous local martingales have continuous raw brackets, their square minus
the raw bracket is a continuous local martingale, and a constant raw bracket
is equivalent to a constant process. Source initial squares are retained.
The argument first proves that a nonnegative zero-starting Protter local
martingale vanishes, using its actual masked true-martingale localizers.
Constant-integrator mixed sums and polarization give the exact centering
identity, including nonintegrable initial variables. The moment/terminal
corollaries remain open; the single-event all-intervals result is proved below.
Owners: `Process/Path/ContinuousOfJump.lean`,
`Process/LocalMartingale/NonnegativeZero.lean`,
`Process/Semimartingale/StochasticIntegral/ContinuousPaths.lean`,
`Process/Semimartingale/QuadraticCovariation/Constants.lean` and
`Process/Semimartingale/QuadraticVariation/{ContinuousLocalMartingale,ContinuousLocalZero,Centering,ContinuousLocalConstancy}.lean`.
Protter II.26's continuous-FV special case and II.27 Corollaries 1--2
(printed pp.71--73, PDF pp.82--84) are proved. Actual pathwise FV agreement
and the continuous self-integral identity give constant raw QV on continuous
FV paths, even if those paths do not form a full-measure event. Continuous
FV local martingales are therefore constant. Ordered stopped differences
have bracket `[X,X]^T - [X,X]^S`; AE order, zero and infinite endpoints are
allowed. Finite variation on the open stochastic interval or bracket constancy
on its finite closed points gives process constancy there. This is a result
for each selected stopping interval; Corollary 5's simultaneous strengthening
is recorded below. Integration by parts and II.20 give the locally-L2 product
residual. Identical jumps, initial values and FV residual differences give
uniqueness of the original raw bracket. General local-martingale preservation
from Chapter III is still separate.
Owners: `Process/Path/StoppingConstancy.lean`,
`Process/LocalMartingale/{Congr,ContinuousFiniteVariation,FiniteVariationInterval,FiniteVariationUniqueness}.lean`,
`Process/Semimartingale/QuadraticVariation/{ContinuousFiniteVariation,Subtraction,StoppedDifference,ContinuousLocalInterval}.lean`
and `Process/Semimartingale/QuadraticCovariation/{LocalMartingale,Characterization}.lean`.
Protter II.27 Corollary 5 (printed p.75, PDF p.86): **MAIN STATEMENT PROVED**.
On one event, a continuous local martingale and its canonical raw bracket
have exactly the same constancy intervals. The final interface covers every
order-connected set, including empty, singleton, open, half-open and unbounded
intervals. Increasing raw or continuous bracket endpoint equality also detects
constancy on each closed interval. Actual departure times of stopped increments
are stopping times; a countable dense set of starting times and continuity
upgrade the existing stopped-bracket equivalence to the common-event result.
No L2 moment theorem, unmasked initial integrability or unproved time change
is used. Arbitrary random endpoints can be evaluated on that event.
For the following discontinuous compensated-Poisson example, the actual
process `N_t-rate*t` is now proved to be a true martingale and hence a local
martingale, with explicit adaptedness and future-real-increment independence
from the chosen past. Exact first moments follow from the Poisson series and
the existing law; rate zero and reversed real increments are included. The
actual compensated process has cadlag/FV paths and is a semimartingale under
the chosen usual filtration, independently of its martingale property.
The canonical raw bracket is now proved to be `N`, both before and after
compensation. Exact second moments give nonnegative square-sum excess with
mean `rate^2 * sum gap^2`; arbitrary vanishing meshes converge in probability.
Uniqueness against the canonical UCP limit identifies the bracket on one event.
At unit rate, integer-valued counts minus time cannot be constant on any
nondegenerate interval. Discrete right continuity supplies a nontrivial flat
right neighborhood of the count, and hence its bracket, at every time on the
same event. The actual compensated process is not a continuous local martingale.
This closes the source counterexample, with no assumed martingale or bracket.
Further owners: `Process/Poisson/{Moments,SecondMoments,Martingale,QuadraticVariationSums,QuadraticVariation,Constancy}.lean`.
Owners: `Process/Stopping/{ClosedRegion,ConstancyExit}.lean` and
`Process/Semimartingale/QuadraticVariation/ContinuousConstancyIntervals.lean`.
Protter II.26 (printed p.71, PDF p.82) is now proved for general cadlag FV
paths, not only continuous ones. Left endpoint steps approach the strict-left
limit and right endpoint steps approach the actual value. Total-variation
dominated convergence and exact finite-cell algebra give the self-integral
identity with the jump integral retained. The two Jordan measures prove
countable jump support, absolute and squared-jump summability; integrable
countably supported functions yield actual singleton-mass series. Thus the
jump integral is the squared-jump series. Existing stochastic/pathwise FV
agreement identifies the sole raw QV, including its initial square. The
continuous component vanishes even on the path-local FV event. The source
quadratic-pure-jump predicate is version-invariant and stable under arbitrary
stopping. It does not exclude continuous drift.
Owners: `Analysis/PathVariation/{EndpointStepConvergence,StieltjesEndpointSums,StieltjesJumpSquareLimit,VariationJumpSeries,StieltjesSelfJump,StieltjesJumpIntegral}.lean`,
`ForMathlib/MeasureTheory/CountablySupportedIntegral.lean` and
`Process/Semimartingale/QuadraticVariation/{FiniteVariation,PureJump}.lean`.

Protter II.28 (printed p.75, PDF p.86) is proved. The existing continuous
square bracket is nonnegative for every integer linear combination. On the
countable intersection of those algebra identities, a vanishing diagonal
forces the mixed continuous component to vanish. This internal proof uses
positivity directly; the source instead deduces the same fact from KW
absolute continuity. The actual absolutely summable jump decomposition then
gives `[X,Y] = X_0 Y_0 + sum_(0,t] Delta X Delta Y` if either argument is
quadratic pure jump. FV and continuous-path corollaries retain the initial
product. Addition, subtraction, negation and scalar multiplication preserve
the same quadratic-pure-jump property. No initial moments or new owner appear.
Owners: `ForMathlib/Analysis/AffineNonnegative.lean`,
`Process/Semimartingale/QuadraticVariation/{ContinuousPartQuadraticAlgebra,PureJumpAlgebra}.lean`
and `Process/Semimartingale/QuadraticCovariation/PureJump.lean`.

Protter II.31 (printed p.78, PDF p.89) is proved for right-continuous FV
paths and processes. The source derives it from later Ito; this implementation
gives a direct proof using genuine two-endpoint Stieltjes sums. Mathlib's
`dslope` includes the derivative on the diagonal. The mean value theorem
gives its joint C1 continuity and compact bounds. Finite-cell telescoping and
variation-measure dominated convergence identify its increment integral.
Subtracting the left derivative leaves a function supported on countably
many jumps. The two Jordan component integrals equal their actual summable
singleton-mass series, yielding the absolute jump-remainder summability and
change-of-variables identity. Local Lipschitz bounds prove FV preservation.
Right continuity plus local BV supplies the left limits, so the source domain
is not narrowed. Path-local Chapter II agreement gives a common-event formula
without expected variation or initial moments; the raw integral of `f'(X_-)`
starts at `f'(0) X_0`, which the increment formula subtracts explicitly.
The general semimartingale Ito formula II.32 remains separate.
Owners: `ForMathlib/Analysis/DSlopeContinuous.lean`,
`Analysis/PathVariation/{EndpointPairStep,CadlagCompositionBounds,StieltjesDSlope,StieltjesCountableSupport,FiniteVariationCadlag,CadlagC1ChangeOfVariables}.lean`,
`Process/FiniteVariation/CadlagChangeOfVariables.lean` and
`Process/Semimartingale/StochasticIntegral/CadlagFVChangeOfVariables.lean`.

Protter II.32's continuous case and continuous preservation corollary
(printed pp.79--81, PDF pp.90--92) are proved. The actual Taylor-Lagrange
coefficient extends continuously across the diagonal. Exact partial-cell
Taylor sums converge using the original left-Riemann integral and weighted
raw-square limit. Two nested UCP subsequences give a common-event proof
that the Taylor errors vanish uniformly on each compact time interval.
This avoids a separate global boundedness reduction and imposes no moments.
Both integrands are source left limits with zero initial value, whereas the
raw bracket still begins at `X_0^2`. The C2 preservation assertion follows
from the proved identity and the existing integral-preservation theorem.
The general jump case and II.33 are proved in subsequent entries; later applications remain open.
Owners: `ForMathlib/Analysis/QuadraticTaylorSlope.lean`,
`Analysis/PathVariation/{ContinuousPairBounds,QuadraticPairSums,TaylorSums,UniformSquareBound}.lean`,
`Process/Partition/TaylorSums.lean`, `Process/UCP/DeterministicHorizon.lean`,
`Process/Semimartingale/QuadraticVariation/WeightedRiemann.lean` and
`Process/Semimartingale/Ito/{ContinuousTaylorError,Continuous,ContinuousPreservation}.lean`.

Protter II.32's general cadlag raw-bracket identity (printed pp.79--81,
PDF pp.90--92) and general C2 preservation are proved. The proof follows
the source's finite-large-crossing/small-remainder split using actual
endpoint-pair sums, and also makes the summable-series tail selection
explicit. Compact one-sided neighborhoods yield finite separators even
without continuous paths. Bounded square sums and vanishing mesh control
unselected cells. Clipping retains the final partial cell with varying
horizons. Nested raw-QV/error UCP subsequences give a common-event formula
for all times. Both actual jump-correction series are absolutely summable
and locally FV. The resulting adapted cadlag residual supplies C2
preservation. The equivalent continuous-component formula is proved in the
following entry, followed by II.33; later applications remain open.
Owners: `ForMathlib/Analysis/PairDiagonalModulus.lean`,
`Process/Path/CadlagFiniteOscillation.lean`,
`Analysis/PathVariation/{CadlagC2JumpSeries,CadlagPairBounds,CellSeparation,SelectedPairSums,QuadraticPairTailBounds,CadlagQuadraticPairLimit,StoppedQuadraticPairLimit,CadlagTaylorLimit,CumulativeJumpSeries}.lean`
and `Process/Semimartingale/Ito/{JumpSummability,CadlagTaylorError,RawBracket,JumpVariation,Preservation}.lean`.

Protter II.32's continuous-component source formula (printed p.79, PDF p.90)
is now proved for general cadlag semimartingales. Point-atomic/diffuse measure
restriction and countable-set integration give a genuine integral split.
The existing Jordan path integral agrees with a Stieltjes function's own
measure, including the separate initial term. The canonical continuous QV
uses exactly the same realization as the raw bracket; integral version
invariance transfers the split to the stochastic owners. Caglad compact
bounds prove absolute weighted-jump summability. Valid convergent-series
algebra converts second-order to first-order jump corrections. Positive-time
continuous composition of left limits does not assume that the function
preserves zero. II.32 is closed; II.33 is closed below, while subsequent applications remain open.
Owners: `ForMathlib/MeasureTheory/PointAtomicIntegral.lean`,
`Analysis/PathVariation/{MonotoneIntegralMeasure,StieltjesIntegralDecomposition}.lean`,
`Process/FiniteVariation/CagladStieltjesIntegral.lean`,
`Process/Path/LeftLimitCompositionPositive.lean`,
`Process/Semimartingale/QuadraticVariation/IntegralDecomposition.lean` and
`Process/Semimartingale/Ito/ContinuousBracket.lean`.

Foundation for Protter II.33 (printed pp.81--82, PDF pp.92--93): the scalar
Lagrange theorem applied to line restrictions proves the Frechet second-order
remainder in arbitrary real normed spaces. Its actual normalized error is
continuous on the whole pair space, including the diagonal, by the operator-
norm Hessian oscillation estimate. Finite cadlag separators now work in metric
spaces; diagonal coefficient bounds work on compact metric sets and proper
normed path spaces. Vector partition convergence, summable vector jump
corrections and the multidimensional Ito formula are proved in the following entries.
Owners: `ForMathlib/Analysis/{FrechetTaylorLine,FrechetTaylorCoefficient,PairDiagonalModulus}.lean`,
`Process/Path/CadlagFiniteOscillation.lean` and `Analysis/PathVariation/CadlagPairBounds.lean`.

Further II.33 prerequisites: actual norm-square weighted endpoint-pair sums
converge to their summable jump series on proper normed cadlag path spaces.
Finite selections control both large crossings and summable tails; only
bounded energies and vanishing mesh are required. Clipping preserves the
last partial cell under varying horizons. The vector sup-norm energy is
bounded by coordinate square sums, with no new stochastic bracket. Exact
Frechet Taylor sums and absolute first-/second-order jump-correction series
are proved. Countable product path events and finite-coordinate jump-energy
domination give common-event semimartingale summability. The full II.33
stochastic integral identity and preservation are proved in the next entry.
Owners: `Analysis/PathVariation/{VectorEnergy,VectorPairSums,VectorPairLimit,StoppedVectorPairLimit,VectorCadlagBounds,VectorTaylorJumpSeries,VectorTaylorSums,VectorTaylorLimit}.lean`,
the generalized `Analysis/PathVariation/{EndpointPairStep,SelectedPairSums}.lean`,
`Process/Path/FiniteProduct.lean` and `Process/Semimartingale/Ito/VectorJumpSummability.lean`.

Protter II.33 (printed pp.81--82, PDF pp.92--93): both raw- and continuous-
bracket finite-dimensional cadlag Ito formulas and C2 semimartingale
preservation are proved. Coordinate derivatives are standard-basis evaluations
of the existing Frechet derivatives. Exact sums include all ordered Hessian
pairs; nested UCP subsequences identify the actual summable jump correction.
The adapted cadlag residual is FV, establishing nonlinear closure. The
mixed-bracket integral split follows by polarization of the square split,
including the initial product. Absolute weighted-jump summability permits
finite/infinite sum interchange. All identities hold on common events for
all finite times, without moments or global derivative bounds.
Owners: `Process/Semimartingale/Ito/{VectorTaylorError,VectorRawBracket,VectorJumpVariation,VectorPreservation,VectorContinuousBracket}.lean`,
`Process/Semimartingale/QuadraticCovariation/IntegralDecomposition.lean`,
`Process/{UCP,Semimartingale}/FiniteSum.lean`, `Process/Path/LeftLimitFiniteComposition.lean`,
`Process/Partition/VectorTaylorSums.lean`, `Analysis/PathVariation/UniformVectorSquareBound.lean`,
and `ForMathlib/Analysis/{FiniteCoordinateDerivatives,FiniteCoordinateTaylorSeries}.lean`.

Protter II.34 and its corollary (printed pp.82--83, PDF pp.93--94): the source
Fisk--Stratonovich integral and C3 change-of-variables formula are proved.
Continuous covariation of stochastic integrals follows from the raw identity,
the actual jumps/initial values and the continuous/atomic integral split.
The C2 Ito residual is FV, establishing the continuous-covariation chain
rule. The derivative transform of a C3 function is a semimartingale, so it
belongs to the source Fisk--Stratonovich domain. The actual jump correction
is retained; for continuous inputs it vanishes. General integration by
parts retains the mixed-jump series, and the source corollary follows when
either input is continuous. The integral's correction is zero with either
FV argument; its initial value is zero and its jumps are the Ito jumps.
The later Chapter V C2 extension is not claimed.
Owners: `Process/Semimartingale/FiskStratonovich/{Basic,Ito,IntegrationByParts,Jump,FiniteVariation}.lean`,
`Process/Semimartingale/Ito/{FiniteVariationResidual,ContinuousCovariation}.lean`,
and `Process/Semimartingale/QuadraticCovariation/ContinuousIntegral.lean`.

Foundation for Protter II.35--II.36 (printed pp.83--84, PDF pp.94--95): the
ordered real-coordinate gradient and Hessian of entire analytic functions
are proved from complex derivatives by restriction of scalars. Real linear
functionals cover real and imaginary components uniformly. The source
complex left-limit process is a coordinate wrapper, zero initially and
equal to the actual strict-left complex limit at positive times on cadlag
paths. It is adapted/caglad under the original usual conditions. Complex
semimartingales are pairs of real ones; complex integrals are assembled from
the original real integrals, with the complex initial product retained.
Real-linear commutation, complex scalar multiplication and analytic
semimartingale preservation are proved. These prerequisites are used by the
completed complex Ito identities below.
Owners: `ForMathlib/Analysis/{FiniteCoordinateSecondDerivative,ComplexCoordinateDerivatives,ComplexRealLinear}.lean`,
`Process/Path/Complex.lean`, `Process/Measurability/ComplexLeftLimit.lean`,
and `Process/Semimartingale/Complex/{Basic,Integral,RealLinearIntegral,Preservation}.lean`.

Protter II.35--II.36 (printed pp.83--84, PDF pp.94--95) are proved.
The bilinear complex bracket is `[Re Z] - [Im Z] + 2i[Re Z,Im Z]`,
assembled from the existing real owners. Its continuous part is continuous
and zero initially; its raw initial value is `Z(0)^2`. The distinct real
energy bracket is the sum of the two real square brackets and is nonnegative
and increasing. Source left limits commute with real linear functionals at
all times. The two gradient and all four ordered Hessian integrals combine
into the existing complex integral and its bilinear continuous-bracket term.
The actual analytic jump correction is absolutely summable on a common
event for every finite horizon. Applying the real vector theorem to both
components proves the cadlag identity (II.36). For continuous inputs jumps
vanish; zero initial integrands identify the raw and continuous bracket
integrals, giving the source raw-bracket formula (II.35). No initial moment,
bounded derivative, Hermitian replacement or new stochastic extension is used.
Owners: `Process/Semimartingale/Complex/{QuadraticVariation,BracketPaths,IntegratorAlgebra,LeftLimitIntegral,BracketIntegral,GradientIntegral,HessianIntegral,JumpSummability,ItoComponent,Ito,ContinuousBracketIntegral,ContinuousIto}.lean`,
`Process/Path/{ComplexLeftLimitLinear,ComplexJump}.lean`, and
`ForMathlib/Analysis/ComplexCoordinateTaylor.lean`.

Protter II.37 foundation (printed pp.84--86, PDF pp.95--97): the actual
product expression is defined from the existing continuous quadratic variation.
Square-summable jumps imply absolute summability of `(1+u)exp(-u)-1`, using
the real C2 Taylor quotient; this proves convergence without excluding zero
or negative factors. The compensated raw-bracket product also converges,
and equality of the two source expressions is proved when `X(0)=0`.
A product zero is equivalent to a positive-time jump of size -1, which
annihilates all subsequent values. The separate initial jump is excluded.
For continuous inputs the same product-defined process is strictly positive,
continuous and a semimartingale. Ito applied to `X-[X]^c/2` proves its
integral equation, retaining `exp(X(0))` without an initial-moment premise;
the source unit-initial equation follows for `X(0)=0`.
General cadlag path regularity is proved by dominated convergence for
products of absolutely summable deviations. The actual product factor has
local finite variation and equals one plus its absolutely convergent jump
series. A finite-subset expansion into step coefficients proves this
without logarithms, sign restrictions, or nonvanishing assumptions.
At every positive time the full exponential satisfies `Delta E = E_- Delta X`
on one common event. Time zero is correctly excluded from this identity.
General adaptedness is proved using the finite-horizon raw-bracket measure:
its positive-time atoms are exactly the squared jumps. Measurable atomic
kernel integrals represent actual real/complex jump series without a
deterministic enumeration. A separately summable zero-factor count and
the principal complex logarithm preserve both zeros and negative factors.
Only capped paths and the horizon sigma-field are used; one initial null
set is removed and restored by usual completeness. The same product-defined
exponential is consequently a semimartingale for general cadlag inputs.
The general jump-case integral equation is now proved. The two-coordinate
Ito formula for `exp(x) y` keeps the full Hessian before FV mixed-bracket
vanishing and continuous drift invariance cancel the bracket terms. The
actual pure-jump Stieltjes integral is its initial product plus its weighted
jump series, so the remaining Ito correction cancels without dividing by
the jump product. Compact path bounds follow from caglad regularity. Both
arbitrary-initial and unit-initial equations use the same canonical process.
Uniqueness remains unproved, so II.37 is not yet closed. Protter's own
uniqueness reference is V.7 (printed pp.257--260, PDF pp.268--271), whose
semimartingale slicing/contraction prerequisites are not assumed here.
Owners for this continuation:
`Analysis/PathVariation/StieltjesPureJumpIntegral.lean`,
`ForMathlib/Analysis/ExponentialProductCoordinates.lean`,
`Process/Semimartingale/StochasticIntegral/{PureJumpFiniteVariation,ZeroIntegrator}.lean`,
`Process/Semimartingale/Ito/ExponentialProduct.lean`, and
`Process/Semimartingale/StochasticExponential/Equation.lean`.

Protter II.38 and its continuous inverse consequence (printed p.86, PDF
p.97) are implemented directly from the product formula. Multiplication
uses `Delta(X+Y+[X,Y])=u+v+uv`, FV drift invariance and the continuous/mixed
jump decomposition. The exponential of the mixed-jump sum cancels its
compensated product, with no division by zero or negative factors. The
general initial correction is `exp(X(0)Y(0))`. The continuous inverse with
the zero-initial continuous bracket needs no initial guard; its raw-bracket
source form requires `X(0)=0`. Version invariance compares the existing
canonical products and brackets. Owners:
`Analysis/PathVariation/ExponentialJumpProductMultiplication.lean`,
`Process/Semimartingale/QuadraticVariation/ContinuousDrift.lean`, and
`Process/Semimartingale/StochasticExponential/{Multiplication,Congr,ContinuousInverse}.lean`.

Protter II.39 exponential-martingale step (printed p.87, PDF p.98): the
actual `exp(i u X + u^2 [X]^c/2)` satisfies its source complex integral
equation. Coordinate integration and real masked local-L2 preservation
prove its complex local-martingale property. When `[X]^c=t`, its norm is
bounded by `exp(u^2 T/2)` on each compact horizon; coordinate envelope
promotion yields the usual complex martingale predicate. The arbitrary
initial phase is kept, so zero-initial conditions remain available for
the separate Brownian identification. The real stochastic exponential
of a continuous local martingale is also proved continuous local.
Owners: `Process/Semimartingale/StochasticExponential/{ContinuousLocalMartingale,Characteristic,CharacteristicEquation,CharacteristicMartingale}.lean`,
`Process/Semimartingale/Complex/{ZeroIntegrator,LocalL2}.lean`,
`Process/LocalMartingale/{Complex,ComplexBounded}.lean`,
`Probability/Martingale/Complex.lean`, and
`ForMathlib/Probability/MartingaleLinearMap.lean`.
Protter II.39 is now proved in both directions (printed pp.86--87,
PDF pp.97--98). Bounded complex conditional-expectation pull-out gives the
Gaussian conditional characteristic function. Fourier uniqueness identifies
the law restricted to every past event, proving the increment law and
independence from the entire past sigma-algebra. Ordered finite-intersection
induction then gives mutual independent increments and the canonical Mathlib
Brownian predicate. Conversely, compatible Brownian increments imply both
martingale and square-minus-time martingale properties; continuous FV
local-martingale constancy identifies the existing raw bracket with time.
The final equivalence keeps adaptedness and independence from the specified
filtration. Brownian laws alone do not imply a martingale in every larger
filtration; the full-information failure is proved. The raw time bracket
forces the zero initial value, whereas the continuous-bracket variant
requires it explicitly. Repeated times and zero variance are supported.
Additional owners: `Probability/Brownian/{LevyConditionalCharacteristic,LevyIncrementLaw,LevyCharacterization,LevyEquivalence,FiltrationMartingale,FiltrationBoundary}.lean`,
`Probability/Independence/{ConditionalCharacteristic,OrderedPast}.lean`,
`Process/IndependentIncrements/Filtration.lean`,
`Process/Semimartingale/QuadraticVariation/ContinuousCharacterization.lean`, and
`ForMathlib/MeasureTheory/ConditionalComplexMultiplication.lean`.
II.40 is completed in the following entries; subsequent applications remain
open. This does not establish general usual-filtration augmentation/transport.

Protter II.40 projection prerequisites: characteristic exponentials with any
deterministic continuous bracket are genuine martingales on finite horizons.
Bracket monotonicity gives the required bound and, in a probability space,
implies monotonicity of the deterministic clock. Conditional characteristic
functions yield Gaussian increment laws with the clock increment as variance
and independence from the past, including flat intervals. Finite linear
combinations of continuous local martingales use the existing masked localizers.
Continuous square and mixed brackets satisfy the full finite double-sum
formula; orthogonality with a common clock gives the sum of squared coefficients.
The raw/continuous orthogonal-clock bridge retains the explicit initial guard.
Owners: `Process/Semimartingale/StochasticExponential/DeterministicBracket.lean`,
`Process/LocalMartingale/{FiniteLinearCombination,DeterministicBracketLaw}.lean`,
`Process/Semimartingale/FiniteSum.lean`,
`Process/Semimartingale/QuadraticCovariation/{FiniteSum,ContinuousLeft,OrthogonalClock}.lean`,
`Process/Semimartingale/QuadraticVariation/FiniteLinearCombination.lean`, and
`Probability/Brownian/LevyLinearProjections.lean`.
These projection prerequisites feed the following joint-law closure.

Protter II.40, printed p.87 / PDF p.98: **IMPLEMENTED**.
Hilbert-space restricted-law Fourier uniqueness gives joint vector increments
with the canonical product Gaussian law and independence from the specified
past. Vector independent increments yield joint Gaussianity across time and
coordinate. Zero cross-coordinate covariance at arbitrary times then proves
mutual independence of the entire coordinate processes. The result uses
Mathlib's `IsBrownianReal` and `iIndepFun`, not a competing vector-process owner.
The raw diagonal bracket forces the initial values to vanish; the continuous
variant states that condition explicitly. Empty finite families and repeated
times are included, without a positive-definiteness premise.
Owners: `Probability/Independence/ConditionalCharacteristicHilbert.lean`,
`ForMathlib/Probability/GaussianVectorCharacteristic.lean`, and
`Probability/Brownian/{LevyVectorIncrementLaw,LevyVectorGaussianProcess,LevyVectorIndependence,LevyMultidimensional}.lean`.
The original real conditional-Fourier theorem delegates to the Hilbert-space
proof. The existing filtration-to-independent-increments theorem now also
supports vector-valued processes. II.37 uniqueness remains open;
the II.41 scope and source correction are detailed below.

Protter II.41, printed pp.87--88 / PDF pp.98--99: **OPEN-DOMAIN HARMONIC AND
CORRECTED CLASSICAL C2 SUBHARMONIC PROVED; NONSMOOTH SCOPE UNDER AUDIT**.
The harmonic case is proved on arbitrary open domains with the existing continuous bracket,
finite stochastic-integral sums and the complete ordered Hessian contraction.
Zero Hessian trace is needed only along one common event of actual paths;
the Euclidean specialization reuses Mathlib's `HarmonicOnNhd` and Laplacian.
Initial values need not be integrable, and empty coordinate families are legal.
The printed subharmonic-to-true-submartingale conclusion is false without
additional hypotheses: `exp(x^2/2)` is smooth with strictly positive Laplacian,
yet its standard Brownian composition is nonintegrable at time 1 and is not
a submartingale under any filtration. This is an actual Gaussian-density
nonintegrability proof, not reliance on the totalized Bochner integral.
The corrected full-space positive direction is now proved. The actual Hessian
trace integral supplies an adapted continuous increasing zero-initial drift;
subtracting it leaves a continuous local martingale. Bounded drift exits and
the existing masked fundamental sequence give Mathlib `Locally Submartingale`.
Compact-time integrable envelopes then permit promotion to a true
submartingale. No integrability assumption is smuggled into the local result.
The harmonic composition is also a true martingale under the same domination.
Open-domain localization is now constructed. Smooth cutoffs give genuine C2
extensions near closed regions; compact exhaustions and their actual exit
times localize the paths. On zero-exit events the coordinates are patched to
a point inside the domain, preserving continuous brackets via an F0-measurable
constant perturbation. The source raw common clock becomes `A_t - A_0`.
The harmonic result uses canonical `HarmonicOnNhd`; the subharmonic result
explicitly assumes `ContDiffOn` of order 2 and nonnegative Laplacian on the
domain. The printed statement does not explicitly state this smoothness
convention, though its proof applies Ito and the Laplacian. No nonsmooth
potential-theoretic extension has been proved, and that source-scope audit
remains open. Thus the unqualified source statement is not marked closed.
Owners: `Process/Semimartingale/Ito/{ContinuousCoordinates,TraceZero,Harmonic}.lean`,
`Process/Semimartingale/QuadraticCovariation/IsotropicIntegral.lean`,
`Process/Semimartingale/StochasticIntegral/FiniteSum.lean`,
`Process/Path/FiniteSum.lean`,
`ForMathlib/Analysis/{EuclideanCoordinateLaplacian,CriticalGaussianGrowth}.lean`,
`ForMathlib/Probability/GaussianCriticalExponential.lean`, and
`Probability/Brownian/SubharmonicBoundary.lean`.
Positive-direction owners:
`Analysis/PathVariation/IncreasingIntegral.lean`,
`Probability/Martingale/{MonotonePaths,LocalSubmartingale}.lean`,
`Process/Semimartingale/StochasticIntegral/Increasing.lean`, and
`Process/Semimartingale/Ito/{IncreasingDrift,Subharmonic}.lean`.
Open-domain owners: `ForMathlib/Analysis/LocalSmoothExtension.lean`,
`ForMathlib/Topology/OpenDomainExhaustion.lean`,
`Probability/Martingale/InitialMask.lean`,
`Process/Stopping/ClosedRegion.lean`, `Process/LocalMartingale/RegionStopping.lean`,
`Process/Semimartingale/QuadraticCovariation/{FiniteVariationPerturbation,OrthogonalClock}.lean`,
and `Process/Semimartingale/Ito/{HarmonicClosedRegion,HarmonicOpenDomain,SubharmonicClosedRegion,SubharmonicOpenDomain,IsotropicApplications}.lean`.

Protter II.42, printed pp.88--89 / PDF pp.99--100: **STATED THEOREM PROVED**.
The canonical extended strict-upper-level hitting
time is the inverse clock. For continuous increasing zero-starting clocks,
`t <= T_s` iff `A_t <= s`; unboundedness gives finite inverse times and
`A_(T_s) = s`. The identity `T_(A_t) = t` is not assumed and is false in
general. Properness and surjectivity make the clock a quotient map; a
continuous path constant on its fibers therefore descends continuously.
The existing continuous bracket is merely converted to `NNReal`, with exact
real-value equality everywhere. Its common-event fiber constancy gives
continuous sampled local-martingale paths, adaptation to the canonical
`F_(T_s)` filtration and actual clock substitution recovering the process.
The original clock is a family of stopping times in that filtration.
Raw-bracket divergence implies continuous-clock unboundedness, and zero
initial values give the exact source raw-bracket inverse times on one event.
The Brownian law follows from the actual characteristic exponential, bounded
after stopping at an inverse-clock level. Complex UI optional sampling at
AE-finite times gives conditional Gaussian characteristic functions; Fourier
uniqueness yields Gaussian laws and independence from the entire `F_(T_s)`
past. No square-moment or time-changed-martingale conclusion is a premise.
Usual completeness identifies the raw and canonical stopping sigma-algebras.
The final theorem uses the exact raw hitting times, the canonical Mathlib
Brownian predicate, and common-event path/clock identities. Nonnegative time
conversion of the raw clock is justified on the same event. No new bracket,
Brownian or filtration owner is introduced. The proof's auxiliary
right-continuation is also proved: `H_s = G_(s+)` is usual, the same Brownian
process is adapted with future increments independent of `H_s`, and the
original clock remains a family of `H`-stopping times. Bounded continuous
tests and dominated convergence pass independence from times above `s` down
to `s`, for any adapted right-continuous real process. No equality `G = H`
or right continuity of the unextended sampled filtration is assumed.
Owners: `Process/TimeChange/{ClockInverse,InverseClockProcess,QuadraticVariationClock,BracketStopping}.lean`,
`Probability/Brownian/{DambisDubinsSchwarzPaths,DambisDubinsSchwarzCharacteristic,DambisDubinsSchwarz,DambisDubinsSchwarzRaw,DambisDubinsSchwarzRightCont}.lean`,
`Process/Filtration/IndependentIncrementsRightCont.lean`,
`Probability/Martingale/OptionalSampling/ComplexBounded.lean`,
`Process/LocalMartingale/ComplexStopping.lean`,
`Process/Stopping/MeasurableSpaceCongruence.lean`, and
`Process/Semimartingale/StochasticExponential/CharacteristicStopping.lean`.

Protter II.43 and its corollary, printed pp.89--91 / PDF pp.100--102:
**CHARACTERISTIC FUNCTION AND POSITIVE-TIME DENSITY PROVED**. The project-owned
area is the difference of the two existing left-limit integrals, with the
source twice-signed-area normalization. It starts at zero for arbitrary
initial coordinates, is a semimartingale, and preserves continuous local
martingales. Raw/continuous mixed brackets and the continuous energy are
derived, not assumed. The actual hyperbolic terminal coefficients are smooth,
satisfy `alpha' = alpha^2 - u^2` and `beta' = alpha`, and vanish at the terminal
time. Their signs bound the actual exponential by one for `t <= T`, including
zero and negative Fourier parameters. The complex coefficient-square algebra
is verified. The actual exponential's Ito equation, drift cancellation,
local-martingale property and inverse-cosh characteristic function are proved.
The positive-time density is proved by the Fourier calculation below.
The corollary's density is meaningful only for positive time; time zero has
the already-proved zero area and hence a point-mass law.
Owners: `Process/Semimartingale/StochasticArea/{Basic,Covariation}.lean`,
`Process/Semimartingale/QuadraticCovariation/Subtraction.lean`, and
`ForMathlib/Analysis/LevyAreaRiccati.lean`.
The actual clock-parameterized area exponent and exponential are constructed
as complex semimartingales, with continuous paths on the continuous domain.
Their deterministic norm bound, inverse-cosh initial value and exact terminal
characteristic integrand are proved. The continuous zero-starting FV C1 formula
gives actual stochastic-integral equations for both Riccati coefficients,
including the initial correction. The full exponential drift cancellation and
local-martingale proof below use these construction results without assuming the conclusion.
Further owners: `Process/Semimartingale/StochasticArea/{Exponent,RiccatiDynamics}.lean`
and `Process/Semimartingale/StochasticIntegral/ContinuousFVChangeOfVariables.lean`.
The two common raw square brackets give the actual squared-radius equation
and, by linearity/associativity, its integrated form for arbitrary adapted
caglad outer integrands. This does not silently center a nonzero raw clock.
The integral of a random constant is its initial product; C1 FV clock
substitution therefore retains `H_0 f(0)` even though the original clock
starts at zero. Regressions distinguish the nonzero constant-integrator
product from the identically zero area of two random constant coordinates.
Owners: `Process/Semimartingale/StochasticArea/Radius.lean` and
`Process/Semimartingale/StochasticIntegral/{ConstantIntegrator,ContinuousFVSubstitution}.lean`.
The continuous-FV multiplier identity retains arbitrary semimartingale and
multiplier initial values. Applied to the squared radius, it proves the actual
real-exponent representation `beta(0) - J_X(alpha X) - J_Y(alpha Y)
- (1/2) J_Q((X^2+Y^2)(alpha^2-u^2))` under continuous zero-starting coordinates
with common raw FV clock. The continuous-coordinate area formula is proved
without zero initial values, since its two initial products cancel. The later
complex-integral and Ito steps use these identities for the drift cancellation.
Owners: `Process/Semimartingale/StochasticIntegral/ContinuousFVProduct.lean` and
`Process/Semimartingale/StochasticArea/{RadiusDynamics,RealDynamics,ContinuousDynamics}.lean`.
Continuous mixed/square brackets of a C1 FV-clock multiplier times a continuous
semimartingale now follow from the actual product formula and removal of its
FV integral remainder. For finite families of actual stochastic integrals,
common diagonal clocks and zero off-diagonal brackets give the clock integral
of the coefficient inner product (or sum of squares). Two-coordinate interfaces
specialize the finite theorem by proved indistinguishability transports.
Consequently the actual continuous area bracket is `J_Q(X^2+Y^2)` for continuous
coordinates with common orthogonal continuous brackets. No zero coordinate
start, moment bound or Brownian law is needed for this identity.
Owners: `Process/Semimartingale/QuadraticCovariation/{ContinuousFVMultiplier,IsotropicStochasticIntegral,IsotropicIntegralPair}.lean`
and `Process/Semimartingale/StochasticArea/OrthogonalClock.lean`.
The squared radius has continuous bracket `4 J_Q(X^2+Y^2)` and zero mixed
continuous bracket with the actual area, under continuous zero-starting
coordinates with common raw FV clock and orthogonal continuous brackets.
FV multiplier calculus then gives real-exponent bracket `J_Q(alpha^2 R)`,
imaginary-exponent bracket `u^2 J_Q(R)`, and zero cross bracket, where
`R=X^2+Y^2`. Combining the existing real owners proves the actual complex
bilinear exponent bracket `J_Q(R(alpha^2-u^2))`. This is not a nonnegative
energy assertion. The exponential Ito cancellation below uses this bilinear bracket.
Owners: `Process/Semimartingale/StochasticArea/{RadiusBracket,ExponentBracket}.lean`.
The complex-coordinate integral now inherits random-constant initial products,
integrator/integrand version invariance, zero-imaginary-integrator reduction
and associativity with a real inner integral. Continuous real local martingales
preserve complex local martingales under arbitrary adapted caglad complex
integrands, using the proved local-square-integrability theorem internally.
These interfaces retain initial products and introduce no new extension or
localization owner. They are used in the actual area-exponential Ito cancellation below.
Owners: `Process/Semimartingale/Complex/{ConstantIntegrator,Invariance,Associativity,ContinuousLocalMartingale}.lean`.

The actual real and imaginary exponent integrals and complex-bracket integral
now combine in analytic Ito: the opposite half-clock terms cancel. This proves
an equation containing only four actual complex integrals against the two
real coordinates, with the exponent's initial value retained. Continuous-local
coordinates therefore give a complex local martingale. At a deterministic
time whose common raw clock has deterministic level `T`, stopping bounds its
norm by one; the true-martingale endpoint identity gives `1/cosh(u*T)`.
The standard clock and independent-Brownian interfaces discharge the clock
regularity and canonical bracket inputs. Brownian square-sum convergence in
probability is compared with the existing raw-bracket UCP limit, using exact
dyadic restriction transport; independent normalized sums then give the mixed
bracket zero. Future-increment independence from the chosen filtration remains
explicit. No area law, martingale differential or extra package is assumed.
The time-zero pushforward is proved to be `dirac 0`; the density corollary for
positive time follows below.
Owners: `Process/Semimartingale/StochasticArea/{Integral,RealExponentIntegral,BracketIntegral,ExponentialEquation,ExponentialMartingale,Characteristic,TimeClock}.lean`
and `Brownian/{SemimartingaleCovariation,StochasticArea}.lean`.

The positive-time density corollary is now proved. A sigmoid substitution
transforms the hyperbolic-secant Fourier integral into Mathlib's beta integral;
the proved Gamma reflection formula evaluates it. Scaling gives the exact
Fourier transform of `1/(2*T*cosh(pi*x/(2*T)))` for `T>0`. The density's
nonnegativity, integrability and unit integral construct an actual probability
measure. Characteristic-function uniqueness identifies the existing area
pushforward with this measure, for both orthogonal clock-time continuous local
martingales and canonical independent Brownian motions with explicit filtration
conditions. This is a proved analytic alternative to the source's residue
calculation, not an assumed transform or density. The zero-scale measure is
`dirac 0`, explicitly different from the zero-density measure. II.43 and its
density corollary are closed; other source obligations remain open.
Owners: `ForMathlib/Analysis/HyperbolicSecantFourier.lean`,
`Probability/Distributions/HyperbolicSecant.lean`,
`Process/Semimartingale/StochasticArea/Density.lean`, and `Brownian/StochasticArea.lean`.

Owners: `Process/Semimartingale/StochasticExponential/{Basic,Product,Continuous,ContinuousEquation}.lean`,
`Process/Semimartingale/StochasticExponential/{Cadlag,Jump,ProductVariation,ProductPureJump}.lean`,
`Analysis/PathVariation/{CumulativeProduct,CumulativeProductJump,CumulativeProductVariation,CumulativeProductExpansion,CumulativeProductPureJump,CumulativeStepSeries,CumulativeStepSeriesPureJump}.lean`,
`ForMathlib/{MonotoneIndicatorVariation,RestrictedFiberSum}.lean`,
`ForMathlib/Topology/Order/StepCutoffLimits.lean`,
`Process/Semimartingale/StochasticExponential/{Adapted,Preservation}.lean`,
`Process/Semimartingale/QuadraticVariation/Atoms.lean`,
`Process/Measurability/CappedJump.lean`,
`Analysis/PathVariation/{ExponentialJumpProductLog,MeasurableExponentialJumpProduct}.lean`,
`ForMathlib/MeasureTheory/{MeasurablePointAtomicPart,PointAtomicIntegrability,MeasurableAtomicSeries,MeasurableComplexAtomicSeries}.lean`,
`Process/Semimartingale/QuadraticVariation/ContinuousDrift.lean`,
`Process/Semimartingale/UsualCongruence.lean`,
`Analysis/PathVariation/{ExponentialJumpFactor,ExponentialJumpProduct}.lean`, and
`ForMathlib/Analysis/SummableQuadraticRemainder.lean`.

### Continuous-time Doob control for the remaining moment criteria

`Martingale/Inequalities/{DoobFiniteTime,DoobContinuousL2}.lean` proves sharp
`p > 1` bounds on arbitrary finite sets of continuous-time samples and an L2
maximal bound on the existing clipped dense grid. Monotone convergence proves
integrability and AE finiteness of the extended square supremum. Its square
root is a measurable L2 envelope, and right continuity gives the common-event
bound for every time up to the terminal time. The envelope's squared integral
is at most four times the terminal second moment; the initial value is retained.
This supplies the Doob/DCT input in Protter II.27, Corollary 3 (printed pp. 73--74).
The forward moment direction is now proved in
`Process/Semimartingale/QuadraticVariation/Moments.lean`: for true cadlag
martingales square-integrable at every finite time, the actual raw bracket is
integrable and its expectation equals the second moment, including time zero.
Localize `X^2-[X,X]`, whose initial residual vanishes. Doob domination controls
the stopped squares; Fatou first proves bracket integrability, then dominated
convergence proves the exact expectation identity. Constant and compensated
Poisson regressions retain the initial term and the discontinuous domain.
The reverse/general local-martingale implication and the infinite-terminal
Corollary 4 remain open.

`QuadraticVariation/{JumpBound,JumpLocalization}.lean` supplies the converse's
localization step. Every jump is bounded by the square root of the actual raw
bracket, including the initial jump. Caglad cutoffs of the left-limit process
give the envelope `n + sqrt([X,X]_T)` for the masked stopped local martingales.
When the bracket is integrable on each finite horizon, these are proved true
L2 martingales using the existing envelope criterion. Initial L2 integrability
is derived, not silently assumed. The existing semimartingale witness remains
explicit until the general LM-to-SM bridge is proved. This localization step
alone does not establish the unlocalized true-martingale conclusion.

`QuadraticVariation/MomentCriterion.lean` now proves that unlocalized conclusion
and the finite-time equivalence on the actual semimartingale domain. Localized
square residuals have integrable envelopes, so their zero expectations give
uniform bracket-controlled second moments. Doob and Fatou give a finite
maximal-square envelope for the original local martingale, proving true
martingality and L2 integrability. The continuous-local-martingale entry needs
no extra semimartingale premise. For a true finite-time L2 cadlag martingale,
the square-minus-raw-bracket residual is itself a true martingale. This is
II.27 Corollary 3 with the existing bracket domain explicit; removing that
witness for every local martingale still requires III.30. Corollary 4's
infinite-terminal statement remains open.

`QuadraticVariation/ContinuousMoments.lean` derives the normalized finite-time
interfaces from the sole existing continuous-part owner. For continuous true
L2 martingales its expectation is `E(X_t^2)-E(X_0^2)`, and `X^2-CQV` is a true
martingale retaining initial value `X_0^2` (Klenke 21.70(ii), printed p. 566).
For continuous local martingales, finite-time L2 is equivalent to initial L2
together with integrability of this normalized bracket at every finite time.
This includes Klenke Corollary 21.76 (printed p. 571), with its initial L2
hypothesis retained; it does not assert a terminal or stopping-time extension.
The zero-normalized-bracket safeguard keeps the initial condition, and the
compensated Poisson counterexample rules out dropping continuity. Remaining
Klenke stopping/characterization and infinite-terminal interfaces stay open.

`QuadraticVariation/Terminal.lean` constructs the extended terminal raw bracket
from the existing owner on integer times, retaining its initial square. A
common-event cofinality proof identifies the whole-half-line supremum and
limit. AE monotone convergence identifies its expectation. Finite expected
terminal energy proves finite-time bracket integrability, true L2 martingality
and a uniform second-moment bound. This is preparatory work for Protter II.27
Corollary 4 (printed pp. 73--74), not its full terminal-martingale assertion.
The constant and Brownian regressions distinguish initial energy from zero
increments and finite terminal energy from the totalized real value of infinity.

`Martingale/Inequalities/DoobGlobalL2.lean` passes the existing finite-horizon
dense suprema to the whole half-line by AE monotone convergence and constructs
an actual L2 envelope with Doob's factor four. `QuadraticVariation/TerminalMoments.lean`
proves the converse terminal-energy bound and its equivalence with true global
L2 boundedness, then supplies the energy-controlled global envelope. This
advances Protter II.27 Corollary 4 without assuming a martingale terminal limit.
Regressions retain initial energy, control arbitrary measurable random-time
evaluations and exclude a global second-moment bound for Brownian motion.

`Martingale/Convergence/ContinuousL2Closure.lean` constructs an actual L2
closing variable from discrete martingale convergence and the global envelope.
Uniform integrability in L2 proves integer-time L2 convergence; dominated
convergence proves second-moment convergence, and the tower property closes
all real-time coordinates. `QuadraticVariation/TerminalClosure.lean` identifies
the closing variable's second moment with the extended terminal raw energy by
finite-time moments and monotone convergence. This proves the terminal moment
identity for that constructed variable. Its whole-half-line convergence is
proved by the following separate extension.

`Martingale/Convergence/ContinuousL2Convergence.lean` uses conditional-expectation
contraction to extend integer L2 convergence to all real times.
`Martingale/Inequalities/DoobTailL2.lean` constructs a whole-tail L2 envelope
by freezing before the starting time and reindexing the filtration.
`Martingale/Convergence/ContinuousL2Limit.lean` passes those envelopes to a
subsequence converging AE to zero via the measure-convergence/Borel-Cantelli
theorem; common-event tail control gives the actual full-half-line AE limit.
`QuadraticVariation/TerminalConvergence.lean` thus proves Protter II.27
Corollary 4 (printed pp. 73--74) on the actual semimartingale domain, including
its terminal moment identity. The continuous-local-martingale entry constructs
its semimartingale witness; general LM-to-SM (III.30) remains open. No terminal
limit or tail-envelope premise is inserted into the end-user theorem.

`Process/Stopping/TerminalValue.lean` provides the explicit terminal-value
stopping owner: finite times reuse Mathlib's `stoppedValue`, while infinity
uses the supplied variable. It proves finite/infinite agreement, convergence
of finite truncations under a full-time limit, norm-envelope control and
indistinguishable/terminal-AE version transport. This prepares Protter I.16
(printed p. 9; PDF p. 21), whose actual-terminal martingale case follows below. Protter I.10--I.13
(printed pp. 8--9) distinguish an arbitrary closing variable from the actual
terminal limit. Mathlib's stopping sigma-field lies in `iSup F`, so that
distinction must remain explicit for stopping at infinity.

`Martingale/OptionalSampling/ContinuousInfiniteTerminal.lean` proves UI of
arbitrary stopping families, the minimum and AE-ordered conditional-expectation
identities for possibly infinite times, and the terminal conditional-expectation
representation with Lp control. It uses bounded sampling, actual terminal-valued
truncation, Vitali L1 convergence and conditional-expectation contraction.
`QuadraticVariation/TerminalSampling.lean` constructs all terminal/UI hypotheses
from finite expected raw energy, giving L2 values at every stopping time.
This implements Protter I.16's martingale sampling identities with the actual
terminal value. General non-L2 terminal construction, supermartingale sampling
and arbitrary-closing-variable source bridges remain separate open work.

`Martingale/Inequalities/DoobWeakFiniteTime.lean` and
`DoobWeakContinuousL1.lean` implement the weak L1 maximal estimate underlying
Protter I.20 (printed p. 11; PDF p. 23). Sorted finite samples use Mathlib's
discrete maximal inequality; increasing finite exceedance events give the
extended dense-supremum estimate. One right-continuity event covers the entire
finite interval. Conditional Jensen now exposes the existing norm-submartingale
proof for arbitrary preordered time indices. No L2 or finite real-supremum
hypothesis is inserted. General UI convergence remains separate work.

`Martingale/Convergence/ContinuousL1Closure.lean` constructs an actual integer
AE/L1 terminal limit for a real-valued UI martingale and closes all real-time
coordinates by the tower property. `ContinuousLpContraction.lean` proves the
general p >= 1 contraction and all-time Lp extension, now reused by the earlier
L2 interface. `DoobWeakGlobalL1.lean` and `DoobWeakTailL1.lean` bound all-time
exceedance events by the L1 closing error. `ContinuousL1Limit.lean` then proves
the actual full-half-line AE/L1 limit using zero-measure late-deviation events
at countably many scales. This implements Protter I.12 and the UI/actual-limit-
closing equivalence in I.13 (printed p. 9; PDF p. 21), without L2. The explicit
extended-index filtration formulation and arbitrary-closing-variable bridge
remain separately tracked. `ContinuousUITerminal.lean` constructs all limit
premises of the actual-terminal martingale sampling identities of I.16.
General L1-bounded non-UI and supermartingale convergence are not claimed.

`ContinuousClosingProjection.lean` implements Protter I.10's closed-martingale
assertion (printed p. 8; PDF p. 20): an arbitrary integrable closing variable
has actual terminal limit equal to its conditional expectation onto `iSup F`.
Integer cofinality and Levy upward convergence identify the projection; the
previous full-time UI limit supplies actual half-line AE/L1 convergence.
`Process/Filtration/Terminal.lean` extends the filtration to `WithTop` and
proves agreement with the existing infinite stopping sigma-field.
`ContinuousTerminalExtension.lean` proves the explicit extended-index
martingale/UI equivalence of I.13, preserving finite-time evaluations.
A symmetric two-point counterexample separates an arbitrary closing variable
from its terminal projection. Source I.16 requires a convention bridge at
infinity: the stopping sigma-field in the book (printed p. 5; PDF p. 17)
starts with ambient events, whereas Mathlib's owner starts with `iSup F`
events. Neither that source convention nor an arbitrary terminal variable is
silently substituted for the native stopping owner. General I.10 non-UI/
supermartingale limits remain open.

`Martingale/OptionalSampling/ContinuousClosingTerminal.lean` supplies the
native-owner correction for Protter I.16 (printed p. 9; PDF p. 21).
For arbitrary integrable closing input Y it evaluates the process at infinity
using `E[Y | iSup F]`, proves integrability, and identifies each stopped value
with `E[Y | F_tau]`; AE-ordered optional sampling permits both times infinite.
If Y is terminal-field measurable the unprojected formula follows explicitly.
The original ambient/native distinction is documented rather than hidden:
the symmetric two-point example has a proved usual filtration but the
unprojected formula fails for two infinite stopping times. The martingale
source correction is thus proved and regression-protected; no competing
ambient stopping owner is built. The supermartingale part remains open.

`Process/Filtration/SubmartingaleReindex.lean` reuses the native filtration
reindexing owner for both one-sided martingale classes, including repeated
sample times. `Martingale/Inequalities/UpcrossingFiniteTime.lean` transports
Mathlib's Doob upcrossing estimate to arbitrary finite time partitions and
bounds it by the terminal first moment plus the level/total-mass correction.
The native count is strict-before, so `size + 1` includes the terminal sample.
This is a prerequisite for Protter I.9--I.10 regularization/general L1-bounded
convergence, not a claim that those theorems are already complete.

`ForMathlib/Probability/UpcrossingEmbedding.lean` proves monotone-sampling
comparison for the existing discrete crossing times/counts by hitting-time
minimality. The target cutoff remains strict. `Analysis/PathVariation/
UpcrossingRefinement.lean` uses the existing ceiling-index projection to
derive endpoint-inclusion monotonicity, including different terminal horizons,
and endpoint-set invariance with repetitions allowed. Actual repeated-sample,
common-refinement and incorrect-cutoff regressions protect the quantifiers.
These are deterministic prerequisites of the remaining Protter I.9--I.10
dense-time proof; no full non-UI convergence claim is made here.

### General L1-bounded continuous-time convergence (Protter I.10)

`Analysis/PathVariation/{ExpandingDyadic,DenseUpcrossings,DenseUpcrossingLimit}.lean`
reuses the existing dyadic partition and native crossing owners. Expanding
horizons retain all earlier endpoints; right ceiling approximations converge
at every time. Finite dense counts attain a maximum, and two late strict visits
force an additional crossing on a refinement. With finite counts at every
rational level pair, this extends an integer-time limit to the full half-line.
`Martingale/Inequalities/UpcrossingGlobalL1.lean` proves the finite expectation
bound and one common rational-level event from uniformly bounded first moments.
`Martingale/Convergence/ContinuousL1Bounded.lean` then constructs an integrable
full-time almost-sure limit for right-continuous submartingales, supermartingales
and martingales. This closes the general convergence assertion of Protter I.10
(printed p. 8; PDF p. 20), superseding the earlier open notices above.
There is no UI/L2, supplied-limit, or pathwise supremum premise; no L1 convergence
or terminal closing identity is inferred. I.9 regularization and one-sided
optional sampling remain separate open tasks. No external code was adopted.

### Bounded one-sided stopping integrability (part of Protter I.17)

`Analysis/PathVariation/CeilingIndex.lean` owns exact ceiling evaluation and its
order equivalence; existing upcrossing proofs now reuse it. `Process/Stopping/
PartitionIndex.lean` transports a bounded stopping time to the native discrete
index and recovers exact evaluation on grid endpoints. Discrete submartingale
integrability and expected-stopping monotonicity are reused, not rebuilt.
`OptionalSampling/CountableRangeOneSided.lean` proves terminal conditional
bounds by countably assembling native stopping fibers. `Stopping/UpperApproxPartition.lean`
puts the existing upper approximations on finite uniform partitions and proves
their integrability, signed expectation bounds and a uniform L1 estimate.
`OptionalSampling/ContinuousOneSidedIntegrability.lean` uses right continuity
and Fatou to prove actual bounded stopping-value integrability for both
submartingales and supermartingales. This closes the integrability assertion
of I.17 (printed p. 10; PDF p. 22), not its general conditional inequality.
No UI, positivity, global L1 bound or usual-filtration hypothesis is imposed.
Closed-supermartingale I.16 and full continuous-time one-sided sampling remain open.

### Stopping-value characterization (Protter I.21)

`Martingale/OptionalSampling/ContinuousCharacterization.lean` proves the source
criterion (printed p. 12; PDF p. 24), with an additional arbitrary-common-mean
version. The explicit terminal-valued owner is tested at all stopping times,
finite or infinite. Testing t on a past event and infinity on its complement
gives exact set-integral identities and conditional closure. The finite-time
process is then a uniformly integrable martingale. The proof uses adaptedness
alone; the book's cadlag assumption is unnecessary for this implication.
There is no claim that an arbitrary supplied closing variable equals the actual
path limit. Regressions distinguish deterministic tests from stopping tests,
zero means from zero initial values, and finite-time fallback from the explicit
terminal value. No external code was adopted.

### Convex process transformations (Protter I.19)

`Martingale/Convex.lean` proves both process corollaries (printed p. 11;
PDF p. 23). The conditional Jensen theorem itself is reused from Mathlib's
`ConditionalExpectation/CondJensen.lean`; no duplicate conditional-expectation
owner or theorem alias is introduced. The martingale corollary also supports
finite-dimensional Banach-valued inputs. Global convexity supplies continuity.
Submartingale inputs require a nondecreasing map, and both interfaces require
integrability of every transformed coordinate. Regressions distinguish these
two guards and exercise a nonlinear exponential transformation. No external
implementation was adopted.

### General all-time Doob Lp inequality (Protter I.20)

`DoobNonnegativeFiniteTime.lean`, `DoobCountableLp.lean` and `DoobGlobalLp.lean`
prove the full main inequality (printed p. 11; PDF p. 23): the Lp seminorm of
the all-time supremum is at most p/(p-1) times the supremum of the coordinate
Lp seminorms, for every real p > 1. The input is a nonnegative submartingale,
not merely a true martingale or an L2 process. A separate interface permits
coordinatewise AE positivity. Arbitrary countable sampling needs no ordered
or cofinal enumeration. Right continuity identifies the actual uncountable
extended supremum with a measurable countable one. Finiteness is derived
before constructing a real-valued Lp maximal envelope.

`ForMathlib/MeasureTheory/Function/LpMonotoneSup.lean` proves extended-nonnegative
Lp monotone convergence from native monotone integration and the rpow order
isomorphism. `Process/Path/SupremumGlobal.lean` owns the purely pathwise
dense/full-supremum bridge and its AE-measurability corollary; no alternative
supremum definition is introduced. The norm form for Banach-valued true
martingales follows from the existing norm-submartingale owner. The source's
terminal-L2 specialization uses a closing terminal variable; mere existence
of an L2 path limit is not substituted for closure. No external code was adopted.

### Reverse one-sided uniform integrability

`Martingale/Convergence/ReverseOneSided.lean` supplies a technical prerequisite
for the general one-sided stopping passage in Protter I.17. It uses Mathlib's
filtration and supermartingale on the order dual of the naturals. Expectations
are monotone in the ordinary natural index, and the nonnegative residual
`X_j - E[X_i | F_j]` has exact L1 seminorm equal to the difference of expectations.
An upper expectation bound yields a global L1 bound and UI. The proof splits
off a finite prefix, then combines uniformly small conditional residuals with
UI of the conditional expectations of one integrable coordinate. Negation
gives the reverse-submartingale lower-expectation-bound theorem. No reverse
convergence, optional-sampling conclusion or L2 assumption is inserted.
Its transport to decreasing stopping approximations is completed in the next
entry. No external implementation was adopted.

### General bounded one-sided optional sampling (Protter I.17)

`Martingale/OptionalSampling/{DiscreteOneSided,PartitionOneSided,OneSidedUpperApprox,
ContinuousOneSided,ContinuousOneSidedUsual}.lean` completes the conditional
inequality in I.17 (printed p. 10, PDF p. 22). Native discrete stopping is
transported through exact finite-partition stopping indices and sigma-fields.
`Process/Stopping/PartitionIndexField.lean` permits repeated endpoints and
proves equality of the native stopping information for on-grid times.
`Process/Stopping/DyadicMonotone.lean` proves that the existing upper
approximations at indices `2^n - 1` decrease; the full original mesh need not.
Reverse-supermartingale UI applies to these samples using the initial expected
value bound. Vitali supplies L1 convergence, and set-integral inequalities pass
to the earlier stopping sigma-field. The reusable conditional-order criterion
lives in `ForMathlib/MeasureTheory/ConditionalOrder.lean`.

The usual-condition version uses an indistinguishable progressive modification
before evaluation at random times. AE ordering and AE bounds preserve the
original stopping sigma-field through its proved null-set congruence theorem.
No nonnegativity, global first-moment bound, L2 data, Class D or assumed UI is
added. This closes bounded I.17, not closed-supermartingale I.16 at unbounded
times. No external implementation was adopted.

### Commuting stopping-time conditional expectations (Protter I.18, second corollary)

`Probability/Conditional/StoppingCommutation.lean` proves the two conditioning
orders equal conditioning on the minimum stopping sigma-field (printed p. 11,
PDF p. 23). It reuses native restricted stopping-field comparisons, measurable
indicators and the tower property. The proof is direct and works for complete
real Banach targets and second-countable ordered time spaces, without assuming
ordering, boundedness, path regularity or usual conditions. Both times may be
infinite. The sigma-field at infinity remains the native filtration supremum.

The source statement concerns integrable input. The Lean identities also hold
for nonintegrable input by native conditional expectation's zero totalization;
this does not assert integrability of that input. No external code was adopted.

### Lower-closed supermartingale terminal and stopping integrability

For Protter I.16's supermartingale premise (printed p. 9, PDF p. 21), closure
means `E[Y | F_t] <= X_t` for one integrable Y. It does not identify Y with the
actual path limit. `Conditional/StoppingBounds.lean` transports the coordinate
bound to countable-range finite stopping times. `Martingale/OptionalSampling/
ContinuousClosingBound.lean` passes the inequality to arbitrary bounded times
using the proved upper-approximation L1 convergence. The resulting first-moment
bound is independent of the stopping horizon. The elementary signed moment
estimate is reusable in `ForMathlib/MeasureTheory/ConditionalLowerBound.lean`.

`Martingale/Convergence/ContinuousLowerClosing.lean` derives a global first-moment
bound, actual full-time integrable limit, and domination of the closing input's
terminal projection via native Levy upward convergence. `Martingale/
OptionalSampling/ContinuousClosingIntegrability.lean` applies Fatou to truncated
stopping values. Both actual-limit and closing-projection terminal conventions
give integrable values at arbitrary, possibly infinite stopping times. At
infinity their values can differ. No UI or L1 convergence of the original
supermartingale is claimed. The unbounded two-time conditional inequality is
completed in the following entry. All owners remain native/project-local;
no external code was adopted.

### Unbounded lower-closed supermartingale optional sampling (Protter I.16)

`Martingale/OptionalSampling/{ContinuousClosingUpperTime,
ContinuousClosedSupermartingale}.lean` proves the source one-sided inequality
for arbitrary AE-ordered stopping times, including when both are infinite.
For a bounded earlier time, the later time is truncated and the conditional
expectations of the lower closing input form a native upward-convergent L1
martingale. `ForMathlib/MeasureTheory/FatouLowerL1.lean` supplies signed Fatou
with these convergent lower bounds; it does not assume UI of the upper
supermartingale sequence. Countably many finite-time events then remove the
earlier bound. On the infinite-time event, the terminal-measurable indicator
is already measurable for the earlier native stopping sigma-field, as proved
in `Process/Stopping/TerminalMeasurable.lean`.

The theorem uses the same source correction as the martingale I.16 interface:
the native terminal value is `E[Y | iSup F]`. An unprojected corollary requires
Y to be measurable for that sigma-field. A separate nonnegative-supermartingale
corollary uses terminal zero. Neither initial zero, positivity, L2, UI nor a
path-limit identity for Y is imposed on the general theorem. No external
implementation was adopted.

### Right-continuous expectations: necessity in Doob regularization (Protter I.9)

`Martingale/Convergence/{AntitoneSampling,RightContinuousL1,
RegularizationNecessity}.lean` proves the necessary direction of I.9 (printed
p. 8, PDF p. 20). Antitone samples reindex to reverse one-sided martingales,
whose UI follows from the initial expectation bound. Common-event path right
continuity and native Vitali give L1 convergence. Monotonicity of expectations
then identifies the actual right limit. Under usual conditions, completeness
transfers adaptedness to a given modification, yielding the source necessary
condition for existence. No sufficient-direction or cadlag construction is
claimed. In particular, the isolated-initial-drop example shows that the
right-limit process need not be a modification. No external code was adopted.

### Local boundedness and crossings of a countable regularization skeleton

For the upcrossing construction required by Protter I.9, `Martingale/Inequalities/
OneSidedWeak{Discrete,FiniteTime,Countable}.lean` proves signed weak maximal
control before assuming any path regularity. Bounded first-exit sampling and
conditional lower bounds control the stopped first moment. Sorting transfers
the result to arbitrary finite time sets; increasing finite-prefix unions
give the countable bound. `ForMathlib/MeasureTheory/WeakBoundFinite.lean` proves
that a finite weak constant excludes a positive-measure infinite value.

`Martingale/Convergence/RegularizationSkeleton.lean` supplies local first-moment
bounds and finite rational-level upcrossings of the deterministically clipped
process on every integer horizon. These estimates need neither usualness nor
UI, L2 or global moment control. They do not yet supply the dense-skeleton
extension or the modification identity in I.9. No external code was adopted
for these estimates.

### Simultaneous bounded monotone dyadic sequence limits

`Analysis/PathVariation/{DyadicSkeleton,DenseUpcrossingSampling}.lean` uses the
existing expanding dyadic partitions for the deterministic part of I.9's
upcrossing argument. Their endpoint union is countable and dense. Finite-prefix
congruence and order-preserving embedding bound increasing samples; decreasing
samples use reversed, negated crossings with the necessary N+1 cutoff.
`Martingale/Convergence/RegularizationSequenceLimits.lean` combines this with
the common local-boundedness/crossing event to prove convergence for all bounded
monotone and antitone dyadic sequences on that event. It does not yet identify
their one-sided limits or construct a modification.

`ForMathlib/Probability/{UpcrossingCongruence,UpcrossingReversal}.lean` adapts
the audited project-internal Cameron Freer pathwise/reversal proofs. Attribution
is retained; no external package or legacy internal module is imported and
no duplicate downcrossing/reversal process owner is introduced. The source
strict-cutoff correction is protected by a failing-unshifted-cutoff regression.

### Actual dyadic one-sided limits and the cadlag extension

For Protter I.9's path construction, `ForMathlib/Order/MonotoneSelection.lean`
realizes alternating predicates along a strictly monotone sequence. The generic
`ForMathlib/Topology/OneSidedSequenceLimits.lean` rules out two persistent levels
and derives actual one-sided filter limits from local boundedness and sequence
convergence. `Martingale/Convergence/RegularizationOneSidedLimits.lean` applies
this on the common dyadic event for both one-sided martingale classes.

`ForMathlib/Topology/DenseRightLimitExtension.lean` proves right continuity and
left-limit preservation using closed neighborhoods. `Process/Path/DyadicRightLimit.lean`
selects the actual skeleton right limits using native `limUnder` and proves the
extension cadlag. It agrees with already right-continuous inputs and respects
indistinguishability, but may change an unregularized input's initial value.
Usual-filtration adaptation and equality with the original process under
right-continuous expectations remain open. No external code was adopted in
this packet; the proof reuses the previous audited crossing prerequisites.

### Full Doob regularization (Protter I.9 and its corollaries)

`Martingale/Convergence/{DyadicRightLimitL1,RegularizationModification,
Regularization}.lean` and `Process/Measurability/DyadicRightLimit.lean` close
I.9 (printed p.8, PDF p.20). Antitone skeleton sampling converges in L1 to the
actual dyadic extension. Right-continuity of the filtration plus its usual
completion makes that extension adapted; the common bad-path event is reset
at time zero only within the measurability proof. Conditional-order comparison
and equality of expectations then give the coordinate modification identity.

For both submartingales and supermartingales, right-continuous expectations
are equivalent to a cadlag modification. The same martingale class is retained,
and uniqueness is up to indistinguishability among right-continuous versions.
True martingales need no extra mean hypothesis; already right-continuous
one-sided martingales are cadlag under usual conditions. Arbitrary integrable
initial values are retained. This supersedes the earlier partial I.9 checkpoints,
not the outstanding Chapter III decomposition or source-filtration obligations.

### Class D and Class DL: actual stopping-family owners

`Process/ClassD/{Basic,Stopping,Local,Martingale,OneSided}.lean` supplies the
Class D prerequisite in Protter III.3 (printed p.107, PDF p.118). The predicate
uses the existing finite stopping-time witnesses; adaptation, cadlag paths,
supermartingality and initial normalization remain separate hypotheses.
Class DL is UI on each fixed finite horizon and is proved equivalent to
Class D of every deterministically stopped process. UI over the union of all
bounded stopping families, a stronger assertion, is equivalent to Class D.
Truncation extends Class D to AE-finite stopping families without continuity.

Optional sampling proves the right-continuous true-martingale Class D/UI
equivalence and Class DL property. Nonnegative right-continuous submartingales
are Class DL, including coordinatewise-AE positivity via indistinguishable
regular versions. `Process/ClassD/Counterexample.lean` gives an adapted
random-time spike which is a UI modification of zero but not Class D. It has
no right-continuous paths and does not contradict the martingale bridge.
The continuous deterministic submartingale `X_t=t` separates Class DL from
Class D. These results do not prove Doob-Meyer existence or select its parts.

### Complete discrete potential Doob decomposition (Protter III.9)

`Martingale/Potential/{Basic,Decomposition,Examples}.lean` supplies the analytic
potential predicate and III.9 (printed pp.106--107, PDF pp.117--118).
Continuous-time cadlag paths remain separate. `Martingale/Doob/Supermartingale.lean`
uses the native `predictablePart (-X)` and `-martingalePart (-X)` exclusively,
with zero increasing-part start and martingale start `X_0`.

`Martingale/Convergence/MonotoneL1.lean` constructs the increasing part's actual
integrable terminal limit from its first-moment bound. Its L1 convergence and
potential L1 decay give the martingale's conditional closure and UI, with
terminal mean equal to initial mean. `ForMathlib/Probability/DoobUniqueness.lean`
proves indistinguishability uniqueness with AE decomposition and initial
identities, without completeness. No L2 or prescribed closing variable is
assumed. Discrete III.9 and the full continuous-compensator III.10 theorem are
closed; the general predictable III.11 and local III.16 forms remain open.

### Pre-stopping fields and announcing sequences (Protter III.5--III.8)

`Process/Stopping/{BeforeSigma,BeforeSigmaOrder}.lean` implements the source
`F_(T-)` definition (printed p.105, PDF p.116), proves equality with the
positive-time generator convention, and identifies the zero, fixed-time and
infinite-time fields. It embeds into the existing native `F_T`. III.7 is
proved using a countable union of rational comparison events, allowing
infinite stopping times. Terminal-filtration information restricted to
`{T = infinity}` is measurable in `F_(T-)`.

`PredictableValue.lean` proves III.8 for finite evaluation and for the existing
explicit-terminal owner. No path regularity, usualness or moment hypothesis
is needed. `BeforeSigmaGenerators.lean` proves III.5 for finite stopping times
and the full explicit-terminal generator identity at arbitrary stopping times.
The source III.8 proof uses zero-terminal values; extending that convention
to III.5 at an identically infinite time would make every generator constant
zero. The implementation therefore records the finite domain and terminal
convention explicitly, rather than claiming that false extension.

`{Announcing,AnnouncingSigma,AnnouncingExamples}.lean` supplies the source
announcing relation and predictable-stopping predicate (printed p.104, PDF
p.115). III.6 (printed p.106, PDF p.117) identifies `F_(T-)` with the supremum
of the announcing stopped fields under initial completeness. Convergence is
only almost sure; right continuity is not needed. Fixed times, including zero,
and infinity have actual announcing witnesses. A nonzero two-point probability
space witnesses failure of everywhere convergence. Accessibility, total
inaccessibility and their decomposition theorem remain separate proof gates.

### Optional and progressive sigma-fields (Protter III.1)

`Process/Measurability/ProgressiveSigma.lean` defines the finite-horizon
restriction field and proves equality with the source real-progressive-process
generators (printed p.103, PDF p.114). Native `IsProgressive` is exactly
measurability of the uncurried process in this field. Countably many finite
horizons give inclusion in the ordinary product field. Equality is proved
when the filtration is constantly the ambient sigma-field, not an arbitrary
smaller constant filtration.

`Measurability/Optional.lean` constructs the source adapted-cadlag-generated
optional field (printed p.102, PDF p.113) and proves the full inclusion chain.
Continuous ramps generate the predictable strict-future rectangles. The optional
process predicate is strongly measurable in this field, equivalent to ordinary
measurability for real processes. Optional processes are progressive and adapted.
AE-cadlag adapted processes use an indistinguishable everywhere-cadlag optional
version under usual conditions; arbitrary exceptional trajectories are not
silently declared optional.

`Stopping/OptionalValue.lean` proves measurability of the stopping map for the
optional field by transporting its cadlag generators. Consequently arbitrary
optional processes remain optional when stopped, without being assumed cadlag.
Finite samples and explicit-terminal samples are measurable in the native
stopped field. The initial-spike regression proves that an optional process
need not be right-continuous. The source progressive-debut result, finer strict
inclusion/counterexample statements and stopping classification remain separate.

### Native stopped-field generators (Protter I.6)

`Process/Path/RightStep.lean` proves cadlag step paths at finite and infinite
lifetimes. `Stopping/AfterCoefficient.lean` proves that a native `F_T`-measurable
coefficient, revealed at and after `T`, gives an adapted cadlag optional process.
The coefficient need not be initially measurable or integrable. Activation at
zero retains it immediately; activation at infinity stays zero at finite times.

`Stopping/SigmaGenerators.lean` proves I.6 (printed pp.5--6, PDF pp.17--18):
finite adapted-cadlag samples generate exactly the native stopped sigma-field.
Everywhere-cadlag generators need no usualness; the source AE-cadlag convention
uses a usual filtration, indistinguishability and stopped-field completeness.
All optional real samples generate the same field. An additional arbitrary-time
identity uses explicit terminal-filtration-measurable inputs; it neither
extrapolates ordinary finite evaluation to infinity nor replaces the native
terminal field by the ambient sigma-field. I.6 is closed on these exact domains.

### Accessible and totally inaccessible decomposition (Protter III.3)

`Stopping/{Graph,Restriction,Classification,ClassificationStability}.lean`
implements the definitions on printed p.104 (PDF p.115): graphs contain the
zero-time section and exclude infinity; restriction to `A` requires `A` in
native `F_T`, not in `F_0`. Graphs are optional, strict futures predictable.
Countable predictable coverage defines accessibility; finite coincidence
with every predictable time is null for total inaccessibility. Restriction
preserves both classes, and their finite intersection is null. Countably
valued stopping times are accessible. Their overlap consists exactly of
almost-sure infinity; finite constants are not totally inaccessible on a
probability space.

`Stopping/{ClassificationDecomposition,ClassificationUniqueness}.lean` proves
full III.3 (printed pp.104--105, PDF pp.115--116). The relation is specified
before existence; no selector or assumed decomposition is used. Mathlib's
countable essential union selects a countable family of predictable finite
coincidence events. Its union is accessible; the complementary finite event
is totally inaccessible. Both are native stopped-measurable and disjoint,
reconstruct the original time almost surely, and are unique almost surely,
as are the restricted times. Existence works for s-finite measures; uniqueness
does not need that assumption. Usualness is not required. III.4 Meyer's
Markov/Feller jump classification and predictable-graph equivalence are not
consequences asserted here and remain open.

### Predictable-delay and announcing-stability prerequisites

`Stopping/{Delay,PredictableDelay}.lean` supplies the nonnegative-real fixed
delay bridge missing from native addition (which covers additive groups or
countable time domains). Strictly positive delays have explicit announcing
sequences. Each term caps the original time at an integer before adding a
smaller delay, so that infinity is announced by finite times. This supports
the positive-delay argument used in III.10 Lemma 2 (printed pp.108--109).

`Stopping/{AnnouncingStability,Supremum,AnnouncingSupremum}.lean` proves
target-capped announcing data, finite predictable minima/maxima and countable
predictable suprema. The supremum uses finite maxima of diagonally selected
announcing terms and only a countable intersection of convergence events.
The two-point regression shows why naive maxima of source AE-announcing
sequences can fail at exceptional zero-target samples. No usualness or
everywhere convergence is added. Arbitrary decreasing limits are not claimed
predictable, and III.10 Lemma 2's uniform conditional-probability estimate is
still open.

### Predictable restrictions and strict-limit parts

`Conditional/EventApproximation.lean` uses native Levy upward convergence
and indicator thresholds to obtain events in each sampled sigma-field whose
membership eventually agrees with a given terminal event almost surely.
`Stopping/AnnouncingRestriction.lean` turns these into announcing data for
an event-restricted limit. Tail infima give monotonicity; right continuity
gives stopping; integer caps handle infinity; initial completeness repairs
the exceptional event. Strict inequality is needed only on the retained event.

`Stopping/PredictableRestriction.lean` applies the III.6 announcing-field
identity to prove that restricting a predictable time to an `F_(T-)` event
preserves predictability under usual conditions and a finite measure.
No arbitrary `F_T`-event restriction theorem is asserted.
`Stopping/PredictableLimitPart.lean` proves predictability of the strict-limit
part of any increasing stopping sequence, without assuming that the limit
is already predictable or that the sequence is everywhere strictly increasing.
The finite coincidence of this part with a totally inaccessible time is null.
These supply the stopping-time argument in III.10 Lemma 2, not its still-open
uniform conditional-probability convergence estimate.

### Conditional stopping-window versions (Protter III.10, Lemma 2 prerequisite)

`Martingale/ConditionalProjection.lean` proves the submartingale/supermartingale
property of conditional projections of integrable monotone/antitone families.
`Convergence/ConditionalRegularization.lean` derives right-continuous means
by dominated convergence and constructs cadlag versions under usual conditions.
The input family need not be adapted. `Path/RightContinuousOrder.lean` turns
coordinate AE inequalities into a simultaneous pathwise inequality using a
countable dense set and right limits.

`Stopping/FutureProbability.lean` applies these results to `P(tau <= t+delta | F_t)`.
`Stopping/ConditionalWindow.lean` subtracts the revealed stopping indicator
to construct `P(t < tau <= t+delta | F_t)`, with common-event bounds in `[0,1]`
and vanishing at and after tau. Totally inaccessible times have no deterministic
finite atoms, so the closed lower endpoint agrees coordinatewise.
`ConditionalWindowOrder.lean` proves version uniqueness, common-event width
comparison and zero-width indistinguishability from zero.

Printed p.108 (PDF p.119) uses a capped first threshold time. Its threshold
inequality must be restricted to the actual trigger event; the capped no-hit
fallback does not satisfy it. A zero-process regression records this guard.
Other regressions retain the deterministic atom at zero and the zero-width
case. The uniform-in-time probability estimate is completed below.

### Bounded stopping-window sampling (III.10 Lemma 2 prerequisite)

`Conditional/Locality.lean` proves conditional-expectation locality for
integrable inputs agreeing on a conditioning-field event. Native stopped
fields agree with the deterministic field on each stopping fiber;
`Stopping/ConditionalCountableSampling.lean` uses countably many such fibers
to prove sampling for arbitrary integrable conditional-projection families.
Sampled integrability is explicit, not inferred from coordinate integrability.

`ConditionalBoundedSampling.lean` takes dominated right-continuous limits of
the existing upper stopping grids. The jointly measurable input need not be
adapted; the output may be progressive, or adapted/right-continuous under
usual conditions. Neither process is assumed to be a martingale.
`Path/LifetimeWindow.lean` proves the window indicator's difference identity,
right continuity and joint measurability even for a non-stopping lifetime.
`ConditionalWindowSampling.lean` derives the actual bounded-stop window
conditional expectation, the tested integral identity and the probability
bound restricted to a measurable trigger event. The window retains its strict
lower endpoint and never gains a finite occurrence from an infinite target.
The shrinking-window limit and final uniform estimate are completed below.

### Uniform stopping-window convergence (Protter III.10, Lemma 2)

The lemma on printed pp.108--109 (PDF pp.119--120) is now proved.
`Stopping/ConditionalWindowSequence.lean` constructs an everywhere-cadlag,
pointwise decreasing sequence of versions by one countable initial-null-set
repair. `ThresholdHitting.lean` proves order and stopping-field measurability
of the actual trigger event for a capped first hit. `ShrinkingWindow.lean`
derives the shrinking-window probability limit from the predictable strict
limit, with strictness required only on decreasing trigger events.

`ConditionalWindowUniform.lean` combines these with the previously proved
bounded stopping-window sampling identity. `ConditionalWindowLimit.lean`
extends the sequence estimate to arbitrary widths tending to zero and proves
almost-sure finiteness before real conversion. `ConditionalClosedWindowLimit.lean`
provides the source closed-window theorem and actual existence of versions
whose running suprema converge in measure. Its no-atom bridge changes only
fixed deterministic endpoints, never the random-time sampling endpoint.

`Path/RightContinuousSupremum.lean` reuses the existing countable supremum,
identifies it with the whole closed interval, and converts strict positive
tail bounds to native convergence in measure. Tests retain zero/terminal
time values and prove that deterministic-lifetime small-window suprema stay
one, so total inaccessibility is essential. Lemma 3's modulus, the continuous
decomposition and the general III.11 construction remain open.

### Large-jump enumeration and finite residuals (III.10 Lemma 3 prerequisites)

Printed pp.109--110 (PDF pp.120--121) remove large jumps and estimate a
conditional short-window modulus. `Path/CadlagLargeJumps.lean` proves actual
large-jump local finiteness from finite oscillation separators; it does not
claim the separators are jumps. `CadlagShortWindow.lean` derives compact
short-window bounds from actual one-sided limits and positive-time jump bounds.
`CadlagLargeJumpDetection.lean` gives countable dense-increment detection,
and `Stopping/LargeJumpEvents.lean` proves the fixed-horizon events measurable.

`LargeJumpTimes.lean` constructs the next actual jump after an extended
stopping time. `LargeJumpSequence.lean` gives exhaustive stopping-time
enumeration, strict finite ordering and escape from every finite horizon.
`TotallyInaccessibleJumps.lean` provides the positive-time source coverage
predicate and proves the enumerated times totally inaccessible when it holds.
Initial values remain unrestricted; no finite fallback is used at infinity.

`Path/LifetimeStepJump.lean` proves exact step left limits and jumps, including
zero, infinity and coincident finite sums. `Stopping/JumpCoefficients.lean`
uses the existing explicit-zero-terminal stopping owner to obtain actual
stopped-measurable jump coefficients and their optional revealed steps.
`LargeJumpCoverage.lean` proves that missed-prefix probabilities tend to zero;
`LargeJumpResidual.lean` constructs the actual finite-prefix residual, retaining
its initial value and deriving its small-jump bound on the coverage event.

`Path/FiniteJumpRemoval.lean` proves cancellation and a clipped pathwise
increment estimate. `CadlagWindowOscillation.lean` constructs a measurable
two-time envelope, with doubled-width recovery and finiteness before real
conversion. `CadlagWindowMoments.lean` proves the fixed-cap bound
`E[D_delta^2] <= b^2 P(A) + C^2 P(A^c) + epsilon` eventually. The positive
squared excess on A converges by domination by C^2; no jump-count moment is
assumed. `Martingale/Doob/ConditionalJumpRemoval.lean` takes conditional
expectations only after the clipped pathwise estimate. It never exchanges
`min` with conditional expectation or discards a conditional tail using the
sample's unconditioned tail event. The following entry supplies the actual
modulus convergence; the continuous decomposition remains open.

### Conditional increment modulus (Protter III.10, Lemma 3)

Printed pp.109--110 are implemented in compact-horizon form, in the global
random-AE-finite-terminal form used by bounded stopping, and now on the full
bounded-supermartingale source domain without any terminal-lifetime premise.
The latter closes Lemma 3; the earlier finite-termination result remains useful
for bounded adapted processes that need not be supermartingales.

`ForMathlib/MeasureTheory/Function/EssentialFamilySupremum.lean` specifies
measurable essential upper bounds before proving their existence and AE
uniqueness. Native s-finite countable essential unions select a countable
subfamily. `EssentialFamilyVersions.lean` constructs coherent ambient-measurable
versions whose literal full supremum realizes this bound. No automatic
conditioning-field measurability of these capped versions is asserted.
Single-point spikes show why arbitrary uncountable CE versions cannot be used.

`Martingale/Doob/ConditionalModulus*.lean` proves the compact result from the
actual finite-prefix residual, its fixed-cap second moments, actual cadlag
conditional martingale envelopes, Doob's bound and finitely many TI-window
limits. Threshold, prefix size and width are chosen in that order. A fixed
bound then gives squared-integral and native `eLpNorm 2` convergence, for all
widths tending to zero. Usual completeness permits common-event AE-cadlag
input by an indistinguishable everywhere-cadlag repair.

`GlobalConditionalModulusStopping.lean` derives the actual comparison
`G_delta <= W_(T,delta) + 2 N sup_(t<=T) E[1_(T<tau)|F_t]` in real values,
after proving all extended quantities finite. `FiniteLifetimeTail.lean`
retains the infinity atom; its mass vanishes only under the explicit AE-finite
condition. `LifetimeTailEnvelope.lean` constructs the conditional tail
martingales, so `GlobalConditionalModulusConvergence.lean` obtains actual
global moduli and their probability/L2 limits. No supermartingale or zero
initial value is needed for these bounded finite-termination statements.

The downward unit-jump regression is a bounded cadlag supermartingale,
starts at zero, is constant after time one, and has modulus one for every
positive width. It fails exactly the TI-jump condition. Arbitrary initial
random constants and zero horizons have zero moduli.

`Doob/TerminalPotential.lean` constructs the actual bounded terminal limit `Z`
and its cadlag conditional martingale `M`. The nonnegative supermartingale
`U = X - M` has means tending to zero and dominates late conditional decrements.
`Inequalities/NonnegativeSupermartingaleMaximal.lean` proves the whole-future
outer-probability bound `P(sup_(t>=T) U_t > a) <= 3 E[U_T] / a`.
`ConditionalModulusPotential.lean` compares the global modulus with the compact
one at `T + 1` and this tail event. `SupermartingaleConditionalModulus.lean`
then proves actual existence and probability/L2 convergence without a stopping
time, Class D assumption or zero initial value. No Doob-Meyer decomposition
is used to construct the terminal potential.

`Doob/DyadicApproximation.lean` uses the existing dyadic grids and native
discrete predictable part. Its ceiling extension is left continuous, adapted
via predecessor measurability, monotone and uniformly bounded in second moment.
`PredictableDifferenceEnergy.lean` derives L2 convergence to actual monotone
terminal limits and the conditional-tail terminal-difference energy estimate.
`DyadicTerminalIdentity.lean` closes each actual discrete martingale and proves
the conditional remaining-increase identity at every real time. The original
ceiling coefficient is measurable at that time by its predecessor property.
`DyadicRefinement.lean` preserves predictability on a finer common grid.
`ConditionalIncrementDifference.lean` and `DyadicTerminalEnergy.lean` derive
the actual terminal-difference energy bound from the two moduli.
`DyadicTerminalData.lean` constructs all these data from the bounded process.

`Convergence/TerminalEnergyCauchy.lean` uses native Hilbert-space
Cauchy-Schwarz and existing Lp completeness. `DyadicTerminalConvergence.lean`
therefore constructs the L2 limit across meshes, not just within one mesh.
`PredictableDifferenceMaximal.lean` and `DyadicDifferenceMaximal.lean` prove
an actual all-time envelope with second moment at most
`8 (E[(U_n-U_m)^2] + E[(W_n+W_m)^2])`. `UCP/TerminalEnergy.lean` then applies
in `DyadicUCP.lean` to prove UCP-Cauchy and a common locally uniform Cauchy
subsequence of the actual ceiling steps. No maximal or Cauchy certificate is
an input of the final dyadic theorems.

`DyadicStepRegularity.lean` recovers both step processes exactly on a common
finer grid and computes their actual right limits and right increments,
including time zero. `Path/CagladUniformLimit.lean` supplies the deterministic
left-continuity and vanishing-right-error continuity bridges.

`UCP/CagladContinuousLimit.lean` now uses existing adapted cadlag completeness
on the right-limit sequence. Its difference from the original ceiling sequence
vanishes in UCP; a locally uniform subsequence of the original sequence gives
left continuity of the same limit. Existing continuous-version repair gives
everywhere continuous paths. `UCP/MonotoneLimit.lean` preserves the original
monotone paths and initial values on a common event.

`Doob/DyadicContinuous.lean` instantiates these results with the actual moduli
and normalizes the increasing limit to start exactly at zero.
`DyadicLimitClosing.lean` derives the coordinate L2 limit and actual conditional
terminal closure, so `ContinuousBounded.lean` constructs a continuous predictable
increasing finite-variation `A` with `X + A` a true uniformly integrable cadlag
martingale. No compensator or closing certificate is supplied. This closes the
bounded case of III.10, not its unbounded Class D extension or III.11.
`ContinuousUniqueness.lean` proves uniqueness of continuous finite-variation
martingale compensators with a common initial value, without boundedness.
`ContinuousBoundedRegression.lean` invokes actual existence for
`X_t = 1 - min(t,1)` and identifies its output with `A_t = min(t,1)`.

### Stopping and single-jump localization for Protter III.10

`OptionalSampling/ContinuousOneSidedStopping.lean` proves the minimum-field
one-sided inequality and arbitrary stopping for right-continuous super- and
submartingales under usual conditions. It uses the previously proved
comparison-event conditional-field commutation, not an invalid lift of an
inequality from a smaller conditioning field.
`Stopping/CadlagExitLocalization.lean` constructs the actual finite, monotone,
diverging capped open norm exits. Before-exit and left-limit bounds include
the overshooting endpoint correctly: a stopped bound needs a jump-norm bound.
Without it, only a jump strictly greater than twice the level is forced to
occur at the endpoint; equality is not excluded elsewhere.
`Stopping/TotallyInaccessibleJumpStability.lean` preserves the original
countable TI-jump covering under arbitrary pathwise stopping.
`Doob/ContinuousLocalization.lean` constructs every bounded-jump stopped
compensator and its L2 closing variable, then proves stopping consistency by
actual martingale stopping and continuous finite-variation uniqueness.
`Doob/{SingleJump,SingleJumpTruncation,ContinuousComparison}.lean` supplies
Class D for integrable stopped-measurable single jumps, actual negative-jump
supermartingales, clipped continuous compensators, and compensator comparison
from an actual supermartingale difference. The mean of `C - min(C,n)` tends to
zero. These are prerequisites, not the completed unbounded III.10 theorem.

Source corrections checked against printed pp.111--112: if
`Xhat = X + Mplus - Mminus`, recombination is
`X = (Mhat - Mplus + Mminus) - A`. The large-amplitude tail is not bounded by
the cutoff; the small-amplitude part is. Both distinctions have regression
checks. Global martingale closure must still be proved using UI, not asserted
as a consequence of Fatou alone.

### Integrable variation and predictable conditional jumps (Protter III.3)

`FiniteVariation/Integrable.lean` owns integrable variation as almost-sure
finite total path variation plus integrability of its canonical real value.
The equivalent finite-lintegral characterization preserves infinity.
`Analysis/PathVariation/TerminalVariation.lean` proves the integer-compact
supremum representation without path assumptions; the process module proves
measurability of the original full variation in the terminal and ambient fields.
`TerminalStopping.lean` identifies actual stopped variation with existing
terminal-valued sampling, including the endpoint and infinite lifetime.
`IntegrableStopping.lean` proves stopping and event-mask stability.
`LocallyIntegrable.lean` reuses native `Locally`, proves its exact unmasked
source criterion and finite expected stopped-variation criterion, and derives
actual locally finite variation. Removing the mask is specific to variation:
a zero-stopped path is constant, even with an arbitrary initial random value.

`TerminalLimit.lean` constructs actual positive/negative Jordan terminals from
an integrable variation bound. `IntegrableTerminal.lean` supplies that bound
from the canonical integrable-variation predicate and proves full-half-line
AE/L1 convergence, Class D and finite stopping-value integrability. Initial
integrability is an independent hypothesis. `IntegrableRegression.lean`
checks both the infinite-variation/toReal trap and a nonintegrable Gaussian
random constant with zero variation.

`OptionalSampling/PredictableJump.lean` proves the actual left-limit conditional
identity and zero conditional jump mean at positive bounded predictable times.
It uses announcing sequences, the actual before-field sigma identity, optional
sampling and native Levy upward convergence, not absence of predictable jumps.
These are prerequisites; they do not establish III.11, III.12--III.16 or Yoeurp.

Source correction recorded from printed p120: III.20's displayed right-hand
integral uses A itself, with no compensator mark. The statement needs predictable
A; otherwise M = 1 would force every increasing A to be its own predictable
compensator. Its proof also uses that missing hypothesis. The future corrected
consumer will state it explicitly. A compensator substitution alone is not a
valid general repair because common-jump terms may remain. III.19 also needs
actual absolute integrability for a signed integrand.

### Naturality foundation and actual finite mixed sums (Protter III.12--III.14)

`FiniteVariation/Natural.lean` defines naturality by actual raw-bracket terminal
existence, integrability and zero mean for each bounded cadlag test martingale.
Initial zero, adaptedness, cadlag paths and integrable variation are explicit.
No martingale property of the bracket or proposed terminal is assumed. The
continuous IV example follows from the existing continuous-FV bracket identity.
`Martingale/FiniteCovariation.lean` proves that actual raw deterministic mixed
sums of two martingales have terminal-product mean when one is bounded and
the other merely L1. `Analysis/PathVariation/CovariationVariationBound.lean`
controls those actual sums by initial product plus twice the left bound times
actual variation; the initial product is not silently discarded.

`OptionalSampling/AnnouncingBefore.lean` is the shared left-limit/conditional
expectation owner. `PredictableJumpUI.lean` extends the predictable left-limit,
jump integrability and zero conditional mean results to positive AE-finite
stopping times of UI martingales. No deterministic bound or interpretation of
the totalized value at infinity is used. The bounded theorem reuses the same
limit-identification proof and retains its original public signature.
`Martingale/CovariationExpectation.lean` now passes actual raw mixed sums to
the actual bracket: stopped deterministic partitions ending at the chosen T
have a common L1 variation bound, and UCP plus uniform integrability gives L1
convergence and terminal-product expectation. Only L1 of the FV martingale is
needed. `FiniteVariation/NaturalStopping.lean` tests naturality with an actually
stopped bounded martingale, obtaining zero finite-time bracket mean from its
eventually constant terminal. `NaturalUniqueness.lean` constructs the cadlag
conditional martingale of the indicator of `{A_T > 0}`; its bound, terminal
value and the two bracket means prove coordinate zero, then indistinguishability.
This closes III.13 on its full integrable-variation natural-martingale domain.
III.12's full integral characterization is now proved in the terminal section
below; III.14/Yoeurp remains open.

### Integrable-variation and naturality algebra; actual integral control

`FiniteVariation/IntegrableAlgebra.lean` proves negation and constant/scalar
multiplication by exact extended-variation identities, including a zero
multiplier. Addition and subtraction first accept explicit actual variation
measurability, then derive it for adapted cadlag processes under usual conditions.
Initial values remain arbitrary. `NaturalAlgebra.lean` transports actual raw
bracket terminals through linear operations and indistinguishable adapted
replacement. No bracket martingality is assumed in these closures.

`Path/CagladMeasurable.lean` proves Borel measurability of the original left-
continuous real path, hence of caglad paths, via existing progressive sampling
on the one-point space and actual integer-stopped paths. No boundedness or
finite variation is required. `StochasticIntegral/IntegrableVariation.lean`
uses this and the actual Stieltjes agreement to prove extended variation at
most `ofReal C * eVariationOn A univ` when the integrand is bounded by C at
positive times. Integrable variation follows after finiteness is established;
separate initial-product L1 gives actual terminal AE/L1 convergence and Class D.
The bound does not constrain the time-zero integrand or discard the initial term.

### Full naturality characterizations (Protter III.12 and the preceding remark)

`Martingale/FiniteVariationIntegrand.lean` proves that the actual integral
of A's left limits against bounded cadlag martingale M is a true UI martingale
with zero mean. A only needs adapted cadlag IV paths and separate initial L1.
The actual product, FV integral and raw bracket supply an integrable envelope
through the proved integration-by-parts identity; native local-L2 preservation
is applied only to M, not to A. `NaturalTerminalBalance.lean` constructs all
actual integrable terminal variables and proves the terminal expectation
balance, retaining the raw initial product even for nonzero A0.
`NaturalCharacterization.lean` closes III.12 in both directions. The test
requires actual integrable M/A/left-integral terminals to exist, not a vacuous
implication given a proposed terminal. Limit uniqueness identifies the reverse
direction's variables with those in the independently constructed balance.

`NaturalMartingale.lean` also closes the preceding bracket-martingale remark.
Testing with M stopped at arbitrary raw stopping times gives actual stopped
bracket mean zero, using its genuine terminal at infinity. The existing I.21
characterization yields a true UI bracket. Conversely, actual IV terminal L1
convergence carries constant martingale means to zero terminal mean.

Source-reference caution for the still-open III.14 proof: printed p114 cites
Theorem 25 for a predictable-jump-covering reduction. III.25 on p125 concerns
compensator continuity at TI times; IV.25 on p172 concerns measure-change
invariance of integration. Neither is itself a jump-enumeration theorem. The
p125--126 corollary uses self-compensation of a predictable process, which
cannot be assumed ahead of III.14/III.15. This is a dependency caution, not a
confirmed erratum. The planned noncircular route uses the actual III.10 TI
single-jump compensator pair, separately proved predictable Stieltjes duality,
countable path jump support and stopping-time classification. That independent
duality and the resulting predictable FV jump coverage are now implemented
in the following section. The remaining III.14 series argument is still open.

### Noncircular predictable FV jump coverage for Protter III.14

`Measurability/PredictableMeasureExt.lean` and `PredictableKernelDuality.lean`
use the actual native predictable generators, finite-measure uniqueness and
genuine s-finite kernel products. `ForMathlib/Probability/Kernel/PointwiseFinite.lean`
proves the needed kernel class from finite fibers on a countable cover;
`FiniteVariation/StieltjesKernelVariation.lean` identifies actual kernel mass
with extended whole-halfline variation. `StieltjesExpectation.lean` derives
rectangle means directly from increasing martingale differences, and
`PredictableStieltjesDuality.lean` extends them to every nonnegative predictable
integrand, with IV assumed only for the first process.

`Analysis/PathVariation/StieltjesContinuousCountable.lean` proves zero mass on
countable sets from actual continuity, while `StieltjesStep.lean` identifies
positive unit-step variation with a Dirac measure and zero-time variation
with zero. `Doob/SingleJumpContinuousVersion.lean` repairs the actual III.10
unit-jump compensator to an everywhere-continuous monotone version.
`Stopping/PredictableCountableAvoidance.lean` then proves that a TI stopping
time avoids every predictable set with countable time fibers at positive
finite times. This does not assume a general compensator or self-compensation.

`Measurability/PredictableJumps.lean` constructs a predictable everywhere-good
FV version and proves predictable, countable positive jump support.
`FiniteVariation/PredictableJumps.lean` excludes its TI jumps and combines
the real III.3 decomposition and ordinary jump enumeration through
`Stopping/PredictableJumpCoverage.lean` to construct a predictable countable
cover, even under merely AE cadlag/FV hypotheses. No theorem equating graph
predictability with announcing sequences is presumed. Disjoint graphs and
the expectation of the absolutely summable full bracket jump series are next.

`NaturalExamples.lean` independently proves deterministic positive-step
naturality, actual raw bracket agreement, and a discontinuous natural example.
`PredictableJumpIntegrableMultiplier.lean` weakens the coefficient of one
bounded martingale jump to L1 at a positive AE-finite predictable time;
before-field measurability gives zero conditional mean and expectation.

### Disjoint predictable graphs and legitimate jump-series prerequisites

`Stopping/PredictableComparison.lean` derives exact before-field comparison,
equality and finite-equality events from actual announcing sequences and
initial completeness. `PredictableDisjointGraphs.lean` applies the proved
before-field restriction theorem to remove repeated finite graph points and
then zero-time points, preserving the appropriate graph union exactly.
`FiniteVariation/DisjointPredictableJumps.lean` supplies the actual positive
disjoint countable cover of a predictable cadlag FV process's positive jumps.

`FiniteVariation/IntegrableJumps.lean` bounds every positive jump by actual
variation via its increment limit. Its original zero-terminal stopped jump
is L1 for an IV input, independently of the initial value, and is before-field
measurable for a predictable FV input with AE cadlag paths under usual conditions.
`OptionalSampling/PredictableJumpIntegrableTerminal.lean` extends the UI jump
identity to positive predictable times that may be infinite. True UI optional
sampling and actual terminal convergence give identical terminal values on
both sides, whose difference is zero at infinity. L1 before-field multipliers
therefore retain zero conditional mean and expectation, without a false
measurability transfer to an earlier truncated stopping field.

`ForMathlib/Topology/Algebra/InfiniteSum/LifetimeReindex.lean` provides exact
support-based lifetime reindexing and separate summability/partial-sum bounds.
`Analysis/PathVariation/LifetimeJumpSeries.lean` proves the actual jump-mass
variation bound and the `2 C` global-variation envelope for mixed partial sums.
Only positive times are included and global finiteness precedes real conversion.
These complete the discrete graph and series prerequisites. Their actual
III.14 expectation/terminal consumer is now proved in the following section.

### Predictable naturality, Yoeurp and FV local-martingale constancy (III.14--III.15)

Printed pp113--115 are implemented in
`FiniteVariation/ActualNaturalPredictableExpectation.lean`,
`FiniteVariation/NaturalPredictable.lean`,
`Path/JumpSampling.lean`, `LocalMartingale/PredictableFiniteVariation.lean`
and `Martingale/Doob/PredictableUniqueness.lean`.
The actual positive disjoint predictable jump cover supplies before-field L1
coefficients. True predictable-jump identities make each weighted term mean
zero; exact actual lifetime reindexing and the integrable `2 C` variation
envelope justify dominated convergence to the raw bracket. Its independently
constructed actual terminal and L1 convergence prove full III.14 naturality.
The existing III.12 consequence then gives UI of the actual bounded-test
bracket, the integrable-variation version of Yoeurp's lemma used here.

III.15 instead uses the original masked UI localizing sequence. Actual stopped
jumps are computed, proved integrable locally, and identified with their own
before-field conditional expectations. They vanish at every positive
predictable time, including the explicit zero terminal at infinity. The
constructed predictable FV jump cover gives continuous paths; continuous FV
local-martingale constancy preserves the arbitrary initial value. No IV,
local IV, initial L1 or naturality premise is needed. The difference argument
proves uniqueness of both supplied predictable FV/local-martingale parts and
of predictable FV compensating parts. General III.11/III.16 existence is not
inferred from uniqueness.

Incremental verification: 9702 jobs, 6 clean affected final traces and all
12 checks in `Audit/SemimartingalePredictableNaturalUniquenessAxioms.lean`
using only standard Lean axioms. No full-library build or push was performed.

### Signed compact moduli for the regular III.11 residual

`Martingale/Convergence/StoppingLeftExpectation.lean` proves continuity of
Class D expectations along increasing finite stopping times from zero means
of positive predictable jumps. The actual L1 limit is the final sample minus
the jump at the predictable strict-limit restriction. Its jump is proved L1
before using its mean; the L1 limit is not incorrectly identified with X at
the limiting stopping time.
`Doob/ShiftedConditionalSupermartingale.lean` constructs actual cadlag versions
of `E[X(t+delta)|F_t]` and their valid bounded stopping identities. The future
input is not assumed adapted. `ShiftedConditionalModulusOrder.lean` gives
common-event width comparison and the correct compact supremum comparisons;
the reverse comparison needs horizon `T+delta`.
`ShiftedConditionalSequence.lean` performs a legitimate common initial-null
reset to construct everywhere cadlag, nonnegative and decreasing residuals.
`RegularConditionalModulusOrdered.lean` proves their first-threshold probability
estimate using Class D alone. `ClassD/Bounded.lean` proves the true stopping-family
Class D bridge, and `RegularConditionalModulus.lean` constructs all inputs and
proves full width-to-zero compact convergence in probability for bounded regular
supermartingales. Neither a TI hypothesis nor a candidate residual/convergence
certificate is an input to this source conclusion. General III.11 existence
and the general Class D construction remain open.

### Conditional variation and Protter III.17, easy direction

Printed pp118--119 are represented by `Semimartingale/Quasimartingale.lean`.
The actual finite-partition sum includes the explicit `|X T - 0|` tail; no
evaluation at infinity or implicit actual terminal is used. Whole-halfline
conditional variation is ENNReal-valued, and its finiteness does not replace
adaptedness, common AE cadlag paths or coordinate L1 in `IsQuasimartingale`.
A nonnegative supermartingale has conditional variation exactly its initial
mean; a difference of two such supermartingales has variation at most the sum
of their initial means. The terminal tail is essential for this uniform bound.
Existing right-continuous supermartingale regularity proves the cadlag field
for the source III.17 easy direction under usual conditions.
`Analysis/PathVariation/StrictPartition.lean` constructs strict representatives
within the same `TimePartition` owner. The downstream
`Semimartingale/Quasimartingale/StrictPartition.lean` reuses actual cell-sum
endpoint invariance to prove exact equality of the sums and of the strict-source
supremum. The zero-horizon representative is the existing empty partition,
and its terminal tail remains `|X 0|`. III.17's converse and Rao are not proved.

Incremental verification: 9712 jobs, 11 clean affected final traces and all
35 checks in `Audit/SemimartingaleRegularConditionalModulusAxioms.lean` using
only standard Lean axioms. No full-library build or push was performed.

### Actual bracket integrable variation (prerequisites for Protter III.12--III.14)

`Analysis/PathVariation/StieltjesIntegralVariation.lean` proves the actual
primitive increment identity and quantitative compact/global variation bounds.
Only positive-time integrand values need be bounded: the initial term cancels
in increments. The global bound retains extended variation, including infinity.
`QuadraticCovariation/IntegrableVariation.lean` identifies the sole actual raw
bracket with a Stieltjes integral supported on the FV integrator's countable
jump set, plus its raw initial product. This gives total variation at most
`ofReal (2*C) * eVariationOn A univ` when the other semimartingale is bounded
by C. Integrable variation follows; with integrable A0, the existing actual
terminal construction gives all-time AE/L1 convergence and Class D. No
martingale property is needed for this analytic statement, and no bracket
martingality, zero expectation or naturality is concluded from it alone.

`OptionalSampling/PredictableJumpMultiplier.lean` first proves integrability
of the actual weighted jump, then uses native conditional-expectation pull-out
to prove conditional mean and expectation zero. Its predictable-process
consumer only needs bounded sampled values, but its lifetime remains positive
and deterministically bounded. Predictable jump exhaustion and the whole-series
argument of Yoeurp remain open.

### Bounded regular Doob construction, single jumps and partition refinement

`Doob/RegularGlobalConditionalModulus.lean` constructs the actual terminal
potential internally and controls the late-time tail. Compact regular
modulus convergence then gives full-halfline probability and L2 convergence.
The existing dyadic terminal-energy, L2, UCP and martingale-closing proofs
now accept an actual convergent global modulus as an intermediate interface;
their original TI source signatures are retained. The source consumer in
`RegularContinuousBounded.lean` constructs this modulus from zero means of
positive predictable jumps, without a compensator, terminal or convergence input.
Its actual continuous increasing part starts at zero; X's initial value is unrestricted.

`Stopping/TerminalRestriction.lean` and `Doob/RegularStopping.lean` retain
the closed stopping endpoint and explicit zero at infinite lifetime, proving
that arbitrary stopping preserves the predictable jump-mean condition.
`Stopping/PredictableAfterCoefficient.lean` proves predictability of the
actual closed future, graph and before-measurable coefficient step under
initial completeness. `Doob/CenteredSingleJump.lean` proves UI martingality
of the actual before-centered L1 jump, even at an arbitrary stopping time.
`FiniteVariation/SingleJump.lean` computes actual global variation, with zero
variation at zero and infinite lifetimes. `Doob/PredictableSingleJump.lean`
combines these into an actual predictable L1-variation compensator, whose
expected variation is at most E norm Z. No coefficient is assumed zero at infinity.

`Analysis/PathVariation/RefinementSums.lean` proves the generic subadditive
cell-sum refinement inequality on the existing partition owner. Its
`Quasimartingale/Refinement.lean` consumer proves initial-conditional positive,
negative and absolute variation monotonicity, real expectation monotonicity
and the extended-variation inequality. Repeated endpoints and terminal-zero
tails are retained; unconditioned random sums are not claimed pointwise ordered.
General regular Class D existence, III.11/III.16 existence and Rao remain open.

Incremental verification: 9722 jobs, 16 clean affected traces and all 35 checks
in `Audit/SemimartingaleRegularBoundedSingleJumpAxioms.lean` using only standard
Lean axioms, including the six preserved TI wrappers. No full build or push.

### Regular bounded-jump Class D, general single jumps and directed envelopes

`Doob/ContinuousLocalization.lean` now exposes stopped consistency without a TI
hypothesis; its original TI source wrapper is preserved. The actual norm-exit
construction in `RegularContinuousLocalization.lean` and the generic Class D
patching theorem yield `RegularContinuousBoundedJumps.lean`: a continuous
increasing predictable part, true UI martingale and actual integrable terminal
from bounded positive jumps, not bounded values. The general unbounded-jump
regular Class D case and full III.11 existence are not claimed here.

`Stopping/CoefficientOnGraph.lean` and `Doob/AccessibleCoefficients.lean`
construct a disjoint predictable decomposition of a stopped-measurable L1
coefficient. `Path/LifetimeStepSeries.lean` proves actual whole-halfline
uniform convergence, cadlag paths and the total-variation bound.
`ForMathlib/MeasureTheory/Function/SummableNorm.lean` proves the actual
Tonelli norm-series integrability and almost-sure summability before real
conversion. `FiniteVariation/PredictableStepSeries.lean` supplies exact
predictability, IV, expected variation and zero-initial series results.
`Doob/CenteredStepSeries.lean` proves true UI closure and constructs the
before-centered coefficient series. `AccessibleSingleJump.lean` uses it
to construct the accessible single-jump compensator. The signed TI theorem
in `TotallyInaccessibleSingleJump.lean` constructs a continuous IV part.
`SingleJumpCompensator.lean` combines the actual classification components,
masking both coefficients on disjoint events to retain E variation <= E norm D.
`RegularConditionalJump.lean` derives zero before-conditional jump means from
positive predictable tests, only after actual sampled-jump integrability.

`ForMathlib/MeasureTheory/Function/EssentialFamilyDirected.lean` bounds actual
directed essential suprema and proves finiteness/L1 from a finite integral
bound. `Quasimartingale/PartitionEnvelope.lean` constructs fixed-horizon
positive/negative envelopes on the original measure. Exact partition
extension/prepending in `Analysis/PathVariation/HorizonExtension.lean`
feeds `Quasimartingale/HorizonComparison.lean`: adapted horizon comparison,
all-horizon directedness, and the original extended conditional-variation
bound under time shift. No Rao decomposition or future martingale is assumed.

Incremental verification: 9738 jobs, 18 clean affected traces and 35
standard-axiom-only checks in `Audit/SemimartingaleRegularClassDSingleJumpAxioms.lean`,
including the preserved TI localization wrapper. No full build or push.

### Stationary future laws at finite stopping times — checkpoint 2026-09-12 (historical)

`StationaryIndependentIncrements/FiniteFutureLaw.lean` derives actual finite
future-vector stationarity from sorted adjacent increments, native joint
independence and telescoping. The reference subtracts the original initial
value and permits repeated/zero lags. No extra probability, coordinate
measurability or path hypothesis is added to this deterministic law theorem.
`IndependentIncrements/FiniteFutureFiltration.lean` includes the actual past
field in the ordered independent family, then separates it from the entire
future vector. Coordinatewise independence is not substituted for joint
independence.

`StationaryIndependentIncrements/CountableStopping.lean` proves the stopped
conditional identity for bounded measurable single-increment tests.
`Stopping/ConditionalFiniteSampling.lean` uses actual upper grids and
dominated conditional convergence to sample constant conditional projections
at arbitrary genuinely finite stopping times, with coordinate measurability
and a common integrable envelope but without joint measurability or a
deterministic stopping bound.
`StationaryIndependentIncrements/FiniteStopping.lean` and
`StationaryIndependentIncrements/FiniteFutureStopping.lean` give the single
and finite-vector consumers, including actual sampled-vector AE measurability
and true image-law equality. The specified-past independence is essential;
no arbitrary initial-information enlargement is allowed.

`Path/ShrinkingSupremum.lean` proves that the original centered countable
supremum tends to zero along any shrinking initial-window filter. Under
finite measure, strict positive-threshold exceedance measures vanish for
arbitrary shrinking sequences, with no monotonicity or moment condition.

Verification: 10027 incremental jobs, 8 affected / 8 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleSIIStoppingAxioms.lean`.
This is the user-requested publication/pause checkpoint, not package completion.
The stopped-window and announcing-jump consumers were unverified local drafts
and were excluded from that checkpoint. They are verified by the next entry.
No full build.

### Cadlag real-SII predictable jumps and natural-usual total inaccessibility

`StationaryIndependentIncrements/StoppingWindow.lean` turns the proved finite
future-vector law into an equality of actual dense post-stopping running-
supremum tails. Together with the initial shrinking-supremum theorem it supplies
uniform small-window tails after every genuinely finite stopping time.
`Stopping/SmallWindowSampling.lean` converts such tails into convergence in
measure of sampled increments, using only AE ordering and actual finite-time
convergence of the sampling clocks.

`Stopping/AnnouncingJumpLimit.lean` caps genuine predictable announcing times
without evaluating the process at infinity and identifies the AE limit with
zero at a zero target and the real positive-time jump otherwise.
`Stopping/FiniteSampleMeasurability.lean` proves measurable countable-range
sampling and AE-measurable arbitrary finite sampling for coordinate-measurable
right-continuous processes. `StationaryIncrementsCompletion.lean` preserves the
actual increment laws under measure completion.

`StationaryIndependentIncrements/TotallyInaccessibleJumps.lean` uses uniqueness
of limits in measure to make every finite predictable positive-time jump zero,
then integer truncation and the established predictable-test bridge to obtain
the sole `HasTotallyInaccessibleJumps` predicate. Its final consumer applies to
the unchanged measurable, AE-zero-initial cadlag real SII process in the genuine
completed usual augmentation of its own natural filtration. No moments, Markov
or Feller certificate, arbitrary enlarged filtration or alternate realization
is assumed.

This closes the general cadlag real-SII TI theorem, not construction of a cadlag
canonical Levy realization, Protter I.4 Levy decomposition, or Meyer's general
strong-Markov/Feller theorem.

Verification: 10033 incremental jobs, 7 clean production rebuilds and 11
standard-axiom-only checks in
`Audit/SemimartingaleSIIInaccessibleAxioms.lean`. No full build or push.

### Canonical terminal density and cadlag density process

`Semimartingale/MeasureChange/DensityProcess.lean` owns the terminal real
Radon--Nikodym density and proves its measurable/nonnegative/integrable
properties, total integral one and exact set-integral representation under
`Q ≪ P`.

Its `densityProcess` is the existing dyadic right-limit regularization of the
terminal density's conditional-expectation martingale. Under usual conditions
it agrees AE at every time with that conditional expectation, is a true
uniformly integrable martingale with common-event cadlag paths, and is
simultaneously nonnegative on one full-measure event. Integrating at time `t`
over an `F_t` event gives the actual real `Q` mass.

This owner deliberately does not assert `Z_0 = 1` without the corresponding
initial-field hypothesis, pointwise strict positivity, inverse density,
Girsanov correction, stochastic-exponential identification or BD. Those remain
separate Protter III.8--III.9 entries.

Verification: 10034 incremental jobs, 2 clean production rebuilds and 13
standard-axiom-only checks in
`Audit/SemimartingaleDensityProcessAxioms.lean`. No full build or push.

### Fixed-time strict positivity of density processes

`Semimartingale/MeasureChange/EquivalentDensity.lean` uses Mathlib's trimmed
RN derivative/conditional-expectation identification to prove the natural
one-way statement: if `Q ≪ P`, then `densityProcess Q P F t` is strictly
positive `Q`-almost surely for every fixed `t`. Under equivalence the terminal
and fixed-time densities are also strictly positive `P`-almost surely. A
general integrable-real conditional-expectation positivity lemma supplies the
source-measure route.

These declarations do not take an uncountable intersection over time and do
not define an inverse density, stopping-time localizer or Girsanov correction.

Verification: 10035 incremental jobs, 2 clean production rebuilds and 6
standard-axiom-only checks in
`Audit/SemimartingaleEquivalentDensityAxioms.lean`. No full build. The GitHub
push retry did not reach GitHub because port 443 was unavailable.

### Fixed-time reciprocal densities and Bayes formulas

`Semimartingale/MeasureChange/ReciprocalBayes.lean` proves the reciprocal
identity between the two trimmed conditional-expectation density processes at
each deterministic time under equivalent laws. It also proves the one-way
multiplication form of Bayes' formula from RN set integrals and conditional
expectation uniqueness, followed by quotient forms only on the AE domains where
strict positivity is available.

The module does not upgrade coordinatewise equalities to indistinguishability,
sample at stopping times or state a Girsanov correction.

Verification: 10036 incremental jobs, 2 clean production rebuilds and 5
standard-axiom-only checks in
`Audit/SemimartingaleReciprocalBayesAxioms.lean`. No full build or push.

### Common-event reciprocal density paths

`Semimartingale/MeasureChange/PathwiseReciprocal.lean` combines both canonical
càdlàg density processes under equivalence. Their fixed-time product-one
modification is promoted by right-continuous uniqueness to a process-level
indistinguishable identity. This gives all-time strict positivity on one common
event and identifies the pointwise inverse with the reverse density process,
hence supplies its càdlàg version.

No stopping-time evaluation or Girsanov decomposition is encoded here.

Verification: 10037 incremental jobs, 2 clean production rebuilds and 5
standard-axiom-only checks in
`Audit/SemimartingalePathwiseReciprocalAxioms.lean`. No full build or push.

### Density processes at finite stopping times

`Semimartingale/MeasureChange/StoppingDensity.lean` invokes the established
continuous-time closing-variable optional-sampling owner to identify the
canonical density at every everywhere-finite stopping time with the terminal
RN density conditioned on `F_T`. Exact event integrals recover `Q` on `F_T`.
Trimmed RN positivity gives the one-way `Q`-AE sample theorem; equivalence adds
the `P`-AE and reciprocal-sample conclusions.

This module does not yet construct the inverse/left-limit localizers used in a
Girsanov stochastic-integral proof.

Verification: 10038 incremental jobs, 2 clean production rebuilds and 7
standard-axiom-only checks in
`Audit/SemimartingaleStoppingDensityAxioms.lean`. No full build or push.

### Equivalent-density localization and left limits

`Semimartingale/MeasureChange/EquivalentDensityLocalization.lean` combines the
existing capped norm exits for the forward and reverse canonical density
processes. The minimum is localizing under both equivalent measures and bounds
both processes before exit. Left-limit multiplication applied to the pathwise
product-one identity gives positive-time strict positivity and the exact
reciprocal left limit, with both sides bounded up to the joint localizer.

This is the bounded `1 / Z₋` foundation for a later Girsanov proof, not the
Girsanov theorem itself.

Verification: 10039 incremental jobs, 2 clean production rebuilds and 9
standard-axiom-only checks in
`Audit/SemimartingaleEquivalentDensityLocalizationAxioms.lean`. No full build or push.

### Equivalent-law true and UI martingale transfer

`Semimartingale/MeasureChange/MartingaleTransfer.lean` owns the equivalent-law
change-of-measure theorem for true martingales: the target-law martingale `X`
is sent to the source-law martingale `Z * X`. Its UI refinement uses an actual
integrable closing variable multiplied by the terminal RN density. Its local
refinement retains the original masked fundamental sequence and stops the
transferred UI processes once more at the same times. The module
depends on the project's conditional Bayes and RN-integrability interfaces;
it does not import or wrap an external stochastic-process package.

Verification: 10040 incremental jobs, 2 clean production rebuilds and 3
standard-axiom-only checks in
`Audit/SemimartingaleMartingaleTransferAxioms.lean`. No full build or push.

### Equivalent-measure raw Girsanov--Meyer (Protter III.39)

`Semimartingale/MeasureChange/GirsanovMeyer.lean` owns `[Z,M]`, the reverse-law
auxiliary stochastic integral, the division-free correction and its explicit
right-integral expansion. It proves the expansion is the pathwise right-value
Stieltjes integral on the native common event, retains the raw bracket's true
initial product, and proves the corrected process is a local martingale under
the target law.

The implementation is internal and uses only the project's raw bracket,
stochastic-integral invariance and equivalent-density APIs. Predictable III.40
and the one-way zero-density work of III.41--III.42 remain separate owners.

Verification: 10041 incremental jobs, 2 clean production rebuilds and 11
standard-axiom-only checks in
`Audit/SemimartingaleGirsanovMeyerAxioms.lean`. No full build or push.

### Predictable Girsanov correction (Protter III.40)

`Semimartingale/MeasureChange/PredictableGirsanov.lean` owns the canonical
density predictable covariation and its equivalent-law correction. It proves
the reverse density left limit is the literal reciprocal of the forward left
limit at all positive times on a target-full-measure event, proves the
correction starts at zero, and obtains the target local martingale through the
right-value correction and its canonical predictable compensator.

Only the project's internal predictable bracket, right-integral compensation
and measure-change infrastructure are used. The one-way density localization
and zero-density jump of III.41--III.42 remain separate modules.

Verification: 10042 incremental jobs, 2 clean production rebuilds and 8
standard-axiom-only checks in
`Audit/SemimartingalePredictableGirsanovAxioms.lean`. No full build or push.

### Genuine natural Poisson filtration and total inaccessibility

`Independence/FamilyCompletion.lean` preserves native full joint independence
under genuine completion, for arbitrary indices, dependent targets and source
measure. `Poisson/Completion.lean` retains the original process, joint increment
independence, exact increment laws and common path events on that completion.
`Poisson/RealIndependentIncrements.lean` transports the true natural-number
increments to actual real differences using the original AE monotonicity.

`IndependentIncrements/NaturalFiltration.lean` proves that a measurable real
process with native independent increments and AE zero initial value has
future increments independent of its entire original natural past. Sorted
finite grids, actual telescoping sums and joint independence give every finite
past vector; the native cylinder theorem gives the whole past sigma-algebra.
No path regularity or assumed past-independence certificate is needed.
`Filtration/NaturalNatCast.lean` identifies the exact raw natural filtrations
of a measurable count and its real cast, using measurable casting and its
actual natural-floor inverse, with any preordered time and no measure.

`Poisson/NaturalFiltration.lean` derives original and usual-augmented past
independence, then proves TI jumps and TI original hitting arrivals in the
genuine usual natural filtration. The same sample process and original
arrival clocks are retained. Original coordinate measurability is explicit;
rate zero and infinite arrivals are permitted. This closes the natural
Poisson jump-classification bridge, not general Levy/Feller realization or
Meyer's general strong-Markov theorem.

Verification: 10020 incremental jobs, 7 affected / 7 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleNaturalPoissonAxioms.lean`.
No full build or push.

### Nonnegative jump classification and actual Poisson arrivals

`LocalMartingale/NonnegativePredictableJump.lean` proves that the actual
positive-time jump at every predictable testing lifetime is zero for a
native local martingale with nonnegative jumps. The original masked UI
fundamental sequence supplies real jump L1 and zero conditional mean;
nonnegativity and integral zero force localized jumps to vanish. Actual
localizers tending to infinity recover the original jump. Zero-time tests
are restricted away, while infinite samples retain explicit terminal zero.

`Stopping/TotallyInaccessibleJumpTests.lean` proves the converse from
predictable zero tests to the existing countable HasTI predicate for any
adapted cadlag process under usual conditions, with arbitrary source measure.
Actual large-jump sequences of an indistinguishable everywhere-cadlag version
give real stopping times and true finite nonzero jump graphs. Each test has
its own AE event; only the actual countable covering is combined.
`LocalMartingale/TotallyInaccessibleJumps.lean` closes native LM classification
and its continuous-subtraction consumer. The source initial jump is excluded.

`FiniteVariation/ContinuousCompensatorClassification.lean` gives the full
HasTI/continuous-sole-compensator equivalence on the proved local-IV domain
with nonnegative positive-time jumps. No monotone-path or initial-moment
assumption is introduced; arbitrary continuous signed movement is allowed.
`Counting/ArrivalJumpGraph.lean` proves on one event that every finite original
hitting arrival is a positive unit jump, using its true arrival count and
strict-before left-limit bound.
`Poisson/TotallyInaccessibleJumps.lean` combines the actual compensated
Poisson martingale, continuous linear drift and original unit-jump graphs
to classify both all jumps and each original hitting arrival. Future
increments must be independent of the specified past. Rate zero and
infinite arrival tails are permitted; in particular no assertion that such
times are not accessible is made. The natural-filtration independence
bridge and general Meyer/Feller or Levy classification remain separate.

Verification: 10014 incremental jobs, 7 affected / 8 rebuilt clean traces,
8 standard-axiom-only checks in `Audit/SemimartingalePoissonClassificationAxioms.lean`.
No full build or push.

### Actual crude-rate compensation and the positive-risk net-rate corollary

Protter's dependent-censoring example on printed page 124 is now connected
from actual window probabilities to the sole canonical compensator.
`ForMathlib/MeasureTheory/Measure/RNDensityVanishing.lean` proves vanishing
infimum of native RN densities from vanishing infimum mass under an arbitrary
reference measure. `RightWindowVanishing.lean` combines this with a countable
common event of actual finite-AC window derivatives; no monotonicity of chosen
RN representatives or target-limit input is required.

`Counting/CensoringThinWindowMeasure.lean` constructs genuine decreasing
restricted pushforwards of the thin censoring regions, proves their mass
infimum zero and bounds the actual wedge event. `CensoringWedgeRate.lean`
deduces that the original wedge probability divided by width tends to zero
almost everywhere. `LifetimeRealWindow.lean` first rules out the infinite
atom from actual full-real-law AC, then identifies actual real and extended
finite Ico windows. `CensoredCrudeRate.lean` combines these with the exact
cause-plus-wedge identity, keeping finite guards on real measure arithmetic.

`LifetimeRealDensity.lean` constructs one native measurable nonnegative
real RN density for all original restrict-before-map positive caps.
`CensoredDensity.lean` expresses the stopped cause primitive with the true
joint-survival denominator; `CensoredRNDensity.lean` derives all its density
hypotheses directly from the original arrival-real law's AC.
`CensoredCrudeCompensator.lean` defines the actual crude filter limit, proves
its a.e. RN identity, identifies every stopped primitive and the sole
compensator, and proves the original censored-count remainder locally
martingale in the genuine usual observed-pair natural filtration.
`NetRateCensoring.lean` defines the actual net rate and proves the net-rate
remainder locally martingale when net equals crude a.e. on positive joint
survival only. A common positive observation-survival event justifies that
precise domain for every stopped integration interval.

The full-real-law AC hypothesis excludes original arrival atoms, including
at infinity; the earlier general measure formulas retain those cases.
Censoring may have atoms or depend on arrival, and ties belong to arrivals.
Rates at zero survival and outside their proved convergence event are
totalizations, not conditional probabilities or pointwise limit assertions.
No independent-censoring rate identity is silently assumed or claimed.

Verification: 10008 incremental jobs, 12 affected / 12 rebuilt clean traces,
19 standard-axiom-only checks in `Audit/SemimartingaleCrudeCensoringAxioms.lean`.
No full build or push.

### Actual marked and censored compensation; exact crude windows

`Counting/MarkedSingleJumpHazardMartingale.lean` proves predictability of the
actual stopped cause hazard under any measure and its true compensated
marked-count martingale under a finite measure. Actual law integrals pull
back without injectivity; the marked increment has exactly the cause mass.
Survival traces and frozen post-observation increments prove all conditional
testing identities without initially revealing the mark.
`MarkedSingleJumpCompensator.lean` constructs the original marked count's
bounded-jump global-IV domain and uses actual paths, raw right continuity,
genuine usual augmentation and full uniqueness to identify its sole compensator.
`CensoredCompensator.lean` specializes this to the minimum observation with
ties assigned to arrivals. The numerator measure is the actual original
arrival law restricted to arrival before or at censoring; independence,
finite lifetimes and densities are not required for this measure formula.

`CauseSpecificHazardDensity.lean` proves the extended density identity and
actual real interval integrability, keeping cause density and observation
survival in their distinct roles. `MarkedSingleJumpDensity.lean` identifies
the all-time original stopped hazard and the sole marked compensator with
that literal integral on a common event.
`CauseSpecificHazardUniformIntegrability.lean` obtains an actual integrable
integer-supremum envelope from the true finite cause mass, yielding whole-
halfline UI under a finite observation law, not merely coordinate L1.

`CensoringWindow.lean` identifies observation survival with joint survival,
and decomposes crude arrival windows into disjoint cause windows and paths
censored strictly before arrival within the window. The latter term is
retained. `ForMathlib/MeasureTheory/Measure/RightWindowDerivative.lean` uses
native RN integrability and Lebesgue differentiation to identify a finite
absolutely continuous law's right-window rate almost everywhere. Neither
this theorem nor the event decomposition alone removes the censoring term;
the remaining a.e. crude-rate proof is still open.

Verification: 9997 incremental jobs, 9 affected / 9 rebuilt clean traces,
13 standard-axiom-only checks in `Audit/SemimartingaleMarkedCompensationAxioms.lean`.
No full build or push.

### Literal density compensation and cause-hazard / marked-information foundations

`Counting/HazardDensity.lean` changes variables in the actual lifetime law
restricted before the finite-coordinate map. The genuine density gives the
extended hazard integral; a positive-survival cap then proves finiteness,
actual quotient integrability and the real interval integral identity.
`GeneralLifetimeHazardDensity.lean` uses positive survival at the observed
lifetime on one common event to identify the stopped hazard at every time
and the original-space sole compensator with that literal integral. Neither
initial atoms nor mass at infinity is dropped from the original denominator.

`CauseSpecificHazard.lean` defines the distinct cause integral against an
actual dominated submeasure with observation-law closed survival. It recovers
the existing ordinary hazard when all causes are selected, and has measurable
monotone time dependence, genuine domination, finite-cap bounds and the exact
stopped integral. `CauseSpecificHazardBalance.lean` uses Tonelli with the
observation and cause measures in their correct roles; true domination transfers
positive survival to almost every cause time. Extended mean, L1 and the strict
survival increment balance are proved without a deterministic survival guard.
`CauseSpecificHazardPaths.lean` proves finite-cap right continuity by dominated
convergence and actual common-event all-time finite, monotone cadlag stopped
paths, including infinite observations.

`MarkedSingleJumpInformation.lean` proves coordinate measurability, trivial
strict-survival traces and stopping for the literal observed pair of causes.
`MarkedSingleJumpRightContinuous.lean` freezes the actual observed history
after occurrence and uses a common later time for two surviving paths to prove
the genuine raw natural filtration right-continuous. The mark is not initially
revealed. No measure or lifetime-positivity/finiteness assumption is required.
The marked martingale and full censored compensator remain separate work.

Verification: 9989 incremental jobs, 8 affected / 8 rebuilt clean traces,
22 standard-axiom-only checks in `Audit/SemimartingaleDensityCauseAxioms.lean`.
No full build or push.

### General AE-count compensation and hazard-rate / censoring foundations

`Counting/NaturalCompensatorDomain.lean` constructs the original count's
adapted, cadlag, locally integrable variation domain in its genuine usual
natural augmentation from the actual AE count predicate and coordinate
measurability. No expected-count bound or everywhere-valid path input is needed.
`GeneralCountHazard.lean` constructs an actual arrival representative in a
supplied usual source filtration, transports canonical compensation across
equal usual natural filtrations, and identifies the original count's sole
compensator with the original-measure conditional-gap completed-plus-pending
formula. The original count is its index; the source filtration is not used
as an unjustified information enlargement in the conclusion.

`HazardRateLimit.lean` proves the actual conditional right-window mass per
unit width tends to density over positive closed survival. Genuine density
and finite law mass first establish L1; the native fundamental theorem of
calculus gives the limit. No derivative or desired limit certificate is input.
`CensoringLaw.lean` identifies arrival-marked minimum observations with
restricted arrival laws and proves domination by both original marginal laws.
Ties belong to arrivals; arbitrary measures and infinite lifetimes are allowed.
The explicit density primitive and full marked censored compensation remain
separate, open applications.

Verification: 9982 incremental jobs, 5 affected / 5 rebuilt clean traces,
5 standard-axiom-only checks in `Audit/SemimartingaleGeneralCountAxioms.lean`.
No full build or push.

### Independent arrival compensation and genuine natural-information transport

`Counting/ArrivalConditionalIndependent.lean` derives independence of the next
latent duration and its actual prefix arrival history using disjoint finite
coordinate vectors and a measurable prefix map. On the finite preceding-
prefix history event, the actual absorbing gap's conditional law equals the
original latent marginal. Positivity and nonexplosion are not needed for
this conditional-law identity.

`IndependentArrivalHazard.lean` builds the actual count and its compensation
domain from positive independent durations and diverging extended prefixes.
Activation at a finite stopped clock forces finite past, so the original
conditional kernel may legally be replaced by its marginal on one common
event for every stage and time. Infinite previous arrivals never activate.

`ArrivalPrefixHazardInterval.lean` is pure completed-plus-pending algebra
in the latent durations; completed stages have finite past before gap
cancellation. `IndependentArrivalHazardInterval.lean` gives the actual sole
compensator's corrected finite marginal-hazard formula. It includes the
initial interval and all completed terms, correcting the printed III.23
corollary's omitted interval and shifted completed-sum index.

`Filtration/NaturalIndistinguishable.lean` identifies genuine usual natural
augmentations for indistinguishable processes in a metrizable Borel state
space, under any measure. Raw natural filtrations are not asserted equal.
`Counting/ArrivalCountVersion.lean` constructs an everywhere-valid arrival
representative of an actual adapted nonexplosive count in a usual filtration,
with an indistinguishable guarded count and all original hit times on one
event. General-count canonical compensation transport remains a separate
consumer; neither representation nor information equality alone identifies it.

Verification: 9978 incremental jobs, 7 affected / 7 rebuilt clean traces,
6 standard-axiom-only checks in `Audit/SemimartingaleIndependentArrivalAxioms.lean`.
No full build or push.

### Canonical arrival compensation and completed-plus-pending formulas

`Counting/ArrivalHazardLocalization.lean` turns the actual positive arrivals
into reducing times for the original compensated count in genuine usual
augmentation. Finite raw UI martingale prefixes transfer through the proved
right-continuous natural filtration, then are stopped at the original arrival.
The exact stopped-prefix identity supplies a genuine localizing witness;
no conditional law is recomputed under completion.

`ArrivalHazardCompensator.lean` constructs the actual count's local
integrable-variation domain on the completed space and uses full canonical
compensator uniqueness. `ArrivalHazardGapHistory.lean` replaces arrival history
by actual absorbing gap history on one event of measure-valued equality for
all countably many stages, and hence at all times for the entire series.

`ArrivalHazardInterval.lean` is pure path algebra for arbitrary sample-dependent
measures: completed stages evaluate the complete actual gap, and the current
stage evaluates elapsed time. The true series equals completed terms plus
exactly one pending term, including count zero and arrival endpoints.
`ArrivalHazardCompensatorInterval.lean` gives this finite formula for the sole
canonical compensator using the original actual-gap conditional kernels.
These prove the conditional III.23 formula on the everywhere-valid arrival
domain. Independent specialization and transport from merely AE-valid arrival
representatives remain separate entry-point work.

`ForMathlib/Probability/Kernel/CondDistribOnHistoryEvent.lean` proves equality
of actual conditional measures on a history event from equality of variables
there, using restricted joint laws and native kernel uniqueness.
`CondDistribIndependent.lean` identifies an independent variable's conditional
kernel with its true marginal law. `Counting/ArrivalPrefixDurations.lean`
constructs actual extended arrivals from positive diverging latent prefixes
and recovers a latent gap only when its preceding prefix is finite. Absorbing
gaps are not silently declared independent after an infinite arrival.

Verification: 9972 incremental jobs, 9 affected / 9 rebuilt clean traces,
11 standard-axiom-only checks in `Audit/SemimartingaleArrivalCompensationAxioms.lean`.
No full build or push.

### Actual compensated arrival stages and the locally finite hazard sum

`Counting/ArrivalHazardMartingale.lean` proves a true globally UI martingale
for each original arrival indicator minus its actual delayed conditional
gap hazard, in the raw natural count filtration. History is used only at
the preceding arrival. Before the indexed arrival, exact natural-event
traces reduce the testing integral to the conditional clock theorem; after
it the stage has stopped. No initial-history or martingale certificate is
assumed.

`ArrivalCountSum.lean` obtains the original finite-support indicator series
from native hitting-time recovery and caps the stopped count at index plus
one. `ArrivalLocalizing.lean` makes the original strictly positive arrivals
a native localizing sequence for any measure. Infinite tails remain actual
infinite lifetimes, never values at infinite calendar time.

`DelayedHazardSupport.lean` proves zero through the birth endpoint and beyond
the horizon count. `ArrivalHazardPaths.lean` gives exact predictability,
zero initial value and common-event monotone cadlag paths for each actual
stage. `Path/LocallyFiniteSeries.lean` derives genuine summability and local
uniform convergence from compact finite support; monotone cadlag summands
then give a monotone cadlag actual sum.

`ArrivalHazardSum.lean` uses these results and native measurable series to
prove the properties of the actual conditional-hazard sum. Its prefix runs
through the current pending stage. `ArrivalStoppedSum.lean` proves the exact
stopped compensated prefix: the next stage is zero at its birth endpoint.
This algebra needs no measure, measurability, or prior stopping property of
the summands. The total local-martingale proof in genuine usual augmentation,
canonical compensation identification and independent specialization remain
separate III.23 gates.

Verification: 9964 incremental jobs, 9 affected / 9 rebuilt clean traces,
11 standard-axiom-only checks in `Audit/SemimartingaleArrivalSumAxioms.lean`.
No full build or push.

### Safe arrival clocks and equality of actual conditional history laws

`ForMathlib/Probability/Kernel/CondDistribInformation.lean` proves that
histories generating the same sigma field give equal evaluated native
conditional distributions on one common event. Setwise conditional
expectations give finite-mass equalities; actual product-measure
extensionality and native kernel uniqueness give equality of measures.
Only the target needs standard Borel structure. `Counting/ConditionalArrivalInformation.lean`
applies this to genuine finite arrival/gap histories, including empty history
and absorbing infinite gaps; it does not identify arbitrary kernel labels.

`ArrivalGapClock.lean` uses the actual safe age t minus the finite minimum
of t and the preceding arrival. It proves joint measurability, time
monotonicity and the calendar bound. Original closed arrival events equal
actual positive-gap events at that age, and the stopped delayed kernel hazard
equals the gap-stopped hazard at the same age. Before an unoccurred or
infinite starting arrival the age is zero; no infinite calendar value is
interpreted as a real time.

`ConditionalHazardClock.lean` pulls clock-family UI and the history/survival
zero-increment integral to the original space through the actual native
conditional joint law. It uses a genuine integrable indicator and the
noninjective measurable-map integral theorem. `Path/CadlagTimeChange.lean`
proves that continuous monotone clocks preserve cadlag regularity of
monotone right-continuous real paths. `ConditionalHazardPathClock.lean`
applies this on the original single full-measure event, retaining all-time
extended finiteness and monotonicity. Path properties alone need no
measurability assumption on the starting lifetime.

The full natural-filtration compensated arrival segments and their
localized sum are not supplied by these clock identities alone; III.23
and the other remaining package gates are still open.

Verification: 9956 incremental jobs, 7 affected / 7 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleArrivalClockAxioms.lean`.
No full build or push.

### Natural-count right continuity and actual history activation

`Counting/ArrivalRightContinuous.lean` proves raw natural-filtration right
continuity for the actual everywhere-valid nonexplosive count. Each future
event is evaluated on observations frozen at the present; the actual
no-jump window gives eventual pointwise equality, and countable set operations
recover the event. No intersection/comap exchange or generic cadlag-filtration
claim is used. `ArrivalStoppingInformation.lean` proves the original arrivals
are stopping times and each genuine finite history is measurable at its
preceding arrival, including the empty initial history and infinite times.
`ArrivalHistoryEquivalence.lean` proves exact equality of the sigma fields
generated by actual arrival and absorbing-gap histories via difference and
prefix-sum factorization. This is not an ambient vector-space isomorphism or
pointwise identification of conditional kernels.

`ConditionalLifetimeHazard.lean` uses native `condDistrib` and its genuine
joint-law identity. The original-space stopped hazard has its exact real
mean, global UI and common-event finite monotone cadlag paths. No standard
Borel hypothesis is added to the original sample or history space, and no
history is assumed initially known.

`Stopping/DelayedPredictable.lean` proves actual stopped-field information
is predictably available strictly after its stopping time. Zero initial
value then gives predictable closed activation of a Borel age/mark function.
`Counting/DelayedKernelHazard.lean` applies this to the original kernel hazard,
stops at the actual calendar time and proves its exact absorbing-gap
representation. Infinite and coincident calendar times are retained; the
elapsed gap is not asserted to be a calendar stopping time.

`KernelHazardClock.lean` proves integrability at bounded measurable joint
clocks, the zero survival-increment integral at ordered bounded history
clocks using genuine Fubini and the existing fiber martingale, and global UI
for clocks bounded by their calendar index. It makes no optional-sampling
claim about arbitrary clocks. These identities and activation bridges do
not yet prove the full natural-count compensated segments or their localized
sum, so III.23 remains open.

Verification: 9950 incremental jobs, 8 affected / 8 rebuilt clean traces,
13 standard-axiom-only checks in `Audit/SemimartingaleActivatedHistoryAxioms.lean`.
No full build or push.

### Actual kernel hazards and finite arrival histories (III.23 prerequisites)

`Counting/KernelHazard.lean` proves joint measurability of the existing
extended hazard and its actual stopped expectation under the native
history/lifetime composition product. The closed-survival denominator keeps
endpoint atoms. `KernelHazardPaths.lean` first proves a jointly measurable
full-measure positive-survival event; the same pointwise path theorem in
`HazardPathRegularity.lean` then gives all-time finiteness, monotonicity and
cadlag regularity on one event. No arbitrary fiber path event is presumed
jointly measurable, and no coordinatewise AE statement is exchanged with
an uncountable time quantifier.

`KernelHazardUniformIntegrability.lean` converts to real values only after
actual extended expectation finiteness. It proves the exact real mean and
global UI by a genuine integrable integer-supremum envelope, not by a mere
uniform first-moment bound. No kernel martingale or predictability result
is assumed or concluded.

`ArrivalInformation.lean` uses the actual raw natural-count filtration:
before arrival n, its events are restrictions of measurable events in the
first n arrival coordinates. The empty initial history is included.
`ArrivalInterarrival.lean` defines actual positive gaps with absorbing
infinity after an infinite previous arrival, proves their measurability,
and recovers every original arrival by its exact prefix sum. These gaps
are not claimed to be independent latent generating durations.

Actual conditional-distribution transport, history-activated predictable
segments, their natural-filtration martingale identities and localized sum
remain separate steps toward III.23, which is not yet closed.

Verification: 9943 incremental jobs, 7 affected / 16 rebuilt clean traces,
14 standard-axiom-only checks in `Audit/SemimartingaleKernelHistoryAxioms.lean`.
No full build or push.

### Source-strength CDF-AC and exponential compensator corollaries (III.21)

`ForMathlib/MeasureTheory/StieltjesAbsolutelyContinuous.lean` proves that
an absolutely continuous original Stieltjes function has an absolutely
continuous restricted measure. Its actual derivative is integrable on every
relevant subinterval; native FTC identifies interval masses and genuine
measure extensionality proves the result. No density representation is input.

`Counting/HazardCDFAbsolutelyContinuous.lean` converts the actual lifetime
CDF hypothesis into the required original finite positive lifetime-measure
restrictions, using actual map/restriction identities on the finite event.
`GeneralLifetimeHazardAbsolutelyContinuous.lean` transports the already
proved measure-AC result to original stopped hazards and their same selected
canonical compensators. `GeneralLifetimeHazardCDFAbsolutelyContinuous.lean`
then proves the literal CDF-function version on an arbitrary original space,
assuming only measurable AE-finite lifetime and actual compact-interval CDF AC.
All compact intervals share one full-measure event; no density or compensator
path-regularity certificate is added. This closes III.21 Corollary 1.

`GeneralLifetimeHazardExponential.lean` uses the actual original-space
exponential law and the native map-map identity. The actual stopped hazard
is pointwise the positive rate times the finite stopped clock. The same
canonical compensator is indistinguishable from it in the genuine usual
completion. No separate finite-lifetime hypothesis is imposed; the stopped
clock is proved finite before evaluation. This closes rate-corrected III.21
Corollary 2, whose printed shorthand applies only to unit rate.

III.21's integral/diffuse theorem and both corollaries are now proved.
General conditional-history III.23, its corrected independent-interval
indices, and hazard-rate/censored-data applications remain separate work.
An actual interarrival after an infinite preceding arrival must be infinite,
not the default difference infinity minus infinity; no age is evaluated then.
Latent independent gaps and absorbing gaps extracted from arrivals must not
be conflated when infinite gaps are allowed.

Verification: 9938 incremental jobs, 6 affected / 6 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleHazardCorollariesAxioms.lean`.
No full build or push.

### Actual CDF, diffuse logarithmic hazard and law specializations

`ForMathlib/MeasureTheory/Function/UniformIntegrablePullback.lean` transports
native UI through actual measure-preserving norm-tail identities, without
injectivity. `Counting/GeneralLifetimeHazardUI.lean` applies it to the original
arbitrary lifetime and its actual pushforward law, closing that UI gap.

`Counting/{HazardCDF,HazardStieltjes}.lean` identifies the actual probability
CDF and its pre-jump survival, and proves the original ENNReal hazard equals
the native CDF Stieltjes integral on `(0,t]`. Zero mass at infinity is required
before interpreting the totalized real coordinate as a finite lifetime.
Initial and endpoint atoms remain distinguished. `HazardDiffuseCDF.lean`
constructs the actual atomless pushforward and continuous CDF;
`HazardCDFConverse.lean` proves the exact converse, including the infinite point.

`HazardContinuousPaths.lean` uses genuine two-sided dominated convergence
off a null boundary point and proves common-event continuity of the original
stopped paths. `Analysis/PathVariation/StieltjesLogarithm.lean` reuses the actual
pathwise substitution owner to prove NNReal and real-time logarithmic Stieltjes
integrals, retaining the initial value and requiring positive survival.
`ForMathlib/MeasureTheory/StieltjesNNRealRestriction.lean` supplies the exact
positive-halfline measure bridge, with the zero atom explicitly excluded.
`HazardLogarithm.lean` identifies the original finite hazard and its common-event
stopped CDF formula without a density assumption. `GeneralLifetimeHazardDiffuse.lean`
transports continuity and the formula to arbitrary original probability spaces,
then identifies the existing sole compensator in the genuine usual completion.

`HazardAbsolutelyContinuous.lean` derives a genuine finite weighted measure
and its RN primitive from absolute continuity of each actual finite positive
lifetime restriction. Original stopped paths are locally absolutely continuous
on one event, including the infinite-lifetime branch. The CDF-function AC
input bridge remains separate. `HazardExponentialLaw.lean` uses native
`expMeasure r` to derive all singleton masses, survival and actual hazard
`r*t` for arbitrary positive rate, without an extra finite-lifetime premise.
Its final original-space compensator consumer and conditional-history III.23
remain separate work.

Verification: 9933 incremental jobs, 14 affected / 14 rebuilt clean traces
and 24 standard-axiom-only checks in
`Audit/SemimartingaleDiffuseHazardAxioms.lean`. No full build or push.

### Unrestricted compensation and arbitrary lifetime laws

`Filtration/MartingalePullback.lean` identifies the actual natural filtration
of a composed process with the exact comap, including Nat-valued counts.
Native martingales pull back along an actual measure-preserving map with
this filtration equality. The proof transports event integrals and L1;
it assumes neither injectivity nor independence or an arbitrary enlargement.

`Counting/HazardUnrestrictedCompensator.lean` constructs the actual uncapped
closed count's adapted/cadlag/global-IV domain in the genuine usual completion,
and identifies its sole canonical compensator with the original stopped
hazard, with no finite cap or positive-survival guard. Eventual exact recovery
from integer caps proves predictability; no coordinate-AE/all-times exchange
or replacement process is used. The initial count atom remains in the remainder.

`Counting/HazardUniformIntegrability.lean` proves whole-half-line UI of the
actual canonical compensated count. The integer supremum of the existing
extended stopped hazards has expectation at most one by monotone convergence.
Finiteness is established before real conversion; one plus that actual L1
envelope dominates every finite-time remainder. No second terminal owner is added.

`Counting/GeneralLifetimeHazard.lean` constructs the law as the actual
pushforward of any measurable extended lifetime on any probability space.
It proves raw-natural martingality, constructs the completed source domain,
and identifies the actual canonical compensator with that law's original
stopped hazard. The actual stopping-time predicate, predictable stopping map,
common-event path transport and usual augmentation supply all hypotheses.
Zero and infinite lifetimes and terminal atoms are retained.
The CDF/Stieltjes, logarithm, absolute-continuity and exponential applications
of III.21 and general conditional-history III.23 remain separate work.

Verification: 9920 incremental jobs, 5 affected / 5 rebuilt clean traces,
and 8 standard-axiom-only checks in
`Audit/SemimartingaleGeneralHazardAxioms.lean`. No full build or push.

### Actual filtration-shrinkage examples and canonical capped compensation

`LocalMartingale/InitialMagnitudeModel.lean` constructs the second example
on Protter's printed page 128 from the existing symmetric inverse variable.
Reflection proves actual conditional mean zero for every bounded magnitude
cutoff, tested on every initially measurable magnitude event. The existing
initial-value localizer of the magnitude supplies the native fundamental
sequence. `InitialMagnitudeCounterexample.lean` lifts this same process to two
genuine completed usual filtrations: it is a local martingale in the larger
one, is not a local martingale in the smaller one, and remains a FV
semimartingale there. The smaller before-one field has actual zero-one AE
representatives. Native localization forces an impossible first moment.
Together with the earlier geometric process, both printed-page-128 examples
are now complete; the preceding pending entries are superseded.

`PredictableQuadraticVariation/DomainCounterexample.lean` uses the original
geometric model and measure. The raw squared-jump bracket stays the same in
the reveal and full-information usual filtrations. Native local IV is
impossible in the smaller field by the actual increment moment obstruction.
In the larger field, predictability and FV construct the actual angular
domain, and sole uniqueness identifies the actual angle with raw QV.
No angular-domain or proposed-compensator premise is accepted.

`Counting/HazardCompensator.lean` constructs the actual capped closed count's
adapted/cadlag/global-IV domain in the genuinely completed space, then
identifies its sole canonical compensator with the original stopped hazard
when survival at the cap is positive. The initial count atom stays in the
martingale remainder; it is not silently removed from the source.
`ForMathlib/MeasureTheory/OrderSurvival.lean` proves positivity of the closed
upper-tail mass at almost every sample in a first-countable complete linear
order, for arbitrary measures. `HazardUnrestrictedBalance.lean` uses that
fact to remove the deterministic survival guard from actual stopped-hazard
expectation and L1 identities, proving AE extended finiteness before real
conversion. `HazardUnrestrictedMartingale.lean` proves true martingality of
the actual uncapped remainder in the raw natural filtration, not just equality
of its expectations. `HazardPathRegularity.lean` proves common-event extended
finiteness, monotonicity and cadlag paths of the original stopped hazard.
Unrestricted canonical compensation and global UI remain separate.

Verification: 9916 incremental jobs, 9 affected / 9 rebuilt
clean traces and 25 standard-axiom-only checks in
`Audit/SemimartingaleHazardDomainAxioms.lean`. No full build or push.

### Native moment obstruction and actual predictable hazard

`LocalMartingale/GeometricLocalMomentCounterexample.lean` closes the first
example on Protter's printed page 128: the centered geometric value is
revealed at time one in an actual usual filtration. The process is UI and
a native local martingale but is not natively locally square-integrable.
The proof uses the actual before-field moment obstruction, including the
positive-lifetime mask, not a classically redefined localizer.
`FiniteVariation/BeforeFieldMoment.lean` supplies the increment analogue:
native local IV and zero-one information before a positive time force the
actual increment from zero to be L1. The initial value itself need not be L1.

`LocalMartingale/SymmetricInverseModel.lean` constructs the actual uniform
law on (-1,1) and its reciprocal variable. Reflection preserves the measure;
the reciprocal law is symmetric and has zero mass at every singleton, while
its absolute first moment is genuinely infinite. This is the distributional
foundation of the second printed-page-128 example, not its process proof.

`Counting/HazardMartingale.lean` proves that the actual capped closed count
minus the stopped extended-hazard real representative is a true UI martingale
in the raw natural filtration, with positive pre-jump survival at the cap.
Actual event integrals prove the martingale identity; the finite hazard bound
gives a common UI envelope. Initial and infinite atoms are retained.
`HazardPredictable.lean` proves predictability of the original stopped hazard
by the existing exact predictable stopping map. This measurability statement
is valid even without the separate finite-hazard guard; it does not identify
a totalized infinite real value with a finite integral.

`Filtration/MartingaleAugmentation.lean` transports UI through genuine
completion for every exponent and measure, using actual raw AE event
representatives and the original Lp norm. For probability measures and
already right-continuous raw filtrations, true, UI and native local martingales
survive usual augmentation, retaining the exact original fundamental sequence.

Verification: 9908 incremental jobs, 7 affected / 7 rebuilt
clean traces and 24 standard-axiom-only checks in
`Audit/SemimartingaleNativeMomentAxioms.lean`. No full build or push.
General III.21/III.23 compensation and the second process example remain open.

### Hazard balance, genuine usual information and environment counterexamples

`Counting/SingleJumpConditionalExpectation.lean` identifies the actual raw
conditional expectation: full lifetime information on occurrence, the
guarded survival average otherwise. `SingleJumpRightContinuous.lean` proves
the raw closed-count natural filtration is right-continuous without a
measure or restrictions on zero/infinite lifetimes. The two augmentation
files in `Filtration/` prove that adjoining ambient null sets preserves
right continuity and actual original-L1 conditional expectations on the
genuinely completed space. `SingleJumpUsualInformation.lean` then provides
the exact augmented information and the same actual CE formula there.

`Counting/Hazard.lean` owns the single ENNReal cumulative-hazard integral,
with denominator the pre-jump survival mass. Monotonicity, measurability,
positive-survival finite-horizon bounds and capped real right continuity
are proved. `HazardBalance.lean` evaluates the existing stopped process by
Tonelli, then obtains its actual L1 expectation and strict-survival increment
balance. Zero/infinite atoms remain allowed. These are law identities;
predictable compensation, complete III.21 and conditional-history III.23
applications are not claimed from expectation balance alone.

`PredictableQuadraticVariation/ThreePointModel.lean` constructs two equivalent
positive-atom probability laws and the same bounded UI/L2 single-jump
martingale in a usual filtration. `EnvironmentCounterexample.lean` constructs
both actual angular domains and identifies the actual angles as steps of
height 1/2 and 1/4, while the raw bracket is the same squared jump.
`FiltrationCounterexample.lean` fixes the first law and enlarges information
to reveal the squared jump initially. The same process is still UI/L2;
its actual angle becomes the squared-jump step and differs from the small
filtration's angle. Neither counterexample accepts a proposed compensator,
domain witness or martingale certificate as an input.

`LocalMartingale/BeforeFieldMoment.lean` derives actual coordinate MemLp from
native local MemLp when the preceding field at a positive time has only
zero-one events, retaining the native positive-lifetime mask. The concrete
`GeometricMomentModel.lean` specializes the existing geometric measure at
3/4: Z(n)=2^n is L1 with mean 3/2 but has genuinely infinite second moment.
These are prerequisites for printed-page-128 process counterexamples,
not a claim that those process constructions are complete.

Verification: 9902 incremental jobs, 13 affected / 13 rebuilt
clean traces and 49 standard-axiom-only checks in
`Audit/SemimartingaleHazardMomentEnvironmentAxioms.lean`. No full build or push.

### Single-jump information, initial regressions and bracket environments

`Counting/SingleJumpInformation.lean` identifies all past closed single-jump
counts with the actual restricted lifetime: the original lifetime is revealed
when it is at most the observation time, and otherwise infinity is recorded.
It characterizes each natural-information event as a measurable revealed
lifetime event, optionally united with the entire strict survival event.
`SingleJumpInformationRegression.lean` proves on two points that the original
count is measurable in this natural field but not in the field of the capped
lifetime. Zero, endpoint and infinite lifetimes are not silently excluded.

`FiniteVariation/CompensatorIntegralRegression.lean` proves that constant-one
integration has a zero actual variation kernel yet can retain a non-L1
initial integrand. Only the centered integral is automatically L1. A second
test invokes the actual right-value compensator theorem: the left integral
is zero, the original raw initial product survives in the right integral,
and its actual canonical compensator is zero without an initial moment.

`QuadraticCovariation/EnvironmentInvariance.lean` uses the actual integral
environment theorems and polarization for raw QV/QCov. Target semimartingales
are derived for an absolutely continuous measure; target usuality remains.
Two semimartingale filtrations need not contain one another.
`PredictableQuadraticCovariation/ContinuousEnvironment.lean` constructs both
actual mixed-angle domains when one argument is continuous, then compares
them through raw covariation minus the common initial product. This is not
an unconditional predictable-angle invariance theorem.

Verification: 9890 incremental jobs, 6 affected / 6 rebuilt
clean traces and 12 standard-axiom-only checks in
`Audit/SemimartingaleInformationEnvironmentAxioms.lean`. No full build or
push. The single-jump CE/hazard consumers and actual discontinuous-angle
environment counterexamples remain separate work.

### Corrected III.19 and III.20 actual consumers

`FiniteVariation/CompensatorStochasticIntegralAE.lean` constructs the legal
everywhere-good source kernel but states its conclusion using the original
AE-source's actual Chapter II integral and the sole canonical compensator's
actual integral. Both are transferred through actual integral invariance,
not redefined. Expected absolute increment integrability proves the centered
source integral and the compensator integral L1, then their expectation
equality. The compensator starts at zero. The original initial product is
not assumed integrable; the source's ordinary initial L1 remains explicit.

`Analysis/PathVariation/CadlagIntegrandJumpCorrection.lean` derives countable
jump support and actual variation-measure integrability for both right and
left values of an arbitrary cadlag integrand, without integrand FV. The
existing pathwise integrals differ by the absolutely summable positive-time
jump products. Native Function.leftLim at zero equals the initial value,
so these two path-integral initial products cancel.

`FiniteVariation/SpecialLocalIntegrability.lean` uses the proved native
running norm/jump-supremum criteria to show actual local IV for FV local
martingales and FV special semimartingales. Existing actual compensation
gives the reverse specialness equivalence. No random L1 envelopes are
multiplied, and no original initial moment is imposed.

`RightValueCompensator.lean` uses these domains, general local Yoeurp and
actual predictable FV integration. The literal process J + [M,A] has actual
local IV, where J is the original integral of leftLimitProcess M against A.
A genuinely predictable version of J and full canonical uniqueness prove
that the actual compensator of this right-value expression equals J up to
indistinguishability. The actual pathwise identity is also proved, already
on the more general semimartingale/FV domain. Here leftLimitProcess M at
zero is zero, so J starts at zero and the raw bracket retains M_0 A_0.
The predictable-A hypothesis corrects III.20; native localization extends
the bounded-martingale/integrable-variation statement without adding moments.

Verification: 9884 incremental jobs, 5 affected / 5 rebuilt
clean traces and 10 standard-axiom-only checks in
`Audit/SemimartingaleCorrectedIntegralAxioms.lean`. No full build or push.
III.21/III.23 hazards and the other package gates remain open.

### Reverse arrival construction and actual integral compensation

`Counting/ArrivalSequence.lean` owns the guarded nonexplosive extended
arrival domain: positive increasing lifetimes, strict successors while
finite, and divergence to infinity. The actual count is the first index
whose arrival exceeds the horizon. Its exact inequalities, right
continuity, real cadlag paths and unit jumps are proved. The older all-finite
Poisson arrival construction is a proved specialization with the same count.
`ArrivalConstruction.lean` proves exact original native-hitting recovery,
count measurability, counting-process membership and adaptedness iff every
arrival is a stopping time. `ArrivalVersion.lean` uses only initial
completeness to restrict common-AE valid arrivals to one good event. Its
all-infinite exceptional paths are legitimate representatives; no raw
explosive count is totalized. All original arrivals and all-time guarded
counts are recovered on a single common event.

`FiniteVariation/StieltjesCongr.lean` proves equality of actual whole kernel
fibers under indistinguishability. `MonotoneCadlagVersion.lean` constructs
an adapted everywhere-good version. `CompensatorSignedTestsAE.lean` uses
these to construct both legal signed-test kernel representatives, identify
the actual canonical source compensator and retain the original UI remainder.

`UCP/PredictableVersion.lean` constructs a predictable version via the
existing common-event uniform subsequence and the predictable measurable
limit. `Semimartingale/SimplePredictable/PredictableIntegrator.lean` proves
that actual elementary integrals preserve predictable integrators: original
F_tau coefficients are cut off strictly after the left endpoint, where the
original increment already vanishes. The stochastic-integral companion
uses actual simple approximations and UCP uniqueness. No arbitrary raw
exceptional path is declared predictable. `PredictableIntegralCompensator`
then derives actual local IV and the canonical initial-corrected compensator.

`CompensatorStochasticIntegral.lean` restricts an actual predictable version
of an adapted AE-caglad integrand to `(0,T]`, applies signed kernel duality,
and identifies the original Chapter II integrals through FV agreement.
Expected absolute integrability proves both centered integrals L1 and their
expectation equality. The original initial products are retained; their L1
does not follow from an increment-kernel hypothesis. The actual increasing
compensator is constructed, not supplied as a premise. This consumer uses
everywhere-good increasing sources; the full AE-source consumer is separate.

Verification: 9880 incremental jobs, 12 affected / 12 rebuilt
clean traces and 38 standard-axiom-only checks in
`Audit/SemimartingaleArrivalIntegralAxioms.lean`, including the arrival
predicate, constructor and projections. No full build or push. Corrected
III.20, full AE-source Chapter II consumption and hazard formulas remain open.

### General local Yoeurp and nonexplosive counting

`Analysis/PathVariation/LifetimeJumpBudget.lean` extends actual disjoint
positive-jump finite-partial-sum bounds to the whole half-line by choosing
a finite horizon for each finite set. Infinite lifetimes contribute zero.
`FiniteVariation/PredictableBoundedVariationCovariation.lean` uses the
actual predictable jump cover and deterministic variation budget to invoke
the existing UI weighted-jump series theorem. Actual raw FV covariation
reindexing identifies the centered raw bracket as UI; no bounded test
martingale or original initial-product moment is imposed.

`PredictableBoundedVariation.lean` constructs native predictable/cadlag
localizations with deterministic whole-variation budgets: strict announcing
times prevent large-jump overshoot, then capped total-variation exits give
the actual bound. Native stable-property idempotence removes the extra
localization. `Yoeurp.lean` combines these with actual UI localizers,
common initial masks and raw simultaneous stopping to prove the general
local-martingale conclusion. The original initial product is added back as
a constant native local martingale, never assumed L1.
`YoeurpRegression.lean` tests arbitrary measurable initial constants:
zero variation still does not make the raw bracket UI without L1.

`Counting/Basic.lean` owns finite-valued nonexplosive counts with AE
measurable coordinates, zero initial count, common-event monotonicity,
right continuity and positive unit jumps. Real cadlag/FV paths are derived.
`Compensator.lean` constructs actual local IV from the unit-jump bound and
uses the sole canonical compensator, with increasing paths, exact initial
zero, local-martingale remainder and full predictable-FV uniqueness.
`ArrivalTimes.lean` uses the original native hitting times to prove
count/arrival equivalence, positivity, finite strictness, divergence,
finite-support real count sums and actual stopping/localizing properties.
Neither every arrival being finite nor a count moment is assumed.

`Poisson/Counting.lean` derives unit jumps from the proved actual raw
Poisson bracket identity, retaining only the chosen adapted usual
filtration needed by that proof. `Counting/DeterministicJump.lean` proves
the one-jump count, its actual self-compensator, non-Poisson behavior at
every rate, and original arrivals equal to one followed by infinity.

Verification: 9868 incremental jobs, 11 affected / 11 rebuilt
clean traces and 32 standard-axiom-only checks in
`Audit/SemimartingaleCountingYoeurpAxioms.lean`. The counting predicate,
constructor and fields are included. No full build or push. Reverse general
arrival construction, hazard formulas and other package gates remain open.

### Continuous and bilinear angle supplements

`FiniteVariation/ContinuousCompensator.lean` constructs actual local IV
for adapted AE-continuous FV sources and identifies their sole compensator
with the original process minus its initial value. Predictability is used
on the existing good version, not asserted on exceptional original paths.
The square-angle continuous module now reuses these two generic results;
its four public signatures and initial-square correction are unchanged.

`PredictableQuadraticCovariation/Algebra.lean` proves left/right addition
and arbitrary real scaling with genuinely constructed transformed domains,
plus common-path source invariance. `OneSidedStopping.lean` proves stopping
either argument at an arbitrary stopping time, constructing its domain.
`Continuous.lean` derives actual mixed-bracket continuity and local IV
from one continuous source, then identifies its actual angle with the
existing continuous covariation. The other source needs no square angle,
local L2 assumption or continuity.

`QuadraticCovariation/InitialMask.lean` proves the actual raw mixed
bracket identity for a common initial-field event by the original cross
sums, UCP masking and uniqueness. Arbitrary initial products are retained.

Verification: 9858 incremental jobs, 7 affected / 7 rebuilt
clean traces, and 17 standard-axiom-only checks in
`Audit/SemimartingaleAngleSupplementsAxioms.lean`, including the four
refactored square-angle declarations. No full build or push. General local
Yoeurp, remaining counting/hazard applications and change-of-measure results
are not concluded by these supplements.

### Actual mixed angle, polarization and stopping

`FiniteVariation/LocallyIntegrableScaling.lean` extends exact real scaling
to local IV with the same legitimate variation localizers.
`CompensatorAlgebra.lean` proves linearity of the actual selected compensator
under addition, subtraction and real scaling. `CompensatorStopping.lean`
constructs local IV after arbitrary stopping and identifies its actual
compensator with the stopped original compensator, including zero and infinity.

`Semimartingale/PredictableQuadraticCovariation.lean` defines the sole mixed
angle through that same compensator on the actual raw-cross local-IV domain.
It proves properties, full predictable-FV uniqueness, symmetry and agreement
with the existing square angle on the diagonal. No mixed monotonicity or
second selection method is asserted.

`PredictableQuadraticCovariation/LocallyIntegrable.lean` derives the mixed
domain from local IV of the two actual square brackets. The existing
Kunita--Watanabe estimate gives an actual total-variation bound by half the
sum of square variations. Actual measurability and finiteness precede real
conversion; common minimum localizers and original stopping identities
transfer the estimate. Native locally-L2 martingales therefore have the
actual mixed angle without initial product moments.

`LocalMartingale.lean` proves actual product compensation and the full
normalized predictable-FV competitor characterization for general local
martingales on the legal mixed domain. `Polarization.lean` derives the
square domain of the sum and identifies the actual mixed angle with half
the difference of the three actual square angles, using proved compensator
linearity. `Stopping.lean` constructs each stopped domain and proves
arbitrary stopping identities for square and mixed angles; predictability
of the stopping time is not required.

`Poisson/PredictableQuadraticVariation.lean` constructs both raw domains
from actual count integrability and monotonicity. Under the original chosen
past-independence hypotheses, canonical special-part coherence identifies
both actual angles with the linear drift, including rate zero. At positive
rate, the existing second-moment argument proves that compensated Poisson
raw and predictable brackets are not indistinguishable.

Verification: 9853 incremental jobs, 10 affected / 10 rebuilt clean
traces and 26 standard-axiom-only checks in
`Audit/SemimartingaleMixedAngleAxioms.lean`. No full build or push.
The basic mixed-domain, polarization and stopping gaps are closed; further
bilinear/one-sided stopping supplements, remaining compensator applications, change-of-measure/filtration and other package gates
remain separate work.

### Specialness criteria and actual predictable quadratic variation

`Semimartingale/SpecialJumpCriterion.lean` and `SpecialNormCriterion.lean`
prove both directions of Protter III.36--III.37 on the classical source domain.
The reverse jump implication constructs local IV of the actual FV component:
native joint localizers, positive deterministic caps and integrable envelopes
bound its positive jumps, including the stopping endpoint. Actual compensation
then constructs specialness. No good-integrator converse or initial moment
is imported as an assumption.

`FiniteVariation/CanonicalCompensator.lean` exposes the sole continuous-time
selector after actual existence and uniqueness, with full predictable-FV
competitor uniqueness, common-path invariance, monotonicity and coherence
with the actual canonical special parts. `CompensatorPredictable.lean`
proves the zero-terminal jump at a totally inaccessible time is zero, and
normalizes predictable sources by their original initial value.
`CompensatorContinuity.lean` proves III.24 for locally-IV sources with
totally inaccessible positive jumps, without needing source monotonicity.
Actual masked UI localizations show a before-measurable jump is zero;
the compensator's own countable predictable jump cover yields continuity.

`FiniteVariation/MonotoneLocalIntegrability.lean` turns native local
coordinate L1 of an increasing process into actual local IV, retaining its
arbitrary initial value. `Semimartingale/PredictableQuadraticVariation.lean`
uses this and the sole compensator to construct the angle on its legal
domain, with all actual properties, version invariance and full uniqueness.
`QuadraticCovariation/GeneralLocalMartingale.lean` removes local-L2
restrictions from raw-bracket-compensated products and squares via full
III.33 and actual integration by parts.

`PredictableQuadraticVariation/LocalMartingale.lean` proves square compensation
and its uniqueness characterization against all normalized predictable FV
competitors. `LocallySquareIntegrable.lean` derives the actual domain from
native locally-L2 martingales using exact raw-bracket masks, stopping and
finite-time moments. `Continuous.lean` constructs the domain for any
AE-continuous semimartingale through an existing predictable version, and
identifies the selected angle with raw Q minus the original initial square.
It does not declare exceptional original paths predictable.
`InitialRegression.lean` tests actual selection on arbitrary initial
constants, a nonintegrable initial square and the explicit constant-one process.
Printed p125's continuous `[X]=<X>` shorthand requires this initial correction;
the raw bracket starts at `X_0^2`, while its compensator starts exactly at zero.

Verification: 9844 incremental jobs, 13 affected / 13 rebuilt clean
traces and 31 standard-axiom-only checks in
`Audit/SemimartingaleAngleCriteriaAxioms.lean`. No full build or push.
Earlier reverse-classical-criterion and angle-existence gaps are superseded;
mixed angle algebra, remaining applications and the BD entry remain separate.

### Predictable FV local integrability and forward specialness criteria

`Stopping/LargeJumpThresholdLocalization.lean` proves threshold monotonicity
and native localization by the original first jumps larger than `n+1`, using
actual finite first-jump attainment and compact bounds. Combined with proved
predictability and strict-before announcing localizers,
`FiniteVariation/PredictableLocallyIntegrable.lean` establishes general
predictable cadlag FV local IV. No initial moment, bound, zero value or
preselected local-integrability witness is assumed.

`Path/RunningJumpSupremumStopping.lean` proves closed, event-restricted and
native masked stopping of the actual jump supremum, retaining the endpoint
and initial jump. `Measurability/RunningJumpSupremum.lean` proves its adaptedness
from actual first-jump threshold events, rational thresholds and usual
completeness for AE-cadlag paths. No uncountable measurability assertion is
left as a hypothesis. `Path/RunningJumpSupremumRegression.lean` supplies a
cadlag path with running norm one and running jump norm two.

`Semimartingale/SpecialIntegrableVariation.lean` proves local IV of the actual
canonical FV part and the equivalence between specialness and a normalized
LM plus adapted cadlag locally-IV decomposition, by genuine compensation.
`SpecialRunningSupremum.lean` proves whole-half-line native L1 envelopes and
both original running-supremum local-integrability conclusions for special
semimartingales. `FiniteVariation/RunningJumpCriterion.lean` proves local IV
from local coordinate L1 of the original running jumps by actual positive
caps and jump-envelope localization. The generic norm-to-jump implication in
`Measurability/RunningSupremumLocalIntegrability.lean` retains the same native
localizers and needs neither a martingale nor a finite measure.

Verification: 9832 incremental jobs, 10 clean affected/rebuilt traces and
18 standard-axiom-only checks in `Audit/SemimartingalePredictableFVSupremumAxioms.lean`.
No full build or push. The general predictable-FV local-IV gap is closed;
III.36--III.37 reverse criteria and the good-integrator-to-classical bridge
remain separate work. Earlier contrary gap descriptions are superseded.

### Signed compensator tests and source-strength running suprema

`FiniteVariation/CountingCompensator.lean` constructs unique compensators for
increasing bounded-jump processes and their unit-jump natural-valued counting
specialization. No initial L1, zero initial count or independence is assumed.
`JumpEnvelopeLocalization.lean` uses actual total-variation exits to obtain
local IV from an integrable random positive-jump envelope, including overshoot.

`Measurability/PredictableSignedKernelDuality.lean` transfers actual absolute
integrability through predictable rectangle duality before applying signed
Fubini. `FiniteVariation/SignedStieltjesDuality.lean` specializes to the existing
variation kernels; `CompensatorMonotoneVersion.lean` constructs an everywhere
cadlag increasing predictable compensator without changing the original source.
`CompensatorSignedTests.lean` applies the signed identity to that actual
compensator, not an assumed candidate. This repairs III.19's missing absolute
integrability on the everywhere-good kernel domain. General AE-source
Chapter II integral identification and the corrected III.20 consumer remain
open; no arbitrary predictable stochastic-integral operator is claimed.

`LocalMartingale/RunningSupremumIntegrable.lean` strengthens III.38 to genuine
whole-half-line stopped envelopes and integrable terminal suprema of the
original running norm process. It uses the existing masked stopping identity,
now public, and requires initial L1 only for ordinary unmasked stopping.
`Path/RunningJumpSupremum.lean` owns the actual all-times extended jump supremum,
including the initial jump, and proves finiteness and `J <= 2 X*`. A dense grid
of jumps is not substituted and measurability is not yet asserted here.

`Stopping/AnnouncingInfimum.lean` proves predictability for an almost-surely
attained countable infimum, not an unrestricted decreasing limit.
`AnnouncingLocalization.lean` constructs finite localizers strictly before
positive predictable targets by a summable-error diagonal and native tail
infima; no growth rate of the targets is assumed. `PredictableLargeJump.lean`
applies actual before-measurable jump restrictions, finite first-jump attainment
and usual completeness to the original first large-jump time of predictable FV.

Verification: 9823 incremental jobs, 13 clean affected/rebuilt traces and
19 standard-axiom-only declarations in `Audit/SemimartingaleSignedSupremumAxioms.lean`.
No full build or push. General predictable-FV local IV and III.36--III.37 remain
open; the III.38 unmasked/terminal-supremum supplement gap below is superseded.

### Canonical special decomposition, III.35 and running-supremum localization

`Semimartingale/BoundedJumpSpecial.lean` uses actual III.29, bounded-jump FV
local IV and local compensation to construct exact normalized predictable
parts for a classical semimartingale with jumps bounded by `C`. The predictable
part has actual local IV and jump bound `C`; the local-martingale part has
bound `2 C`. `ContinuousSpecial.lean` applies `C=0` and proves continuity of
both parts from their vanishing positive-time jumps.

`CanonicalDecomposition.lean` is the sole canonical-part selector, guarded by
specialness. It retains the original initial value in the martingale part,
proves all source properties, uniqueness against arbitrary predictable FV
competitors and indistinguishability invariance. `CanonicalJumpBounds.lean`
and `CanonicalContinuous.lean` identify actual III.35 outputs with these same
parts, transferring local IV/jump bounds/continuity. The arbitrary-initial
constant regression constructs specialness before identifying its canonical
parts and rejects a UI conclusion for a nonintegrable initial value.

`LocalMartingale/RunningSupremum.lean` gives actual masked localizations with
integrable whole-half-line envelopes by III.29, bounded-jump localization
and zero-initial stopped variation. An explicit stopping/mask identity gives
native local integrability of the original `denseRunningSupremum` norm process
(III.38's masked form); it does not assert unmasked L1 for arbitrary initial
values. Extended suprema are proved finite before their real conversions.
`Poisson/SpecialDecomposition.lean` identifies actual Poisson canonical parts
and proves the two ordinary decompositions are genuinely distinct at positive
rate, using the true time-one second moment. Past independence is explicit.

Verification: 9812 incremental jobs, 8 clean affected/rebuilt traces and
16 standard-axiom-only checks in `Audit/SemimartingaleCanonicalSpecialAxioms.lean`.
No full build or push. III.36--III.37 and the general predictable-FV local-IV
step remain open. Printed p.132's `J <= X*` loses a factor of two; the needed
bound is `J <= 2 X*`, and initial-value/localization conventions must be retained.

### Protter III.33--III.34 and bounded-jump variation localization

`FiniteVariation/BoundedJumpLocalization.lean` proves that the actual total
variation process has positive jump equal to the original jump norm, then
uses its capped exits to give integrable stopped whole-line variation with
the explicit bound `n + 1 + C`. It derives local IV without an initial moment.

`StochasticIntegral/IntegrableVariationMartingale.lean` uses bounded simple
approximation, an actual variation envelope and coordinate-UI closure to
prove true UI integration for a globally IV local martingale with initial
L1 and bounded caglad integrand. `LocallyIntegrableVariationMartingale.lean`
intersects actual variation, initial-value and integrand cutoffs; existing
masked integral identities remove those bounds and initial moments.
`LocalMartingale.lean` combines this with actual III.29 and the old locally-L2
integral theorem, proving full III.33 on the Chapter II domain. Its regression
applies the general theorem to arbitrary initial-measurable constants and
disproves a UI strengthening when the retained initial product is not L1.

`Semimartingale/Special.lean` defines the predictable source decomposition,
derives good-integrator semimartingality and proves III.34 uniqueness against
all predictable FV competitors. Actual Rao and local Doob existence give the
specialness consumers. No component selector or III.35 criterion is claimed
in this packet; the merely-predictable Chapter IV integral is not substituted
for the adapted-caglad source domain.

Verification: 9805 incremental jobs, 7 clean affected/rebuilt traces and
14 standard-axiom-only checks in `Audit/SemimartingaleSpecialIntegralAxioms.lean`.
No full build or push. Earlier III.33 open statements are superseded.

### Protter III.29--III.32: actual fundamental and classical closure

`Path/LargeJumpExitBound.lean` proves the actual joint-exit overshoot estimate,
retaining the original possibly unbounded sample. `FiniteVariation/LargeJumpIntegrable.lean`
uses bounded optional sampling and measured actual extended variation to give
integrable stopped variation and local-IV signed/norm sums for a true cadlag
martingale. `LocallyIntegrableLocalization.lean` proves stability of the
adapted/cadlag/IV bundle and native localization idempotence. `LargeJumpLocal.lean`
uses the original masked fundamental sequence and actual stopping identities
to give local IV for a general local martingale's original sums.

`Martingale/Doob/CompensatedJumpBoundLocal.lean` intersects actual UI and IV
localizers, proves the localized beta/2-beta bounds and recovers all positive
times, with an actual local-compensator existence consumer and no initial L1.
`LocalMartingale/FundamentalDecomposition.lean` constructs the exact III.29
parts M=N+D with local-IV D, correct initial values and proved local L2 for N.
`Semimartingale/LocalMartingale.lean` centers only through the existing initial
local-martingale owner, constructs normalized decomposability and invokes its
source good-integrator implication. `Classical.lean` implements the source
predicate, proves classical/decomposable equivalence by actual III.29, and
proves III.30. `OneSided.lean` uses actual Rao/Doob existence for III.31--III.32
and the submartingale corollary, with no Class D or global UI assumption.

Verification: 9799 incremental jobs, 10 clean affected/rebuilt traces and
24 standard-axiom-only checks in `Audit/SemimartingaleFundamentalLocalAxioms.lean`.
No full build or push. III.33, the reverse good-integrator implication, special
canonical criteria and source examples remain separate obligations.

### Increasing compensators and the large-jump route to Protter III.29

`FiniteVariation/{CompensatorMonotone,CompensatorLocalMonotone}.lean`
prove monotonicity of actual predictable compensators through general Class D
Doob existence, uniqueness, centering and native localizers; the local
existence result imposes no initial moment assumption.
`Analysis/PathVariation/LargeJumpSum.lean` proves compact summability, cadlag
regularity, actual variation bounds and exact jumps of the literal sums.
`Process/Path/LargeJumpSum.lean` names those actual signed/norm processes and
lifts the deterministic properties to one common path event.
`Stopping/LargeJumpSumEnumeration.lean` proves equality with the old countable
enumeration and strong adaptedness for every measurable jump transform;
`Measurability/LargeJumpSum.lean` restores the original AE-cadlag source under
usual conditions. `Path/LargeJumpStopping.lean` proves closed stopping and
arbitrary event-restriction compatibility, including zero/infinite lifetimes.

`LocalMartingale/BoundedJumpLocalization.lean` constructs the actual bounded
fundamental sequence and local square integrability from positive-time jump
bounds, preserving arbitrary initial values through existing masks.
`Martingale/Doob/CompensatedJumpBound.lean` proves actual beta/2-beta jump
bounds at predictable lifetimes and then all positive times, with an actual
global-IV compensator existence consumer and UI residual. Source values are
not required bounded. Strict large jumps leave equality-size jumps in the
residual, which still has the required non-strict bound. Local-IV large-jump
localization and the general local III.29/III.30 assembly remain separate.

Verification: 9790 incremental jobs, 10 clean affected/rebuilt traces and
35 standard-axiom-only checks in
`Audit/SemimartingaleLargeJumpCompensatorAxioms.lean`. No full build or push.

### General compensators (Protter III.5) and UI predictable jump budgets

`Semimartingale/Quasimartingale/IntegrableVariation.lean` proves the direct
bound Var(X) <= E|X(0)| + 2 E[actual total variation], retaining the original
partition and terminal-zero tail. The bound needs no usuality or finite
measure; cadlag paths give the actual quasimartingale bridge.
`FiniteVariation/CompensatorIntegrable.lean` invokes actual Rao existence and
the existing integrable-envelope local-martingale theorem to construct a
predictable global-IV part, true UI remainder, finite-time initial-value-
correct mean identity and uniqueness against predictable FV competitors.

`FiniteVariation/{CompensatorLocalization,CompensatorLocal,CompensatorInitial}.lean`
construct actual native stopped compensators, prove stopped consistency
with only AE localizer monotonicity, and patch through the existing predictable
UCP owner. Stopped recovery gives local IV; native masked localization gives
the actual local-martingale remainder. Centering/restoring the original
constant Protter local martingale removes any initial integrability
requirement. The final compensator starts exactly at zero and is unique.
`CompensatorRegression.lean` invokes that theorem for an arbitrary initial
random constant, identifies its compensator with zero, and proves why a
nonintegrable initial value precludes a true UI remainder.

`Martingale/OptionalSampling/PredictableJumpBudget.lean` constructs the UI
terminal and expresses each actual zero-terminal predictable jump as a
difference of its stopped-field/before-field conditional expectations.
Actual finite-partial coefficient budgets and L1 contractions prove
sum E|weighted jump| <= 2 C E|terminal|, genuine summability and a UI
closed-step series. No bound/L2/semimartingale property of M is assumed.
The native explicit terminal-zero convention is retained at infinite
lifetimes. This does not yet construct the general local Yoeurp variation
localizers or discharge the later counting-process/angle-bracket applications.

Incremental verification: 9781 jobs, 9 clean affected traces and
10 standard-axiom-only checks in `Audit/SemimartingaleCompensatorExistenceAxioms.lean`.
No full build or push. Earlier general-compensator-existence open statements
are superseded here, not the remaining application and package gates.

### General local Doob--Meyer and Rao (Protter III.16 and III.18)

Printed pp.116--119 are now covered by
`Doob/{NormExitClassD,StoppedCompensatorMean,PredictableLocal,PredictableLocalCanonical,PredictableLocalTerminal}.lean`
and `Semimartingale/Quasimartingale/RaoLocal.lean`.
The actual capped norm exit is deterministically bounded, so one-sided optional
sampling makes its actual sample integrable. That sample plus the exit level
dominates the stopped path and all its finite stopping samples, proving Class D
without Class D of the source. General III.11 supplies each actual part.
Predictable FV uniqueness derives stopped consistency, not a source premise.

`Stopping/PredictableProcess.lean` proves predictable-generator measurability
of the actual stopping map, including zero and infinite lifetimes.
`UCP/PredictableConsistentLocalization.lean` reuses UCP completion and stopping
uniqueness, obtains common compact eventual equality, and proves genuine
predictability after a usual initial-null reset using pointwise limits.
No arbitrary indistinguishable-version measurability claim is used.
The exact local construction has a predictable increasing local-IV part,
a local martingale, finite-time integrability and the sharp source mean-drop
bound by optional sampling plus Fatou. Its normalized source form preserves
X(0), has both new parts exactly zero initially, and proves uniqueness.

The existing monotone terminal owner supplies the actual terminal under any
signed lower source-mean bound; the finite limiting-mean form follows from
antitonicity. Both give global IV and whole-time AE/L1 limits. III.18 consumes
the two actual III.17 coordinates, proves exact X = M + A, global/local IV
of the predictable zero-initial A and uniqueness of both parts.
`FiniteVariation/LocallyIntegrableAlgebra.lean` adds native-localizer congruence
and algebra without initial integrability. The deterministic negative-time
regression invokes actual III.16 and identifies its output, testing a source
outside Class D.

Incremental verification: 9774 jobs, 11 clean affected traces and
21 standard-axiom-only checks in `Audit/SemimartingalePredictableLocalAxioms.lean`.
No full build or push. Earlier III.16/III.18 open-status statements below are
historical and superseded here; general compensator and later gates stay open.

### General Class D Doob--Meyer and the positive-supermartingale difference theorem

`Doob/PredictableFiniteCorrections.lean` proves the actual finite correction
induction, with fixed original before-conditional jump means and disjoint
finite graphs. `PredictableSeriesRegularity.lean` uses actual collision-event
integrals and the genuine jump-series formula to cancel every positive
predictable sampled mean. Original and series sampled jumps are L1 before
their integrals are added. `PredictableRegularization.lean` constructs the
cover, coefficients, finite supermartingales, Class D moment budget, summability,
predictable increasing IV series and regular residual from the original source.
`Convergence/InMeasureOrder.lean` supplies the coordinatewise UI supermartingale
limit theorem. No series convergence or corrected supermartingale is assumed
by the final construction.

`PredictableClassD.lean` combines that actual correction with the full regular
continuous construction, proving Protter III.11 existence without source
value/jump bounds, TI, regularity, or a zero original initial value. The part
is predictable, cadlag, exactly zero initially, increasing, IV and Class D;
its sum with X is a true UI martingale. The existing IV terminal owner supplies
actual all-time AE/L1 limits. The existing predictable FV uniqueness theorem
supplies uniqueness. `PredictableClassDRegression.lean` identifies the actually
constructed part of a signed random-initial, integrable random-amplitude
downward step; the deterministic unit case is proved neither regular nor TI.
`FiniteVariation/MonotoneIntegrable.lean` owns the reused monotone-envelope IV
bound, with AE cadlag/zero initial data and no finite-measure requirement.
The old TI single-jump interface is preserved as a consumer.

`Quasimartingale/RaoCoordinates.lean` constructs the two actual nonnegative
supermartingale coordinates from the future envelopes. The canonical dyadic
right-limit extension remains a supermartingale, preserves nonnegativity on
one common event, and preserves a right-continuous difference, by
`Convergence/RegularizationSupermartingale.lean`. No individual modification
or right-continuous expectation is assumed. `Quasimartingale/Rao.lean` proves
the exact difference decomposition and equivalence of Protter III.17 with
cadlag coordinates and the original variation bound. The source names the
subsequent III.18, not III.17, Rao's theorem; III.16/III.18 remain open.

Incremental verification: 9764 jobs, 12 clean affected traces and 16
standard-axiom-only checks in `Audit/SemimartingalePredictableClassDAxioms.lean`.
No full build or push. Earlier prerequisite entries below describe their
historical checkpoints, superseded by the source-completion statements here.

### Predictable jump removal, correction budgets and dynamic future envelopes

`Stopping/PredictableJumpTests.lean` constructs positive disjoint predictable
graphs from actual large-jump sequences, accessible/TI classification and
before-field restrictions. Every fixed predictable test is covered almost
surely at its nonzero positive jump. The AE event may depend on the test;
there is no common event over all random tests or false predictable
jump-amplitude restriction.
`Path/LifetimeStepSeriesJump.lean` passes actual uniform series convergence
to jumps, proves the coefficient identity on disjoint finite graphs, and
proves monotonicity for nonnegative coefficients, including time zero.

`Doob/ClassDPredictableJumpMean.lean` proves that the original integrable
zero-terminal jump has nonpositive before-conditional mean. Actual deterministic
caps have the terminal X_T on both sides; bounded-upper minimum sampling,
announcing limits and before-field integer masks handle arbitrary lifetimes.
`PredictableJumpRemoval.lean` proves that subtracting one such mean from a
cadlag Class D supermartingale preserves supermartingality. Actual clamped
announcing samples and Class D L1 convergence prove the raw-jump removal
bound; the existing centered single-jump martingale then gives the target.
`NonnegativeStepBudget.lean` bounds the sum of coefficient moments when
every actual finite corrected sum is a supermartingale and the original
expectations are uniformly bounded below. Vanishing coefficients at infinity
are explicit. Finite-series preservation and the full infinite regular
reduction are not inferred from this intermediate budget premise.

`ForMathlib/MeasureTheory/Function/EssentialFamilyConditional.lean` preserves
the actual essential supremum on a measurable restriction and passes common
conditional upper bounds to its finite integrable real representative.
`Quasimartingale/FutureEnvelopeSupermartingale.lean` applies exact partition
prepending and these event-integral bounds to the actual future envelopes.
It proves their dynamic conditional inequality and the true supermartingale
property of chosen measurable coordinates. No cadlag version, modification,
supremum/conditional-expectation interchange, or Rao theorem is assumed.

Incremental verification: 9754 jobs, 8 clean affected traces and 11
standard-axiom-only checks in `Audit/SemimartingalePredictableReductionAxioms.lean`.
No full build or push.

### Full regular Class D continuous decomposition and whole-future balance

`Stopping/NormExitResidual.lean` proves that subtracting the entire actual
exit jump from the capped stopped process leaves a uniformly bounded
residual, including a possible zero exit. `IntegrableJumpEnvelope.lean`
converts actual positive-jump domination into genuine sampled-jump L1.
`Doob/PredictableCompensatorJump.lean` identifies the actual compensator
jump as the before-field conditional mean, first deriving source-jump L1.
`RegularJumpRemoval.lean` uses zero predictable-jump means and the actual
predictable FV jump cover to give common-event bounds 2C for compensator
jumps and 4C for compensated-residual jumps. No amplitude-selected centering
or TI condition is used.

`RegularSingleJumpRemoval.lean` constructs the actual single-jump compensator
and applies the bounded-jump regular theorem. Adding back the UI martingale
leaves the continuous increasing part unchanged. `RegularContinuousClassD.lean`
constructs these parts at actual capped exits, proves consistency and invokes
the shared Class D patching/terminal owner. The final source theorem has no
value/jump bounds, assumed coefficient moment, proposed compensator, terminal,
consistency or convergence input. `ClassDPredictableJump.lean` independently
proves integrability of arbitrary zero-terminal stopping values and positive
predictable jumps of Class D processes by masked finite and announcing samples;
it needs neither finite measure, adaptation nor usual conditions.

`Quasimartingale/FutureEnvelope.lean` constructs both actual all-future
essential envelopes on the original measure, with the original global variation
bound. `FutureEnvelopeBalance.lean` proves the exact finite-partition signed
telescoping identity and the real-valued envelope difference at each time.
Translated essential upper bounds, not a supremum/subtraction interchange,
give the latter. Finiteness precedes real conversion. Supermartingale and
cadlag envelope versions, Rao, and general III.11/III.16 existence remain open.

Incremental verification: 9747 jobs, 10 clean affected traces and all
16 checks in `Audit/SemimartingaleRegularFullClassDAxioms.lean` using only
standard Lean axioms. No full build or push.

### Full continuous Class D decomposition (Protter III.10)

`Doob/ContinuousClassD.lean` proves actual existence from a cadlag Class D
supermartingale, usual conditions, totally inaccessible positive-time jumps
and an almost-sure zero initial value. There is no bound on values or jumps,
and no proposed compensator, selected exceptional time, coefficient moment,
consistency, terminal variable or convergence certificate in the input.
The output is adapted, predictable, everywhere continuous, exactly zero
initially, and almost surely increasing/FV. Its sum with X is a true UI cadlag
martingale. The increasing part is Class D with an actual integrable terminal
envelope and full-half-line AE/L1 convergence. Continuous FV uniqueness is
already proved in `ContinuousUniqueness.lean`, so this closes III.10.

`SingleJumpComparison.lean` and `UCP/MonotoneTail.lean` derive actual maximal
and UCP-Cauchy bounds from ordered compensator differences and amplitude tails.
`SingleJumpContinuous.lean` constructs the unbounded integrable single-jump
compensator and both actual terminal variables. `Convergence/ContinuousMonotoneL1.lean`
extends the existing integer terminal to the whole half-line and Class D.
`UCP/ConsistentLocalization.lean` constructs actual continuous local-to-global
limits with whole-path stopped recovery. `ContinuousClassDLocalization.lean`
separates Fatou integrability from the UI limit argument proving martingality;
the bounded-jump theorem reuses this owner instead of duplicating its proof.
`Stopping/{JumpExitIntegrability,SingleJumpLocalization}.lean` supplies actual
stopped-field measurability, L1 and the restricted TI exceptional time at each
norm exit. `OneLargeJump.lean` removes the actual exceptional jump using two
constructed martingales and retains the same increasing compensator when
recovering X. `Stopping/TotallyInaccessibleJumpAlgebra.lean` provides the
required linear jump-covering stability.
`ContinuousClassDRegression.lean` calls the full source theorem for
`X_t = -Z min(t,1)`, with arbitrary integrable nonnegative F0-measurable Z,
and identifies its output with `Z min(t,1)` by actual uniqueness.

III.11 is not inferred from III.10: conditional mean-zero jumps at predictable
times do not imply that all jumps are totally inaccessible. The printed
general-case reduction needs a separate justification on that broader domain.

### Predictable increasing-process energy (Protter III.10, Lemma 1)

The lemma on printed p.108 (PDF p.119) is proved in
`Martingale/Doob/{PredictableEnergy,PredictableTerminalEnergy}.lean`.
The conditional remaining mean is bounded by `N`, starting from zero. Finite
L2 calculations use the actual predictable increments and conditional
pull-out. Fixed truncations preserve predictability and monotonicity; diagonal
limits and native Lp Fatou derive terminal square integrability and
`E[C_infinity^2] <= 2 N^2` from an integrable terminal input. The input L1
condition makes the source conditional expectations meaningful; L2 is not
a premise of the final theorem. AE path and zero-starting conditions suffice.

`ForMathlib/MeasureTheory/FatouNonnegative.lean` supplies the general
integrability-and-bound consequence of native Fatou on arbitrary measure spaces.
`Doob/BoundedEnergy.lean` proves the conditional tail identity for the native
`predictablePart (-X)`, uniform `8 K^2` second-moment bounds for bounded
supermartingales, and constructs the actual increasing terminal L2 limit.
No mesh-dependent constant, continuous-time compensator or selector is assumed.
The subsequent dyadic results construct the bounded continuous decomposition.
The full unbounded Class D extension of III.10 is now proved above;
the general predictable III.11 construction remains open.

The former external `exchangeability` dependency and its inherited `checkdecls` dependency have
been removed. The exact theorem closure used by StochLean is now an attribution-preserving internal
implementation under `StochLean/Internal/Exchangeability`, compiled directly against Mathlib
v4.33.0. Reverse conditional-expectation convergence, contractability, directing-measure
construction, finite-product factorization, de Finetti, and the Boolean specialization are covered
by the ordinary build and semantic regression gates; cached external oleans are no longer used.

### One-way lower-density localization for Protter III.41

`Semimartingale/MeasureChange/AbsoluteContinuousDensityLocalization.lean`
owns the first entrance times of the canonical density into the open intervals
below `2⁻⁽ⁿ⁺¹⁾`. For `Q ≪ P`, the exact identity at the capped stopping time
bounds each early-exit probability by that summable threshold. Consequently
the exits form a genuine `Q`-localizing sequence. A common target-full-measure
event has `Z_{t-} ≥ 2⁻⁽ⁿ⁺¹⁾` at every positive `t ≤ Rₙ`, and hence a locally
bounded reciprocal. This is the source-faithful small-density localization
used by Protter III.41; it neither imports a reverse density nor asserts the
remaining III.41/III.42 local-martingale corrections.

Incremental verification: 10043 jobs, a clean isolated production check and
12 standard-axiom-only checks in
`Audit/SemimartingaleAbsoluteContinuousDensityLocalizationAxioms.lean`.

### One-way local-martingale transfer for Protter III.41

`Semimartingale/MeasureChange/AbsoluteContinuousMartingaleTransfer.lean`
owns the stopping-field Bayes and integrability identities under `Q ≪ P` and
the resulting density criterion. For a bounded stopping time it identifies an
integrable terminal value under `Q`, closes the target stopped process by
conditional expectations, and cancels the sampled density only on its
`Q`-full positivity event. The local theorem takes the minimum of the source
masked localizer, the geometric density exits and deterministic caps. Thus
`densityProcess Q P F * X` being `P`-local implies `X` is `Q`-local, with
target usualness explicit and no reverse density. This is the transfer bridge
used by III.41; its predictable correction and III.42 remain separate owners.

Axiom verification is owned by
`Audit/SemimartingaleAbsoluteContinuousMartingaleTransferAxioms.lean`.
Incremental verification passed 10044 jobs, a clean production check and all
6 standard-axiom-only declarations in that audit owner.

## Semimartingale SP-03 final closure — 2026-09-17

The merged Protter I--III and Klenke 21.10 implementation contract is complete
at the design's explicit-disposition boundary.  Current source-by-source
authority is split deliberately across four ledgers:

- [`docs/SEMIMARTINGALE_BLOCKER_LEDGER.md`](docs/SEMIMARTINGALE_BLOCKER_LEDGER.md)
  gives the final disposition of SM-B01--SM-B21.
- [`docs/SEMIMARTINGALE_PROTTER_LEDGER.md`](docs/SEMIMARTINGALE_PROTTER_LEDGER.md)
  records every numbered Protter item in Chapters I--III.
- [`docs/SEMIMARTINGALE_KLENKE_LEDGER.md`](docs/SEMIMARTINGALE_KLENKE_LEDGER.md)
  records Klenke 21.56--21.76 and Exercises 21.10.1--3.
- [`docs/SEMIMARTINGALE_REGRESSION_MATRIX.md`](docs/SEMIMARTINGALE_REGRESSION_MATRIX.md)
  closes R01--R38 with 30 theorem-level passes and 8 intentional structural
  guards.

The final production additions include Yan separation and
Bichteler--Dellacherie, the one-way Lenglart--Girsanov correction, Kazamaki and
Novikov criteria, stochastic-exponential uniqueness, Klenke normalized square-
and mixed-bracket uniqueness, stopping-moment interfaces and Exercise 21.10.3,
plus exact non-circular foundations for Protter I.52, I.56, Jacod expansion and
Meyer--Feller.  `Audit/SemimartingaleCompletionAxioms.lean` is the aggregate
declaration-level trust check; its 18 listed endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`.

The boundary remains exact.  The explicit rational-liminf identification in
I.52, process-level Jacod preservation in II.5, and the full Meyer--Feller
theorem III.4 are still blocked and are not exported.  Nonsmooth II.41,
canonical Levy cadlag realization/decomposition, Klenke Example 21.69(ii), and
the I.56 stochastic-selection extension are deferred.  These dispositions are
part of the completed coverage contract, not hidden theorem claims.

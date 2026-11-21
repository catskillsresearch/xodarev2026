# Pinned Mathlib audit

Baseline: Lean/Mathlib `v4.33.0`, resolved Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Searches covered the pinned checkout, the complete
local tree, and the approved-external ledger before each public gap was added.

## Global external-source rule

Mathlib is the only external Lean package permitted in the final dependency graph. An external
repository may be used only as an implementation reference after exact-revision statement,
dependency, proof-hole, axiom, build, provenance, and license review. Accepted code is copied into
the StochLean source tree, adapted to StochLean's mathematical owner and public API, and compiled
without an import or Lake dependency on the source repository. External names and module layouts
have no normative force. This is a permanent project rule for every present and future design
document.

## Reuse and gap decisions

| Topic / design row | Pinned result | Decision |
| --- | --- | --- |
| Ch.1 generated spaces and measure uniqueness | Mathlib generated measurable spaces and `Measure.ext_of_generateFrom_of_cover` | Reuse; no compatibility wrapper required. |
| Klenke 1.65 semiring approximation | Exact theorem `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring` in `MeasureTheory/Measure/MeasuredSets.lean` | Reuse; audit-first row closed as upstream. |
| Ch.2 independence/generators/regrouping | Canonical `Indep`, `iIndep`, `IndepFun`, `iIndepFun`; anchors include `iIndepSet.indep_generateFrom_of_disjoint` and `iIndepFun.indepFun_finset` | Reuse. |
| Laws of independent sums | Generated additive theorems `IndepFun.hasLaw_add` and `IndepFun.map_add_eq_map_conv_map₀` | Reuse for laws; add only the thin PGF expectation specialization. |
| Probability generating functions | No canonical PGF for `PMF ℕ` | Add `PMF.pgf`, the measure/law bridge, analytic layer, and safe-domain semantics. |
| PGF factorial derivative/moment boundary | General iterated-derivative, locally uniform sum, monotone-convergence, and ENNReal tools exist, but no probability theorem connects them | Add generic arbitrary-order derivative identification and `ℝ≥0∞` boundary theorem in `Analytic.lean`. |
| Discrete setwise convergence | PMF coefficient and summability APIs exist; no direct arbitrary-set convergence theorem from atomwise convergence | Add `PMF.setMassReal` and the tight-tail/discrete-Scheffé theorem `PMF.tendsto_setMassReal_of_tendsto_mass`. |
| Discrete PGF convergence | No matching atomwise/PGF equivalence | Add in `Probability/Convergence/Discrete.lean`. |
| `PoissonLimitThm` | Canonical i.i.d. binomial point-probability limit exists | Re-export upstream; add only the non-i.i.d. Bernoulli triangular-array result. |
| Finite independent Bernoulli sum law | `PMF.poissonBinomial` exists, but no generic family-to-law bridge | Add `iIndepFun.hasLaw_fintype_sum_bernoulli`. |
| Random sums | `PMF.bind` and `PMF.map` exist; no law-level random-sum PGF API | Build convolution powers and random sums from canonical monadic operations. |
| Galton-Watson | No matching construction/PGF/extinction fixed-point API | Add law-level branching modules. |
| Probability multinomial law | Only `Nat.multinomial` and product-measure primitives; no categorical-count PMF theorem | Add generic `PMF.multinomial` and `iIndepFun.hasLaw_categoricalCounts`. |
| Poissonized multinomial splitting | Poisson laws and characteristic functions exist; no finite categorical Poisson-mixing theorem | Add `PMF.poissonizedMultinomial_eq_independentPoissonCounts`. |
| Wald 5.5 / Blackwell-Girshick 5.10 | Independence integration and moment primitives exist; no matching random-count identities found | Add generic stopped-sum theorems in `Probability/Moments/RandomSum.lean`. |
| Paley-Zygmund exercise | Holder/Cauchy-Schwarz primitives exist; no matching zero-threshold probability inequality | Add multiplicative and quotient forms. |
| Empirical CDF / Glivenko-Cantelli | No matching empirical-CDF or GC declaration | Add strict/non-strict CDF APIs and full arbitrary-law uniform theorem; reuse `strong_law_ae`. |
| Kolmogorov maximal inequality 5.28 | Martingale maximal APIs exist, but no exact independent centered square-integrable specialization with the textbook bound | Add the square-submartingale bridge and Kolmogorov specialization. |
| Strong-law rate 5.29 | Borel-Cantelli exists; no exact Klenke dyadic/logarithmic rate theorem | Add the rate package after the maximal inequality. |
| Process representation and independent increments | Canonical processes are functions; `HasIndepIncrements` exists | Reuse and introduce no process structure. |
| Stationary increments | No exact generic predicate found | Add one function-based reusable predicate. |
| Poisson process / P1-P5 characterization | Poisson measures and independent increments exist, but no counting-process predicate or interval-axiom equivalence | Add corrected common-event path semantics and both directions of Klenke 5.34. |
| Klenke 5.35 uniform points | No probability multinomial/Poissonization package | Reuse the new generic distribution modules; keep process-specific code thin. |
| Klenke 5.36 exponential arrivals | Exponential measures exist; no arbitrary finite ordered-partition arrival/count law or needed simplex-volume bridge | Add generic simplex/cumulative-coordinate measure results and the full construction theorem. |
| Local convergence in measure | Mathlib `TendstoInMeasure` is global | Add `TendstoLocallyInMeasure` by finite restrictions. |
| Exhaustion metric and local completeness | No inducing pseudo/metric or sigma-finite Cauchy-completeness package | Add raw pseudometric, `AEEqFun` metric, fast convergence, subsequences, and completeness. |
| Uniform integrability / finite Vitali | Mathlib `UniformIntegrable`, `UnifTight`, `tendsto_Lp_finite_of_tendstoInMeasure`, and `tendstoInMeasure_iff_tendsto_Lp` exist | Reuse on finite restrictions and as canonical compatibility targets. |
| Klenke sigma-finite envelope UI | No exact literal envelope/tail/density package | Add separately named predicates and equivalences; do not shadow Mathlib UI. |
| de la Vallee-Poussin | No full superlinear-envelope bridge/converse found | Add sufficient and finite-measure converse theorems. |
| Klenke 7.3 | Mathlib `Lp` completeness exists; no local-convergence plus powered-envelope characterization | Add one generic bridge in `LpLocalConvergence.lean`. |
| Klenke 7.47/7.49/7.50 `Lp` dual representation | Holder pairing exists, but no exact general dual representation theorem was found | Explicitly defer to general functional-analysis/ForMathlib, as authorized by the handoff. |
| Conditional expectation and distributions | Canonical `condExp`, `Kernel`, `condDistrib`, `StandardBorelSpace`, and `condExp_ae_eq_integral_condDistrib` exist | Reuse; add only natural-domain and law-a.e. uniqueness guards. |
| External results 2.46, 5.30, 5.32 | No approved external dependency was admitted | Explicitly deferred; no hidden trust-boundary dependency. |

## Semantic and public-domain checks

- `PMF.pgf` accepts only `unitInterval`; the heavy-tail regression proves no outside-domain
  convergence is assumed.
- `PMF.factorialMoment` and the derivative boundary theorem use `ℝ≥0∞`, preserving infinite
  factorial moments.
- `TendstoLocallyInMeasure` is distinguished from global `TendstoInMeasure`; raw functions use
  a pseudometric and only a.e. classes receive a metric.
- The corrected Poisson process has one common full-measure monotone/right-continuous path event.
- The exponential-arrival proof establishes every finite partition and compiles an explicit
  four-increment application.
- `DivergentArrivalSequence.count` requires a divergence witness.
- Conditional-event APIs require positive mass, and conditional-kernel uniqueness is law-a.e.
- No project theorem relies on a conclusion-shaped premise, `sorry`, `admit`, or a
  project-defined axiom.

## Process Core duplicate audit

The Process Core audit used the same pinned commit and searched the full current local tree before
adding declarations.

| Topic / design row | Pinned result | Decision |
| --- | --- | --- |
| Process laws and finite-dimensional laws | `IdentDistrib`; `Measure.map`; `map_restrict_eq_of_forall_ae_eq`; `map_eq_of_forall_ae_eq` in `Mathlib.Probability.Process.FiniteDimensionalLaws` | Reuse. Local bridges only name the distinct modification semantics and explicitly avoid path-space-law claims. |
| Independent increments | `ProbabilityTheory.HasIndepIncrements` | Reuse the canonical predicate. |
| Gaussian process | `ProbabilityTheory.IsGaussianProcess` in `Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.{Def,Basic,Independence}` | Reuse; no local predicate. |
| Modification / indistinguishability | No matching process predicates found | Add `IsModification` and `Indistinguishable`, relation operations, countable collapse, and the dense right-continuous collapse. |
| Stationarity | No generic full-shift process-law predicate found | Add `IsStationary` by coordinate-product law, not marginal equality. |
| Natural filtration | `Filtration.natural` and `Filtration.stronglyAdapted_natural` exist; no direct order-minimality theorem found | Add only `Filtration.natural_le_of_stronglyAdapted`. |
| Predictable processes | `Filtration.predictable`; `IsStronglyPredictable.isStronglyProgressive`; `.stronglyAdapted`; `.measurable_add_one`; `.iff_measurable_add_one` | Reuse completely. |
| Right-continuous filtration | `Filtration.rightCont`, `le_rightCont`, `rightCont_self`, and `Filtration.IsRightContinuous` | Reuse. |
| Usual conditions | No combined right-continuity plus initial-completeness property found | Add `Filtration.IsUsual` with completeness relative to all ambient null sets. |
| Completed right continuation | `MeasureTheory.NullMeasurableSpace`, `Measure.completion`, and `Filtration.rightCont` exist separately; no filtration augmentation combining them was found | Add `nullSets`, `withNullSets`, and `usualAugmentation` on the genuinely completed ambient type. |
| Product/joint measurability | No process-level predicate found; ordinary `Measurable (Function.uncurry X)` is canonical | Add the thin name `IsProductMeasurable` and direct coordinate/path/process consequences. |
| Progressive measurability | Mathlib `IsProgressive` and `IsStronglyProgressive` | Reuse; no second predicate. |
| Continuous adapted process is progressive | `StronglyAdapted.isStronglyProgressive_of_continuous` | Reuse for continuous paths. |
| Right/left-continuous adapted process is progressive | No exact theorem found in pinned Mathlib | Add ceiling/floor-grid theorems for `ℝ≥0`; also add joint measurability for right-continuous paths. |
| A.s. regular paths give a progressive version | No exact theorem found | Add explicit modification constructions under usual completeness, changing the process only on the one common null event. |
| Adapted plus product measurable gives progressive modification | No approved Mathlib/local/external implementation found; Klenke attributes the result externally | Explicitly defer; no hidden dependency or unsupported theorem. |
| Stopping times and stopped sigma-algebras | `IsStoppingTime`, `.measurableSet_eq`, `isStoppingTime_of_measurableSet_eq`, `.min`, `.max`, `.add_const`, `.add`, `.measurableSpace`, and `.measurableSpace_mono` | Reuse. |
| Stopped process/value | `stoppedProcess`, `stoppedValue`, `IsStronglyProgressive.stoppedProcess`, and `measurable_stoppedValue` | Reuse; add one right-continuous adapted evaluation bridge. The theorem does not interpret Mathlib's total fallback at `τ = ∞`. |
| Hitting times | `hittingBtwn`, `hittingAfter`, `Adapted.isStoppingTime_hittingBtwn`, and `Adapted.isStoppingTime_hittingAfter` | Reuse with exact order/path hypotheses. |
| Cadlag path predicate | No generic common-a.s. predicate found | Add trajectory predicates only; defer Skorokhod topology. |
| Doob regularization and path-space topology | No Process Core implementation authorized | Explicitly defer to their designated later packages. |

## Process Core semantic checks

- The diagonal spike on the unit interval is a modification of zero but is not indistinguishable;
  its coordinate-product map law still agrees with zero.
- A Boolean Rademacher process has equal one-time marginals at all times but fails full
  stationarity because its first pair and shifted pair have different equality laws.
- A constant trivial filtration is right-continuous but is not usual for a Dirac probability on a
  nontrivial ambient measurable space.
- `usualAugmentation` changes to `NullMeasurableSpace Ω P` and `P.completion`, contains the original
  information, and is proved usual; no same-ambient completion is asserted.
- Right- and left-continuous adapted paths imply progressive measurability by countable-range
  approximations. Under usual conditions the a.s. variants produce explicit modifications.
- Predictable-to-progressive-to-adapted and the discrete `F n` measurability of `X (n+1)` use exact
  Mathlib declarations.
- The always-infinite stopping time retains `WithTop` infinity on a probability-one event.

## Discrete martingale and exchangeability duplicate audit

| Topic / design row | Pinned result or approved source | Decision |
| --- | --- | --- |
| Martingale predicates and conditional expectation | Mathlib `Martingale`, `Submartingale`, `condExp`, stopped processes, and filtration APIs | Reuse; local adapters do not define a second martingale notion. |
| Discrete stochastic integral | No named exact Klenke-indexed transform API found | Add `discreteStochasticIntegral` and prove its algebraic/probabilistic interface. |
| Quadratic variation / bracket | Mathlib has square-integrability and conditional expectation primitives but no matching discrete predictable-bracket package | Add pathwise and predictable processes with exact stopped compatibility. |
| Optional sampling | Bounded stopping theorems exist upstream | Reuse them; add only UI and a.s.-finite limit bridges. |
| Doob `L^p` | General upstream maximal inequality exists | Reuse and expose the exact sharp real-valued specialization; preserve `1 < p`. |
| Finite-bracket convergence | No exact predictable-bracket criterion found | Add predictable localization and derive Klenke 11.14 from ordinary martingale convergence. |
| Exchangeability | No pinned Mathlib finite-dimensional exchangeability predicate | Add the f.d.d.-correct local predicate; do not use equality of marginals as a surrogate. |
| Reverse conditional expectation | Upstream conditional expectation and martingale convergence exist | Add the antitone-filtration interface and exact infimum-field convergence. |
| de Finetti | No pinned Mathlib theorem with the required standard-Borel product-mixture statement | Maintain the audited proof closure internally under `StochLean/Internal/Exchangeability` and expose only the structural StochLean facade. |
| Empirical measure and symmetric factorization | No exact finite-tuple empirical-measure recovery/factorization API found | Add nonempty empirical measures, multiplicity recovery, permutation reconstruction, and plain factorization. |
| Invariant vs tail sigma-field | Raw `T ≤ E` is deterministic; no exact modulo-law equality was found upstream or in the audited source closure | Add the `L¹` finite-block relocation proof and explicit `MeasurableSpace.EqModulo`. |
| Hewitt-Savage | Mathlib has Kolmogorov zero-one, not Hewitt-Savage | Derive Hewitt-Savage through the modulo-tail theorem; no duplicate Kolmogorov proof. |

The exchangeability/de Finetti proof lineage was audited for its exact source revision, license,
dependency closure, and placeholder scan before being ported into the project. Original copyright
and Apache-2.0 attribution are retained in every internal source file. Project-facing milestone
declarations are rechecked independently in `Audit/Axioms.lean`.

## Measure convergence and projective construction duplicate audit

| Topic / design row | Pinned Mathlib or approved source result | Decision |
| --- | --- | --- |
| Standard Borel vocabulary | Mathlib `StandardBorelSpace`; distinct from `BorelSpace` | Reuse; define no local Borel-space class. |
| Weak convergence | Topology of `ProbabilityMeasure` with `tendsto_iff_forall_integral_tendsto` | Reuse ordinary `Tendsto`; define no `Weak` predicate. |
| Portmanteau | Closed/open limsup/liminf criteria and null-frontier set-mass convergence | Reuse completely. |
| Tightness / Prokhorov | `IsTightMeasureSet`, compact-closure implications in both directions on the canonical hypotheses | Reuse completely. |
| Convergence in distribution / Slutsky | `TendstoInDistribution`, `TendstoInMeasure.tendstoInDistribution`, `.continuous_comp`, `.prodMk_of_tendstoInMeasure_const`, and related corollaries | Reuse completely. |
| A.e.-continuous mapping | No theorem with exactly a measurable map and limit-law-null discontinuity set found | Add the Portmanteau bridge `ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous`. |
| Vague convergence | No canonical convergence-against-`C_c` predicate found | Add `TendstoVaguely` with local finiteness built into its semantics; add weak-to-vague and compact-space equivalence bridges. |
| Levy continuity | Pinned `Mathlib.MeasureTheory.Measure.LevyConvergence` contains the canonical characteristic-function/tightness package | Reuse; add no theorem. |
| Empirical weak convergence | Rational-interval pi-system criterion exists, but no theorem consumes StochLean's empirical object | Add only `tendsto_empiricalProbabilityMeasurePM_ae`, reusing the existing empirical CDF and measure APIs. |
| Cylinders / product sigma-field | `measurableCylinders`, `generateFrom_measurableCylinders`, coordinate measurability | Reuse. |
| Arbitrary product measure | `Measure.infinitePi`, projectivity, finite restriction, and cylinder formulas | Reuse. |
| Kernels / Ionescu--Tulcea | `ProbabilityTheory.Kernel.traj`, `trajMeasure`, and their finite-prefix/conditional-law API | Reuse. |
| Projective family and limit | Mathlib `IsProjectiveMeasureFamily` and `IsProjectiveLimit`, including finite uniqueness and probability preservation without nonempty index | Reuse the vocabulary and consequences. |
| Arbitrary-index standard-Borel extension | Not present in the pinned Mathlib checkout; `RemyDegenne/kolmogorov_extension4` supplied the audited reference construction | Internalize the proof under `StochLean.Internal.KolmogorovExtension` and expose a minimal StochLean facade; temporary Polish upgrades remain implementation-only, and no external package remains in the dependency graph. |
| Process/canonical path wrapper | Product coordinates are already functions and no path topology follows from projective construction | Add nothing; use `fun i ω ↦ ω i`. |

### Audited Kolmogorov-extension implementation reference

- Repository: `https://github.com/RemyDegenne/kolmogorov_extension4.git`.
- Exact audited commit: `7d76e184c3d2138a2741baf923b57e9a01b9cf25`. This revision records
  provenance only; it is not present in `lakefile.toml` or `lake-manifest.json`.
- License: Apache License 2.0.
- Audit checkout: `D:\Math\external-audit\kolmogorov_extension4-7d76e184c3d2138a2741baf923b57e9a01b9cf25`;
  its audited source is content-equal to the clean Git checkout at the pinned commit (line-ending
  normalization is the only byte-level difference).
- Placeholder/trust scan: no Lean occurrence of a declaration beginning with `axiom` or `unsafe`,
  and no `sorry` or `admit`.
- Independent reference build: successful, 1773 jobs.
- Project-facing axiom audit: `isProjectiveLimit_projectiveLimit` and every facade theorem depend
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- Internalization boundary: the adapted modules are compiled from
  `StochLean/Internal/KolmogorovExtension`; imports and namespaces were redirected to project
  owners. Public signatures contain only Mathlib/StochLean types and namespaces, and the external
  project is neither imported nor linked.

The complete fourth-milestone semantic gate is recorded as 23 numbered cases in `SOURCE_MAP.md`.

## Markov-process duplicate and source audit

| Topic / design row | Pinned Mathlib or approved project result | Decision |
| --- | --- | --- |
| Kernels and composition | Mathlib `ProbabilityTheory.Kernel`, `Kernel.comp`, powers, sums, maps/comaps, `compProd`, and deterministic kernels | Reuse completely; local declarations are relations or specialized constructions over the canonical kernel. |
| Transition systems / semigroups | No pinned forward-pair transition-system or homogeneous kernel-semigroup predicate with the required orientation was found | Add raw-function predicates `TransitionSystem`, `IsMarkovTransitionSystem`, and `IsMarkovSemigroup`; pin `K r t = K s t comp K r s`. |
| Future sigma-field | Mathlib tail sigma-field exists for sequences, but no generic time-indexed future sigma-field | Add `futureMeasurableSpace`; prove the discrete bridge to Mathlib's tail construction. |
| Markov property | No exact kernel-free event conditional-expectation predicate and transition-representation split was found | Add `HasMarkovProperty` and `HasTransitionSystem`; reuse Mathlib `condExp`, `CondIndep`, filtrations, and kernels in all bridges. |
| Discrete path law | Mathlib `Kernel.traj`, `partialTraj`, projective-limit correctness, and conditional-trajectory theorems | Add only the homogeneous specialization `markovChainPathKernel`/`markovChainLaw` and its kernel-power marginal interface. |
| General canonical path law | StochLean's audited Standard-Borel Kolmogorov facade and Mathlib `IsProjectiveLimit` | Reuse; add no Markov-private product-measure or projective-limit object. |
| Irreducibility | Mathlib `Kernel.IsIrreducible Measure.count` and `Kernel.CanReach` | Reuse as the only irreducibility/reachability notions; add strict-positive-return bridges where Klenke differs on the diagonal. |
| Hitting times | Mathlib `hittingAfter` and `WithTop` random-time APIs | Reuse; define only Markov-specific return/hitting events and extended means. |
| Recurrence / Green / excursion | No exact countable-chain statewise package found | Add the Klenke-level predicates and occupation constructions, using canonical path laws and ENNReal sums. |
| Invariant / reversible measures | Mathlib `Kernel.Invariant` and `Kernel.IsReversible` | Reuse unchanged; add normalization, uniqueness, positive-recurrence, and Kac bridges. |
| Periodicity | No countable-kernel return-time gcd interface found | Add `transitionTimes`, `period`, communication propagation, and aperiodicity without a second irreducibility notion. |
| Generic couplings | No exact measure marginal relation plus the required full-TV convention was found | Add the thin coupling relation and event/full-TV bounds; retain Mathlib signed-measure variation as the normalization source. |
| Coalescent chain | No semantic independent-coalescent kernel found | Add product-off-diagonal/absorbing-diagonal construction; do not copy the corrupted Klenke OCR formula. |
| Klenke 18.11--18.13 | No matching countable-chain coupling-to-full-TV equivalence package found | Build from canonical irreducibility, invariant measures, periods, path couplings, and total variation. |
| Q-matrix | No conservative countable-state Q-matrix predicate or kernel-semigroup right-derivative relation found | Add `IsQMatrix`, `exitRate`, and `HasQMatrix`; off-diagonal nonnegativity explicitly requires unequal states. |
| Uniformization | Poisson measures and kernel powers exist; no bounded-Q Poisson-mixture semigroup or safe zero-rate construction | Add the mixture, semigroup/generator proofs, rate-independence theorem, and canonical uniqueness predicate. |
| Feller functions | Mathlib `ZeroAtInftyContinuousMap` | Reuse exactly; define no local C0 type. |
| Feller semigroup | No exact Klenke 21.26 predicate was found | Add the pointwise-at-zero/C0-preserving predicate and induced contraction operator. Do not redefine it by sup-norm continuity. |
| Feller strong-continuity equivalence | Klenke cites external literature; exact Revuz--Yor III, Proposition 2.4 proof text unavailable locally | DEFERRED under the mandatory external-proof policy; no independent replacement proof. |
| Feller RCLL strong-Markov realization | Klenke cites Rogers--Williams III.7ff/8ff and Revuz--Yor III, Theorem 2.7; proof text unavailable locally | DEFERRED under the mandatory external-proof policy; no realization theorem is declared. |

The Markov source scan found no alternative approved implementation of the new predicates or
theorems at the pinned revision. The two external Feller rows are recorded as deferred rather than
treated as permission to invent a proof. All other decisions and source corrections are mirrored
in the final Markov section of `SOURCE_MAP.md`.

## Fourier probability and classical-limit duplicate audit

The active v4.33 pin supplies the canonical measure-first characteristic function, independent-sum
product identities, Gaussian characteristic functions, Levy continuity through
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`, and the scalar iid CLT through
`tendstoInDistribution_inv_sqrt_mul_sum`. These are reused directly. Searches of the pinned
Mathlib tree and full local StochLean tree found no exact Kolmogorov three-series theorem,
Lindeberg/Lyapunov triangular-array package, Lindeberg--Feller theorem, Polya criterion, or exact
multivariate Cramer--Wold CLT bridge.

The surviving local declarations therefore own raw dependent triangular arrays, separated
hypothesis predicates, the finite variance identity, maximum-tail nullness and its eventual form,
positive-scale Lindeberg/Lyapunov conditions, Lyapunov-to-Lindeberg and Lindeberg-to-nullity,
the forward Lindeberg--Feller theorem, ordered-series/truncation semantics, the complete
Kolmogorov three-series equivalence, and a thin PSD multivariate iid CLT bridge. The forward
Lindeberg--Feller proof is an attribution-preserving internal port of the audited Apache-2.0
StatLean proof lineage at exact commit `dd2c4bbc72b7c643e62985d77c84755b31aec9f5`; it imports no
external package. Klenke's externally delegated converse and Berry--Esseen theorem remain deferred
pending recovery of the exact cited proofs.

An independent finite-dimensional Bochner implementation was also audited at Apache-2.0 commit
`58405ecd328cf8383a1c0b53d37605fe61a0b3f6`. Its source closure contains no proof holes or project
axioms, but it is not Klenke's cited proof and targets a different Mathlib revision (plus an
unrelated package dependency in its project manifest). Under the source protocol it is retained
only as a reference: StochLean neither imports it nor exposes its names. Pólya and the exact
moment-determinacy/even-derivative converse remain explicitly identified generic candidates; no
stronger replacement theorem is claimed.

## Levy/SII duplicate audit

| Topic | Active-pin/local result | Decision |
| --- | --- | --- |
| Convolution | Mathlib `Measure.conv` is canonical but does not close the operation in `ProbabilityMeasure` | Add the thin probability-law closure and convolution powers; do not define another measure convolution. |
| Stationary/independent increments | StochLean `HasStationaryIncrements` and Mathlib `HasIndepIncrements` | Reuse and combine only as a predicate; no `LevyProcess` bundle. |
| Convolution semigroup | No exact law-family predicate with the frozen basic/continuous split | Add the two thin predicates without a hidden identity-at-zero assumption. |
| Infinite divisibility | No exact active-pin probability-law predicate | Add positive-integer existential convolution roots. |
| Compound Poisson | Poisson measures and measure bind exist; no finite-intensity compound-Poisson probability law | Add a genuine bind mixture and zero-safe finite-measure entry point; prove common-jump intensity addition by Tonelli and derive infinite divisibility from the resulting semigroup. |
| Levy measure/triplet | No canonical active-pin definitions | Add the minimal atom/integral predicate, derive sigma-finiteness, validate infinite activity with an explicit infinite-mass geometric atomic example, and add data-only fixed-truncation triplets. |
| Levy--Khintchine | No exact active-pin theorem | Implemented entirely inside StochLean: triplet-to-law approximation, weighted canonical-root converse extraction, uniqueness, and the nonnegative specialization. No external Lean package is linked. |
| Stable laws | No matching active-pin law predicates/classification | Project-owned non-Dirac broad/strict/indexed predicates, affine/triplet scaling, index existence and bound, homogeneous jump density, Gaussian endpoint, corrected centering branches, and source-safe exponent expressions are implemented. |

The finite-intensity compound-Poisson API handles `ν = 0` before normalization and proves
`ofFiniteMeasure (r • μ.toFiniteMeasure) = law r μ`; the proof does not use a zero denominator.
The Levy-measure predicate does not store sigma-finiteness and does not install a global instance.

The LS-B08 audit searched the pinned Mathlib Gamma, beta, Mellin, improper-integral, and
trigonometric-integral modules, the complete local tree, and public Lean source search. No existing
oscillatory Gamma integral implementation suitable for the active pin was found. Direct inspection
of Klenke Remark 16.23 exposed a more fundamental source defect: an arbitrary translation keeps
the same Levy measure but adds `i*d*t` to the exponent. `StableExponent.lean` therefore internalizes
the two printed Gamma/trigonometric expressions as project-owned, zero-safe APIs, proves continuity
of the exceptional logarithmic term, supplies the explicit location correction, and proves the
translation obstruction. It deliberately exports no false theorem claiming that a jump measure
alone determines the complete exponent. The 2026-09-07 coverage audit corrects the prior status:
this resolves the source-semantic defect, but **not** the corrected integral-identity theorem.
LS-B08 remains open until the analytic equality with `LevyTriplet.exponent` is proved. No
external package, namespace, or API is retained.

## Brownian/path-regularity duplicate and external audit

The active Mathlib pin contains `ProbabilityTheory.IsPreBrownianReal` and
`ProbabilityTheory.IsBrownianReal` in `Mathlib.Probability.BrownianMotion.Basic`, together with
evaluation laws, covariance, independent increments, Gaussian characterization components,
negation, nonzero scaling, shifts, whole-past shift independence, time inversion, and the exact
centered-Gaussian covariance characterization. StochLean therefore adds no parallel Brownian
object. Its current Brownian module supplies SII/law-level bridges, an explicit piecewise
time-inversion theorem at zero, and the source-facing Gaussian Brownian-bridge transform with its
endpoint, mean, and covariance laws.

The generic active-pin `Mathlib.Probability.Process.Kolmogorov` defines
`IsKolmogorovProcess`/`IsAEKolmogorovProcess` and their measurable representatives, but not the
Kolmogorov--Chentsov Holder-modification conclusion required by the handoff.

The approved external repository `https://github.com/RemyDegenne/brownian-motion` was checked out
at exact commit `314f04a34ff75e18fd383917ae7fe7d77beb1b6f`:

- license: Apache-2.0;
- relevant transitive source closure: 27 Lean modules, 6459 source lines;
- proof-hole/trust scan: no `sorry`, `admit`, declaration beginning with `axiom`, or unsafe
  declaration in that closure;
- exact revision was confirmed by Git;
- a direct stable-v4.33 source build does not pass unchanged because
  `BrownianMotion/Auxiliary/Algebra.lean` redeclares `Set.indicator_apply_apply`, which is already
  present in the active Mathlib pin.

The useful proof closure was subsequently internalized under `StochLean/Internal/Brownian` at that
exact audited revision. Active-pin duplicates such as `Set.indicator_apply_apply` were removed,
imports and namespaces were redirected to StochLean/Mathlib owners, and the resulting source was
rebuilt as part of the ordinary project graph. The external repository is neither imported nor
linked; its exact revision and Apache-2.0 provenance are recorded in the internal directory.

The remaining Brownian document results are project-owned constructions over this foundation and
the pinned Mathlib Brownian API: the canonical continuous coordinate realization, simultaneous
subcritical Holder regularity, covariance characterization, bridge and conditional bridge laws,
Blumenthal zero--one, finite-stopping-time strong Markov cylinders, strict/closed reflection,
Levy's full arcsine CDF, pointwise Paley--Wiener--Zygmund nowhere differentiability, Schauder
uniform convergence, and the basis-independent deterministic Wiener linear isometry.

## Semimartingale active-pin/local/reference audit (2026-09-07)

Continuation audit: deterministic variation reuses Mathlib `eVariationOn`,
`image_range_of_monotone`, `comp_le_of_monotoneOn`, and
`lowerSemicontinuous_aux`, rather than a second total-variation object.
Deterministic UI stopping reuses `Integrable.uniformIntegrable_condExp` and
the existing stopping/filtration owners. Brownian martingales specialize the
already implemented finite-cylinder conditional-independence bridge; Gaussian
moments, finite-time `MemLp 2`, conditional pull-out, and integrability are
proved before expanding squares. No new external code/dependency was adopted.
The 54-declaration audit includes the new load-bearing proof closures.

Searches covered stopping/localization (`IsStoppingTime`, `IsPreLocalizingSequence`,
`Locally`, `stoppedValue`, `stoppedProcess`), path predicates, deterministic variation,
uniform integrability operations, UCP and convergence in measure, simple predictable
processes, and Brownian moments/increment independence.

- REUSE: Mathlib stopping sigma-algebras and localization; canonical `Martingale`,
  `UniformIntegrable`, `TendstoInMeasure`, `eVariationOn`, Gaussian laws/moments and
  independent increments. Existing StochLean process equivalence and path owners remain
  canonical. Generic running suprema were moved out of the Brownian-specific file
  without changing their declaration names.
- BUILD: only missing Protter local-martingale/source bridges, finite endpoint witness,
  caglad/operation bridges, joint partition owner, UCP measurable compact deviations,
  elementary integration with pathwise representation independence, and good-integrator
  continuity/stability. The public stochastic integral/bracket selectors remain absent
  until their existence/construction theorems are proved.
- Gaussian fourth moments reuse the already internalized and audited
  `StochLean/Internal/Brownian/Gaussian/Moment.lean`; no new external closure was copied.
- Git revalidated the local external Brownian snapshot as
  `314f04a34ff75e18fd383917ae7fe7d77beb1b6f`. Its
  `BrownianMotion/StochasticIntegral/DoobMeyer.lean` still contains unfinished proofs
  (for example lines 207, 338 and 625). That file is not trusted or imported. External
  deterministic bounded simple processes and theorem-field integral representations
  are not substitutes for the source Protter construction.
- The dependency graph still permits only Mathlib as an external Lean package. The
  shared Mathlib checkout has a pre-existing modification only to `Cache/Requests.lean`,
  not to its mathematical source files; it was preserved.

See the [active ledger](docs/SEMIMARTINGALE_STATUS.md) for the corrected Klenke mesh,
initial-value safeguards, actual proof coverage and open load-bearing dependencies.

### Continuous-time stopping closure audit (2026-09-07)

- REUSE: Mathlib countable-range bounded optional sampling, stopping sigma-algebras,
  conditional-expectation tower/restriction identities, UI conditional-expectation
  families, Vitali, and discrete martingale convergence. Their proofs are used directly,
  not duplicated as a separate stochastic hierarchy.
- BUILD: upper countable-range stopping approximation capped at a finite horizon,
  continuous-time bounded sampling and its usual-filtration transport, closed/UI
  equivalence via the integer restriction, and arbitrary UI stopping. The exact
  Protter references are I.17 for bounded sampling and I.18 for UI stopping; I.16's
  unbounded terminal statement is not closed by these bounded results alone.
- REFACTOR: generic upper-grid stopping helpers moved from Brownian StrongMarkov to
  `Process/Stopping/Approximation.lean`, preserving all existing public names.
- Single common-event path equality, rather than fixed-time modification alone,
  is used to transport random stopping values. Relative completeness transports
  coordinate measurability; arbitrary null-path assignments are not asserted to be
  jointly progressively measurable.
- REUSE: `IsStable.locally_induction`, diagonal extraction and tail-infimum
  stopping-time lemmas from Mathlib `Probability.Process.LocalProperty`. The
  project proves stability of the canonical UI+cadlag conjunction and separately
  derives an everywhere-monotone fundamental sequence; AE monotonicity is not
  silently equated with the project's stronger witness convention.

### Continuous bounded-localization audit (2026-09-07)

- REUSE: Mathlib `hittingAfter` remains the single hitting-time definition. Its
  existing attainment and stopping results require discrete/well-founded time;
  the new continuous-time results prove closed-target attainment using the closed
  infimum, and closed absolute-level measurability using compact maxima and the
  existing countable running supremum.
- BUILD: no-overshoot with an explicit initial bound, level times tending to infinity,
  everywhere-continuous indistinguishable versions, actual bounded localization,
  and bounded masked fundamental sequences giving local finite-time L2.
- BUILD: relative completeness transports stopping times after AE changes. An
  AE-monotone sequence is normalized on one initial null event, preserving its
  coordinates AE and its random lifetime, before the bounded refinement.
- Source safeguards remain enforced: centering does not assume initial L1; the
  original unmasked process is not claimed bounded for arbitrary initial values.
  The general-local construction uses the canonical Protter mask, not a new hierarchy.
- No external proof source or dependency was adopted for this closure.

### Elementary-integration L2 prerequisites (2026-09-07)

- REUSE: Mathlib conditional-expectation Lp contraction, the existing StochLean
  bounded optional sampling, discrete predictable integral and discrete brackets.
- BUILD: Lp stopping-value bounds, finite-time L2 stopping preservation, ordered
  stopping-time filtration reindexing and sampled martingales, the discrete
  integral isometry and common coefficient energy estimate.
- BUILD: normalization of coefficients on zero-length source stopping intervals.
  An extensional process bound does not bound irrelevant representation coefficients;
  the normalized representation has the same process and integral and satisfies the bound.
- This checkpoint supplied prerequisites only. The later closure below proves
  the random-partition estimate and the actual L2/local-L2 examples.

### Brownian reverse-martingale strong QV, fixed horizon (2026-09-07)

- REUSE: pinned Mathlib Gaussian-process covariance characterization and
  finite-dimensional law uniqueness, conditional-expectation algebra and
  probability-limit uniqueness; the existing project-owned Levy downward theorem.
- BUILD: deterministic path reflections, exact finer-square-sum invariance,
  joint Brownian sign symmetry and conditional centering of cross increments.
  The actual square sum is identified with the conditional expectation of the
  terminal square on its future sigma-field, not assumed to be a reverse martingale.
- BUILD: fixed-horizon a.s. convergence under arbitrary nested vanishing mesh.
  Coordinatewise measurable versions are transferred on the countable endpoint
  set; no uncountable intersection of null events is used. Lossless restrictions
  of source infinite partitions are included.
- Common-event all-times extraction and independent Brownian cross-QV are not
  claimed by this closure. No external dependency or new bracket owner is added.

### All-times Brownian paths and infinite variation (2026-09-07)

- REUSE: Mathlib dense-set monotone approximation, Brownian deterministic shifts,
  independent Gaussian product laws and covariance algebra, and the existing
  deterministic bounded-variation zero-QV theorem.
- BUILD: repeated-endpoint invariance; exact stopping/restriction transport;
  monotone completed-cell dense extraction. The source infinite-restriction
  covariation FV bound is now proved without a changed partition convention.
- BUILD: one-event all-times Brownian QV for each prescribed admissible sequence;
  normalized sums of independent Brownian processes and all-times zero cross-QV.
  No raw partial-cell sum is assumed monotone, and no uncountable null-set
  intersection is taken. The event is not claimed independent of the partition sequence.
- BUILD: actual uniform infinite partitions, their global adjacent-gap bound and
  dyadic admissibility; infinite variation on every nondegenerate compact interval
  via a countable family of shifts. No external source code was adopted.
- This closes the native Klenke 21.64--21.65 / Exercise 21.10.1 and Protter I.28--I.29
  chain, but does not construct the general stochastic bracket or integral.

### Elementary L2 estimate and martingale semimartingale examples (2026-09-07)

- REUSE: the canonical stopping-time sigma-fields, UI optional sampling, conditional
  Lp contraction, discrete predictable integral and its existing discrete QV owner.
- BUILD: sampling on each source finite stopping partition extended constantly
  after its last endpoint. Endpoints are everywhere finite but need no deterministic
  bound. `X(min(tau,T))` is the conditional expectation of `X_T` in the original
  `F_tau`; coefficients are not silently moved to the smaller `F_(tau min T)`.
- BUILD: exact elementary/discrete sum equality, orthogonality of the initial term
  to the future transform, and the sharp square-integral energy bound. Empty-cell
  normalization supplies bounds on the effective coefficients from the process bound.
- BUILD: Markov's inequality implies source continuity. The L2 martingale theorem
  requires only finite-time L2, and masked localization proves the locally L2 and
  continuous-local examples without any initial L1/L2 assumption in the latter case.
- BUILD: small-exceptional-set patching and the pre-localization corollary, plus the
  strict-before-lifetime form of Protter II.6. Random lifetimes need not be stopping
  times. Adapted/cadlag hypotheses remain explicit at this patching boundary.
- Sources checked directly: Protter printed pp.51--55 (PDF pp.62--66), including the
  standing usual-filtration hypotheses. No external stochastic implementation was used.
- The general caglad stochastic integral, FV examples, Brownian filtration transfer,
  and the remaining stability/decomposition results are not supplied by this block.

### Finite variation and measure/filtration stability (2026-09-07)

- REUSE: Mathlib local/global bounded variation and `eVariationOn`, stopping-time
  sigma-fields, absolute continuity, convergence-in-measure subsequence criteria,
  and nonnegative dominated convergence under the counting measure.
- BUILD: source integral measurability without coefficient integrability, pathwise
  variation estimates including the initial term and normalized empty intervals,
  and finite-variation/Poisson/decomposable semimartingale examples.
- BUILD: absolute-continuous finite-target-measure transport, finite-mass countable
  mixtures and normalized probability mixtures, and Stricker filtration shrinkage.
  Countable measure sums are evaluated on arbitrary deviation sets, so an unnecessary
  extra measurability premise is not imposed on the mixture convergence lemma.
- The Poisson cadlag bridge is derived from the existing monotone/right-continuous
  path predicate. Adaptedness to the chosen usual filtration remains explicit.
- Source checks: Protter printed pp.53--55 (PDF pp.64--66). Only actual one-way
  decomposition implications are claimed. No new external source code or dependency
  is used; no random Stieltjes integral or general decomposition is substituted by
  a theorem-shaped assumption.

### Left limits, source stopping and predictable measurability (2026-09-07)

- REUSE: Mathlib `Function.leftLim`, closed-neighborhood cluster-point arguments,
  measurable pointwise limits, stopping sigma-fields and the rectangle-generated
  predictable sigma-field. No alternative predictable owner is introduced.
- BUILD: source `X_(0-) = 0`, jumps, caglad left-limit paths, adapted left limits,
  and exact `T-` stopping/patching, including common-event indistinguishability.
  Infinite lifetimes preserve all finite coordinates without evaluating at infinity.
- BUILD: strict-past predictable grids; left-continuous adapted processes are
  predictable, and the source caglad-generated sigma-field equals the canonical one.
  AE path regularity is handled by an actual indistinguishable predictable version,
  not by asserting measurability of arbitrary exceptional time dependence.
- BUILD: left-endpoint stopping coefficient measurability, elementary step-path
  regularity and source simple-process adaptedness/caglad/predictability.
  Repeated endpoints and unbounded finite coefficients remain legal.
- This closes basic predictable source ownership and simple-process regularity,
  not UCP density, stochastic-integral construction, optional classification or
  the Chapter III decomposition theorems. No external proof code was copied.

### Random variation and Stieltjes integration (2026-09-08)

- REUSE: Mathlib `variationOnFromTo`, locally bounded variation, Stieltjes functions
  and locally finite measures, finite-measure pi-system generation, Bochner integrals
  and dominated convergence. Positive/negative components use these existing owners.
- BUILD: local-BV right continuity of variation and right-continuous partition-sum
  convergence; adapted variation/Jordan processes and a common-event cadlag/FV version.
- BUILD: measurable Stieltjes measure families on nonnegative time, without probability
  CDF normalization or global finite mass. Finite-horizon restrictions need only past
  coordinates. Finite-fiber kernel integration is proved by measurable mass truncation;
  fiberwise finiteness is not confused with a uniform bound over samples.
- BUILD: actual pathwise FV integrals, the separate source initial term, linearity,
  bounds, dominated convergence, ambient measurability and adaptedness for progressive
  integrands. Nonintegrable inputs retain Mathlib's totalized convention; measurable
  bounded inputs on compact time intervals have proved integrability.
- Still open: integral path regularity, source elementary agreement, change of variables
  and I.52 differentiation/polar density. No external stochastic proof code was copied.

### FV integral path regularity (2026-09-08)

- REUSE: Bochner dominated convergence, interval restriction/union and singleton
  integrals, and canonical Mathlib variation suprema.
- BUILD: primitive right continuity and open-endpoint left limits for measures
  with atoms; the jump is atom mass times integrand. A Dirac-at-one regression
  checks a nonzero jump instead of testing only continuous/atomless examples.
- BUILD: variation arithmetic from actual finite-partition sums and local BV of
  real primitives from positive/negative integrand parts. Locally pathwise
  integrable Stieltjes integrals are cadlag and locally BV; progressive integrands
  give semimartingales without an expected-variation or initial-integrability premise.
- This advances the preceding block's path-regularity gap. Elementary agreement,
  C1 calculus and random differentiation/polar density remain separate obligations.

### FV elementary-integral agreement (2026-09-08)

- REUSE: finite Bochner sums, indicator integrals, finite Stieltjes interval masses,
  and the existing source simple-predictable representation/independence owner.
- BUILD: stopped-endpoint interval formula, finite-step local integrability and
  exact agreement of pathwise Stieltjes and elementary integrals. The initial
  value is retained separately. There is no bounded-coefficient, distinct-endpoint
  or deterministic-endpoint restriction.
- Regressions prove zero contribution for repeated endpoints and intervals lying
  after the horizon. This closes the earlier elementary-agreement gap, not UCP
  density/extension, C1 calculus or I.52 differentiation/polar density.

### Source caglad FV-integrand domain (2026-09-08)

- BUILD: a left-continuous path with right limits is locally bounded, by combining
  the two one-sided filters. A compact finite subcover supplies actual horizon bounds.
- BUILD: progressive finite-horizon sections and those bounds imply pathwise
  Stieltjes integrability for adapted everywhere-caglad source integrands. Their
  FV integrals are progressive and semimartingales under usual conditions.
- Neither path integrability nor an expected-variation bound is added as an
  unproved source premise. This does not construct the general semimartingale integral.

### FV integral jumps (2026-09-08)

- REUSE: Stieltjes atom masses and the proved open/closed-endpoint primitive limits.
- BUILD: subtracting the two canonical Jordan atoms gives the integrator jump;
  their weighted primitive jumps give the full FV integral jump formula.
- Time zero uses the separate source initial term, not an artificial measure atom.
  Common-event all-times statements follow pathwise, without an uncountable null-set union.
- The adapted-caglad version derives its local integrability from the preceding block.

### FV integral stopping (2026-09-08)

- REUSE: monotone time-change variation, Stieltjes initial-interval masses and
  finite-measure uniqueness on the Iic generating family.
- BUILD: canonical total/positive/negative stopped measures equal restriction to
  the closed horizon. This proves both FV instances of Protter II.12 pathwise,
  even for a random lifetime that can be infinite.
- BUILD: cutoff preserves adaptedness, caglad paths and canonical predictability.
  The source initial value and endpoint atom are retained; no integrability or
  stopping-time premise is needed for the purely pathwise totalized identities.
- Source regularity and the resulting semimartingale statement are proved with
  their actual stopping-time hypotheses, separately from those identities.

### FV integral locality and UCP continuity (2026-09-08)

- BUILD: full-integral linearity, path equality/indistinguishability transport,
  a compact-horizon operator bound retaining `|X_0|`, and uniform convergence.
- REUSE: subsequence convergence criteria and finite-measure convergence of
  measurable event indicators. The latter is applied to measurable output
  compact deviations, not to arbitrary outer-measure sets.
- BUILD: equivalence of compact-deviation convergence and ordinary uniform path
  convergence, UCP subsequence converse and right-continuous limit uniqueness.
- BUILD: actual UCP continuity of source adapted-caglad FV integration, with no
  expected-variation bound. Given source simple approximations, their elementary
  integrals converge to the canonical FV integral. The later II.10 entry supplies density.

### Continuous-FV C1 calculus (2026-09-08)

- BUILD: unique nonempty cells despite repeated endpoints, left-step uniform
  approximation and Stieltjes left sums, including the moving terminal partial cell.
- REUSE: compact uniform continuity, one-dimensional mean-value bounds, the proved
  partition variation bound, concrete dyadic restrictions and the ordinary FTC.
- BUILD: first-order remainders tend to zero against finite path variation;
  actual Stieltjes integral limits prove Protter I.54 and its substitution corollary.
  C1 composition preserves local BV, with common-event process versions.
- Regression retains the nonzero initial term in the full self-integral and the
  initial integrand value for an empty partition. This is not Klenke 21.62's
  C1 composition formula for a general nonzero quadratic-variation path, which
  is now separately proved in the C1 quadratic-variation increment below.

### Protter I.53 tagged random-partition approximation (2026-09-08)

- BUILD: arbitrary closed-cell tags, including either endpoint, converge uniformly
  for continuous integrands. Repeated/empty cells and the initial term are retained.
- REUSE: unique cells, finite-step integrability and the established FV operator
  bound. The resulting tagged sums converge to the canonical Stieltjes integral,
  uniformly over the terminal partial cell.
- BUILD: sample-dependent finite partitions/tags and AE mesh/path conditions give
  the source random-partition theorem on one common event. No stopping-time or
  adaptedness assertion is made for future tags or their step functions.
- Regressions exercise a right-endpoint tag and a repeated zero cell.

### Source simple-predictable refinement and algebra (2026-09-08)

- REUSE: Mathlib's stopping-time minima/maxima, `measurableSet_inter_le` and
  stopping-time comparison events. These yield actual coefficient measurability
  at the new left endpoint without usual-filtration assumptions.
- BUILD: a finite common-refinement witness using repeated min/max splits; old
  endpoints cannot lie inside a refined cell. Random coincidences and empty cells
  remain legal. The construction establishes existence, not optimal partition size.
- BUILD: full source repartitioning invariance, zero-preserving binary Borel
  operations, addition/product/scalar closure and elementary bilinearity. The
  representation-independent source integral remains the sole elementary owner.
- REFACTOR: the four existing integrator-linearity declarations move unchanged
  from good-integrator `Stability.lean` to `SimplePredictable/IntegratorAlgebra.lean`.
  Public names/statements remain unchanged; no duplicate higher-layer owner is added.
- Regressions cover different terminal times, independent initial coefficients,
  multiplication at time zero and zero splits introducing repeated endpoints.
- This closes algebra/refinement, not the source density or general integral construction.

### Source cutoff and semimartingale stopping (2026-09-08)

- REUSE: common stopping-time refinement, original endpoint comparison sigma-fields,
  pure interval-sum representation independence and common-event stopped-path regularity.
- BUILD: the full source simple class is closed under `H 1_[0,τ]`, including
  infinite `τ`; cap at the representation's finite terminal time before constructing
  the new stopping partition. This is a cutoff, not a frozen integrand.
- BUILD: the elementary stopping identity for arbitrary raw integrators, with no
  finite-variation, continuity or measurability premise. Initial terms remain separate.
- BUILD: stopping preserves good integrators directly from the epsilon/delta source
  criterion. Existing usual-filtration adaptedness yields total/ordinary semimartingale
  closure; deterministic stopping also proves total implies ordinary without usualness.
- Regressions retain the initial term under zero stopping, preserve the whole integral
  under infinite stopping and retain the value at the closed finite endpoint.
- The constructed general integral and its Protter II.12 identity remain separate.

### Source linear operator and nonzero-limit continuity (2026-09-08)

- REUSE: Mathlib `Submodule`/`LinearMap` and `TendstoInMeasure`, the existing source
  predicate and elementary integral, proved full source algebra and epsilon/delta criterion.
- BUILD: the exact source submodule and elementary linear operator into raw random
  variables, with congruence, negation and subtraction laws. This is not a bounded
  replacement domain or an additional stochastic integral owner.
- BUILD: uniform-in-input difference estimates, a Cauchy-in-measure bound and
  convergence in measure for uniform source convergence to any simple integrand.
- The operator is not silently assigned an L0 quotient or a stronger topology.
  UCP completeness/extension and a selected general integral remain open; density is
  supplied by the subsequent corrected II.10 construction.
- Regressions retain arbitrary initial values for a constant integrator and verify
  source self-subtraction without regularity or measurability assumptions on the integrator.

### Right-continuous hitting and first-exit bounds (2026-09-08)

- REUSE: Mathlib `hittingAfter`, its strict-before and no-hit characterizations,
  right-continuous-filtration stopping criterion, dense right-approximating sequences
  and infimum approximations. No second hitting-time owner is introduced.
- BUILD: countable dense detection for open targets, strict-hit measurability,
  stopping under right-continuous filtrations, and a common-null-event usual version.
  Only measurable open sets are required of the state's measurable structure.
- BUILD: finite-hit closure membership, closed-target attainment and norm exit bounds.
  The stopping value is not asserted to belong to an open target or to have no overshoot.
- Regressions exhibit a continuous boundary hit and a jump overshoot. Rendering
  Protter II.10's printed p.57 also confirmed a missing-first-interval lower index
  in its final finite sum; constant no-hit/empty-tail regressions certify the failure.
- These hitting lemmas are prerequisites, not substitutes for the integral theorem.
  The subsequent maximal, full UCP-input and corrected density closures are recorded below.

### Source elementary integral process (2026-09-08)

- REUSE: the existing source elementary integral and its representation independence,
  Mathlib stopped processes, source coefficient-revelation measurability and the
  usual-filtration stopped-process theorem. No second general integral is introduced.
- BUILD: canonical `J_X(H)` at deterministic stops, its initial/terminal values and
  source linearity; cadlag finite sums, common-event cadlag paths and adaptedness.
  Original left-endpoint coefficients are revealed only after that endpoint; the
  corresponding increment is zero before it. No future measurability is presumed.
- BUILD: arbitrary raw-time stopping, legal source cutoff and finite stopping-value
  identities; reuse the existing FV agreement to identify the whole elementary process.
- Regressions distinguish closed and open source unit intervals and retain `H_0 X_0`
  when stopping at zero. Completion and extension remain open; density is supplied below.

### Elementary maximal estimate and uniform-to-UCP continuity (2026-09-08)

- REUSE: the source `J_X(H)`, its usual-filtration adaptedness and cadlag paths,
  the existing first-exit owner, actual cutoff closure and terminal good-integrator bound.
- BUILD: compact strict-exceedance events are bounded by first-exit stopped-value
  events on the common right-continuity event. This uses AE measure monotonicity,
  not unproved supremum measurability, no overshoot or maximum attainment.
- BUILD: maximal neighborhood estimates, both total (uniform over horizons) and
  ordinary (at a fixed horizon), and uniform-input convergence to any simple limit
  implies UCP convergence of the actual elementary integral processes.
- BUILD: strict real-threshold events characterize the original ENNReal compact
  deviation definition, including its infinite-threshold case. No replacement UCP owner.
- This is the first half of II.11; its second half and II.10 density are recorded next.
  Completion and extension remain open. The zero-horizon event still detects `X_0`.

### Full source UCP continuity (2026-09-08)

- REUSE: the same Mathlib hitting-time owner and strict-hit characterization,
  dense left-approaching sequences, source initial coefficient sigma-fields,
  legal cutoff and the proved maximal estimate. No external proof code was copied.
- BUILD: countable detection for left-continuous open hits with the start time
  explicitly included, stopping under a right-continuous filtration, and the
  first-exit upper bound on `{tau > 0}`.
- BUILD: F0-event masks of the full source class, exact masked elementary
  identities, actual uniformly bounded first-exit truncations, and pre-exit agreement.
- BUILD: quantitative UCP neighborhoods, Protter II.11 at zero and every simple
  limit, and UCP-Cauchy control. The input horizon can be any `S > T`, which covers
  infima at an unattained boundary and right jumps at zero.
- Regressions cover an isolated oversized initial value, its masked truncation,
  and a right jump with hitting infimum zero. No positive separation of stopping
  endpoints, bound on the original coefficients or normalized initial value is assumed.
- UCP completeness and a general integral limit remain open; corrected density follows below.

### Right-limit and nonaccumulation density prerequisites (2026-09-08)

- REUSE: Mathlib's strict `rightLim` selector, limit uniqueness, closed-neighborhood
  cluster arguments, monotone convergence and filtration right-continuation.
- BUILD: right-limit left convergence without excluding a bottom time; cadlag
  regularity, positive-time reconstruction and common-event transport. The original
  initial value is not silently replaced by its right limit.
- BUILD: adapted right limits from actual sequences in `(t,u)` for every `u > t`,
  then the intersection sigma-field; a usual-completeness version for AE caglad paths.
- BUILD: positive separated consecutive samples force finite times to diverge;
  the extended-time version includes sequences that actually reach infinity.
  The finite-accumulation contradiction uses the path's finite left limit.
- Isolated-initial regressions distinguish `H_0` from `H_(0+)`. The actual adaptive
  stopping partition and corrected density are constructed in the next entry.

### Corrected source simple predictable UCP density (2026-09-08)

- REUSE: the existing hitting/stopping owners, actual adapted right limits, proved
  nonaccumulation, finite stopping coefficient measurability and vanishing early-exit
  probabilities under a finite measure. No external library or density axiom is used.
- BUILD: recursive first exits of `X - X^tau`, ordered stopping times with finite
  strict increments and common-event divergence to infinity; the source left-limit
  cell error bound includes the right endpoint without requiring an open hit there.
- BUILD: finite capped partitions of extended stopping sequences and actual simple
  representations with F_T-measurable finite coefficients. Every cell from index zero
  is present; coefficients at infinite uncapped times are never evaluated.
- BUILD: Protter II.10 on the full adapted/common-event-caglad source domain under
  usual conditions and a finite measure. A proved probability diagonal selects each
  finite number of cells; thresholds shrink and caps grow. No uniform bound on the
  original integrand or its coefficients is added to the theorem.
- The regression applies the actual representation and proves exact constant-one
  reconstruction on its cap, correcting the printed missing-first-interval formula.
- The following increment closes UCP completeness; the general integral remains open.

## Sequential UCP completeness

- REUSE: Mathlib's complete extended-metric `UniformFun`, geometric Cauchy criterion,
  pointwise `limUnder`, uniform-Cauchy convergence and interchange-of-limits theorem.
- BUILD: existence of a filter limit passes through uniform convergence without
  assuming convergence of the approximants' limits; locally uniform cadlag closure.
- BUILD: Cauchy criterion for the existing UCP owner, a summable-probability
  common-event uniform Cauchy subsequence, and convergence of the full sequence.
- BUILD: actual adapted cadlag limit under usual conditions and a finite measure.
  One initial-measurable null-set reset gives everywhere cadlag paths and pointwise
  measurable limits. Compact-deviation measurability follows from the existing
  dense-time/right-continuity theorem, not a bare uncountable supremum claim.
- No new stochastic function-space quotient, assumed integral operator, external
  dependency, or general stochastic-integral selector is introduced here.

## Constructed Chapter II stochastic-integral extension

The Chapter II general-integral extension is now independently constructed in
`Semimartingale/StochasticIntegral.lean` and its construction/algebra/continuity/
initial-value modules. It reuses the verified source density, elementary integral
and UCP-completeness owners. Every simple approximation converges to the same
cadlag process up to indistinguishability; no operator or existence theorem is
installed as a field. Simultaneous UCP diagonals establish continuity on the whole
adapted-caglad domain. Initial values are retained without L1 assumptions.
The selector has legal-domain proof arguments only, with proof irrelevance proved.
No arbitrary-predictable Chapter IV integral or stochastic bracket is introduced.

## General-integral finite-variation agreement

The general integral now reuses the pathwise FV integral through proved source
UCP agreement and uniqueness (Protter II.17). Null-set resets and independently
proved integrator indistinguishability invariance cover the common-event FV
source domain; no everywhere-path premise is imposed by the final pathwise theorem.
The deterministic FV self-integral theorem is reused unchanged for a general-
integral regression, retaining the initial square.

## General-integral stopping

Protter II.12 reuses the existing source elementary stopping identity and the
canonical stopped process. New UCP event bounds prove stopping and cutoff
continuity even for arbitrary raw possibly infinite times. Legal stopping times
then give the three general-integral identities by approximation and uniqueness.
Common-event caglad cutoff regularity reuses the deterministic cutoff theorem.
Regressions cover zero stopping (initial product retained) and infinite stopping
(identity without an infinity evaluation). No new stopping-time owner is introduced.

## General-integral jumps

Protter II.13 reuses the canonical source left-limit/jump owner. Finite stopped
summands have proved strict-left limits, including the closed right endpoint;
finite-sum algebra gives the elementary jump formula. Uniform convergence controls
the values of existing filter limits, and hence source left limits and jumps.
Two actual locally uniform subsequences give the general jump identity for all
times on one full-measure event, without assuming right continuity of jump processes.
The zero-time and right-partition-endpoint regressions retain source conventions.

## General-integral absolutely continuous measure changes

Protter II.14 reuses the source semimartingale measure-change theorem and constructs
the integral identification by approximation. A new event-measure transfer lemma
uses actual source-measurable covers of a summable subsequence, Borel-Cantelli and
finite target measure. Thus UCP transfer needs neither measurable compact deviations
nor an invalid outer-measure continuity claim. Target usualness is not transferred
from source usualness: it remains explicit. The zero-target-measure completeness
regression demonstrates the distinction, and the initial-product regression checks
the measure-change identity at time zero. No new probability-space owner is introduced.

## General-integral mixture and filtration invariance

Protter II.15 and II.16 reuse the same canonical stochastic integral. Countable
mixture mass and positive-component absolute continuity are proved from Mathlib's
measure-sum owner. Usualness transfers toward a dominating measure, so mixture
usualness is derived from a positive-weight component. Two half-weights construct
the two-probability common version; a two-Dirac regression excludes zero-weight
domination. Filtration invariance uses Mathlib's pointwise infimum, with proved
adaptedness, right continuity and initial completeness. A common source approximation
in that intersection has exactly equal elementary integrals after transport. Neither
a larger union filtration nor an additional integral hierarchy is introduced.

## General-integral local behavior

Protter II.18 is proved directly from the constructed approximants, avoiding any
implicit completion of a conditional measure. The existing density theorem is now
a wrapper around the stronger zero-path-preserving construction, with its original
statement unchanged. Pathwise elementary locality reuses the interval-increment
identity, including unbounded coefficients and repeated endpoints. Subtraction and
actual uniform output subsequences yield integral locality on arbitrary whole-path
agreement events. Individual-path Stieltjes agreement plus uniform FV continuity
give the finite-variation-event assertion without a full-probability FV premise.
Regressions expose arbitrary selected events and impose no initial measurability.
Both assertions of the stopped-interval corollary are now proved.

The corollary's path-agreement assertion is now proved. It reuses whole-path locality
and the canonical cutoff/stopped-process owners, with differences rather than a new
interval-integral definition. Right continuity recovers the integrator's excluded
left endpoint, including when the upper endpoint is infinite. A non-right-continuous
initial-spike regression shows that this step cannot be dropped. A second regression
allows arbitrary distinct initial integrand values on `(0,infinity]`.

The FV-interval proof reuses Mathlib's exact one-sided variation/jump formula.
Open-interval BV becomes closed-interval BV without deleting the terminal jump.
Monotone clamping and subtraction of a constant give BV of the stopped increment,
with a finite-subhorizon argument when the upper endpoint is infinite. Existing
whole-path FV locality and the stopped-difference identity identify the integral
with the one canonical Stieltjes owner. A unit endpoint-jump regression guards the
open/closed distinction; a linear-path regression checks the local, not global,
variation requirement on an unbounded horizon.

## General-integral integrator algebra

Negation/subtraction of good integrators and total/ordinary semimartingales are
derived from the existing scalar/additive stability, not from decomposition.
Elementary process linearity is derived from the existing source finite-sum owner.
Common simple approximants and UCP uniqueness give general-integral addition,
scaling and subtraction in the integrator. Initial-value regressions distinguish
the uncentered sum from the centered difference of stopped processes. This adds
no arbitrary-integrator UCP-continuity or semimartingale-preservation assumption.

## General-integral associativity and semimartingale preservation

Protter II.19 is built from the project's existing finite source integral, actual
UCP extension and good-integrator predicate. Common partitions prove the exact
cell-increment identity and elementary associativity for arbitrary integrators.
Fixed elementary integrands act continuously on UCP-convergent adapted cadlag
integrators. This finite-sum result is not continuity in a varying integrator
for arbitrary general integrands. Compact bounds and measurable left-continuous
deviations prove multiplication by a fixed caglad process is UCP-continuous;
the separate initial value is included. AE-measurable deviations suffice for
the subsequence converse, using measurable representatives and AE event equality.

Simple-outer associativity is proved before semimartingale preservation. Uniform
simple test inputs, multiplied by the fixed integrand, converge to zero in UCP;
general integral continuity then proves the good-integrator condition at each
finite horizon. A second approximation proves full Chapter II associativity.
No decomposition, closure theorem or initial integrability is assumed. The FV
remark follows from the canonical Stieltjes owner on individual FV paths.
Regressions retain the triple initial product, detect an isolated initial spike
in compact deviations, and require FV only on an arbitrary event.

## Bounded-integrand L2 martingale preservation

The bounded step of Protter II.20 reuses the exact existing source L2 estimate,
including `H_0 X_0`, and the project's superlinear-envelope criterion with the
actual square envelope. Uniform second moments imply L1 uniform integrability;
Vitali convergence and set-integral identities prove martingale closure under
coordinatewise probability limits. No uniform-in-time L2 bound is assumed.

Source bounded martingale preservation is proved for random finite endpoints
without deterministic endpoint bounds. Raising endpoints to the conditioning
time permits the stopping-sigma-field tower argument. Empty-cell coefficients
are normalized before inferring coefficient bounds from the process bound.
Scalar interval projection preserves the source class and UCP convergence;
the original integrand need only satisfy its bound on one common AE event.
Initial-value and unbounded-unused-coefficient regressions are included.

## General locally-L2 martingale preservation

Protter II.20 is derived using the existing Mathlib `Locally` convention, including
its initial-event mask. No replacement local-martingale hierarchy is introduced.
Open norm exits of an everywhere-caglad adapted version increase to infinity;
their proof uses compact bounds, not a false open-target attainment claim.
The positive-exit mask gives bounded closed cutoffs without an initial-value bound.
Pathwise source identities and UCP contraction prove mask commutation in both
integral variables. The minimum of the two existing localizer families supplies
L2 witnesses for the original integral, rather than assuming preservation as a
property of a chosen integral. Finite-time L2 stability and indistinguishability
transport use actual optional sampling and conditional expectation.
Regressions distinguish zero from positive lifetimes and allow arbitrary finite
initial random values with no L1 or L2 hypothesis. General local-martingale
preservation beyond locally-L2 remains open, as deferred in Protter III.33.

## Random left sampling and continuous-integrand Riemann limits

The process sampler reuses the deterministic `TimePartition.leftStep` owner and
the source `SimplePredictableRep`; there is no second integral construction.
AE left-continuous stopping-value measurability follows from the existing
indistinguishable predictable version and stopping-sigma-field completeness.
Compact deviation contracts under arbitrary left sampling. For continuous paths,
actual compact-uniform convergence follows from eventual horizon coverage and
vanishing mesh, without nested partitions or a deterministic rate. UCP density
then proves the integral limit. Increment-only sums remove the initial product;
zero-time cutoff and subtraction identify this with the source left-limit integral.
The original continuous argument alone does not cover jumps. A unit jump inside a cell gives
an explicit unit sampling discrepancy even for a small cell, preventing an invalid
uniform integrand argument. Constant-integrator sums vanish despite nonzero initial values.

## General cadlag/caglad Riemann limits

Full Protter II.21 is now derived from the existing source integral. The UCP
right-limit transformation is controlled by the canonical compact deviation on
a larger horizon. Both endpoint projections use the original partition, allow
repeated endpoints, are capped at the horizon, and have error at most its mesh.
Finite interval-increment representation independence supplies their exact sum
formulas for arbitrary integrators, before any semimartingale hypothesis.
Uniform convergence of right-stopped paths uses only right continuity at the
limiting stopping value. It also makes the initial-spike contribution vanish.
The general proof derives a uniform deviation bound from convergence for every
selection of a sampling partition; pointwise row convergence alone is not used
as a substitute for uniformity. Adaptedness and cadlag regularity supply measurable
deviations when converting pathwise convergence to UCP. The double-limit lemma
itself needs neither measurable events nor finite total mass.
Regressions distinguish ordinary and strictly upper projection at time zero,
retain the exact first-cell initial-spike contribution, and verify the zero
initial value of the source-left-limit integral without initial integrability.
No external package, replacement UCP owner or second stochastic integral is added.

## Canonical raw quadratic variation

The raw bracket is an algebraic definition from the already constructed integral,
available only under a semimartingale witness and usual conditions. Proof
irrelevance is definitional; indistinguishable integrators give indistinguishable
brackets. Left-limit algebra explicitly requires zero-preserving scalar maps
so that the source time-zero convention is not lost in the jump-square proof.
Random square sums reuse the pure `quadraticVariationSum` owner and add `X_0^2`
once. Their exact telescoping formula and II.21 give UCP convergence. Endpoint
exhaustion is proved by measurable stopping events; no measurability of arbitrary
path deviations is silently assumed.
The source's brief monotonicity argument is expanded using upper endpoint
projection: only the completed-cell square sums are asserted monotone, and their
limit is identified using right-side evaluation of a locally uniform subsequence.
This works for jumps, not merely continuous paths. Self-stopping compatibility
follows from actual partition-sum stopping and UCP uniqueness. Raw square sums
and zero-stopped brackets retain the original initial square in regression tests.
Mixed covariation and mixed stopping are now proved in the next increment.
No second normalized or predictable bracket is introduced.

## Polarized mixed covariation, product formula and one-sided stopping

The sole mixed owner is half the square bracket of `X+Y` minus the two individual
square brackets. Pure mixed increment sums plus `X_0 Y_0` converge to this owner
by the three square-sum limits. UCP uniqueness proves both-variable linearity
and self-covariation agreement with raw QV. Finite-variation paths follow from
the three increasing square brackets, not from monotonicity of mixed brackets.
Source left-limit addition gives the common-event jump-product formula.
Actual finite-cell telescoping and II.21 give integration by parts and the
product semimartingale theorem, without integrator-continuity assumptions.

Mathlib's `discrim_le_zero`, rational density and closedness of a polynomial
inequality are reused to prove the increment Cauchy--Schwarz bound. The countable
intersection ranges only over rational scalars: the QV monotonicity and algebra
already hold for every time on each event. This supplies one event for all
intervals, not an uncountable intersection of probability-one events.
The printed sign in Protter II.25's discriminant argument (p.69/PDF p.80) is
incorrect; the formal proof uses nonpositive discriminant. The weighted
total-variation-measure conclusion is completed in the next block.

Both-argument stopping of finite sums is exact. Single-argument stopping is
instead deduced from the increment bound and flat stopped square brackets,
then simultaneous stopping and idempotence. A one-cell continuous-path example
formally refutes the incorrect finite-sum single-argument identity. Constant
mixed sums and zero-stopped mixed brackets retain the initial product, with
no initial integrability assumption.

## Weighted Kunita--Watanabe and the initial term

Mathlib finite-sum square-root Cauchy--Schwarz bounds all ordered variation sums.
Their supremum gives the canonical total-variation measure's interval bound.
The difference of two ordered Stieltjes functions is itself a Stieltjes function:
this yields measure order from increment order, avoiding any unproved extension
from an interval generating family. The resulting inequality `2 r |da| <= r^2 db + dc`
holds as an order of sigma-finite measures.

Density order follows from Mathlib's set-lower-integral comparison theorem and
the actual Radon--Nikodym integral identities. Scalar/additive RN identities,
a countable absolute-rational intersection, polynomial continuity and the correct
discriminant sign give the density Cauchy--Schwarz bound. Mathlib Holder then
proves the weighted lower-integral inequality, including zero and infinite energies.
There is no silent substitution of a totalized Bochner integral for a divergent
positive integral, nor a finite-total-mass assumption on the half-line measures.

One event supplies genuine Stieltjes realizations of both canonical square
brackets, the mixed bracket's variation measure, both absolute-continuity results
and the inequality for every measurable weight pair. Initial values are handled
separately: quadratic domination is stable under addition, and scalar Dirac
triples satisfy the same inequality. Adding the initial absolute product and
squares therefore preserves the theorem. No stochastic bracket is redefined.
The expectation/Lp corollary is now exported as well. A new measurable lower-
integral lemma uses Mathlib's finite-fiber measurable sections and simple-function
approximation, followed by an increasing finite-measure exhaustion. Fiberwise
finite mass is not confused with uniform kernel finiteness. Adapted initial
null-event resets yield genuine Stieltjes realizations of the canonical brackets;
their energies are measurable for jointly measurable weights with no adaptation
requirement. Mathlib Holder and the almost-everywhere essential-supremum bound
cover finite conjugate exponents and both endpoints. All integrals are extended
nonnegative integrals, initial atoms are explicit, and energies/expectations are
invariant under the allowed null-event realization choices.

## Stieltjes continuous/jump decomposition

Mathlib's s-finite disjoint-family theorem gives countability of positive-mass
singletons. Restriction to this set and its complement splits the original
measure. On general measurable spaces, the complement is only asserted to
have zero mass on singletons; this is not silently promoted to general
nonatomicity. A dominated half-line measure has finite initial-interval mass,
and its cumulative function is right-continuous by the original Stieltjes
increment bound. Finite restrictions and an increasing cover prove equality
of the entire reconstructed measure. The singleton/left-limit formula then
proves continuity of the point-diffuse realization. The jump realization is
the actual sum over `(0,t]`, with real summability proved from finite extended
mass, rather than relying on the default value of a nonsummable real series.
Initial values are separate. For random finite-measure fibers, singleton mass
is a jointly measurable kernel integral of the diagonal. Its zero-mass region
therefore defines a measurable point-diffuse measure. Removal of point atoms
commutes with measurable finite-time restriction; consequently the continuous
component at time T only uses the original filtration at T. The raw square
bracket's continuous component is now adapted, continuous, increasing and FV.
Its exact decomposition and squared-jump summability follow from the unique
raw bracket's already-proved initial and jump identities. The real-time index
is explicit, and indistinguishable versions and continuous paths have the
corresponding invariance and normalization identities. Mixed continuous
covariation is now polarized from these same components. The bound
`abs (a*b) <= a^2+b^2` proves absolute summability of mixed jumps. Exact
summable-series polarization and the raw bracket identities give the mixed
decomposition and bilinearity, with its initial product separate. Symmetry,
diagonal and version invariance are also proved. No sign or monotonicity is
asserted for mixed continuous covariation.

## Continuous bracket stopping

BUILD: stopped Stieltjes measures are closed-endpoint restrictions. The previously
proved diffuse-restriction identity gives continuous-part stopping pathwise.
Actual indistinguishable raw-bracket realizations transfer it to square brackets;
polarization gives simultaneous mixed stopping. One-sided stopping uses the raw
identity and the exact jump cutoff `t <= tau`, not an incorrect one-sided finite
partition-cell identity. The cutoff includes the stopping endpoint and the source
jump at zero. Zero and infinite stopping regressions distinguish the vanishing
continuous component from the raw bracket's retained initial product. No new
stopping-time, raw-bracket or integral owner is introduced.

## Weighted mixed random-partition limits

BUILD: Protter II.30's finite weighted mixed sums use the original left sampling
times and retain the moving terminal cell. An exact cellwise product identity
reduces them to three existing random Riemann sums. REUSE: the full cadlag II.21
theorem, existing semimartingale product, integrator subtraction, associativity,
and indistinguishability invariance. The source left-limit multiplication lemma
includes zero; it identifies the limit with the existing bracket integral.
Regressions distinguish the increment sum from a raw initial atom and test a
nontrivial partial cell. No uniform convergence of discontinuous sampling is used.
This increment proves weighted partition convergence; II.29 is proved separately below.

## Brackets of Chapter II stochastic integrals

BUILD: Protter II.29, from exact raw mixed sums of the existing source elementary
integral. Stopped mixed brackets converge and arbitrary finite random coefficients
are controlled by pathwise compact bounds, with measurable output deviations.
No coefficient bound or moment assumption is introduced. A UCP contraction for
source left limits and multiplication by a fixed cadlag process support the
extension. REUSE: density, continuity in the integrand, the actual product formula
and associativity. Only brackets along integrals of a fixed integrator are asserted
UCP-continuous; arbitrary varying-semimartingale continuity is not claimed.
Symmetry and the existing raw diagonal give the two-integral and square formulas.
Regressions retain the four-factor initial product and initial square, and remove
all positive-time coefficients for a constant integrator. Natural-number square
exponents are explicit to avoid ambiguous generic-power elaboration.

## Continuous-local bracket compensation and constancy

BUILD: Protter II.27's main continuous-local bracket theorem. Positive-time
jump vanishing upgrades cadlag paths to continuous paths without incorrectly
annihilating the source jump at zero. REUSE: the integral jump identity and
masked locally-L2 bridge give continuous-local preservation of integration;
the raw square definition gives the compensated-square local martingale.
Actual masked UI localizers, zero expectation and nonnegativity prove the
zero-starting nonnegative-local-martingale lemma. Constant raw mixed sums and
polarization prove centering, so bracket constancy implies process constancy
even for an unmasked initial value with no moments. The reverse implication
uses version invariance, not a new normalized bracket. Interval corollaries
are now proved below; moment corollaries remain separate obligations.

## Finite-variation constancy and raw-bracket characterization

BUILD: Protter II.26's continuous-FV specialization and II.27 Corollaries 1--2.
REUSE: actual pathwise Stieltjes agreement and the continuous self-integral
identity; the source left limit differs at zero, so only positive-time
increment integrals are identified. Open-interval BV extends to endpoints,
then clamping gives an FV stopped difference. Existing one-sided bracket
stopping and exact subtraction identify its raw bracket. No false cellwise
mixed stopping formula is used. Stopping constancy is expressed entirely
with finite evaluations, including infinite endpoints and AE stopping order.
The original masked localizers give version invariance. Integration by parts
and II.20 give locally-L2 product residuals; zero jumps make an FV residual
difference continuous, proving uniqueness. No external package, predictable
compensator or unmasked initial-moment premise is introduced. The general
FV bracket theorem and single-event all-intervals constancy are now proved
below. Moment/terminal corollaries remain open.

## Continuous-local constancy intervals on a common event

BUILD: deterministic departure times via the canonical hitting time of a
stopped-increment process; their usual-filtration stopping property;
closed endpoint retention; a countable-dense-grid transfer lemma; and the
common-event raw/continuous bracket constancy theorems. REUSE: the existing
ordered-stopping bracket equivalence, `denseSeq`, closure of real intervals,
Mathlib `EqOn` and `OrdConnected`, and monotonicity of the actual raw bracket.
No new interval or bracket predicate, L2 premise, or unproved inverse clock
is introduced. A single event covers all intervals and arbitrary random
endpoints. Regressions retain an infinite exit for constant-seven paths and
the zero exit for a linearly increasing path (the open target is not attained
at the infimum). The source compensated-Poisson example is covered by the
separate counting-process increment described below.

## General finite-variation raw bracket and quadratic pure jump

BUILD: Protter II.26 from real endpoint step functions and the original
Stieltjes increment integral. Strict-left and right endpoint limits differ
at jumps. REUSE: compact cadlag bounds, dominated convergence on the actual
variation measure and finite-cell square algebra. The self-integral identity
retains the jump integral. Jordan singleton masses control actual jump support
and absolute summability; both component series are proved summable before
subtracting their `tsum`s. Countably supported integrals are evaluated by
Mathlib's countable-set integral theorem with integrability retained. Existing
pathwise FV agreement identifies raw QV with the initial square plus the
positive-time squared-jump series. The source quadratic-pure-jump property
uses the existing continuous component, not a new bracket. Regressions retain
endpoint jumps, separate time zero from `(0,t]`, and allow nonconstant drift.
The mixed pure-jump theorem II.28 and full discontinuous-FV C1
change-of-variables theorem II.31 are proved below.

## Quadratic pure-jump mixed covariation

BUILD: Protter II.28. REUSE: the existing continuous component's bilinearity,
nonnegative diagonal and absolutely summable mixed-jump decomposition. A
real affine function nonnegative at every integer has zero slope, by the
Archimedean property. Taking the countable intersection before selecting a
path or a time gives path-local mixed vanishing when one diagonal is zero.
Both argument orders, FV specializations and continuous-path corollaries
are proved with the raw initial product retained. The same algebra proves
quadratic-pure-jump linear stability; it does not imply stepwise paths or
annihilate continuous drift. Regressions distinguish integer from merely
nonnegative coefficients, verify the initial term, and test nonconstant
linear drift against an arbitrary, possibly discontinuous semimartingale.

## Right-continuous finite-variation C1 change of variables

BUILD: Protter II.31 directly, without assuming Ito. REUSE: Mathlib's
derivative-filled `dslope`, mean value theorem, local C1 Lipschitz estimates,
Bochner dominated convergence and the actual Jordan/Stieltjes owners. Joint
divided-slope continuity handles diagonal cells, while the real endpoint
limits retain each jump. Exact finite sums telescope. Weighted FV jump
series are genuinely absolutely summable; countably supported integrals are
evaluated only after proving their integrability. The derivative correction
has support contained in the actual jump set. Right-continuous local BV
implies cadlag regularity, so no extra path premise is hidden in the source
theorem. Process and semimartingale interfaces use the existing integral,
with the source `f'(0) X_0` term explicitly removed in the increment formula.
Regressions evaluate an actual path jumping from 1 to 3: square change 8,
derivative integral 4, and jump remainder 4. They also test the nonzero
diagonal differentiated slope and the source derivative's initial argument.
General jump Ito and Klenke's C1 formula for arbitrary QV paths remain open.

## Continuous-semimartingale Ito formula

BUILD: the continuous case and preservation corollary of Protter II.32.
REUSE: Mathlib's Taylor-Lagrange theorem, compact uniform continuity and
the project's genuine raw bracket and random-partition integral limits.
The quadratic Taylor quotient is filled with half the second derivative
on the diagonal; mean-value squeezing proves its joint continuity. Exact
finite Taylor sums keep original left-endpoint weights and partial cells.
Uniform convergence of raw square sums bounds actual partial square sums
without asserting that they are increasing. Nested UCP subsequences and
compact diagonal-error bounds force the error limit to vanish on one event
for all times. Existing integral preservation then proves C2 composition
preserves continuous semimartingales. No new bracket, initial moments,
global derivative bounds or external package is introduced. A cubic jump
regression retains the nonzero remainder; general jump Ito remains open.

## General cadlag raw-bracket Ito identity and C2 preservation

BUILD: the general raw-bracket identity in Protter II.32's proof and its
semimartingale-preservation assertion. REUSE: compact one-sided cadlag
bounds, Mathlib's Lebesgue-number lemma, actual summable series, exact
endpoint-pair step sums and the sole raw bracket's UCP limit. Finitely many
separators control small coefficients outside selected cells; vanishing
mesh separates the finite selection. The selection also contains a finite
approximation to the actual target series. Remaining cells are bounded by
a small coefficient times bounded square sums, without assuming these sums
are monotone. Clipping preserves repeated endpoints and partial cells.
Nested subsequences identify the stochastic error on a common event. Compact
Taylor bounds prove absolute jump summability. Positive and negative actual
cumulative series prove FV, and the raw identity transfers FV to an adapted
cadlag residual, yielding general C2 preservation without circular closure
assumptions. No external package or moment bound is introduced. The source's
continuous-component formula and multidimensional extension are proved below.

## General Ito continuous-bracket form

BUILD: the source form of Protter II.32, closing the one-dimensional C2 theorem.
REUSE: Mathlib countable-set Bochner integration and measure-addition integrals,
the intrinsic point-atomic/diffuse restrictions, canonical continuous QV and
the existing stochastic integral's FV agreement and version invariance.
The actual Jordan path integral of a Stieltjes function equals integration
against its own measure plus the separate initial term. Integrability, not
totalized integral algebra, justifies the continuous/atomic split. Caglad
compact bounds prove absolute weighted-jump summability. Both raw and
continuous brackets use the same realization, with no competing owner.
Convergent-series subtraction gives the first-order jump correction. The
positive-time composition lemma deliberately excludes zero unless the
transform preserves zero; the source derivative integrands start at zero.
No additional external package, custom axiom or moment assumption is used.

## Multidimensional Taylor prerequisites

BUILD: first/second Frechet derivatives along actual affine lines, the
second-order Lagrange remainder, and its operator-norm Hessian oscillation
bound. Dividing the actual error by the squared increment norm yields a
jointly continuous diagonal-zero coefficient; no direction is chosen at a
zero increment. REUSE: Mathlib scalar Taylor, Frechet chain rules and
continuous-linear-map operator norms. Existing scalar finite-separator and
diagonal-modulus lemmas are generalized in place to metric/proper normed
spaces, preserving their scalar applications. No vector stochastic-integral
or quadratic-variation owner is introduced. These prerequisites feed II.33 below.

## Vector partition limits and actual jump series

BUILD: deterministic vector norm-square energy bounds, weighted pair limits
under finite cadlag separation, stopping-compatible partial sums, exact
Frechet Taylor identities and actual absolute jump-correction summability.
REUSE: the existing finite partitions and scalar coordinate square sums,
Mathlib finite-product norms, actual strict-left limits and summable-series
operations. Endpoint-pair steps are generalized in place. The product-norm
energy is only a deterministic dominating quantity, not a stochastic bracket.
Countable coordinate path intersections preserve one common event; finite
coordinates supply square-jump summability from the existing raw QV owners.
The whole vector Ito stochastic identity and C2 preservation are proved below.

## Finite-dimensional cadlag Ito formula (Protter II.33)

BUILD: exact standard-basis coordinate derivative expansion, finite UCP and
semimartingale sums, common-event vector Taylor-error identification, raw
and continuous mixed-bracket Ito formulas, actual FV jump corrections and
C2 semimartingale preservation. REUSE: Mathlib Frechet derivatives, finite
product measurability and summable-series algebra; the project's existing
scalar integral, raw/continuous bracket owners and square integral split.
The mixed integral split is derived by polarization with the initial
product retained. Absolute weighted-jump summability justifies every series
interchange. Positive-time left-limit composition does not impose f(0)=0.
No initial moments, global derivative bounds, external packages or custom
axioms are introduced. The empty coordinate family is supported.

## Fisk--Stratonovich and the continuous-covariation chain rule

BUILD: continuous covariation of one/two general stochastic integrals; FV
of the C2 Ito residual; the continuous-covariation chain rule; the source
semimartingale-domain Fisk--Stratonovich integral, C3 change of variables
(II.34), actual-jump integration by parts and its continuous-argument
corollaries. REUSE: existing raw/continuous bracket owners, actual jumps,
integral preservation, FV zero continuous covariation and the proved Ito
formula. The source correction is continuous, has zero initial value, and
vanishes with either FV argument. No arbitrary-caglad or later Chapter V
C2 domain extension is asserted. No moment premise or custom axiom is added.

## Complex coordinate calculus foundation

BUILD: ordered real-coordinate derivatives of entire analytic functions,
coordinate complex path/left-limit and semimartingale interfaces, complex
integration assembled from the existing real integrals, preservation and
real-linear commutation. REUSE: Mathlib complex differentiability/analyticity,
restriction of scalars, real continuous linear maps, and the project's
proved finite-coordinate Ito preservation. Source left limits still begin
at zero; the integral retains its complex initial product. The negative
imaginary-imaginary Hessian entry and both mixed entries are regression
checked. No independent complex good-integrator, stochastic extension or
bracket construction is introduced. These prerequisites now feed the
completed II.35--II.36 identities below.

## Complex bilinear brackets and analytic Ito formulas

BUILD: complex bilinear raw/continuous square brackets as real-coordinate
combinations, separate nonnegative energy, real-integrator algebra for complex
integrands, all-time linear left-limit commutation, actual absolute jump-series
summability, and Protter II.35--II.36. REUSE: the canonical real square/mixed
brackets, proved finite-dimensional cadlag Ito theorem, scalar integral algebra,
and raw/continuous/atomic Stieltjes decomposition. The proof includes all four
ordered Hessian entries and identifies the complex bilinear bracket, not its
Hermitian energy. Component/tsum interchange requires proved summability.
The continuous source raw-bracket formula uses a proved integral comparison
with a zero initial integrand; raw bracket initial squares remain unchanged.
No independent bracket/integral extension, external package, moment restriction,
global derivative bound, placeholder or custom axiom is introduced.

## Stochastic-exponential product and continuous existence

BUILD: the actual Doleans--Dade product expression, absolute summability of
factor deviations from square summability, the zero-factor criterion and
equivalent raw/continuous-bracket products. The continuous-integrator case
has proved continuity, positivity, semimartingale preservation and its actual
stochastic integral equation. REUSE: Mathlib's proved real infinite-product
convergence and nonvanishing theorems, the project's filled C2 Taylor quotient,
canonical bracket decomposition, finite-variation drift invariance and Ito.
Zeros and negative factors are retained, with no illegal global logarithm;
time zero is excluded from the product and initial moments are not assumed.
The pathwise continuation below proves general cadlag regularity and the
pure-jump finite-variation factor. General adaptedness and semimartingale
preservation are proved by the subsequent measurable-kernel construction.
The general jump-case integral equation is proved in the continuation below.
Uniqueness remains open. II.37 is not complete.

## Stochastic-exponential product paths and pure-jump variation

BUILD: closed/open endpoint product limits, cadlag paths, the actual
positive-time exponential jump identity, local finite variation of the
product factor, and its absolutely convergent actual jump-series identity.
REUSE: Mathlib's `tendsto_tprod_one_add_of_dominated_convergence`, the
finite-subset `tprod_one_add` expansion, Tannery's dominated convergence
theorem and absolutely convergent fiberwise summation. Their hypotheses
are supplied by the proved sum of absolute factor deviations. Splitting
the finite-subset coefficients into positive and negative parts expresses
the product as a difference of monotone series. Grouping activation times
proves that all variation is accounted for by the actual jumps, including
repeated activation times and zero factors. This is an internal deterministic
construction using Mathlib only, not an assumed adapted product or solution.
Three regressions check the zero-time boundary, the jump sum after a zero
factor, and simultaneous step coefficients. No product division, globally
defined real logarithm of negative factors, or moment hypothesis is used.

## Random jump-product measurability and general semimartingale preservation

BUILD: measurable intrinsic point-atomic kernels, actual unweighted real
and complex series on their sample-dependent atoms, and the finite-horizon
measurability bridge for the original jump product. REUSE: the canonical
raw-bracket Stieltjes realization and squared-jump identity, finite-fiber
kernel integration, countable-atom integration, and Mathlib's proved complex
logarithm summability and exponential/product identity. The principal complex
logarithm retains negative signs; a separately summable -1-jump count guards
zero factors, where exp(log(0)) would otherwise incorrectly give one.
Absolute summability proves integrability of the inverse-singleton-mass
representation. Zero-mass points are explicitly removed by the support
condition, not by cancelling zero denominators. Capped progressive path and
left-limit restrictions use only the horizon sigma-field, and usual
completeness restores the original process on the exceptional null set.
Thus the original real product is adapted. Its proved FV/cadlag properties
and the existing C2/multiplication theorems imply general semimartingale
preservation. No new stochastic integral, bracket, external dependency,
moment premise or enumeration of random jump times is assumed.

## General stochastic-exponential equation

BUILD: the pure-jump FV Stieltjes/integral identity, the actual gradient and
all ordered Hessian entries of `exp(x) y`, the two-coordinate FV product
Ito formula, and the stochastic-exponential equation for general cadlag
inputs. REUSE: the canonical Jordan continuous/atomic decomposition,
compact caglad path bounds, source stochastic-integral FV locality,
Mathlib's Frechet product/exponential derivatives, finite-dimensional Ito,
continuous mixed-bracket vanishing, drift invariance and integral algebra.
The pure-jump hypothesis identifies the two continuous Jordan components;
their integrals cancel, leaving the actual weighted jump series. That
series then cancels the Ito jump correction. No division by the product,
positivity, initial moment or random-path-uniform bound is required.
The arbitrary initial value is `exp(X(0))`; unit initial value explicitly
requires `X(0)=0`. Regressions check mixed Hessian terms at a zero factor
and the zero initial integral with unrestricted random initial values.
Uniqueness and later source applications remain open; II.37 is not closed.

## Stochastic-exponential multiplication and continuous inverse

BUILD: the exact compensated jump-product multiplication identity, canonical
exponential version invariance, Protter II.38 and its continuous inverse
consequence. REUSE: Mathlib's `HasSum.rexp` and `HasProd.mul`, actual
square/mixed jump summability, the canonical raw/continuous mixed bracket
decomposition, FV drift invariance, and the continuous explicit exponential.
No stochastic-equation uniqueness result is assumed. Product factors may
vanish or be negative; only nonzero ordinary real exponentials are inverted.
The arbitrary-initial product identity retains `exp(X(0)Y(0))`. The continuous
inverse uses the continuous bracket without an initial restriction; the raw
bracket formula explicitly requires zero initial value. Three regressions
protect these initial guards and simultaneous absorbing jumps. No new owner,
external dependency, moment premise or custom axiom is introduced.

## Characteristic-exponential local and true martingales

BUILD: real exponential local-martingale preservation, the coordinate complex
local-martingale predicate and stability, compact-envelope promotion, and the
actual compensated characteristic exponential with its integral equation.
REUSE: the proved continuous complex Ito formula and coordinate bracket
integral expansion, real FV continuous-bracket vanishing, real integral
algebra, masked local L2 preservation, and Protter I.51 envelope promotion.
Mathlib's conditional-expectation/continuous-linear-map commutation proves
linear-map martingale preservation and the exact complex-coordinate bridge.
The negative imaginary-imaginary bracket cancels the positive compensation.
The bracket-equals-time case has a deterministic bound on each compact
horizon, not a global boundedness assumption. No initial moment, new
stochastic owner or law/independence assumption is inserted. Three regressions
check the unit initial phase norm, positive compensation and zero frequency.
The distributional closure and filtered equivalence are recorded next.

## Levy's real Brownian characterization

BUILD: complex conditional-expectation pull-out, restricted-law identification
from constant conditional characteristic functions, past-event independence,
ordered mutual independence, and both directions of Protter II.39. REUSE:
Mathlib's real-bilinear pull-out, set-integral conditional-expectation identity,
finite-measure characteristic-function uniqueness, Gaussian characteristic
function, `HasLaw`, `Indep`, `HasIndepIncrements` and `IsBrownianReal`.
The reverse direction uses Gaussian first/second moments and independence,
then continuous FV local-martingale constancy to identify the existing raw
bracket. No new Brownian, bracket, independence or integral owner is defined.
The final filtered equivalence retains the complete past-independence clause.
The full-information filtration cannot make a Brownian process a martingale;
this is proved from its actual nonzero variance. Zero-length increments and
nonzero initial shifts have regression coverage. Usual-filtration
augmentation and the multidimensional theorem are not supplied by this result.

## Deterministic brackets and finite orthogonal projections

BUILD: deterministic-clock characteristic martingales and Gaussian increment
laws, finite continuous-local-martingale sums, full continuous-bracket double
sums, common-clock orthogonal projection formulas, and the raw/continuous
initial-value bridge. REUSE: the existing finite-sum semimartingale theorem,
masked addition, compact-envelope promotion, conditional Fourier uniqueness,
canonical continuous bilinearity and the actual mixed-jump decomposition.
The original `IsSemimartingale.finset_sum` interface is retained unchanged;
the fully indexed-family form is a direct wrapper. Finite event intersections
require no countability of the ambient coordinate type. No division by a
coefficient norm, strictly positive variance, initial moments or additional
clock-monotonicity assumption is introduced. Regressions cover flat-clock
Dirac laws, empty projections, and both ordered cross terms for a repeated
coordinate. The joint-law/process-independence step is completed next.

## Levy's multidimensional characterization

BUILD: Hilbert-space conditional-Fourier restricted laws, joint Gaussian
vector increment laws and past independence, joint Gaussian processes in
time and coordinate, cross-time covariance cancellation, and Protter II.40.
REUSE: Mathlib's finite-measure characteristic-function uniqueness, Gaussian
product characteristic functions, `HasLaw`, `HasIndepIncrements`, Gaussian
process transformations and independence from zero cross-covariances.
The canonical finite Gaussian product is transported by `MeasurableEquiv.toLp`;
no new multivariate law or Brownian predicate is introduced. Entire coordinate
paths are mutually independent, not just pairwise or at equal times.
The real conditional-Fourier API now specializes the general proof, preserving
its existing signatures. Filtration-independent increments now support generic
measurable subtraction. Final independence interfaces use `Finite`; concrete
enumerations are chosen only inside proofs when needed. Initial-zero guards,
repeated endpoints and empty coordinate families are retained.

## Harmonic composition and the subharmonic source boundary

BUILD: finite stochastic-integral sums retaining the initial product, the
continuous-coordinate Ito formula, isotropic Hessian contraction, trace-zero
composition along actual paths, and the full-space harmonic specialization.
REUSE: existing pointwise caglad finite sums, canonical stochastic integration,
continuous bilinear covariation, masked local-martingale stability, Mathlib's
Euclidean orthonormal basis, iterated derivatives, Laplacian and harmonic owner.
No competing harmonic, Laplacian, Brownian or local-martingale definition is added.
The common clock can be random and flat; no initial moments are assumed.
The Gaussian-density calculation proves that `exp(x^2/2)` is not integrable
under `gaussianReal 0 1`; its explicitly computed Laplacian is strictly positive.
Transfer by `HasLaw` disproves the unqualified true-submartingale statement
for actual Brownian motion in any filtration. The source correction is not a
substitute for the open-domain proof chain. The corrected full-space positive
direction is now proved below.

## Corrected subharmonic composition and local-to-true promotion

BUILD: increasing pathwise and stochastic integrals, integrable adapted
monotone-process submartingales, actual masked local-submartingale witnesses,
compact-envelope promotion, the isotropic Ito increasing drift, and the
full-space Laplacian interfaces. REUSE: the existing Jordan/Stieltjes integral,
Chapter II FV agreement, bounded continuous stopping sequences, Protter
fundamental-sequence refinement, dominated set-integral limits, Mathlib's
`Locally` and `Submartingale`. No local-submartingale predicate is introduced.
The drift is constructed from the actual integral, not supplied as a premise.
The local theorem needs no moments; the true theorem explicitly requires a
compact-time integrable envelope. Regressions cover empty coordinates,
nonintegrable initial values and increasing integrals with negative initial
products. The open-domain extension/localization is proved below.

## Open-domain harmonic and classical C2 subharmonic composition

BUILD: smooth extension near an arbitrary closed subset of an open domain;
compact exhaustion retaining a basepoint; closed-region exits and their actual
localizing sequence; zero-exit coordinate patching; compact masked true
submartingales; open-domain local composition and envelope promotion; source
raw-bracket interfaces with initial-clock centering. REUSE: Mathlib's smooth
functions with prescribed support, normal separation, `CompactExhaustion`,
canonical harmonic/Laplacian owners and masked `Locally`; existing stopping,
continuous square/mixed brackets, FV invariance and local-martingale recovery.
Neighborhood equality transports derivatives, not just function values.
The coordinate correction is an actual F0-measurable random constant and
preserves continuous brackets without moments. Regression tests cover this
zero-exit branch, Laplacian transport, dimension zero and a raw clock starting
at nine. No extra package, exhaustion structure or subharmonic predicate is
introduced. The subharmonic APIs explicitly require C2 on the domain; the
source's unstated smoothness convention and nonsmooth coverage remain under
audit. No general nonsmooth result is asserted.

## Inverse clocks and the DDS path/stopping foundation

BUILD: strict-upper-level inverse values, endpoint/sublevel identities,
proper/quotient clock maps, continuous descent along clock fibers, sampled
path factorization, inverse-clock stopping times and adaptation, and the
original clock's stopping property in the reindexed filtration. REUSE:
Mathlib `hittingAfter`, proper/quotient maps, `stoppedValue`, stopping-time
sigma-algebras and the existing `Filtration.stoppingTimeReindex`; StochLean's
common-event constancy intervals and sole continuous bracket. The `NNReal`
clock is only a codomain conversion, with exact real value everywhere.
Raw divergence and zero-initial raw-inverse identification are proved.
Regressions retain identity and delayed clocks, an infinite inverse for a
bounded clock, and nonzero initial process values on an initial flat fiber.
Neither a two-sided inverse nor strict clock increase is assumed. The
Brownian-law extension is recorded below.

## Dambis--Dubins--Schwarz Brownian law and source filtration

BUILD: bounded complex-local optional sampling at AE-finite times, stopping
stability, characteristic-exponential level bounds, conditional Gaussian
increment laws, full past independence, the canonical Brownian conclusion,
and the exact source raw-bracket theorem. REUSE: real coordinate UI sampling,
the existing characteristic exponential, Fourier uniqueness, Mathlib's
`IsBrownianReal`, canonical stopping sigma-algebras and the sole bracket.
Usual completeness proves equality of stopping sigma-algebras under AE-equal
times; this is not an equality-in-law transport. All path reconstruction and
clock-level conclusions share one event. The zero initial-value premise is
explicit and necessary. No L2 or prior Brownian/time-change law is assumed.
Regressions cover zero-length increments, necessity of the original zero
start, and substitution of arbitrary, even nonmeasurable, random times.
BUILD: future-increment independence under right continuation for adapted
right-continuous real processes, and the source DDS right-continuation theorem.
REUSE: Mathlib's bounded-continuous-test characterization of independence,
independent set integrals, dominated convergence and `Filtration.rightCont`.
Initial completeness is transported through the actual stopping sigma-algebra
and its right continuation. The same raw hitting times, Brownian process,
reconstruction and clock-level identities are retained; the clock is still
a stopping time in the enlarged filtration. No assertion `G = G_+` is needed.
This closes the separate right-continuation step in the proof of II.42.

## Levy stochastic-area construction and Riccati foundation

BUILD: the actual antisymmetric area integral, zero initial value, continuous
local-martingale preservation, raw/continuous mixed brackets, continuous
energy, and the source terminal Riccati coefficients with their derivatives,
smoothness, signs and deterministic exponential bound. REUSE: the sole
Chapter II integral, canonical brackets, continuous integral preservation,
and Mathlib's real hyperbolic functions and calculus. No new stochastic
integral, bracket, area-law assumption or external package is introduced.
The parameter may be zero or negative; the initial coordinates need not
vanish for the construction. The actual exponential drift cancellation and
characteristic function and positive-time density are now proved below.

The explicit-clock area exponent and exponential now have actual complex
semimartingale and continuous-path proofs, an exact inverse-cosh initial
value, the source terminal characteristic integrand and the required norm
bound. BUILD also supplies the continuous zero-starting FV derivative-integral
identity and the two Riccati stochastic-integral equations. REUSE: the proved
cadlag C1 FV formula, integrand congruence, complex analytic preservation,
and the existing area. No new FV integral or unproved exponential-martingale
premise is introduced. These are inputs to the proved drift cancellation below.
BUILD also supplies the squared-radius equation and its actual integrated
form under a common raw clock, and C1 substitution for transformed continuous
FV clocks. REUSE: raw square-bracket definitions, integrator linearity,
associativity and stopping at zero. The proved random-constant integral
retains the initial product, including nonintegrable random constants.
No new radius or clock-integral owner is introduced.
BUILD: continuous-FV multiplier and C1-weighted radius formulas, the actual
real-coordinate area-exponent integral representation, and the continuous
area formula with arbitrary initial coordinates. REUSE: raw integration by
parts, continuous-FV raw covariation, initial-increment comparison and C1
substitution. Initial products are canceled explicitly where justified, not
discarded. The complex-bracket drift cancellation uses these identities below.
BUILD: mixed/square continuous-FV multiplier brackets, common-clock brackets
of finite sums of actual stochastic integrals, their two-coordinate interfaces
and the area energy `J_Q(X^2+Y^2)`. REUSE: the product representation, FV
integral preservation, finite-sum bilinearity, isotropic matrix contraction,
integral brackets and indistinguishability transport. The area identity does
not require Brownian laws, integrability or zero initial coordinates. No new
clock, bracket or integral selector is introduced.
BUILD: squared-radius bracket, radius/area orthogonality, all real-coordinate
brackets and the actual complex bilinear bracket of the compensated exponent.
REUSE: raw radius representation, finite-variation perturbations, common-clock
integral-pair brackets, FV multiplier calculus, integral associativity and the
existing complex coordinate owner. The final bracket is `J_Q(R(alpha^2-u^2))`,
not the nonnegative energy. No exponent differential or bracket identity is
assumed. The exponential's Ito cancellation and local-martingale proof follow below.

BUILD: complex-integrand random-constant formula, both kinds of complex
integral version invariance, zero-imaginary-integrator reduction, associativity
with a real inner integral and continuous-local-martingale preservation.
REUSE: real initial products, real integral congruences and associativity,
coordinatewise complex integration, and proved continuous-LM local square
integrability. No initial-integrability or extra local-L2 premise is inserted.
BUILD: actual complex integrals of the area, real exponent and complex bracket;
the exponential Ito equation with cancellation of the half-clock terms;
complex local-martingale preservation; bounded stopped true martingales;
the inverse-cosh characteristic function for a deterministic common-clock
level, the standard time clock and canonical independent Brownian motions.
REUSE: the existing real/complex integral and bilinear bracket, analytic Ito,
continuous-LM integration, integrable-envelope localization and martingale
set-integral equality. Brownian raw brackets are identified from the existing
square-sum probability limit and raw-bracket UCP limit, with exact dyadic
restriction transport; independent normalized sums identify mixed brackets.
This does not require changing the older Brownian path modules. The chosen
filtration's adaptedness and future-increment independence are explicit.
No assumed exponential differential, area law, new bracket owner or external
dependency is introduced. The time-zero Dirac law is proved.

BUILD: the hyperbolic-secant Fourier integral, positive-scale normalization
and integrability, the zero-safe hyperbolic-secant probability measure and its
characteristic function, and the actual stochastic-area law/density for the
continuous-local-martingale and independent-Brownian interfaces. REUSE:
Mathlib's sigmoid derivative/range, the one-dimensional Jacobian theorem,
beta integral, Gamma reflection formula, measures with density and finite-measure
characteristic-function uniqueness. The analytic identity is proved by a
sigmoid/Beta substitution, as an alternative to Protter's contour calculation.
No external integration result or assumed density certificate is inserted.
The positive-time guard is retained; at zero the measure is Dirac, not the
zero-density measure. This closes II.43 and its corollary, not the package.

## Compensated Poisson martingale prerequisite

BUILD: the exact Poisson first moment and process/increment transfer, the
actual compensated Poisson true/local martingale, its cadlag/FV paths and
usual-filtration semimartingale property. REUSE: the existing Poisson law
and first-moment integrability, the exponential series, independent conditional
expectation, deterministic martingale localization and FV semimartingales.
The chosen past's independence from future real increments is explicit; no
arbitrary enlarged-filtration claim or new counting-process predicate is made.
BUILD: second-moment integrability and the exact Poisson second moment by
series shifting; nonnegative square-sum excess, its exact mean and mesh bound;
the probability limit for arbitrary vanishing meshes; canonical raw-bracket
identification for the count and its compensation; and the source all-interval
nonconstancy/flat-bracket counterexample. REUSE: the existing count law, L1 to
probability convergence, raw-bracket UCP uniqueness, exact dyadic restriction,
continuous-FV covariation, discrete right continuity and order-connected sets.
The unit-rate compensated process is formally ruled out as a continuous local
martingale by the already-proved constancy theorem. No unit-jump premise,
alternative bracket, source-law certificate or extra dependency is introduced.
The counterexample after II.27 Corollary 5 is closed; Corollaries 3--4 remain open.

## Brownian usual-augmentation transfer

BUILD: an explicit probability instance for the completed measure; old-event
AE representatives after adjoining ambient null sets; independence and law
transfer to completion; adaptedness and future-increment independence in
the completed usual augmentation; Brownian finite-dimensional/path transport;
true and square-minus-time martingales, continuous-local and semimartingale
properties, and the sole canonical raw bracket equal to time. A natural-past
entry point derives independence from the original Brownian shift theorem.
REUSE: `eventuallyMeasurableSpace`, the existing `nullSets`/`usualAugmentation`,
Mathlib completion with its unchanged outer measure, bounded-continuous-test
right-continuation, the canonical Brownian predicate, Gaussian moments and
the proved semimartingale bracket limit. No same-ambient fake completion or
independence under arbitrary enlarged information is asserted. Regressions
keep the actual zero start and reject the full-information martingale claim
even on the completed probability space.

## C1 quadratic-variation composition (Klenke 21.62)

BUILD: finite cumulative-step integration, including initial mass; continuous
weighted limits from pointwise nonnegative cumulative-mass convergence; completed
square-sum transport; derived zero initial value, monotonicity and local BV of
the limit; vanishing continuous diagonal errors against bounded square sums;
the actual C1 Stieltjes formula and continuous increasing zero-starting output.
REUSE: compact uniform continuity, finite sum algebra, the canonical pathwise
Stieltjes integral and its Riemann approximation, exact partition restrictions,
and Mathlib's `dslope` with the previously proved joint C1 continuity.
No C2 condition, input finite variation, new bracket owner or assumed weighted
identity is used. Regressions check affine translation/scaling with arbitrary
initial values, a nonzero constant image, and initial mass on an empty partition.
This closes 21.62; full-sequence partition dependence is proved separately below.

## Full-sequence quadratic-variation partition dependence

BUILD: refinement decreases the mesh; an actual intermediate-value midpoint in
every cell halves its square sum. Iteration and finite endpoint unions construct
nested, vanishing-mesh, zero-square-sum partitions of any continuous path.
Finite extensions of full dyadic partitions preserve local finiteness,
unboundedness and the global mesh bound. Exact endpoint-set invariance transports
the finite construction to genuine Klenke admissibility. A path extracted from
the internally constructed Brownian measure has dyadic QV one and another
admissible-sequence QV zero at horizon one. The quantifier-swapped Brownian
probability-one event is disproved. REUSE: IVT, finite product-index equivalence,
geometric convergence, sorted endpoint sets, the internal Brownian construction
and the fixed-horizon summable-mesh second-moment theorem. No external package,
random-partition independence or uniform null-set assertion is assumed.
The separate nested-sequence nonconvergence construction is now proved below.

## Nested-sequence quadratic-variation nonconvergence

BUILD: exact point-insertion range and square-sum product error; fixed finite
insertions preserve a continuous-path QV limit; common refinement with any
fixed finite partition preserves that limit. Alternating high and low
refinements of the previously constructed continuous path retain all old
endpoints and a dyadic grid at every step. Finite extensions give a genuine
nested admissible infinite sequence. Even square sums are below `1/4`, odd
square sums above `3/4`, so no real limit exists at horizon one. REUSE: actual
interlaced endpoints, endpoint-set invariance, continuity and mesh convergence,
IVT small-square-sum refinements, the internal Brownian witness, and cofinal
even/odd subsequences. Regressions cover existing/degenerate endpoints and
prove that the example cannot be a bounded-variation path. No arbitrary
interleaving is claimed to preserve nesting. Klenke 21.56--21.63's outstanding
deterministic construction obligations are now closed.

## Continuous-time Doob maximal control

REUSE: the internal discrete Banach-valued Doob Lp bound, monotone time
reindexing, sorted finite endpoint partitions, the existing extended
`denseRunningSupremum`, finite measurable suprema, and monotone convergence.
BUILD: arbitrary finite-time sampling sets for `p > 1`; the dense-grid square
supremum L1 bound with constant four; AE finiteness, real integrability, and an
actual measurable L2 square-root envelope. Right continuity transfers the
bound to every time in the finite interval on one event, including its endpoint.
No alternative running-supremum owner or integrable infinity fallback is used.
Regressions retain the initial square, the nonzero constant case, and arbitrary
pathwise choices of bounded time. This is a prerequisite for Protter II.27,
Corollaries 3--4, not their general local-martingale or infinite-terminal closure.
No external implementation was copied or added as a dependency.

## Raw bracket second moments of true L2 martingales

BUILD: the actual square-minus-raw-bracket process is a local martingale for
locally square-integrable integrators; true finite-time L2 cadlag martingales
have integrable raw brackets and exact second-moment expectations. REUSE:
the Chapter II integral's locally-L2 preservation, source masked fundamental
sequences, the proved zero initial residual, its integrable-initial unmasked
bridge, continuous-time Doob control, Fatou, and dominated convergence.
Bracket integrability is proved before the final dominated limit, not assumed
or inferred from the total Bochner integral. The raw initial square is retained.
Regressions exercise a nonzero constant and the actual compensated Poisson
martingale, including its chosen-filtration independence premise. This closes
the forward direction of II.27 Corollary 3 for true square-integrable cadlag
martingales, not the reverse/general-LM implication or Corollary 4. No external
code, extra dependency, or alternative bracket owner is introduced.

## Bracket-controlled jump localization

BUILD: every squared jump, including time zero, is bounded by the actual raw
bracket at every later horizon on one event. Integrable bracket values give
L2 square-root control and force the unmasked initial value into L2. For an
actual semimartingale which is a local martingale, integrable raw brackets at
all finite times construct masked square-integrable martingale localizations.
REUSE: canonical continuous/jump decomposition and summability; bounded caglad
cutoffs of the left-limit process; source local-martingale masking/stopping;
the proved integrable-envelope criterion and canonical `Locally` predicate.
The envelope is `n + sqrt([X,X]_T)`, so jumps can overshoot the exit threshold.
Regressions preserve the initial jump, reject bracket integrability for a
non-L2 initial value, and allow arbitrary nonzero/unbounded L2 initial values.
The unlocalized converse is now proved below; the general LM-to-SM theorem
is still separate work. No external implementation was adopted.

## Finite-time raw bracket moment equivalence

BUILD: integrable raw bracket values imply a uniform dense-grid maximal-square
estimate and make the original local martingale a true finite-time L2
martingale. Together with the forward moment identity this proves the
equivalence on the actual semimartingale domain. The continuous-local entry
uses its already constructed semimartingale witness. True L2 cadlag martingales
also have a true square-minus-raw-bracket martingale, retaining zero initial
residual without assuming a zero initial value for the original process.
REUSE: the constructed masked L2 localizers, local square residual, Doob,
integrable-envelope criterion and Fatou. Each localized residual is dominated
by its squared maximal envelope plus the original bracket. Its zero expectation
bounds localized second moments by the bracket mean. Eventual equality on an
entire finite interval passes dense-grid maxima to the original process.
Finiteness precedes real conversion, and true martingality is proved rather
than inferred from pointwise L2. Regressions cover compensated Poisson via
bracket integrability, the exact constant-process initial L2 criterion and
the true compensated-square residual. III.30's general LM-to-SM bridge and
infinite-terminal Corollary 4 are not closed. No external code was adopted.

## Normalized continuous-bracket moments

BUILD: normalized bracket integrability and the second-moment difference
formula; Klenke 21.70(ii)'s true compensated-square martingale; the continuous
local-martingale L2 equivalence with both initial L2 and normalized bracket
integrability, including Klenke 21.76. REUSE: the actual continuous-part owner, its continuous-path
identity `CQV = rawQV - X_0^2`, the raw moment criterion, constant initial
martingales and coordinate AE congruence. No second zero-starting bracket is
introduced. Regressions retain the initial second moment, reject omission of
initial L2 when the normalized bracket vanishes, and prove that the compensated
Poisson square is not a martingale even though its continuous bracket is zero.
Continuity is therefore not silently dropped. This closes these finite-time
normalized interfaces, not the rest of 21.70--21.76, the general LM-to-SM bridge
or any infinite-terminal assertion. No external implementation was adopted.

## Extended terminal raw quadratic variation

BUILD: the measurable extended terminal raw-bracket owner; common-event
cofinality, full-half-line limit and finite-time domination; the monotone
convergence integral identity; finite-energy integrability and uniform second
moments of the resulting true L2 martingale. REUSE: the sole raw bracket,
its AE monotonicity and initial square, Mathlib's AE monotone convergence and
the proved finite-time moment criterion. Finiteness is established before
real conversion. Constant initial-energy and Brownian infinite-energy
regressions guard the hypotheses. The L2 closing variable and its moment
identity and whole-half-line convergence are covered below. No external code
was adopted.

## Global Doob envelope and terminal-energy equivalence

BUILD: the whole-half-line maximal-square integral estimate, an actual global
L2 envelope, the converse terminal-energy bound and the equivalence of finite
expected terminal energy with true global L2 boundedness. REUSE: the existing
finite-horizon dense supremum, right-continuity bridge, Doob estimate, AE
monotone convergence, raw terminal owner and finite-time moment identity.
Only a countable family of horizons is intersected before obtaining all-time
bounds. The square root is taken after AE finiteness is proved. Regressions
retain nonzero initial energy, cover unbounded measurable random-time
evaluations and distinguish Brownian finite-time L2 from global L2 boundedness.
Whole-half-line martingale terminal convergence remains separate. No external code
was adopted.

## Actual L2 closure and terminal energy identity

BUILD: an actual L2 closing variable, integer-time AE/L2 convergence,
all-real-time conditional-expectation closure, second-moment convergence and
the exact terminal raw-energy identity for that variable. REUSE: Mathlib's
discrete martingale convergence and finite-measure Vitali theorem, project
uniform-integrability operations, the global Doob envelope, conditional
expectation towers and the raw finite-time/terminal integral identities.
The nonzero constant regressions retain the initial variable and its second
moment. A continuous oscillating path vanishes at every integer but has no
half-line limit at zero, guarding against an invalid extension of convergence.
Whole-half-line AE convergence is supplied by the separate extension below.
No external code was adopted.

## Whole-half-line L2 and almost-sure convergence

BUILD: conditional-expectation control of later increments and closing errors,
whole-half-line L2 convergence, tail Doob envelopes and the actual half-line
AE limit. REUSE: the existing integer closing variable, global Doob envelope,
filtration reindexing, L2 conditional-expectation contraction and Mathlib's
in-measure-to-AE subsequence theorem (Borel-Cantelli). The tail envelopes are
proved to vanish in L2, not assumed. Only countably many AE tail-control
events are intersected; each already controls all later times. The terminal
energy theorem now includes both full-time limits and the exact moment
identity on the actual semimartingale domain, with automatic CLM entry.
Regressions preserve constant initial values, allow sample-dependent escaping
clocks and identify any other terminal value AE. General LM-to-SM (III.30)
and non-L2/supermartingale convergence remain open. No external code was adopted.

## Explicit terminal values under stopping

BUILD: the finite/infinite stopped-value owner, its branch identities,
AE truncation convergence under an actual full-time limit, norm domination
and version transport. REUSE: Mathlib's finite stopped-value owner and the
project's common-event indistinguishability. Regressions distinguish explicit
infinite values from totalized evaluation, reject truncation convergence to
a wrong terminal value and test a mixed finite/infinite random time. No
optional-sampling theorem is asserted by these definitions alone; the proved
actual-terminal sampling extension follows below. The active-pin
stopping sigma-field is bounded by `iSup F`; an arbitrary ambient-measurable
closing variable must not silently be treated as the actual terminal limit.
No external code was adopted.

## Possibly infinite optional sampling with an actual terminal variable

BUILD: UI stopping families, integrability, minimum and AE-ordered sampling
identities, terminal conditional-expectation representations and Lp transfer
for arbitrary possibly infinite stopping times. REUSE: bounded usual-filtration
sampling, explicit terminal-valued truncation, UI limits, Vitali L1 convergence
and L1 contraction of conditional expectation. A finite-energy entry constructs
the actual L2 terminal variable and UI from previous results; no limit/UI premise
is added to that end-user theorem. Regressions cover both times infinite,
the nonzero time-zero term and two unbounded times ordered only AE. The native
sigma-field at infinity is still `iSup F`; arbitrary closing variables are not
silently substituted for an actual terminal limit. General non-L2 terminal
construction and supermartingale sampling remain open. No external code was adopted.

## Weak L1 maximal inequalities

BUILD: Banach-valued weak Doob bounds on arbitrary finite time sets, the
extended dense running supremum and all-time finite-horizon exceedance events.
REUSE: the existing conditional-Jensen norm-submartingale proof, now public and
generalized to arbitrary preordered indices; Mathlib's discrete maximal bound,
sorted time partitions and increasing-union measure continuity. Initial values
are not erased, and neither L2 nor a finite real supremum is assumed.
Regressions cover horizon zero, an integrable non-L2 constant martingale and a
nonzero initial constant. All eight public-theorem/regression axiom checks pass
with only the three standard axioms. No external code was adopted.

## General UI half-line convergence and constructed terminal sampling

BUILD: global/tail weak L1 bounds, the actual integer-time UI terminal variable,
all-real-time AE/L1 convergence and the UI/actual-limit-closing equivalence.
REUSE: discrete martingale convergence, Vitali L1 convergence, conditional
expectation contraction and increasing-union outer-measure continuity. The
all-time limit is proved by zero-measure late-deviation events at countably
many scales, not by assuming that integer convergence controls other times.
The Lp contraction proof is shared with the existing L2 entry. Constructed UI
terminal values feed the existing possibly-infinite optional-sampling theorem
without a terminal-limit or L2 premise. Regressions retain a non-L2 constant
initial variable, permit both sampling times to be infinite and apply the
actual limit to arbitrary sample-dependent escaping clocks. General non-UI
L1-bounded/supermartingale limits and explicit extended-filtration/arbitrary-
closing bridges are not marked complete. No external code was adopted.

## Actual closing projections and the extended-time UI martingale

BUILD: actual terminal projection of arbitrary integrable closing variables,
the terminal filtration, its native infinite-stopping agreement and the full
extended-index martingale/UI equivalence. REUSE: Mathlib Levy upward limits,
integer cofinality, all-time UI convergence, conditional expectation and the
existing explicit terminal-valued stopping owner. No second process-evaluation
or stopping-sigma-field owner is introduced. The finite-coordinate L1 and
initial-value conventions survive extension to infinity. Regressions include
a concrete symmetric two-point closing-variable counterexample, the terminal-
measurable recovery case and random integrable constant initial values.
Read-only source verification confirms that Protter's stopping sigma-field
definition starts with ambient events, unlike Mathlib's `iSup F` domain;
literal source I.16 at infinity therefore needs an explicit bridge. No
external code was adopted.

## Native optional sampling from arbitrary closing input

BUILD: projected-terminal integrability, representation by the original
closing variable's stopped conditional expectation, and AE-ordered sampling
for possibly infinite times. The unprojected formula is provided under an
explicit terminal-field measurability hypothesis. REUSE: proved terminal
projection limits, native optional sampling and the tower property using
`F_tau <= iSup F`. The regression accepts arbitrary closing input without
terminal measurability, and a symmetric two-point usual-filtration example
rejects using the unprojected input at two infinite times. This implements
the documented I.16 martingale source correction, not a second ambient
stopping-sigma-field owner. Supermartingale sampling remains open. No external
code was adopted.

## One-sided monotone sampling and finite-time upcrossing estimates

BUILD: monotone reindexing of submartingales and supermartingales, measurability
and integrability of the finite-partition upcrossing count, and endpoint
positive-part/first-moment estimates. REUSE: the existing filtration reindexing
and discrete upcrossing owners, time partitions and Doob's discrete inequality.
The strict-before cutoff is `size + 1` so terminal crossings are retained.
Regressions test this cutoff, repeated sampling of a proper submartingale and
its negative supermartingale, and the finite-measure mass correction. General
non-UI half-line convergence remains open. No external code was adopted.

## Upcrossing refinement without replacing the native count

BUILD: comparison of the existing crossing times under monotone sampling,
the resulting count inequality, endpoint-inclusion monotonicity across finite
partitions and endpoint-set invariance. REUSE: Mathlib's hitting-time minimality,
strict-before upcrossing owner, and StochLean's existing ceiling-index projection
and refinement predicate. The sampling map may repeat indices; every sampled
index must lie strictly before the target cutoff. Regressions prove that
repeating all samples twice leaves the count unchanged, the actual common
refinement controls both inputs, and a non-strict cutoff can lose a crossing.
General non-UI full-time convergence remains open. No external code was adopted.

## General L1-bounded half-line convergence

BUILD: expanding dyadic horizons, right-side endpoint approximation, dense
native-count aggregation and maximum attainment, the late-crossing refinement
argument, global expectation bounds, countably simultaneous level finiteness,
and the actual integrable full-time limit for submartingales/supermartingales.
REUSE: existing dyadic partitions and ceiling projections, Mathlib upcrossings,
monotone convergence, and the discrete submartingale limit-process and L1
integrability theorems. No second grid, crossing-time owner, or limit-process
representation is introduced. Right continuity is used on a single path event.
The non-UI theorem asserts almost-sure convergence, not L1 convergence or closure.
Regressions cover the proper one-sided case, non-L2 initial values, arbitrary
escaping clocks and infinite dense crossings of the integer-only counterexample.
No external code was adopted. Regularization and supermartingale sampling remain open.

## One-sided bounded-stopping integrability

BUILD: the existing ceiling index as a discrete stopping time, exact sampled
values when the original stop lies on the partition, one-sided countable-range
terminal conditional bounds, and the actual upper-approximation L1 estimate.
REUSE: native finite discrete stopping integrability/expectation monotonicity,
the conditional-expectation restriction lemma on stopping fibers, existing
uniform partitions and upper stopping approximations, conditional L1 contraction
and `Lp.eLpNorm_le_of_ae_tendsto`. The shared ceiling identities replace private
copies in the upcrossing proofs. Bounded real-time stopping values are now
integrable without UI, sign, global L1-bound or usual-filtration premises.
The general two-time conditional inequality still requires its own proof.
Regressions reject replacing the one-sided inequality by equality or dropping
the endpoint-range guard, and cover an unbounded-in-time submartingale and
negative initial values. No external code was adopted.

## Stopping-value characterization of uniformly integrable martingales

BUILD: Protter I.21 and its arbitrary-common-mean extension. Testing the
stopping time equal to t on a past event and infinity on its complement
identifies every coordinate as the conditional expectation of the explicit
terminal input. REUSE: native stopping-time past-event pasting, conditional
expectation uniqueness, the existing terminal-valued stopping owner, the
conditional-expectation martingale and the existing closing-to-UI theorem.
Adaptedness suffices; no unnecessary cadlag/regularization premise is imposed.
The all-stopping-times hypothesis is the source's substantive test, not a
replacement for the conclusion. Regressions reject deterministic-only tests
and nonintegrable terminal input, and retain centered nonzero random initial
values and nonzero common means. No external code was adopted.

## Convex transformations of martingales and submartingales

REUSE: native finite-dimensional conditional Jensen, automatic continuity of
convex functions on the whole finite-dimensional space, and native martingale
conditional identities. BUILD: the two process corollaries of Protter I.19.
The norm-submartingale interface remains with its existing owner. Regressions
allow a decreasing convex map for a true martingale, reject it for a proper
submartingale, reject a nonintegrable square of an integrable non-L2 random
constant, and exercise the nondecreasing exponential map. No external code
was adopted; all six new theorem/regression axiom audits use only the standard
three axioms.

## Whole-half-line strong Doob Lp control

BUILD: the general nonnegative-submartingale I.20 inequality for every real
p > 1, its coordinatewise-AE-positive form, a genuine measurable Lp envelope,
and the Banach-martingale norm corollary. REUSE: the project's proved natural-time
strong Doob inequality, sorted finite partitions, native one-sided reindexing,
native positive-part submartingales, monotone Lebesgue integration, conditional
norm Jensen and the ENNReal rpow order isomorphism. The purely analytic extended
Lp monotone-supremum and finiteness lemmas have their own reusable owner.

The extended all-time supremum may be infinite. No finite real supremum or
maximal-envelope witness is assumed. Right continuity supplies a countable
representation on one event, not an uncountable intersection of coordinate
null-set statements. Regressions cover a proper submartingale at p = 3, an
infinite supremum, a missed isolated spike without right continuity, retained
random initial values, and failure of the totalized quotient at p = 1.
All 16 theorem/regression axiom checks use only the standard three axioms.
No external implementation was adopted.

## Reverse one-sided uniform integrability

REUSE: native order-dual natural indexing, filtration and supermartingale
owners, conditional expectation, finite-family UI, UI of conditional
expectations of one integrable random variable, and conditional L1 contraction.
BUILD: expectation monotonicity, exact L1 residual formula, the derived uniform
L1 bound, reverse-supermartingale UI from an upper expectation bound, and the
dual reverse-submartingale theorem. No parallel reverse-martingale hierarchy or
legacy external exchangeability import is introduced. The tail error is
derived from the supremum of expectations; UI is a conclusion, not a premise.
Regressions include a proper supermartingale, a negative submartingale, failure
without the expectation bound and non-L2 initial data. All nine axiom checks
passed with the standard three axioms. No external code was adopted.

## General bounded one-sided optional sampling

REUSE: native one-sided martingales and discrete stopping, the project's sole
finite-stopping-time, partition and upper-approximation owners, native stopping
sigma-fields, reverse one-sided UI, Vitali, conditional integration and the
existing indistinguishable progressive version under usual conditions.
BUILD: exact index-field transport (allowing repeated endpoints), decreasing
dyadic approximation, arbitrary finite-partition conditional sampling, derived
UI and L1 convergence of upper-approximation values, and the general bounded
submartingale/supermartingale conditional inequalities. A reusable conditional
order criterion is proved separately, with no new conditional expectation owner.

The ordinary mesh is not falsely assumed decreasing. Random-time evaluation
uses indistinguishability, not merely a modification. AE order and bound
interfaces retain the original sigma-field by usual completeness. Four
regressions cover non-nested meshes, a negative supermartingale without a
global L1 bound, AE-ordered sampling with non-L2 initial data, and repeated
partition points. All 28 axiom audits use only the standard three axioms.
No external implementation was adopted; Class D and unbounded I.16 remain
separate obligations.

## Commuting conditional expectations at stopping times

REUSE: native stopping sigma-field comparisons on the two time-order events,
indicator pullout, conditional expectation's uniqueness and tower property.
BUILD: stopping-measurable inputs condition at the minimum time; arbitrary
iterated stopping-time conditional expectations equal the minimum projection
and commute. This closes Protter I.18's second corollary directly, without
using a not-yet-constructed cadlag conditional-expectation version.

The identities apply to complete real Banach targets, possibly infinite and
unordered stopping times, and need no usual conditions. Nonintegrable input
only satisfies the identities via native zero totalization; input integrability
is not claimed. Regressions test crossing time orders, the strict terminal
projection at two infinite times, and retained non-L2 initial data. All six
axiom checks use only the standard three axioms. No external code was adopted.

## Lower-closed supermartingale control and stopping integrability

REUSE: native conditional expectation, stopping sigma-fields and fibers,
the proved one-sided upper-approximation L1 convergence, usual progressive
versions, global L1-bounded martingale convergence, Levy upward convergence,
Fatou and the existing explicit-terminal stopping owner.
BUILD: countable-fiber conditional lower bounds, their bounded-time continuous
passage, a reusable signed first-moment estimate, horizon-independent bounds,
the actual integrable terminal limit and its lower closing projection bound,
and integrability of arbitrary stopped values with either terminal convention.

The closing input is not relabeled as the path limit. Its terminal projection
may be strictly smaller. The proofs do not assume or conclude UI or L1
convergence of the original supermartingale. Three regressions test strict
lower closure of a proper supermartingale, non-L2 random initial data, and
failure of lower closure for the process minus time. All 16 axiom checks use
only the standard three axioms. No external code was adopted. The unbounded
two-time conditional inequality remains a separate I.16 obligation.

## Unbounded lower-closed supermartingale sampling

REUSE: bounded one-sided optional sampling, lower closing bounds, arbitrary
stopping integrability, native Levy upward AE/L1 convergence, conditional
expectation restriction and indicators, and stopping-field null-set congruence.
BUILD: signed Fatou with AE/L1-convergent lower bounds, terminal-field indicator
measurability at infinite stopping, an unbounded later-time conditional bound,
and the full AE-ordered closed-supermartingale theorem. No L1 convergence or
UI of the upper supermartingale is inserted into the Fatou step.

The native terminal owner uses the lower closing variable's projection onto
`iSup F`; the unprojected corollary has an explicit terminal measurability
premise. A nonnegative supermartingale may close at zero. Regressions include
a proper supermartingale with strict lower closure, non-L2 random initial data,
a usual-filtration counterexample to unprojected infinite sampling, and signed
negative Fatou bounds. All 13 axiom audits use only the standard three axioms.
No external code was adopted. I.16 is closed with the documented native-owner
correction; regularization and the remaining semimartingale obligations remain.

## Regularization necessity and right-side L1 sampling

REUSE: project reverse one-sided UI and monotone filtration reindexing, native
Vitali convergence and monotone-function right limits, and usual-filtration
completion. BUILD: UI under any antitone deterministic clock, L1 convergence
along decreasing right-side samples, right-continuity of expectations for both
one-sided classes, and transfer to an assumed right-continuous modification.

This closes only the necessary direction of Protter I.9. No global first-moment
bound or square-integrability is added, and no path-regularized version is
assumed to equal the original at zero. Three regressions cover the initial-drop
obstruction, lack of a global L1 bound, and retained non-L2 initial data. All
11 axiom checks use only the standard three axioms. No external code was adopted.

## Local regularization skeleton estimates

REUSE: native bounded hitting times and crossing counts, project bounded
one-sided optional sampling, conditional lower-bound moment control, monotone
filtration reindexing, existing finite partitions and global upcrossing bounds.
BUILD: signed discrete and arbitrary-finite-time weak maximal estimates,
countable weak bounds, outer-measure finiteness from a finite weak constant,
one common event of local countable-skeleton boundedness, local first moments,
and rational-level clipped-process crossing finiteness at every integer horizon.

No regular paths, usual conditions, nonnegative values, L2 or globally bounded
first moments are assumed. Countable-skeleton boundedness is not relabeled as
all-real-time path boundedness, and these estimates alone do not imply that
right limits preserve the initial value. All 22 declaration/regression axiom
checks use only the standard three axioms. No external implementation was
adopted in this packet; I.9's full sufficient direction remains open.

## Simultaneous dyadic sequence limits and native crossing reversal

REUSE: existing expanding dyadic partitions, their monotone endpoint inclusion,
native crossing times/counts and deterministic convergence from bounded
crossings, and the common local skeleton estimates. BUILD: finite-prefix
crossing congruence, corrected N+1 time reversal, finite-prefix grid containment,
increasing/decreasing sample crossing bounds, the countable dense skeleton set,
and one common event of convergence for every bounded monotone dyadic sequence.

The generic congruence/reversal proofs adapt the audited existing internal
Cameron Freer implementation and retain its attribution. No external package,
legacy module import or second crossing owner is added. The final proof still
needs identification of different sequences' one-sided limits and construction
of the modification. All 24 declaration/regression axiom checks use only the
standard three axioms; cutoff loss, initial-drop obstruction and non-L2 initial
values are regression-tested.

## Actual one-sided limits and cadlag dyadic extension

REUSE: the common monotone-dyadic-sequence convergence event, native bounded
filter convergence, closed neighborhood bases and `limUnder`, and the existing
cadlag/indistinguishability owners. BUILD: indexed monotone selection, exclusion
of two persistent one-sided levels, actual subset filter limits, regularity of
right-limit extension, and the canonical dyadic right-limit process with proved
cadlag paths. The universal time quantifier remains inside one AE event.

The selector restricts to the existing skeleton and is not an unguarded use of
the full-time `rightLimitProcess`. It agrees with right-continuous inputs but
does not necessarily preserve an unregularized input at zero. Adaptation and
the modification identity under I.9's expectation hypothesis are not yet claimed.
Changed-initial-value, non-L2-initial-value and genuine-jump regressions pass;
all 21 axiom checks use only the standard three axioms. No external code was
adopted in this packet.

## Full Doob regularization and modification identity

REUSE: native Vitali/L1 convergence, conditional expectation and integral order,
the existing antitone-sampling UI, dyadic right-limit and common-event cadlag
owners, usual-filtration completeness and modification/indistinguishability.
BUILD: L1 convergence to the actual extension, its usual-filtration adaptation,
one-sided comparison with the original process, equality under right-continuous
expectations, the full I.9 equivalence, same-class preservation and uniqueness.
The true-martingale and already-right-continuous corollaries are proved.

No global first-moment bound, UI, L2 or zero-initial premise is introduced.
Modification is a proved conclusion, not a version-construction assumption.
Regressions preserve non-L2 random initial data, a proper non-UI submartingale,
and uniqueness without original path regularity. All 28 new declaration/
regression axiom checks use only the standard three axioms. No external code
was adopted. The earlier partial I.9 checkpoints are now superseded.

## Class D and Class DL stopping families

No equivalent Class D owner was found in the active Mathlib/project sources.
REUSE: finite stopping witnesses, native UI and its AE-limit closure, project
UI algebra/reindexing, optional sampling and indistinguishability. BUILD:
unbundled stopping-family Class D/Class DL, algebra and stopping stability,
bounded-family equivalence, AE-finite extension and the martingale bridges.
The nonnegative-submartingale Class DL proof keeps its positivity guard.

The exact audited Brownian snapshot's `StochasticIntegral/ClassD.lean` was
inspected: its public predicate bundles progressive measurability and the file
contains unfinished unrelated proofs. That owner and its dependency closure
were not adopted. The implementation here uses the existing project stopping
and path owners; no external code or package import was added.

All 33 declaration/regression axiom checks use only the standard three axioms.
Regressions separate local/global UI, modification/indistinguishability and
finite sampling/terminal bookkeeping, while retaining non-L2 initial values.
The explicit deterministic-UI counterexample is not right-continuous; no
cadlag counterexample is claimed by it. Doob-Meyer remains a separate proof gate.

## Discrete potential Doob decomposition

REUSE: native `Centering` predictable/martingale parts, predictable-martingale
constancy, discrete convergence and L1 conditional closure; project common
monotone paths and UI domination. BUILD: the increasing-sign supermartingale
interface, actual integrable terminal limit, potential L1 decay, full III.9
closed/UI decomposition and AE-identity uniqueness. No second selector or
closing premise is introduced.

The external Doob-Meyer reference was re-inspected for the next stage; its
generalized discrete martingale-part, predictability and later mesh/UI proofs
are unfinished. None was adopted or imported. This closure directly reuses
the proved active Mathlib discrete owner. All 11 axiom checks use only the
standard three axioms. Regressions preserve non-L2 initial data and the
increasing sign and reject dropping the vanishing-expectation condition.

## Pre-stopping fields and announcing sequences

No `F_(T-)` or announcing-sequence owner was found in the active pinned
Mathlib/project stopping hierarchy. REUSE: native stopped and predictable
sigma-fields, finite stopping witnesses, explicit terminal values, generated
measurable spaces, rational density and initial completeness. BUILD: the sole
pre-stopping field and its comparison/generator identities, predictable value
measurability, source announcing/predictable-time relations, fixed/infinite
announcing witnesses and the almost-sure III.6 field identity.

All 37 declaration/regression axiom checks use only `propext`, `Classical.choice`
and `Quot.sound`. Incremental validation passed 9520 jobs; all eight affected
final traces have zero warnings/errors. No external proof or package was
adopted. The generator theorem at infinite times explicitly retains terminal
data. Zero-terminal evaluations alone generate the bottom field there, not
the full pre-stopping field. Announcing convergence remains almost sure;
no right-continuity or initial-moment premise is introduced.

## Optional and progressive sigma-fields

REUSE: native progressive/predictable predicates and predictable sigma-field,
project cadlag/progressive bridges, initial-completeness version construction,
native stopped values and the explicit terminal owner. BUILD: the progressive
restriction field and its exact real-generator identity, optional cadlag
generators and strong optional predicate, the full source inclusion chain,
constant-ambient progressive/product equivalence, optional stopping-map
measurability and arbitrary optional stopping stability. No competing native
process predicate or implicit terminal value is introduced.

Incremental validation passed 9523 jobs. All four affected final traces have
zero warnings/errors, and all 27 declaration/regression axiom checks use only
the standard three axioms. No external code or dependency was adopted.
Regressions reject optional-implies-cadlag, preserve finite values when stopping
at infinity, and retain an explicitly supplied nonintegrable terminal input
without claiming it is a process limit. General progressive-debut and the
remaining stopping-classification proof gates are not closed by these bridges.

## Cadlag generators of the native stopped field

REUSE: native stopped-field event characterization, supported strong-measurability
transfer, optional sampling measurability, project path/version owners and
initial completeness. BUILD: right-continuous activation paths, arbitrary
stopped-measurable coefficients, exact I.6 finite cadlag/optional generator
identities, the source AE-cadlag bridge under usual conditions, and the
explicit-terminal optional generator identity at arbitrary stopping times.
No new stopped-field owner or implicit infinite-time process value is used.

Incremental validation passed 9526 jobs. A long-line warning was corrected;
all four affected final traces have zero warnings/errors. All 11 declaration/
regression axiom checks use only the standard three axioms. Regressions
preserve activation at zero, the absence of finite activation at infinity,
and nonintegrable stopped-measurable coefficients. No external code or
dependency was adopted, and no full-library build or push was performed.

## Accessible and totally inaccessible stopping times

REUSE: native stopping fields and equality-event measurability, project
announcing/predictable predicates, and Mathlib's
`Measure.exists_ae_subset_biUnion_countable` under s-finiteness. BUILD: the
finite graph and its optionality, predictable strict future, stopped-event
restriction, accessible/totally-inaccessible predicates and stability, and
full III.3 existence, reconstruction and almost-sure uniqueness. The essential
union is of a countable subfamily, not an unjustified uncountable intersection
of almost-sure statements. No competing stopping or predictable owner is used.

The 9532-job incremental build passed. After correcting two flexible-tactic
warnings, all seven affected final traces are warning/error free. All 45
public-declaration/regression axiom checks use only the standard three axioms.
Zero and infinity have distinct graph semantics; countable-valued
accessibility does not imply every accessible time is predictable. No external
implementation or dependency was adopted, and no full-library build or push
was performed. The finer predictable-graph and Meyer jump bridges remain open.

## Predictable increasing-process energy and bounded Doob approximants

REUSE: native conditional pull-out/monotonicity, Lp Fatou, predictablePart,
the project increasing-sign Doob data and monotone L1 limit construction.
BUILD: a nonnegative Fatou integrability-and-bound interface, finite energy
calculation, full III.10 Lemma 1 by truncation, and the bounded-supermartingale
conditional-tail identity, uniform 8 K^2 energy bound and actual terminal limit.
No second discrete decomposition or continuous compensator is introduced.

The incremental build passed 9536 jobs. All five affected final traces have
zero warnings/errors. All eight public-declaration/regression axiom checks
use only the standard three axioms. The two regressions show that the zero
initial condition is necessary and that the final theorem genuinely derives
terminal L2. No external implementation or dependency was used, and no full
build or push was performed. Continuous Doob-Meyer remains unimplemented.

## Predictable delays, maxima and countable suprema

REUSE: native finite stopping minima/maxima, order-topology limits, the
source announcing owner and deterministic announcing witnesses. BUILD:
nonnegative-real delay measurability, explicit predictable positive delays,
target-capped witnesses, predictable finite minima/maxima, finite/countable
stopping suprema and countable predictable suprema. Native addition does
not cover the uncountable nonnegative-real domain. No new stopping owner,
usualness assumption or everywhere convergence requirement is introduced.

The incremental build passed 9541 jobs. All six affected final traces have
zero warnings/errors. All 13 public-declaration/regression axiom checks use
only the standard three axioms. Regressions reject uncapped announcing at
infinity and exhibit failure of naive maxima on a null zero-target sample.
No external implementation or dependency, full-library build or push was
used. These closure tools do not prove III.10's conditional jump estimate.

## Predictable event restrictions and strict-limit parts

REUSE: native Levy upward convergence, stopped-field reindexing, conditional
expectations, countable stopping infima under right continuity, initial
completeness and the proved III.6 announcing-field identity. BUILD:
eventually correct measurable event approximations, tail-infimum/capped
restricted announcing data, predictable F_(T-)-event restriction and the
predictable strict-limit part of monotone stopping sequences. Its finite
coincidence with a totally inaccessible time is proved null. No conclusion
is presumed predictable, and no general F_T restriction theorem is claimed.

The incremental build passed 9545 jobs. All five affected final traces have
zero warnings/errors; all eight declaration/regression axiom checks use only
the standard three axioms. Regressions retain infinity on empty restriction
and exclude zero from the strict-limit event of the all-zero sequence.
No external implementation/dependency, full build or push was used. The
uniform conditional jump estimate and continuous Doob-Meyer remain open.

## Conditional stopping-window versions

The native conditional-expectation tower property, monotonicity, dominated
convergence and project Doob regularization give actual cadlag versions of
conditional future and left-open stopping-window probabilities. No optional
projection theorem is assumed. Right-continuous dense-set order yields
simultaneous bounds, support vanishing and width comparison. The closed lower
endpoint is justified only after proving absence of deterministic atoms for
totally inaccessible times. Version uniqueness and zero-width vanishing are
proved without a finite-measure assumption once versions are given.

The incremental build passed 9551 jobs. All seven affected final traces have
zero warnings/errors; all 16 production/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. Regressions distinguish the
zero-time atom, prove zero-width process vanishing and refute the unguarded
threshold inequality at a capped no-hit fallback. No full build, external
implementation/dependency or push was used. III.10 Lemma 2's uniform estimate
and continuous Doob-Meyer remain open.

## Bounded stopping-window sampling

Native conditional-expectation restriction/locality and equality of stopped
fields on stopping fibers give countable-valued sampling. Dominated right-grid
limits then give the bounded stopping identity for jointly measurable input
families and progressive outputs, or usual adapted/right-continuous outputs.
The source window indicator's joint measurability and right continuity are
proved separately; no optional-projection theorem is presumed. The concrete
window sampling identity, event integral identity and guarded threshold
probability bound are proved with their original strict lower endpoint.

The 9556-job incremental build passed. All six affected final traces have
zero warnings/errors after shortening two lines. All 12 production/regression
axiom checks use only the standard three axioms. Regressions sample at the
window's own bounded lifetime and at an infinite target; both give zero,
without inserting a finite totalized terminal value. No external dependency,
full build or push was used. The uniform small-window limit remains open.

## Uniform stopping-window convergence

Protter III.10 Lemma 2 is now proved through native first-hit order,
conditional sampling, predictable strict-limit avoidance and dominated
convergence. Countable initial-null-set repair produces genuinely ordered
cadlag witnesses. Width monotonicity gives the full zero-neighborhood limit;
version uniqueness transports it to arbitrary right-continuous coordinate
versions. The existing dense running supremum agrees with the full compact
interval and is almost surely finite before `toReal` is used. No uncountable
intersection of exceptional events or optional-projection axiom is assumed.

The 9564-job incremental build passed. All nine affected final traces have
zero warnings/errors. All 41 production/regression checks in
`Audit/SemimartingaleWindowUniformAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. Tests retain zero and terminal endpoints,
the deterministic-lifetime obstruction and the no-atom closed zero-width
identity. The capped no-hit guard and strict random-time lower endpoint
remain in force. No external dependency, full build or push was used.
Lemma 3 and continuous Doob-Meyer remain open.

## Actual large jumps and fixed-prefix residual estimates

The native one-sided limits, compact Lebesgue-number lemma and countable
measurable unions/intersections now yield actual stopping-time large-jump
enumeration. The generally non-right-continuous jump process is not fed into
a right-continuous hitting theorem. Finite entries are attained, distinct,
exhaustive and locally finite; repeated infinity is allowed. The process-level
totally-inaccessible jump predicate excludes only positive-time predictable
jumps and does not force a zero initial value.

Finite-prefix removal uses stopped-measurable actual jump coefficients and
zero explicitly at infinity. The missing-prefix event has probability tending
to zero, derived from pathwise escape. A measurable dense two-time envelope
and fixed-cap positive-excess dominated convergence control residual second
moments. Conditional estimates follow the pathwise clipped inequality; no
random jump-count moment or min/conditional-expectation interchange is used.

The 9580-job incremental build passed. All 18 affected final traces have zero
warnings/errors after a doc-comment line was shortened. All 120 new public
declaration/regression checks in `Audit/SemimartingaleLargeJumpAxioms.lean`
use only the standard three axioms. Four tests retain arbitrary initial
constants, exclude future jumps of a constant path, expose repeated-jump
over-cancellation and refute right continuity of a cadlag step's jump process.
No full build or push was performed. The final conditional modulus and
continuous Doob-Meyer remain open.

## Version-safe conditional modulus and random finite termination

Native s-finite countable essential unions and dense ENNReal thresholds now
construct the measurable essential supremum of an arbitrary measurable
family. The relation precedes existence and AE uniqueness. Capping at the
selected countable supremum gives actual coherent ambient-measurable versions,
not an invalid uncountable intersection of coordinate exceptional events.

The compact conditional-increment modulus is controlled by actual fixed-cap
large-jump residuals and actual regularized conditional martingales. Native
Doob L2 contraction/maximal bounds and the proved TI-window limits give
convergence in probability. Fixed AE bounds give squared-integral and
`eLpNorm 2` convergence for arbitrary filters. Actual stopping-time tail
envelopes extend this to the half-line for random AE-finite terminal times.
The raw lifetime tail converges to its infinity-atom mass, not unconditionally
to zero. The unrestricted printed terminal-lifetime domain is not certified
by this stronger-in-other-respects finite-termination theorem.

The 9598-job incremental build passed, with all 19 affected final traces free
of warnings/errors. All 90 public definition/theorem/regression checks in
`Audit/SemimartingaleConditionalModulusAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. Tests include uncountable singleton
spikes, arbitrary initial constants, zero horizons and an actual bounded
cadlag supermartingale with predictable downward jump and nonvanishing modulus.
No external implementation/dependency, full build or GitHub push was used.
The continuous Doob-Meyer construction remains open.

## Full bounded-supermartingale modulus and dyadic energy foundations

REUSE: native supermartingale convergence, conditional expectation, Doob
regularization, nonnegative-supermartingale weak maximal bounds and the existing
discrete predictable part. No outside dependency or competing grid is introduced.

BUILD: the actual terminal conditional martingale and nonnegative potential;
vanishing whole-future maximal tails; and the full bounded-supermartingale
global conditional-modulus probability/L2 limit. The source stopping-time
definition permits infinity, so the previous AE-finite-termination theorem
alone was insufficient. The new theorem needs no termination time at all and
closes III.10 Lemma 3 without using continuous Doob-Meyer.

The actual dyadic increasing parts and their left-continuous ceiling extensions
have predecessor measurability, adaptation, monotonicity, uniform `8 K^2`
second moments and actual fixed-mesh terminal limits. A predictable-difference
telescoping argument, conditional pullout and dominated convergence prove
`E[(U-V)^2] <= 2 E[W(U+V)]` under the stated conditional remaining-mean bound.
Mesh-Cauchy and continuous-limit construction are not inferred from these alone.

The 9604-job incremental build passed. All 7 affected final traces are free of
warnings/errors. All 45 public declarations in
`Audit/SemimartingaleTerminalPotentialAxioms.lean` depend only on `propext`,
`Classical.choice` and `Quot.sound`. No full build or GitHub push was performed.

## Actual dyadic terminal L2 convergence and UCP-Cauchy construction

The conditional remaining means now follow from actual discrete terminal
limits, native martingale closing and the tower property at arbitrary real
times. Finer-grid predictability is proved using the coarse predecessor, not
inferred from mere adaptedness. Exact common-grid recovery applies to the
original left-continuous ceiling extensions.

The terminal-difference energy is instantiated with the actual conditional
moduli. Native L2 Cauchy-Schwarz and existing Lp completeness produce a genuine
mesh-terminal L2 limit. Two actual conditional martingale envelopes give the
missing maximal estimate, with constant 8 and an explicit remaining-modulus
term. This proves UCP-Cauchy and a common locally uniform Cauchy subsequence;
terminal L2 convergence alone is not presented as a maximal argument.

Right increments use the existing right-limit owner, including the possibly
nonzero initial right limit. Actual modulus finiteness precedes real conversion.
The deterministic continuity bridge controls right errors, not the trivially
zero left jumps of a left-continuous step. No new grid, supremum, external
dependency or limit selector is introduced.

The 9619-job incremental build passed. All 14 affected final traces contain no
warnings/errors. All 53 checks in `Audit/SemimartingaleDyadicCauchyAxioms.lean`
use only `propext`, `Classical.choice` and `Quot.sound`. No full build or push
was performed. Continuous-compensator construction and true-martingale closing
remain open.

## Constructed continuous bounded Doob decomposition

REUSE: existing adapted cadlag UCP completeness, right-limit and continuous
version owners, common locally uniform subsequences, native conditional
expectation contraction and continuous finite-variation martingale constancy.

BUILD: an actual continuous increasing dyadic UCP limit, exact zero initial
normalization, predictability, and actual conditional terminal closing. The
bounded supermartingale theorem constructs `A` and an L2 closing variable;
`X + A` is proved a true uniformly integrable cadlag martingale. Fixed-time
L2 convergence is obtained from the actual terminal identity and contraction,
not by treating the left-continuous ceiling approximants as martingales.
The uniqueness theorem needs no boundedness or supermartingale hypothesis.

The regression uses `X_t = 1 - min(t,1)`: its nonzero initial value is retained,
and the genuinely constructed compensator is identified with `min(t,1)` by
uniqueness. Its dyadic UCP convergence remains part of the conclusion.

The 9626-job incremental build passed. All 8 affected final traces contain
zero warnings/errors. All 19 checks in
`Audit/SemimartingaleContinuousBoundedDoobAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or GitHub push was performed.
The unbounded Class D extension and III.11 remain open.

## Stopping and single-jump Doob localization

REUSE: native stopped processes and stopped sigma-fields, the local
comparison-event conditional commutation, optional stopped-coefficient
measurability, lifetime-step paths and exact jumps, Class D, open norm hits,
cadlag compact bounds, actual bounded Doob construction and continuous FV
uniqueness. No second step-process or hitting-time owner is introduced.

BUILD: arbitrary stopping for right-continuous one-sided martingales;
actual capped norm localizers with explicit overshoot hypotheses; TI-jump
coverage stability; integrable single-jump Class D and negative-jump
supermartingales; actual clipped continuous compensators and mean tail
convergence; actual compensator-difference monotonicity; and an actually
constructed stopped compensator family with proved consistency.

The 9633-job incremental build passed, with 8 clean affected final traces.
All 41 checks in `Audit/SemimartingaleDoobLocalizationAxioms.lean` use only
`propext`, `Classical.choice` and `Quot.sound`. Two checks reject the printed
pp.111--112 recombination-sign and bounded-tail errors. No full build or push
was performed. Unbounded global decomposition and III.11 remain open.

## Integrable variation and predictable conditional jump foundation

REUSE: native extended variation and monotone-composition identities, the
existing adapted variation/Jordan processes, native `Locally`, terminal-valued
sampling, the actual continuous monotone L1 terminal construction, announcing
sigma-fields, bounded optional sampling and native Levy upward convergence.
No duplicate variation, terminal selector, conditional expectation, bracket,
or external package was introduced. Local integrable variation is an abbreviation
of the native masked local property, with the unmasked source equivalence proved.

BUILD: actual terminal variation measurability and stopped-variation identity;
safe integrable-variation ownership and finite-lintegral equivalence; stopping
and masking stability; actual Jordan terminal, Class D and sampling consumers;
actual predictable left-limit and jump conditional identities. The two boundary
regressions use an infinite-variation deterministic ramp and a genuinely
nonintegrable Gaussian random initial value, respectively.

The 9656-job incremental build passed with 11 clean affected final traces.
All 44 checks in `Audit/SemimartingaleIntegrableVariationAxioms.lean` use only
standard Lean axioms. No full build or push was performed. Naturality, Yoeurp,
general predictable Doob-Meyer and predictable FV uniqueness remain open.
Printed III.20's omitted predictable-A hypothesis and III.19's signed-integral
integrability requirement are recorded as source corrections, not completed
compensator theorems.

## Actual bracket integrable variation and weighted predictable jumps

REUSE: the canonical Stieltjes primitive, Jordan measures, countably supported
integral/jump-series identity, the existing pure-jump raw bracket identity,
terminal variation measurability, integrable-variation and actual terminal
owners, predictable sampling and native conditional-expectation pull-out.
BUILD: quantitative compact/global Stieltjes variation estimates; actual mixed
bracket integrable variation with the raw initial product retained; actual
terminal AE/L1 convergence and Class D with independent initial integrability;
integrable weighted predictable jumps with zero conditional mean and expectation.

All 10 checks in `Audit/SemimartingaleBracketIntegrableVariationAxioms.lean`
use only standard Lean axioms. The 9659-job incremental build passed and all
4 affected final traces are clean. No full build, push, external implementation
dependency, duplicate bracket or terminal selector was introduced. General
naturality, Yoeurp and predictable Doob-Meyer remain unproved.

## Naturality foundation and finite mixed-sum expectation

REUSE: the existing raw bracket, actual integrable terminal and variation
owners, native conditional-expectation pull-out, Levy upward convergence and
the existing bounded/unbounded optional-sampling theorems. The announcing
left-limit identification is shared between bounded and AE-finite lifetimes.
BUILD: nonvacuous naturality and the continuous IV example; actual finite
mixed-sum L1 and terminal-product expectation without L2 of the second
martingale; actual variation domination; UI predictable-jump identities at
positive AE-finite, not necessarily bounded, stopping times.

All 25 checks in `Audit/SemimartingaleNaturalFoundationAxioms.lean` use only
standard Lean axioms. The incremental build passed 9664 jobs, with 8 clean
affected final traces. No full build or push was performed. Definition and
finite-sum results do not close III.13 uniqueness, III.14/Yoeurp or III.11.

## Full natural-martingale uniqueness (Protter III.13)

REUSE: actual raw mixed-sum expectations and variation bounds, deterministic
partition stopping, existing raw-bracket UCP convergence, native UI/L1 limits,
one-sided bracket stopping, cadlag conditional-envelope construction and
right-continuous common-event uniqueness. No duplicate bracket or terminal
owner, external package, L2 hypothesis on A, or bracket-martingale input is used.
BUILD: actual bracket terminal-product expectation for bounded M and IV
martingale A; finite-time natural bracket zero means; full III.13 equality
to zero up to indistinguishability, using the actually constructed indicator test.

The incremental build passed 9667 jobs with 4 clean affected final traces.
All 6 checks in `Audit/SemimartingaleNaturalUniquenessAxioms.lean` use only
standard Lean axioms. No full build or push was performed. III.12, III.14/Yoeurp,
predictable FV local-martingale uniqueness and III.11 remain open.

## Natural algebra and actual stochastic-integral variation

REUSE: native extended variation, existing measurability of adapted cadlag
variation, actual raw-bracket linearity, original left-continuous progressive
measurability, actual stochastic/Stieltjes integral agreement, quantitative
Stieltjes variation and the existing IV terminal construction.
BUILD: IV linear algebra with legitimate actual variation measurability;
naturality linear/version stability by actual terminal transport; Borel
measurability of the original left-continuous/caglad path; actual stochastic
integral IV, terminal AE/L1 and Class D with independent initial-product L1.
There is no bound required at time zero, no duplicate integral or terminal
owner, and no custom axiom or external package.

The incremental build passed 9671 jobs with 5 clean affected final traces.
All 17 checks in `Audit/SemimartingaleNaturalIntegralAlgebraAxioms.lean` use
only standard Lean axioms. No full build or push was performed. III.12 and
III.14/Yoeurp are not concluded from these foundations alone.

## Full naturality characterizations (Protter III.12)

REUSE: actual integration by parts, IV terminal envelopes, finite-time L2
of the bounded test martingale, local-L2 integral preservation, the integrable
envelope local-to-UI theorem, full-time UI terminal convergence, one-sided
bracket stopping and the existing I.21 zero-stopped-mean characterization.
BUILD: actual integral UI and zero mean; constructed terminal expectation
balance; full III.12 iff with actual integrable terminal existence; full
naturality iff bounded-test actual brackets are martingales, with UI forward.
Raw stopping times at infinity use the actual terminal, not `untopA` fallback.
No L2 or martingale assumption on the IV integrand is added.

The incremental build passed 9675 jobs with 5 clean affected final traces.
All 9 checks in `Audit/SemimartingaleNaturalCharacterizationAxioms.lean` use
only standard Lean axioms. No full build or push was performed. III.14/Yoeurp
and III.15 remain open. The p114 Theorem-25 citation is not recorded as a
proved jump-enumeration dependency: III.25 is a compensator continuity result,
and the following self-compensation argument cannot be assumed noncircular
here. The independently required predictable Stieltjes duality is still open.

## Actual predictable duality and FV jump coverage

REUSE: native kernel pieces/restrictions/sums, measurable mass cells, native
finite-measure generator uniqueness, composition-products, coordinate swaps,
measure trims and lower integrals; actual Stieltjes variation measures, the
constructed III.10 TI unit-jump compensator, cadlag left limits, countable BV
jump support, III.3 stopping decomposition and actual ordinary jump sequences.
BUILD: s-finiteness from finite fibers or a countable finite-fiber cover;
actual variation-kernel total mass and finite expected mass; predictable
rectangle measure uniqueness and iterated-integral equality; actual increasing
martingale-difference Stieltjes duality; continuous variation nullity on
countable sets and exact step Dirac measures; TI avoidance of predictable
countable fibers; predictable FV zero-TI-jump theorem and actual predictable
countable jump coverage. Actual predictable versions use an initial-null mask.
No candidate compensator, naturality, self-compensation or jump enumeration
is smuggled into a source-existence premise. Infinity is handled explicitly.

The packet also builds deterministic discontinuous natural examples and L1
before-field multipliers of bounded martingale jumps at positive AE-finite
predictable times, without requiring boundedness or L2 of the multiplier.
The incremental build passed 9690 jobs with 16 clean affected final traces.
All 41 checks in `Audit/SemimartingalePredictableJumpCoverAxioms.lean` use only
standard Lean axioms. No full build or push was performed. Disjointifying
predictable graphs and the legitimate full jump-series expectation argument
remain for III.14; Yoeurp, III.15 and general predictable III.11 remain open.

## Positive disjoint predictable graphs and actual jump-series bounds

REUSE: actual capped announcing sequences, native before sigma-fields and
initial completeness, existing predictable restrictions and finite graph
owners, true UI optional sampling and terminal convergence, native infinite
sum support reindexing, and actual positive/negative variation Stieltjes parts.
BUILD: before-field comparison/equality with a predictable time; exact general
and positive disjoint graph restrictions; a constructed positive disjoint FV
jump cover; actual IV stopped-jump L1 and original before-field measurability;
actual terminal-valued predictable UI jump identities including infinity,
and L1 weighted zero conditional/ordinary means; exact lifetime reindexing,
summability and finite partial-sum bounds from actual path variation.
The martingale terminal at infinity cancels as Z-Z; no fabricated finite
evaluation, initial-value integrability or L2 coefficient assumption is used.

The incremental build passed 9697 jobs with 8 clean affected final traces.
All 24 checks in `Audit/SemimartingalePredictableDisjointSeriesAxioms.lean` use
only standard Lean axioms. No full build or push was performed. The final
actual bracket expectation/terminal consumer for III.14 remains separate.

## Full predictable naturality and predictable FV local-martingale constancy

REUSE: the actual disjoint predictable jump cover, native before sigma-fields,
terminal-valued UI predictable-jump identities, L1 multiplier pullout, actual
lifetime-series reindexing and variation domination, Bochner dominated
convergence, actual bracket IV terminal convergence, and the existing naturality
characterization. The III.15 proof independently reuses masked UI localization
and continuous FV local-martingale constancy, not III.14 or local IV.
BUILD: actual bounded-test bracket L1 and zero expectation; full III.14;
bounded-test IV Yoeurp UI martingality; exact pathwise masked/stopped jump
sampling; zero predictable stopped jumps of a predictable FV local martingale,
continuous paths and full III.15 constancy with arbitrary initial values;
uniqueness of both supplied predictable FV/local-martingale decomposition parts.
No assumed jump cover, terminal, bracket martingale or decomposition existence
is used to claim an existence conclusion. Initial and infinite-time values
retain the existing raw-bracket and explicit-terminal conventions.

The incremental build passed 9702 jobs with 6 clean affected final traces.
All 12 checks in `Audit/SemimartingalePredictableNaturalUniquenessAxioms.lean`
use only standard Lean axioms. General predictable III.11 and local III.16
existence remain open. No full build or push was performed.

The III.11 residual requires a signed conditional-mean argument: the current
TI modulus proof bounds an unweighted jump-occurrence window after taking
norms, which is not implied by zero conditional predictable jump means.
Amplitude-selecting a centered predictable jump also need not keep it centered.
Thus both the regular bounded modulus and its general Class D localization
require real new proofs; the existing TI hypotheses cannot simply be weakened.

## Regular signed compact moduli and source-exact conditional variation

REUSE: actual predictable strict-limit restrictions, Class D UI and Vitali,
Doob regularization, legitimate cadlag versions and stopped conditional
sampling, common-event right-continuous order, first-hitting/truncation owners,
actual conditional modulus and countable running supremum. The compact proof
uses signed conditional increments, not norms of unweighted jump occurrences.
BUILD: stopping-expectation left continuity with the actual jump-corrected L1
limit; actual shifted projections and coherent residuals; first-threshold
maximal convergence under Class D; the bounded-supermartingale Class D bridge
and full zero-width compact conditional-modulus convergence without TI jumps.
The first-threshold intermediate is Class D-level, while the source projection
existence/compact consumer in this packet is bounded. General III.11 existence
is not inferred from these estimates.

Active-pin/local duplicate checks found no existing quasimartingale or
conditional-variation owner. BUILD: the actual terminal-zero partition sum,
extended expected/global conditional variation, separate finiteness predicate
and adapted/cadlag/coordinate-L1 quasimartingale predicate. REUSE: the existing
TimePartition, conditional expectation, Bochner integration and supermartingale
regularization. The nonnegative-supermartingale exact variation identity and
the III.17 easy direction include the otherwise missing terminal-tail bound.
Existing `sum_cells_eq_of_range_eq` already supplied the generic endpoint
invariance theorem; it was reused, not duplicated. Sorted endpoint sets give
strict representatives and exact equality with the source strict-partition
supremum, including the singleton endpoint at zero. III.17 converse/Rao remain.

The incremental build passed 9712 jobs with 11 clean affected final traces.
All 35 checks in `Audit/SemimartingaleRegularConditionalModulusAxioms.lean`
use only standard Lean axioms. No full build or push was performed.

## Bounded regular Doob construction and actual single-jump compensation

REUSE: actual terminal potentials and maximal inequalities, the existing
global modulus, dyadic energy/L2/UCP/closing proof owners, stopping restriction
and jump sampling, announcing sequences, before-field generators, native
conditional expectations, Class D domination and the original variation owner.
The six TI interfaces are preserved as source wrappers around generic modulus
proofs. Their bodies were refactored rather than copied into a new construction.
BUILD: regular global probability/L2 convergence, the source bounded regular
continuous Doob decomposition, stability of the jump-mean condition under
arbitrary stopping, actual predictable closed futures/graphs/coefficient steps,
before-centered single-jump UI martingality, exact single-jump global variation
and the explicit predictable compensator with its first-moment variation bound.
Only initial completeness is needed for closed-future predictability. The raw
single-step IV theorem needs only measurable lifetime and an L1 coefficient.
No finite lifetime, compensator or assumed terminal is introduced.

REUSE: existing finite partitions, prefix sums, conditional Jensen and tower
properties. BUILD: pure cell-cost refinement and actual conditional variation
refinement, separately for positive/negative/absolute components and their
terminal tails. Almost-sure ordering is after conditioning at the initial field,
not a false pointwise ordering of the unconditioned sums. Rao remains open.

The incremental build passed 9722 jobs with 16 clean affected traces. All 35
checks in `Audit/SemimartingaleRegularBoundedSingleJumpAxioms.lean` use only
standard Lean axioms. No full build or push was performed.

## Regular bounded-jump Class D, general single jumps and directed envelopes

REUSE: the actual regular bounded construction, norm exits, continuous FV
uniqueness and the generic Class D localization/terminal owner. BUILD: actual
regular stopped decompositions, TI-free consistency and the bounded-jump
Class D continuous Doob theorem. No supplied local compensator, consistency,
terminal or convergence certificate appears in the source theorem.

REUSE: actual accessible/TI classification, predictable graph restrictions,
native Tonelli, conditional expectations, martingale convergence and variation.
BUILD: actual disjoint stopped-coefficient decomposition, signed closed-step
series uniform convergence/cadlag paths, exact predictability, integrable
variation and UI closure. Accessible compensation uses the actual series;
signed TI compensation uses the existing continuous nonnegative construction.
General positive-lifetime compensation combines disjoint masked coefficients,
retaining the sharp E variation <= E norm D budget. Infinite lifetime is never
evaluated as a finite time; no vanishing coefficient at infinity is required.
Regular conditional centering separately requires actual jump integrability.

REUSE: the native essential-family supremum and finite-partition owners.
BUILD: directed-family integral equality/bounds and finite-to-L1 conversion;
actual positive/negative fixed-horizon partition envelopes; exact horizon
extension/prepending, adapted all-horizon directedness and shift variation
comparison. Real conversion follows extended-value finiteness, not the
default real value of infinity. General regular Class D, III.11 and Rao
existence remain open; these intermediate results do not assert them.

The incremental build passed 9738 jobs with 18 clean affected traces.
All 35 checks in `Audit/SemimartingaleRegularClassDSingleJumpAxioms.lean`
use only standard Lean axioms. No full build or push was performed.

## Stationary finite-stopping laws — checkpoint 2026-09-12

REUSE: native IdentDistrib.pi, actual finite-set sorting, joint independent
increments and telescoping. BUILD: true finite future-vector stationarity
with the original initial value retained. REUSE: ordered-past independence
and disjoint measurable-space suprema. BUILD: independence of the whole
future vector from the original past field, not a pairwise surrogate.

REUSE: existing countable stopping-fiber conditional sampling, countable
measurable pasting, actual upper dyadic stopping grids, conditional towers
and dominated convergence. BUILD: constant conditional projections at any
genuinely finite stopping time and the single/full finite-vector stationary
increment consumers. REUSE: native AE measurability of actual sequential
limits and bounded-continuous finite-measure extensionality. BUILD: the
original stopped vector's true image-law equality, without extra usualness,
initial normalization, moment or deterministic stopping-bound hypotheses.

REUSE: the sole denseRunningSupremum, right-continuity neighborhoods and native
measurable-indicator convergence. BUILD: centered shrinking initial-window
suprema and their strict positive-threshold event measures tend to zero.
There is no new process/supremum selector or random-lag independence premise.
General cadlag real-SII TI classification was not concluded by this historical checkpoint.

Verification: 10027 incremental jobs, 8 affected / 8 rebuilt clean traces,
9 standard-axiom-only checks. No external source code or package was added.
Publication and pause are explicitly requested for this checkpoint; no full build.

## Cadlag real-SII predictable jumps and natural-usual TI

REUSE: finite future laws after genuine stopping times, the sole dense running
supremum, right-continuity shrinking-window convergence and native convergence
in measure. BUILD: exact dense post-stopping supremum laws and their uniform
shrinking-window tails, with no random-lag independence or moment premise.

REUSE: source announcing sequences, everywhere-finite stopping-time wrappers,
dyadic upper grids, native AE metric limits and the existing predictable-test
classification of TI jumps. BUILD: actual finite announcing sample increments
converge AE to zero at a zero target and to the positive-time jump otherwise;
coordinate measurability plus common-event right continuity makes every finite
stopping-time sample AE measurable. A uniform stopped-window bound makes the
same increments converge in measure to zero. Uniqueness in measure therefore
forces each finite predictable positive-time jump to vanish. Integer truncation,
not an uncountable AE intersection, extends this to arbitrary possibly-infinite
predictable tests.

REUSE: the exact natural-filtration independent-increment theorem, genuine
completion/augmentation and stationary-increment image-law semantics. BUILD:
stationary increment laws survive completion and a measurable AE-zero-initial
cadlag real SII process has TI jumps in the genuine completed usual augmentation
of its own natural filtration. The original process is retained. There is no
arbitrary information enlargement, totalized value at infinity, replacement
process or external dependency.

This closes the general cadlag real-SII TI consumer. It does not construct a
cadlag version of the canonical Levy coordinate process, prove Levy
decomposition, or prove Meyer's strong-Markov/Feller theorem.

Verification: 10033 incremental jobs, 7 clean production rebuilds and all 11
checks in `Audit/SemimartingaleSIIInaccessibleAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## Canonical terminal density and cadlag density process

REUSE: native `rnDeriv`, real conversion, integrability and exact set-integral
reconstruction. BUILD: the project terminal real density with explicit
measurability, pointwise nonnegativity, integrability and total mass one.

REUSE: Mathlib's conditional-expectation martingale/UI family and StochLean's
proved dyadic right-limit regularization under usual conditions. BUILD: one
canonical cadlag density process, its fixed-time AE conditional-expectation
identity, true martingale and UI properties, and one common event on which it is
nonnegative at every time. Exact current-filtration event integrals recover the
target law. `F_0` triviality, strict positivity, inverse density and zero-density
localization are not smuggled into this owner.

This is the noncircular foundation for Protter III.8. Equivalent and merely-AC
Girsanov--Meyer, Kazamaki/Novikov, Brownian acceptance and the BD transfer remain
separate BUILD obligations.

Verification: 10034 incremental jobs, 2 clean production rebuilds and all 13
checks in `Audit/SemimartingaleDensityProcessAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## Fixed-time strict positivity of density processes

REUSE: Mathlib RN-derivative positivity, finiteness, trimming and the theorem
identifying a trimmed real RN derivative with conditional expectation. BUILD:
strict positivity of the terminal density `Q`-AE under `Q ≪ P`, strict
positivity of every fixed-time canonical density `Q`-AE, and their `P`-AE
equivalent-measure corollaries. The project also proves the general integrable
real conditional-expectation strict-positivity lemma used by the reverse-AC
route.

The one-way theorem transports the trimmed derivative's positivity through
`toReal_rnDeriv_trim`; it does not use an invalid measurability exchange between
terminal density and `F_t`. The conclusions are coordinatewise. Common-event
all-time positivity, inverses and Girsanov remain separate BUILD obligations.

Verification: 10035 incremental jobs, 2 clean production rebuilds and all 6
checks in `Audit/SemimartingaleEquivalentDensityAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build. The GitHub push retry failed
at the network layer because `github.com:443` was unreachable.

## Fixed-time reciprocal densities and Bayes formulas

REUSE: Mathlib's inverse RN derivative, trimmed RN/conditional-expectation
identity, RN change-of-measure integrability and set integrals, conditional
expectation set-integral uniqueness, and measurable-factor pull-out. BUILD:
the fixed-time forward/reverse reciprocal identity under equivalent laws, its
source-measure transport, the one-way division-free Bayes identity, and the
target/source AE quotient corollaries.

The primary Bayes theorem requires only `Q ≪ P` and integrability under `Q`;
reverse AC and quotient integrability are not inserted as premises. Every
division occurs on the already proved fixed-time strictly-positive event.
No stopping-time or common-event reciprocal identity and no Girsanov theorem is
claimed here.

Verification: 10036 incremental jobs, 2 clean production rebuilds and all 5
checks in `Audit/SemimartingaleReciprocalBayesAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## Common-event reciprocal density paths

REUSE: StochLean's right-continuous-modification uniqueness, cadlag path
transport under absolute continuity, path multiplication and the fixed-time
reciprocal/strict-positivity layer. BUILD: indistinguishability of the
reverse-forward density product from constant one, common-event all-time strict
positivity/nonvanishing, indistinguishability of pointwise inverse with the
reverse canonical density, and cadlag regularity of that inverse.

The proof uses countable dense-time reduction hidden in the existing
right-continuous uniqueness theorem; it does not form an uncountable AE
intersection. Stopping-time sampling, left-limit localization and Girsanov are
separate BUILD obligations.

Verification: 10037 incremental jobs, 2 clean production rebuilds and all 5
checks in `Audit/SemimartingalePathwiseReciprocalAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## Density processes at finite stopping times

REUSE: StochLean's arbitrary-closing-variable continuous optional sampling,
native finite stopping-time field, exact RN set-integral reconstruction and
trimmed RN/conditional-expectation identity. BUILD: conditional identification
and integrability of `Z_T`, exact target-law integration on every `F_T` event,
one-way target-law strict positivity, its equivalent-law source corollary, and
the sampled reciprocal identity.

The closing theorem correctly projects arbitrary terminal inputs at infinity;
because `T` is everywhere finite, its sample is the ordinary process value.
No hidden terminal-field measurability premise is introduced. The one-way
positivity proof trims directly to `F_T` rather than transferring from a
source-AE statement.

Verification: 10038 incremental jobs, 2 clean production rebuilds and all 7
checks in `Audit/SemimartingaleStoppingDensityAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## Equivalent-density localization and left limits

REUSE: canonical forward/reverse density martingales, cadlag path transfer,
capped norm-exit localization, process-level reciprocal identity and
left-limit multiplication. BUILD: the joint minimum localizer under both
equivalent laws, pre-exit bounds, common-event positive-time left-limit product
one, strict positivity, reciprocal identification and localized norm bounds.

The stopping-time minimum is reconstructed from its measurable event union to
avoid an incoherent `NNReal` preorder instance generated by a generic `min`
theorem; its mathematical stopping-time, monotonicity and divergence properties
are proved directly. Division excludes time zero, where the project deliberately
uses Protter's `Z_{0-}=0` convention.

Verification: 10039 incremental jobs, 2 clean production rebuilds and all 9
checks in `Audit/SemimartingaleEquivalentDensityLocalizationAxioms.lean` use
only `propext`, `Classical.choice` and `Quot.sound`. No full build or push.

## Equivalent-law martingale transfer

REUSE: canonical density martingales, the division-free Bayes identity,
conditional-expectation towers, integrable closing variables and the exact RN
integrability equivalence. BUILD: multiplication by `Z = dQ/dP` transfers true
martingales from `Q` to `P`, and multiplication of an actual closing variable
transfers uniform integrability. The native masked fundamental sequence then
transfers local martingales without changing the project's zero-time convention.

The proof transports only established AE equalities through the reverse
absolute continuity and never cancels a density. It therefore has no hidden
pointwise-positivity premise. Fundamental-sequence convergence and path
regularity are transported only through `P ≪ Q`. Girsanov covariation
corrections are deliberately left to their own modules.

Verification: 10040 incremental jobs, 2 clean production rebuilds and all 3
checks in `Audit/SemimartingaleMartingaleTransferAxioms.lean` use only
`propext`, `Classical.choice` and `Quot.sound`. No full build or push.

## Equivalent-measure raw-bracket Girsanov--Meyer (Protter III.39)

REUSE: raw quadratic covariation, product-minus-bracket local martingales,
integration by parts, stochastic-integral absolute-continuity invariance,
right-value finite-variation Stieltjes realization, pathwise reciprocal
densities and local-martingale density transfer. BUILD: the raw density bracket
`B=[Z,M]`, the auxiliary target-local integral `∫B₋dW`, the division-free
correction `WB-∫B₋dW`, its right-integral expansion, exact initial value and the
final target-law local martingale.

The proof uses the raw bracket required by III.39, not the predictable bracket
of III.40. The extra `[W,B]` converts the predictable left-value integral into
the right-value source formula. At zero it combines with the raw initial
product to give `R_0=M_0`; neither initial-field triviality nor `Z_0=1` is
assumed.

Verification: 10041 incremental jobs, 2 clean production rebuilds and all 11
checks in `Audit/SemimartingaleGirsanovMeyerAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## Predictable Girsanov theorem (Protter III.40)

REUSE: the canonical predictable compensator of the raw mixed bracket,
product-minus-predictable-bracket local martingales, equivalent-density left
limits, right-value integral compensation, raw bracket environment invariance
and density transfer. BUILD: the selected density angle `⟨Z,M⟩`, its target-law
left correction, a right-value companion, the product proof for that companion,
zero initial value and the final predictable-compensator reduction.

The hypothesis is exactly local integrable variation of the actual raw density
covariation; no predictable bracket is supplied by the caller. The inverse
notation is justified only at positive times by the reverse-left-density
identity. The construction retains explicit usualness of both equivalent laws.

Verification: 10042 incremental jobs, 2 clean production rebuilds and all 8
checks in `Audit/SemimartingalePredictableGirsanovAxioms.lean` use only
`propext`, `Classical.choice` and `Quot.sound`. No full build or push.

## Whole natural past, genuine completion and Poisson jump classification

REUSE: native finite-family preimage intersection characterization of
iIndepFun and the actual completion measure. BUILD: arbitrary jointly
independent families survive completion without pairwise substitution or
additional measurability/finite-measure assumptions. REUSE: existing HasLaw
completion and original common-event Poisson paths. BUILD: the same Poisson
process on the genuine completed sample space. Original AE monotonicity
justifies natural-subtraction casting to real independent increments.

REUSE: native joint independence of adjacent grid increments, independent
suprema of disjoint generated fields, finite-set sorting and exact telescoping.
BUILD: every actual finite natural-past vector is independent of a future
increment. REUSE: native process cylinder independence and natural_eq_comap.
BUILD: whole natural-past independence for measurable AE-zero-initial real
independent-increment processes. There is no path or supplied-past premise.

REUSE: natural-filtration minimality, measurable natural casting and native
measurable floor with exact floor_natCast. BUILD: equality of the count and
real-count raw natural filtrations for any preordered index, without a measure.
REUSE: original right-continuous increment-independence augmentation, genuine
completion and original Poisson jump/arrival TI consumers. BUILD: true usual
natural-filtration Poisson TI jumps and original arrival clocks, including
zero rate and infinite arrivals. No arbitrary information enlargement and
no general Levy/Meyer closure are inferred.

Verification: 10020 incremental jobs, 7 affected / 7 rebuilt clean traces,
9 standard-axiom-only checks. No full build or push.

## Nonnegative jump classification and genuine Poisson arrival graphs

REUSE: actual UI fundamental localization, positive predictable restriction,
possibly-infinite predictable jump integrability/CE0 and exact masked-stopped
jump sampling. BUILD: nonnegative positive-time native LM jumps vanish at
each predictable test, with no original initial moment or global jump L1.
REUSE: actual everywhere-cadlag version, genuine large-jump finite graphs
and existing countable coverage. BUILD: predictable-zero-test converse to
the sole HasTI owner under arbitrary source measure, preserving per-test
AE quantifiers. No new stopping-time selector or all-tests-common event.

REUSE: source jump subtraction and continuity. BUILD: native nonnegative
LM jump classification and the original-source continuous-subtraction
consumer. REUSE: actual canonical compensator properties and proved
TI-to-continuity direction. BUILD: full continuous-sole-compensator iff
under nonnegative positive-time jumps on the existing local-IV domain;
continuous signed source movement and the initial value remain unrestricted.

REUSE: original hitting-arrival properties, true strict-before count bounds,
cadlag left-limit passage and unit jumps. BUILD: every original finite
arrival has jump exactly one, on one event for all indices.
REUSE: original compensated Poisson LM under genuine past independence,
linear continuous drift, counting membership and the sole HasTI graph test.
BUILD: original Poisson jumps and original hitting arrivals are TI, including
rate zero and infinite tails. This does not supply natural-past independence
or the general Meyer--Feller/Levy theorem.

Verification: 10014 incremental jobs, 7 affected / 8 rebuilt clean traces,
8 standard-axiom-only checks. No full build or push.

## Actual crude-rate limits and dependent-censoring compensation

REUSE: native RN measurability, integral bounds, finite-law real derivatives
and Lebesgue differentiation. BUILD: vanishing infimum of actual RN densities
from infimum mass zero, followed by an a.e. window-rate sandwich on one
countable event. BUILD: true thin censoring regions with empty intersection,
continuity-from-above mass limit, actual pushforward domination and the
triangular-window bound. These prove the real original wedge rate zero a.e.,
without independence, a joint density or an assumed error limit.

REUSE: native map/restrict and singleton-null AC, finite RN reconstruction
and withDensity restriction. BUILD: actual finite lifetime window conversion,
one native RN density for every original positive cap, and the actual crude
window's a.e. limit through finite ENNReal-to-real addition. The full real
arrival law is the AC hypothesis, not a supplied cause-density certificate.

REUSE: actual marked/censored sole compensation and interval-integral AE
congruence. BUILD: literal joint-survival density and RN primitives, actual
crude filter-limit compensation, and the original count's native LM
remainder in its genuine usual natural filtration. REUSE: relative complete
measurable congruence for the actual version; no second compensator selector.
BUILD: actual net-rate RN identity and the printed net-equals-crude corollary,
requiring equality only at positive joint survival. Actual observation-law
positive closed survival controls all stopped integration intervals on one
event. Null-time limit fallback and zero-survival quotients are not treated
as genuine conditional limits there.

Verification: 10008 incremental jobs, 12 affected / 12 rebuilt clean traces,
19 standard-axiom-only checks. No full build or push.

## Canonical marked compensation and literal censoring windows

REUSE: actual cause-hazard balance, marked natural-information traces,
predictable stopping, native noninjective integral pullback and conditional
expectation uniqueness. BUILD: the original marked count's true martingale
remainder under a finite measure. REUSE: bounded single-jump global IV,
common-event cause paths, genuine raw right continuity and usual augmentation,
and the sole canonical compensator's full uniqueness. BUILD: actual marked
and arbitrarily dependent censored compensation, retaining ties and zero or
infinite lifetimes without an initially revealed mark or candidate certificate.

REUSE: restricted law change of variables, withDensity and native interval
integration. BUILD: actual cause-density primitives with observation survival
and their common-event marked sole-compensator consumer. REUSE: genuine
Tonelli mean, monotone convergence and norm domination of UI families. BUILD:
whole-halfline stopped cause-hazard UI from an actual L1 supremum envelope,
with only finite observation measure and true cause domination.

BUILD: exact joint-survival and disjoint crude-window identities with the
within-window censoring error retained. REUSE: native RN real integrability,
Lebesgue differentiation, actual RN set integrals and derivative slopes.
BUILD: finite absolutely continuous real-law right-window rates almost
everywhere, without continuous-density or target-limit certificates.
The error-window limit and printed crude-rate identification remain open.

Verification: 9997 incremental jobs, 9 affected / 9 rebuilt clean traces,
13 standard-axiom-only checks. No full build or push.

## Density primitives and actual cause-hazard / marked-information foundations

REUSE: actual restricted pushforward, native withDensity integration, interval
integration and the existing finite hazard bound. BUILD: density divided by
original closed survival as the actual cumulative hazard primitive, first in
ENNReal and then in real L1. A common positive-survival event at the lifetime
identifies all stopped times and the original sole compensator. Initial and
infinite atoms remain in the denominator; no primitive certificate is assumed.

BUILD: the mathematically distinct cause-specific integral against a genuine
submeasure, with the observation survival denominator. Selecting the whole
law recovers the existing ordinary hazard. REUSE: measure domination,
Tonelli, native absolute continuity and AE positive closed survival. BUILD:
the real cause mean and strict-survival increment identities only after
extended finiteness. Dominated convergence and monotonicity prove actual
common-event cadlag paths, without a replacement process or support guard.

REUSE: native natural-filtration comap history, strong adaptation and stopping.
BUILD: actual marked-pair observation measurability, survival trace and original
lifetime stopping, followed by raw right continuity using frozen history and
two paths' common future survival. No initial revelation of the mark, measure
completion assumption or finite lifetime is inserted.

Verification: 9989 incremental jobs, 8 affected / 8 rebuilt clean traces,
22 standard-axiom-only checks. The marked compensation consumer remains open.
No full build or push.

## General count compensation and density / censoring inputs

REUSE: genuine natural adaptation, existing completion probability instance,
actual count-to-local-IV theorem and the sole canonical compensator. BUILD:
the original AE count's natural-usual compensation domain and its conditional-
gap finite hazard formula via the actual arrival representative, usual natural
information equality and canonical compensator congruence. All conditional
laws remain under the original measure. No count expectation or candidate
compensator is supplied, and the original count determines the finite index.

REUSE: native withDensity integration, real interval integral and the fundamental
theorem of calculus. BUILD: the actual right conditional-window rate from a
continuous probability density and positive survival, including the real L1
proof from finite total mass. REUSE: measurable minimum, restricted measure,
map congruence and map monotonicity. BUILD: the arrival-marked censored
observation submeasure and its two genuine domination statements. Ties remain
arrivals; no independence or normalization is assumed.

Verification: 9982 incremental jobs, 5 affected / 5 rebuilt clean traces,
5 standard-axiom-only checks. Explicit density integration and full censored
compensation are not claimed by these inputs. No full build or push.

## Independent latent-duration compensation and actual representative transport

REUSE: native independence of disjoint finite coordinate vectors and
measurable function composition. BUILD: actual prefix-history independence
and the original marginal conditional law only on the finite-past event.
The active event forces finite past; inactive hazards are zero, so the
existing canonical compensator equals the original marginal-hazard series
without declaring absorbing gaps independent after infinity.

REUSE: genuine extended prefix arrival construction and conditional canonical
compensation. BUILD: latent completed-plus-pending path algebra and its sole
compensator consumer, with the corrected initial interval and completed-sum
index. Positivity and actual prefix divergence construct the domain rather
than replacing it with a compensation certificate.

REUSE: native natural-filtration generators, null-set completion and
measurability under AE equality. BUILD: equality of genuine usual natural
augmentations for indistinguishable metrizable Borel processes under any
measure. REUSE: actual hitting-time properties and common-null-set arrival
version. BUILD: an everywhere-valid arrival sequence whose actual guarded
count is indistinguishable from the original adapted count. No raw natural
equality or finite-count moment is assumed.

Verification: 9978 incremental jobs, 7 affected / 7 rebuilt clean traces,
6 standard-axiom-only checks. The general-count canonical hazard consumer
remains separate work. No full build or push.

## Canonical arrival compensation and conditional-law specialization foundations

REUSE: actual stage UI martingales, raw natural right continuity, genuine
usual-augmentation transport, ordinary UI stopping and native localization.
BUILD: the actual total compensated count's local martingale proof with its
original positive arrival sequence. Actual compact finite support and the
birth-endpoint stopped-prefix identity justify the reduction.

REUSE: the count's unit-jump local-IV domain and full sole-compensator
uniqueness. BUILD: canonical conditional-hazard identification on the completed
space, with kernels retained from the original measure. Countably many true
kernel equalities give the actual-gap-history formula at all times on one
event. Pure completed/pending algebra gives the explicit finite source formula
without dropping count zero or the next birth endpoint.

REUSE: finite-kernel composition-product uniqueness and actual restricted
joint laws. BUILD: conditional-law equality on a history event, with arbitrary
sample/history spaces and only a finite ambient measure. Native independence
and product joint laws give the original constant marginal conditional kernel.
Positive extended prefix sums construct actual nonexplosive arrivals; finite
preceding sums, not arbitrary infinite subtraction, justify latent-gap recovery.

The conditional III.23 formula is established on the everywhere-valid arrival
domain. Independent specialization and AE-representative transport remain
separate work. Verification: 9972 incremental jobs, 9 affected / 9 rebuilt
clean traces, 11 standard-axiom-only checks. No full build or push.

## Actual arrival-stage martingales and compact finite hazard support

REUSE: original conditional clock UI and survival-increment identities,
actual finite-history event traces and delayed predictability. BUILD:
true uniformly integrable compensated arrival stages in the raw natural
count filtration. The actual history is not treated as initial information.

REUSE: native hitting-time indicator sum on a Unit Dirac space, original
arrival recovery, count-at-arrival and count monotonicity. BUILD: pointwise
count sums, stopped count caps and native positive arrival localization.
The localization theorem requires only an arbitrary measure.

BUILD: actual hazard zero support including the birth endpoint; stage
predictability, exact initial zero and common-event monotone cadlag paths.
REUSE: native finite-support summability, finite sum inequalities and the
proved locally uniform cadlag limit theorem. BUILD: compact-finite real path
series and the actual conditional-hazard sum, with native strongly measurable
series for exact predictability. No expected total count bound is needed.

BUILD: exact stopped finite-prefix algebra, including the next stage's
zero birth endpoint. A merely horizon-based truncation would incorrectly
drop the current pending stage. Genuine-augmentation local martingality
and sole compensator identification are not inferred from path properties.

Verification: 9964 incremental jobs, 9 affected / 9 rebuilt clean traces,
11 standard-axiom-only checks. No full build or push.

## Safe clocks and actual conditional-information invariance

REUSE: native conditional-expectation representation, finite measure
extensionality on products and finite-kernel composition-product uniqueness.
BUILD: equality of evaluated native conditional distributions from equality
of generated information, on one common event of equality of measures.
The actual arrival/gap history consumer keeps empty and infinite-tail
histories and does not equate arbitrary kernel labels.

REUSE: original positive absorbing gaps, prefix recovery and calendar-stop
hazard identity. BUILD: jointly measurable monotone calendar-bounded safe
elapsed clocks and exact original-arrival/gap-event and hazard identities.
The finite minimum, not an infinite starting time, is evaluated.
Original-space clock UI and zero-increment tests use the actual conditional
joint law and an integrable indicator; injectivity and optional sampling
of arbitrary clocks are not assumed.

REUSE: native right-ray composition and monotone real left limits. BUILD:
monotone-path cadlag time change and its single-common-event conditional
hazard consumer. No arbitrary cadlag/continuous-composition principle or
uncountable AE quantifier exchange is used. The starting lifetime needs
no measurability for this purely pathwise consumer.

Verification: 9956 incremental jobs, 7 affected / 7 rebuilt clean traces,
9 standard-axiom-only checks. Full natural-count segment martingales and
the localized compensation sum remain open. No full build or push.

## Natural information, conditional-law pullback and delayed activation

REUSE: native natural-filtration comaps, stopped sigma fields, strict-future
predictability of restricted stopping times and predictable stopping maps.
BUILD: raw count right continuity by eventual equality of genuinely frozen
observations, actual finite-history measurability at the preceding arrival,
and exact arrival/gap history-field equality on the actual valid sequence.
No intersection/comap interchange, ambient history isomorphism, or universal
cadlag-natural-filtration right-continuity claim is made.

REUSE: native conditional distributions and exact composition-product
disintegration. BUILD: original-space L1/mean, UI and common-event hazard
paths, using a genuinely measure-preserving pair map. The lifetime target's
standard Borel structure is constructed from the native ENNReal instance;
the original space and history need no such assumptions. Noninjective maps
use actual integral-map transport, not the injective integral-comp theorem.

BUILD: zero-starting Borel delayed activation from true stopped-field marks,
its actual calendar-stopped kernel-hazard consumer and absorbing-gap clock
identity. No history is exposed at zero, no gap is treated as a calendar
stopping time, and no infinite calendar value is evaluated.

REUSE: the verified single-law martingale, kernel Fubini and common-event
monotonicity. BUILD: actual bounded-clock hazard L1 and survival-increment
integral identities; clock-family UI follows from a genuine UI domination,
not moment bounds alone or optional sampling of arbitrary clocks.
The actual full-count compensated segments and localized sum remain open.

Verification: 9950 incremental jobs, 8 affected / 8 rebuilt clean traces,
13 standard-axiom-only checks, no full build or push.

## Actual kernel hazard and finite-history foundations

REUSE: the sole extended cumulative-hazard owner, native kernel measurable
sections, parameterized integrals, composition-product Tonelli and actual
closed-survival positivity. BUILD: joint stopped-hazard mean, a jointly
measurable common-event path bridge and real L1/UI consumers. The path bridge
exposes the existing pointwise positive-survival proof without changing its
earlier public consumers. UI uses a genuine integrable integer supremum
proved finite before real conversion; no first-moment-only shortcut is used.

REUSE: native natural filtrations/comaps and the existing guarded arrival
count. BUILD: exact finite-history trace representation on next-arrival
survival. Actual interarrival gaps use the extended difference only when
the previous arrival is finite; the infinite branch is explicit. Prefix
recovery is also proved on the infinite tail. No independent-gap hypothesis,
alternative arrival/count selector or conditional-law owner is introduced.
The full history-activated compensation theorem is still open.

Verification: 9943 incremental jobs, 7 affected / 16 rebuilt clean traces,
14 standard-axiom-only checks, no full build or push.

## Source-strength III.21 absolute-continuity and exponential corollaries

REUSE: native absolute-continuity derivative integrability, FTC, nonnegative
monotone derivatives, interval measure extensionality, actual map/restriction
identities and the existing weighted-measure/RN hazard owner. BUILD: the
actual Stieltjes-function-to-measure AC bridge and direct original-space CDF
consumers, including the already selected compensator's common-event paths.
No density representation, version selector or path-regularity certificate
is supplied as an input. The finite-lifetime event is established before
the CDF-coordinate measure comparison.

REUSE: native exponential law, map-map identity, verified finite hazard and
sole canonical compensator. BUILD: the original stopped-clock equality and
actual compensator identification with its general positive rate. Infinite
original samples do not prevent finite stopped-clock evaluation, whose
finiteness is proved explicitly. No extra almost-sure finiteness assumption
or parallel compensator is introduced.

Source audit: III.23 uses conditional survival, not a CDF. Its independent-
interval corollary has mismatched printed indices and omits the first
interval; corrected active intervals retain all completed gaps. Infinite
previous arrivals require an absorbing gap and no age evaluation. These
III.23 applications and the hazard-rate/censored-data example are not claimed
by completion of III.21 and its two corollaries.

Verification: 9938 incremental jobs, 6 affected / 6 rebuilt clean traces,
9 standard-axiom-only checks, no full build or push.

## Native CDF/Stieltjes hazard, continuous logarithm and law applications

REUSE: native probability CDF and `measure_cdf`, Stieltjes interval/singleton
masses, true map/restriction integrals, the existing pathwise substitution
owner, reciprocal/logarithm calculus, norm-tail UI criteria, actual RN
derivatives and the native absolutely-continuous interval-primitive predicate.
The pinned native exponential measure and CDF remain the distribution owners.

BUILD: exact finite-lifetime CDF and ENNReal hazard integration bridges;
measure-preserving UI pullback and its original-lifetime consumer; actual
diffuse CDF continuity and its converse; two-sided hazard continuity; and
positive-survival Stieltjes logarithm identities on both time domains.
The NNReal Stieltjes measure maps to the real measure restricted to positive
times, not to its initial atom or negative halfline. Actual extended hazard
finiteness and L1 are established before its real logarithmic identification.
The original-space log compensator reuses the same already constructed source
domain and sole compensator. No density is imposed on a diffuse law.

BUILD: actual weighted-measure/RN absolute-continuity consumers retaining
infinite lifetimes; and rate-correct exponential hazard from the actual
pushforward law. CDF-function AC and final original-space exponential
compensation are not inferred from these intermediate results.
No new CDF, hazard, compensator, integral or path-regularity owner is introduced.

Verification: 9933 incremental jobs, 14 affected / 14 rebuilt clean traces,
24 standard-axiom-only checks, no full build or push.

## Unrestricted hazard compensation and exact measure-preserving pullback

REUSE: the existing extended hazard, actual unrestricted martingale and
common-event path results, predictable stopping, sole canonical compensator,
native deterministic localization and genuine usual augmentation. REUSE:
native comap/iSup identities, measure-preserving L1 transport and event-integral
conditional-expectation uniqueness. No second filtration, hazard, terminal
envelope selector or compensator owner is introduced.

BUILD: native martingale pullback for exact comap filtrations, including the
actual Nat-valued natural filtration equality; unrestricted canonical
compensator identification without a survival guard; whole-half-line UI from
an actual integrable extended-hazard supremum; and the original probability-
space consumers using the actual pushforward law of a measurable lifetime.
No injective map or assumed domain certificate is needed. The proofs retain
zero/infinite lifetimes and establish extended finiteness before real conversion.
CDF/logarithm, absolute-continuity, exponential and III.23 consumers are not
inferred from the general integral formula.

Verification: 9920 incremental jobs, 5 affected / 5 rebuilt clean traces and
8 standard-axiom-only checks. No new external dependency, full build or push.

## Genuine filtration shrinkage and actual hazard-domain consumers

REUSE: the actual symmetric inverse and geometric probability models,
reflection invariance, native conditional-expectation uniqueness, centered
single-jump UI, the existing magnitude/initial-value localizer, genuine usual
augmentation, before-field moment and increment obstructions, actual raw
bracket invariance, predictable FV localization and sole angle/compensator
uniqueness. The pinned Mathlib/local/approved-source scan found no matching
completed concrete filtration-shrinkage consumers or unrestricted hazard
expectation theorem. Native infimum-approximating sequences and countable
null unions supply the closed-tail positivity lemma.

BUILD: the actual second printed-page-128 example, including both usual
filtrations, all cutoff moments and the native non-local-martingale proof.
BUILD: actual loss of the angular domain under a smaller filtration while
the same semimartingale and raw bracket remain. BUILD: actual finite-capped
count domain and identification of the canonical hazard compensator.
BUILD: closed-tail positivity almost everywhere and unrestricted actual
stopped-hazard expectation/L1 identities, with AE extended finiteness proved
before real conversion. BUILD: unrestricted true martingality from the
actual event decomposition and common-event finiteness/monotone/cadlag paths
from the same positive-closed-survival event. Initial and infinite atoms
remain allowed. No global UI is inferred from a mere L1 bound.

Verification: 9916 incremental jobs, 9 affected / 9 rebuilt
clean traces and 25 standard-axiom-only checks. No external dependency,
new selector, hidden moment assumption or totalized infinite real integral.
General uncapped compensation and conditional-history III.23 remain open.
No full build or push.

## Native moment counterexample and predictable hazard consumers

REUSE: original geometric measure/moment results, native before-field
localization obstruction, centered single-jump UI, original path variation,
reflection invariance of Lebesgue measure, actual restriction and finite
scalar integration, the sharp power-integrability criterion, the exact
predictable stopping-map owner and the completed conditional-expectation bridge.
The pinned Mathlib/local/approved-source audit found no matching concrete
geometric UI-but-not-locally-L2 process, reciprocal-uniform non-L1 model,
native local-IV increment obstruction or complete capped hazard UI consumer.

BUILD: the actual first printed-page-128 process counterexample, the second
example's symmetric atomless non-L1 random variable, and the native local-IV
increment obstruction. BUILD: true/UI martingality of the original capped
compensated count and predictability of its actual stopped hazard.
BUILD: UI transport through genuine completion for arbitrary exponents and
measures, plus true/UI/local martingale usual-augmentation bridges on an
already right-continuous raw probability filtration. No new process hierarchy,
compensator selector, external package, initial moment or unmasked substitute
for native localization is introduced.

Verification: 9908 incremental jobs, 7 affected / 7 rebuilt
clean traces and 24 standard-axiom-only checks. The finite-horizon hazard
guard is explicit; full general compensation and the second process
counterexample are not inferred from these prerequisites. No full build or push.

## Actual hazard balance, completed information and negative angular tests

REUSE: native restricted stopping times and actual stoppedProcess, original
natural information/event decomposition, Doob--Dynkin, CE uniqueness, measure
completion/trim, countable AE representatives, Tonelli and dominated convergence,
native local positive-lifetime masks, pinned geometricMeasure and its weighted
integral/summability API, finite-space integration, centered single-jump UI,
actual raw bracket invariance and sole predictable-compensator uniqueness.
The pinned/current-tree audit found no matching complete hazard or completed
single-jump CE consumer, native zero-one-before-field moment obstruction,
or actual finite-model angular environment counterexample.

BUILD: exact raw and usual single-jump CE, right-continuous completion bridges,
one extended hazard owner with finite-domain real consequences and true
survival increment balance. BUILD: a native-localization moment obstruction
and a concrete geometric finite-first/infinite-second moment model.
BUILD: actual equivalent-law and larger-filtration angular counterexamples,
including probability/usuality/UI/L2 checks and constructed angular domains.
No external package, proposed compensator input, hidden initial moment,
finite-lifetime coercion at infinity or totalized infinite real hazard is used.

Verification: 9902 incremental jobs, 13 affected / 13 rebuilt
clean traces and 49 standard-axiom-only checks. Complete III.21/III.23
compensation, loss-of-angular-domain examples and printed-page-128 process
counterexamples remain separate work. No full build or push.

## Actual natural information and bracket environment boundaries

REUSE: native natural filtrations, existing restricted stopping times and
comap measurable events, exact trivial-field measurable-set classification,
the actual constant-integrator and raw-constant identities, actual
right-value compensation, stochastic-integral environment invariance,
raw polarization and the one-continuous-source actual-angle domain.
No duplicate raw environment wrapper or exact closed-count information
consumer was found in the pinned baseline or existing project.

BUILD: the censored-lifetime natural-information theorem and full event
decomposition, with an actual two-point nonmeasurability regression against
the incorrect raw capped-lifetime field. BUILD: actual increment-kernel
and initial-product regression tests for corrected III.19/III.20.
BUILD: raw QV/QCov environment invariance and genuine one-continuous-source
mixed-angle invariance with constructed domains. The latter does not replace
full compensator uniqueness by conclusion-shaped compatibility assumptions.
General discontinuous angles can depend on the environment; no contrary
claim or theorem is introduced.

Verification: 9890 incremental jobs, 6 affected / 6 rebuilt
clean traces and 12 standard-axiom-only checks. No external code or
package, full build or push. CE/hazard consumers and finite-model negative
angle tests remain pending.

## Corrected signed and right-value compensator formulas

REUSE: actual AE-source signed compensation, integral invariance, original
Stieltjes integrals and countable-support atom integration, finite large
cadlag jumps, compact pair bounds, native running-supremum criteria, actual
canonical compensation, general local Yoeurp and predictable integral
versions. Searches found no existing completed right-value compensator
consumer or cadlag-integrand Stieltjes correction at this generality.
No external implementation or package was added.

BUILD: the full AE-source III.19 consumer of the original actual integrals,
with a constructed source-kernel version, centered source L1 and canonical
compensator integral L1. The absolute condition controls increments only;
it does not grant an initial-product moment. BUILD: cadlag right/left
variation-measure integrability and the absolutely summable jump correction.
The original integrand need not have finite variation.

BUILD: FV native local martingales and FV special semimartingales have actual
local IV; the latter is equivalent to specialness on the adapted cadlag FV
domain. BUILD: corrected III.20 on the predictable-integrator domain,
extended to general native local martingales. The right-value expression
has a proved path-integral meaning and an actual compensator domain; full
uniqueness identifies its canonical compensator with the actual left
integral. No new right-integral selector or conclusion-shaped premise is
used. The different native-path and process left-limit conventions at zero
are explicitly reconciled, retaining the raw initial product.

Verification: 9884 incremental jobs, 5 affected / 5 rebuilt
clean traces and 10 standard-axiom-only checks. No full build or push.
Hazard and other package dependencies remain open.

## Guarded arrival counts and predictable integral versions

REUSE: native hittingAfter and measurable upper-ray criteria, original
Poisson guarded counts, initial complete subspaces and restricted stopping
times, common-event UCP subsequences, Mathlib measurable limUnder on the
predictable sigma field, original simple coefficient/stopped-process APIs,
actual stochastic-integral convergence and FV agreement, signed kernel
duality and actual canonical compensation. Targeted pinned-Mathlib and
project searches found no existing general extended arrival owner, UCP
predictable-version theorem or completed actual signed integral consumer.
No external Lean source or package was adopted.

BUILD: the guarded extended arrival predicate and count, exact native
arrival recovery, adaptedness equivalence and common-AE arrival versions.
Infinity is not evaluated as a finite time; bad raw arrival paths are never
silently assigned a count. The existing all-finite count is proved coherent.

BUILD: whole-fiber variation-kernel congruence, actual everywhere-monotone
cadlag versions and AE-source signed compensation. BUILD: predictable
versions of UCP limits and actual integrals, actual locally-IV predictable
FV integration and normalized canonical compensation. The simple proof
uses the original F_tau coefficient only strictly after tau and does not
assume it measurable strictly before tau. The actual initial product remains.

BUILD: finite-time Chapter II signed tests on the everywhere-good increasing
source domain. The actual integrand is only adapted and AE-caglad; a true
predictable version and finite-window cutoff are derived. Bochner L1 is
proved from the absolute Stieltjes condition before taking expectations.
This controls centered increments, not unchecked initial products.

Verification: 9880 incremental jobs, 12 affected / 12 rebuilt
clean traces, 38 standard-axiom-only checks. Full AE-source Chapter II
consumption, corrected III.20 and hazards are not claimed closed. No full
build or push.

## General local Yoeurp and finite-valued counting

REUSE: the actual predictable disjoint jump cover, before-field jump
measurability, UI terminal/weighted-jump budget theorem, FV raw-bracket
series and lifetime reindexing, predictable large-jump announcing
localizers, actual capped variation exit bounds, native stable-property
idempotence and local-martingale closure, raw masks/stopping, canonical
compensation, native hittingAfter, and Poisson raw bracket/moment owners.
The former positive-real-interarrival Poisson count is an all-finite
specialization, not an owner for possibly terminating arrival sequences.
No general nonexplosive counting predicate or deterministic-variation
localizer interface was found in pinned Mathlib or the existing project.

BUILD: whole-variation finite jump budgets, centered actual UI covariation
for an unbounded UI test, genuine predictable bounded-variation localizers,
general local Yoeurp, and its initial-product regression. No two random L1
envelopes are multiplied without proof. The centered bracket is UI; the
arbitrary raw initial product is only a native local martingale.

BUILD: the nonexplosive counting predicate and real path consequences,
actual canonical counting compensation, forward actual hitting-time arrival
representation/localizers, Poisson membership and a deterministic non-Poisson
single-jump regression with exact eventual-infinity arrivals. All time
quantifiers use common path events; finite hit membership is proved before
finite clock evaluation. Actual finite support precedes the count tsum.

Verification: 9868 incremental jobs, 11 affected / 11 rebuilt
clean traces and 32 standard-axiom-only checks, including predicate
constructor/projections. No full build or push. General reverse arrival
construction and III.21/III.23 hazard formulas are still separate work.

## Continuous compensation and actual-angle supplements

REUSE: actual canonical-compensator congruence/linearity/stopping, the
existing predictable version for AE-left-continuous adapted sources,
predictable FV local IV, actual raw bilinearity/one-sided stopping/jump
identities, continuous covariation and cross-sum UCP uniqueness.
Pinned Mathlib and local searches found no existing public generic
AE-continuous FV compensator bridge or common-event raw mixed mask owner.

BUILD: generic continuous FV local IV and centered actual compensation;
left/right mixed-angle bilinearity, source invariance and one-sided stopping;
actual mixed existence and continuous-owner equality with only one
continuous argument; raw mixed initial-event masking. REFACTOR: the existing
four continuous square-angle public declarations now consume the shared FV
bridge instead of retaining a second private predictable-version proof.

Every transformed raw domain is derived, not supplied as an algebra
conclusion. The continuous mixed result does not assume the other square
domain. Zero/infinite times, arbitrary real scalars and nonintegrable initial
values are retained; there is no exceptional-path predictability claim.
Verification: 9858 incremental jobs, 7 affected / 7 rebuilt
clean traces and 17 standard-axiom-only checks. No full build or push.

## Mixed predictable brackets, domain estimates and canonical algebra

REUSE: the sole canonical compensator, raw square/mixed bracket identities,
full predictable-FV uniqueness, actual Kunita--Watanabe variation bounds,
native unmasked variation localization, actual variation measurability,
general raw product compensation, predictable stopping, and Poisson canonical
parts/second moments. Pinned Mathlib and project searches found no competing
continuous-time mixed-angle owner or selected-compensator algebra.

BUILD: same-localizer real scaling; actual compensator addition/subtraction/
scaling and arbitrary stopping; mixed-angle properties/full uniqueness,
symmetry/diagonal agreement; genuine mixed local IV from the two square
domains; native locally-L2 existence; general product characterization;
actual sum-square domain and polarization; stopped-domain construction and
square/mixed stopping identities; actual Poisson angle identification and
positive-rate distinction from raw Q.

The mixed variation estimate controls the original measurable variation,
not an arbitrary proxy. Finiteness precedes real conversion. Native initial
values, zero/infinite lifetimes and the chosen filtration independence are
retained. No initial product moment, assumed sum-square domain, extra
predictable-time restriction, mixed monotonicity or second selector is used.

Verification: 9853 incremental jobs, 10 affected / 10 rebuilt clean
traces and 26 standard-axiom-only checks in
`Audit/SemimartingaleMixedAngleAxioms.lean`. No full build or push.

## Classical specialness criteria and the actual continuous-time angle

REUSE: actual canonical special parts, local compensator existence/full
uniqueness, predictable jump avoidance and coverage, localized UI jump
conditional expectations, native masks/localization, general III.33, raw
QV/covariation and their moments, stopping, initial values and UCP limits.
The existing unqualified predictable quadratic variation belongs to discrete
time; it is not a continuous-time compensator selector. No other external
library is imported or made an API owner.

BUILD: actual reverse running-jump/norm criteria on the classical domain;
native coordinate-L1 to local-IV for increasing processes; the domain-guarded
canonical compensator and coherence with canonical special parts; normalized
self-compensation, zero jumps at totally inaccessible times and continuity
for totally inaccessible source jumps; the actual angle as this same
compensator; general raw-bracket-compensated local-martingale products/squares;
angle square characterization; native locally-L2 and AE-continuous existence;
the continuous initial-square correction and actual constant regressions.

No given candidate compensator, initial moment, zero initial value, unmasked
replacement, second bracket selector or good-integrator converse substitutes
for these constructions. AE continuity gives a predictable version, not a
claim of predictability of arbitrary exceptional raw paths. Mixed angle
covariation and the remaining III.19--III.23 consumers are separate work.

Verification: 9844 incremental jobs, 13 affected / 13 rebuilt clean
traces and 31 standard-axiom-only checks in
`Audit/SemimartingaleAngleCriteriaAxioms.lean`. No full build or push.

## Predictable FV local IV and actual running-jump measurability

REUSE: actual first large jumps and finite attainment, predictable jump cover,
strict-before announcing localizers, bounded/random-jump FV local IV, native
local-property idempotence, original running norm and jump owners, canonical
special parts, actual compensation and full-path martingale envelopes.

BUILD: original integer-threshold jump localization; general predictable FV
local IV; exact actual running-jump stopping and rational-threshold
measurability including AE-cadlag originals; canonical FV local IV and genuine
compensation of locally-IV classical decompositions; whole-path native L1
envelopes and both running-supremum conclusions for special processes; FV
running-jump local-IV criterion and generic norm-to-jump local integrability.
The factor-two regression explicitly changes a cadlag path from one to minus
one. No dense jump grid, second supremum, unmasked initial-moment assumption,
unrestricted predictable infimum or good-integrator converse is substituted.

Verification: 9832 incremental jobs, 10 clean affected/rebuilt traces and
18 standard-axiom-only checks in `Audit/SemimartingalePredictableFVSupremumAxioms.lean`.
The long declaration was split by a namespace without changing its public
name; its incremental rebuild is clean. No full build or push.

## Signed predictable tests and actual running-supremum terminal integrability

REUSE: predictable nonnegative kernel duality, native composition-product
Fubini, actual variation kernels, monotone compensators, usual null-complete
predictable versions, actual variation exits, the existing masked running
supremum identity, predictable disjoint jump coverage, before-measurable
zero-terminal jump coefficients, announcing sequences and native tail infima.

BUILD: signed absolute-integrability transfer and actual compensator tests;
everywhere-good increasing compensator construction; bounded/unit-jump counting
compensators and random jump-envelope local IV; whole-path L1 and terminal L1
for stopped original running norm suprema; the actual all-times jump supremum
with initial jump and factor-two bound; attained countable predictable infima,
strict-before finite localizers and predictability of original first large jumps.
The former private masked norm-supremum bridge is promoted, not duplicated.
Only the actual jump supremum needs a new owner; no integral, compensator,
variation or localizer replacement is introduced. General signed tests require
finite expected absolute integral, not a finite totalized signed integral.

Verification: 9823 incremental jobs, 13 clean affected/rebuilt traces and
19 standard-axiom-only declarations in `Audit/SemimartingaleSignedSupremumAxioms.lean`.
No full build or push. Full AE-source canonical integral tests, corrected
III.20, predictable-FV local IV and the specialness criteria remain open.

## Actual canonical special parts and bounded-jump construction

REUSE: actual III.29, finite-variation jump localization, local predictable
compensation and jump bounds, positive-zero-jump continuity, predictable FV
uniqueness, arbitrary-initial constant local martingales, actual variation
envelopes, native dense running supremum, Poisson moments and its compensated
martingale for an explicit past-independent filtration.

BUILD: actual III.35 normalized predictable decomposition and its continuous
case; the sole proof-guarded canonical martingale/FV parts, complete properties,
uniqueness and version invariance; jump/continuity consumers for those same
parts and the nonintegrable-initial regression; integrable whole-path envelopes
for native localizations and actual masked stopping of the original running
supremum; Poisson canonical identification and genuine classical nonuniqueness.
No alternative integral, bracket, compensator or localization owner is added.
The canonical martingale includes the original initial random value, so neither
UI nor unmasked initial L1 is silently asserted. The counting example requires
the existing actual Poisson predicate and independence from the chosen past.

Verification: 9812 incremental jobs, 8 clean affected/rebuilt traces and
16 standard-axiom-only checks in `Audit/SemimartingaleCanonicalSpecialAxioms.lean`.
No full build or push. The general specialness criteria and predictable-FV
local-integrability step remain open; source p.132's missing factor two in
the running-jump bound is not used as printed.

## General local-martingale integration and special uniqueness

REUSE: actual total variation and its native left limits, capped norm exits,
overshoot bounds, variation integrability and measurability; bounded simple
source approximation, true-martingale simple integration, coordinate-UI
limit closure, actual initial-value and variation localizers, masked integral
identities, locally-L2 integration and III.29; predictable FV uniqueness and
actual Rao/local Doob decompositions.

BUILD: bounded-jump FV actual local IV; bounded-integrand global-IV UI
integration, its local-IV extension without initial moments, full III.33
assembly and an arbitrary-initial-value regression; the special predicate,
III.34 uniqueness and actual quasimartingale/supermartingale consumers.
The source integral, total variation and localization owners are unchanged.
No new canonical-part selector, external implementation or package is added.
Extended variation is proved finite before real conversion; the initial
integral product is retained. III.33 does not claim arbitrary predictable
integrands. Later special criteria and component selection remain open.

Verification: 9805 incremental jobs, 7 clean affected/rebuilt traces and
14 standard-axiom-only checks in `Audit/SemimartingaleSpecialIntegralAxioms.lean`.
No full build or push. Earlier general-integral-preservation gaps are superseded.

## Actual fundamental decomposition and classical semimartingales

REUSE: actual large-jump owners, genuine left limits and capped norm exits,
bounded optional sampling, measured actual extended variation, native stable
local-property idempotence, exact masked stopping, predictable compensation
and jump bounds, bounded-jump L2 localization and the good-integrator easy
direction. BUILD: joint-exit large-jump variation control, actual true/local
martingale large-jump local IV, local compensated jump bounds, actual III.29
decomposition with no initial moment, normalized decomposability and general
LM-to-SM. The classical source predicate is implemented by the same normalized
fields as decomposable without its L2 field; actual III.29, not a definition
change, proves their equivalence. Actual Rao and Doob give III.31--III.32.

No new jump enumeration, total-variation, localizer, compensator or stochastic
integral selector is introduced. The source good-integrator predicate is not
redefined by a classical decomposition. The reverse good-integrator direction,
III.33, special canonical criteria and source examples are not claimed here.
No external package or copied implementation was added.

Verification: 9799 incremental jobs, 10 clean affected/rebuilt traces and
24 standard-axiom-only checks in `Audit/SemimartingaleFundamentalLocalAxioms.lean`.
No full build or push; earlier fundamental LM-to-SM open statements are superseded.

## Increasing compensators and actual large-jump foundations

REUSE: actual Doob/compensator existence, predictable FV uniqueness, initial
centering and native localizers; compact cadlag large-jump finiteness, actual
variation, old lifetime enumeration/reindexing, usual versions/completeness;
ordinary stopping, masked initial-value localization, bounded local-martingale
closure, predictable jump conditional expectations and actual jump covers.
BUILD: increasing global/local compensators without initial local L1;
literal signed/norm large-jump sums with compact path/variation/jump proofs,
actual enumeration equality and original-process adaptedness; closed stopping
and arbitrary event restriction; actual square-integrable localization from
bounded positive jumps; global-IV/UI compensation with beta/2-beta jump bounds.

No second jump enumeration, variation owner, local-martingale predicate or
terminal selector is added. The sum definitions are the literal Ioc(0,t)
expressions. Finite-horizon summability is proved rather than silently
assuming full-half-line summability. The infinite lifetime indicator remains
outside arbitrary coefficient transforms. General local-IV large-jump
localization, the local jump-bound extension and full III.29/III.30 remain
open at this checkpoint. No external package or copied proof was added.

Verification: 9790 incremental jobs, 10 clean affected/rebuilt traces and
35 standard-axiom-only checks in
`Audit/SemimartingaleLargeJumpCompensatorAxioms.lean`. No full build or push.

## General compensator existence and predictable UI jump budgets

REUSE: native partitions and actual variation, conditional L1 contraction,
Rao existence/uniqueness, IV algebra, integrable-envelope local-martingale
closure, native localizers and stopping, predictable UCP patching, masked
local-martingale localization and the arbitrary-initial constant theorem.
BUILD: quantitative IV-to-quasimartingale; actual global-IV compensator with
UI remainder and initial-correct finite-time mean; actual stopped local
compensators and consistency under AE monotonicity; general local-IV
compensator construction/uniqueness without initial moment assumptions.
The arbitrary-initial regression calls actual existence and rejects a UI
remainder for nonintegrable initial data. No new compensator selector or
process hierarchy is introduced.

REUSE: actual UI terminal, finite/explicit-terminal predictable sampling,
conditional pull-out/contraction, genuine real summability and the centered
closed-step series theorem.
BUILD: the actual weighted predictable jump moment bound and UI sum from a
finite-partial coefficient budget, with no boundedness/L2/semimartingale
input. Terminal, jump integrability and summability are conclusions, not
certificates. Infinite lifetimes have explicit terminal zero. This does not
claim the general local Yoeurp extension or its still-missing actual
bounded-variation localizers. No external package or copied proof was added.

The incremental build passed 9781 jobs with 9 clean affected traces
and a clean rebuilt dependency closure. All 10 checks in
`Audit/SemimartingaleCompensatorExistenceAxioms.lean` use only standard Lean axioms,
including the local Doob source after its EOF-only formatting fix.
No full build or GitHub push. General compensator existence is closed;
increasing inheritance, applications and predictable angle bracket remain open.

## General local Doob--Meyer and Rao

REUSE: actual capped exits and bounded one-sided optional sampling, Class D
sampling/UI, the general III.11 theorem, predictable FV uniqueness, native
stopping identities, UCP completion/stopping/uniqueness, initial completeness,
strong-measurability limits, native local-property/masked bridges, nonnegative
Fatou and the existing monotone terminal owner.
BUILD: Class D of actual exit-stopped supermartingales without source Class D;
exact predictable stopping; actual predictable stopped-consistent patching;
ordinary-stopping and compensator mean bounds; the full local III.16
construction, normalized source form and uniqueness; actual terminal/global-IV
supplements under a signed mean lower bound or finite source mean limit.
The proof does not infer source-stopping UI or L1 convergence from locality.

REUSE: actual III.17 nonnegative cadlag coordinates and the new III.16 lower
mean-bound conclusion, original IV algebra and predictable FV uniqueness.
BUILD: actual Rao III.18 exact X = M + A, global/local integrable variation
and uniqueness against predictable FV competitors. Initial X(0) is retained
in the local martingale. Native-localizer variation algebra retains AE
monotonicity and does not impose extra integrability of initial values.
The negative-time regression invokes actual local existence, then uniqueness.
No new process representation, selector, external package or copied external
proof is introduced.

The incremental build passed 9774 jobs with 11 clean affected traces.
All 21 checks in `Audit/SemimartingalePredictableLocalAxioms.lean` use only
standard Lean axioms; rebuilt dependency traces are clean. No full build or
push. Earlier III.16/III.18 open statuses are superseded by this closure;
general local Yoeurp, compensators and later package gates remain open.

## General Class D Doob--Meyer and Protter III.17

REUSE: original Class D sampling, predictable test covers, single-jump removal,
native conditional expectation, actual lifetime series, norm-moment budgets,
IV terminal construction and the full regular continuous Doob theorem.
BUILD: finite preservation with fixed original jump coefficients, the actual
infinite predictable increasing correction, and integrable mean-zero sampled
jumps of its residual. Class D supplies the budget; actual uniform summability
and coordinatewise UI probability limits supply supermartingality. None of
these conclusions is a source-existence input. General III.11 then follows by
centering/restoring the arbitrary integrable initial value and adding the two
constructed increasing IV parts. The monotone-envelope IV proof is extracted
into its functional owner, preserving the old TI single-jump signature.
The regression calls actual existence and predictable FV uniqueness, and
explicitly proves that its unit predictable jump has nonzero mean and is not TI.

REUSE: actual whole-future envelopes and their dynamic order, canonical dyadic
right limits, and source-exact terminal-zero conditional variation.
BUILD: actual nonnegative supermartingale coordinates, their right-limit
supermartingale order without mean continuity, and a common-event difference
identity. The final exact positive-supermartingale difference characterization
closes III.17. It does not assert the local decomposition named Rao in III.18.
No second envelope, right-limit, UCP, variation or compensator owner, and no
external package or copied external proof, is introduced.

The incremental build passed 9764 jobs with 12 clean affected traces.
All 16 checks in `Audit/SemimartingalePredictableClassDAxioms.lean` use only
standard Lean axioms. All rebuilt dependency traces were checked for warnings
and errors. No full build or push. Local III.16 and Rao III.18 remain open.

## Predictable jump reduction prerequisites and dynamic future envelopes

REUSE: actual large-jump enumeration, accessible/TI classification and
predictable graph deduplication. BUILD: a positive disjoint predictable
sequence covering every fixed predictable jump test almost surely. The
quantifiers remain test-before-AE; no jump-amplitude event is presumed
before-measurable. Actual uniform series convergence and the finite jump
formula yield the infinite jump sum and isolated-coefficient identity.

REUSE: Class D actual predictable-jump L1, bounded-upper minimum sampling,
announcing/Levy limits and before-field conditional expectations. BUILD:
nonpositive conditional jump means at arbitrary positive predictable lifetimes,
with an independent infinite-lifetime branch. Actual clamped sample limits
and Class D uniform integrability prove raw predictable-jump removal preserves
supermartingality; the already proved centered single-jump martingale gives
conditional-mean removal. The nonnegative-step budget uses actual finite
corrected supermartingales as an explicit intermediate input. Their finite
terminal coefficient sums follow by dominated convergence; the full series
budget then follows from bounded nonnegative partial sums. This does not
pretend to establish finite-sum preservation or general III.11 by itself.

REUSE: native essential suprema, measurable restrictions, event-integral
conditional order and exact source partition extensions. BUILD: conditional
upper bounds for finite integrable directed essential suprema and actual
future-envelope supermartingale inequalities. Empty families are covered by
the explicit nonnegative bound; arbitrary envelope versions are transferred
by AE uniqueness, not falsely assumed measurable at the required filtration.
Cadlag envelope construction and Rao remain separate.

The incremental build passed 9754 jobs with 8 clean affected traces.
All 11 checks in `Audit/SemimartingalePredictableReductionAxioms.lean` use
only standard Lean axioms. No full build or push was performed.

## Full regular Class D construction and whole-future envelope balance

REUSE: actual capped exits, Class D sampling and UI limit closure, general
single-jump compensation, predictable FV jump cover, native conditional
expectation contraction, the bounded-jump regular construction and the unique
continuous Class D localization/terminal owner.
BUILD: the whole-exit-jump residual bound; integrable positive-jump envelopes;
actual predictable compensator jump identification; and common-event 2C/4C
jump estimates from the bounded residual. Actual sampled-jump integrability
is established before conditional centering or integral subtraction.
The full regular Class D theorem constructs its continuous increasing part
without source bounds or proposed witnesses. Signed single-jump compensation
is used only through its true UI martingale, not added to the increasing part.
Independent masked finite/announcing samples prove Class D zero-terminal
stopping-value and predictable-jump L1 even with infinite lifetime and without
finite-measure, adaptedness or usual-filtration assumptions.

REUSE: actual all-horizon directedness, essential-family integral bounds and
conditional-expectation towers. BUILD: the two actual whole-future envelopes,
finiteness/L1 under the original global variation bound, the finite signed
telescoping identity and the fixed-time real envelope difference equal to X.
Two translated essential upper bounds prove the balance; no false distribution
of supremum over subtraction is used. No supermartingale/cadlag envelope or
Rao decomposition is assumed or claimed.

The incremental build passed 9747 jobs with 10 clean affected traces.
All 16 checks in `Audit/SemimartingaleRegularFullClassDAxioms.lean` use only
standard Lean axioms. General III.11/III.16 existence remains open.
No full build or push was performed.

## Full continuous Class D Doob decomposition

REUSE: the bounded construction and continuous FV uniqueness, actual lifetime
steps and jump coefficients, Class D stopping families, native Lp Fatou,
the integer monotone L1 terminal owner, UCP completion/stopping/uniqueness,
and the existing coordinate-UI martingale limit theorem. No second terminal
selector, bracket, compensator process representation or external package
was added. The bounded-jump proof is refactored through the generic Class D
localization owner; its public signature is unchanged.

BUILD: full III.10 actual existence without bounded values or jump amplitudes,
unbounded integrable single-jump compensation, actual exceptional-time and
coefficient construction, whole-path localization recovery, independent UI
martingale closing after Fatou, and actual increasing-process terminal limits.
The random-amplitude regression invokes the full theorem with only F0
measurability, nonnegativity and integrability of its amplitude, then identifies
the genuinely constructed output by continuous FV uniqueness.

The 9646-job incremental build passed, with 14 clean affected final traces.
All 27 checks in `Audit/SemimartingaleContinuousClassDAxioms.lean` use only
`propext`, `Classical.choice` and `Quot.sound`. No full build or push was
performed. The source III.11 predictable conditional-mean-zero reduction is
not silently treated as TI-jump coverage; that broader step remains open.

## Existing internal-package reproducibility


The external `exchangeability` package and inherited `checkdecls` dependency have been removed
from both `lakefile.toml` and `lake-manifest.json`. The used reverse-martingale and de Finetti proof
closure now lives under `StochLean/Internal/Exchangeability` and compiles against the pinned
Mathlib v4.33.0 environment. The public reverse-martingale, conditional-IID, de Finetti, Bernoulli,
and exchangeability regression modules are built from those local sources, so the build no longer
depends on cached external oleans.

## One-way absolute-continuous density localization

REUSE: Mathlib's `hittingAfter`, the closure theorem for right-continuous
open-set hits, finite stopping-time truncation, the first Borel--Cantelli lemma
and ENNReal geometric summability; StochLean's canonical density process and
exact finite-stopping event-integral identity.

BUILD: `MeasureChange/AbsoluteContinuousDensityLocalization.lean` defines the
summable threshold `2⁻⁽ⁿ⁺¹⁾` and the first time `Z` enters its strict lower
interval. The exits are stopping times and increase pointwise. On an exit
before a deterministic horizon, right continuity and the stopped-density
identity give `Q(Rₙ ≤ T) ≤ 2⁻⁽ⁿ⁺¹⁾`; Borel--Cantelli yields `Rₙ → ∞`
`Q`-almost surely. Before each exit, positive-time `Z₋` is bounded below by
the threshold, so its reciprocal is nonnegative and locally bounded. No
reverse density, equivalence assumption, external package, or copied external
implementation is used. This establishes the localization prerequisite, not
the Girsanov conclusions of III.41--III.42.

The incremental build passed 10043 jobs. All 12 checks in
`Audit/SemimartingaleAbsoluteContinuousDensityLocalizationAxioms.lean` use only
standard Lean axioms. The production module passed isolated checking with zero
diagnostics. No full build or push.

## One-way absolute-continuous martingale transfer

REUSE: Mathlib conditional expectation, RN-derivative integrability, stopping
sigma-fields and local-property minima; StochLean finite stopping-time density
sampling, continuous optional sampling, UI closing variables, native masked
local martingales and the geometric lower-density exit sequence.

BUILD: `MeasureChange/AbsoluteContinuousMartingaleTransfer.lean` proves the
finite-stopping integrability equivalence and stopping-field Bayes formulas.
It transfers bounded stopped density-weighted UI martingales from `P` to `Q`,
then intersects a source localizer with density exits and deterministic caps
to obtain `Z * X` local under `P` implies `X` local under `Q`. The proof uses
only `Q ≪ P` in the valid AE direction, retains all time-zero masks, and asks
separately for target usualness in the local theorem. It introduces no reverse
density, external dependency or copied implementation. The incremental build
passed 10044 jobs; all 6 declarations in
`Audit/SemimartingaleAbsoluteContinuousMartingaleTransferAxioms.lean` use only
standard Lean axioms, and the production module passed isolated checking with
zero diagnostics. No full build or push.

## SP-03 final dependency and trust audit — 2026-09-17

The completed Semimartingale tranche keeps the repository's Mathlib-only
dependency boundary. `lakefile.toml` has one direct requirement, Mathlib at
`v4.33.0`; scans of all production and audit imports find only `Mathlib.*` and
`StochLean.*`. No external Brownian, exchangeability, stochastic-calculus, or
other Lean package is linked.

The final aggregate check is
`Audit/SemimartingaleCompletionAxioms.lean`. Its 18 load-bearing declarations
cover Yan/Bichteler--Dellacherie, one-way Lenglart--Girsanov,
Kazamaki--Novikov, stochastic-exponential uniqueness, Klenke bracket and
stopping interfaces, Protter I.52/I.56 cores, progressive strictness, Jacod and
Meyer--Feller cores, and the R36 counterexample. Every printed dependency set
contains only `propext`, `Classical.choice`, and `Quot.sound`.

A source scan found no `sorry`, project `axiom`, or tactic `admit`; matches for
the English word “admit” occur only in documentation comments. The deliberately
blocked and deferred source statements are represented in ledgers, not by
placeholder declarations or conclusion-shaped assumptions.

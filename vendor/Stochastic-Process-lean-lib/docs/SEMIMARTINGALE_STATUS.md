# Semimartingale implementation ledger

Normative contract: `D:/Math/StochLean_Semimartingale_Core_Design_v0.1.pdf`,
SP-03 SEMIMARTINGALE, 2026-09-07. This contract supersedes CM-QV.

Status: **IN PROGRESS**. No package-completion or publication claim is made by
this ledger. A declaration is implemented only after Lean compilation and its
stated semantic checks. The dependency baseline remains Mathlib v4.33.0 only.

## Implemented foundation (2026-09-07)

All files below have passed individual Lean elaboration. Incremental-build and
axiom audit results, with the historical full-build checkpoint, are recorded
under Verification below. This is **not**
an implementation-complete semimartingale package.

| Layer | Proved content | Canonical files under `StochLean/` |
| --- | --- | --- |
| Local martingales | Protter fundamental/reducing witnesses, masked localization, finite-time square integrability, UI-to-local bridge, exact masked/unmasked Klenke equivalence with integrable initial value | `Probability/Process/LocalMartingale.lean` |
| Initial values | Arbitrary finite F0-measurable random constants are continuous Protter local martingales; explicit 0/infinity localizer; nonintegrable squares/products and unbounded initial values obstruct the unguarded Klenke claims | `Probability/Process/LocalMartingale/InitialValue.lean`, `InitialValueCounterexample.lean` |
| Bounded localization | Masked localizations eventually agree at each finite time; a common-event globally bounded local martingale is a martingale (Klenke 21.68) | `Probability/Process/LocalMartingale/Bounded.lean` |
| Deterministic localization | Every cadlag martingale is a Protter local martingale; deterministic stopping closes it with `X_T` and gives actual unmasked UI localizers; continuous martingales are continuous local martingales | `Probability/Process/LocalMartingale/DeterministicStopping.lean` |
| Integrable domination | Protter I.51 in compact integrable-envelope form; a global integrable envelope gives a UI martingale. The previous constant-bound API is a corollary. | `Probability/Process/LocalMartingale/Bounded.lean`, `ForMathlib/MeasureTheory/Function/UniformIntegrableOperations.lean` |
| Path semantics | Common-event caglad paths, continuous-to-cadlag/caglad bridges, continuous operations and addition; generic dense running suprema reused by Brownian path functionals | `Probability/Process/Path/{Cadlag,Caglad,Algebra,Supremum}.lean` |
| Finite stopping | Everywhere-finite stopping-time witness, F_T, minimum/constant constructors, source-safe evaluation | `Probability/Process/Stopping/Finite.lean` |
| Continuous-time stopping | Capped upper-grid approximation, UI and L1 convergence; bounded martingale optional sampling, the minimum formula, and stopping for the original filtration; progressive/right-continuous and usual-filtration common-event versions | `Probability/Process/Stopping/Approximation.lean`, `Probability/Martingale/OptionalSampling/{ContinuousTime,ContinuousStopping,ContinuousUsual}.lean` |
| UI and closure | Actual integrable closing variable from the integer restriction; closed/UI equivalence; bounded and AE-finite stopping-value families are UI; arbitrary stopping preserves a UI martingale (Protter I.18) without any evaluation at infinity | `Probability/Martingale/Convergence/ContinuousClosure.lean`, `Probability/Martingale/OptionalSampling/ContinuousUniformIntegrable.lean` |
| Stopped paths and versions | Stopping preserves common-event continuous/cadlag/right-continuous paths and indistinguishability; relative completeness transports measurability after AE changes | `Probability/Process/Path/Stopping.lean`, `Probability/Process/Filtration/Usual.lean` |
| Local martingale stability | Actual common minimum fundamental sequence, arbitrary stopping and continuous-local stopping; addition, scalar multiplication, negation and subtraction, with the Protter masks retained | `Probability/Process/LocalMartingale/Stability.lean` |
| Unbounded sampling | UI optional sampling and the minimum formula at AE-finite terminal stopping times; AE ordering is sufficient; no deterministic bound is imposed | `Probability/Martingale/OptionalSampling/ContinuousUnbounded.lean` |
| Iterated localization and reducing times | Protter I.48(a--e), including AE-ordered reducing times, maxima, initial-event masks, and locally-local idempotence; I.50 and finite-time L2 I.49 on the cadlag domain. Adaptedness is derived from localizations and relative completeness; tail infima give genuinely pointwise-monotone witnesses. | `Probability/Process/LocalMartingale/{Localization,Reducing}.lean` |
| Continuous bounded localization | Closed-target hitting-time attainment; absolute-level stopping times, no overshoot and divergence of integer-level times; everywhere-continuous indistinguishable versions; bounded/centered unmasked UI and finite-time L2 localizations; refinement of true-martingale witnesses up to arbitrary random lifetimes, including AE-monotone source sequences | `Probability/Process/Stopping/{ContinuousHitting,BoundedLocalization,Usual}.lean`, `Measurability/ContinuousVersion.lean`, `LocalMartingale/{BoundedLocalization,LocalizationUpTo}.lean` |
| Continuous local L2 | Explicit bounded masked fundamental sequences for continuous local martingales with arbitrary finite initial values, with no initial L1 assumption; equivalence with locally square-integrable martingales on the common-event continuous path domain | `Probability/Process/LocalMartingale/ContinuousSquareLocalization.lean` |
| Stopping and integration L2 prerequisites | Lp contraction of bounded stopping values, finite-time square integrability preserved by arbitrary stopping, sampled martingales on ordered individually bounded stopping families, discrete predictable-integral isometry and energy bound; removal of arbitrary coefficients on empty stopping intervals preserves the source process and its integral | `Probability/Martingale/OptionalSampling/{ContinuousLp,ContinuousReindex}.lean`, `Process/Filtration/StoppingTimeReindex.lean`, `Martingale/DiscreteIntegral/L2.lean`, `Process/Semimartingale/SimplePredictable/Normalization.lean` |
| Partitions | Finite ordered endpoints, gaps/mesh, telescoping increments; locally finite infinite endpoint sets; lossless finite-horizon restriction; nested admissibility with corrected adjacent-gap mesh; deterministic embedding into random stopping-time partitions tending to the identity | `Analysis/PathVariation/{Basic,AdmissiblePartition}.lean`, `Probability/Process/Partition.lean`, `Partition/Klenke.lean` |
| Pure variation | p/QV/covariation sums and convergence predicates; polarization, Cauchy-Schwarz, zero-QV cross/perturbation; continuous bounded-variation paths have zero increment QV with vanishing mesh only | `Analysis/PathVariation/{Basic,FiniteVariation}.lean` |
| Variation exponents and total variation | Uniformly vanishing cell increments; finite/bounded lower-exponent sums imply zero higher-exponent variation; refinement monotonicity of one-variation; convergence to Mathlib total variation, including infinity, from continuity and vanishing mesh alone | `Analysis/PathVariation/{Oscillation,Approximation,Exponent,TotalVariation}.lean` |
| Completed-cell repair | Source two-square polarization; completed square sums are monotone; last partial-cell cross-sum error vanishes uniformly on a compact horizon; limiting covariation has bounded variation with the square-root bound (fixed enclosing horizon) | `Analysis/PathVariation/{Algebra,CompletedSums,PartialSums,CovariationVariation}.lean` |
| UCP | Compact ENNReal deviations, countable-supremum measurability on right-continuous paths, fixed-time probability convergence, one subsequence converging a.s. locally uniformly on one event | `Probability/Process/UCP.lean` |
| Brownian QV prerequisites | Exact squared-increment second/fourth moments; expected square sum T; variance `2 sum gap^2 <= 2 T mesh`; probability convergence for vanishing mesh; fixed-horizon a.s. convergence for summable mesh | `Probability/Brownian/QuadraticVariationMoments.lean` |
| Brownian fixed-horizon strong QV | Deterministic reflections preserve the full Brownian law; interval flips preserve every finer square sum and center cross increments conditionally on the entire future. Actual square sums form a reverse martingale of terminal-square conditional expectations. Levy downward convergence and the variance estimate give a.s. convergence for arbitrary nested vanishing mesh, including lossless infinite-partition restrictions; no extra coordinate measurability hypothesis remains in the final fixed-horizon theorem. | `Analysis/PathVariation/Reflection.lean`, `Probability/Conditional/Symmetry.lean`, `Probability/Brownian/{DeterministicReflection,ReflectionLaw,QuadraticVariationConditional,QuadraticVariationStrong}.lean` |
| Brownian martingales | Natural-filtration Brownian and square-minus-time martingales from independent increments; finite-time L2 and continuous-local-martingale bridges. Coordinate measurability is explicit. | `Probability/Brownian/Martingale.lean` |
| Brownian usual augmentation | Genuine completion preserves the actual Brownian laws and paths. Null-set enlargement and right continuation preserve future-past independence. True/square-minus-time martingales, CLM/semimartingale status and the canonical time bracket are proved, with a natural-filtration entry point. | `Probability/Brownian/UsualAugmentation.lean`, `Process/Filtration/IndependentIncrementsAugmentation.lean`, `Probability/Independence/Completion.lean` |
| Infinite-partition transport and all-times extraction | Clipped finite partitions preserve refinement and mesh; cell sums are invariant under repeated endpoint enumeration; exact stop/restrict square and cross identities; monotone completed-cell dense extraction and the limiting-covariation FV bound for the original infinite restrictions | `Analysis/PathVariation/{Stopping,EndpointInvariance,Restriction,DenseConvergence,RestrictionConvergence}.lean` |
| Brownian strong paths | One event, for each prescribed admissible sequence, supports QV equal to time for all times. Independent Brownian cross-QV is zero on one all-times event, via a proved normalized-sum Brownian law. Actual uniform/dyadic admissible partitions supply a concrete instance; Brownian total variation is infinite on every nondegenerate compact interval, on one event. | `Analysis/PathVariation/UniformPartition.lean`, `Probability/Brownian/{QuadraticVariationPaths,IndependentCombination,CrossQuadraticVariation,InfiniteVariation}.lean` |
| Elementary integration | Genuine finite stopping-time intervals and left-endpoint-measurable finite coefficients, pathwise representation independence for every integrator, proof-indexed integral, time-zero convention, linearity in the integrator | `Analysis/PathVariation/StepIntegral.lean`, `Probability/Process/Semimartingale/{SimplePredictable,Stability}.lean` |
| Semimartingale foundation | Good-integrator sequential/epsilon-delta equivalence; total/ordinary predicates; adaptedness and common-event cadlag paths; arbitrary measurable random constants; addition and scalar multiplication | `Probability/Process/Semimartingale/{Basic,Stability}.lean` |
| Source elementary L2 estimate | Original stopping-endpoint sigma-fields, individually unbounded finite sampling, exact reduction to the discrete integral including its initial term, initial/future orthogonality, and `E[(H dot X^T)^2] <= C^2 E[X_T^2]` from a global process bound. Empty intervals are normalized, not excluded. | `Probability/Martingale/OptionalSampling/ContinuousTerminalLp.lean`, `Process/Partition/Sampling.lean`, `Martingale/DiscreteIntegral/InitialL2.lean`, `Moments/L2.lean`, `Process/Semimartingale/SimplePredictable/{Sampling,L2}.lean` |
| Actual martingale semimartingale examples | Protter II.8 and Corollaries 1--2: finite-time L2 martingales, locally L2 cadlag martingales, and continuous local martingales are ordinary source semimartingales. The last statement does not assume unmasked initial integrability. | `Probability/Process/Semimartingale/{L2Martingale,LocalL2Martingale}.lean` |
| Source localization | Indistinguishable integrators give AE equal elementary integrals; agreement off small-probability sets preserves good integrators. Strict-before-lifetime agreement yields ordinary semimartingale patching for measurable, not necessarily stopping, lifetimes. Masked pre-localization and locally-semimartingale forms are proved on the adapted cadlag domain. | `Probability/Process/Stopping/LocalizingTail.lean`, `Process/Semimartingale/Localization.lean` |
| Finite variation | Common-event local/global BV predicates reuse Mathlib variation. Source elementary integrals are measurable and have the pathwise initial-plus-variation bound. Adapted cadlag local FV processes are ordinary semimartingales; global FV gives total semimartingales. No integrability of random variation is required. | `Probability/Process/Path/FiniteVariation.lean`, `Process/Semimartingale/SimplePredictable/{Measurability,VariationBound}.lean`, `Process/Semimartingale/FiniteVariation.lean` |
| Random Stieltjes foundation | Right-continuous one-variation sums converge to extended total variation, including infinity. Canonical adapted total/positive/negative variation processes, cadlag increasing components, locally finite random increment measures and their F_T-measurable restrictions are constructed. Pathwise integration includes the initial term, linearity, variation bounds, dominated convergence, measurability and progressive-integrand adaptedness. | `Analysis/PathVariation/{Stieltjes,StieltjesIntegral,TotalVariation}.lean`, `ForMathlib/{MeasurableStieltjesNNReal,MeasurableIntegralFiniteFibers}.lean`, `Process/FiniteVariation/{Variation,Jordan,Stieltjes,Integral}.lean`, `Measurability/CadlagVersion.lean` |
| Measure stability | Protter II.2--II.3: absolutely continuous finite-target-measure changes and finite-mass countable mixtures preserve the total/ordinary predicates. No bounded density, equivalent measure or uniform componentwise convergence rate is assumed. | `ForMathlib/MeasureTheory/Function/ConvergenceInMeasure{AbsoluteContinuity,Mixture}.lean`, `Probability/Process/Semimartingale/{AbsoluteContinuity,Mixture}.lean` |
| Filtration shrinkage | Protter II.4 (Stricker), with explicit adaptedness to the smaller filtration; source stopping partitions, coefficient sigma-fields and elementary integrals are transported without change. | `Probability/Process/Stopping/Filtration.lean`, `Process/Semimartingale/Stricker.lean` |
| Further examples | The existing Poisson predicate yields real monotone cadlag finite-variation paths and hence a semimartingale under a chosen usual adapted filtration. The source decomposable predicate has a proved easy implication to semimartingales, without predictability or a converse. | `Probability/Process/Poisson/Semimartingale.lean`, `Process/Semimartingale/Decomposable.lean` |
| FV integral regularity | Local pathwise integrability yields cadlag and locally BV integral paths, and progressive integrands give semimartingales under usual conditions. Closed-endpoint primitive right limits, open-endpoint left limits and atom jump formulas are proved without atomlessness. | `ForMathlib/{StieltjesPrimitiveRegularity,VariationAlgebra}.lean`, `Analysis/PathVariation/StieltjesIntegralRegularity.lean`, `Process/FiniteVariation/IntegralRegularity.lean` |
| Left limits and `T-` | Source initial-left value zero, jump process, caglad left-limit paths and adaptedness under usual conditions; zero/infinite-lifetime stopping semantics; exact `T-` patching with equality or indistinguishability. Small-set patching now allows common-event AE agreement. | `ForMathlib/Topology/Order/LeftLimitRight.lean`, `Probability/Process/Path/LeftLimit.lean`, `Measurability/LeftLimit.lean`, `Stopping/Before.lean`, `Semimartingale/{Localization,StoppingBefore}.lean` |
| Predictable source ownership | Strict-past deterministic grids give predictability of everywhere-left-continuous adapted real processes. The source caglad-generated sigma-field equals Mathlib's predictable owner. AE left-continuity gives an actual indistinguishable predictable version. | `Probability/Process/Measurability/{PredictableGrid,Predictable,PredictableGenerators}.lean`, `Path/Step.lean` |
| Source simple-process regularity | Original stopping coefficient sigma-fields give adaptedness; finite step paths give everywhere-caglad regularity, hence canonical predictability. No bounded coefficients or distinct endpoints are assumed. | `Probability/Process/Stopping/Coefficient.lean`, `Process/Semimartingale/SimplePredictable/Regularity.lean` |
| Source simple-process algebra | Actual common finite stopping-time refinements; coefficient measurability at new left endpoints; process/integral invariance; zero-preserving binary Borel operations; addition, product, scalar, negation and subtraction closure; elementary bilinearity. Initial coefficients and repeated endpoints are retained. | `Probability/Process/Partition/Refinement.lean`, `Stopping/CoefficientAtStopping.lean`, `Semimartingale/SimplePredictable/{Refinement,Algebra,IntegratorAlgebra}.lean` |
| Source stopping | Closed cutoff preserves the full simple class, including infinite stopping times; elementary stopping holds for arbitrary integrators. Good integrators are stable under stopping; total/ordinary semimartingales inherit stopping under usual conditions. Total implies ordinary without usual conditions; bounded stopping of an ordinary semimartingale is total. | `Probability/Process/Semimartingale/{SimplePredictable/Stopping,Stopping}.lean` |
| Source linear operator and continuity | Exact source submodule and elementary linear map; negation/subtraction; uniform epsilon/delta difference control, uniform-Cauchy to Cauchy-in-measure estimates and convergence in measure at every simple limit. No UCP extension is claimed. | `Probability/Process/Semimartingale/{SimplePredictable/LinearMap,Continuity}.lean` |
| Right-continuous first exits | Countable open-target detection, stopping under right-continuous filtrations and the common-event usual version; finite-hit closure membership/closed-target attainment; pre-hit upper and at-hit lower norm bounds. Jumps may overshoot. | `Probability/Process/Stopping/{RightContinuousHitting,FirstExit}.lean` |
| Source elementary integral process | Canonical `J_X(H)` from the existing elementary integral at deterministic stops; representation independence, initial/terminal values, source linearity, cadlag paths, usual-filtration adaptedness, arbitrary raw-time stopping, legal cutoff and FV agreement. No coefficient bounds or integrability are assumed. | `Probability/Process/Semimartingale/SimplePredictable/IntegralProcess*.lean`, `Process/FiniteVariation/SimpleAgreement.lean` |
| Elementary maximal/UCP step | Actual finite first-exit reduction and source cutoff give maximal estimates for total/ordinary semimartingales. Uniform convergence in time and sample to any simple limit implies UCP convergence of elementary integral processes. Strict real-threshold events are equivalent to the original extended-deviation UCP definition. | `Probability/Process/Stopping/FirstExitMaximal.lean`, `Process/UCP/DeviationEvents.lean`, `Process/Semimartingale/{Maximal,UniformUCP}.lean` |
| Full source UCP continuity | Protter II.11: actual uniformly bounded left-continuous first-exit truncations with initial masks give S_UCP-to-D_UCP continuity at every simple limit and UCP-Cauchy estimates. Countable left-hit detection includes the initial point. | `Probability/Process/Stopping/LeftContinuousHitting.lean`, `Process/Semimartingale/SimplePredictable/{InitialMask,FirstExitTruncation}.lean`, `Process/Semimartingale/UCP.lean` |
| Right limits and oscillation nonaccumulation | Caglad inputs give cadlag adapted right-limit processes, with positive-time reconstruction and independent initial values. Uniformly separated ordered cadlag samples cannot accumulate finitely, including extended times that may reach infinity. | `ForMathlib/Topology/Order/RightLimitLeft.lean`, `Probability/Process/Path/{RightLimit,Oscillation}.lean`, `Process/Measurability/RightLimit.lean` |
| Corrected source density | Protter II.10: actual recursive oscillation stopping times, finite capped partitions including the first cell, original initial values and finite left-endpoint coefficients give source simple UCP approximants of every adapted/common-event-caglad process under usual conditions and a finite measure. No coefficient bound is imposed. | `Probability/Process/Stopping/Oscillation.lean`, `Process/Partition/TruncateSequence.lean`, `Process/Semimartingale/SimplePredictable/{OscillationApproximation,Density}.lean` |

Sequential adapted-cadlag UCP completeness is proved in `Process/UCP/{Cauchy,Complete}.lean`.
The source Chapter II stochastic integral is constructed in
`Semimartingale/StochasticIntegral.lean` and its construction/algebra/continuity/
initial-value modules. It has arbitrary-simple-approximation convergence, adapted
everywhere-cadlag output, indistinguishability uniqueness, proof irrelevance,
linearity, integrand invariance, full UCP continuity and initial value `H_0 X_0` AE.
This closes construction, not the remaining general-integral property ledger below.
The general integral also has proved addition, real scaling and subtraction in
the semimartingale integrator, by common source approximants. This fixed-integrator
algebra does not assert continuity for arbitrary varying semimartingale integrators.

Protter II.19 is proved: the constructed integral is a semimartingale, and
iteration on the adapted-caglad domain agrees with integration of the product
integrand, including the unnormalized initial product. Exact source cell sums
give elementary associativity; fixed-simple integrands are continuous in a
UCP-varying integrator. Multiplication by a fixed caglad process is UCP-continuous
using only compact path bounds. Simple-outer associativity then proves the
good-integrator condition before the outer general integral is selected.
The FV remark is proved on individual finite-variation paths up to one null set.
No initial L1/L2 assumption, global coefficient bound or decomposition is used.

The bounded-integrand part of II.20 is proved. Bounded source simple processes
preserve martingales even with arbitrary finite stopping endpoints and unbounded
unused coefficients. Bounded adapted-caglad integrands preserve finite-time L2
martingales, with the sharp horizon L2 estimate and retained initial value.
Clipped source density, the square-envelope UI criterion and actual martingale
limit closure supply the proof. The general locally-L2 case of II.20 is now proved
as well: the minimum of the integrator's L2 localizers and the integrand's open
norm-exit localizers yields the integral's actual L2 localizations. Initial-event
masks and stopping commute with integration in both variables; the unmasked initial
value need not be integrable. General local-martingale preservation beyond locally-L2
is now proved by III.33, using actual III.29 and local-IV integration below.
Full II.21 is proved for adapted cadlag or caglad integrands and
actual random partitions with AE vanishing mesh and diverging terminal horizon.
Its increment-only sums converge to the integral of the source left-limit process;
for caglad inputs this is the original integral minus its initial product.
Exact ordinary/strict upper projection of source endpoints and uniform stopped-path
convergence handle jumps. Sequential error control over every choice of partitions
gives the uniform approximation bound used in the double-limit argument. No false
uniform integrand approximation or initial-value integrability premise is used.

The canonical raw QV owner is now `X^2 - 2 (X_- . X)`. Adaptedness, cadlag paths,
the initial square, the common-event jump-square formula and indistinguishability
invariance are proved. The actual raw random-partition square sums converge in UCP.
Their upper-endpoint projections are completed-cell sums and hence genuinely
monotone; right continuity of the UCP limit yields increasing paths on one event.
Consequently QV has locally finite-variation paths and is itself a semimartingale.
The self-stopping identity holds for arbitrary, possibly infinite stopping times.
Mixed covariation and the mixed identities in II.22(iii) are now proved.
The unique polarized owner retains `X_0 Y_0`, has cadlag/FV paths and the jump
product, and is bilinear by the actual mixed-sum UCP limits. Finite-cell
telescoping gives integration by parts and the semimartingale algebra theorem.
The common-event Cauchy--Schwarz increment bound proves that mixed covariation
is constant where one square bracket is constant. This closes one-sided stopping
without assuming an incorrect finite-cell formula. The weighted II.24--II.25
measure theorem is now proved through actual total variation, quadratic measure
domination, RN density bounds and Holder's inequality. One event covers every
pair of measurable weights, without finite-energy or initial-integrability
assumptions. Increment-measure and explicit-initial-term interfaces are both
provided. The expectation/Lp corollary (printed p.70) is now proved: jointly
measurable weights give measurable random energies without an adaptedness or
moment assumption, and finite conjugate exponents and both L1/L-infinity
endpoints are covered. Initial atoms are retained; changing the null-event
Stieltjes version preserves the energies almost surely and their expectations.
Continuous-part stopping, II.30's weighted partition limit and II.29's brackets
of general Chapter II integrals are proved below.

The deterministic foundation for the continuous part is now proved. Positive-
mass singletons form a countable intrinsic set; restriction gives point-atomic
and point-diffuse measures. Every submeasure of an increasing half-line Stieltjes
measure has a genuine zero-starting Stieltjes realization. The point-diffuse
realization is continuous, while the jump realization is the summable series
of all jumps in `(0,t]`. Their sum is the original increment, with the original
initial value separate. For continuous paths the jump part vanishes. The raw
square bracket's continuous component is now adapted, everywhere continuous
and increasing, zero-starting and an FV semimartingale. Joint singleton-mass
measurability and compatibility of diffuse restriction with finite time
restriction prove nonanticipation. Its all-times decomposition uses the actual
squared jumps of the original process and proves their finite-horizon
summability. Indistinguishable processes give indistinguishable continuous
brackets; for continuous processes the component is raw QV minus the initial
square. Mixed continuous covariation is now polarized from these components:
adaptedness, continuous/FV paths, zero initial value, symmetry, the diagonal,
version invariance and bilinearity are proved. The raw mixed bracket equals its
initial product, continuous component and the absolutely summable series of
mixed jumps. Continuous square and mixed brackets now commute with simultaneous
and one-sided stopping, including zero and infinity. Stopped Stieltjes measures
are closed-endpoint restrictions; the exact jump cutoff retains the stopping
endpoint and the source jump at zero.

Protter II.30 is now proved for actual weighted mixed-increment sums on random
partitions tending to the identity. The cadlag adapted weight need not be bounded
or integrable. Exact finite-cell algebra, full II.21 convergence and associativity
identify the UCP limit as the integral of the source `H_-` against the existing raw
mixed bracket. Its initial value is zero, not `H_0 X_0 Y_0`. The moving partial
terminal cell and repeated endpoints are retained.

Protter II.29 is also proved. The simple case uses actual random-coefficient
mixed sums and one-sided stopped bracket limits. UCP continuity along integrals
of one fixed semimartingale follows from the product formula, left-limit
contraction, multiplication and associativity. Actual simple approximation
therefore gives the full adapted-caglad result. Symmetry and associativity give
the two-integral product-of-integrands formula; the same raw diagonal gives
the square-integrand formula. Neither integrability nor boundedness of the
initial variables or the integrands is assumed.

Protter II.27's main theorem is proved. A continuous local martingale has a
continuous raw square bracket, and its square minus that bracket is a continuous
local martingale. A nonnegative zero-starting Protter local martingale vanishes;
the proof uses actual masked true-martingale localizers, not an unjustified
unmasked integrability assumption. Constant raw mixed brackets and polarization
give exact centering: the centered process has raw QV `[X,X] - X_0^2`.
Thus `[X,X] = X_0^2` if and only if `X = X_0`, up to indistinguishability.
II.26's continuous-FV special case and II.27 Corollaries 1--2 are also proved.
Pathwise Stieltjes agreement proves constant raw QV on continuous FV paths,
without requiring that the FV event have full measure. Continuous FV local
martingales are constant. For each pair of AE-ordered stopping times, the raw
bracket of `X^T - X^S` is `[X,X]^T - [X,X]^S`. Open-interval finite variation
or closed-interval bracket constancy gives process constancy on the finite
points of that interval; zero and infinite endpoints are covered. The product
of two locally-L2 martingales minus their raw bracket is local, and adapted
cadlag FV candidates with the same residual, jumps and initial product agree
up to indistinguishability. II.27 Corollary 5's main assertion is now proved
on one event for every interval, not just each separately selected stopping
interval. The interface covers all order-connected sets, including open,
half-open and unbounded intervals. Equality of raw or continuous bracket
endpoints detects constancy on the full closed interval; arbitrary random
endpoints need no measurability or stopping assumption. Actual departure
times, a countable dense set and continuity supply the common event using
the existing stopped-bracket equivalence. Corollaries 3--4 (moments/terminal
values) remain open. The following discontinuous compensated-Poisson example
is now also proved.
For that example the actual compensated process `N_t-rate*t` now has a proved
true-martingale and local-martingale property under explicit adaptedness and
future-increment independence from the chosen past. The Poisson series proves
the exact first moment, including zero rate, and real-increment transfer retains
negative means when time order is reversed. Cadlag/FV paths and the ordinary
semimartingale property are also proved. Exact second moments yield an L1
mesh-error bound for square-increment sums. Probability-limit uniqueness with
the raw-bracket UCP theorem identifies `[N,N]=[N-rate*t,N-rate*t]=N` on one event.
At unit rate the compensated path has no nondegenerate constancy interval;
the bracket has a nontrivial flat right interval at every time on one event.
The actual compensated process is formally not a continuous local martingale.
This closes the source counterexample, not the remaining moment corollaries.

Protter II.26 is now proved for general cadlag finite-variation paths. Actual
endpoint steps, strict-left/right pointwise limits and variation-measure
dominated convergence give the self-integral identity with jumps. The Jordan
components prove countable jump support, absolute and squared-jump summability,
and convert the jump integral into its genuine singleton-mass series. Raw QV
is therefore the initial square plus the sum of squared jumps over `(0,t]`;
its existing continuous part vanishes. This holds path-locally without assuming
that the FV event has full measure. Quadratic pure jump is a property of that
same component, with version invariance, arbitrary stopping and the continuous-
path raw normalization. Continuous FV drift is a valid quadratic-pure-jump
example.

Protter II.28 is proved. Positivity of the continuous square bracket for
all integer linear combinations, on one countable-intersection event, forces
the mixed continuous component to vanish when one diagonal vanishes.
Consequently the raw mixed bracket with a quadratic-pure-jump argument is
the initial product plus its actual absolutely summable mixed-jump series.
Both argument orders and FV cases are covered. If the other argument is
continuous, or one argument is continuous FV, only the initial product
remains. Quadratic pure jump is stable under real linear operations.

Protter II.31 is proved on the right-continuous FV domain. The actual
two-endpoint step integrals telescope; joint continuity of the derivative-
filled slope and compact bounds allow variation-measure dominated convergence.
The slope minus the left derivative is supported on the jumps, and its
Stieltjes integral is the absolutely summable jump-remainder series. C1
composition preserves local FV. Right-continuous BV gives the required finite
left limits rather than assuming them. Process and path-local Chapter II
formulas are proved on common events, with the exact initial `f'(0) X_0`
term subtracted. This does not close the general semimartingale Ito formula.

The continuous case of Protter II.32 and its C2 preservation corollary are
proved. A second-derivative-filled Taylor quotient is jointly continuous,
including on the diagonal. Exact finite sums retain the partial terminal
cell. The existing raw square-sum UCP limit supplies eventual pathwise
bounds, and two nested subsequences identify the Taylor error limit with
zero on one event for all times. The weighted square limit uses the original
raw bracket; both derivative integrands are source left limits, hence zero
initially. Neither initial moments nor global derivative bounds are required.
The general raw-bracket formula, equivalent continuous-component formula
and C2 preservation are now proved below, followed by the multidimensional extension.

Protter II.32's general cadlag raw-bracket identity is proved. Compact
one-sided neighborhoods give finitely many separating times and a common
small-oscillation scale. Fine partitions eventually separate any prescribed
finite selection, and exact selected-cell sums converge to the two-sided
jump values. The unselected remainder is bounded by a small coefficient
times the actual square sum. The finite selection also controls the tail
of the genuinely summable target series. Clipping handles varying partition
horizons and partial cells. Nested UCP subsequences identify the stochastic
Taylor error on one common event for every finite time. Both first- and
second-order jump-correction series are absolutely summable and locally FV.
The raw identity identifies an adapted cadlag residual with the FV series,
proving general C2 semimartingale preservation without assuming nonlinear
closure. Initial moments, global derivative bounds and expected variation
are not required.

The equivalent continuous-bracket formula is now proved. The original
Stieltjes measure is split into its intrinsic point-atomic and point-diffuse
restrictions. Genuine integrability gives the integral split; compact caglad
bounds give absolute summability of the weighted jumps. The canonical raw
and continuous quadratic variations use the same Stieltjes realization,
and the existing integral's indistinguishability invariance transfers this
identity to processes. The initial square remains separate; the derivative
left-limit integrands vanish at zero. Absolutely convergent series algebra
then converts the raw second-order correction to the source first-order
correction. This closes II.32; the II.33 extension is recorded below.

The II.33 foundation now includes affine-line Frechet derivatives and the
actual second-order Lagrange remainder on arbitrary real normed spaces.
The Hessian operator norm controls the error divided by the squared
increment norm. This coefficient is jointly continuous and zero on the
diagonal. Existing finite cadlag separators are generalized to metric
spaces, and compact diagonal bounds to proper normed path spaces.

Vector norm-square pair sums now converge to their actual jump series,
including varying partition horizons and partial terminal cells. Their
finite-product sup-norm energy is dominated by the existing coordinate
square sums; it is not asserted to be a stochastic bracket or equal to
their sum. The original endpoint-pair step interface is generalized in
place to metric path values. Exact Frechet Taylor sums retain the original
left derivative samples. Compact path/left-limit bounds prove absolute
summability of both Frechet jump corrections. Countable coordinate path
products and finite-coordinate square-jump summability transfer these
assertions to semimartingales on one event for all times.

Protter II.33 is now proved, including C2 semimartingale preservation.
Standard-basis evaluations expand the existing Frechet derivatives into
finite scalar coordinate sums, with all ordered Hessian pairs. One UCP
subsequence of the sum of coordinate raw-square approximations supplies
vector energy bounds; a nested error subsequence identifies the actual
jump correction on one common event for all finite times. The raw identity
identifies an adapted cadlag residual with a proved FV jump series and
therefore yields nonlinear preservation without assuming it. Polarization
of the square-bracket integral decomposition gives the mixed version,
including the initial product and absolutely summable weighted jumps.
Positive-time composition and finite/summable-series algebra give the
source continuous-bracket formula. No initial moments, global derivative
bounds or extra stochastic bracket owner are introduced. Regressions cover
the empty coordinate family, ordered off-diagonal terms and raw mixed
integral initial values. The Fisk--Stratonovich extension is recorded next;
the remaining II.7 applications and II.8 are still open.

Protter II.34 and its integration-by-parts corollary are now proved. The
source Fisk--Stratonovich integral takes a semimartingale integrand made
left continuous, with one half of continuous covariation added to the
existing Ito integral. It is a zero-starting semimartingale, has the same
jumps as that Ito integral, and its correction vanishes with either FV
argument, even for discontinuous FV paths. Continuous covariation of one
or two stochastic integrals is derived from the raw identity and actual
continuous/jump decomposition. The C2 Ito residual is FV, proving the
continuous-covariation chain rule. Applying it to the derivative of a C3
function proves II.34 with its actual jump correction. The continuous-path
formula and integration-by-parts corollary follow by vanishing jumps.
No Chapter V C2 extension of the Fisk--Stratonovich domain is claimed.

The II.35--II.36 foundation now includes the real coordinate gradient and
ordered Hessian of entire complex analytic functions. A single real linear
functional handles both real and imaginary components; the imaginary-
imaginary Hessian entry has the actual negative sign. Complex processes
and their source left limits are coordinate wrappers, with proved path
regularity and adaptedness under usual conditions. The complex
semimartingale predicate is exactly the conjunction of the two existing
real predicates, not a new good-integrator construction. Complex integrals
are assembled from real ones, preserve this predicate and retain the
complex initial product. Real linear functionals commute with
complex-integrand integration; complex scalar multiplication follows.
The real finite-coordinate C2 theorem proves analytic preservation.
Protter II.35--II.36 are now proved from these prerequisites. The complex
bilinear raw bracket is the difference of the real square brackets plus
twice i times their mixed bracket, with initial square `Z(0)^2`; it is not
the separate real nonnegative energy. Its continuous part is everywhere
continuous and zero initially. All four ordered Hessian entries are
combined under the real integral, and the actual analytic jump correction
is proved absolutely summable on a common event for all finite horizons.
The cadlag formula follows from the real vector theorem; continuous inputs
have zero positive-time jumps. The source raw-bracket continuous formula
uses a proved comparison requiring the integrand to vanish at zero.
The existing canonical real owners remain the only stochastic constructions.

The II.37 product foundation is implemented. Deviations of the actual factors
from one are absolutely summable by a C2 Taylor estimate and square-summable
jumps. Both source products converge, including zero and negative factors;
their equivalence uses the actual raw/continuous/jump bracket decomposition.
Zeros correspond exactly to positive-time jumps of size -1. The same
product-defined process has proved continuous-integrator semimartingale
preservation, strict positivity, continuity and its defining integral equation.
The arbitrary initial value is `exp(X(0))`, with the source unit initial value
requiring `X(0)=0`. No initial-moment premise is added. General cadlag
regularity of the product and full expression is now proved, as is the
positive-time identity `Delta E = E_- Delta X`. The product factor has
local finite variation and is exactly one plus its absolutely convergent
actual positive-time jump series. The proof expands the product into
absolutely summable finite-subset coefficients and groups their activation
times; zero/negative factors and repeated activation times are retained.
General adaptedness and semimartingale preservation are also proved. The
finite-horizon raw-bracket kernel supplies the squared-jump atoms; actual
real/complex atomic series, a zero-factor count and a principal complex-log
formula establish measurability without enumerating random jump times.
Capped progressive restrictions use only the horizon sigma-field and
usual completeness restores the original paths. The original real product
definition remains unchanged. The general jump-case integral equation is now
proved by the two-coordinate Ito formula for `exp(x) y`. The actual pure-jump
FV integral is the initial term plus its weighted jump series. Its continuous
Jordan components cancel, and the remaining series cancels the Ito correction.
No division by a potentially zero product, sign restriction, initial moment,
or sample-uniform path bound is used. The initial value remains `exp(X(0))`.
Uniqueness remains open; II.37 is not yet closed.

Protter II.38 is implemented independently of that uniqueness gap. The actual
product identity uses the algebraic jump `u+v+uv`, its compensated exponential
factor, and the absolutely summable mixed-jump series. For arbitrary initial
values, `E(X+Y+[X,Y]) = exp(X(0)Y(0)) E(X) E(Y)`; the source zero-initial
formula is a corollary. No product is divided out, so absorbing minus-one
jumps and negative factors are retained. Indistinguishable integrators have
indistinguishable exponentials. For continuous integrators, `E(X)^(-1)` equals
`E(-X+[X]^c)` without an initial-moment premise. Replacing the continuous
bracket by the source raw bracket explicitly requires `X(0)=0`.
The multidimensional Levy characterization is proved below; later applications remain open.

The stochastic exponential of a continuous local martingale is now proved to be a
continuous local martingale, preserving arbitrary random initial values.
Complex local martingales are pairs of the existing real masked predicates;
coordinate integral preservation and compact integrable-envelope promotion
are proved. The actual characteristic exponential
`exp(i u X + u^2 [X]^c / 2)` is continuous and a complex semimartingale.
Its Ito equation cancels the positive FV drift against the negative
imaginary-imaginary bilinear bracket. It is a complex local martingale for
continuous local-martingale inputs. If `[X]^c=t`, deterministic compact
norm bounds make it a true complex martingale. The initial phase is retained
and has unit norm even without initial integrability. The remaining real
distributional steps are now proved: bounded complex pull-out gives the
conditional characteristic function, finite-measure Fourier uniqueness gives
the Gaussian law restricted to every past event, and ordered finite-intersection
induction gives mutual independent increments. These identify Mathlib's
canonical Brownian predicate. In the converse direction Gaussian moments and
past independence give the martingale and square-minus-time martingale;
continuous FV uniqueness identifies the existing raw bracket with time.
The resulting II.39 equivalence retains adaptedness and independence from
the specified past. The full-information filtration is proved incompatible
with Brownian martingales. The raw bracket forces zero initial value; the
continuous-bracket form requires it explicitly. Subsequent applications and
general usual-filtration transport remain open; the II.40 closure follows below.

The II.40 projection prerequisites now cover deterministic continuous-bracket
clocks, their actual Gaussian increments and past independence, without strict
clock increase. Finite continuous-local-martingale sums preserve the masked
localizers. Continuous square and mixed brackets satisfy the full finite
double sum; orthogonal coordinates with a common clock yield the coefficient
square sum. The raw/continuous bridge keeps the initial clock-zero guard.
The actual scalar linear-projection laws and conditional characteristic
functions are proved. The joint-law and process-independence steps are now
also proved, completing II.40 (Protter printed p.87, PDF p.98).
Hilbert-space Fourier uniqueness identifies the vector increment law as the
canonical Gaussian product transported to Euclidean space and proves its
independence from the entire past. Ordered vector increments give joint
Gaussianity in time and coordinate. Same-time independence and independence
of later increments give zero cross-coordinate covariance at arbitrary times;
Mathlib's Gaussian-process theorem then gives mutual independence of the
entire coordinate paths. `levy_multidimensional` returns the existing
`IsBrownianReal` predicates and `iIndepFun`, without a new Brownian owner.
The raw bracket forces zero initial values; the continuous-bracket version
requires them. The final independence interfaces only require `Finite`, not
a caller-selected enumeration. Empty families and repeated times are covered.

The open-domain harmonic part of II.41 (printed pp.87--88, PDF pp.98--99) is
proved. Finite integral sums and the complete ordered Hessian contraction
reduce the drift to the trace against the actual common continuous bracket.
Trace zero is required only on a common event of actual paths; the harmonic
specialization uses Mathlib's Euclidean Laplacian and `HarmonicOnNhd`.
Arbitrary initial values are handled by the existing Protter masks. No clock
integrability, strict increase or nonempty coordinate family is assumed.
The printed subharmonic conclusion requires correction: the smooth function
`exp(x^2/2)` has strictly positive Laplacian, but its Brownian composition is
nonintegrable at time 1 and hence is not a true submartingale in any filtration.
Both the actual Gaussian nonintegrability and analytic derivative calculation
are proved. The corrected full-space positive direction is now proved as
well: the actual common-clock Hessian integral gives a continuous increasing
zero-initial drift, and the remainder is a continuous local martingale.
Bounded drift exits and the masked fundamental sequence construct the
`Locally Submartingale` witness. A compact-time integrable envelope promotes
the composition to a true submartingale; the same guard gives a true
martingale for the harmonic case. No moment condition is required for the
local statement. Both results now hold on general open domains: genuine
smooth extensions near closed regions, compact exhaustions and actual exit
times are constructed. Zero-exit events use a domain basepoint rather than
an out-of-domain zero vector; the F0-measurable correction preserves the
continuous brackets. Raw common clocks are centered by `A_0`.
The subharmonic theorem explicitly covers classical C2 functions with
nonnegative Laplacian. The source statement does not spell out a smoothness
convention, although its proof invokes Ito and the Laplacian. No nonsmooth
potential-theoretic extension is claimed; that source-coverage audit remains
open, so the unqualified II.41 statement is not marked closed.

II.42's DDS theorem is proved, including the Brownian law. The inverse is the actual
strict-upper-level hitting time; unbounded clocks give finite inverse times
and exact level values. Continuous increasing clocks are proper quotient
maps, so continuous paths constant on clock fibers descend continuously.
The nonnegative-real clock is an exact codomain conversion of the sole
continuous bracket. Its inverse gives continuous sampled paths adapted to
`F_(T_s)`, the clock-substitution factorization and stopping times for the
original clock in that new filtration. All path conclusions share one event.
Raw divergence supplies unboundedness; zero initial values identify these
times with the source raw-bracket inverse. Flat intervals are allowed and
`T_(A_t) = t` is not asserted. The stopped characteristic exponential has a
deterministic bound; complex UI optional sampling at AE-finite times gives
the conditional Gaussian characteristic function. Fourier uniqueness yields
the increment law and independence from the entire stopping-time past.
The canonical Mathlib Brownian predicate follows with the explicit zero start.
Completeness identifies the canonical and raw-inverse stopping sigma-algebras,
so the source statement uses the actual raw hitting times, not only a version
with an unspecified filtration. No square-moment, prior Brownian-law or
time-changed-martingale premise is introduced. The proof's auxiliary
right-continuation step is also proved: `H_s = G_(s+)` is usual, the same
Brownian process is adapted with future increments independent of `H_s`, and
the original clock is still a family of stopping times. The general transfer
uses bounded continuous tests and dominated convergence with common-event
right continuity; Gaussian laws are not needed for that transfer. There is
no assertion that the original `G` is right continuous or equals `H`.
This does not close the package.

II.43's construction and algebraic prerequisites are proved: the actual
antisymmetric area integral starts at zero for arbitrary initial coordinates,
is a semimartingale, and is a continuous local martingale for continuous-local
coordinates. Its raw/continuous mixed brackets and continuous energy are
identified using the existing integral and bracket owners. The source
Riccati coefficients `u*tanh(u*(T-t))` and `-log(cosh(u*(T-t)))` are globally
smooth, satisfy their differential equations and terminal conditions, and
give the required exponential bound on `t <= T`, including nonpositive `u`.
The actual exponential's stochastic differential/drift cancellation,
characteristic function and positive-time density are now proved below.
At `T = 0` the proved area law is a point mass, not a Lebesgue density.
The actual Riccati-compensated area exponent and exponential are now constructed
with an explicit clock and proved to be complex semimartingales; continuous
coordinates and clock give continuous paths. The norm bound holds wherever
the clock is at most the terminal level. Zero initial coordinates and clock
give the source initial inverse-cosh value, and reaching the terminal clock
level leaves the actual area characteristic integrand. The continuous FV C1
formula removes the source zero-time and jump terms by proof, giving actual
stochastic-integral equations for both Riccati coefficients. These are used
in the full exponential drift cancellation and martingale proof below.
The squared-radius equation follows from the two common raw square brackets;
integrator linearity and associativity prove its integrated form for arbitrary
adapted caglad outer integrands. This permits nonzero raw-clock starts.
The actual integral of a random constant is its initial product, with no
integrability assumption. Consequently C1 substitution along a continuous
zero-starting FV clock retains `H_0 f(0)` for a transformed clock starting at
`f(0)`. These are proved ingredients of the full exponent drift calculation.
The continuous-FV multiplier formula now accounts for both left-limit initial
corrections and the raw bracket's initial value. Its weighted-radius consequence
and the Riccati equations prove the real-exponent representation with constant
`beta(0)` and radial drift `-(1/2) J_Q((X^2+Y^2)(alpha^2-u^2))`. The continuous
area formula also uses the actual integrals, with arbitrary initial coordinates.
The exponential drift cancellation below combines this real-coordinate
identity with the actual complex-bracket integral.
Continuous-FV multiplier mixed/square bracket formulas are now proved by
removing the actual FV integral remainder. Finite stochastic-integral sums
under isotropic continuous brackets have the clock integral of the coefficient
inner product as their mixed bracket; the square version and two-coordinate
interfaces are also proved. Applied to the actual continuous-coordinate area,
this gives its energy as `J_Q(X^2+Y^2)`, allowing arbitrary initial coordinates
and imposing no Brownian or moment assumptions.
The squared-radius continuous bracket is now proved to be `4 J_Q(R)` and its
mixed bracket with area to be zero. For the actual compensated exponent, FV
multiplier calculus gives the real bracket `J_Q(alpha^2 R)`, imaginary bracket
`u^2 J_Q(R)` and zero cross bracket. Thus its complex bilinear bracket is
`J_Q(R(alpha^2-u^2))`, where `R=X^2+Y^2`. This remains distinct from the
nonnegative energy. These identities use zero-starting continuous coordinates,
the common raw FV clock and orthogonal continuous brackets, with no supplied
exponent differential. They supply the bracket in the full exponential Ito
cancellation below.
Complex-integral initial-product, version-invariance, zero-imaginary-integrator
and real-inner-integral associativity interfaces are proved coordinatewise.
The continuous-real-local-martingale interface derives the required local L2
property internally, so callers need not supply it. These results preserve
arbitrary initial products and support the actual area-exponential equation
and its local-martingale property.

The actual complex integrals of the area, real exponent and complex bracket
now give the exponential Ito equation: its half-clock terms cancel exactly.
The remaining four integrals against the two continuous local martingales,
together with the retained initial random constant, prove that the actual
area exponential is a complex local martingale. At a deterministic time `S`
with deterministic common-clock value `T`, monotonicity of the raw clock and
the proved norm bound make the stopped exponential a true martingale. Its
endpoint expectation is the area characteristic function `1/cosh(u*T)`.
The standard-clock theorem derives clock regularity and zero coordinate
starts. The canonical independent-Brownian interface derives the raw and
continuous brackets from Brownian square-sum probability convergence and
independent normalized sums; future-increment independence from the chosen
usual filtration is explicit. It yields `E[exp(i*u*A_S)] = 1/cosh(u*S)` with
the source twice-signed-area normalization. Zero-parameter, time-zero
characteristic-function and actual time-zero Dirac-law regressions are included.
The positive-time density corollary is now proved. A sigmoid change of variables
and Mathlib's Beta/Gamma reflection identity evaluate the actual Fourier
integral of the hyperbolic-secant function. Scaling proves the transform and
normalization of `1/(2*T*cosh(pi*x/(2*T)))` for `T>0`. The resulting probability
measure has the required characteristic function, so Fourier uniqueness gives
the actual area law and explicit pushforward-with-density identity. The
canonical independent-Brownian interface includes the same theorem with its
filtration conditions explicit. At time zero the law is Dirac; a regression
proves that the zero-density measure would be incorrect. Further regressions
check the time-one density at the origin is `1/2` and negative Fourier parameters.
This closes II.43 and its density corollary. The entire package remains open.

The explicit counterexample is `Z(x)=x^(-1/2)` under Lebesgue probability on
`(0,1)` with the full initial filtration. Lean proves `Z` integrable, `Z^2`
nonintegrable, existence of an unmasked Klenke witness for the constant `Z`,
nonexistence for its square, and Protter-local legality of both processes.

## Required work still open

| Design block | Remaining implementation |
| --- | --- |
| Klenke 21.56--21.63 | Closed at the stated deterministic scope: genuine full-sequence partition dependence and nested-sequence nonconvergence, C1 composition with the actual Lebesgue-Stieltjes identity and continuous increasing zero-starting limit, exponent comparison, one-variation refinement/limit, source two-square polarization, zero-QV perturbation and exact infinite-restriction transport of the limiting-covariation FV theorem are proved. |
| Klenke 21.64--21.65, Exercise 21.10.1 | Native strong pathwise closure is proved: actual reverse-martingale square-sum construction, arbitrary nested vanishing mesh, common-event all-times Brownian QV, and independent Brownian cross-QV. The event may depend on the prescribed partition sequence. These results do not define a general stochastic bracket. |
| Klenke 21.70--21.76 | Finite-time normalized L2 equivalence with initial L2 (including 21.76), normalized second-moment identity and the true compensated-square theorem 21.70(ii) are proved from the sole raw/continuous-part owners. Remaining exact normalized/centered characterization and stopping interfaces, full 21.74 specialization and repaired all-times 21.71 extraction require their source-level closure audits. |
| Exercises 21.10.2--21.10.3 | Weighted quadratic-variation sums and the stopping/expectation counterexample. Example 21.69(ii) retains its explicitly permitted later Ito/harmonic application disposition. |
| Protter I.1--I.2, I.5--I.6 | Remaining source stopping/jump/F_T bridges. Full Doob regularization (I.9), same-class cadlag versions, indistinguishability uniqueness and the true-martingale/cadlag corollaries are proved under usual conditions. Bounded sampling, AE-finite UI sampling with AE ordering, closed/UI equivalence, arbitrary UI stopping, I.48(a--e), I.49 on the cadlag domain, I.50, I.51, continuous bounded masked localizers and continuous-local/locally-L2 equivalence are proved. For right-continuous true martingales with uniformly bounded second moments, the constructed L2 terminal variable now has full-half-line AE/L2 convergence and all-time conditional-expectation closure; the tail Doob/Borel-Cantelli argument extends the integer limit. Possibly infinite sampling is proved for UI martingales with their actual terminal limit, including AE-only ordering and Lp control; finite raw terminal energy constructs all required hypotheses. General right-continuous UI martingales now have a constructed integrable terminal variable with full-time AE/L1 convergence and closure, without L2; this also supplies the possibly-infinite sampling limit premise. I.10's arbitrary-closing terminal projection and I.13's explicit extended-index martingale/UI equivalence are proved with the canonical `iSup F` terminal field. The I.16 native-owner correction from arbitrary closing input uses its terminal projection; unprojected sampling requires terminal-field measurability, and a usual two-point counterexample rejects dropping it. General L1-bounded right-continuous submartingale/supermartingale full-time convergence (I.10) is now proved with an integrable limit, without UI or L2; this does not assert L1 convergence or closure. General bounded one-sided I.17 and stopping-time conditional-expectation commutation (I.18, second corollary) are proved. Lower-closed supermartingales now have a proved actual integrable terminal limit dominating the closing projection, horizon-independent stopping first moments, and arbitrary stopping integrability; the full unbounded AE-ordered conditional inequality is proved with the same terminal-projection correction, together with its nonnegative zero-terminal corollary. |
| Protter I.3--I.4 | Brownian source-filtration transfer to the genuine completed usual augmentation is proved. Cadlag Levy realization, Levy decomposition and remaining source path results are open. Poisson real cadlag/FV paths and its adapted usual-filtration semimartingale example are proved. Brownian and square-minus-time martingales, strong QV and infinite variation on every nondegenerate interval are proved; these do not supply Levy path theorems or arbitrary information enlargement. |
| Protter I.7--I.8 | I.52 random differentiation/polar-density theorem and required impossibility statements. Random variation measures/integrals, regularity, source elementary agreement, tagged random-partition I.53, continuous-FV I.54 with its substitution corollary, and right-continuous FV C1 change of variables (II.31) are proved. |
| Protter II.1--II.3 | Jacod expansion and Levy examples remain open. Brownian source-filtration transfer to the genuine completed usual augmentation is proved. Source simple-process common refinement, algebra, bilinearity, cutoff/elementary stopping, good-integrator and total/ordinary stopping, adaptedness/caglad/predictability, absolute-continuous changes of measure, countable mixtures, Stricker shrinkage, FV/Poisson/decomposable and L2/locally L2/CLM examples, and exact `T-` patching/localization are proved. |
| Protter II.4--II.5 | General local-martingale preservation beyond locally-L2 is now proved by III.33. Corrected II.10 density, full II.11 continuity, UCP completeness and the unique linear UCP-continuous Chapter II integral extension are proved, including its initial term, stopping/cutoff (II.12), jumps (II.13), absolutely continuous measure invariance (II.14), countable-mixture invariance and a common two-probability version (II.15), invariance between possibly incomparable usual filtrations (II.16), integrator indistinguishability invariance, common-event FV agreement (II.17), locality on whole-path-agreement/finite-variation events (II.18), both assertions of its stopping-interval corollary, semimartingale preservation/associativity with FV preservation (II.19 and its remark), general locally square-integrable martingale preservation (II.20), and full cadlag/caglad random-partition Riemann approximation (II.21). |
| Protter II.6 | II.22--II.23: raw QV and polarized mixed covariation, initial/jump identities, random-partition UCP limits, mixed bilinearity/FV, stopping in both or either argument, integration by parts and semimartingale products are proved. II.24--II.25 and the expectation/Lp corollary are proved, including endpoints, measurable random energies and initial terms. Continuous square and mixed components are adapted, continuous, zero-starting and FV, with exact summable-jump decompositions, mixed bilinearity, version invariance and simultaneous/one-sided stopping. General II.26 and the source quadratic-pure-jump property are proved from actual Stieltjes jump integrals and summable series. II.27's main theorem and Corollaries 1--2 are proved without initial moments: compensation, centering, FV constancy, each ordered stopping-interval result, and locally-L2 raw mixed characterization. Corollary 5's common-event all-intervals statement is proved, including arbitrary random endpoints and unbounded intervals. The discontinuous compensated-Poisson example is proved, including the actual raw bracket and common-event flat intervals; Corollary 3's finite-time moment equivalence, exact expectations and true compensated-square martingale are proved on the actual semimartingale domain, with automatic continuous-local-martingale entry; terminal raw energy is equivalent to true global L2 boundedness, with a constructed L2 closing variable, integer AE/L2 convergence, all-time conditional-expectation closure and the exact terminal moment identity; whole-half-line AE/L2 convergence is now proved, completing Corollary 4 on the actual semimartingale domain with automatic CLM entry; the general local-martingale semimartingale witness is now supplied by the proved III.30 corollary. II.28's quadratic-pure-jump mixed formula, FV/continuous-path corollaries and linear stability are proved. II.29's brackets of general integrals and II.30's weighted random-partition limits are proved. **No fallback or competing continuous-martingale bracket exists.** |
| Protter II.7--II.8 | Stochastic-exponential uniqueness and later applications remain open. II.31's right-continuous FV C1 formula, summable jump correction and FV preservation are proved. II.32--II.33's scalar and finite-dimensional cadlag cases, both raw- and continuous-bracket formulas, actual summable/FV jump corrections and C2 preservation are proved. II.34's source Fisk-Stratonovich definition, C3 chain rule, jump/FV properties and integration-by-parts corollary are proved. II.35--II.36's complex analytic formulas, actual absolute jump correction, bilinear brackets and source initial-value comparison are proved. II.37's actual product is an adapted cadlag semimartingale satisfying the general integral equation, but uniqueness is not proved. II.38's product and continuous inverse formulas are proved, with explicit raw initial-value guards. II.39's real Brownian characterization is proved in both directions, retaining adaptedness and independence from the specified past; the canonical raw bracket forces zero initial value. II.40 is proved with joint Gaussian increment laws and mutual independence of the entire coordinate processes. |
| Protter II.8 applications | II.41's nonsmooth subharmonic scope remains under audit; the open-domain harmonic and corrected classical C2 subharmonic statements are proved. II.42's stated DDS theorem and its auxiliary usual right-continuation step are proved. II.43's characteristic function and positive-time area density are proved, with the zero-time Dirac case separate. |
| Protter III.1--III.2 | Remaining deeper progressive-debut/strict-inclusion statements, predictable-graph equivalence and III.4 Meyer's Markov/Feller jump classification. Accessibility, total inaccessibility and full III.3 existence/reconstruction/AE uniqueness are proved with native stopped-measurable events. Every stopping graph is optional; the strict future is predictable. The source optional/progressive sigma-fields, exact progressive generator/predicate identity, full predictable/optional/progressive/product inclusion chain, optional version and stopping bridges are proved. The predictable source identification and left-limit bridges, F_(T-), III.7, finite and explicit-terminal III.5/III.8, source AE announcing sequences and the III.6 field identity are proved. Cadlag AE-zero-initial real SII processes now have TI jumps in their own genuine completed usual natural filtrations; canonical Levy cadlag realization/decomposition and Meyer--Feller remain separate gaps. |
| Protter III.3--III.5 | General local Doob--Meyer/Rao, canonical compensation, III.24--III.25, general local Yoeurp, actual angles, lifetime/arrival/censoring hazards and nonexplosive forward/reverse counts are proved. Corrected III.19 now consumes the original AE-source and actual canonical-compensator integrals. Corrected III.20 identifies the right-value pathwise integral and its actual compensation on the predictable FV domain, extending to native local martingales. Initial products are retained. Later measure/filtration-change applications remain open. |
| Protter III.6--III.7 | III.29--III.35 fundamental/classical/integral/canonical-special results and III.38 source-strength stopped supremum integrability are proved. General predictable FV local IV and the normalized locally-IV decomposition criterion are proved. III.36--III.37 now hold in both directions on the classical domain, using actual compensation for the converses. The original jump supremum is adapted and commutes with stopping; its factor-two bound is necessary. The good-integrator-to-classical implication remains separate work. |
| Protter III.8--III.9 | The terminal real RN density and canonical cadlag/UI/nonnegative density process, fixed/stopping-time Bayes and density identities, common-event reciprocal/positivity/cadlag inverse, and a joint forward/reverse localizer are proved. Positive-time left limits are strictly positive with exact reciprocal identities and local bounds under equivalence. True, uniformly integrable and local martingales transfer by density multiplication. Protter III.39 is proved with the raw bracket, a division-free reverse-density correction and its exact right-value Stieltjes representation. Protter III.40 is proved with the canonical predictable bracket on its actual locally-integrable-variation domain. For merely `Q ≪ P`, the geometric lower-density exits form a `Q`-localizing sequence and bound positive-time `Z₋` away from zero up to each exit. Protter III.41 is proved by a target-law predictable correction and clipped source-law localization, without reverse absolute continuity. Remaining: Lenglart--Girsanov III.42 and its zero-density jump compensator, Kazamaki/Novikov, Brownian acceptance, Yan/Hahn--Banach control, Rao/Girsanov transfer and finite-horizon patching for the actual BD equivalence. |
| Source closure | Exact individual theorem/corollary/remark/exercise transcription for all Protter I--III sections. The section rows here are a working ledger, not a replacement for this completion gate. |

## Blocker status

`PARTIAL` and `OPEN` below are working statuses, not final completion dispositions.
The package completion gate has not been reached.

| ID | Current status | Evidence / remaining obligation |
| --- | --- | --- |
| SM-B01 | PARTIAL | Cadlag/caglad, finite stopping, optional/progressive fields, accessibility/inaccessibility with III.3 decomposition, and deterministic FV owners resolved; finer stopping-classification bridges and random FV closure stay open. |
| SM-B02 | RESOLVED at corrected mesh semantics | Deterministic/random partition owner, finite restriction and tending-to-identity bridge proved. See source correction below. |
| SM-B03 | RESOLVED on the source finite-measure domain | UCP measurability, fixed-time bridge, common-event subsequence and sequential adapted-cadlag completeness are proved. The general integral is a separate construction. |
| SM-B04 | PARTIAL | General bounded one-sided and arbitrary AE-ordered closed-supermartingale sampling are proved, including native projected terminal values; unprojected values retain their terminal-measurability guard. General L1-bounded/UI full-time convergence, actual closed/UI equivalence, arbitrary UI stopping, I.48--I.51 and the continuous-local/locally-L2 bridge are proved on their stated domains. Full Doob regularization and its source corollaries are proved; remaining source stopping/filtration bridges stay open. |
| SM-B05 | RESOLVED | Mathlib `TendstoInMeasure` reused directly. |
| SM-B06 | RESOLVED | Existing `Indistinguishable`/modification owners retained. |
| SM-B07 | RESOLVED for source continuity criterion | Both directions of sequential/epsilon-delta zero-continuity, uniform difference estimates, Cauchy-in-measure control and convergence at every simple limit are proved. |
| SM-B08 | RESOLVED for the source class | F_T coefficient domain, representation independence, common stopping-time refinement, Borel algebra closure, elementary bilinearity, cutoff/elementary stopping, adaptedness/caglad/predictability and corrected II.10 UCP density are proved. The general integral reuses this source owner. |
| SM-B09 | RESOLVED | Actual reverse-martingale conditional-square construction; arbitrary admissible-sequence strong Brownian QV and independent cross-QV, on common all-times events. Concrete dyadic admissibility is proved. |
| SM-B10 | PARTIAL | Masked/unmasked bridge, initial-value regressions, monotone completed square sums, uniformly vanishing partial-cell error and native Brownian all-times extraction are proved. Remaining obligations are the exact normalized/centered Klenke 21.70--21.76 source interfaces, including repaired general 21.71, full 21.74 and random-lifetime 21.75. |
| SM-B11 | RESOLVED for construction and approximation independence | The Chapter II integral is constructed by density, source continuity and proved UCP completeness. Every simple approximation converges to the same cadlag limit; linearity and full-domain UCP continuity are proved. Further integral properties remain in the Chapter II ledger. |
| SM-B12 | RESOLVED for canonical construction and random-partition theorem | Actual raw square/mixed brackets, initial values, random-partition UCP approximation and continuous/jump decomposition are proved. Remaining applications and LM-to-SM entry are tracked separately. |
| SM-B13 | RESOLVED for Doob--Meyer and Yoeurp closure | Discrete potential decomposition, continuous III.10, general Class D III.11, III.12--III.15, general local III.16, normalized zero-initial form, predictable FV uniqueness, the finite-mean-limit integrable-terminal supplement and general local Yoeurp are proved. |
| SM-B14 | RESOLVED for quasimartingale/Rao closure | Source-exact terminal-zero conditional variation and strict-partition equality, both directions of III.17, and actual III.18 Rao existence/uniqueness are proved. The variation part even has global integrable variation on the global quasimartingale domain. |
| SM-B15 | PARTIAL for applications | Actual local-IV compensation, global-IV UI/mean conclusions, III.24--III.25, actual angles, counting compensation, reverse arrivals and the designed lifetime/arrival/censoring hazard applications are proved. Corrected full AE-source III.19 and actual right-value III.20 consumers are proved with explicit initial conventions and constructed domains. Later measure/filtration-change applications remain open. |
| SM-B16 | RESOLVED for fundamental decomposition and LM-to-SM | Actual large-jump local-IV localization, local compensation jump bounds and III.29 exact decomposition are proved. Its locally square-integrable part gives normalized decomposability and the general LM-to-SM bridge. Classical/decomposable equivalence, III.30--III.37, general local-martingale integration and canonical special decomposition are proved. The good-integrator-to-classical direction remains the separate BD gate. |
| SM-B17 | PARTIAL | The terminal RN density and its canonical cadlag uniformly integrable nonnegative density process are constructed with exact deterministic/stopping-field event integrals. Fixed/stopping-time Bayes, common-event reciprocal/positivity/cadlag inverse, a two-law joint localizer with bounded positive-time left-limit inverses, equivalent-law true/UI/local martingale transfer, raw-bracket III.39, predictable-bracket III.40 and merely-AC predictable III.41 are proved. The one-way geometric lower-density exits are a `Q`-localizing sequence with exact positive left-limit and reciprocal bounds. Lenglart--Girsanov III.42 remains. |
| SM-B18--SM-B19 | OPEN | Kazamaki/Novikov and the Yan/Hahn--Banach/BD chain. |
| SM-B20 | OPEN | Exact individual source transcription is incomplete. |
| SM-B21 | PARTIAL | Exact external revision revalidated; unfinished Doob-Meyer closure rejected. No new external code was copied. Further adopted closures would require their own audits. |

## Regression coverage

R01--R04 and R06 have the elementary-integral/finite-stopping/continuity results.
R33--R34 have the explicit L1-not-L2 example. R38 holds for the current production
dependency graph. R05 has the source stopping-time representation, but no full
negative-test fixture. R07--R08 have UCP bridges, not yet their complete separation
counterexamples. R16/R19/R20/R35 have deterministic increment/cross-sum tests,
not the still-missing general stochastic bracket conclusions.
R35 now has monotone completed-cell approximation, uniformly vanishing partial-cell
error, exact infinite-restriction transport and dense-to-all-times deterministic
extraction. The native Brownian theorem uses this repaired extraction on one event;
the general continuous-local-martingale bracket specialization still awaits its owner.
R34 additionally checks the positive centered bounded-localizer construction,
without an initial integrability hypothesis. The original unbounded-initial
counterexample is retained alongside this corrected bridge.
R36 has the unrestricted deterministic zero-QV perturbation theorem, not yet the
full local-martingale specialization. R37 has the actual partition embedding and
the general random-partition square/mixed UCP limit theorems. R09--R15, R17--R18,
R21--R32 and all remaining parts of the preceding partial rows remain open.

## Source correction: Protter II.25 discriminant

Printed p.69/PDF p.80 calls the discriminant nonnegative for an everywhere
nonnegative quadratic polynomial. The required sign is nonpositive.
`QuadraticCovariation/IncrementBound.lean` uses Mathlib's `discrim_le_zero`
after a countable rational-scalar intersection and a density argument.
All interval endpoints are covered on one event. The weighted measure theorem
is now proved separately, using actual measure domination and Holder's inequality.

## Source correction: Klenke 21.56 mesh

Printed page 562 (PDF page 568) defines the supremum of **nearest-neighbor**
distances. This is insufficient: take

`P_n = { k + j/(4*2^n) : k in Nat, j=0,...,2^n }`.

These sets are nested, unbounded and locally finite. Every point has a neighbor
within `1/(4*2^n)`, but the adjacent gap `(1/4,1)` remains of length `3/4`.
The continuous bounded-variation function which is zero up to `1/4`, rises
linearly to one at `1`, and then stays one has square sum exactly one on `[0,1]`
for every `P_n`. Consequently the literal printed mesh condition cannot imply
even the source continuous-FV zero-QV claim.

The project uses the maximum **adjacent** gap, defined by finite restrictions
and an extended supremum over horizons. This correction is explicit; no theorem
claims a lossless implication from the defective nearest-neighbor hypothesis.
The counterexample argument in this paragraph has been checked mathematically
against the rendered source; it has not itself been encoded as a Lean theorem.

The FV elementary-agreement increment proves pathwise local integrability for the
full source class and exact equality at every finite horizon with the elementary
integral of the stopped integrator. At a representation's random terminal endpoint
it equals the entire finite sum. Repeated endpoints and arbitrary finite coefficients
remain valid. Owners: `Analysis/PathVariation/StieltjesIntegralSimple.lean` and
`Process/FiniteVariation/SimpleAgreement.lean`.

Source adapted everywhere-caglad integrands now have proved compact path bounds,
hence local Stieltjes integrability, progressive FV integrals and their
semimartingale property. Users need not supply a separate path-integrability
assumption for this source class. Owners: `Process/Path/CagladBounded.lean` and
`Process/FiniteVariation/CagladIntegral.lean`.

The full FV integral jump identity is proved from canonical Jordan measure atoms
at positive times and the separate initial term at zero. Both source caglad and
common-event all-times AE versions are available in `Process/FiniteVariation/Jump.lean`.

Both FV instances of Protter II.12 are proved: stopping the integral equals
integrating the cutoff integrand and integrating against the stopped integrator.
Canonical variation measures restrict to the closed horizon; zero/infinite
lifetimes and endpoint atoms are retained. Stopping-time cutoff preserves
adapted caglad paths and predictability. Owners: `Analysis/PathVariation/StieltjesIntegralStopping.lean`,
`Process/Stopping/Integrand.lean` and `Process/FiniteVariation/Stopping.lean`.

FV integration is now proved path-local and invariant under indistinguishable
changes. The compact operator bound retains the initial value and proves uniform
convergence. Actual UCP continuity on the source adapted-caglad class follows by
common-event subsequences and measurable output deviations, without expected
variation integrability. Given source simple approximations, their elementary
integrals converge to the pathwise FV integral. The later II.10 theorem supplies
density; the general integral is still separate. Owners: `StieltjesIntegralContinuity.lean`,
`Process/FiniteVariation/{Continuity,UCP}.lean` and `Process/UCP/UniformConvergence.lean`.

Continuous-FV Protter I.54 and its substitution corollary are now proved from
actual left Riemann sums and uniform first-order remainder estimates. C1 composition
preserves local BV and has common-event process/semimartingale versions. Full
source integrals retain the initial term; in particular `integral X dX` equals
`(X_t^2 + X_0^2)/2`. Owners: `Analysis/PathVariation/C1ChangeOfVariables.lean`,
the left-step/Riemann prerequisite modules and `Process/FiniteVariation/ChangeOfVariables.lean`.
Klenke 21.62 is a different C1 formula for general quadratic-variation paths.
It is now proved separately in `Analysis/PathVariation/QuadraticVariationComposition.lean`,
using `CumulativeIntegralLimit.lean` and `QuadraticVariationStieltjes.lean`.
Continuous weights against finite nonnegative cumulative sums converge to the
actual path Stieltjes integral. The squared differentiated-slope error vanishes
against bounded square sums. The output is continuous, increasing, starts at
zero and satisfies all-time QV convergence. Neither input finite variation,
C2 smoothness nor a weighted-limit certificate is assumed. Repeated endpoints
and arbitrary input initial values are retained. Full-sequence partition
dependence is now proved separately: actual value-midpoint refinements and
finite extensions of dyadics yield nested admissible zero-QV sequences for any
continuous path at the prescribed horizon. A continuous path from the internal
Brownian construction has dyadic QV one at that horizon. Consequently the
Brownian theorem cannot use one probability-one event for all admissible
sequences. This is not merely a finite-refinement inequality counterexample.
Owners: `Analysis/PathVariation/{MidpointRefinement,CommonRefinement,SmallVariationPartitions,FiniteExtension}.lean`
and `Probability/Brownian/PartitionDependence.lean`. The separate nested-sequence
nonconvergence example is now proved in `Analysis/PathVariation/{CellInsertion,FiniteInsertionLimit}.lean`
and `Probability/Brownian/QuadraticVariationNonconvergence.lean`. Adding any fixed
finite endpoint set preserves continuous-path QV convergence. Each new high or
low step refines all preceding endpoints and the next dyadic grid. Even square
sums stay below `1/4`, odd ones above `3/4`. The extended infinite sequence is
nested and admissible and has no real QV limit. This closes the remaining
deterministic Klenke 21.56--21.63 construction obligations.

Protter I.53 is now proved for sample-dependent finite partitions and arbitrary
tags in their closed cells. Common-event mesh/continuous-integrand hypotheses
give uniform convergence over partial terminal times on the fixed horizon and
the source terminal increment limit. Future tags need not be stopping times;
their step functions are not claimed adapted. Owners: `TaggedStepApproximation.lean`,
`StieltjesIntegralTagged.lean` and `Process/FiniteVariation/Riemann.lean`.

Source simple-predictable common refinement and algebra are now proved. The
min/max endpoint construction is finite and permits sample-dependent coincidences.
Repartitioned coefficients are known at their new left stopping endpoints; the
entire process and elementary integral are unchanged. Zero-preserving binary
Borel operations give addition/product closure, with scalar/negative/subtractive
closure and elementary bilinearity. Unbounded finite coefficients, empty cells and
independent initial values are all retained. No probability or usual-filtration
assumption is needed. Four existing integrator-linearity declarations have moved
to the lower `SimplePredictable/IntegratorAlgebra.lean` owner without API changes.
The later II.10 construction supplies source density; the general integral remains separate.

Source stopping is now proved as well. The closed cutoff stays in the full simple
class, and its elementary integral equals integration against the stopped integrator
for arbitrary raw integrators and possibly infinite stopping times. The initial
term is retained at zero. The source epsilon/delta criterion proves good-integrator
stopping; under usual conditions this gives total/ordinary semimartingale stopping.
Total implies ordinary without usual conditions, and bounded stopping of an ordinary
semimartingale is total. Owners: `SimplePredictable/Stopping.lean` and
`Semimartingale/Stopping.lean`. This does not close the general-integral II.12 theorem.

The source operator is now an actual linear map on the exact simple-predictable
submodule. Elementary negation/subtraction laws and uniform difference estimates
prove continuity in measure at every simple limit, and send uniformly Cauchy source
sequences to Cauchy families in measure. The input convergence is uniform in both
time and sample, not UCP. No L0 quotient, limit selector or general integral is
postulated by these interfaces. Owners: `SimplePredictable/LinearMap.lean` and
`Semimartingale/Continuity.lean`.

Right-continuous open-target hitting is now proved using the existing Mathlib
owner. The everywhere-path version needs right continuity of the filtration,
not completeness. The AE-path version resets one initial null event and transfers
the original hitting time back using usual completeness. Finite hits lie in the
closure of the target; norm bounds deliberately allow overshoot. These support
the II.10--II.11 density/maximal/UCP proof chain, only partly closed below.

The source elementary process `J_X(H)` now reuses the existing integral at each
deterministic stop. It has adaptedness, common-event cadlag paths, exact initial
and terminal values, source linearity, stopping/cutoff identities and FV agreement.
The adaptation proof reveals a coefficient only strictly after its original left
endpoint and uses the zero increment before that point. None of these results
requires bounded coefficients or integrability.

The maximal estimate and uniform-input half of II.11 are now proved. A finite
first-exit cutoff reduces the maximal event to the already-controlled terminal
elementary integral; no maximum attainment or no-overshoot assumption is used.
The total bound is uniform over horizons and the ordinary bound fixes a horizon.
Uniform convergence in time and sample to any simple limit implies convergence
in the original UCP predicate, via a proved strict-real-threshold characterization.
The second half of II.11 is now proved as well: the full simple source class is
closed under initial-event masks, and the actual left-continuous first-exit
truncation is uniformly bounded. Countable hit detection keeps the separate initial
point. A larger input horizon controls the discarded event even when the first hit
is an unattained boundary or the path jumps immediately after zero. This yields
UCP continuity at every simple limit and UCP-Cauchy estimates. UCP completeness
and the general integral extension remain open; corrected density is proved next.

Right-limit and nonaccumulation prerequisites for II.10 are also proved. The
right-limit process is cadlag and adapted under right continuity of the filtration;
its left limit recovers the caglad input at positive times. The separate initial
value is retained. Actual uniformly separated ordered samples escape every finite
horizon, including sequences of extended times that reach infinity. Actual recursive
oscillation stopping times and finite capped partitions are now constructed from
these results. The cell estimate compares the input's positive-time left limit
with its right-limit sample, while preserving the separate original initial value.
Shrinking thresholds and a proved probability diagonal for finite cell counts yield
full corrected II.10 density under a finite measure and usual conditions.

## Source correction: Protter II.10 first interval

Printed p.57 (PDF p.68), checked by rendering, starts the final finite approximation
sum at `i = 1` even though `T_0 = 0`. For `Y = Z = 1` and a positive oscillation
threshold, every positive-index hitting time is infinite. After capping at `n`,
the printed cells are all `(n,n]`, so the approximant is zero at positive times.
The first interval must be included, for example by summing `i = 0,...,n-1`.
The constant no-hit and omitted-first-interval expressions are formal regressions.
The corrected full density construction is now proved in `SimplePredictable/Density.lean`.
The actual finite representation reproduces the constant-one process on its entire
cap with one cell, including the first interval. Its coefficients sample only finite
capped endpoints, avoiding unprovided values at infinite uncapped times.

## Verification

Current user-directed build policy: check incremental modules and their affected
dependents during continued implementation. Do not repeat a whole-library build
until the entire Semimartingale package is complete. The full build recorded below
finished before this policy change; it is historical checkpoint evidence.

- Full `lake --no-cache build`: **PASS, 9026 jobs**, including ten new production
  modules for unbounded endpoint sampling, the sharp elementary L2 estimate,
  actual L2/local-L2/CLM semimartingale examples and source localization, after
  the 9016-job Brownian all-times/infinite-variation checkpoint.
- Current FV/stability increment: **PASS**, targeted Lake build of
  `StochLean.Probability.Process.Semimartingale.SemanticRegression` and its affected
  dependencies (8836-job dependency closure, with unchanged jobs reused). This is
  not a repeated whole-library build. The twelve new production modules and two
  modified production modules have no warning/error-level entries in final traces.
- Subsequent left-limit/predictability increment: **PASS**, the same targeted
  dependency build (8847-job closure, unchanged jobs reused), covering eleven new
  production modules and two modified production modules. Final traces have zero
  warning/error-level entries. No whole-library build was run for this increment.
- Random variation/Stieltjes increment (2026-09-08): **PASS**, targeted dependency
  build (8857-job closure, unchanged jobs reused), with nine new production modules
  and two modified production modules. All eleven changed-module traces have zero
  warning/error-level entries after line-length cleanup. No whole-library build.
- FV integral regularity increment: **PASS**, targeted 8861-job dependency closure,
  four new production modules and the updated semantic regression. Final changed
  traces have zero warning/error-level entries; no whole-library build was run.
- FV elementary agreement increment: **PASS**, targeted 8863-job dependency closure,
  two new production modules and updated regressions. All three changed-module
  traces have zero warning/error-level entries. No whole-library build was run.
- Source caglad FV-integrand increment: **PASS**, targeted 8865-job closure;
  two new production modules and the updated regression import have zero
  warning/error-level entries. No whole-library build was run.
- FV integral jump increment: **PASS**, targeted 8867-job dependency closure;
  two new production modules and the updated semantic regression have zero
  warning/error-level trace entries. No whole-library build was run.
- FV integral stopping increment: **PASS**, targeted 8870-job dependency closure;
  three new production modules and updated semantic regressions have zero
  warning/error-level trace entries after line-length cleanup. No whole-library build.
- FV continuity/UCP increment: **PASS**, targeted 8874-job dependency closure;
  four new production modules and the updated semantic regression import have
  zero warning/error-level trace entries after line-length cleanup.
  No whole-library build was run.
- Continuous-FV C1 increment: **PASS**, targeted 8878-job dependency closure;
  four new production modules and two new semantic regressions. All changed
  production traces have zero warning/error-level entries after line-length cleanup.
  No whole-library build was run.
- Tagged random-partition increment: **PASS**, targeted 8881-job dependency closure;
  three new production modules and two semantic regressions have zero warning/error
  trace entries after style cleanup. No whole-library build was run.
- Source simple algebra/refinement increment: **PASS**, targeted 8886-job dependency
  closure, with unchanged jobs reused. Five new production modules and three
  modified production modules, including semantic regressions, have zero warning/error
  trace entries after style cleanup. No whole-library build was run.
- Source stopping increment: **PASS**, targeted 8888-job dependency closure,
  with unchanged jobs reused. Both new production modules and the updated semantic
  regression have zero warning/error-level trace entries. No whole-library build.
- Source linear-map/continuity increment: **PASS**, targeted 8890-job dependency
  closure, with unchanged jobs reused. Two new and two modified production modules
  have zero warning/error-level trace entries. No whole-library build was run.
- Right-continuous first-exit increment: **PASS**, targeted 8892-job dependency
  closure, with unchanged jobs reused. Both new modules and the updated semantic
  regression have zero warning/error-level traces. No whole-library build was run.
- Source elementary-process increment: **PASS**, targeted 8895-job dependency
  closure, with unchanged jobs reused. Three new and three modified production
  modules have zero warning/error-level traces. No whole-library build was run.
- Elementary maximal/uniform-to-UCP increment: **PASS**, targeted 8899-job dependency
  closure, with unchanged jobs reused. Four new modules and the updated semantic
  regression have zero warning/error-level traces. No whole-library build was run.
- Full source UCP-continuity increment: **PASS**, targeted 8903-job dependency
  closure, with unchanged jobs reused. Four new modules and the updated semantic
  regression have zero warning/error-level traces. No whole-library build was run.
- Right-limit/nonaccumulation increment: **PASS**, targeted 8907-job dependency
  closure, with unchanged jobs reused. Four new modules and the updated semantic
  regression have zero warning/error-level traces. No whole-library build was run.
- `Audit/SemimartingaleAxioms.lean`: **PASS, 102 selected load-bearing declarations**,
  with the expected count checked automatically and zero unexpected axiom sets.
  Every set is exactly `propext`, `Classical.choice`, `Quot.sound`.
- `Audit/SemimartingaleIntegrationAxioms.lean`: **PASS, 10 additional declarations**,
  checked in the smaller integration-prerequisite import closure; zero unexpected
  axiom sets. These supplement, rather than replace, the preceding 102-declaration audit.
- `Audit/SemimartingaleBrownianAxioms.lean`: **PASS, 13 additional declarations**,
  including the actual reverse martingale and non-summable fixed-horizon theorem;
  exact count checked and zero unexpected axiom sets (the same three standard axioms).
- `Audit/SemimartingalePathAxioms.lean`: **PASS, 14 additional declarations**,
  including all-times QV/cross-QV, exact restriction transport, dyadic admissibility
  and infinite variation on every nondegenerate interval; only the same standard axioms.
- `Audit/SemimartingaleL2ExamplesAxioms.lean`: **PASS, 22 additional declarations**,
  including the initial-term energy bound, good-integrator proof, strict-before-lifetime
  patching and the continuous-local example; only the same three standard axioms.
- `Audit/SemimartingaleFVStabilityAxioms.lean`: **PASS, 19 additional declarations**,
  covering source measurability/variation estimates, FV/Poisson/decomposable examples,
  absolute continuity, countable mixtures and Stricker; only the same standard axioms.
- `Audit/SemimartingaleLeftLimitAxioms.lean`: **PASS, 30 additional declarations**,
  covering left limits, source `T-`/AE patching, strict-past grids, predictable
  sigma-field identification and full source simple-process regularity. Exact
  count checked automatically; zero unexpected axiom sets (the same standard three).
- `Audit/SemimartingaleStieltjesAxioms.lean`: **PASS, 38 additional declarations**,
  including right-continuous variation approximation, random measure construction,
  finite-fiber integral measurability, pathwise bounds/dominated convergence and
  progressive-integrand adaptedness. Exact count and standard three-axiom sets
  checked automatically. Regressions preserve the initial term, zero initial
  variation and absence of an artificial time-zero increment-measure atom.
- `Audit/SemimartingaleFVRegularityAxioms.lean`: **PASS, 13 additional declarations**,
  checked count and standard three-axiom sets. These cover one-sided primitive
  limits, atom jumps, actual variation arithmetic, locally BV/cadlag pathwise
  integrals and their semimartingale property. A Dirac-at-one primitive has a
  formally verified unit jump.
- `Audit/SemimartingaleFVAgreementAxioms.lean`: **PASS, 11 additional declarations**,
  checked count and standard three-axiom sets. Full source agreement/integrability,
  random terminal evaluation, repeated endpoints and future-interval zero contribution
  are covered without coefficient boundedness or strict partition assumptions.
- `Audit/SemimartingaleFVCagladAxioms.lean`: **PASS, 7 additional declarations**,
  count and standard three-axiom sets checked. Compact bounds are derived from
  actual two-sided path regularity, including the time-zero boundary.
- `Audit/SemimartingaleFVJumpAxioms.lean`: **PASS, 7 additional declarations**,
  all with the standard three axioms. The initial-jump regression needs no local
  integrability assumption and retains an arbitrary nonzero initial value.
- `Audit/SemimartingaleFVStoppingAxioms.lean`: **PASS, 27 additional declarations**,
  exact count and standard three-axiom sets checked automatically. Regressions
  retain the initial integral under zero stopping and the cutoff value/measure
  atom at the stopping endpoint.
- `Audit/SemimartingaleFVContinuityAxioms.lean`: **PASS, 18 additional declarations**,
  exact count and standard three-axiom sets checked automatically. Includes path
  locality, uniform/UCP convergence, subsequence converse, limit uniqueness and
  the elementary-approximation implication (not an assumed density construction).
- `Audit/SemimartingaleFVC1Axioms.lean`: **PASS, 26 additional declarations**,
  exact count and standard three-axiom sets checked automatically. Covers partition
  cells, Riemann limits, actual C1 change of variables, substitution, local BV
  preservation and common-event process formulas.
- `Audit/SemimartingaleFVTaggedAxioms.lean`: **PASS, 16 additional declarations**,
  exact count and standard three-axiom sets checked automatically. Includes the
  full tagged approximation and its common-event random-partition versions.
- `Audit/SemimartingaleSimpleAlgebraAxioms.lean`: **PASS, 24 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers actual
  common refinement, stopping coefficient measurability, repartitioning invariance,
  source algebra and elementary bilinearity, including the retained integrator-linearity
  API. Three regressions preserve unequal horizons, initial products and zero splits.
- `Audit/SemimartingaleSimpleStoppingAxioms.lean`: **PASS, 15 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers source
  cutoff, arbitrary-integrator stopping, good-integrator/semimartingale stopping,
  total-to-ordinary and bounded-total bridges, with zero/infinite/closed-endpoint regressions.
- `Audit/SemimartingaleSourceContinuityAxioms.lean`: **PASS, 11 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers the exact
  source linear map, difference laws, uniform probability estimates, Cauchy control
  and nonzero-limit convergence, with initial-value/self-subtraction regressions.
- `Audit/SemimartingaleFirstExitAxioms.lean`: **PASS, 17 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers open
  hitting, closure membership, the usual AE-path version and norm bounds, plus
  boundary/overshoot and the source II.10 missing-first-interval regressions.
- `Audit/SemimartingaleIntegralProcessAxioms.lean`: **PASS, 27 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers the
  source process definition/identities, adaptedness, cadlag regularity, stopping,
  finite stopping values and FV agreement, with closed/open/zero-stop regressions.
- `Audit/SemimartingaleMaximalAxioms.lean`: **PASS, 8 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers first-exit
  event reduction, total/ordinary maximal bounds, the canonical UCP event criterion
  and uniform-input UCP convergence, with the nonempty zero-horizon event regression.
- `Audit/SemimartingaleUCPContinuityAxioms.lean`: **PASS, 22 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers left-hit
  detection/bounds, initial masks, actual bounded truncations, full Protter II.11
  continuity and UCP-Cauchy control, with isolated-initial/right-jump regressions.
- `Audit/SemimartingaleRightLimitAxioms.lean`: **PASS, 16 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers actual
  right limits, cadlag/adapted bridges, source initial reconstruction and finite/extended
  nonaccumulation, with regressions separating an initial spike from its right limit.
- Corrected source-density increment: **PASS**, targeted 8911-job dependency
  build; the four new production modules and updated semantic regression have
  zero warning/error entries in their final Lake traces after line-length cleanup.
- `Audit/SemimartingaleDensityAxioms.lean`: **PASS, 21 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers actual
  oscillation stopping times, nonaccumulation, finite capped partitions, the
  pathwise approximation bound and Protter II.10 UCP density, including the
  actual corrected construction's constant-process first-interval regression.
- Sequential UCP-completeness increment: **PASS**, targeted 8916-job dependency
  build. Five new production modules and the semantic regression have zero
  warning/error entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleUCPCompletionAxioms.lean`: **PASS, 10 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers uniform
  limit existence, cadlag closure, geometric uniform Cauchy control, UCP-Cauchy
  subsequence extraction, actual adapted cadlag limits and nonzero-constant retention.
- Chapter II integral-extension increment: **PASS**, targeted 8923-job dependency
  build. Seven new production modules and the semantic regression have zero
  warning/error entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralExtensionAxioms.lean`: **PASS, 25 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers UCP
  algebra/diagonals, actual integral construction, arbitrary-approximation uniqueness,
  legal-domain selection, regularity, proof irrelevance, linearity, full-domain UCP
  continuity and initial values, with closed-interval and isolated-initial regressions.
- General-integral FV/invariance increment: **PASS**, targeted 8926-job dependency
  build. Three new production modules and the semantic regression have zero
  warning/error entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralFVAxioms.lean`: **PASS, 6 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers source
  and general integrator invariance, everywhere/common-event FV agreement and
  the continuous-FV general self-integral regression with its initial square.
- General-integral stopping increment: **PASS**, targeted 8929-job dependency
  build. Three new production modules and the semantic regression have zero
  warning/error entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralStoppingAxioms.lean`: **PASS, 9 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers common-event
  cutoff regularity/invariance, UCP stopping/cutoff and all three Protter II.12
  general-integral identities, including zero- and infinite-stopping regressions.
- General-integral jump increment: **PASS**, targeted 8934-job dependency build.
  Five new production modules and the semantic regression have zero warning/error
  entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralJumpAxioms.lean`: **PASS, 9 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers uniform
  limit-value control, source left limits, finite stopped-path limits, elementary
  and general jump identities (II.13), with right-endpoint and time-zero regressions.
- Absolute-continuity increment: **PASS**, targeted 8937-job dependency build.
  Three new production modules and the semantic regression have zero warning/error
  entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralACAxioms.lean`: **PASS, 5 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers finite-target
  absolute continuity for arbitrary event probabilities, UCP transfer and II.14,
  including the target-completeness and nonzero-initial-value regressions.
- Mixture/filtration-invariance increment: **PASS**, targeted 8943-job dependency build.
  Six new production modules and the semantic regression have zero warning/error
  entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralInvarianceAxioms.lean`: **PASS, 14 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers intersection
  adaptedness/usualness, unchanged source integral transport, II.16, probability
  mixtures and domination, derived usualness, II.15 and the two-probability corollary.
  Regressions exclude zero-weight domination and check the source initial product.
- Whole-path locality increment: **PASS**, targeted 8950-job dependency build.
  Seven new production modules, the strengthened density owner and the semantic
  regression have zero warning/error entries in their final Lake traces. All affected
  canonical-integral dependencies rebuilt successfully; no whole-library build was run.
- `Audit/SemimartingaleIntegralLocalityAxioms.lean`: **PASS, 22 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers individual-path
  Stieltjes agreement, zero-path-preserving density, source pathwise locality, cadlag/caglad
  subtraction, integral subtraction and both whole-path assertions of II.18. Regressions
  use arbitrary selected events, with no full-probability or initial-measurability premise.
- Integrator-algebra increment: **PASS**, targeted 8953-job dependency build.
  Three new production modules and the semantic regression have zero warning/error
  entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralIntegratorAlgebraAxioms.lean`: **PASS, 15 selected declarations**,
  all output declarations checked against the standard three-axiom set. Covers source
  negation/subtraction stability, elementary integrator algebra and general-integral
  addition/scaling/subtraction. Regressions check uncentered initial-value addition
  and exact initial cancellation for a difference of two arbitrarily stopped integrators.
- Stopping-interval path-agreement increment: **PASS**, targeted 8956-job dependency build.
  Three new production modules and the semantic regression have zero warning/error
  entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralIntervalAxioms.lean`: **PASS, 10 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers endpoint
  recovery from right continuity, pathwise cutoff/stopped differences, general
  stopped-difference identities and stochastic-interval integral locality. Regressions
  allow distinct initial integrand values and exhibit failure of endpoint recovery
  for a deliberately non-right-continuous initial-spike path.
- Stopping-interval FV increment: **PASS**, targeted 8958-job dependency build.
  Two new production modules and the semantic regression have zero warning/error
  entries in their final Lake traces. No whole-library build was run.
- `Audit/SemimartingaleIntegralIntervalFVAxioms.lean`: **PASS, 8 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers open-to-closed
  BV extension with the endpoint jump, clamped/centered stopped-increment variation,
  infinite-upper-end local variation and both finite/general interval Stieltjes identities.
  Regressions retain a unit right-endpoint jump and the unbounded-horizon linear path.
- Associativity/preservation increment: **PASS**, targeted 8969-job dependency build.
  Eleven new production modules, the modified UCP convergence module and the
  semantic regression have zero warning/error entries in final Lake traces.
  Protter II.19 and its FV remark are proved without a decomposition or initial
  integrability premise. Regressions retain the triple initial product, detect
  an isolated initial spike and preserve FV on an arbitrary path event.
  No whole-library build was run.
- `Audit/SemimartingaleIntegralAssociativityAxioms.lean`: **PASS, 27 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers the
  elementary cell/associativity formulas, fixed-simple integrator continuity,
  left-continuous deviations and bounded multipliers, the derived general
  semimartingale/associativity/FV preservation results, and three regressions.
- Bounded-integrand L2 increment: **PASS**, targeted 8977-job dependency build.
  Seven new production modules and the semantic regression have zero warning/error
  entries in final Lake traces. Bounded source integrals are actual martingales;
  bounded caglad integration preserves finite-time L2 martingales, including
  their original initial term. General local L2 preservation is still open.
  No whole-library build was run.
- `Audit/SemimartingaleIntegralBoundedL2Axioms.lean`: **PASS, 19 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers clipping,
  uniform bounded density, conditional weighted increments, square-moment uniform
  integrability, in-measure martingale closure and the constructed integral's L2
  estimate. Regressions retain the initial L2 bound and arbitrary unused coefficients
  on empty source intervals.
- General local L2 increment: **PASS**, targeted 8987-job dependency build.
  Ten new production modules and the semantic regression have zero warning/error
  entries in final Lake traces. Protter II.20 is proved by the minimum of actual
  masked integrand/integrator localizing sequences. No whole-library build was run.
- `Audit/SemimartingaleIntegralLocalL2Axioms.lean`: **PASS, 31 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers the
  everywhere-caglad version, diverging open norm exits, bounded masked cutoffs,
  source/general mask identities, joint stopping, finite-time L2 stability and the
  derived local L2 result. Regressions distinguish zero/positive lifetimes and
  permit arbitrary finite initial random values with no initial L1/L2 premise.
- Continuous-integrand Riemann increment: **PASS**, targeted 8994-job dependency build.
  Seven new production modules and the semantic regression have zero warning/error
  entries in final Lake traces. Random left sampling and the increment-only limit
  are proved for continuous adapted integrands, including the source left-limit
  normalization. This increment covered only the continuous case; the subsequent
  general Riemann increment closes cadlag/caglad II.21. No whole-library build was run.
- `Audit/SemimartingaleIntegralContinuousRiemannAxioms.lean`: **PASS, 23 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers AE
  left-continuous stopping values, varying-horizon left steps, source sample
  representations, partition-uniform deviation contraction, actual continuous
  Riemann convergence and the initial-product correction. Regressions cover
  arbitrary constant integrators and a unit jump strictly inside a partition cell.
- General Riemann increment: **PASS**, targeted 9016-job dependency build.
  Twenty-two new production modules and the semantic regression have zero
  warning/error entries in final Lake traces. Full cadlag/caglad II.21 is proved
  for random partitions tending to the identity, with the original initial
  correction and source-left-limit convention. No whole-library build was run.
- `Audit/SemimartingaleIntegralGeneralRiemannAxioms.lean`: **PASS, 57 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Covers
  ordinary/strict endpoint projections, actual jump displacement, initial-spike
  sums, right-limit UCP continuity, sequential uniform error control and both
  general Riemann theorems. Regressions distinguish strict projection at zero,
  retain the exact initial-cell term and exclude any initial integrability premise.
- Raw QV increment: **PASS**, targeted 9026-job dependency build.
  Ten new production modules and the semantic regression have zero warning/error
  entries in final Lake traces. The raw square bracket, its source initial value,
  jump-square formula, UCP square sums, all-times increasing/FV paths and self-stopping
  identity are proved. Mixed covariation and mixed stopping remain open.
  No whole-library build was run.
- `Audit/SemimartingaleRawQuadraticVariationAxioms.lean`: **PASS, 29 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Includes the
  completed-cell monotonicity argument for discontinuous paths, measurable
  endpoint exhaustion, actual partition-sum stopping and raw initial-square regressions.
- Mixed covariation increment: **PASS**, targeted 9039-job dependency build.
  Thirteen new production modules and the semantic regression have zero warning/error
  entries in final Lake traces. II.22--II.23's polarized owner, mixed-sum UCP limits,
  bilinearity, jumps, integration by parts, semimartingale products and stopping
  in both or either argument are proved. The interval Cauchy--Schwarz estimate
  is proved on a common all-times event; full weighted II.24--II.25 remains open.
  No whole-library build was run.
- `Audit/SemimartingaleMixedCovariationAxioms.lean`: **PASS, 41 selected declarations**,
  exact count and standard three-axiom sets checked automatically. Regressions
  retain constant/zero-stopped initial products and refute exact single-argument
  stopping of a finite mixed sum when the stopping time is inside a cell.
- Targeted `SemanticRegression` dependency build: **PASS, 9053 jobs** for the
  weighted Kunita--Watanabe increment (14 new production modules). The final
  traces of all 14 modules and the regression module have zero warnings/errors.
  The pathwise II.24--II.25 inequality includes arbitrary measurable weights,
  infinite energies, both absolute-continuity conclusions and explicit initial
  atoms. Its expectation/Lp corollary remains open. No whole-library build ran.
- `Audit/SemimartingaleKunitaWatanabeAxioms.lean`: **PASS, 27 selected declarations**,
  exact count checked automatically; only `propext`, `Classical.choice` and
  `Quot.sound`. Regressions include zero energy against possibly infinite energy
  and the zero mass of the increment Stieltjes measure at time zero.
- Targeted `SemanticRegression` dependency build: **PASS, 9060 jobs** for the
  expectation/Lp corollary (seven new production modules). All seven production
  traces and the regression trace have zero warnings/errors. Finite conjugate
  exponents and both endpoints use proved measurable random energies with the
  original initial atoms, and are invariant under null-event realization choices.
  No whole-library build ran.
- `Audit/SemimartingaleKunitaWatanabeExpectationAxioms.lean`: **PASS, 25 selected
  declarations**, exact count checked; only the standard three axioms. The new
  regressions cover a zero expected energy against possibly infinite partner
  energy and preservation of the initial square without an integrability premise.
- Targeted `SemanticRegression` dependency build: **PASS, 9064 jobs** for the
  deterministic Stieltjes continuous/jump decomposition (four new production
  modules). The four production traces and the regression trace have zero
  warnings/errors after a line-length cleanup. No whole-library build ran.
- `Audit/SemimartingaleStieltjesPartsAxioms.lean`: **PASS, 33 selected declarations**,
  exact count checked, only the standard three axioms. The actual positive-time
  jump series is summable; continuous paths have no jump part, and a nonzero
  constant initial value is not inserted into either zero-starting component.
  The stochastic continuous-bracket interface remains open.
- Targeted `SemanticRegression` dependency build: **PASS, 9070 jobs** for the
  raw square bracket's continuous component (six new production modules).
  All six final production traces and the regression trace have zero
  warnings/errors. No whole-library build ran.
- `Audit/SemimartingaleContinuousQVAxioms.lean`: **PASS, 22 selected declarations**,
  exact count checked; only the standard three axioms. Adaptedness is derived
  from finite-time restriction, and the common-event decomposition retains
  the original initial square and proves the positive-time squared-jump series
  summable. Regressions check the distinct raw/continuous initial conventions
  and the empty real-time jump interval at zero. Mixed continuous covariation
  and the remaining stopping identities remain open at this checkpoint.
- Targeted `SemanticRegression` dependency build: **PASS, 9073 jobs** for mixed
  continuous covariation (three new production modules). All three final
  production traces and the regression trace have zero warnings/errors.
  No whole-library build ran.
- `Audit/SemimartingaleContinuousCovariationAxioms.lean`: **PASS, 20 selected
  declarations**, exact count checked, only the standard three axioms. The
  actual mixed-jump series is absolutely summable, and continuous covariation
  is adapted, continuous, FV, symmetric and bilinear with the correct diagonal
  and version invariance. Regressions retain the separate raw initial product
  and zero continuous initial value. Continuous-part stopping was still open
  at that checkpoint and is closed in the following increment.
- Targeted `SemanticRegression` dependency build: **PASS, 9080 jobs** for
  continuous-part stopping (seven new production modules). All seven final
  production traces and the regression trace have zero warnings/errors.
  No whole-library build ran.
- `Audit/SemimartingaleContinuousStoppingAxioms.lean`: **PASS, 17 selected
  declarations**, exact count checked, only the standard three axioms. Closed
  Stieltjes restriction and the exact jump cutoff prove continuous square,
  simultaneous mixed and one-sided mixed stopping. Regressions check the
  retained endpoint jump, zero continuous part under one-sided zero stopping,
  and preservation under infinite stopping without an infinity evaluation.
- Targeted `SemanticRegression` dependency build: **PASS, 9084 jobs** for
  Protter II.30 (four new production modules). All four final production traces
  and the regression trace have zero warnings/errors. No whole-library build ran.
- `Audit/SemimartingaleWeightedCrossAxioms.lean`: **PASS, 11 selected declarations**,
  exact count checked, only the standard three axioms. Regressions check a moving
  partial cell and the zero initial values of both the weighted increment sums
  and their actual stochastic-integral limit. The constant unit-weight formula
  explicitly subtracts the raw bracket's initial product.
- Targeted `SemanticRegression` dependency build: **PASS, 9095 jobs** for
  Protter II.29 (eleven new production modules). All eleven final production
  traces and the regression trace have zero warnings/errors. No whole-library
  build ran.
- `Audit/SemimartingaleIntegralBracketAxioms.lean`: **PASS, 27 selected declarations**,
  exact count checked, only the standard three axioms. Actual simple mixed-sum
  limits and UCP extension identify both-integral and square bracket formulas.
  Regressions retain the full initial product and square and remove positive-time
  coefficients for a constant integrator. II.26--II.28 were still open at this gate.
- Targeted `SemanticRegression` dependency build: **PASS, 9103 jobs** for
  Protter II.27's main theorem (eight new production modules). All eight final
  production traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleContinuousLocalBracketAxioms.lean`: **PASS, 18 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`. Regressions
  retain the nonzero source jump at time zero for a continuous path, the initial
  square for an arbitrary measurable constant, and the zero compensated initial
  value. II.27's corollaries, II.26 and II.28 were still open at this gate.
- Targeted `SemanticRegression` dependency build: **PASS, 9114 jobs** for
  II.27 Corollaries 1--2 and the continuous-FV special case (eleven new production
  modules). All eleven final production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleLocalBracketCorollaryAxioms.lean`: **PASS, 25 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`. Regressions
  check the nonconstant path `t+1` with raw QV `1`, complete raw-bracket
  cancellation for equal stopping endpoints, and the zero-to-infinity interval
  without infinite-time evaluation. Corollaries 3--5, general II.26 and II.28
  were still open at this gate.
- Targeted `SemanticRegression` dependency build: **PASS, 9123 jobs** for
  general Protter II.26 (nine new production modules). All nine final production
  traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleFiniteVariationBracketAxioms.lean`: **PASS, 38 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`. Regressions
  distinguish left/right sampling at a jump, retain its square, exclude the
  initial square from the positive-time series, and exhibit a nonconstant
  continuous drift which is quadratic pure jump. II.28, the moment corollaries
  and the single-event all-intervals constancy result were still open at this gate.
- Targeted `SemanticRegression` dependency build: **PASS, 9127 jobs** for
  Protter II.28 (four new production modules). All four final production
  traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingalePureJumpMixedAxioms.lean`: **PASS, 22 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`. Regressions
  require both integer coefficient directions, retain the raw initial mixed
  product, and test nonconstant continuous drift against an arbitrary
  semimartingale. The moment corollaries, single-event all-intervals result
  and discontinuous-FV C1 formula were still open at this gate.
- Targeted `SemanticRegression` dependency build: **PASS, 9136 jobs** for
  Protter II.31 (nine new production modules), repeated after line-wrap cleanup.
  All nine final production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleCadlagFVC1Axioms.lean`: **PASS, 44 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. The actual path jumping
  from 1 to 3 has square change 8, derivative integral 4, and jump correction 4.
  Additional regressions test the derivative-filled diagonal and the source
  zero-time left-limit argument. General semimartingale Ito is still open.
- Targeted `SemanticRegression` dependency build: **PASS, 9147 jobs** for
  the continuous case of Protter II.32 (eleven new production modules).
  All eleven production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleContinuousItoAxioms.lean`: **PASS, 29 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Regressions retain the nonzero diagonal Taylor coefficient and the
  actual cubic jump remainder 8, and expose C2 preservation without
  initial moments or global derivative bounds. The general jump formula,
  multidimensional extension and remaining package gates are still open.
- Targeted `SemanticRegression` dependency build: **PASS, 9163 jobs** for
  the general cadlag raw-bracket Ito identity and C2 semimartingale preservation
  (sixteen new production modules). All sixteen production traces and the
  regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleCadlagItoAxioms.lean`: **PASS, 29 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. The actual jump corrections
  are absolutely summable and locally FV. Regressions keep the initial value
  outside the positive-time jump series and impose no initial moments or global
  derivative bounds. Conversion to the continuous-component source form,
  multidimensional Ito and the remaining package gates are still open.
- Targeted `SemanticRegression` dependency build: **PASS, 9170 jobs** for
  the continuous-bracket form of general cadlag Ito (seven new production
  modules). All seven production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleContinuousBracketItoAxioms.lean`: **PASS, 21 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  New regressions retain the raw integral's initial square, show why arbitrary
  continuous composition of source left limits excludes zero, and keep a
  nonzero constant Stieltjes initial integral outside its zero increment
  measure. This checkpoint closes II.32; II.33 is closed in the later increment below.
- Targeted `SemanticRegression` dependency build: **PASS, 9172 jobs** for
  the vector Taylor foundation (two new and three generalized production
  modules). All five production traces, seven affected scalar Ito dependency
  traces, and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleVectorTaylorAxioms.lean`: **PASS, 16 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. Vector regressions check
  a diagonal-zero coefficient despite a nonzero Hessian and a genuine
  nonzero cubic jump remainder in a two-coordinate ambient space. This is
  an analytic prerequisite increment; II.33 was still open at that checkpoint.
- Targeted `SemanticRegression` dependency build: **PASS, 9182 jobs** for
  vector partition limits and actual jump series (ten new and two generalized
  production modules). All twelve production traces, twenty affected scalar
  dependency traces, and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleVectorPartitionAxioms.lean`: **PASS, 36 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. Regressions distinguish
  the vector sup-norm energy from the sum of coordinate squares and retain
  the actual cubic error in a partial terminal cell. Common-event absolute
  jump-correction summability is proved for coordinate semimartingales;
  the full II.33 stochastic integral identity was still open at that checkpoint.
- Targeted `SemanticRegression` dependency build: **PASS, 9195 jobs** for
  the finite-dimensional Ito increment (thirteen new production modules).
  All thirteen production traces and the regression trace contain
  **0 warnings/errors** after style cleanup.
- `Audit/SemimartingaleVectorItoAxioms.lean`: **PASS, 23 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. Regressions cover the
  empty coordinate family, ordered off-diagonal Hessian terms and the raw
  mixed integral's initial product. II.33's raw and continuous formulas and
  C2 preservation are closed; subsequent package gates remain open.
- Targeted `SemanticRegression` dependency build: **PASS, 9203 jobs** for
  the Fisk--Stratonovich increment (eight new production modules). All eight
  production traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleFiskStratonovichAxioms.lean`: **PASS, 19 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Regressions show the spurious initial term caused by a raw-bracket
  Stratonovich correction and the nonzero first-order jump correction of
  a quadratic function. II.34 and its corollary are closed; II.35--II.36
  and the remaining package gates are still open.
- Targeted `SemanticRegression` dependency build: **PASS, 9212 jobs** for
  the complex coordinate foundation (nine new production modules). All nine
  production traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleComplexFoundationAxioms.lean`: **PASS, 35 selected
  declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Regressions verify the source complex left limit at zero and the actual
  imaginary-imaginary/mixed Hessian signs of z squared. Complex path,
  integration and analytic-preservation prerequisites are proved; neither
  II.35 nor II.36 is closed by this checkpoint.
- Targeted `SemanticRegression` dependency build: **PASS, 9227 jobs** for
  the complex Ito increment (15 new production modules). All 15 production
  traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleComplexItoAxioms.lean`: **PASS, 44 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. Regressions separate the
  constant-I bilinear bracket (-1) from its energy (1), retain the negative
  analytic correction of an imaginary jump, and verify the raw complex
  bracket integral's initial product. II.35--II.36 are closed. No full-library
  build or GitHub push was run; stochastic exponential and later gates remain open.
- Targeted `SemanticRegression` dependency build: **PASS, 9236 jobs** for
  the stochastic-exponential product/continuous-existence foundation (nine
  new production modules). All nine production traces and the regression
  trace contain **0 warnings/errors**.
- `Audit/SemimartingaleStochasticExponentialFoundationAxioms.lean`: **PASS,
  34 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Regressions distinguish an initial -1 value from a positive-time -1 jump,
  retain the negative multiplier of a -2 jump, and verify absorption after
  an actual -1 jump. General cadlag regularity/adaptedness, its equation and
  uniqueness remain open; II.37 is not closed. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9250 jobs** for
  general stochastic-exponential product paths and pure-jump variation
  (fourteen new production modules). All fourteen production traces and
  the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleStochasticExponentialProductPathAxioms.lean`: **PASS,
  35 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  The three regressions protect the positive-time jump boundary, the full
  jump sum after a zero factor, and repeated activation times. General
  cadlag regularity, finite variation of the product factor, and its actual
  pure-jump identity are proved. Adaptedness, the jump-case integral equation
  and uniqueness remain open; II.37 is not closed. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9260 jobs** for
  random atomic-series measurability, the zero-guarded complex-log product
  representation, and general adaptedness/semimartingale preservation
  (ten new production modules). All ten production traces and the regression
  trace contain **0 warnings/errors**.
- `Audit/SemimartingaleStochasticExponentialAdaptedAxioms.lean`: **PASS,
  23 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Two regressions show why the complex logarithm requires a zero guard and
  that it preserves a negative jump multiplier. The finite-horizon kernel
  argument uses only past coordinates and a common initial null set.
  General adaptedness and semimartingale preservation are proved. The
  jump-case integral equation and uniqueness remain open; II.37 is not closed.
  No full-library build or GitHub push was run.
- Targeted `SemanticRegression` dependency build: **PASS, 9266 jobs** for
  the general stochastic-exponential integral equation (six new production
  modules). All six production traces and the regression trace contain
  **0 warnings/errors**. The proof uses the actual pure-jump FV integral
  formula, full two-coordinate exponential-product Hessian, canonical
  bracket drift invariance and integral algebra.
- `Audit/SemimartingaleStochasticExponentialEquationAxioms.lean`: **PASS,
  16 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Two regressions retain mixed Hessian entries at a zero product factor
  and verify the zero initial integral with unrestricted random initial
  values. The general jump-case equation is proved. Uniqueness and later
  applications remain open; II.37 is not closed. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9270 jobs** for
  Protter II.38, canonical exponential version invariance and the continuous
  inverse (four new production modules plus the FV drift-algebra extension).
  All five production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleStochasticExponentialMultiplicationAxioms.lean`: **PASS,
  11 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Three regressions protect the nonzero raw initial product, absorbing
  simultaneous jumps, and the raw-inverse initial guard. II.38 is proved
  independently of stochastic-equation uniqueness; II.37 uniqueness and
  Levy/later applications remain open. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9280 jobs** for
  characteristic-exponential equations, complex local martingales and
  compact-envelope promotion (ten new production modules). All ten production
  traces and the regression trace contain **0 warnings/errors**.
- `Audit/SemimartingaleCharacteristicExponentialAxioms.lean`: **PASS,
  24 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  Three regressions protect the initial phase norm, positive compensation
  and zero frequency. The bracket-equals-time exponential is a true complex
  martingale. Conditional characteristic functions, Gaussian increment laws
  and independence remain open at this checkpoint; Levy's theorem is not
  yet closed. No full-library build or GitHub push was run.
- Targeted `SemanticRegression` dependency build: **PASS, 9291 jobs** for
  Protter II.39, the real filtered Levy equivalence (eleven new production
  modules). All eleven production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleLevyRealAxioms.lean`: **PASS, 26 selected declarations**,
  only `propext`, `Classical.choice`, `Quot.sound`. Three regressions cover
  zero-length increments, the nonzero-initial obstruction, and failure of
  Brownian martingales in the full-information filtration. The proof derives
  Gaussian laws and independence from conditional characteristic functions;
  the reverse direction identifies the existing raw bracket using FV
  local-martingale uniqueness. II.39 is closed, but II.37 uniqueness, II.40,
  later applications and general usual-filtration transport remain open.
  No full-library build or GitHub push was run.
- Targeted `SemanticRegression` dependency build: **PASS, 9299 jobs** for
  deterministic brackets and finite orthogonal projections (eight new
  production modules plus a wrapper around the unchanged finite-sum owner).
  All nine production traces and the regression trace contain
  **0 warnings/errors**.
- `Audit/SemimartingaleLevyProjectionAxioms.lean`: **PASS,
  27 selected declarations**, only `propext`, `Classical.choice`, `Quot.sound`.
  This includes the retained original finite-sum interface and regressions for
  flat-clock Dirac increments, empty projections and repeated-coordinate cross
  terms. The projection laws are proved; joint vector laws and entire-process
  independence are still open. II.40 is not closed. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9305 jobs** for
  Protter II.40 (six new production modules, two generalized existing modules
  and the regression module). The final interfaces use `Finite` where an
  enumeration is unnecessary. All **nine** affected module traces have
  **zero warning/error entries** after rebuilding those interfaces.
- `Audit/SemimartingaleLevyVectorAxioms.lean`: **PASS, 24 selected declarations**,
  each using only `propext`, `Classical.choice`, and `Quot.sound`. Regressions
  cover the zero-length joint increment, the empty vector's normalized
  characteristic function, and coordinate independence at independently
  chosen times. The joint law and entire-process independence are proved,
  closing II.40. II.37 uniqueness, II.41--II.43 and the remaining package gates
  stay open. No full-library build or push was attempted.
- Targeted `SemanticRegression` dependency build: **PASS, 9315 jobs** for the
  full-space harmonic core and the subharmonic source counterexample (ten new
  production modules and the expanded regression module). All **11 affected
  final Lake traces contain zero warnings/errors**.
- `Audit/SemimartingaleHarmonicCoreAxioms.lean`: **PASS, 20 selected declarations**,
  all using only `propext`, `Classical.choice`, and `Quot.sound`.
- Regressions retain the finite-integral initial product, the empty-coordinate
  trace-zero case, and the smooth positive-Laplacian Brownian counterexample.
  II.41 remains partial: open-domain localization and the corrected positive
  direction are still open. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9321 jobs** for the
  corrected full-space subharmonic theorem (six new production modules and
  the expanded regression module). All **seven affected final Lake traces
  contain zero warnings/errors**.
- `Audit/SemimartingaleSubharmonicAxioms.lean`: **PASS, 16 selected declarations**,
  all using only `propext`, `Classical.choice`, and `Quot.sound`.
- The actual increasing Ito drift, masked local-submartingale witnesses and
  integrable-envelope promotion are proved. Regressions test empty coordinates,
  legal nonintegrable masked initial values versus illegal true submartingales,
  and an increasing Stieltjes integral with a negative initial product.
  General open-domain II.41 remains open. No full-library build or push.
- Targeted `SemanticRegression` dependency build: **PASS, 9332 jobs** for
  open-domain harmonic and corrected classical C2 subharmonic composition
  (eleven new production modules, the centered raw-clock bridge, public
  regression export and two documentation-only source-header updates).
  All **15 affected module traces** contain zero warnings/errors.
- `Audit/SemimartingaleOpenDomainAxioms.lean`: **PASS, 29 selected declarations**,
  each using only `propext`, `Classical.choice`, and `Quot.sound`.
  Four regressions verify Laplacian transport through the genuine extension,
  the zero-exit domain basepoint, dimension zero and a raw clock initially nine.
  The open-domain harmonic and classical C2 local-submartingale statements
  are proved; true promotion retains compact-time integrable envelopes.
  The unstated source smoothness convention/nonsmooth scope remains under
  audit. No full-library build or document-completion push was performed.
- Targeted `SemanticRegression` dependency build: **PASS, 9334 jobs** for
  II.27 Corollary 5's common-event constancy-interval theorem (two new
  production modules and the generalized closed-region endpoint lemma).
  All **seven inspected changed/downstream traces** have zero warnings/errors.
- `Audit/SemimartingaleConstancyIntervalsAxioms.lean`: **PASS, 15 selected
  declarations**, using only `propext`, `Classical.choice`, and `Quot.sound`.
  The theorem covers every order-connected interval on one event, including
  open, half-open and unbounded intervals; raw/continuous bracket endpoint
  equality detects closed-interval constancy. Three regressions verify
  arbitrary non-stopping random endpoints and zero/infinite departure times.
  The moment/terminal corollaries and compensated-Poisson source example
  remain open. No full-library build or document-completion push.
- Targeted `SemanticRegression` dependency build: **PASS, 9338 jobs** for
  the DDS inverse-clock path/stopping foundation (four new production modules
  and four new regressions). After explicit compact bounds and line-length
  cleanup, all **five affected final traces** have zero warnings/errors.
- `Audit/SemimartingaleInverseClockAxioms.lean`: **PASS, 38 selected declarations**,
  using only `propext`, `Classical.choice`, and `Quot.sound`.
  The actual inverse-clock stopping times, finite level identities, continuous
  adapted sampled paths, factorization and raw-inverse comparison are proved.
  Regressions cover identity/delayed/bounded clocks and a nonzero process
  initial value on a flat clock fiber. The Brownian-law conclusion remains
  open at that checkpoint. No full-library build or document-completion push.
- Targeted `SemanticRegression` dependency build: **PASS, 9346 jobs** for
  the DDS Brownian-law and exact raw-filtration extension (eight new production
  modules and three new regressions). All **ten affected final traces** have
  zero warnings/errors.
- `Audit/SemimartingaleDDSAxioms.lean`: **PASS, 16 selected declarations**,
  covering all new public theorems and regressions, with only `propext`,
  `Classical.choice`, and `Quot.sound`. No admissions, custom axioms or new
  external dependency were introduced. Conditional Gaussian laws, full
  sampled-past independence and the actual raw-bracket DDS statement are proved.
  Regressions check degenerate increments, the necessary zero start, and
  arbitrary random-time reconstruction. The right-continuation remark and
  II.43 remain open. No full-library build or document-completion push.
- Targeted `SemanticRegression` dependency build: **PASS, 9350 jobs** for
  the Levy-area integral/bracket/Riccati foundation (four new production
  modules and three new regressions). All **five affected final traces**
  have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaFoundationAxioms.lean`: **PASS, 35 declarations**,
  covering all new public definitions, theorems and regressions, using only
  `propext`, `Classical.choice`, and `Quot.sound`. The area is the actual
  antisymmetric source integral; its brackets are derived, not assumed.
  The explicit Riccati functions satisfy their derivative, terminal and
  sign identities for every real parameter. Regressions check arbitrary
  initial coordinates, parameter sign and the terminal exponent. The
  characteristic function and positive-time density remain open. No
  full-library build or document-completion push.
- Targeted `SemanticRegression` dependency build: **PASS, 9353 jobs** for
  the actual area exponent/exponential and Riccati integral equations (three
  new production modules and three new regressions). All **four affected
  final traces** have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaExponentAxioms.lean`: **PASS, 16 declarations**,
  covering every new public definition, theorem and regression, with only
  `propext`, `Classical.choice`, and `Quot.sound`. The initial/terminal values,
  path/semimartingale properties and clock-level bound concern the constructed
  exponential, not a supplied candidate. Both coefficient equations use the
  existing stochastic integral. Regressions check the zero parameter, zero
  horizon and actual terminal time clock. Full exponential drift cancellation,
  local-martingale identification and the area law remain open. No full-library
  build or document-completion push.
- Squared-radius and continuous FV substitution increment: **PASS, 9356 jobs**
  (three new production modules and two new regressions). All **four affected
  final traces** have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaRadiusAxioms.lean`: **PASS, 7 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The squared-radius
  identity and its integrated form use the actual raw bracket and stochastic
  integral. Constant-integrator and C1 continuous-FV substitution formulas retain
  their initial products; regressions check the nonzero product and vanishing
  area of arbitrary initial random constants. Full area-exponential drift
  cancellation and the area law remain open. No full-library build or push.
- Continuous-FV multiplier and real area-exponent dynamics increment:
  **PASS, 9360 jobs** (four new production modules and two new regressions).
  All **five affected final traces** have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaDynamicsAxioms.lean`: **PASS, 6 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The multiplier,
  weighted-radius, real-exponent and continuous-area identities concern the
  existing integral, not a supplied differential representation. Regressions
  retain the initial `beta(0)` and check the vanishing real terminal exponent.
  The complex bracket and full exponential drift cancellation remain open.
  No full-library build or document-completion push.
- Continuous-FV multiplier, isotropic integral-sum and area-clock bracket
  increment: **PASS, 9364 jobs** (four new production modules and one new
  regression). All **five affected final traces** have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaClockAxioms.lean`: **PASS, 8 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The finite-family
  and two-coordinate formulas concern brackets of the actual integral sums.
  The area energy formula allows nonzero initial coordinates; the regression
  proves zero mixed bracket for rotated arbitrary caglad weights. Explicit
  pointwise multiplication keeps all new declarations within the default
  heartbeat limit. The compensated exponent's complex bracket and the full
  exponential drift cancellation remain open. No full-library build or push.
- Squared-radius and full compensated-area-exponent bracket increment:
  **PASS, 9366 jobs** (two new production modules and two new regressions).
  All **three affected final traces** have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaExponentBracketAxioms.lean`: **PASS, 8 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The actual radius
  and radius/area brackets lead to all exponent coordinate brackets and its
  full complex bilinear bracket `J_Q(R(alpha^2-u^2))`. No differential identity
  for the exponent is assumed. Regressions check zero Fourier parameter and
  the vanishing imaginary bracket, without confusing the bilinear bracket
  with nonnegative energy. Full exponential Ito cancellation, local-martingale
  identification and the law remain open. No full-library build or push.
- Complex-integral calculus increment: **PASS, 9370 jobs** (four new production
  modules and two new regressions). All **five affected final traces** have
  zero warnings/errors.
- `Audit/SemimartingaleComplexIntegralCalculusAxioms.lean`: **PASS, 10 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. Constant-integrator
  initial products, both version-invariance directions, real-integrator reduction
  and real-inner-integral associativity use the existing real coordinate owners.
  Continuous-LM preservation derives local L2 internally. Regressions verify
  the complex initial product `21+14i` and real-integrator embedding with an
  arbitrary initial integrand. The area-exponential Ito cancellation and law
  remain open. No full-library build or document-completion push.
- Levy-area exponential and characteristic-function increment: **PASS, 9380 jobs**
  (nine new production modules, one extended complex-invariance module and
  three new regressions). All **11 affected final traces** have zero warnings/errors.
- `Audit/SemimartingaleLevyAreaCharacteristicAxioms.lean`: **PASS, 16 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The actual complex
  integral equation cancels the FV drift; the proved local martingale becomes
  a bounded stopped true martingale, giving the inverse-cosh characteristic
  function. Standard-clock and canonical independent-Brownian interfaces derive
  their auxiliary clock/bracket conditions. Filtration-past independence stays
  explicit. Regressions check zero parameter, time-zero characteristic function
  and the actual time-zero Dirac law. The positive-time density and package
  completion remain open. No full-library build or document-completion push.
- Levy-area density increment: **PASS, 9383 jobs** (three new production
  modules, the extended Brownian interface and three new regressions).
  All **five affected final traces** have zero warnings/errors after correcting
  one long line and rebuilding its dependent modules.
- `Audit/SemimartingaleLevyAreaDensityAxioms.lean`: **PASS, 27 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The sigmoid/Beta/Gamma
  proof supplies the actual Fourier integral and its scaled integrability;
  normalization constructs the probability measure, and Fourier uniqueness
  identifies the actual area law and positive-time density. The zero-density
  versus Dirac regression enforces the time-zero boundary; other regressions
  check the normalization at the origin and negative Fourier parameters.
  II.43 and its corollary are closed. The package remains open. No full-library
  build or document-completion push.
- Compensated-Poisson martingale increment: **PASS, 9386 jobs** (two new
  production modules and two regressions). All **three affected final traces**
  have zero warnings/errors. The first moments include zero rate and reversed
  real increments; the actual compensated process has proved true/local
  martingale, cadlag/FV and semimartingale properties.
- `Audit/SemimartingaleCompensatedPoissonMartingaleAxioms.lean`: **PASS,
  14 declarations**, with only `propext`, `Classical.choice`, and `Quot.sound`.
  The canonical bracket and constancy-interval example remain open.
  No full-library build or document-completion push.
- Poisson raw-bracket/constancy increment: **PASS, 9390 jobs** (four new
  production modules and three regressions). All **five affected final traces**
  have zero warnings/errors. The actual count and compensated count have raw
  bracket `N`; all vanishing meshes are covered, with no assumed unit jumps.
- `Audit/SemimartingalePoissonBracketAxioms.lean`: **PASS, 22 declarations**,
  using only `propext`, `Classical.choice`, and `Quot.sound`. Regressions check
  the second-moment linear term, zero rate and the deterministic drift's
  nonconstancy. The common-event flat-bracket intervals close the source
  counterexample after II.27 Corollary 5; a final theorem formally rules out
  continuous-local-martingale status. No full-library build or document-completion push.
- DDS right-continuation increment: **PASS, 9392 jobs** (two new production
  modules and one regression). All **three affected final traces** have zero
  warnings/errors.
- `Audit/SemimartingaleDDSRightContAxioms.lean`: **PASS, 3 declarations**, with
  only `propext`, `Classical.choice`, and `Quot.sound`. Bounded continuous tests
  pass future-increment independence to the right-continuation past, retaining
  equal endpoints. The DDS theorem keeps its actual raw-clock inverse and
  Brownian process in a usual `G_+`, with reconstruction and clock stopping.
  This closes the auxiliary right-continuation step, without asserting `G = G_+`.
  No full-library build or document-completion push.
- Brownian usual-augmentation increment: **PASS, 9396 jobs** (three new production
  modules and two regressions). All **four affected final traces** have zero
  warnings/errors.
- `Audit/SemimartingaleBrownianAugmentationAxioms.lean`: **PASS, 20 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. Laws and independence
  transfer to the genuinely completed measure. Old-event AE representatives
  justify null-set enlargement, and the earlier right-continuation theorem
  preserves future independence. The same Brownian process has true and
  square-minus-time martingale, CLM/semimartingale and canonical time-bracket
  interfaces, including a natural-past entry point. Regressions preserve zero
  start and reject full-information martingales even after completion.
  This closes the Brownian source-filtration augmentation bridge, not the Levy
  path/decomposition or remaining source obligations. No full-library build or push.
- Klenke 21.62 C1 quadratic-variation increment: **PASS, 9399 jobs** (three new
  production modules and three regressions). All **four affected final traces**
  have zero warnings/errors.
- `Audit/SemimartingaleC1QuadraticVariationAxioms.lean`: **PASS, 14 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. Actual finite
  cumulative-mass integration and continuous step approximation identify the
  Stieltjes integral. The C1 differentiated-slope remainder vanishes against
  bounded square sums; the composed path has a continuous increasing
  zero-starting QV limit. Arbitrary initial values, repeated/empty cells and
  initial cumulative mass are covered. This closes 21.62, not the separate
  full-sequence partition-dependence/nonexistence example. No full-library
  build or document-completion push.
- Full-sequence partition-dependence increment: **PASS, 9404 jobs** (five new
  production modules and two regressions). All **six affected final traces**
  have zero warnings/errors after four line-length warnings were corrected.
- `Audit/SemimartingalePartitionDependenceAxioms.lean`: **PASS, 22 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. IVT value-midpoint
  insertion halves square sums while preserving every old endpoint. Iteration,
  common refinements and finite dyadic extensions construct genuine nested
  admissible infinite partitions with zero QV at the prescribed horizon. The
  internally constructed Brownian law supplies a continuous path whose full
  dyadic sequence has QV one at horizon one. A uniform probability-one event
  for all admissible sequences is disproved. Regressions retain unbounded
  global endpoints at horizon zero and rule out mere re-enumeration of the
  dyadic endpoints. The separate nested-sequence nonconvergence example remains
  open. No full-library build or document-completion push.
- Nested-sequence QV nonconvergence increment: **PASS, 9407 jobs** (three new
  production modules and two regressions). All **four affected final traces**
  have zero warnings/errors.
- `Audit/SemimartingalePartitionNonconvergenceAxioms.lean`: **PASS, 11 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. Exact insertion
  product errors vanish by continuity and mesh convergence. Fixed finite
  insertions and common refinement preserve the QV limit. Alternating high
  and low refinements keep all prior endpoints and dyadic mesh control;
  the resulting global nested admissible sequence has even square sums below
  `1/4` and odd square sums above `3/4`, so no real limit exists. Existing
  endpoints contribute zero insertion error, and the example is proved not
  to have bounded variation. This closes the remaining deterministic
  Klenke 21.56--21.63 construction gates. The Semimartingale package remains
  in progress. No full-library build or document-completion push.
- New regressions verify the nonzero source time-zero jump, zero/infinite-lifetime
  `T-` behavior, strict-past selection at a grid endpoint and source simple-process
  regularity without forbidding repeated endpoints.
- All seven new continuous bounded-localization modules have zero warning/error
  entries in their final Lake traces. The previous twelve stopping/closure/localization
  modules passed the same check. The moved Brownian StrongMarkov module retains
  four pre-existing style/unused-variable warnings; no new warning was introduced there.
- The integration-prerequisite and reflection/strong-QV module traces have zero
  warning/error entries after style cleanup, as does the updated future-sigma-field module.
- All ten new all-times/infinite-variation module traces also have zero warning/error entries.
- All ten new L2-example/localization modules and the three modified Lean modules
  have zero warning/error entries in their final Lake traces. Regressions cover an
  arbitrary coefficient on a zero-length interval and the absence of an unmasked
  initial-integrability premise in the CLM-to-semimartingale theorem.
- New Lean source scan: no proof holes, admissions, custom axioms or unsafe
  declarations. `git diff --check` passed.
- Sole direct Lake requirement: Mathlib v4.33.0, resolved to
  `db584cd6d46c92f209a44c0f1c829460d327499d`, with its existing support dependencies.
  The manifest is unchanged and no external stochastic-library import was added.
- Build settings: `--memory=24000`, `--threads=3`, `LEAN_NUM_THREADS=3`.
  Process-memory samples remained below the 24 GB aggregate budget; this
  observation is not a claim that Lean's per-process memory flag enforces an OS
  job-wide ceiling.

These checks certify the implemented foundation, not the open mathematics.
No document-completion GitHub push was attempted: the user's whole-document
publication gate has not passed.

- Continuous-time Doob increment: **PASS, 9410 jobs** (two production modules
  plus regression export); all three final module traces have zero warnings
  and errors after line-length cleanup.
- `Audit/SemimartingaleContinuousDoobAxioms.lean`: **PASS, 12 declarations**,
  depending only on `propext`, `Classical.choice`, and `Quot.sound`. The finite
  sampling and dense-grid bounds, actual finite L2 envelope, initial and
  terminal cases, and common-event arbitrary-time selection are checked.
  This remains an incremental prerequisite checkpoint, not whole-package
  completion. No full-library build or document-completion push.

- True-L2 raw bracket moment increment: **PASS, 9411 jobs** (one new production
  module and updated regression export); both final traces have zero warnings
  and errors.
- `Audit/SemimartingaleQuadraticVariationMomentsAxioms.lean`: **PASS, 4 declarations**,
  with only `propext`, `Classical.choice`, and `Quot.sound`. The actual local
  residual, derived bracket integrability and exact moment identity, nonzero
  constant, and compensated Poisson jump case are checked. This closes the
  forward direction of II.27 Corollary 3 at the stated true-L2 domain; the
  reverse/general-LM direction and infinite-terminal Corollary 4 remain open.
  No full-library build or document-completion push.

## Continuous-time Doob maximal control

The new `Martingale/Inequalities/DoobFiniteTime.lean` sorts arbitrary finite
sampling times and reuses discrete Doob for Banach-valued martingales, retaining
the sharp factor `p/(p-1)` for `p > 1`. `DoobContinuousL2.lean` uses the existing
clipped dense-grid supremum, not a competing real-valued owner. Monotone
convergence bounds its square energy by four times the terminal second moment.
AE finiteness is proved before real conversion; the square root is a measurable
L2 envelope. Right continuity gives its bound at all times on one event,
including time zero and the terminal time. Regressions cover the initial square,
a nonzero constant process, and arbitrary pathwise choices of time.

This is the Doob/DCT prerequisite in Protter II.27, Corollary 3. The forward
direction is now proved in `QuadraticVariation/Moments.lean`: a true cadlag
martingale square-integrable at every finite time has an integrable actual raw
bracket with `E([X,X]_t) = E(X_t^2)`, including time zero. The proof localizes
`X^2-[X,X]`, whose zero initial residual legitimizes the unmasked bridge.
Stopped squares have the Doob L2 envelope; Fatou first establishes bracket
integrability, then DCT proves the exact expectation identity. Regressions
cover a nonzero constant and the compensated Poisson jump martingale with
its explicit chosen-past independence assumption.

The reverse implication for general local martingales and infinite-terminal
Corollary 4 remain open. No bracket integrability is used as a premise of the
forward direction, and no total integral fallback is used to establish it.

- Bracket-controlled jump-localization increment: **PASS, 9413 jobs** (two
  production modules plus regression export); all three final traces have
  zero warnings and errors.
- `Audit/SemimartingaleJumpLocalizationAxioms.lean`: **PASS, 8 declarations**,
  depending only on `propext`, `Classical.choice`, and `Quot.sound`. Initial
  and positive-time jump bounds, derived initial L2, actual masked true-L2
  localizers, and the initial-value safeguards are checked. The original
  unlocalized converse and general LM-to-SM bridge remain open.
  No full-library build or document-completion push.

## Bracket-controlled jump localization

`QuadraticVariation/JumpBound.lean` bounds every squared jump by the actual
raw bracket at any later horizon on one event, including the initial jump.
`JumpLocalization.lean` derives L2 square-root and initial-value control from
an integrable bracket. For an actual semimartingale/local-martingale pair,
integrable bracket values at all finite times construct square-integrable
martingale localizations in the canonical masked `Locally` convention.
Bounded caglad cutoffs of the left-limit process give the stopped bound
`n + sqrt([X,X]_T)`. Thus the proof permits jump overshoots rather than asserting
that a discontinuous exit attains the threshold. The source integrable-envelope
criterion proves true martingality of each localizer.

Regressions retain the initial jump, rule out integrable raw brackets for
non-L2 initial values, and allow nonzero/unbounded L2 initial values.
The original unlocalized true-martingale conclusion is now proved in
`QuadraticVariation/MomentCriterion.lean`. Each localized square residual has
an integrable envelope, so it is a true martingale with zero expectation.
This bounds the localized second moments by the original bracket expectation.
Doob estimates and Fatou then give an L2 maximal envelope for the original
process. The source envelope criterion proves its true martingality, and the
moment equivalence follows from the already proved forward identity.

The continuous-local-martingale entry constructs the semimartingale witness
internally. For true finite-time L2 cadlag martingales, the square minus the
raw bracket is also a true martingale, with zero initial residual and no
zero-initial restriction on the original martingale. Regressions use the
compensated Poisson bracket, the exact initial L2 criterion for constant
processes and the true compensated-square residual.

The general LM-to-SM bridge and infinite-terminal Corollary 4 remain open.
Consequently this is Corollary 3 on the actual semimartingale domain, not a
claim to have already constructed a bracket for every local martingale.

- Finite-time raw moment-criterion increment: **PASS, 9414 jobs** (one new
  production module and regression export); both final traces have zero
  warnings and errors.
- `Audit/SemimartingaleMomentCriterionAxioms.lean`: **PASS, 8 declarations**,
  using only `propext`, `Classical.choice`, and `Quot.sound`. The uniform
  maximal estimate, original true-L2 martingale, equivalence, continuous-local
  entry, true compensated-square martingale and all three regressions pass.
  The general LM-to-SM bridge and infinite-terminal Corollary 4 remain open.
  No full-library build or document-completion push.

## Normalized continuous-bracket moments

`QuadraticVariation/ContinuousMoments.lean` uses the existing continuous-part
owner and its identity with raw QV minus the initial square on continuous paths.
True finite-time L2 continuous martingales have integrable normalized brackets
with expectation `E(X_t^2)-E(X_0^2)`. Their square minus this normalized bracket
is a true martingale retaining initial value `X_0^2`, proving Klenke 21.70(ii).
For continuous local martingales, the finite-time L2 criterion requires both
initial L2 and integrability of the normalized bracket at every finite time.
This includes Klenke Corollary 21.76 (printed p. 571) at its finite-time scope.

Regressions retain the initial second moment, reject omission of initial L2
even when the normalized bracket is zero, and prove that a compensated Poisson
square is not a martingale although its continuous bracket vanishes. Thus no
continuity or initial-moment premise is silently removed. Remaining Klenke
21.70--21.76 source bridges and infinite-terminal criteria are separate work.

- Incremental validation: 9415 jobs passed; both affected final traces contain
  zero warnings or errors. All seven declaration/regression axiom audits passed
  using only `propext`, `Classical.choice` and `Quot.sound`. No full-library
  build or document-completion push was performed.

## Extended terminal raw quadratic variation

`QuadraticVariation/Terminal.lean` defines the extended terminal raw bracket
as the supremum of integer-time values of the existing owner. It is measurable,
retains the initial square, equals the whole-half-line supremum almost surely,
and is the actual extended-value limit along all nonnegative real times.
Its nonnegative integral equals the supremum of the finite-time integrals by
AE monotone convergence. Finite expected terminal energy proves AE finiteness,
integrability of its real value and all finite-time brackets, and true L2
martingality with a uniform second-moment bound.

The constant regression retains arbitrary initial energy and characterizes its
finite expectation exactly by initial L2. The Brownian regression proves an
infinite terminal bracket and rules out finite expected terminal energy.
The martingale's actual terminal value and half-line convergence are not
assumed or supplied here; Protter II.27 Corollary 4 is not yet closed.

- Incremental validation: 9416 jobs passed, with zero warnings or errors in
  both affected final traces. All 15 owner/theorem/regression axiom audits
  passed using only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Global Doob envelope and terminal-energy equivalence

`Martingale/Inequalities/DoobGlobalL2.lean` proves the whole-half-line
maximal-square estimate by AE monotone convergence of the existing dense
running suprema. It constructs a measurable, nonnegative global L2 envelope
with factor four, controlling all times on one event. No uncountable
intersection or real-valued fallback at infinity is used.

`QuadraticVariation/TerminalMoments.lean` proves the converse terminal-energy
bound from true martingality and uniform second moments. Finite expected raw
terminal energy is therefore equivalent to true global L2 boundedness on the
existing semimartingale domain, and supplies the global envelope. Regressions
retain the initial square, control arbitrary measurable random-time evaluations
without a deterministic bound, and rule out globally bounded Brownian second
moments. The martingale's terminal convergence and moment identity are still open.

- Incremental validation: 9418 jobs passed; all three affected final traces
  contain zero warnings or errors. All eight theorem/regression axiom audits
  passed using only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Actual L2 closure and terminal energy identity

`Martingale/Convergence/ContinuousL2Closure.lean` constructs an L2 closing
variable using the integer restriction and a global L2 envelope. It proves
integer-time AE and L2 convergence, conditional-expectation closure at every
real time, convergence of second moments and the inherited second-moment
bound. `QuadraticVariation/TerminalClosure.lean` identifies that variable's
second moment with the expected extended terminal raw bracket, in both
extended and finite real forms, using monotone convergence.

Regressions retain an arbitrary constant initial variable and the second
moment 25 for the constant-five martingale. A continuous oscillating path
with zero integer samples but nonzero quarter-integer samples rejects any
automatic inference of full-half-line convergence from integer convergence.
The actual half-line AE convergence theorem is still open, so Corollary 4
is not yet source-level complete.

- Incremental validation: 9420 jobs passed; all three affected final traces
  contain zero warnings or errors. All six theorem/regression axiom audits
  passed using only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Whole-half-line L2 and almost-sure convergence

`Martingale/Convergence/ContinuousL2Convergence.lean` proves the later-time
increment and closing-error L2 estimates by conditional expectation, and
extends integer L2 convergence to every real time tending to infinity.
`Martingale/Inequalities/DoobTailL2.lean` freezes the process before a
deterministic start, reindexes the filtration, and constructs a whole-tail
L2 envelope controlled by the closing error.

`Martingale/Convergence/ContinuousL2Limit.lean` proves that these envelopes
vanish in L2, extracts an AE-vanishing subsequence via Borel-Cantelli and
uses their common-event all-later-times control to prove the genuine
whole-half-line AE limit. `QuadraticVariation/TerminalConvergence.lean`
combines this with the constructed closing variable and exact terminal
energy moment identity. This completes Protter II.27 Corollary 4 on the
actual semimartingale domain. The CLM entry constructs its semimartingale
witness internally; general LM-to-SM (III.30) remains open.

Regressions retain nonzero constant initial variables, support arbitrary
sample-dependent clocks escaping to infinity, and identify any independently
specified terminal value AE with the constructed one. General non-L2/UI and
supermartingale convergence, infinite-terminal sampling and regularization
are not closed by this L2 packet.

- Incremental validation: 9424 jobs passed; all five affected final traces
  contain zero warnings or errors. All 11 theorem/regression axiom audits
  passed using only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Explicit terminal values under stopping

`Process/Stopping/TerminalValue.lean` defines `stoppedValueWithTerminal` by
reusing Mathlib's owner at finite times and using the supplied terminal
variable at infinity. It proves branch/finite-time identities, AE convergence
of bounded truncations from a full-time limit, norm-envelope domination and
version transport using process indistinguishability and terminal AE equality.

Regressions distinguish explicit infinite values from totalized evaluation,
reject convergence to a wrongly supplied terminal value and cover mixed
finite/infinite random times. Infinite-terminal optional sampling remains
open. Source I.10--I.13 distinguish arbitrary closing variables from actual
terminal limits; Mathlib's stopping sigma-field lies in `iSup F`, so the
terminal-measurability/limit condition cannot be dropped at infinity.

- Incremental validation: 9425 jobs passed; both affected final traces contain
  zero warnings or errors. All 11 owner/theorem/regression axiom audits passed
  using only `propext`, `Classical.choice` and `Quot.sound`. No full-library
  build or document-completion push was performed.

## Possibly infinite optional sampling with an actual terminal variable

`Martingale/OptionalSampling/ContinuousInfiniteTerminal.lean` proves uniform
integrability of all stopping families and integrability of each stopped value,
the minimum formula at the original stopping sigma-field, AE-ordered optional
sampling, terminal conditional-expectation representation and Lp transfer.
Both stopping times may be infinite. Bounded truncations converge to the
explicit terminal-valued owner; Vitali L1 convergence and conditional-expectation
contraction pass the proved bounded identity to the limit.

`QuadraticVariation/TerminalSampling.lean` constructs the terminal variable,
full-time limit and UI from finite expected raw terminal energy, giving L2
stopped values and sampling identities for every pair of AE-ordered stopping
times. Regressions cover both times infinite, the time-zero initial term and
unbounded times ordered only AE. This closes the actual-terminal martingale
sampling identities of Protter I.16. General non-L2 terminal construction,
supermartingale sampling and arbitrary-closing source bridges remain open.

- Incremental validation: 9427 jobs passed; all three affected final traces
  contain zero warnings or errors. All ten theorem/regression axiom audits
  passed using only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Weak L1 maximal estimates without second moments

The existing norm-submartingale proof is now public for arbitrary preordered
time indices. `DoobWeakFiniteTime.lean` proves exact weak bounds for sorted
partitions and arbitrary nonempty finite sampling sets. `DoobWeakContinuousL1.lean`
passes to the extended dense supremum by increasing finite exceedance events,
then uses a common right-continuity event to cover the entire finite interval.
All results are Banach-valued and need only first moments. Horizon zero and
non-L2/nonzero constant regressions protect the initial-value and L1 scope.
These are prerequisites, not a claim of general UI half-line convergence.

- Incremental validation: 9429 jobs passed; all four directly affected final
  traces contain zero warnings or errors. All eight theorem/regression axiom
  checks passed with only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## General UI half-line limits and constructed terminal sampling

`ContinuousL1Closure.lean` constructs an integrable integer-time AE/L1 limit
and closes all finite coordinates. `ContinuousLpContraction.lean` supplies
the all-real-time Lp extension for p >= 1, sharing the proof with the existing
L2 API. Global and tail weak L1 estimates bound the probability of any later
deviation by the L1 closing error. `ContinuousL1Limit.lean` proves that the
event of arbitrarily late deviations at each positive scale has measure zero;
countably many scales give the actual full-half-line AE limit. No L2 moment,
integrable path supremum or integer-to-half-line shortcut is assumed.

This implements Protter I.12 and the UI/actual-limit-closing equivalence of
I.13. `ContinuousUITerminal.lean` constructs the terminal variable for the
possibly-infinite optional-sampling theorem, including AE-only ordering.
Regressions retain a non-L2 constant initial variable, test sampling without a
limit premise and apply convergence to sample-dependent escaping clocks.
The general L1-bounded non-UI/supermartingale convergence theorem, explicit
extended-filtration formulation and arbitrary-closing bridges remain open.

- Incremental validation: 9435 jobs passed; all eight directly affected final
  traces contain zero warnings or errors. All 18 public/refactored-theorem and
  regression axiom checks passed with only `propext`, `Classical.choice` and
  `Quot.sound`. No full-library build or document-completion push was performed.

## Closing-variable projection and the actual extended-index martingale

`ContinuousClosingProjection.lean` identifies an actual terminal limit with
the conditional expectation of any closing variable onto `iSup F` and proves
full-time AE/L1 convergence to that projection. This closes the martingale
closing assertion of Protter I.10, not its general supermartingale assertion.
`Process/Filtration/Terminal.lean` extends the time index to `WithTop`, preserves
all finite sigma-fields and uses `iSup F` at infinity, in agreement with the
native infinite stopping sigma-field. `ContinuousTerminalExtension.lean`
proves the extended-martingale/UI equivalence in Protter I.13 using the existing
terminal-valued stopping owner. No initial term or finite-time value is changed.

Regressions include a symmetric two-point nonunique closing variable, recovery
of a terminal-measurable closing variable and arbitrary integrable random
constant initial values. Source I.16's ambient-event stopping-sigma-field
definition (printed p. 5; PDF p. 17) is not silently identified with Mathlib's
`iSup F` domain at infinity; that source bridge remains separately tracked.

- Incremental validation: 9438 jobs passed; all four affected final traces
  contain zero warnings or errors. All 12 owner/theorem/regression axiom
  checks passed with only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Native infinite sampling from arbitrary closing input

`ContinuousClosingTerminal.lean` proves integrability and optional sampling
for projected terminal values starting from any integrable closing variable Y.
Each stopped value equals `E[Y | F_tau]`, because `F_tau <= iSup F` and the
tower property removes the terminal projection inside conditional expectation.
Both times may be infinite and ordered only AE. When Y is terminal-field
measurable, the unprojected formula follows with that premise explicit.

The source I.16 native-owner correction is now implemented and protected by
two regressions. One accepts arbitrary closing input without terminal
measurability or a supplied limit. The other proves that the symmetric two-point
counterexample has a usual filtration and nevertheless rejects the unprojected
formula at two infinite times. Thus neither usual conditions nor ordinary
ambient measurability can replace the terminal projection. No competing
ambient stopping owner is introduced. Supermartingale sampling remains open.

- Incremental validation: 9439 jobs passed; both affected final traces contain
  zero warnings or errors. All six theorem/regression axiom checks passed with
  only `propext`, `Classical.choice` and `Quot.sound`. No full-library build or
  document-completion push was performed.

## Finite-time upcrossing bounds for one-sided martingales

`SubmartingaleReindex.lean` adds monotone sampling for both submartingales and
supermartingales using the existing filtration owner. Repeated sample times
are allowed. `UpcrossingFiniteTime.lean` proves measurability/integrability of
the native upcrossing count and its endpoint positive-part and first-moment
bounds on any finite time partition. Because the native count is strict-before,
the cutoff is `size + 1`, retaining the final horizon sample. The level term
is multiplied by the actual measure mass, not silently normalized to one.

Regressions detect the lost-terminal-index error, preserve one-sided inequalities
under repeated sampling without falsely obtaining a martingale, and retain the
finite-measure bound. These prepare general L1-bounded convergence; the dense-
grid refinement and full-time non-UI convergence steps remain open.

- Incremental validation: 9441 jobs passed; all three affected final traces
  contain zero warnings or errors. All nine theorem/regression axiom checks
  passed with only `propext`, `Classical.choice` and `Quot.sound`. No full-library
  build or document-completion push was performed.

## Upcrossing monotonicity under refinement and repeated sampling

`ForMathlib/Probability/UpcrossingEmbedding.lean` compares the native crossing
times by hitting-time minimality and proves that monotone sampling cannot
increase the number of completed upcrossings. Repetitions are allowed, but
all retained indices must precede the target cutoff strictly.
`Analysis/PathVariation/UpcrossingRefinement.lean` uses the existing ceiling
projection to prove endpoint-inclusion monotonicity across possibly different
horizons, the standard refinement interface and endpoint-set invariance.

Regressions show that repeating every sample twice leaves the count unchanged,
the actual common refinement controls both input counts, and a non-strict
target cutoff loses a completed crossing. The growing dense-grid global bound
and general non-UI full-time convergence proof remain open.

- Incremental validation: 9443 jobs passed; all three affected final traces
  contain zero warnings or errors. All seven theorem/regression axiom checks
  passed with only `propext`, `Classical.choice` and `Quot.sound`. No full-library
  build or document-completion push was performed.

## General L1-bounded submartingale and supermartingale limits

`Analysis/PathVariation/ExpandingDyadic.lean` restricts the existing dyadic
partition to growing integer horizons, retaining all preceding endpoints.
The ceiling values approach every fixed time from the right. `DenseUpcrossings.lean`
aggregates native finite counts and proves maximum attainment when finite.
`DenseUpcrossingLimit.lean` proves that two later strict visits create a new
crossing on a refinement. Thus finite rational-level counts rule out intervening
oscillations and extend an integer-time limit to the entire half-line.

`UpcrossingGlobalL1.lean` gives the global first-moment expectation bound,
measurability and one full-measure event for all rational level pairs.
`ContinuousL1Bounded.lean` combines these with Mathlib's integer limit process
to construct an actual integrable almost-sure full-time limit for each
right-continuous L1-bounded submartingale, supermartingale or martingale.
This closes general Protter I.10, superseding the historical open notices above.
It requires neither UI nor L2 and does not assert L1 convergence or closure.
Regularization, supermartingale optional sampling and the other package gates
remain open. Regressions cover a proper supermartingale, non-L2 initial values,
sample-dependent escaping clocks and the continuous integer-only counterexample.

- Incremental validation: 9448 jobs passed; all six affected final traces
  contain zero warnings or errors. All 24 definition/theorem/regression axiom
  checks passed with only `propext`, `Classical.choice` and `Quot.sound`. No
  full-library build or document-completion push was performed.

## Bounded stopping integrability for submartingales and supermartingales

The shared `CeilingIndex.lean` lemmas now support both existing upcrossing
proofs and the stopping-index construction in `Stopping/PartitionIndex.lean`.
Its native discrete stopping values are exact when the original times belong
to the partition. Discrete expected-stopping monotonicity and integrability
then apply to the original processes without a parallel finite-index calculus.

`CountableRangeOneSided.lean` proves terminal conditional inequalities on
countable-range stopping fibers. `UpperApproxPartition.lean` embeds the existing
upper approximations in restrictions of the existing uniform grid and bounds
their first moments by the signed initial expectation plus twice the terminal
norm expectation. `ContinuousOneSidedIntegrability.lean` passes this bound
through the actual right-continuous limit by Fatou, proving integrability of
bounded stopped values for both one-sided martingale classes.

This is the integrability assertion of Protter I.17, not the full two-time
conditional inequality. There is no UI, nonnegativity, global L1 bound,
pathwise envelope or usual-filtration premise. Regressions distinguish a
proper supermartingale from equality, test the endpoint-range guard, and cover
unbounded-in-time first moments and a negative initial value.

- Incremental validation: 9453 jobs passed; all eleven affected final traces
  contain zero warnings or errors. All 32 new/refactored-declaration and
  regression axiom checks passed with only `propext`, `Classical.choice` and
  `Quot.sound`. No full-library build or document-completion push was performed.

## Protter I.21 stopping-value characterization

`OptionalSampling/ContinuousCharacterization.lean` proves that an adapted
process with integrable, common-mean stopped values at every stopping time,
including infinity, is a UI martingale. Past-event pasting of a finite time
and infinity identifies each coordinate as the conditional expectation of
the explicit terminal input. The source zero-mean theorem is a corollary,
with no zero-initial-value assumption. Neither path regularity nor a supplied
terminal-limit premise is needed for this implication.

Regressions give an adapted continuous two-point process with zero means at
every deterministic time that is not a martingale, retain nonzero centered
random initial values and nonzero common means, and reject nonintegrable
terminal input by the infinite stopping test. The conclusion treats the
input as a closing variable, not necessarily the actual terminal path limit.

- Incremental validation: 9454 jobs passed; both affected final traces contain
  zero warnings or errors. All seven theorem/regression axiom checks passed
  with only `propext`, `Classical.choice` and `Quot.sound`. No full-library
  build or document-completion push was performed.

## Convex process transformations (2026-09-10)

`Martingale/Convex.lean` closes the two process corollaries of Protter I.19 by
reusing Mathlib's conditional Jensen theorem. The martingale input may be
finite-dimensional Banach-valued. Submartingale inputs require a nondecreasing
convex map; both interfaces retain transformed-coordinate integrability.
No path regularity or unnecessary finite-measure hypothesis is added.

Four regressions distinguish monotonicity from convexity, transformed
integrability from original integrability, and test the nonlinear exponential
map on a proper submartingale. Incremental validation passed 9455 jobs; both
affected final traces have zero warnings or errors. All six axiom audits passed
with only `propext`, `Classical.choice` and `Quot.sound`. No full-library build
or document-completion push was performed. General I.20 remains open here.

## General Doob Lp maximal inequality (2026-09-10)

Protter I.20's full main inequality is now proved for nonnegative
submartingales and every real p > 1, superseding the open notice above.
The actual extended supremum over all NNReal times has Lp seminorm at most
p/(p-1) times the supremum of the coordinate seminorms. Coordinatewise AE
nonnegativity is sufficient. No L2, UI or finite uniform bound is needed for
the extended inequality. A finite uniform bound constructs a measurable
nonnegative real Lp envelope, equal to the all-time supremum almost surely,
with simultaneous domination at all times and the same sharp constant.
The Banach-valued true-martingale norm form is also proved.

Finite sample sets are sorted through the existing partition owner; arbitrary
countable samplings are controlled by increasing finite prefixes. The new
extended-nonnegative Lp monotone-convergence lemma and the pure right-continuous
dense/full-supremum bridge are independently reusable. Five regressions test
a proper submartingale at p = 3, infinite suprema, isolated off-grid spikes,
random initial values and the strict exponent guard.

- Incremental validation: 9460 jobs passed, all six affected final traces
  contain zero warnings or errors, and all 16 axiom audits use only `propext`,
  `Classical.choice` and `Quot.sound`. No full-library build or document-completion
  push was performed. General one-sided conditional optional sampling and
  regularization remain open; this milestone does not close the package.

## Reverse one-sided UI prerequisite (2026-09-10)

`Martingale/Convergence/ReverseOneSided.lean` proves uniform integrability of
a reverse supermartingale from an upper bound on its expectations, and of a
reverse submartingale from a lower bound. The native order-dual natural-time
filtration is reused. Exact conditional-residual L1 norms are expectation
differences. Their tail smallness, finite-prefix UI and conditional-expectation
UI prove the assertion; the global L1 bound is derived independently. No sign,
L2 or assumed UI condition is used.

Four regressions retain the reverse order and one-sided direction, demonstrate
the necessity of the expectation bound and permit non-L2 random initial data.
Incremental validation passed 9461 jobs; both affected final traces have zero
warnings or errors, and all nine axiom audits use only `propext`, `Classical.choice`
and `Quot.sound`. No full-library build or document-completion push was performed.
This is a prerequisite for the stopping approximation argument; it does not
yet close general I.17 or regularization.

## General bounded one-sided optional sampling (2026-09-10)

Protter I.17 is now proved for general real submartingales and supermartingales.
The original dyadic upper approximations decrease; their sampled processes
are native reverse one-sided martingales on stopping sigma-fields. The proved
expectation bound gives UI, and right continuity plus Vitali gives L1 convergence.
Exact finite-partition conditional inequalities then pass to the original
stopping information by set-integral comparison. Repeated grid endpoints are
allowed, and the ordinary non-dyadic mesh is not assumed decreasing.

The progressive interface requires one common right-continuity event. Under
usual conditions, an indistinguishable progressive version yields the theorem
for the original process. Native stopping-time interfaces also permit AE order
and AE deterministic bounds. No global L1 bound, nonnegativity, Class D, L2 or
assumed UI is used. Integrability at bounded times was proved in the earlier
packet; the present packet completes its general conditional inequality.
UI of each decreasing approximation sequence is not UI over all bounded stops.

Incremental validation passed 9469 jobs; all nine affected final traces contain
zero warnings/errors. All 28 new declaration/regression axiom audits use only
`propext`, `Classical.choice` and `Quot.sound`. Four regressions cover the
non-nested original mesh, negative unbounded-in-time values, AE-ordered sampling
with non-L2 random initial data, and repeated-endpoint stopping information.
No full-library build or document-completion push was performed. Closed
supermartingale sampling at unbounded times (I.16), regularization (I.9), and
the remaining package obligations are still open.

## Stopping-time conditional-expectation commutation (2026-09-10)

The second corollary to Protter I.18 is proved in
`Probability/Conditional/StoppingCommutation.lean`: both conditioning orders
equal conditioning on the minimum stopping sigma-field. The proof uses the
native comparison events and tower property, not a regularized martingale
version. It covers complete real Banach targets, unordered stopping times and
two infinite times without usual conditions. At infinity the native terminal
projection remains explicit; no ambient information is inserted.

Three regressions cover crossing orders, a terminal projection that is genuinely
different from its input, and non-L2 random initial values. Incremental validation
passed 9470 jobs, both affected final traces have zero warnings/errors, and all
six axiom audits use only `propext`, `Classical.choice` and `Quot.sound`.
No full-library build or document-completion push was performed. This closes
the commutation corollary, not regularization or unbounded closed-supermartingale
sampling; the entire package is still incomplete.

## Lower-closed supermartingale integrability (2026-09-10)

The conditional lower bound in Protter's supermartingale closure now passes
from deterministic times through countable stopping fibers and the existing
L1-convergent upper approximations to arbitrary bounded stopping times. A
signed elementary estimate gives first-moment bounds independent of the
horizon. No nonnegativity or second-moment condition is imposed.

The same estimate yields a global first-moment bound and hence an actual
integrable full-half-line limit. Native Levy upward convergence shows that
the lower closing input's terminal projection is at most that limit. These
variables are not identified. Fatou applied to truncated stopping values
proves integrability at arbitrary, possibly infinite stopping times using
the actual limit; replacing its infinite-time value by the closing projection
preserves integrability. No UI or L1 convergence of the original process is
assumed or asserted.

Incremental validation passed 9475 jobs, all six affected final traces have
zero warnings/errors, and all 16 new declaration/regression axiom audits use
only `propext`, `Classical.choice` and `Quot.sound`. Three regressions exhibit
strict lower closure of a proper supermartingale, retain non-L2 initial data,
and reject lower closure for minus time. The unbounded two-time conditional
inequality of I.16 remains open. No full-library build or document-completion
push was performed; the whole package remains incomplete.

## Unbounded closed-supermartingale optional sampling (2026-09-10)

Protter I.16's supermartingale conditional inequality is now proved with the
same native stopping-owner correction as the martingale version. Both times
may be infinite and are only required to be AE ordered. The lower closing
input is evaluated at infinity through its terminal projection `E[Y | iSup F]`;
an unprojected corollary explicitly requires terminal-filtration measurability.
The nonnegative-supermartingale corollary uses terminal zero.

Signed Fatou subtracts the conditional expectations of the lower closing input,
which converge AE and in L1 along the truncated stopping filtration. This
removes the later bound without assuming UI of the original supermartingale.
The earlier bound is removed on countably many finite-time events. On the
event that both times are infinite, the terminal indicator is measurable in
the native earlier stopping sigma-field. Usual completeness transports the
pointwise theorem to AE ordering without changing the original conditioning
information.

Incremental validation passed 9479 jobs; all five affected final traces have
zero warnings/errors, and all 13 new declaration/regression axiom audits use
only `propext`, `Classical.choice` and `Quot.sound`. Four regressions cover a
proper supermartingale with strict lower closure, non-L2 initial data, failure
of unprojected infinite sampling and negative signed Fatou bounds. No full-library
build or document-completion push was performed. Regularization (I.9) and
the other recorded package obligations remain open; the package is not complete.

## Doob regularization: necessary direction (2026-09-10)

Antitone deterministic samples of either one-sided martingale class are now
proved uniformly integrable. On common-event right-continuous paths, samples
approaching a time from the right converge in L1, and the expectation function
is right-continuous. Usual completeness transfers martingality to a given
modification, proving the necessary direction of Protter I.9 without an L2 or
global first-moment bound. No cadlag version is constructed by these results;
I.9's sufficient direction and its simultaneous path construction remain open.

Incremental validation passed 9482 jobs. All four affected final traces have
zero warnings/errors, and all 11 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. Regressions reject a right-continuous
modification of the isolated-initial-drop supermartingale, demonstrate local
L1 sampling without global first-moment control, and retain non-L2 random initial
data. No full-library build or document-completion push was performed.

## Local skeleton estimates before regularization (2026-09-10)

Signed weak maximal inequalities are now proved for discrete and arbitrary
finite deterministic samples of submartingales and supermartingales. The
first absolute-level hitting time and bounded optional sampling control its
first moment by the initial expectation and terminal absolute first moment.
No nonnegativity, right continuity, usual conditions or L2 premise is used.
Finite-prefix unions give weak bounds for countable bounded sampling families;
an outer-measure argument excludes an infinite supremum. Countably many integer
horizons yield one common local-boundedness event for each chosen skeleton.

Local first moments also control the existing dyadic upcrossing counts for
deterministically clipped processes, simultaneously for all rational levels
and integer horizons. This does not yet construct the regularized path or
bound every real-time value of an unregularized process. The isolated initial
drop satisfies these bounds but has no right-continuous modification.

Incremental validation passed 9487 jobs. All six affected final traces have
zero warnings/errors, and all 22 new declaration/regression axiom audits use
only `propext`, `Classical.choice` and `Quot.sound`. Four regressions retain
negative means, non-L2 random initial values at zero horizon with repeated
endpoints, the initial-drop obstruction, and processes lacking a global L1
bound. No full-library build or document-completion push was performed.

## Simultaneous monotone dyadic sequence limits (2026-09-10)

The union of the existing expanding-grid endpoints is now explicitly proved
countable and dense. A finite monotone sample prefix embeds in a common grid;
its native upcrossing count is bounded by the existing dense count. Reversal
and negation give the decreasing-sample bound, with cutoff N+1 retaining the
reflected initial endpoint. Congruence and reversal proofs were adapted from
the audited project-internal exchangeability implementation with attribution
preserved, using only native Mathlib crossing owners and no legacy imports.

For both one-sided martingale classes, one full-measure event now supports
finite limits along every bounded monotone or antitone sequence of dyadic
points. The proof places the universal sequence quantifier inside the event;
it does not intersect uncountably many coordinate convergence events. Different
sequences' limits are not yet identified, and no cadlag modification is claimed.

Incremental validation passed 9492 jobs. All six affected final traces have
zero warnings/errors; all 24 declaration/regression axiom audits use only
`propext`, `Classical.choice` and `Quot.sound`. Regressions enforce the reversal
cutoff correction, retain non-L2 random initial data, and exhibit simultaneous
sequence limits without a right-continuous modification. No full-library
build or document-completion push was performed; the package remains incomplete.

## Actual one-sided limits and cadlag dyadic extension (2026-09-10)

A generic alternating monotone selection argument now identifies actual
one-sided filter limits from convergence of all monotone samples. It applies
to subsets of ordered time spaces and does not assume continuity. On the
common dyadic event, both one-sided limits exist at every positive time and
the right limit exists at zero. Right-limit extension is right-continuous,
and its left limits agree with the strict-left skeleton limits.

The actual `dyadicRightLimitProcess` uses native `limUnder` on the existing
dyadic skeleton strictly after each time. This is not the full-time right-limit
selector of an arbitrary unregularized input. It has cadlag paths for both
one-sided martingale classes, without assuming right-continuous expectations.
For already right-continuous inputs it agrees pointwise, and indistinguishable
inputs give indistinguishable extensions. Adaptation and the modification
identity under the I.9 expectation condition remain to be proved. An isolated
initial drop explicitly gives a cadlag extension that is not a modification.

Incremental validation passed 9497 jobs. All six affected final traces have
zero warnings/errors; all 21 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. Three regressions cover the
actual changed initial value, retained non-L2 initial data and distinct left/
right limits at a jump. No full-library build or document-completion push was
performed. I.9 is still partial until the modification and source corollaries
are verified; the whole package remains incomplete.

## Full Doob regularization: I.9 closed (2026-09-10)

The actual dyadic extension now has proved L1 right-side sampling and adaptation
under the usual conditions. Conditional-order comparisons bound it on the
correct side of the original one-sided martingale; right-continuous expectations
make their means equal and hence give the modification identity. No original
path regularity, UI, L2, global first-moment bound or zero initial value is used.

Protter I.9 is proved in both directions for real submartingales and
supermartingales, with same-class cadlag versions and uniqueness up to
indistinguishability among right-continuous modifications. The true-martingale
existence corollary and the already-right-continuous cadlag corollary are proved.
This closes the earlier I.9 partial checkpoints, not the remaining package.

Incremental validation passed 9501 jobs. All five affected final traces have
zero warnings/errors; all 28 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. Three regressions retain non-L2
random initial data, preserve a proper submartingale without global L1 control,
and verify uniqueness without original path regularity. No full-library build
or document-completion push was performed.

## Class D and Class DL stopping families (2026-09-10)

The sole Class D predicate uses UI over every finite stopping-time value, not
just deterministic times. Class DL retains a separate UI estimate at each
finite horizon. Their definitions do not bundle adaptation, path regularity,
one-sided martingality or initial normalization. Proved interfaces include
algebra, indistinguishable-version invariance, arbitrary stopping, equivalence
with one UI bound over all bounded stopping times, and AE-finite sampling by
eventually exact truncation. Every deterministically stopped process is Class D
exactly when the original process is Class DL.

Optional sampling proves the Class D/UI equivalence and Class DL property for
right-continuous true martingales. Nonnegative right-continuous submartingales
are Class DL, with common-event or coordinatewise-AE positivity. The positive
guard is not discarded for general one-sided martingales.

Incremental validation passed 9507 jobs. All seven affected final traces have
zero warnings/errors, and all 33 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. The continuous process `X_t=t`
is Class DL but not Class D. An adapted random-time spike is a deterministic-UI
modification of zero but not Class D; this latter example is not right-continuous.
Other regressions retain non-L2 initial data and reject unrelated terminal
bookkeeping at infinity. No full-library build or document-completion push
was performed. Doob-Meyer existence/uniqueness and the other package gaps remain.

## Discrete potential Doob decomposition: III.9 closed (2026-09-10)

The potential predicate retains nonnegative supermartingality and vanishing
expectations. The increasing and martingale terms use native discrete parts
of the negative process. Their initial values and expectation identity are
proved. A first-moment bound constructs an integrable terminal limit of the
increasing process, with domination, UI and L1 convergence. Potential L1 decay
gives the same martingale limit, conditional closure, UI and the exact terminal
mean. Uniqueness permits AE initial normalization and decomposition identities
and concludes indistinguishability of both parts without completeness.

Incremental validation passed 9513 jobs. All seven affected final traces have
zero warnings/errors; all 11 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. Regressions retain non-L2 random
initial values, distinguish the increasing sign and reject a nonvanishing
constant potential. No full-library build or document-completion push occurred.
This closes III.9 only; continuous-time Doob-Meyer and the other gaps remain.
The current blocker table also separates the already-proved SM-B12 bracket
construction from the still-open Chapter III proof gates.

## Pre-stopping fields and announcing sequences (2026-09-10)

The sole `IsStoppingTime.measurableSpaceBefore` owner agrees with Protter's
positive-time generators and embeds into the native stopped field. Its zero,
fixed-time and infinite-time identities are proved. III.7 allows both stopping
times infinite. Predictable finite evaluation is measurable before stopping;
the explicit-terminal extension requires terminal-filtration-measurable data.
Finite predictable samples generate the entire field (III.5). At arbitrary
times the corresponding identity uses explicit terminal values. The source's
zero-terminal proof convention cannot give the full generator identity at an
identically infinite time, where those samples generate only the bottom field.

The announcing relation keeps pointwise monotonicity and strict inequality
on the positive-lifetime event, with only AE convergence. III.6 identifies
the supremum of the announcing stopped fields under initial completeness;
right continuity is unnecessary. Deterministic finite times, zero and infinity
have actual witnesses. Regressions retain nonintegrable initial data, preserve
the whole terminal field, reject information-erasing zero-terminal generators,
and give a nonzero probability-space example of non-everywhere announcing.

Incremental validation passed 9520 jobs. All eight affected final traces have
zero warnings/errors; all 37 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. No full-library build or push
occurred. Optional/progressive sigma-field bridges, accessibility, total
inaccessibility, continuous Doob-Meyer and the other package gaps remain open.

## Optional and progressive sigma-field bridges (2026-09-10)

The progressive field is characterized by all finite-horizon restrictions and
proved equal to the source real-process-generated field. Its measurable maps
are exactly native progressive processes. The optional field has the source
adapted, everywhere-cadlag generators. The full predictable-to-optional-to-
progressive-to-product inclusion chain is proved; continuous ramps handle
the predictable strict-future generators. The constant ambient filtration
has progressive field equal to the product field.

Strong optional processes are adapted and strongly progressive. Under usual
conditions an AE-cadlag adapted real process has an indistinguishable optional
version. The optional stopping map is measurable by transporting its generators,
so stopping preserves optionality without imposing cadlag paths on the process
being stopped. Native stopped-field measurability is proved for finite samples
and explicit-terminal samples. An initial-spike regression rejects the false
implication from optionality to right-continuous paths; other regressions
preserve finite-time stopping at infinity and nonintegrable terminal data.

Incremental validation passed 9523 jobs. All four affected final traces have
zero warnings/errors; all 27 declaration/regression axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. No full-library build or push
occurred. Deeper progressive-debut/strict-inclusion results, stopping
classification, continuous Doob-Meyer and the remaining package gates stay open.

## Protter I.6: cadlag generators of the native stopped field (2026-09-10)

The process revealing a native stopped-measurable coefficient at and after its
stopping time is adapted, everywhere cadlag and optional. It requires neither
initial measurability nor integrability of that coefficient. This construction
proves that finite adapted-cadlag samples generate exactly `F_T`. The same
identity holds for all optional real samples. The source AE-cadlag version is
proved under usual conditions by an indistinguishable optional version and
completeness of the native stopped field. I.6 is therefore closed, while other
Chapter I stopping/jump/filtration results remain separately open.

At arbitrary times, optional samples with explicitly supplied terminal-field
data generate the native stopped field. This is not an unguarded extension
of finite process evaluation. Activation at zero preserves the coefficient;
activation at infinity never reveals it at a finite time. A nonintegrable
coefficient is still an actual adapted-cadlag sample at a finite stopping time.

Incremental validation passed 9526 jobs. After correcting one long-line warning,
all four affected final traces have zero warnings/errors; all 11 declaration/
regression axiom checks use only `propext`, `Classical.choice` and `Quot.sound`.
No full-library build or document-completion push occurred. Stopping
classification, continuous Doob-Meyer and the other package gaps remain.

## Canonical owners verified at the active pin

| Interface | Owner | Decision |
| --- | --- | --- |
| Extended stopping times, stopped process, stopping sigma-algebra | Mathlib `Probability.Process.Stopping` | REUSE |
| Pre-localizing/localizing sequences; masked `Locally` | Mathlib `Probability.Process.LocalProperty` | REUSE |
| Predictable sigma-algebra and predictable implies progressive | Mathlib `Probability.Process.Predictable` | REUSE |
| Cadlag, continuous, left/right continuous common-event paths | StochLean `Probability.Process.Path` | REUSE |
| Indistinguishability and modifications | StochLean `Probability.Process.Equivalence` | REUSE |
| Deterministic bounded variation | Mathlib `Topology.EMetricSpace.BoundedVariation` | REUSE |
| Protter local martingale and Klenke witness bridge | StochLean `Probability.Process.LocalMartingale` | BUILD |
| Everywhere finite stopping-time witness | StochLean `Probability.Process.Stopping.Finite` | BUILD |
| Caglad common-event path property | StochLean `Probability.Process.Path.Caglad` | BUILD |

## Accessible and totally inaccessible decomposition (2026-09-10)

Six stopping modules implement the source finite graph, stopped-measurable
restriction, accessible and totally inaccessible predicates, restriction
stability and full III.3. A countable essential union of predictable
coincidence events constructs the decomposition. The two events are disjoint,
belong to native F_T, cover the finite-time event almost surely, and reconstruct
the original time. Both events and both restricted times are unique almost
surely. Existence holds for s-finite measures, without usualness. No selector
or decomposition assumption substitutes for existence.

Incremental validation passed 9532 jobs. Two flexible-tactic warnings were
corrected; all seven affected final traces now have zero warnings/errors.
The four regressions retain the zero-time graph, exclude infinity from finite
coincidence tests, rule out non-null countably valued inaccessible times, and
invoke unconditional decomposition existence with uniqueness. The 45-entry
axiom audit covers all 41 new public declarations and those regressions.
Only the standard three Lean axioms occur. No full-library build or push was
performed. Predictable-graph equivalence, finer restriction/hitting bridges,
III.4 Meyer, continuous Doob-Meyer and the remaining package gates stay open.

## Predictable energy and bounded Doob approximants (2026-09-10)

Protter III.10 Lemma 1 is proved: for an increasing predictable discrete
process with AE zero initial value and integrable terminal limit, a uniform
conditional remaining-mean bound N gives terminal L2 and second moment at
most 2 N^2. The finite L2 calculation is only an intermediate step; fixed
truncations and Fatou remove that assumption from the final theorem.

The actual increasing Doob owner `predictablePart (-X)` has the exact
conditional remaining-mean identity. For a supermartingale bounded by K,
all finite second moments and the constructed terminal second moment are
bounded by 8 K^2, independently of the number of time points. The terminal
limit dominates all coordinates and has the existing AE/UI/L1 convergence
properties. No continuous compensator or decomposition selector is supplied.

Incremental validation passed 9536 jobs; all five final affected traces have
zero warnings/errors. All eight declaration/regression axiom checks use only
the standard three axioms. Regressions retain the essential zero-starting
premise and reject an alleged bounded-tail example with non-L2 terminal value.
No full-library build or push was performed. The remaining III.10 jump/modulus
and continuous-time construction, III.11, III.16 and later package gates stay open.

## Predictable delays and announcing stability (2026-09-10)

Fixed nonnegative-real delays preserve stopping without right continuity;
strictly positive delays have explicit announcing witnesses, including
infinite lifetimes via integer caps. Target-capping repairs announcing
data at exceptional zero-time samples. Predictable times are closed under
finite minima/maxima and countable suprema. Suprema use finite diagonal
maxima and countably many AE convergence events, with pointwise monotonicity
and strictness maintained. Arbitrary decreasing-limit closure is not asserted.

The 9541-job incremental build passed. All six affected final traces have
zero warnings/errors; all 13 declaration/regression axiom checks use only
the standard three axioms. The infinity regression requires finite capped
announcing terms. A nonzero two-point probability-space regression disproves
naive maxima of AE announcing sequences without zero-target correction.
No full build or push was performed. F_(T-)-event restriction, predictable
graph equivalence, III.10's uniform conditional jump estimate and continuous
Doob-Meyer remain open.

## Predictable restrictions and strict-limit parts (2026-09-10)

Events measurable in the supremum of an increasing filtration now have
eventually correct measurable approximations, by native Levy upward
convergence. Tail infima of restricted stopping times, integer caps and
initial-null-event repair turn such approximations into actual announcing
data. Strictness is only needed on the retained event; no predictability of
the target is assumed by the general construction.

Under usual conditions and a finite measure, restricting a predictable time
to an F_(T-)-measurable event preserves predictability. The strictly announced
part of any increasing stopping-time limit is predictable as well, and has
null finite coincidence with every totally inaccessible stopping time.
General F_T events and arbitrary decreasing limits are not substituted.

The 9545-job incremental build passed. All five affected final traces have
zero warnings/errors. All eight declaration/regression axiom checks use only
the standard three axioms. Empty restriction yields infinity; the all-zero
sequence has an empty strict-limit event, rather than a finite zero restriction.
No full build or push was performed. III.10's uniform conditional jump estimate,
predictable graph equivalence, continuous Doob-Meyer and later gates remain open.

## Conditional stopping-window versions (2026-09-10)

Conditional projections of monotone integrable families have the expected
one-sided martingale property. Dominated right-continuous families have
right-continuous means, hence actual cadlag conditional versions under usual
conditions. A countable dense-set argument lifts coordinate AE order to one
common pathwise event; no uncountable intersection is presumed full measure.

For every nonnegative delay, the future stopping probability has a cadlag
submartingale version. Subtracting the adapted cadlag stopping indicator
constructs a cadlag version of the left-open conditional window. Its `[0,1]`
bounds and vanishing at and after the stopping time hold simultaneously.
Width comparison and version uniqueness are proved; zero width gives the
zero process up to indistinguishability. Total inaccessibility eliminates
fixed finite atoms and permits the source closed lower endpoint.

The 9551-job incremental build passed. All seven affected final traces have
zero warnings/errors. All 16 production/regression axiom checks use only
the standard three axioms. Tests retain the deterministic zero-time atom,
zero-width process vanishing and the necessary trigger-event guard at a
capped first threshold time. No full build or push was performed. These are
version prerequisites, not a proof of III.10 Lemma 2's uniform convergence;
stopping-time sampling and the uniform estimate are the next steps.

## Bounded stopping-window sampling (2026-09-10)

Conditional-expectation locality and countable stopping fibers now prove
sampling for integrable conditional-projection families without a martingale
assumption. Dominated right-continuous upper-grid limits extend this to every
bounded stopping time. The input is jointly measurable but need not be adapted;
usual adapted/right-continuous outputs are handled through a genuine
indistinguishable progressive version.

Lifetime-window indicators have proved joint measurability, right continuity
and a difference-of-revealed-indicators identity. Applying the sampling theorem
gives `R_delta(S) = P(S < tau <= S+delta | F_S)` almost surely. Its integral on
an F_S event is the actual window-event probability. The threshold probability
bound retains the event on which the threshold inequality holds; it does not
apply unguarded to a capped no-hit fallback.

The 9556-job incremental build passed. All six affected final traces have
zero warnings/errors, and all 12 production/regression axiom checks use only
the standard three axioms. Own-lifetime and infinite-target sampling
regressions both give zero. No full build or push was performed. The coherent
decreasing-window construction, shrinking trigger-event limit and final
uniform estimate are next; III.10 and the package are still in progress.

## Uniform stopping-window convergence: III.10 Lemma 2 closed (2026-09-10)

The proof now constructs coherent decreasing cadlag window versions,
measurable capped-hit trigger events and increasing bounded hit times. A
predictable strict-limit argument excludes coincidence with the totally
inaccessible lifetime on the retained events. Actual bounded-stop conditional
sampling then bounds each trigger probability by its shrinking-window
probability. No-hit fallback values are never assigned a threshold bound.

The sequence estimate extends by width monotonicity to arbitrary widths
tending to zero. Indistinguishability transports the conclusion to any
right-continuous coordinate versions. The running supremum is the existing
countable owner, equals the supremum over the full closed interval and is
almost surely finite before conversion to real values. Native convergence
in measure and an existence-of-versions entry are proved for the source
closed-window probabilities. The endpoint change uses only deterministic
no-atom identities; random-time sampling retains the strict lower endpoint.

The 9564-job incremental build passed, with all nine affected final traces
free of warnings/errors. All 41 production/regression axiom checks use only
the standard three axioms. Tests include horizon zero, a jump exactly at the
terminal time, deterministic-lifetime small windows with supremum one, and
the totally-inaccessible closed zero-width identity. No full build or push
was performed. Lemma 2 is closed; Lemma 3's jump/modulus construction and the
remaining continuous Doob-Meyer proof are the next steps. The package is not
complete.

## Actual large-jump enumeration and finite residuals (2026-09-10)

Actual positive-time large jumps are locally finite. Compact left/right-limit
control gives short-window bounds from a jump bound, and a countable dense
increment characterization makes large-jump occurrence events measurable.
The next actual large jump after a stopping time is now a stopping time under
right-continuous filtrations. Its finite values are attained strictly after
the starting time. Recursive enumeration has no omitted jumps, no repeated
finite values and escapes every finite horizon. A process whose positive jumps
are covered by totally inaccessible stopping times has totally inaccessible
enumerated entries. Neither the initial jump nor infinite graph points are
silently treated as positive finite jumps.

Finite-prefix coverage is a stopped-measurable event with complement probability
tending to zero. Actual jump coefficients use the existing explicitly
zero-terminal stopping owner and are measurable at the native stopped field.
Their revealed steps are optional. Fixed-prefix residuals are adapted cadlag,
retain the initial value and have all positive jumps bounded by b on the
coverage event. Exact cancellation requires uniqueness of finite lifetimes.

A measurable two-time oscillation envelope recovers arbitrary closed-width
increments at doubled positive width and is finite on cadlag paths. Fixed-cap
positive-excess dominated convergence gives the residual squared-moment
estimate on the good event and its complement. Conditional increment bounds
are obtained only after the pathwise clipped estimate. This repairs the
source's unproved integrability/tail passages without imposing a random
jump-count moment or exchanging `min` and conditional expectation.

The 9580-job incremental build passed; all 18 affected final traces are free
of warnings/errors. All 120 public declaration/regression axiom checks use
only the standard three axioms. Four new regressions retain arbitrary initial
constants, make constant-path future enumeration infinite, expose duplicate
jump removal and reject right-continuous hitting of the jump process itself.
No full build or push was performed. The final conditional two-time modulus,
its L2 convergence, the dyadic continuous-limit construction and general
Doob-Meyer remain open; these prerequisites do not close III.10 Lemma 3.

## Conditional modulus: compact and random-finite global forms (2026-09-10)

The conditional two-time modulus now has a measurable essential-supremum
specification, existence and AE uniqueness. Actual coherent representatives
realize its full pointwise supremum. They are asserted ambient-measurable,
not automatically measurable in every coordinate's conditioning field.
Singleton spikes formally refute the raw arbitrary-version interpretation.

For bounded adapted processes with common-event cadlag paths and totally
inaccessible positive-time jumps, compact moduli converge to zero in measure,
in squared integral and in native `eLpNorm 2`. This uses actual capped
large-jump residuals, their proved moment bounds, actual conditional martingale
envelopes and the finite TI-window convergence theorem. No supremum convergence
certificate, random jump-count moment or initial normalization is assumed.

For paths constant after an almost surely finite stopping time, the same
results hold for the global half-line modulus. The stopping time need not be
bounded. A proved global/compact comparison uses actual conditional probabilities
of its tail; their maximal probabilities vanish with the cutoff. The raw
tail-to-infinity-atom theorem keeps the finite-lifetime assumption explicit.
The global statement is the random-finite-termination form of III.10 Lemma 3;
the following increment extends this to the unrestricted source domain.
The dyadic Cauchy/continuous-limit construction and continuous Doob-Meyer
existence, predictability and uniqueness remain open.

The 9598-job incremental build passed. All 19 affected final traces contain
zero warnings/errors. The 90 public declaration/regression axiom checks use
only the standard three axioms. The actual predictable-jump counterexample
is bounded, cadlag, a supermartingale, initially zero and constant after time
one, but its positive-width modulus remains one. Constant arbitrary initial
variables and zero horizons have zero moduli. No full build or push was made.

## Full III.10 Lemma 3 and dyadic foundations (2026-09-10)

The bounded cadlag supermartingale theorem now proves global conditional-modulus
existence, convergence in probability and L2 with totally inaccessible
positive-time jumps, without a terminal stopping time. This covers the printed
Lemma 3 even though the source stopping-time convention permits infinity.
No Class D or zero-initial assumption is needed for this bounded result.

The proof constructs the actual terminal variable `Z`, the cadlag martingale
`M_t = E[Z | F_t]`, and the nonnegative potential `X - M`. Its vanishing means
and a proved future maximal inequality control late increments; compact moduli
at `T + 1` control the remaining increments for widths at most one. There is
no circular compensator input and no TI-jump assumption on the potential.

The actual dyadic predictable parts, their ceiling left-continuous extensions,
adaptation via predecessor measurability, monotonicity and uniform second
moments are implemented. Fixed-mesh actual terminal limits are constructed.
A separate predictable-difference energy theorem derives L2 convergence of
monotone coordinates and bounds terminal differences by conditional tails.
The mesh-Cauchy argument, uniform limit, continuity and continuous Doob-Meyer
decomposition are still open; these definitions and estimates do not close them.

The 9604-job incremental build passed. All 7 affected final traces contain
zero warnings/errors; all 45 public axiom checks use only the standard three
axioms. No full build or GitHub push was performed. The package remains active.

## Actual dyadic mesh L2 convergence and UCP-Cauchy (2026-09-10)

The fixed-mesh terminal identity is now proved at every real time from the
actual discrete martingale closing, the tower property and predecessor
measurability of the ceiling extension. Coarse extensions are predictable
on every finer dyadic grid. Applying the conditional-modulus bounds to the
actual remaining difference proves the terminal-difference energy estimate.
Native L2 Cauchy-Schwarz and existing completeness now construct the actual
terminal L2 limit across meshes.

Two conditional martingale envelopes control the remaining difference as
well as the terminal difference. Their genuine global maximal bound has
second-moment constant 8. Exact common-grid recovery transfers this bound
to all times, without treating a ceiling extension as a martingale or as a
cadlag process. It yields UCP-Cauchy and a common-event locally uniform
Cauchy subsequence of the original dyadic steps.

The actual right limit is the coefficient after the floor index; this does
not change the original ceiling extension. Its right increment is one
conditional decrement or zero and is uniformly bounded by the actual global
modulus on a common event, including time zero. Deterministic locally uniform
limits preserve left continuity and become continuous when these right
errors vanish. The stochastic continuous-limit construction, its closing
martingale and the unbounded/general Doob-Meyer steps remain open.

The 9619-job incremental build passed. All 14 affected final traces have
zero warnings/errors, and all 53 public axiom checks use only the standard
three axioms. No full build or GitHub push was performed.

## Continuous bounded Doob decomposition constructed (2026-09-10)

For a bounded cadlag supermartingale with totally inaccessible positive-time
jumps, `ContinuousBounded.lean` now constructs a continuous predictable increasing
finite-variation process `A`, exactly zero at the initial time. It is the actual
UCP limit of the dyadic predictable parts. An actual L2 closing variable gives
`X_t + A_t = E[L | F_t]` almost surely at every time. Consequently `X + A` is
a genuine uniformly integrable cadlag martingale, and both coordinates have L2
moments. Neither a compensator nor a closing identity is a hypothesis.

Continuity follows by applying existing cadlag completeness to the right-limit
sequence and using the proved vanishing right-error bound to recover the same
limit from the original left-continuous sequence. A locally uniform subsequence
then supplies left continuity as well. Monotone paths and the initial value are
preserved on a common event; exact normalization keeps the UCP limit unchanged.

Continuous finite-variation compensators with a common initial value are unique
up to indistinguishability, without a boundedness hypothesis. The descending
ramp regression first invokes actual existence and then identifies its output
with the nonzero increasing ramp; it retains source initial value 1 and dyadic
UCP convergence. The unbounded Class D extension and general III.11 remain open.

The 9626-job incremental build passed. All 8 affected final traces have no
warnings/errors, and all 19 public/regression axiom checks use only the standard
three axioms. No full build or GitHub push was performed. Work continues on the
remaining source domain; the Semimartingale package is not complete.

## Actual stopping and single-jump localization (2026-09-10)

Seven modules add 39 public definitions/theorems. Arbitrary stopping preserves
right-continuous supermartingales and submartingales under usual conditions,
without Class D or bounded/finite lifetimes. The proof uses the actual
comparison-event stopped-field conditional-expectation identity.

The actual capped open norm exits are finite, monotone and diverge almost
surely. Their stopped paths are bounded only with an explicit common bound on
positive-time jump norms. Without that premise, a jump strictly greater than
twice the level must be at the stopping endpoint; equality is not excluded.
Totally inaccessible jump coverage survives arbitrary pathwise stopping.
For the bounded-jump case, the actual bounded theorem constructs each local
continuous compensator and L2 closing variable. True martingale stopping and
continuous FV uniqueness prove consistency, rather than taking it as input.

An integrable coefficient measurable at its stopped field gives a Class D
single jump, with no finite-lifetime premise. A nonpositive coefficient gives
an actual supermartingale. TI lifetimes give TI positive-time jumps and no
initial activation almost surely. Clipping a nonnegative amplitude by R
produces an actual bounded continuous compensator; the mean residual
`C - min(C,n)` tends to zero. An actual bounded supermartingale difference,
not pointwise order alone, gives monotone compensator differences.

The Protter source was rechecked at printed pp.111--112. The correction
`Xhat = X + Mplus - Mminus` requires the recovered martingale to be
`Mhat - Mplus + Mminus`. The large-amplitude tail need not be bounded by R;
the small-amplitude part is bounded. Two regression checks record these
distinctions. Fatou integrability alone is not used to claim martingality.

The 9633-job incremental build passed. All 8 affected final traces are clean,
and all 41 public/regression axiom checks use only the standard three axioms.
The full unbounded single-jump construction and global Class D patching are
still open, as are general III.11 and later dependencies. No full build or
GitHub push was performed; the package remains in progress.

## Full Protter III.10 completed (2026-09-10)

`ContinuousClassD.lean` now proves the full source continuous-compensator
theorem, not merely its bounded or bounded-jump case. From usual conditions,
a cadlag Class D supermartingale, TI positive-time jumps and X0 =AE0, it
constructs adapted predictable everywhere-continuous increasing/FV A with
exact A0 = 0. The sum X+A is proved a true UI cadlag martingale. A is Class D
with an actual integrable terminal envelope, all-time AE convergence and L1
convergence. Continuous FV uniqueness was already proved and applies here.

The original process and its jump amplitudes may be unbounded. Actual capped
norm exits, restricted TI jump times and the original stopped coefficients'
L1/stopped-field measurability are derived. Each local single-jump correction
uses genuinely constructed compensated martingales, with the corrected
recombination signs. Local compensators and their stopping consistency are
then constructed, not left in the full theorem's inputs. Generic continuous
localization and native Fatou give an integrable increasing part; a separate
coordinate-UI limit argument proves the true martingale property.

The single-jump theorem permits an infinite lifetime and arbitrary integrable
nonnegative amplitude. Actual clipping differences give a maximal mean-tail
bound and UCP-Cauchy convergence. Coordinate monotone L1 convergence closes
its true martingale before its global terminal envelope is constructed.
The continuous-time increasing-process terminal theorem reuses the existing
integer limit and gives Class D, avoiding another terminal selector.

The regression invokes full III.10 on `-Z min(t,1)` for any integrable
nonnegative F0-measurable Z, without a deterministic bound, and identifies
the actual compensator with `Z min(t,1)`. The generic Class D localization
proof is shared with the bounded-jump wrapper rather than duplicated.

The 9646-job incremental build passed. All 14 affected final traces are clean,
and all 27 public/regression axiom checks use only the standard three axioms.
No full build or GitHub push was performed. The Semimartingale package remains
in progress: III.11/III.16, naturality, predictable FV uniqueness, conditional
variation/Rao, compensators/angle bracket and later dependencies remain open.
In particular, the printed III.11 residual's conditional mean-zero predictable
jumps do not imply TI-jump coverage, so III.10 is not applied to it without
an additional proved bridge.

## Integrable variation and predictable jump foundation (2026-09-10)

Whole-half-line extended variation is the supremum over integer compact
intervals, and the original function is measurable in the terminal and ambient
sigma-fields under usual adapted cadlag hypotheses. Integrable variation now
explicitly retains AE finiteness and has the exact finite-lintegral criterion.
Stopping retains endpoint jumps and uses full variation at an infinite lifetime.
Integrable variation is stable under stopping and measurable event masks.

Local integrable variation reuses native `Locally`. Its positive-lifetime mask
does not affect variation because a zero-stopped path is constant. The exact
unmasked localizing-sequence and finite expected stopped-variation criteria are
proved, without a hidden initial-value restriction; locally finite variation
is derived. For an adapted cadlag process with integrable initial value,
integrable variation supplies actual Jordan terminal limits, full-time AE/L1
convergence, Class D and integrable finite stopping values. A deterministic ramp
guards against dropping AE finiteness before `toReal`; a Gaussian random constant
guards against inferring initial integrability from zero variation.

At a positive bounded predictable stopping time, the actual martingale left
limit equals the before-field conditional expectation of its stopped value.
Both the left limit and actual jump are integrable, and the conditional jump
mean is zero. The proof uses actual announcing limits, native Levy convergence
and bounded optional sampling. It does not say the jump itself is zero.

The 9656-job incremental build, 11 clean affected final traces and 44 standard
axiom checks passed. No whole-package build or GitHub push was performed.
III.11, naturality/Yoeurp, predictable FV uniqueness and later requirements
remain open. Printed p120 III.20 omits predictability of A in its displayed
formula; the corrected future theorem must include it. III.19 must also use
actual integrability for signed integrands. These source corrections are not
substitutes for proofs of those theorems.

## Actual mixed-bracket integrable variation (2026-09-10)

For globally bounded cadlag semimartingale M and integrable-variation A, the
actual raw bracket now has integrable variation. The proved global extended
variation bound is `ofReal (2*C) * eVariationOn A univ`. The countably supported
Stieltjes representation reuses A's actual FV jump support and the canonical
bracket; it does not require a new enumeration of M's jumps. Quantitative
compact and global primitive variation bounds retain the stopping endpoint
and do not add an initial atom.

The raw bracket's initial product M0*A0 is retained. With A0 integrable, it
has an actual terminal, whole-half-line AE/L1 convergence and Class D. This
analytic result does not require M to be a martingale and does not prove the
bracket is a martingale. For one positive bounded predictable stopping time,
bounded before-field multipliers of the actual martingale jump are proved
integrable with zero conditional mean and expectation. The predictable-process
consumer retains the same lifetime restriction and only bounds its sampled value.

The 9659-job incremental build passed with 4 clean affected final traces and
10 standard-axiom-only checks. No full build or push was performed. Natural
processes, Yoeurp, predictable FV uniqueness and III.11 remain open.

## Frozen implementation order

1. Active-pin/local/reference audit and ownership decisions.
2. Local martingales, stopping, localization, initial-value source corrections.
3. Deterministic and random partitions; UCP and common-event subsequences.
4. Deterministic Klenke 21.56--21.63 and full zero-QV perturbation.
5. Strong Brownian QV/cross-QV, including Exercise 21.10.1.
6. Remaining Chapter I prerequisites and source bridges.
7. Simple predictable representations and representation-independent integral.
8. Good-integrator continuity and total/ordinary semimartingales.
9. Chapter II integral construction by UCP extension and its properties.
10. General raw QV, random-partition approximation, and Klenke normalization.
11. Ito, Fisk-Stratonovich, stochastic exponential, and core applications.
12. Optional/predictable stopping theory; Class D; Doob-Meyer; Rao.
13. Compensators, angle bracket, fundamental local-martingale theorem.
14. Classical/special decomposition, Girsanov, Kazamaki, Novikov, BD.
15. Exact source ledger, regressions R01--R38, dependency/axiom/build audits.

Every still-unproved step remains open; definitions alone do not close a step.
The all-design gap inventory is maintained in `DESIGN_GAPS.md` as a provisional
working report. It is not the requested post-completion certification until
this package's completion gate has actually passed.

## Naturality foundation and finite mixed sums

Naturality now explicitly requires an actual integrable terminal limit of
every tested raw bracket, with zero mean, and does not hold by vacuous absence
of a supplied terminal. Continuous zero-initial IV processes are natural.
Actual finite mixed sums have terminal-product expectation for bounded M and
merely L1 martingale A, and initial-product-plus-variation domination.
The predictable left-limit and jump conditional identities extend to positive
AE-finite stopping times of UI martingales. Their shared announcing-limit
proof also backs the unchanged bounded API; no infinity fallback is interpreted
as a genuine stopped value. III.13 uniqueness, III.14/Yoeurp and the broader
predictable decomposition are still open.

The incremental build passed 9664 jobs, with 8 clean affected final traces and
25 standard-axiom-only checks. No full build or push was performed.

## Full natural-martingale uniqueness (Protter III.13)

The full III.13 conclusion is proved: an integrable-variation natural process
which is a martingale is indistinguishable from zero. Actual finite mixed sums
converge in L1 to the existing raw bracket under an actual variation dominator,
so its finite-time expectation equals the terminal-product expectation without
requiring A to be L2. Naturality tested against an actually stopped bounded
martingale gives the same bracket zero mean. The cadlag conditional martingale
of `{A_T > 0}` is constructed, not postulated as a certificate; positivity and
the original zero initial mean give coordinate zero, then common-path zero.
III.12's integral characterization, III.14/Yoeurp and predictable FV local
martingale uniqueness remain open. The finite-time test is not a proof of
whole-bracket martingality for arbitrary natural A.

The incremental build passed 9667 jobs, with 4 clean affected final traces and
6 standard-axiom-only checks. No full build or push was performed.

## Natural algebra and actual integral variation

IV negation/scalar multiplication and addition/subtraction are proved with
actual extended-variation finiteness and measurability. Natural processes
are stable under linear operations and indistinguishable adapted replacement,
by transporting actual raw-bracket terminals. Original left-continuous and
caglad real paths are Borel measurable. A bounded positive-time caglad
integrand gives actual stochastic-integral variation at most C times the
integrator variation. IV, actual terminal AE/L1 and Class D follow, with
initial-product integrability explicitly separate from positive-time bounds.
These results do not yet establish III.12 or III.14/Yoeurp.

The incremental build passed 9671 jobs, with 5 clean affected final traces and
17 standard-axiom-only checks. No full build or push was performed.

## Full naturality characterizations (Protter III.12)

The actual integral of an adapted cadlag IV process's left limits against a
bounded cadlag martingale is proved true UI with zero mean. Actual IV envelopes
and integration by parts provide the domination; no bound, L2, martingale or
naturality assumption on A is introduced, and its initial L1 is separate.
The full III.12 iff then follows from constructed actual terminal variables
and their expectation balance. The reverse direction identifies terminals by
actual full-time limit uniqueness, not a supplied equality certificate.

The bracket-martingale characterization preceding III.12 is also complete:
actual stopped tests at arbitrary raw stopping times, including infinity with
the genuine bracket terminal, yield the I.21 criterion and UI. The converse
uses actual bracket IV terminal L1 convergence. III.14/Yoeurp, predictable FV
local-martingale uniqueness and the broader III.11 remain open.

The incremental build passed 9675 jobs, with 5 clean affected final traces and
9 standard-axiom-only checks. No full build or push was performed. Source audit
does not identify the p114 Theorem-25 citation as a proved jump-enumeration
theorem: III.25 is compensator continuity, and self-compensation must not be
assumed at this stage. This is not labeled a confirmed erratum. Independent
predictable Stieltjes duality is the next noncircular dependency to construct.

## Noncircular predictable FV jump coverage (2026-09-11)

The actual variation kernel now has its extended global variation as total
mass and is s-finite by compact finiteness, without assuming finite half-line
mass. General kernels with pointwise finite fibers, or finite fibers on a
countable measurable cover, are proved s-finite. This supplies the genuine
native kernel-composition hypotheses rather than its fallback value.
The existing predictable generators give finite-measure uniqueness from
initial and finite-interval rectangle masses. Native product/trim integration
then proves duality for every nonnegative predictable function. Only one
expected total kernel mass is assumed finite; the other is derived.

For actual increasing adapted processes with an integrable-variation first
process, finite-time L1 and a true martingale difference supply those rectangle
equalities directly. Their Stieltjes integrals therefore have equal expected
values. A continuous locally-FV variation measure is proved to vanish on any
countable set, and a positive unit step has actual variation measure `dirac T`;
activation at zero has zero increment measure. The existing III.10 unit-jump
continuous compensator, after an initial-null monotonicity reset, yields a
fully continuous increasing partner. Thus TI stopping times avoid predictable
sets with countable time fibers. All infinity cases have zero actual unit-jump
variation; no infinite time is evaluated as a finite one.

For predictable FV inputs, an actual predictable initial-null reset gives
everywhere-cadlag FV paths. Their positive jump support is predictable and
fiberwise countable. TI jumps therefore vanish, and the existing III.3
decomposition plus actual ordinary large-jump sequences construct a countable
predictable cover on one common full-measure event. No general compensator,
predictable graph section theorem, naturality, or supplied cover is assumed.
The individual ordinary jump times are shown accessible, not predictable.

The same packet proves naturality of deterministic positive steps directly
from their actual weighted raw bracket, including a discontinuous natural
example. A coefficient multiplying a bounded martingale's jump may now be
merely L1 and before-field measurable at a positive AE-finite predictable time.
III.14 still requires disjoint graph handling and the justified bracket-series
expectation step; Yoeurp, III.15 and general III.11 remain open.

The incremental build passed 9690 jobs, with 16 clean affected final traces and
41 checks using only standard Lean axioms. No full build or push was performed.

## Disjoint predictable jumps and actual series domination (2026-09-11)

Comparison with a predictable time is now measurable before an arbitrary
stopping time under initial completeness alone. Equality and finite equality
are included, without imposing predictability on the second time. These
before-field events permit actual predictable restrictions retaining the least
index of each finite graph point. The finite graphs are pairwise disjoint and
their union is preserved exactly. The positive version removes zero graph
points and has strictly positive lifetimes everywhere, allowing infinity.
Predictable cadlag FV processes therefore have an actually constructed common
AE jump cover with positive, disjoint finite graphs.

Actual positive jumps are bounded by finite whole-halfline variation, using
limits of increments. IV gives L1 stopped jumps without integrability of X0.
Predictable FV inputs have actual before-field measurable stopped jumps even
under AE path assumptions. UI martingale before-field identities now include
infinite lifetimes: the constructed terminal cancels with itself in the actual
jump, whose explicit terminal is zero. Weighted zero-mean identities need only
L1 of the before-field coefficient, not its boundedness or L2.

Disjoint finite lifetime graphs reindex actual series with no summability
assumption for equality; summability and finite absolute-sum bounds are proved
separately. Actual compact jump mass is bounded by compact variation. For a
cadlag path bounded by C, every finite mixed-jump partial sum against an FV
path is bounded by `2 C` times actual global variation, with finiteness explicit
before `toReal`. No candidate envelope or jump-count moment is assumed.
The final DCT/terminal consumer for III.14 is not yet included in this packet.

The incremental build passed 9697 jobs, with 8 clean affected final traces and
24 standard-axiom-only checks. No full build or push was performed.

## Full III.14, bounded-test Yoeurp and III.15 (2026-09-11)

Predictable zero-initial cadlag IV processes are now proved natural, without
supplied covers or bracket terminals. The actual disjoint predictable jump
series has mean-zero L1 terms and an integrable variation envelope. Dominated
convergence gives zero means for the actual raw bracket, and its constructed
actual terminal has zero mean by L1 convergence. The existing naturality
characterization gives a UI actual bracket for bounded cadlag test martingales
(the IV bounded-test Yoeurp conclusion, not a general local extension).

III.15 is proved separately without IV, local IV or initial integrability.
For the existing masked UI localizers, the actual jump-sampling formula
identifies each stopped jump with a before-field measurable L1 variable.
The true predictable-jump conditional identity forces it to vanish. Removing
the localizers and using the constructed positive predictable jump cover gives
continuous paths, hence constancy at the arbitrary initial random value.
Both parts of supplied predictable FV/local-martingale decompositions, and
supplied predictable FV compensating parts, are therefore unique up to
indistinguishability when their FV initial values agree. III.11 uniqueness is
closed; general III.11/III.16 existence remains open.

For III.11 existence, the source residual has conditional mean-zero predictable
jumps, not TI jumps. `ConditionalJumpRemoval.lean` currently takes norms before
using unweighted occurrence windows; this loses the signed cancellation needed
for the residual. Its amplitude-selected jumps also need not remain centered,
so the existing TI Class D localization cannot be reused unchanged. Work on
stopped-expectation continuity and the actual signed conditional modulus does
not yet close those separate proof obligations.

The incremental build passed 9702 jobs, with 6 clean affected final traces and
12 standard-axiom-only checks. No full build or push was performed.

## Regular compact conditional moduli and quasimartingale foundation (2026-09-11)

Class D and zero means of actual positive predictable jumps now imply
left-continuity of expectations along increasing finite stopping times.
The actual L1 limit retains the jump at the predictable strict-limit lifetime;
its independent L1 proof precedes the zero-mean cancellation. This does not
assert that the jump itself vanishes.
Actual cadlag shifted conditional projections and their bounded stopping
identities are constructed from bounded cadlag supermartingales. A common
initial-null reset gives everywhere cadlag, nonnegative, ordered residuals.
The first-threshold estimate uses actual capped hits, Class D continuity and
optional sampling of the upper endpoints. Together with the source modulus
comparison it proves full width-to-zero compact convergence in probability
without a TI hypothesis or a proposed residual/convergence input. The reverse
supremum comparison retains the enlarged horizon `T+delta`. Global convergence,
the regular general Class D construction and general III.11 existence are
not claimed by this packet.

The quasimartingale foundation now includes the actual terminal-zero sum,
extended conditional variation and an adapted, common AE cadlag, coordinate-L1
predicate with finite variation. A nonnegative supermartingale has exact
conditional variation equal to its initial mean. A difference of two such
right-continuous processes is a quasimartingale under usual conditions,
proving III.17's easy direction. The explicit terminal tail supplies the full
halfline estimate; its Bochner default is not used without integrability.
Strict representatives preserve actual sums and expectations within the one
TimePartition owner, proving exact equality with the source strict-partition
supremum. Horizon zero still contributes the initial-to-zero tail. The reverse
III.17 implication and Rao's decomposition remain open.

The incremental build passed 9712 jobs, with 11 clean affected final traces and
35 standard-axiom-only checks. No full build or push was performed.

## Bounded regular decomposition and actual predictable single jumps (2026-09-11)

The regular compact-modulus theorem now extends to the whole half-line:
an internally constructed actual terminal potential controls late increments.
Deterministic boundedness then gives square-integral and native L2 convergence.
The existing dyadic terminal-energy, L2, UCP and closing proofs are factored
through that actual modulus, retaining all six original TI source interfaces.
The bounded regular source theorem constructs a continuous predictable increasing
Doob part and an L2 closing variable, with no supplied modulus, convergence,
terminal or compensator. Its original random initial value is preserved.

Arbitrary stopping preserves the zero means of positive predictable jumps:
the event that the test time precedes the stop is measurable before the test,
and restricting the test preserves predictability. Actual zero-terminal sampling
retains equality at the stopping endpoint and excludes finite evaluation of infinity.
Actual predictable closed futures and graphs now follow from announcing sequences
under initial completeness. A before-measurable coefficient gives a predictable
closed step. A stopped-measurable L1 coefficient minus its before-conditional
expectation gives a true UI single-jump martingale, even for arbitrary stopping times.
At a positive predictable lifetime this constructs a zero-initial predictable
compensator of integrable variation. Its expected actual variation is at most
the original coefficient's first absolute moment. Zero and infinite lifetime
variation are proved zero separately; the coefficient need not vanish at infinity.

Partition refinement increases actual expected conditional variation. More
precisely, positive, negative and absolute conditional-decrement sums are
ordered after conditioning at the initial field. Every terminal-zero tail and
repeated endpoint is retained. The pure cell-sum inequality uses only the
existing partition owner. These are foundations, not Rao's decomposition.
The general regular Class D extension, general III.11/III.16 existence and
III.17 converse remain unimplemented.

The incremental build passed 9722 jobs, with 16 clean affected traces and
35 standard-axiom-only checks, including all six retained TI interfaces.
No full build or push was performed.

## Regular bounded-jump Class D and general single jumps (2026-09-11)

Regular Class D supermartingales with bounded positive jumps now have an
internally constructed continuous predictable increasing Doob part, a true
UI martingale and an actual integrable all-time terminal limit. Values need
not be bounded. Actual capped norm-exit decompositions and their stopped
consistency are constructed; the original TI localization interface remains
unchanged. The general unbounded-jump regular case is still open.

Every L1 coefficient at a positive stopping time now has an actual predictable
cadlag IV single-jump compensator, zero initially almost surely, with expected
variation at most the original first absolute moment and a true UI residual.
The accessible proof constructs the disjoint predictable coefficient series;
the signed TI proof constructs a continuous part. Actual classification into
disjoint stopped events ensures their budgets add without a factor of two.
Signed closed-step series have actual whole-halfline uniform convergence,
cadlag paths, exact predictability, variation bounds and UI martingale closure.
No coefficient must vanish at infinite lifetime; zero terminal sampling is
retained. Zero means at all positive predictable tests imply zero before-
conditional means only with separately proved actual sampled-jump L1.

Actual directed essential suprema now have expectation bounds, with extended
finiteness proved before conversion to integrable real representatives.
Positive/negative fixed-horizon conditional-variation envelopes are constructed
on the original measure. Exact partition horizon extension and shift-prepending
give all-horizon directedness and the original variation bound under shift.
The terminal-zero tails, repeated cells and genuine adaptedness requirement
for the conditional horizon comparison remain explicit. These are foundations
for III.17/Rao, not a claimed decomposition or cadlag envelope version.

The incremental build passed 9738 jobs, with 18 clean affected traces
and 35 standard-axiom-only checks. All rebuilt dependency traces were checked
for warnings and errors. No full build or push was performed. General
III.11/III.16 existence and the other package gaps remain unimplemented.

## Full regular Class D continuous construction (2026-09-11)

The continuous Doob construction is now proved for zero-initial cadlag
Class D supermartingales with zero means of all positive predictable jumps,
without bounds on either values or jump norms. At actual capped norm exits,
the full exit jump has an internally proved L1 stopped-measurable coefficient;
subtracting it leaves a deterministic path bound. Its actual predictable IV
compensator gives a true UI martingale. Actual conditional jump identification
and the predictable FV jump cover bound the compensated residual's jumps.
The bounded-jump regular theorem then constructs a continuous increasing part.
Adding back the true UI martingale preserves that same increasing part.
Actual stopped consistency and the existing Class D patching owner construct
the global part, a true UI martingale, and an integrable whole-time terminal.
No supplied compensator, terminal, coefficient moment, local consistency,
convergence certificate, or total-inaccessibility premise remains.

General integrable jump-envelope sampling and predictable-compensator jump
identification have separate proved interfaces. Class D independently gives
L1 of zero-terminal stopping values and positive predictable jumps, using
finite-lifetime masks and actual announcing limits before subtraction.
The latter results require no finite measure, adaptation or usual conditions.
The broader general III.11 predictable, possibly discontinuous increasing
part still requires its actual predictable jump-mean series construction;
III.16 local existence also remains open.

The actual positive and negative whole-future conditional-variation envelopes
are now constructed on the original measure at each fixed time. The original
global variation bounds their integrals and proves their finiteness before
real conversion. The finite-partition signed sums telescope, and translated
essential upper bounds prove that the two real envelopes differ by X at that
time. This does not yet construct their supermartingale/cadlag versions or Rao.

The incremental build passed 9747 jobs, with 10 clean affected traces
and 16 standard-axiom-only checks. All rebuilt dependency traces were checked
for warnings and errors. No full build or push was performed.

## Predictable reduction prerequisites and dynamic envelopes (2026-09-11)

An actual positive disjoint predictable sequence now covers the nonzero
positive jump at every fixed predictable testing time, almost surely for
that test. The construction uses actual large-jump sequences, each time's
accessible/TI decomposition, accessible predictable covers and legitimate
before-field graph restrictions. It neither exchanges test/AE quantifiers
nor restricts predictable graphs using an unproved before-measurable
jump-amplitude event.

Class D supermartingales now have nonpositive conditional jump means at all
positive predictable lifetimes, including infinity. Actual jump L1 precedes
conditional sampling. Deterministic caps use the actual terminal X_T, and
integer before-field masks cover finite lifetimes; the infinite branch is
proved separately. Removing one actual predictable conditional jump mean
preserves supermartingality, using clamped announcing samples, Class D L1
convergence and the existing genuine centered single-jump martingale.
Actual absolutely summable step series have the exact jump-sum formula,
isolated coefficients on disjoint finite graphs, and monotone paths for
nonnegative coefficients. A uniform lower bound on source expectations
bounds all coefficient moments once the finite corrected sums have been
proved supermartingales. The remaining finite-series induction and full
infinite predictable correction are still required for general III.11.

Actual directed essential suprema preserve their relation on measurable
restrictions. Event-integral tests pass common conditional upper bounds to
their finite L1 real representatives. Applied to source-exact prepended
partitions, this proves the whole-future envelopes' dynamic inequality and
their true supermartingale coordinate interfaces. Cadlag right-limit
construction, the final Rao decomposition, and local III.16 remain open.

The incremental build passed 9754 jobs, with 8 clean affected traces
and 11 standard-axiom-only checks. All rebuilt dependency traces were checked
for warnings and errors. No full build or push was performed.

## General Class D Doob--Meyer and Protter III.17 (2026-09-11)

The general Class D predictable Doob--Meyer construction, III.11, is now
proved. An actual positive disjoint predictable cover gives fixed original
negative conditional jump means. Their coefficients are L1/nonnegative and
vanish at infinite lifetimes. Finite induction proves supermartingality of
every actual corrected sum; the original Class D expectation bound then
proves summability of all coefficient moments. The actual predictable
increasing cadlag series has integrable variation and is Class D. Its sum
with X remains a supermartingale by genuine coordinatewise UI/L1 convergence.
For each positive predictable test, both sampled jumps are L1 and their
expectations cancel over actual disjoint before-measurable collision events.
The covering AE event may depend on the test; no quantifier swap is used.

The full regular continuous theorem constructs the remaining increasing part.
Their sum is predictable, cadlag, exactly zero initially, IV and Class D, with
an actual integrable terminal and full-half-line AE/L1 convergence. Its sum
with X is a true UI martingale retaining X's arbitrary integrable initial
value. No value/jump bound, regularity, TI condition, proposed compensator,
terminal or convergence certificate is a final source premise. Existing
predictable FV uniqueness completes the III.11 uniqueness direction.
A regression with signed random initial value and unbounded integrable random
predictable jump invokes actual existence and identifies the result by that
uniqueness. Its unit jump has mean -1 and is not TI. The monotone terminal-
envelope IV bound has one reusable owner, also consumed by the old TI theorem.

Both directions of III.17 are now proved. Actual positive/negative future
envelopes give nonnegative supermartingale coordinates with the original
variation budget. Their canonical dyadic right limits remain supermartingales
without expectation continuity or individual modification identities. The
countable skeleton gives one common nonnegativity/difference event, and an
algebraic representative gives the exact source identity X = Y - Z with cadlag
coordinates. The source names III.18, not III.17, Rao's theorem. Local III.16
and Rao III.18 remain open, along with compensators and the other package gaps.

The incremental build passed 9764 jobs, with 12 clean affected traces
and 16 standard-axiom-only checks. All rebuilt dependency traces were checked
for warnings and errors. No full build or push was performed.

## General local Doob--Meyer and Rao closure (2026-09-11)

Protter III.16 is now proved on the original cadlag supermartingale domain,
without Class D, regularity, value/jump bounds or a proposed decomposition.
Actual bounded norm exits give Class D stopped supermartingales. The proved
general III.11 construction produces each local part, and predictable FV
uniqueness proves their stopped consistency. Arbitrary stopping preserves the
actual predictable sigma field. The existing UCP completion, a common initial
null reset and the native strong-measurability limit theorem give an actual
predictable cadlag patched process, not merely a claimed predictable version.

The same exit times prove locally integrable variation and give genuine
unmasked UI localizers for X + A; the existing Klenke-to-Protter bridge retains
the positive-lifetime masks. The compensator starts exactly at zero.
Bounded minimum optional sampling and nonnegative Fatou separately prove
finite-time integrability and E[A(t)] <= E[X(0)] - E[X(t)]. No L1 convergence
of the original stopped source is assumed. Subtracting the original constant
martingale gives the exact normalized source form X = X(0) + M - A,
M(0) = A(0) = 0, with uniqueness even against merely predictable FV competitors.

A signed lower source-mean bound, and separately its finite limiting-mean
formulation, construct the actual integrable terminal of A. The whole-half-line
envelope, AE limit, UI, L1 limit and global integrable variation are conclusions.
Rao III.18 applies this result to the two actually constructed nonnegative
supermartingale coordinates of III.17. Their difference gives X = M + A
exactly, with unique local-martingale and predictable variation parts; global
integrable variation strengthens the source's local-IV conclusion.

Local-IV algebra uses the existing native minimum localizer, including its
AE monotonicity. No extra initial integrability is required for variation
congruence, negation, addition or subtraction. The X(t) = -t regression calls
actual III.16 and identifies the constructed compensator as t by uniqueness.
Earlier checkpoint statements that III.16/III.18 were open are superseded here.
General local Yoeurp, compensators, angle bracket, fundamental local-martingale
and subsequent package gates remain open; the package is not complete.

The incremental build passed 9774 jobs. All 11 affected final traces
and the rebuilt dependency closure are clean. All 21 checks in
`Audit/SemimartingalePredictableLocalAxioms.lean` use only standard Lean axioms.
No full build or GitHub push was performed.

## General compensator existence and predictable jump budgets (2026-09-11)

The actual conditional variation satisfies
Var(X) <= E|X(0)| + 2 E[actual total variation]. This direct proof uses each
native partition, conditional-expectation L1 contraction and the explicit
terminal-zero tail. It requires neither finite measure nor usual conditions;
cadlag paths are added only for the quasimartingale consumer. Actual variation
finiteness and measurability are retained before using its real conversion.

Actual Rao existence constructs a predictable global-IV part for a global-IV
adapted cadlag source with initial L1. Its local-martingale remainder has an
actual initial-value-plus-variation integrable envelope, so it is a true UI
martingale. The finite-time compensator mean is E[X(t)] - E[X(0)]; no such
unqualified true-mean identity is inferred from local integrability alone.
Uniqueness allows a competing predictable merely FV part with AE zero initial
value and only a local-martingale remainder.

Native local-IV witnesses produce actual stopped compensators. Their stopped
consistency is proved on the witness's original AE-monotonicity event.
Predictable UCP completion and stopping recovery give the actual local-IV
compensator and local-martingale remainder through native masked localization.
Centering by X(0) and restoring its existing Protter constant local martingale
remove all initial moment assumptions from the final theorem. The compensator
starts exactly at zero. The arbitrary-initial constant regression invokes
actual existence, identifies its compensator with zero by uniqueness, and
rules out a UI remainder for a nonintegrable initial random variable.

For a true UI cadlag martingale, actual zero-terminal jumps at positive
predictable lifetimes are differences of stopped-field and before-field
conditional expectations of an actually constructed UI terminal Z. A bound C
on every finite sum of before-measurable coefficient norms proves
sum E|weighted jump| <= 2 C E|Z| and genuine summability. The actual centered
closed-step series is UI. Coincident and infinite lifetimes are allowed.
No totalized real-tsum budget, proposed terminal, bounded-martingale, L2 or
semimartingale hypothesis is used. This is not yet the general local Yoeurp
extension; its actual variation-budget localization remains separate.

The incremental build passed 9781 jobs with 9 clean affected traces
and a clean rebuilt dependency closure. All 10 checks in
`Audit/SemimartingaleCompensatorExistenceAxioms.lean` use only standard Lean axioms.
The prior local Doob source is rechecked after an EOF-only formatting fix.
No full build or push. Earlier general-compensator-existence gaps are
superseded here; remaining compensator applications and later gates stay open.

## Increasing compensators and actual large-jump foundations (2026-09-11)

An increasing IV source is Class D; applying actual Doob existence to its
negative and predictable FV uniqueness proves that its actual normalized
compensator is increasing. Centering by the original initial value, using
native intersected localizers, and passing to the common divergence event
gives the local-IV result without initial L1. The final existence consumers
construct the compensator before proving this property.

The actual signed and norm large-jump sums run over Ioc(0,t). Compact cadlag
jump finiteness proves their regularity, actual variation bound and exact
jumps. The old enumeration is genuinely summable on each horizon and is
proved equal to the literal sum, including the endpoint. An arbitrary
measurable jump transform need not vanish at zero because the lifetime
indicator stays outside it. An everywhere-cadlag version and usual relative
completeness give adaptedness of the original sums. Stopping and arbitrary
event restriction preserve the signed/norm sums; these identities even allow
an arbitrary real threshold. Infinite lifetimes add no finite-time term.

For a bounded-positive-jump local martingale, centering and the original
initial-value localizer construct bounded masked stopped martingales, hence
a square-integrable fundamental sequence. No initial moment or process-value
bound is assumed. For a UI source and global-IV removed process, predictable
jump conditional expectations and the actual compensator jump cover prove
compensator jump norm <= beta and residual jump norm <= 2 beta. Actual
global compensator existence supplies the final UI residual. The general
local version and actual local-IV property of the large-jump sums are not
claimed by this packet. Jumps of norm exactly beta remain in the residual;
the strict large-jump convention still gives the same non-strict bound.

Incremental verification: 9790 jobs, 10 clean affected/rebuilt traces and
35 standard-axiom-only checks in
`Audit/SemimartingaleLargeJumpCompensatorAxioms.lean`. No full build or push.
Earlier increasing-compensator open statements are superseded by this packet.

## Fundamental decomposition and classical semimartingales (2026-09-11)

For the actual cumulative large-jump norm C, the joint capped norm exits of
C + |M| have a proved overshoot bound C(stopped) <= 2(n+1) + |M(exit)|.
The exit is finite before untopping, and zero exits use C(0)=0 without any
condition on M(0). Bounded optional sampling makes the actual envelope L1
for every true cadlag martingale, not only a UI one. Measurability of actual
stopped variation is proved; the extended bound gives finiteness before
toReal. Both original signed/norm sums therefore have locally integrable
variation. Native stable-bundle localization idempotence, exact event
restriction and stopped-sum identities extend this to every local martingale.

The two original UI fundamental sequences and the predictable part's local-IV
sequence give a common native localization for the compensation jump bound.
Predictable stopping and initial masks retain predictability and true IV;
common divergence recovers the beta/2-beta bounds at all positive times.
Actual local compensator existence removes all initial moment requirements.
Using the actual large-jump sum A and its constructed compensator B gives
D=A-B and N=M-A+B, exact M=N+D, D(0)=0, N(0)=M(0), locally IV D,
two actual local martingales and locally square-integrable N. This is III.29,
with the harmless strict large-jump convention explained in the prior packet.

Centering by the original initial-value local martingale yields the existing
normalized decomposable predicate. Its proved elementary-integrator easy
direction gives the general local-martingale semimartingale result. The new
classical source predicate differs from decomposable only by omitting the L2
localization field. Actual III.29 splits its M into N+D and absorbs D into
the existing FV part, proving classical/decomposable equivalence and III.30.
Actual Rao and local Doob existence give III.31--III.32, including the
submartingale corollary, without Class D or global UI assumptions.
These implications do not prove the converse good-integrator-to-classical
decomposition theorem, which remains with the later package gates.

The incremental build passed 9799 jobs with 10 clean affected/rebuilt
traces. All 24 declarations in `Audit/SemimartingaleFundamentalLocalAxioms.lean`
use only standard Lean axioms. No full build or push. Earlier fundamental
LM-to-SM open statements are superseded; source examples, III.33 and later
special/canonical criteria and the other unfinished gates are not closed here.

## General local-martingale integration and special uniqueness (2026-09-11)

The actual total-variation jump is the norm of the original positive-time
jump. Its capped exits give actual integrable stopped variation bounded by
`n + 1 + C`, hence local IV for adapted cadlag FV processes with positive
jumps bounded by `C`. No initial normalization or moment is assumed.

For a globally IV local martingale with initial L1, bounded adapted-caglad
integration is proved true UI by actual simple approximants, a common L1
variation envelope, coordinate-UI martingale closure and integral Class D.
Native initial-value/variation/integrand localizers then prove local-IV
integration without initial L1 or an integrand bound. Actual III.29 and the
existing locally-L2 theorem yield full Protter III.33. The arbitrary-constant
regression invokes this general theorem, retains `H_0 X_0`, and shows why a
nonintegrable initial product prevents a true-UI conclusion.

The source special predicate requires a predictable FV part in an actual
normalized classical decomposition; it does not redefine semimartingales.
III.34 gives uniqueness of both parts against arbitrary predictable FV
competitors, without variation moments or extra competitor path assumptions.
Actual Rao and local Doob existence show quasimartingales and cadlag
supermartingales are special. Canonical component selection, III.35 and later
criteria remain separate work; no Chapter IV integral is asserted.

The incremental build passed 9805 jobs with 7 clean affected/rebuilt traces.
All 14 declarations in `Audit/SemimartingaleSpecialIntegralAxioms.lean` use
only standard Lean axioms. No full build or push. Earlier III.33 open
statements are superseded, not the other unfinished package gates.

## Actual canonical special parts and III.35 (2026-09-11)

Bounded positive-time jumps of a classical semimartingale give an actual
normalized predictable decomposition, with exact reconstruction, exact zero
initial components, local IV of the predictable part and `C`/`2 C` jump bounds.
The continuous case follows from `C=0` and positive-zero-jump continuity,
not a false condition on the original jump at zero.

The sole canonical selectors are now exposed on the proved special domain.
The canonical martingale includes `X_0`; its companion is predictable FV and
zero-initial almost surely. Reconstruction, uniqueness against all predictable
FV competitors and version invariance are proved. The actual III.35 components
are identified with these selectors, proving their continuous-path and jump
bounds. An arbitrary-initial constant regression constructs specialness before
identifying its parts and rules out true UI when the initial value is not L1.

General local martingales have actual native masked localizations with
integrable whole-half-line envelopes, constructed using III.29 and actual
stopped variation. The original dense running norm supremum commutes with
masked stopping and is locally integrable in the native coordinate-L1 sense.
This supplies the masked III.38 step; source-strength unmasked/terminal-supremum
supplements are tracked separately, with initial integrability handled explicitly.
Actual Poisson inputs have canonical parts equal to their compensated count
and deterministic linear drift. At positive rate the two complete classical
decompositions are not indistinguishable, proved from the time-one second
moment. Together with III.34 this supplies the mathematical R29 distinction.

Source audit: printed p.132 drops a factor of two between `|Delta X| <= 2 X*`
and its running-jump conclusion. The correct bound is `J <= 2 X*`.
III.36--III.37 and general predictable-FV local IV are not declared proved.

The incremental build passed 9812 jobs with 8 clean affected/rebuilt traces.
All 16 declarations in `Audit/SemimartingaleCanonicalSpecialAxioms.lean` use
only standard Lean axioms. No full build or push. Earlier canonical-selection
and III.35 gaps are superseded, not the remaining package gates.

## Signed compensator tests, III.38 and predictable localizers (2026-09-11)

Actual increasing bounded-jump processes, including natural-valued unit-jump
counting inputs, now have unique predictable compensators without an initial
moment or zero-initial assumption. Random integrable positive-jump envelopes
give local IV through the existing total-variation exits with overshoot retained.

Signed predictable rectangle duality proves actual integrability on both
composition-product measures before signed Fubini. The existing variation
kernels inherit it. An actual everywhere-cadlag increasing predictable
compensator is constructed and satisfies these signed tests, under finite
expected absolute integral. This is the corrected III.19 kernel consumer on
the everywhere-good path domain, not full AE-source Chapter II integral
identification. That bridge and the corrected III.20 consumer remain open.

III.38 now includes whole-half-line stopped L1 envelopes and integrability of
the actual terminal running supremum. Native masks allow arbitrary initial
values; the ordinary stopped form explicitly assumes initial L1 and thus
covers the book's zero-initial reduction. The actual all-times jump supremum
includes the initial jump, is compact-finite for cadlag paths and satisfies
the corrected `J <= 2 X*` bound. Jump-grid measurability is not assumed.

Countable predictable infima are proved under actual finite attainment.
A summable-error announcing diagonal gives native finite localizers strictly
before each positive predictable target. Actual before-measurable jump
coefficients and the disjoint predictable cover make the original first
large jump predictable. These are verified ingredients, not yet the final
general predictable-FV local-IV theorem or III.36--III.37 criteria.

The incremental build passed 9823 jobs with 13 clean affected/rebuilt traces.
All 19 declarations in `Audit/SemimartingaleSignedSupremumAxioms.lean` use only
standard Lean axioms. No full build or push. Earlier source-strength III.38
supplement gaps are superseded; the whole package remains in progress.

## General predictable FV local IV and forward specialness criteria (2026-09-11)

The general predictable cadlag FV local-IV step is proved, without initial
moments or a variation-localization premise. Actual threshold jump times
localize; predictable announcing times stop strictly before their jumps;
bounded-jump variation localization and native idempotence complete the proof.
This establishes local IV of the actual canonical FV part. Conversely, an
adapted cadlag locally-IV part in a normalized LM decomposition is actually
compensated, proving equivalence with specialness.

Special semimartingales now have native integrable whole-path envelopes.
Consequently their original running norm and actual all-times running jump
suprema are locally integrable. The latter is proved adapted via rational
positive-threshold events and actual first large jumps, including initial and
terminal endpoints. Its stopping and native-mask identities are exact.
Local coordinate L1 of running jumps gives local IV for an arbitrary adapted
cadlag FV process; generic local coordinate L1 of running norms implies that
of running jumps along the same original localizers. The factor-two regression
has running norm one and running jump norm two on a genuine cadlag path.

Verification: 9832 incremental jobs, 10 clean affected/rebuilt traces and
18 standard-axiom-only declarations in
`Audit/SemimartingalePredictableFVSupremumAxioms.lean`. No full build or push.
Earlier predictable-FV local-IV and jump-supremum measurability gaps are closed.
The reverse III.36--III.37 criteria and BD entry remain separate requirements.

## Classical criteria and actual predictable quadratic variation (2026-09-11)

III.36--III.37 now hold in both directions on the classical semimartingale
domain. Running-jump local L1 and the actual martingale envelope give local
IV of the genuine classical FV part, which is then compensated. No proposed
predictable part, initial moment or reverse BD implication is assumed.

The sole predictable compensator is selected only on the previously proved
domain and agrees with canonical special parts. It preserves common path
equality and has full predictable-FV uniqueness. Its zero-terminal jump at a
totally inaccessible time is AE zero, including the zero/infinite branches.
For sources with only totally inaccessible positive jumps, the actual
compensator is continuous, even without monotonicity of the source. The proof
localizes actual jump conditional expectations, then uses the compensator's
own countable predictable cover. Predictable sources self-compensate only
after subtracting their original initial value.

The actual angle process is this compensator applied to the original raw Q.
Its existence follows from native local coordinate L1 of raw Q, from native
locally-L2 local martingales, or from AE-continuity of a semimartingale.
The latter uses an existing predictable version and common-path transport;
no exceptional raw trajectory is declared predictable. General local-martingale
products and squares minus raw brackets are local martingales, and the actual
angle compensates the square with uniqueness against all normalized
predictable FV competitors.

The corrected continuous identity is angle = raw Q - const(X_0^2), not an
unnormalized equality. Raw Q has its original initial square and the angle
starts exactly at zero. Actual arbitrary-initial constant regressions show
that a nonintegrable initial square prevents true UI, and constant one gives
unequal raw and predictable quadratic variation.

Verification: 9844 incremental jobs, 13 affected / 13 rebuilt clean
traces and 31 standard-axiom-only declarations in
`Audit/SemimartingaleAngleCriteriaAxioms.lean`. No full build or push.
These results supersede the earlier classical converse, III.24--III.25 and
angle-existence gaps, not mixed angle algebra, remaining applications or BD.

## Mixed angle construction and actual Poisson consumers (2026-09-11)

The mixed angle is the same canonical compensator of the original raw mixed
bracket. It has full predictable-FV uniqueness, symmetry and diagonal
agreement, not an increasing-process assertion. Actual local IV of the two
square brackets gives the mixed domain by Kunita--Watanabe and the half-sum
variation bound. Actual measurable variation is finite before conversion.
Native minimum localizers and existing raw stopping identities prove the
local result, including arbitrary initial products. Native locally-L2 inputs
therefore construct their actual mixed angle.

General local-martingale product compensation and its full predictable-FV
competitor characterization are proved on this legal domain. The actual
compensator is linear and commutes with arbitrary stopping. This yields
polarization with a genuinely derived sum-square domain, and square/mixed
angle stopping identities with genuinely constructed stopped domains.
Zero and infinite lifetimes are allowed; the stopping time need not be
predictable. Original initial moments are not assumed.

For an actual Poisson process, count integrability constructs both raw-Q
domains. The proved canonical Poisson decomposition and compensator
coherence identify the count and compensated-count angles with linear drift,
including zero rate. Positive rate gives unequal raw and predictable
brackets by the existing second moment. The original chosen-past independence
hypothesis is retained, not asserted for arbitrary filtration enlargements.

Verification: 9853 incremental jobs, 10 affected / 10 rebuilt clean
traces and 26 standard-axiom-only checks in
`Audit/SemimartingaleMixedAngleAxioms.lean`. No full build or push.
The basic mixed-angle domain/polarization/stopping gaps are closed; further
bilinear and one-sided stopping supplements, remaining applications, measure/filtration change and other package gates are not.

## Continuous, bilinear and one-sided angle supplements (2026-09-11)

Mixed-angle left/right addition and real scaling, source invariance and
one-sided arbitrary stopping are proved for the actual selected processes.
Each changed raw local-IV domain is constructed by existing algebra and
raw identities. No additional predictable-stopping restriction is used.

An adapted AE-continuous FV process has actual local IV and compensator
equal to itself minus the original initial value. This is now a shared
interface used by the continuous square-angle results. One continuous
source similarly makes actual raw mixed covariation continuous FV, hence
gives its actual mixed angle, identified with existing continuous
covariation. The second source does not need its own square angle.
The initial square/product correction remains explicit.

The original mixed cross sums also prove the exact common initial-event
mask identity for the actual raw mixed bracket. This provides a native
localization ingredient, not a proof of general local Yoeurp on its own.

Verification: 9858 incremental jobs, 7 affected / 7 rebuilt
clean traces and 17 standard-axiom-only checks in
`Audit/SemimartingaleAngleSupplementsAxioms.lean`. No full build or push.
Counting/hazard applications, general local Yoeurp, measure/filtration-change
conclusions and other package gates remain open.

## General local Yoeurp and counting processes (2026-09-11)

General local Yoeurp is proved for the original raw mixed covariation of
a native local martingale and a predictable AE-cadlag FV source. Actual
predictable large-jump announcing times and total-variation exits construct
deterministically bounded variation localizations. The actual disjoint jump
cover has finite coefficient budgets, so the existing UI weighted-jump
theorem proves centered actual covariation UI. Raw masks/stopping and
iterated native localization give the general result. Arbitrary initial
products are kept as constant native local martingales, not assumed L1.
A zero-variation random-constant regression tests this boundary.

The nonexplosive counting predicate and its real cadlag/FV consequences
are implemented. Unit jumps derive actual local IV; the sole canonical
compensator gives increasing predictable compensation with full uniqueness.
Original hittingAfter clocks satisfy the count equivalence, positive
finite-strict arrival order, divergence, finite-support count representation
and actual stopping/localizing properties. An eventual infinite tail is
allowed. The existing Poisson process enters this domain; a deterministic
one-jump count is non-Poisson for every rate, has itself as compensator,
and has first arrival one followed by infinite arrivals.

Verification: 9868 incremental jobs, 11 affected / 11 rebuilt
clean traces and 32 standard-axiom-only checks in
`Audit/SemimartingaleCountingYoeurpAxioms.lean`. No full build or push.
This closes general local Yoeurp, not the reverse general arrival
construction, hazard formulas, complete III.19/III.20 consumers or other
package gates.

## Reverse arrivals and predictable integral consumers (2026-09-11)

Extended nonexplosive arrival paths now construct the actual guarded count.
Exact native-hitting recovery includes infinite arrivals. Count adaptedness
is equivalent to all original arrivals being stopping times. For common-AE
valid stopping-time arrivals, initial completeness alone constructs a legal
everywhere-good representative, with one-event recovery of all arrivals
and all-time original guarded counts. No raw explosion fallback is used.

Actual variation-kernel fibers are invariant under common path equality,
and adapted AE-monotone cadlag sources have everywhere-good versions. Signed
kernel compensation now accepts these original AE sources and identifies
the sole canonical compensator. A predictable UCP limit and the actual
integral against a predictable source have genuine predictable versions.
For predictable FV integrators this proves actual local IV and canonical
compensation equal to the integral minus its original initial product.

The finite-time Chapter II signed consumer on everywhere-good increasing
sources proves both centered actual integrals L1 and equality of their
expectations from expected absolute Stieltjes integrability. The integrand
is the original adapted AE-caglad process; predictability of a version and
the finite-window kernel test are derived. The increasing compensator is
constructed internally. No original initial-product moment is inferred.

Verification: 9880 incremental jobs, 12 affected / 12 rebuilt
clean traces and 38 standard-axiom-only checks in
`Audit/SemimartingaleArrivalIntegralAxioms.lean`. No full build or push.
Full AE-source Chapter II consumption, corrected III.20, hazard formulas
and the other package gates remain open.

## Corrected III.19 and III.20 closure (2026-09-11)

The corrected signed-integral theorem now accepts the original adapted
AE-monotone cadlag IV source and adapted AE-caglad integrand. A legal source
kernel version is constructed, but the conclusion concerns the original
actual source integral and the actual canonical-compensator integral.
Expected absolute increment integrability proves L1 and expectation equality
after subtracting the source initial product. Its integrability is not inferred.

The right/left Stieltjes correction is proved for an arbitrary cadlag
integrand and FV integrator, including actual variation-measure integrability
and absolute jump-product summability. General native FV local martingales
have actual local IV by the proved running-supremum criteria. FV specialness
is equivalent to local IV on its adapted cadlag domain.

These results give corrected III.20 for native local M and predictable
cadlag FV A. The original J + [M,A] is identified on one common event with
the actual right-value path integral. It has actual local IV, and its actual
canonical compensator is indistinguishable from J, the original left-value
integral. A genuine predictable version of J is constructed before full
uniqueness is used. J_0 is zero under the process left-limit convention;
the raw bracket supplies M_0 A_0. No initial moment is added.

Verification: 9884 incremental jobs, 5 affected / 5 rebuilt
clean traces and 10 standard-axiom-only checks in
`Audit/SemimartingaleCorrectedIntegralAxioms.lean`. No full build or push.
Hazards, measure/filtration-change applications and the other package gates
are not included in this closure.

## Information and environment semantic checks (2026-09-11)

Closed single-jump natural information is exactly the information of the
original lifetime restricted to occurrence by the observation time. The
survival event is a single unrevealed atom; the endpoint is in the revealed
part. The full measurable-event decomposition is proved without a measure
or usuality. A two-point actual nonmeasurability proof rules out replacing
this raw field by the field of min(lifetime, observation time).

Two actual-integral regressions preserve the original initial product and
the distinction between centered and uncentered L1. In particular a zero
variation kernel and integrable source initial value do not force an
arbitrary original integrand initial product into L1. The actual right-value
compensator formula is exercised on arbitrary initial-measurable constants.

Raw QV/QCov are invariant under absolutely continuous measure changes and
between usual semimartingale filtrations. With one continuous argument,
actual mixed-angle domains and environment invariance are derived as well,
with the same initial product removed. General discontinuous-angle
environment invariance is not asserted; its concrete negative examples and
the CE/hazard formulas remain open.

Verification: 9890 incremental jobs, 6 affected / 6 rebuilt
clean traces and 12 standard-axiom-only checks in
`Audit/SemimartingaleInformationEnvironmentAxioms.lean`. No full build or push.

## Hazard balance and actual angular counterexamples (2026-09-11)

The single-jump raw CE formula is now proved, as are raw right continuity,
right-continuity preservation by null-set enlargement and actual original-L1
CE preservation under genuine completion. Consequently the actual usual
single-jump information and CE formula are proved as well. Occurrence includes
the observation endpoint; strict survival is the unrevealed information atom.

The unique cumulative hazard remains ENNReal. Its denominator is pre-jump
survival, including atoms at the integration time. Positive survival at a
finite horizon gives a finite bound and right continuity after deterministic
capping. Tonelli proves the actual stopped-hazard mean and the strict-survival
increment balance; L1 and real values are obtained only after finiteness.
Initial and infinite lifetime atoms are allowed. Actual predictable hazard
compensation and full general III.21/III.23 remain open.

Three-point probability laws explicitly give the same bounded UI/L2
martingale and raw bracket but actual predictable QV steps of height 1/2
and 1/4. Under the first law, initially revealing the squared jump yields
a larger usual filtration with the same UI/L2 process but actual angle
equal to the squared-jump step, again different. All actual angular domains,
martingale facts and compensator identifications are constructed. This
supersedes the preceding pending finite-model environment examples; failure
of angular-domain existence under an environment change is still separate.

Native local MemLp cannot remove a moment obstruction at a positive time
whose preceding field has only zero-one events: a genuine localizer reaches
that time almost surely. The concrete geometric variable 2^n under parameter
3/4 has mean 3/2 and infinite second moment. Its process-level L1-not-locL2
consumer and the local-martingale filtration-shrinkage example remain open.

Verification: 9902 incremental jobs, 13 affected / 13 rebuilt
clean traces and 49 standard-axiom-only checks in
`Audit/SemimartingaleHazardMomentEnvironmentAxioms.lean`. No full build or push.

## Native moment counterexample and predictable hazard (2026-09-11)

The first example on Protter's printed page 128 is now a complete concrete
process: revealing the centered geometric variable at time one gives an
actual UI martingale in a usual filtration, but no native masked localization
can make it square-integrable. The before-one field is genuinely trivial,
and the established moment obstruction yields the contradiction.
This supersedes the preceding pending first-example process entry.

The companion native local-IV obstruction controls the increment from zero
to a positive deterministic time with zero-one preceding information.
It requires only AE strong measurability of that increment; no initial L1
condition, adaptedness, usuality or path regularity is added.
The reciprocal of an actual uniform (-1,1) sample supplies a symmetric,
singleton-atomless law with infinite absolute first moment. Its completed
filtration-shrinkage process construction, the second example, is still open.

The actual closed count minus its capped stopped hazard is now a UI
martingale in the raw natural filtration when pre-jump survival at the finite
cap is positive. Its original stopped hazard is strongly predictable by the
existing predictable stopping map, without replacement. At zero the remainder
retains the possible count atom; infinite lifetimes are not coerced to a
finite lifetime. Finiteness and actual integral identities remain separately
guarded even though predictability of the total real representative is general.

Uniform integrability survives actual measure completion for every exponent
and measure. True, UI and native local martingales survive genuine usual
augmentation of an already right-continuous raw probability filtration.
The original fundamental sequence and its time-zero masks are preserved.
Canonical capped compensator identification and full III.21/III.23 remain open.

Verification: 9908 incremental jobs, 7 affected / 7 rebuilt
clean traces and 24 standard-axiom-only checks in
`Audit/SemimartingaleNativeMomentAxioms.lean`. No full build or push.

## Filtration-domain counterexamples and actual capped compensation (2026-09-11)

Both examples on Protter's printed page 128 are now concrete verified
processes. The second uses the symmetric reciprocal-uniform variable with
infinite first absolute moment. Its bounded magnitude cutoffs have actual
conditional mean zero in the initially known magnitude field, by reflection
on every such event. The existing magnitude localizer yields a native local
martingale. In the genuine completed usual smaller filtration, the before-one
field has only probability-zero-or-one events; the native moment obstruction
rules out local martingality. The original cadlag FV process remains a
semimartingale there. This closes the previous pending second-example entry.

The geometric model now gives an actual angular-domain loss example.
The larger full-information usual filtration has a constructed local-IV
raw bracket and an actual angle equal to that bracket. The smaller usual
reveal filtration has the same actual raw bracket and original semimartingale,
but local IV of the raw bracket would force the impossible second moment.
This closes domain loss in addition to the earlier finite-model angle changes.

For the capped closed count, the actual adapted/cadlag/global-IV source
domain is constructed on the completed space. Under positive pre-jump
survival at the finite cap, sole canonical compensator uniqueness identifies
the actual compensator with the original stopped hazard. The possible
initial count is retained in the martingale remainder.
The expected stopped hazard and its actual L1 identity now hold at every
finite observation time without that deterministic survival guard.
Closed upper-tail positivity holds at almost every sample; Tonelli then
proves the finite extended expectation before the real-value identity.
The actual uncapped count minus stopped hazard is a true martingale in the
raw natural filtration. On one common event the original stopped hazard is
extended-finite at all finite times, monotone and cadlag; no replacement is
used at null support endpoints. Global UI and unrestricted canonical
compensator identification remain separate. Full general III.21 and
conditional-history III.23 remain open.

Verification: 9916 incremental jobs, 9 affected / 9 rebuilt
clean traces and 25 standard-axiom-only checks in
`Audit/SemimartingaleHazardDomainAxioms.lean`. No full build or push.

## General lifetime compensation and whole-half-line UI (2026-09-11)

The uncapped canonical count's full source domain is now constructed on the
genuinely completed usual natural filtration. Its sole canonical compensator
is indistinguishable from the actual stopped cumulative hazard, without a
finite cap or deterministic positive-survival condition. Integer caps give
pointwise eventual exact recovery for predictability, and the already proved
common-event path regularity supplies monotonicity and cadlag paths.

The actual canonical count minus hazard is uniformly integrable over all
finite times. Monotone convergence proves that the integer supremum of the
existing extended stopped hazards has expectation at most one. It is finite
almost surely and yields a genuine integrable envelope before any real
conversion is used. This closes the previous canonical global-UI gap.

The same uncapped compensator formula is now proved for any measurable
extended lifetime on any probability space, with its law constructed as the
actual pushforward. Native martingality transfers through the actual
measure-preserving lifetime map and exact natural-filtration comap equality.
Adapted/cadlag/global-IV domain evidence, stopping-time measurability,
predictability and the usual-filtration local martingale are all constructed;
none are supplied as conclusion-shaped input certificates. Initial atoms,
infinite lifetimes and finite terminal atoms remain allowed.

This supersedes the previous unrestricted-compensation and canonical-UI
pending entries. Arbitrary-lifetime UI transport is separate work, as are
III.21's native CDF/Stieltjes identification, continuous-law logarithm,
absolute-continuity and exponential-law specializations. General
conditional-history III.23 and the other package gates remain open.

Verification: 9920 incremental jobs, 5 affected / 5 rebuilt clean traces and
8 standard-axiom-only checks in `Audit/SemimartingaleGeneralHazardAxioms.lean`.
No full build or push.

## Native CDF and the actual continuous logarithmic compensator (2026-09-11)

The original extended hazard now has its actual native probability-CDF
Stieltjes formula, with `(0,t]` and `1-F(u-)`. Zero mass at infinity is an
explicit domain guard for interpreting the finite-coordinate map; its
arbitrary fallback at infinity is not treated as a finite observation.
The actual original-space compensated count is now uniformly integrable
through genuine measure-preserving norm-tail transport.

Diffuse lifetime laws have continuous original stopped hazard paths by
two-sided dominated convergence, on one common event. CDF continuity and
the original lifetime law's null-singleton condition are proved equivalent.
The actual logarithm identity uses the existing Stieltjes substitution
theorem and the exact positive-halfline measure restriction, with the
initial value retained in the generic analytic identity. Positive survival
and finite extended hazard precede real conversion; singular continuous
distributions are included. The common-event logarithmic formula transfers
to arbitrary original spaces and identifies the already selected canonical
compensator in the genuine completed usual natural filtration.

Absolute continuity of actual finite positive lifetime restrictions now
constructs a finite weighted hazard measure and a genuine integrable RN
primitive. The original stopped hazard is locally absolutely continuous on
one event, with the infinite-lifetime case treated on each compact interval.
The explicit CDF-function AC input bridge is still separate work.
The native exponential law with arbitrary positive rate forces zero
singleton masses and gives survival exp(-r*t) and actual cumulative hazard
r*t. The original-space exponential compensator consumer remains separate;
the printed unit-rate shorthand is not used for a general rate.

This supersedes the previous UI/CDF/diffuse-log pending entries. The remaining
AC/exponential consumers, conditional-history III.23 and the other package
gates remain open; the whole package is not declared complete.

Verification: 9933 incremental jobs, 14 affected / 14 rebuilt clean traces,
24 standard-axiom-only checks in `Audit/SemimartingaleDiffuseHazardAxioms.lean`.
No full build or push.

## Full III.21 corollaries and source-history boundaries (2026-09-11)

The literal CDF-function absolute-continuity corollary is now proved.
The actual Stieltjes derivative, its genuine interval integrability and
native FTC construct the absolutely continuous restricted Stieltjes measure.
True finite-lifetime map/restriction identities supply the hazard theorem's
measure hypothesis. On any original probability space with a measurable
AE-finite lifetime and compact-interval AC of its actual CDF, both the
original stopped hazard and its same selected canonical compensator have
locally absolutely continuous paths on one common event. No density or
compensator-path regularity is assumed. This closes III.21 Corollary 1.

For the actual native exponential original-space law of any positive rate,
the stopped hazard is pointwise that rate times the actual stopped clock.
The existing canonical compensator is indistinguishable from that process
in the genuine completed usual natural filtration. Finiteness of every
stopped clock is explicit, even at exceptional infinite original lifetimes.
This closes rate-corrected Corollary 2; t-min-tau alone is only the unit-rate case.

Together with the previous CDF integral, continuous-path and logarithmic
identifications, III.21 and its two corollaries are now closed. This entry
supersedes their preceding pending rows, not the remaining package ledger.

Printed pp.122--125 were rechecked for the next task. III.23 uses conditional
survival. The independent-interval formula must include the first interval
and all already completed gaps with consistent indices. Extracted gaps are
absorbing after an infinite arrival, and then no elapsed age is evaluated.
Such actual absorbing gaps need not remain independent even when latent
generating gaps are independent. Actual conditional-history construction,
raw count-information/right-continuity bridges and finite-sum localization
remain to be proved. Hazard-rate/censored-data applications are also separate.

Verification: 9938 incremental jobs, 6 affected / 6 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleHazardCorollariesAxioms.lean`.
No full build or push.

## Kernel hazards and actual finite histories (2026-09-11)

The original extended hazard is jointly measurable in its lifetime kernel
parameter and observation time. Under the actual native composition-product
law it has the positive-arrival expectation. A jointly measurable positive
closed-survival event has full measure and supplies all-time finite values,
monotone paths and cadlag paths together. Real integrability and its exact
mean follow after extended finiteness; global UI of the compensated closed
count follows from an actual integrable integer-supremum envelope.

Raw natural-count events on next-arrival survival are now represented by
the genuine finite arrival history, including the empty history. Actual
interarrival durations are measurable and positive, and their prefix sums
recover every original arrival, including infinity. After an infinite
previous arrival the actual gap remains infinity rather than infinity minus
infinity. Independence of latent durations is not attributed to these gaps.

These are verified III.23 foundations, not its full compensator formula.
Conditional-law pullback, natural-count right continuity, predictability
after history activation, true compensated segment identities and the
localized sum still require their own proofs.

Verification: 9943 incremental jobs, 7 affected / 16 rebuilt clean traces,
14 standard-axiom-only checks in `Audit/SemimartingaleKernelHistoryAxioms.lean`.
No full build or push.

## Actual conditional histories and predictable activation (2026-09-11)

The actual everywhere-valid nonexplosive count has a right-continuous raw
natural filtration: its pathwise no-jump windows make frozen future-event
representatives eventually equal to the original event. This uses countable
set operations, not an intersection/comap exchange. All original arrivals
are stopping times, and each finite history is measurable at its actual
preceding arrival. Empty histories and infinite arrivals are retained.
Actual arrival and absorbing-gap histories generate exactly the same sigma
field by measurable difference/prefix-sum factorization.

Native conditional lifetime distributions now supply original-space hazard
L1/mean, global UI and common-event finite monotone cadlag paths via their
actual joint law. Neither original nor history space needs a standard Borel
assumption. Stopped-field marks are predictable strictly after their stop;
zero initial value gives closed delayed Borel activation. Applying this to
the kernel hazard and stopping at the next calendar lifetime gives the
exact absorbing-gap clock representation, without treating that gap as an
original-filtration stopping time.

Actual bounded-clock stopped hazards are integrable. For ordered bounded
history clocks, their compensated increment integrates to zero on a history
event intersected with earlier survival, by actual kernel Fubini and the
verified fiber martingale. Clocks bounded by their calendar index also
preserve global UI by domination by a genuinely UI family.

These close the preceding pending right-continuity, conditional-law pullback
and delayed-predictability prerequisites. The full original natural-count
compensated segments, localized sum, III.23 identification and its independent
specialization are still separate work; other package gates are unchanged.

Verification: 9950 incremental jobs, 8 affected / 8 rebuilt clean traces,
13 standard-axiom-only checks in `Audit/SemimartingaleActivatedHistoryAxioms.lean`.
No full build or push.

## Safe arrival clocks and original conditional-law identities (2026-09-11)

Native conditional distributions now depend only on the generated history
information as actual evaluated measures on one common event. The proof
uses setwise conditional expectations, finite product-measure extensionality
and native kernel uniqueness. In particular the next actual gap has the
same conditional law given actual arrival history or actual gap history;
no claim about arbitrary history labels is made.

Safe elapsed time subtracts the finite minimum of observation and starting
arrival. It is jointly measurable, monotone and calendar-bounded, and is
zero before an unoccurred or infinite starting arrival. It gives exact
original closed-arrival/gap-event and delayed-hazard identities. Original-
space conditional clock UI and zero history/survival increment integrals
are now proved through the genuine joint law.

Continuous monotone clocks preserve cadlag regularity of monotone
right-continuous real paths. Applying this on the original common-event
conditional hazard path gives simultaneous finite values, monotonicity
and cadlag regularity at safe elapsed times. No measurability of the
starting lifetime is needed for these path facts.

The next step remains the true compensated segment in the full natural
count filtration and its localized sum; the complete III.23 formula and
independent specialization are not yet claimed.

Verification: 9956 incremental jobs, 7 affected / 7 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleArrivalClockAxioms.lean`.
No full build or push.

## Actual stage martingales and locally finite hazard sums (2026-09-11)

Each closed actual arrival indicator minus its actual delayed conditional
gap hazard is a true globally UI martingale in the raw natural count
filtration. The proof derives adaptedness from the preceding-arrival
history and predictable hazard; before the indexed arrival it uses the
exact history/survival testing integral, and afterwards the stage is stopped.

The original positive arrivals form a native localizing sequence for any
measure. Their finite-support indicator sum is the original count, and
stopping at index m caps that count at m+1, including infinite arrival tails.

Each delayed hazard is zero before and at birth. Its exact predictability,
zero initial value and monotone cadlag paths are proved without a path
certificate. On a finite horizon, only indices strictly above the count
vanish. Compact finite support gives genuine summability and local uniform
convergence. The total original hazard is therefore predictable with zero
initial value and common-event monotone cadlag paths; its prefix retains
the current pending stage.

Stopping the count-minus-series at arrival m equals the stopped sum of
compensated indicators through index m. The next stage vanishes even at
its birth endpoint. This identity is pure path algebra, not an assertion
of martingality or compensator uniqueness.

The remaining III.23 steps are total local martingality in the genuine
usual augmentation, identification with the sole canonical compensator,
and the corrected independent-interval specialization. Other package
gates remain open; this is not a package-completion claim.

Verification: 9964 incremental jobs, 9 affected / 9 rebuilt clean traces,
11 standard-axiom-only checks in `Audit/SemimartingaleArrivalSumAxioms.lean`.
No full build or push.

## Canonical conditional arrival compensation (2026-09-11)

The actual count minus its original conditional-hazard series is a local
martingale in the genuine usual natural augmentation. Finite raw UI prefixes
transfer through raw natural right continuity and ordinary stopping; the
birth-endpoint prefix identity gives an actual positive arrival reducing
sequence and the existing canonical masked local-martingale predicate.

The original count's local-IV domain is constructed on the completed space,
without expected-count assumptions. Full compensator uniqueness identifies
the existing sole selector with the actual series. All conditional kernels
are computed on the original probability space before completion. Replacing
arrival history by actual absorbing gap history uses one event of equality
of all countably many evaluated conditional measures, valid at every time.

Pure pathwise identities give the explicit completed-plus-pending formula:
at count k, completed indices are n<k and the current hazard is index k at
elapsed time from its preceding arrival. The initial interval and all arrival
endpoints are retained. The canonical compensator is indistinguishable from
this finite formula on the everywhere-valid nonexplosive arrival domain.

Independent conditional kernels equal their actual marginal laws. Variables
equal only on a measurable history event have equal actual conditional laws
there, as measures on a common event. Positive diverging extended latent
prefixes give valid arrivals; actual absorbing gaps recover latent durations
only with finite past. These foundations do not yet establish the complete
independent specialization or the merely AE-valid representative entry point.
The printed independent corollary's omitted first interval and completed-sum
index remain explicitly corrected in the planned consumer.

Verification: 9972 incremental jobs, 9 affected / 9 rebuilt clean traces,
11 standard-axiom-only checks in `Audit/SemimartingaleArrivalCompensationAxioms.lean`.
No full build or push. Other package gates remain open.

## Independent marginal hazards and arrival representatives (2026-09-11)

The next independent latent duration is independent of its actual preceding
arrival history, by native finite-vector independence and measurable prefix
sums. Its marginal is the actual absorbing gap's conditional law on the
finite-past history event. This local law identity needs neither positivity
nor nonexplosion and does not claim independence of absorbing gaps globally.

Positive independent durations with actual diverging extended prefixes give
the nonexplosive count. At an activated finite observation its past is finite,
so the canonical conditional-hazard series agrees with the original marginal-
hazard series on a single event for all stages and times. The true finite
formula uses every completed duration and one current elapsed-time hazard.
This proves the corrected III.23 independent corollary on the literal-prefix
domain, including the initially empty completed sum and infinite arrival tails.

Indistinguishable coordinatewise strongly measurable processes now have equal
genuine usual natural augmentations for arbitrary measures and metrizable
Borel state spaces. Their raw natural filtrations need not agree. Every actual
adapted nonexplosive count in a usual filtration now has an everywhere-valid
measurable arrival representative; its guarded count and all original hitting
times agree on common full-measure events. No expected-count bound is needed.

The general AE-count compensation consumer still needs to combine this
representative and information transport with canonical compensator congruence;
these foundations alone are not that final formula. Hazard-rate/censored-data
applications and the other package gates remain open.

Verification: 9978 incremental jobs, 7 affected / 7 rebuilt clean traces,
6 standard-axiom-only checks in `Audit/SemimartingaleIndependentArrivalAxioms.lean`.
No full build or push.

## General-count III.23 consumer and application inputs (2026-09-11)

The original AE nonexplosive count now has its genuine natural-usual
compensator domain without a finite count moment. Given adaptation to a usual
source filtration, its actual everywhere-valid arrival representative has
the same count and all original hitting times on common full-measure events.
Equality of the genuine usual natural filtrations and canonical compensator
congruence transport the proved conditional-gap formula to the original
count's sole compensator. The original count selects its completed and pending
terms, and the original probability measure supplies every conditional kernel.
This closes the remaining general-count III.23 entry point on that domain.

For a true real probability density continuous at the queried time, the
conditional short-right-window mass divided by its width now tends to density
over positive closed survival. Finite density mass supplies actual integrability
before the native fundamental theorem of calculus is used. This is the rate
limit, not yet the integral representation of the lifetime compensator.

For arbitrary measurable arrival and censoring lifetimes, the arrival-marked
minimum's restricted pushforward equals the restricted original arrival law.
It is dominated by both the observation law and the arrival law. Ties belong
to arrivals, infinite lifetimes are retained, and no independence or normalized
conditional law is assumed. The explicit density primitive and marked censored
compensator formula remain open, along with the other package gates.

Verification: 9982 incremental jobs, 5 affected / 5 rebuilt clean traces,
5 standard-axiom-only checks in `Audit/SemimartingaleGeneralCountAxioms.lean`.
No full build or push.

## Literal density compensation and cause-specific foundations (2026-09-11)

The actual density of each finite positive lifetime restriction now gives
the original extended hazard as a Lebesgue integral. Positive closed survival
proves its finiteness before real conversion and establishes interval
integrability of density divided by original survival. On the single event
of positive survival at the observed lifetime this applies at every finite
stopped clock. The original-space canonical compensator therefore equals the
literal stopped density integral. Initial atoms and infinite lifetimes remain
allowed, with no uncountable exchange of AE quantifiers or candidate input.

A cause-specific hazard now integrates the actual cause submeasure against
the full observation-law survival denominator. Its self case is exactly the
existing ordinary hazard, not a competing owner. Domination gives finite-cap
bounds. Tonelli and genuine absolute continuity give the actual stopped
extended mean, real L1 and strict-survival increment identity. Dominated
convergence at positive-survival caps and monotonicity give actual cadlag
paths on a common observation-law event, including infinite lifetimes.

The observed pair of marked and complementary closed counts has measurable
coordinates and trivial information on strict survival, and its original
lifetime is a stopping time. Frozen observed histories on the occurrence set,
combined with common later survival of any two surviving paths, prove raw
natural right continuity. No mark is revealed before the jump, and no measure,
positive-lifetime or finite-lifetime premise is used for these information facts.

These results close the ordinary explicit density-primitive application and
supply actual ingredients for marked compensation. The marked martingale,
full censored compensator/density-rate application and other package gates
remain open.

Verification: 9989 incremental jobs, 8 affected / 8 rebuilt clean traces,
22 standard-axiom-only checks in `Audit/SemimartingaleDensityCauseAxioms.lean`.
No full build or push.

## Canonical marked/censored compensation and rate foundations (2026-09-11)

The actual marked count minus its stopped cause hazard is a true martingale
in the original pair's raw natural filtration under any finite measure.
The hazard is predictable even without finite total measure. Actual mean
identities pull back under the original lifetime map, and the genuine
marked count increment has the matching cause mass. Survival information
and frozen post-observation increments prove every conditional test.

The original marked count's actual bounded-jump global IV, common-event
cadlag paths, genuine raw right continuity and usual augmentation now supply
the canonical compensation domain and full uniqueness. Its sole compensator
equals the actual stopped cause hazard. For arbitrary dependent arrival and
censoring lifetimes this uses the law of their minimum for survival and the
original arrival law restricted to arrival before or at censoring for the
cause measure. Ties belong to arrivals; zero and infinite lifetimes remain.

Actual cause-restriction densities yield a literal observation-survival
primitive, first as a finite extended integral and then as a real L1 interval
integral. A common observation-law event identifies every stopped time and
the marked canonical compensator with that primitive. The stopped cause
hazard is also globally UI, from its real integrable integer-supremum envelope;
no coordinate-L1-to-UI shortcut is used.

The exact crude-window decomposition retains paths censored strictly before
arrival inside the window. This term cannot be deleted pointwise. A finite
absolutely continuous real law now has the genuine native RN right-window
rate almost everywhere, by Lebesgue differentiation and actual set integrals.
The remaining step is to prove the extra window rate vanishes almost
everywhere and to connect the printed crude-rate application. This and the
other package gates remain open.

Verification: 9997 incremental jobs, 9 affected / 9 rebuilt clean traces,
13 standard-axiom-only checks in `Audit/SemimartingaleMarkedCompensationAxioms.lean`.
No full build or push.

## Full dependent-censoring rate application (2026-09-11)

The printed-page-124 censoring application now has its actual limiting proof.
Genuine thin-window restricted pushforwards have mass infimum zero and are
dominated by the original real arrival law. A native RN integral bound gives
zero pointwise density infimum almost everywhere; the countable true window
derivative event then forces the actual triangular censoring error rate to
zero. No pointwise monotonicity of chosen RN versions is presumed.

Actual full-real-law absolute continuity first eliminates the original
infinite arrival atom before finite real-window conversion. The exact
cause-plus-wedge decomposition, including finite measure addition guards,
proves the crude right-window quotient tends a.e. to the true cause RN
density divided by joint closed survival. Censoring remains arbitrary and
may be dependent or atomic; ties belong to arrivals. No rate limit at every
time is asserted, and a zero-survival quotient is not a conditional probability.

One measurable nonnegative native RN density now represents every actual
positive-cap restriction before its real pushforward. Thus the original
arrival-law AC hypothesis constructs the density data used by the censored
compensation theorem. The actual crude filter-limit primitive agrees with
that RN primitive at every stopped upper limit, since both differ only on
one deterministic time-null set. Its sole canonical compensator identity
and the original censored-count local-martingale remainder are proved in
the genuine usual natural filtration of both observed causes.

The actual net filter-limit rate has the original arrival RN formula a.e.
The net-equals-crude corollary requires equality only a.e. where joint
survival is positive. A common event of positive closed survival at the
observed lifetime controls every stopped interval; no post-risk-set rate
equality, extra integrability, adaptedness or compensation certificate is
needed. The stronger all-time equality would wrongly exclude ordinary
fixed censoring after its cutoff, and is not the implemented hypothesis.

This closes this censoring-rate example and its stated net-rate corollary,
not general Meyer/Levy classification, independent-censoring rate-factorization,
Girsanov, BD, or the remaining package gates. The general measure-level
compensation theorem still permits initial/infinite arrival atoms; this
full-real-law AC specialization does not.

Verification: 10008 incremental jobs, 12 affected / 12 rebuilt clean traces,
19 standard-axiom-only checks in `Audit/SemimartingaleCrudeCensoringAxioms.lean`.
No full build or push.

## Nonnegative-jump classification and Poisson arrivals (2026-09-11)

Native local martingales with nonnegative positive-time jumps now have zero
jump at every predictable testing lifetime. The actual masked UI reducing
sequence supplies integrable sampled jumps and zero before-field conditional
mean, including infinite test lifetimes with explicit terminal zero.
Nonnegativity gives AE zero, and the original reducing sequence tending to
infinity recovers every positive finite test point. No initial moment, FV,
global jump integrability or assumed classification is used.

The converse from predictable zero tests to the existing countable HasTI
property is proved for any adapted cadlag process under usual conditions,
without finite-measure assumptions. Genuine large-jump sequences of the
actual everywhere-cadlag version provide stopping times and nonzero finite
jump graphs. Each fixed predictable test gets its own allowed null set.
Flattening the true countable coverage and transporting its jump graph
back identifies the original process, with no all-tests AE quantifier swap.

Combining these proves the native LM nonnegative-jump classification and
its continuous-subtraction consumer. On the locally integrable-variation
domain, the sole canonical compensator is continuous exactly when the
source has TI jumps, provided its positive-time jumps are nonnegative.
This hypothesis is weaker than monotone paths, but essential for the
converse: a centered signed jump martingale at a deterministic time has
zero continuous compensator without TI jumps. No initial-value condition
is hidden in the positive-time statement.

Every original finite counting arrival is now proved to be a positive
unit jump on one common event, using the actual count at arrival and
the true strict-before left-limit bound. The actual compensated Poisson
LM and continuous rate drift therefore classify its jumps and each
original hitting arrival as TI in any usual filtration satisfying the
stated whole-past increment independence. Rate zero and infinite arrival
tails are retained; TI does not mean not-accessible in those cases.

Printed page 105 was visually checked: Protter III.4 explicitly uses a
strong Markov Feller process with its natural completed filtration.
The present Poisson interface still states the required past independence;
deriving it from genuine independent increments in the natural filtration
is the next step. General Meyer/Feller and Levy classification, and all
other remaining package gates, are not closed by this packet.

Verification: 10014 incremental jobs, 7 affected / 8 rebuilt clean traces,
8 standard-axiom-only checks in `Audit/SemimartingalePoissonClassificationAxioms.lean`.
No full build or push.

## Genuine usual natural Poisson jump classification (2026-09-11)

The explicit-past Poisson interface now has a genuine natural-filtration
entry point. Native real independent increments imply independence of the
entire original natural past: sorted finite grids recover the true finite
past by telescoping jointly independent increments, then native cylinder
independence passes to every past coordinate. Only coordinate measurability
and AE zero initialization are needed for this generic real-process bridge.

For Poisson, actual natural-number differences become real differences on
the original common monotonicity event. Measurable casting and its exact
natural-floor inverse identify the raw count and real-count natural
filtrations. Arbitrary joint families retain independence under the actual
completion measure; the same Poisson process keeps its laws and path events.
Original right continuity then transfers proved past independence to the
genuine usual augmentation, whose usual conditions and adaptedness are
constructed internally.

Thus the original Poisson jumps and each original hitting arrival are TI
in the genuine usual natural filtration. Original coordinate measurability
is explicit because the original raw natural filtration is used. Rate zero
and infinite arrival tails remain permitted. No alternate realization or
arrival selector is introduced. General cadlag Levy jump classification,
Meyer's strong-Markov/Feller theorem and the other package gates stay open.

Verification: 10020 incremental jobs, 7 affected / 7 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleNaturalPoissonAxioms.lean`.
No full build or push.

## Publication/pause checkpoint — 2026-09-12 (historical)

The actual finite future-increment vector now has its stationary reference
law after every genuinely finite stopping time. Bounded continuous vector
tests have the corresponding conditional mean in the original stopped field.
Inputs are an adapted real process, stationary increments independent of the
specified past, and common-event right continuity. No usualness, initial
normalization, left limits, moments or deterministic stopping bound is added.

Actual sorted adjacent increments, joint independence and telescoping prove
the deterministic vector law. Inserting the original past sigma-field in
the ordered independent family proves the whole-vector past independence.
Countable stopping fibers, actual upper grids and conditional dominated
convergence then give the stopped identity. Original sampled-vector AE
measurability and equality of image measures are proved, with no supplied
random-time law or replacement process.

The original centered dense running supremum also tends to zero along any
shrinking initial-window filter. Its measurable positive-threshold exceedance
events tend to measure zero under finite measure, for arbitrary shrinking
sequences and without moments. General stopped-window control and the
announcing-jump consumer still need verification before general Levy TI can
be concluded. The natural-past bridge retains its actual zero-initial
hypothesis; SII alone does not exclude future information in a random initial value.

Verification: 10027 incremental jobs, 8 affected / 8 rebuilt clean traces,
9 standard-axiom-only checks in `Audit/SemimartingaleSIIStoppingAxioms.lean`.
The user requested publication at this checkpoint and then a pause pending
approval. Work subsequently resumed; this paragraph records the historical
boundary and is not the current package state. No full-library build or
package-completion claim was made. Local drafts excluded at that checkpoint were
`StationaryIndependentIncrements/StoppingWindow.lean`,
`Stopping/SmallWindowSampling.lean` and `Stopping/AnnouncingJumpLimit.lean`.
They are verified and integrated by the next entry.

## Cadlag SII predictable-jump and natural-usual TI closure — 2026-09-16

`StationaryIndependentIncrements/StoppingWindow.lean` identifies the actual
dense post-stopping running-supremum law with its centered initial-window law.
`Stopping/SmallWindowSampling.lean` converts uniform vanishing window tails into
convergence in measure of genuine finite stopping-time samples. The argument
uses outer measure for the process events, retains the endpoint, and assumes
only AE ordering of each approximant.

`Stopping/AnnouncingJumpLimit.lean` turns a finite predictable time's actual
announcing sequence into everywhere-finite stopping times and proves AE
convergence of sampled increments to zero at a zero target and to the genuine
positive-time jump otherwise. `Stopping/FiniteSampleMeasurability.lean` supplies
the required AE measurability of right-continuous samples from coordinate
measurability, first on countable ranges and then through upper dyadic grids.
`StationaryIncrementsCompletion.lean` preserves every increment law under the
actual measure completion.

`StationaryIndependentIncrements/TotallyInaccessibleJumps.lean` combines these
interfaces. At each finite predictable time the sampled increments converge in
measure both to the actual positive-time jump and to zero, so uniqueness forces
that jump to vanish. Integer truncations provide the countable common event
needed for arbitrary possibly-infinite predictable tests; the existing
predictable-test classification then gives actual totally inaccessible jumps.
The final theorem applies to the unchanged measurable, AE-zero-initial cadlag
real SII process in the genuine completed usual augmentation of its own natural
filtration. No arbitrary filtration enlargement, moment assumption, replacement
process, Markov/Feller certificate or value at infinity is used.

This closes the general cadlag real-SII TI consumer. It does not construct a
cadlag realization from the canonical Levy triplet/convolution process, prove
Protter I.4 Levy decomposition, or prove III.4 Meyer's strong-Markov/Feller
theorem; those are distinct remaining gates.

Verification: 10033 incremental jobs, 7 clean production rebuilds and 11
standard-axiom-only checks in
`Audit/SemimartingaleSIIInaccessibleAxioms.lean`. All six production modules
also passed isolated Lean checks with zero diagnostics. No full build or push.

## Canonical density-process foundation — 2026-09-16

`Semimartingale/MeasureChange/DensityProcess.lean` defines the real terminal
Radon--Nikodym density `terminalDensity Q P` and proves its ambient
measurability, pointwise nonnegativity, integrability, total integral and exact
set-integral reconstruction whenever `Q ≪ P`.

For a usual filtration it defines the canonical process as the existing dyadic
right-limit regularization of the terminal density's conditional expectations.
The process is a true `P`-martingale with common-event cadlag paths, is uniformly
integrable, agrees AE with the conditional expectation at every fixed time and
is nonnegative simultaneously at every time on one full-measure event. Its
integral on any `F_t` event is exactly the real `Q` mass. No triviality of
`F_0`, value `Z_0 = 1`, pointwise strict positivity, inverse density,
Girsanov correction, stochastic-exponential identification, classical
decomposition or BD implication is asserted.

Verification: 10034 incremental jobs, 2 clean production rebuilds and all 13
checks in `Audit/SemimartingaleDensityProcessAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. The production file also passed its isolated
checker with zero diagnostics. No full build or push.

## Fixed-time strict positivity of equivalent densities — 2026-09-16

`Semimartingale/MeasureChange/EquivalentDensity.lean` proves that conditional
expectation preserves almost-sure strict positivity for integrable real inputs.
For `Q ≪ P`, the terminal density and every fixed-time coordinate of the
canonical density process are strictly positive `Q`-almost surely. Under the
additional reverse absolute continuity `P ≪ Q`, the corresponding terminal and
fixed-time statements are transported to `P`-almost surely, with a nonzero
corollary.

The single-direction fixed-time proof uses the RN derivative after trimming to
`F_t`; it does not incorrectly treat the terminal density as `F_t`-measurable.
No common full-measure event over all real times, inverse process, stopping-time
positivity or Girsanov theorem is asserted.

Verification: 10035 incremental jobs, 2 clean production rebuilds and all 6
checks in `Audit/SemimartingaleEquivalentDensityAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. The production file also passed its isolated
checker with zero diagnostics. No full build. Two GitHub push retries failed
because `github.com:443` was unreachable; the local commits remain intact.

## Fixed-time reciprocal densities and Bayes formulas — 2026-09-16

`Semimartingale/MeasureChange/ReciprocalBayes.lean` identifies the forward and
reverse canonical density processes as reciprocal at each deterministic time
under equivalent probability measures. The primary equality is `Q`-AE; its
source-measure corollary uses only the reverse absolute-continuity transport.

For one-way `Q ≪ P`, the module proves the division-free Bayes identity
`Z_t E_Q[Y | F_t] = E_P[(dQ/dP)Y | F_t]` for every `Q`-integrable real `Y`.
Fixed-time strict positivity then yields the quotient form `Q`-AE; equivalence
also yields its `P`-AE corollary. The proof uses trimmed RN densities, exact
set-integral identities and conditional pull-out. It does not assert all-time
pathwise reciprocals, stopping-time Bayes or Girsanov.

Verification: 10036 incremental jobs, 2 clean production rebuilds and all 5
checks in `Audit/SemimartingaleReciprocalBayesAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. The production file passed isolated Lean
checking with zero diagnostics. No full build or push.

## Common-event reciprocal density paths — 2026-09-16

`Semimartingale/MeasureChange/PathwiseReciprocal.lean` upgrades the fixed-time
reciprocal identity to indistinguishability of the forward/reverse density
product with the constant-one process. Both factors have càdlàg paths under a
common measure by equivalence; right-continuous modification uniqueness performs
the upgrade without taking an invalid uncountable intersection of AE events.

Consequently, the forward density is strictly positive and nonzero at every
time on one `P`-full-measure event. Its pointwise inverse is indistinguishable
from the reverse canonical density and therefore has càdlàg paths under `P`.
Stopping-time evaluation, left-limit lower localization and Girsanov are not
claimed in this module.

Verification: 10037 incremental jobs, 2 clean production rebuilds and all 5
checks in `Audit/SemimartingalePathwiseReciprocalAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. The production file passed isolated Lean
checking with zero diagnostics. No full build or push.

## Density processes at finite stopping times — 2026-09-16

`Semimartingale/MeasureChange/StoppingDensity.lean` uses the existing arbitrary
closing-variable optional-sampling theorem to identify `Z_T` with the terminal
RN density conditioned on the native `F_T` for every everywhere-finite stopping
time. It proves integrability and the exact identity
`Q(A) = ∫_A Z_T dP` for every `A ∈ F_T`; the terminal density need not be
measurable for the supremum filtration because the established closing
projection theorem handles that distinction.

For one-way `Q ≪ P`, `Z_T > 0` is proved `Q`-AE using the RN derivative after
trimming to `F_T`. Under equivalence it is also `P`-AE, and the reverse sampled
density equals `1 / Z_T` `P`-AE. These are finite-stopping-time results; no
Girsanov local-martingale transfer is claimed.

Verification: 10038 incremental jobs, 2 clean production rebuilds and all 7
checks in `Audit/SemimartingaleStoppingDensityAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. The production file passed isolated Lean
checking with zero diagnostics. No full build or push.

## Equivalent-density localization and left limits — 2026-09-16

`Semimartingale/MeasureChange/EquivalentDensityLocalization.lean` defines the
minimum of the capped norm exits of the forward and reverse canonical density
processes. It proves this is a localizing sequence under both equivalent laws,
with deterministic pre-exit bounds for each density.

Taking left limits of the common-event product-one identity proves that the
positive-time forward and reverse left limits have product one. The forward
left limit is strictly positive on one common `P`-full-measure event, the
reverse left limit is its exact reciprocal, and up to the joint exit both the
forward left limit and its reciprocal are norm-bounded by the integer level.
The time-zero Protter convention `Z_{0-}=0` is retained and excluded explicitly
from division.

Verification: 10039 incremental jobs, 2 clean production rebuilds and all 9
checks in `Audit/SemimartingaleEquivalentDensityLocalizationAxioms.lean` use
only `propext`, `Classical.choice` and `Quot.sound`. The production file passed
isolated Lean checking with zero diagnostics. No full build or push.

## Equivalent-law martingale transfer — 2026-09-16

`Semimartingale/MeasureChange/MartingaleTransfer.lean` proves that if `X` is a
true `Q`-martingale and `P` and `Q` are equivalent, then `Z * X` is a true
`P`-martingale for the canonical density process `Z = dQ/dP`. The proof uses
the division-free conditional Bayes identity and conditional-expectation towers;
it does not divide by a density on an exceptional set.

Uniformly integrable martingales transfer as well. An actual `Q`-integrable
closing variable is multiplied by the terminal RN density and proved
`P`-integrable through the RN integral equivalence, yielding an explicit
closing variable for the transferred process. Local martingales are then
transferred along their original fundamental sequence: convergence and path
regularity move only through `P ≪ Q`, and the native zero-time masks are retained
under the second stop. This module does not yet claim a Girsanov covariation
correction.

Verification: 10040 incremental jobs, 2 clean production rebuilds and all 3
checks in `Audit/SemimartingaleMartingaleTransferAxioms.lean` use only
`propext`, `Classical.choice` and `Quot.sound`. The production file passed
isolated Lean checking with zero diagnostics. No full build or push.

## Equivalent-measure Girsanov--Meyer (Protter III.39) — 2026-09-16

`Semimartingale/MeasureChange/GirsanovMeyer.lean` defines the actual raw
covariation `B=[Z,M]` and the reverse density `W=dP/dQ`. Its canonical
division-free correction is `W B - ∫ B₋ dW`. Integration by parts identifies
that process with `∫ W₋ dB + [W,B]`, and the existing finite-variation theorem
identifies the latter on one common event with the right-value pathwise
Stieltjes integral `∫ W_s dB_s` appearing in Protter III.39.

The auxiliary integral is a `Q`-local martingale by stochastic-integral
invariance under absolute continuity. The new local-martingale density transfer
then proves first that `Z (M-R)` is `P`-local and finally that `M-R` is
`Q`-local. The raw bracket initial value and the project convention for process
left limits show `R_0=M_0` almost surely; no trivial initial sigma-algebra or
claim `Z_0=1` is introduced.

Verification: 10041 incremental jobs, 2 clean production rebuilds and all 11
checks in `Audit/SemimartingaleGirsanovMeyerAxioms.lean` use only `propext`,
`Classical.choice` and `Quot.sound`. The production module passed isolated Lean
checking with zero diagnostics. No full build or push.

## Predictable Girsanov theorem (Protter III.40) — 2026-09-16

`Semimartingale/MeasureChange/PredictableGirsanov.lean` selects `⟨Z,M⟩` as the
project's canonical predictable compensator of `[Z,M]` on its actual locally
integrable-variation domain. The target correction is the stochastic integral
of the reverse density left limit against this predictable bracket. At every
positive time that integrand equals `1/Z_-` on one `Q`-full-measure event; time
zero is deliberately excluded from division and the correction is proved zero
there.

The product argument first proves the right-value companion correction. Under
`Q`, the existing right-value-integral theorem identifies the left correction
as its canonical predictable compensator. The compensated difference is local,
so adding it to the right-corrected local martingale proves III.40. No merely
absolutely-continuous density, zero-density stopping or initial-field
normalization is smuggled into this equivalent-measure theorem.

Verification: 10042 incremental jobs, 2 clean production rebuilds and all 8
checks in `Audit/SemimartingalePredictableGirsanovAxioms.lean` use only
`propext`, `Classical.choice` and `Quot.sound`. The production module passed
isolated Lean checking with zero diagnostics. No full build or push.

## Reference audit

The local Protter source is available as `D:/Math/Teachfile/Books/Protter.pdf`.
Git revalidated the external Brownian snapshot at exact revision
`314f04a34ff75e18fd383917ae7fe7d77beb1b6f`. Its
`BrownianMotion/StochasticIntegral/DoobMeyer.lean` contains unfinished proofs,
as anticipated in the design. It is not an implementation-complete dependency.
No external stochastic-integral or local-martingale hierarchy has been imported.

## Source safeguards

The Protter mask is `{T_n > 0}`. The reverse Klenke bridge restores the constant
term `X_0 1_{T_n = 0}` and requires `Integrable (X 0)`. Finite-time L2 and global
L2 boundedness remain distinct. Deterministic-time UI is not Class D.

## One-way lower-density localization — 2026-09-16

`Semimartingale/MeasureChange/AbsoluteContinuousDensityLocalization.lean`
implements the localization prerequisite in Protter III.41 without assuming
equivalence. The geometric thresholds `2⁻⁽ⁿ⁺¹⁾` are positive, decreasing and
summable. Their open lower-interval first entrances are stopping times in the
usual source filtration and increase pointwise with `n`.

For each deterministic horizon, finite-stopping sampling and the exact density
event integral prove `Q(Rₙ ≤ T) ≤ 2⁻⁽ⁿ⁺¹⁾`. The first Borel--Cantelli lemma,
followed by a countable integer-horizon argument, proves `Rₙ → ∞` `Q`-almost
surely. Strictly before `Rₙ`, `Z` is at least the threshold; cadlag left limits
extend this to every positive `t ≤ Rₙ`, giving positivity and a reciprocal
bound. The time-zero left-limit convention remains excluded explicitly.

This closes zero-density localization only. It does not claim III.41's
predictable correction or III.42's raw-bracket correction and zero-density
jump compensator. Verification: 10043 incremental jobs, a clean isolated
production check and all 12 declarations in
`Audit/SemimartingaleAbsoluteContinuousDensityLocalizationAxioms.lean` checked
with standard Lean axioms only. No full build or push.

## One-way local-martingale density transfer — 2026-09-16

`Semimartingale/MeasureChange/AbsoluteContinuousMartingaleTransfer.lean`
proves finite-stopping integrability equivalence and multiplication/division
Bayes formulas on the native stopping sigma-field for `Q ≪ P`. A bounded
stopping theorem then transfers a stopped density-weighted `P`-UI martingale
to an unweighted `Q`-UI martingale using an actual integrable closing value.

Intersecting the original masked source localizer with the geometric
lower-density exits and deterministic natural-number caps proves the local
criterion: if `densityProcess Q P F * X` is a `P`-local martingale and `X` is
adapted and `P`-cadlag, then `X` is a `Q`-local martingale. Target usualness is
required explicitly for the final local construction; it is not inferred from
absolute continuity. The stopped transfer theorem also handles stopping times
that vanish on a non-null set by retaining their initial branch. No reverse
density or external package is used. This closes the transfer bridge for
III.41; its predictable correction and III.42 remain separate checkpoints.
Verification: 10044 incremental jobs, a clean isolated production check and all 7 declarations in
`Audit/SemimartingaleAbsoluteContinuousMartingaleTransferAxioms.lean` checked
with standard Lean axioms only. No full build or push.

## One-way predictable Girsanov theorem (Protter III.41) — 2026-09-16

`Semimartingale/MeasureChange/AbsoluteContinuousPredictableGirsanov.lean`
proves the merely absolutely-continuous predictable Girsanov theorem without
introducing a reverse density. Under `Q ≪ P`, one target-full-measure event
supports strict positivity of every finite-time density and every positive-time
left limit. The actual reciprocal `1 / Z₋` is adapted and càglàd under `Q`.

For the source-law product calculation, the proof uses globally regular
threshold-clipped reciprocals. On each geometric lower-density window they
agree with `1 / Z₋`; stochastic-integral associativity, integration by parts,
Yoeurp's theorem and bracket-of-integral identities show the stopped weighted
correction is a `P`-local martingale. The one-way stopped density-transfer
theorem then yields the corrected `Q`-local martingale. This is III.41 on the
canonical predictable-covariation domain; III.42's density-killing jump and
its compensator are intentionally not conflated with it.

The production module and aggregate Semimartingale semantic regression pass.
All 13 public declarations in
`Audit/SemimartingaleAbsoluteContinuousPredictableGirsanovAxioms.lean`, plus
the extended 7-declaration transfer audit, report only `propext`,
`Classical.choice` and `Quot.sound`. No full build or push.

## SP-03 final implementation boundary — 2026-09-17

The Semimartingale design is complete at its permitted explicit-disposition
boundary.  SM-B01--SM-B21 now all have final resolved workflow dispositions;
the exact mathematical subitems that remain unavailable are still recorded as
`STILL-BLOCKED` or `DEFERRED`, never as proved surrogates.  R01--R38 close with
30 theorem-level `PASS` rows and 8 `STRUCTURAL-GUARD` rows.

The last production tranche proves Yan separation and the
Bichteler--Dellacherie equivalence, Lenglart--Girsanov III.42, Kazamaki and
Novikov, Protter II.37 stochastic-exponential uniqueness, Klenke 21.70/21.73
normalized candidate uniqueness, Klenke 21.75/21.76, Exercise 21.10.3, and the
R36 continuous adapted zero-QV non-semimartingale counterexample.  It also
provides the exact proved cores for Protter I.52, I.56, Jacod expansion and
Meyer--Feller, with their missing stronger bridges stated explicitly.

Focused incremental checks passed for every added production/audit pair.
`Audit/SemimartingaleCompletionAxioms.lean` passed as an aggregate check: all
18 listed load-bearing declarations report only `propext`, `Classical.choice`,
and `Quot.sound`.  No full-library build was used for this tranche.

The current source boundaries and supersession rules are authoritative in:

- `docs/SEMIMARTINGALE_BLOCKER_LEDGER.md`;
- `docs/SEMIMARTINGALE_PROTTER_LEDGER.md`;
- `docs/SEMIMARTINGALE_KLENKE_LEDGER.md`;
- `docs/SEMIMARTINGALE_REGRESSION_MATRIX.md`.

Remaining unclaimed source mathematics is: I.52's rational-liminf/RN-density
identification, II.5's process-level Jacod preservation theorem, and III.4's
full Meyer--Feller theorem.  Accepted deferred scope is nonsmooth II.41,
canonical Levy cadlag realization/decomposition, Klenke 21.69(ii), and the
stochastic-selection extension of I.56.

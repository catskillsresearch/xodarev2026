# Unimplemented design work — working inventory

Checked against the 11 `StochLean_*_Design_*.pdf` files in `D:/Math`, the local
source tree, `SOURCE_MAP.md`, and `MATHLIB_AUDIT.md`; Semimartingale closure
updated on 2026-09-17 (the other-package coverage review is from 2026-09-07).

**SEMIMARTINGALE IS COMPLETE AT THE DESIGN'S EXPLICIT-DISPOSITION BOUNDARY.**
All 21 design blockers now have final dispositions and R01--R38 are closed.
This wording does not claim the three source bridges still marked
`STILL-BLOCKED`, or any accepted `DEFERRED` scope.  The authoritative closure
records are [SEMIMARTINGALE_BLOCKER_LEDGER.md](SEMIMARTINGALE_BLOCKER_LEDGER.md),
[SEMIMARTINGALE_PROTTER_LEDGER.md](SEMIMARTINGALE_PROTTER_LEDGER.md),
[SEMIMARTINGALE_KLENKE_LEDGER.md](SEMIMARTINGALE_KLENKE_LEDGER.md), and
[SEMIMARTINGALE_REGRESSION_MATRIX.md](SEMIMARTINGALE_REGRESSION_MATRIX.md).
The numbered “Active Semimartingale gaps” narrative below is retained as
historical implementation detail and is superseded by those ledgers.

An explicitly deferred item is still unimplemented, but it is different from
a missing mandatory BUILD theorem. Work transferred to a later package is
counted once under its current owner, not as an independent duplicate project.
This inventory checks coverage and exported declarations; it does not purport
to re-review the mathematics of every previously compiled proof.

The baseline foundation passed two full builds (8966 jobs each). The continuation
adds ten production modules, passes two full builds (8976 jobs each), and expands the
axiom audit to 54 load-bearing declarations, all using only the standard Lean
axioms. Current build/lint evidence is maintained in the active ledger. None
of these checks establishes the still-missing theorems listed below.

## All design documents

| Design document | Unimplemented items and disposition |
| --- | --- |
| `StochLean_Klenke_Ch01-08_Design_v0.1.pdf` | No new missing mandatory BUILD item identified. Explicitly deferred: Kesten 2.46; entropy/source coding 5.25--5.27; Rademacher--Menshov 5.30; Baum--Katz 5.32; Bernstein--Chernoff Exercise 5.2.1; general Lp dual representation 7.47, 7.49, 7.50. These remain unimplemented despite completion at the permitted milestone boundary. |
| `StochLean_ProcessCore_InformationFlow_Design_v0.1.pdf` | Deferred: full Skorokhod topology; adapted + jointly measurable implies existence of a progressive modification (Klenke Remark 25.7). The cadlag path predicate does not construct a Skorokhod topology. The formerly deferred Doob regularization is now proved in Semimartingale under its precise usual-filtration and right-continuous-expectation hypotheses; it is not counted again as missing. |
| `StochLean_DiscreteMatingaleCalculus_Design_v0.1.pdf` | No new missing mandatory item identified. The repository copy spells the filename `DiscreteMartingaleCalculus`. Discrete calculus, internal exchangeability/reverse convergence and de Finetti are implemented; no external exchangeability package is needed. Broader measurable factorization/Doob--Dynkin extensions beyond the implemented empirical-measure/tail tests remain separate work, not an implemented arbitrary factorization theorem. |
| `StochLean_MeasureConvergence_ProjectiveConstruction_Design_v0.1.pdf` | Functional/topological path-space weak convergence is deferred. Coordinate projective construction supplies a raw product law, not sample-path regularity or Skorokhod convergence. |
| `StochLean_MarkovProcesses_Design_v0.1.pdf` | Shared gaps with the consolidated Markov design: Feller pointwise-to-sup-norm strong-continuity equivalence; Klenke 21.27 RCLL strong-Markov realization. MCMC applications and spectral convergence rates are deferred. |
| `StochLean_MarkovProcesses_Kernels_Semigroups_Design_v0.1.pdf` | MK-B04/MK-B05 remain deferred for exact source-proof recovery: Revuz--Yor III Proposition 2.4 and Rogers--Williams III.7ff/8ff or Revuz--Yor III Theorem 2.7. Existing C0 contraction/semigroup and countable-chain convergence APIs do not imply those stronger conclusions. Semimartingales/integration transferred to the active package; stochastic differentials/SDEs remain in the separate planned package. |
| `StochLean_FourierProbability_ClassicalLimitTheorems_Design_v0.1.pdf` | FP-B03 remains a genuine open BUILD-CANDIDATE: exact Polya criterion, moment determinacy and the even-derivative converse. Deferred: Bochner, Berry--Esseen, Lindeberg--Feller converse, functional CLT/Donsker. The former LSII/Brownian forward references have later implementations and must not be counted again as wholly missing. |
| `StochLean_Levy_StationaryIndependentIncrements_Design_v0.1.pdf` | **Mandatory mathematical gap:** the corrected Remark 16.23 stable Gamma/trigonometric exponent formula has not been proved equal to `LevyTriplet.exponent` for the classified stable jump measure, with the correct location/truncation term. Defining `stableExponentWithLocation`, proving continuity and disproving the location-free shorthand do not supply this integral identity. Deferred: null-array ID 16.12--16.13; domains of attraction 16.26--16.30; cadlag Levy realization; PPP/Levy--Ito; Skorokhod weak convergence; Levy stochastic integration; multidimensional/LCA Levy--Khintchine. Some cadlag/decomposition material is now active in Protter I.4. |
| `StochLean_BrownianMotion_PathRegularity_Design_v0.2.pdf` | The specified construction/path-regularity milestone is implemented at its boundary. Still outside that completed boundary: general-SII regularization, Feller path realization, Donsker/functional weak convergence and LIL/Skorokhod. Precise Doob regularization, native Brownian all-times strong QV/cross-QV, the Chapter II integral and the canonical general semimartingale square/mixed bracket are now constructed in Semimartingale; the remaining integration and bracket applications are still open. |
| `StochLean_ContinuousMartingales_QuadraticVariation_Design_v0.1.pdf` | **Superseded by Semimartingale**, not independently complete. Its partition/QV, continuous-local-martingale, stopping/L2 and weighted-sum obligations survive in the active package. Do not create a second continuous-martingale bracket to satisfy this obsolete owner. |
| `StochLean_Semimartingale_Core_Design_v0.1.pdf` | **Implementation contract complete at explicit-disposition boundary.** The Chapter-II integral/brackets, Doob--Meyer/Rao/compensation, change of measure through III.42, stochastic-exponential existence and uniqueness, Kazamaki/Novikov, Bichteler--Dellacherie, Klenke 21.70--21.76 and Exercises 21.10.1--3, exact source ledgers, and R01--R38 closure are implemented. `STILL-BLOCKED`: I.52's explicit rational-liminf/RN identification, II.5's process-level Jacod preservation theorem, and III.4's full Meyer--Feller theorem. `DEFERRED`: nonsmooth II.41, canonical Levy cadlag realization/decomposition, Klenke 21.69(ii), and I.56 stochastic selection. |

## Active Semimartingale gaps

1. Deterministic Klenke 21.56--21.63 is now closed at the stated scope. A
   continuous-path example has no real QV limit along one genuinely nested
   admissible sequence, with even/odd square sums separated by a fixed gap.
   Fixed finite endpoint insertions are proved to preserve QV limits, so every
   alternating high/low step retains all old endpoints. Full-sequence partition dependence is
   proved by a continuous path with QV zero and one at the same horizon along
   two genuine nested admissible infinite sequences. The universal-event
   quantifier swap in Brownian QV is disproved. Klenke 21.62 C1
   composition is proved with the actual Stieltjes integral, continuous increasing
   zero-starting limit, and no input-FV, C2 or weighted-certificate assumption. Exponent comparison,
   one-variation refinement/limit, limiting covariation FV with exact infinite-
   restriction transport, and completed-cell dense-to-all-times extraction are proved.
2. Native Brownian strong QV/cross-QV is now closed, including the actual reverse
   martingale and one probability-one event for every time, for each prescribed
   admissible sequence. Concrete dyadic admissibility and Protter I.29 infinite
   variation on every nondegenerate interval are proved. The general stochastic
   bracket and random-partition UCP theorem are now proved by the separate
   canonical Chapter II construction below, not by redefining the Brownian owner.
3. Remaining Protter I: regularization,
   cadlag Levy construction/decomposition, remaining FV/Stieltjes calculus and source bridges.
   Continuous-time Doob bounds on arbitrary finite sampling sets and the actual
   dense-grid L2 supremum are now proved. A measurable L2 envelope controls all
   times in a finite interval on one right-continuity event, with the constant
   four second-moment estimate and the initial value retained. This prerequisite
   does not close general II.27 Corollaries 3--4 or supply an infinite terminal value.
   The forward direction of II.27 Corollary 3 is now proved: true cadlag
   martingales square-integrable at each finite time have integrable raw
   brackets with exactly the same expectations as their squares. No bracket
   moment is assumed; localization, Doob, Fatou and DCT prove it. The reverse
   implication on the existing semimartingale domain and Corollary 4's
   terminal convergence are completed below; general LM-to-SM remains open.
   The reverse direction's L2 localization step is now constructed for a local
   martingale with an actual semimartingale witness. Raw-bracket jump bounds
   include the initial jump, and left-limit cutoffs handle overshoot with the
   envelope `n + sqrt([X,X]_T)`. Integrable brackets force initial L2 and make
   each masked stopped localizer a true L2 martingale. Promotion of the original
   process is now proved by the uniform Doob/Fatou maximal estimate. Thus the
   full finite-time moment equivalence holds on the actual semimartingale domain,
   and automatically for continuous local martingales using the existing
   semimartingale construction. The compensated square is a true martingale
   for true finite-time L2 cadlag martingales. The general LM-to-SM bridge
   remains open; Corollary 4 is completed below on the actual bracket domain.
   The normalized continuous-bracket finite-time interfaces are also proved:
   Klenke 21.70(ii), the second-moment difference formula and the L2 equivalence
   with initial L2 explicitly included, closing Corollary 21.76. A zero normalized bracket does not
   bypass the initial condition; compensated Poisson disproves applying the
   continuous-path compensated-square result to jumps. This does not close
   the remaining Klenke 21.70--21.76 interfaces or any infinite-terminal claim.
   The extended terminal raw bracket now has a measurable owner, common-event
   half-line limit and monotone-convergence expectation identity. Finite
   expected terminal energy proves a true L2 martingale with uniformly bounded
   finite-time second moments.
   The converse terminal-energy implication and full global L2 equivalence
   are now proved on the existing semimartingale domain. A global Doob L2
   envelope controls all times on one event.
   An actual L2 closing variable has now been constructed with integer-time
   AE/L2 convergence, all-real-time conditional-expectation closure and the
   exact raw terminal-energy moment identity. Whole-half-line L2 and AE
   convergence are now proved by contraction and tail Doob/Borel-Cantelli
   control. Corollary 4 is implemented on the actual semimartingale domain,
   with automatic CLM entry; removing the general LM witness still requires
   III.30. General L1-bounded right-continuous submartingale/supermartingale
   half-line convergence is now proved, with an actual integrable limit and
   no UI or L2 premise. L1 convergence and a closing identity do not follow
   from this weaker hypothesis and are not asserted.
   Explicit terminal-valued stopping is now defined, retaining finite-time
   evaluation and using the supplied variable only at infinity. Its finite
   truncations converge under the actual full-time limit hypothesis. The
   possibly-infinite optional-sampling identities are now proved for a UI
   martingale with its actual terminal limit, including AE-only ordering and
   Lp transfer. A finite-energy entry constructs the terminal/UI hypotheses
   and yields L2 stopped values. General UI terminal construction is now proved
   without L2: the actual terminal variable has full-half-line AE/L1 convergence
   and closes every finite coordinate. The UI optional-sampling entry now
   constructs it without a limit premise. Supermartingale/arbitrary-closing
   source convention at infinite times differs where the book's ambient-event
   stopping sigma-field is larger than the native owner. The arbitrary-closing
   projection in I.10 and explicit extended-index martingale/UI equivalence
   in I.13 are now proved. The terminal filtration is `iSup F`, agrees with
   native stopping at infinity, and does not erase the initial value.
   I.16's native-owner martingale correction now accepts arbitrary integrable
   closing input: projected terminal values are integrable, represented by
   the original input's conditional expectations and satisfy AE-ordered
   optional sampling. The unprojected formula has an explicit terminal-field
   measurability premise. A usual two-point counterexample rejects dropping it;
   no second ambient stopping owner is introduced. Closed-supermartingale
   sampling at unbounded stopping times is now proved with the same native
   terminal projection correction and explicit unprojected measurability guard.
   One-sided martingale reindexing and finite-partition Doob upcrossing estimates
   are now proved, including measurability, integrability, strict terminal-index
   handling and the finite-measure first-moment bound. Native-count monotone
   sampling and endpoint-inclusion refinement, including growing horizons,
   are now proved; repetitions do not change the count. The dense-grid global
   expectation bound and simultaneous rational-level finiteness are proved.
   Right continuity transfers late visits to the expanding grids; their maximal
   count rules out oscillations between integers and closes general non-UI I.10.
   The separate I.9 cadlag regularization construction is now also proved below.
   Bounded stopping-value integrability for both one-sided classes is now
   proved from finite-time first moments and one common right-continuity event.
   Countable-range terminal conditional bounds and finite-partition expected
   sampling monotonicity are also proved. The general continuous two-stopping-time
   inequality in I.17 is now proved from the actual decreasing dyadic upper
   approximations, their derived UI, L1 convergence and finite conditional
   inequalities. Progressive versions and usual-condition original-process
   interfaces are provided, including AE ordering and AE deterministic bounds.
   The lower closing bound now passes to arbitrary bounded times and gives
   horizon-independent first-moment control. The actual integrable full-time
   limit dominates the lower closing input's terminal projection, which need
   not equal that limit. Stopped values using either terminal convention are
   integrable at arbitrary, possibly infinite stopping times. The unbounded
   two-time conditional inequality of closed-supermartingale I.16 is now proved:
   signed Fatou handles the later time, finite-event restriction handles the
   earlier time, and a terminal-measurable indicator handles the event where
   both are infinite. AE ordering and the nonnegative zero-terminal corollary
   are included. Neither UI nor equality of closing input and actual limit is inferred.
   Reverse-supermartingale UI from an upper expectation bound, and the dual
   reverse-submartingale theorem, are now proved with exact conditional-residual
   L1 identities. These require neither sign nor L2 assumptions. Transport to
   decreasing stopping approximations and the final conditional passage are
   now completed. UI of one approximation sequence is not silently upgraded
   to Class D or UI over all bounded stopping times.
   The second corollary to I.18 (commuting conditional expectations at any two
   stopping times) is now proved directly from native stopping sigma-fields,
   including unordered and infinite times. No path regularization is assumed
   in that proof. I.9 is now proved in both directions: under usual conditions
   a cadlag modification exists exactly when expectations are right-continuous. The
   proof derives UI for antitone deterministic samples and their L1 convergence
   on right-continuous paths, without a global first-moment bound. The converse
   constructs the actual simultaneous cadlag modification. A proper
   supermartingale with an isolated initial drop has no right-continuous
   modification; simply taking its right limits changes the initial value.
   Signed weak maximal estimates now give local boundedness of any countable
   deterministic skeleton without path regularity. Local first-moment bounds
   give finite rational-level upcrossings for the clipped process on all integer
   horizons, on one common event. The deterministic dense-skeleton extension
   is now constructed and proved a modification under right-continuous expectations.
   Every bounded monotone or antitone sequence in the existing dyadic skeleton
   now converges on one common event. The sequence quantifier is inside that
   event. The proof uses finite-prefix embeddings and the corrected N+1 cutoff
   for reversed native upcrossings. A generic alternating-selection argument
   now identifies actual one-sided filter limits, and closed neighborhoods
   prove their right-limit extension cadlag. The canonical selector uses only
   the existing dyadic skeleton. Adaptation, L1 sampling and the modification
   identity under right-continuous expectations are proved, together with
   same-class preservation, uniqueness among right-continuous versions and
   the true-martingale/cadlag corollaries. The isolated-initial-drop
   example produces a cadlag extension but not a modification.
   Protter I.21 is now proved using every stopped value, including the explicit
   terminal value at infinity: common expected values imply conditional closure,
   martingality and UI. The zero-mean source statement is a corollary. This does
   not identify an arbitrary closing input with the actual terminal path limit.
   Both convex process-transform corollaries of I.19 are now proved by reusing
   native conditional Jensen. The nondecreasing-map and transformed-integrability
   guards are explicit and regression-tested. General nonnegative-submartingale
   whole-half-line strong Doob control for every real p > 1 (I.20) is now proved,
   including coordinatewise AE positivity and the Banach-martingale norm form.
   A finite uniform Lp bound constructs an actual measurable maximal envelope;
   the general extended inequality does not assume finiteness, UI or L2.
   Five regressions preserve the path-regularity, strict-exponent, infinity
   and initial-value boundaries. The independent proofs of regularization and
   one-sided optional sampling have now also been supplied.
   Weak L1 Doob bounds now cover arbitrary finite sampling sets, extended dense
   suprema and every time on a finite horizon, using only first moments. This
   extends to the whole half-line and to closing-error tail bounds. Vanishing
   probabilities of arbitrarily late deviations and countably many scales
   close the general UI half-line limit gate, not merely integer convergence.
   The adapted total/positive/negative variation processes, locally finite random
   Stieltjes measures and their finite-horizon filtration measurability are now proved.
   The actual pathwise integral has initial-term, linearity, variation-bound,
   dominated-convergence, measurability and progressive-integrand adaptedness theorems.
   Local pathwise integrability now also gives cadlag/FV integral paths and the
   semimartingale property. Primitive one-sided limits retain atoms correctly;
   their jumps are the atom mass times the integrand. Full source elementary agreement
   and finite-step integrability are now proved, with repeated endpoints and unbounded
   finite random coefficients. Adapted everywhere-caglad integrands now have derived
   compact bounds and local pathwise integrability, with progressive FV integrals.
   The full FV integral jump identity is now proved, including the initial jump and
   a common probability-one event for all times. This does not close the general integral jump theorem.
   Both FV integral stopping identities now hold for arbitrary possibly infinite
   random times. Canonical variation measures restrict to the closed stopping
   horizon, and stopping-time cutoff preserves the adapted-caglad/predictable domain.
   These are FV instances, not a construction of the general Chapter II integral.
   FV integral path-locality, indistinguishability invariance, compact-uniform
   continuity and UCP continuity on the adapted-caglad class are now proved.
   Given source simple approximations, their elementary integrals converge to
   the FV integral; this does not prove the existence of those approximations.
   Protter I.54 continuous-FV C1 change of variables, BV preservation and its
   oriented-interval substitution corollary are now proved, using actual Riemann
   sums. Protter I.53 now also permits arbitrary within-cell tags and sample-dependent
   finite partitions on one common event, with uniform convergence over the fixed horizon.
   Protter II.31's discontinuous-FV C1 change of variables is now proved
   directly from endpoint-pair Stieltjes sums and actual countably supported
   integrals, including absolute jump-remainder summability, FV preservation,
   right-continuous source inputs and the raw Chapter II initial correction.
   Protter II.32's continuous-semimartingale Itô formula and C2 preservation
   corollary are now proved from exact Taylor sums and raw QV convergence.
   No moment or global derivative bound is assumed. The general cadlag
   raw-bracket Itô identity, absolutely summable/FV jump corrections and
   general C2 semimartingale preservation are now proved as well. The equivalent
   continuous-bracket formula is also proved by the genuine continuous/atomic
   integral decomposition, closing II.32. The multidimensional extension II.33 is also proved;
   its Frechet Taylor remainder/coefficient, metric cadlag separators, vector
   partition jump-series limits and common-event absolute jump-correction
   summability, full raw-/continuous-bracket vector stochastic formulas and C2
   semimartingale preservation are proved. Mixed integrals retain their initial
   product in the proved continuous/jump split. Protter II.34's source
   Fisk--Stratonovich definition, C3 chain rule and integration-by-parts corollary
   are proved, including continuous-covariation integral/chain rules, jump identities
   and zero correction with a finite-variation argument. Stochastic-exponential
   uniqueness remains open; the multidimensional Levy characterization is proved below.
   The real filtered Levy equivalence (II.39) is proved. The exponential product's convergence,
   zero-factor criterion, equivalence of source expressions, and continuous-case
   semimartingale existence and integral equation are proved. General cadlag
   paths and the positive-time exponential jump identity are now proved.
   The actual product factor has local finite variation and equals one plus
   its absolutely convergent actual jump series, including zero/negative factors.
   General adaptedness and semimartingale preservation are now proved through
   the actual squared-jump kernel, capped path measurability and a zero-guarded
   complex-log product representation. The jump-case integral equation is proved;
   uniqueness remains open.
   The complex Ito foundation has proved coordinate gradient/Hessian identities,
   complex path/left-limit wrappers, coordinate semimartingales, complex integration
   assembled from real integrals, real-linear commutation and analytic preservation.
   The actual II.35--II.36 stochastic identities are proved, with canonical
   bilinear complex brackets, distinct nonnegative real energy, all four Hessian
   entries, absolutely convergent actual jump corrections and a zero-plus
   raw/continuous-bracket integral comparison preserving raw initial squares.
   The I.52 random differentiation/polar-density theorem and impossibility examples remain open.
   Deterministic UI stopping, cadlag martingale-to-local and integrable-envelope
   criteria, Brownian natural-filtration and square-minus-time martingales are proved.
   Brownian source-filtration transfer is now proved on the genuinely completed
   usual augmentation: actual laws/paths, independent future increments,
   martingale/CLM/semimartingale properties and the canonical time bracket.
   The natural-filtration entry point derives its independence condition.
   Arbitrary information enlargement remains excluded.
   Bounded continuous-time martingale sampling, actual closed/UI equivalence,
   arbitrary UI stopping and UI families of AE-finite stopping values are also proved.
   Local-martingale linear and stopping stability now use actual common minimum
   fundamental sequences, including the original time-zero masks.
   I.48(a--e), I.50 and I.49 on the cadlag domain are proved, as is UI sampling
   at unbounded AE-finite times with AE ordering. Infinite terminal sampling and
   full half-line path convergence are not consequences claimed by these results.
   Corrected Klenke 21.67 bounded/centered localization, including refinement up to
   a random lifetime, and the continuous-local/locally-L2 bridge are now proved.
   Actual bounded masked witnesses handle nonintegrable initial values; AE-monotone
   source sequences are normalized on a single initial null event.
4. Full Protter II stability/examples and remaining properties of the stochastic integral,
   including local-martingale/martingale preservation and Riemann approximations.
   The following paragraphs record the completed stopping, jump, invariance,
   FV-agreement, associativity and semimartingale-preservation substeps.
   The sharp random-stopping-partition elementary L2 estimate now retains the
   initial term and proves the actual finite-time L2, locally L2 cadlag and CLM
   semimartingale examples. Small-event patching, strict-before-lifetime agreement
   and masked pre-localization are proved. FV/Poisson/decomposable examples,
   absolute-continuous finite-measure changes, countable mixtures and Stricker
   filtration shrinkage are now proved. Exact `T-` patching also permits
   indistinguishability. Source simple-process adaptedness, everywhere-caglad paths
   and canonical predictability are proved. Actual common stopping-time refinement,
   zero-preserving Borel algebra operations and elementary bilinearity are now
   proved for the full source class, including unbounded finite coefficients,
   repeated endpoints and independent initial terms. Source cutoff closure and
   elementary stopping now hold even for infinite stopping times and arbitrary
   integrators, yielding actual good-integrator and total/ordinary semimartingale
   stopping stability. Brownian source-filtration transfer to the genuine
   completed usual augmentation is proved. Jacod expansion and Levy examples
   remain open. General-integral stopping is not
   claimed by its elementary precursor.
   The exact source submodule/elementary linear map and uniform-to-in-measure
   continuity at every simple limit are now available, with uniform Cauchy estimates.
   They do not supply UCP completeness or select the general integral's limit.
   Right-continuous open-target hitting, the usual AE-path version and first-exit
   bounds are now proved as maximal/density prerequisites. The printed II.10
   approximation's missing first interval is recorded with a constant-path
   regression; the corrected density implementation now includes that interval.
   The canonical source elementary process `J_X(H)` now has initial/terminal values,
   source linearity, adaptedness/cadlag regularity, stopping/cutoff and FV agreement.
   Its maximal estimate and full source UCP continuity (Protter II.11) are now
   proved under usual conditions, with actual bounded first-exit truncations,
   initial masks and UCP-Cauchy control. UCP completeness is now proved;
   the general stochastic integral is constructed in the extension increment below.
   Right-limit cadlag/adapted bridges and finite/extended-time nonaccumulation of
   separated samples are proved. Actual recursive oscillation stopping times,
   finite capped partitions and the corrected II.10 source density theorem are now
   implemented under usual conditions and a finite measure. The source initial term,
   all cells starting at index zero and unbounded finite coefficients are retained.
   Sequential UCP completeness constructs an adapted everywhere-cadlag limit after
   an initial null-set reset, under usual conditions and a finite measure. It uses
   geometric Cauchy control, a common-event subsequence and actual real limits.
   The Chapter II integral is now actually constructed on the adapted-caglad domain,
   with arbitrary-simple-approximation convergence, adapted/cadlag output,
   indistinguishability uniqueness, proof irrelevance, linearity, integrand invariance,
   full UCP continuity and the unnormalized initial term. Integrator indistinguishability
   invariance and Protter II.17 FV agreement are now proved, including the original
   common-event FV paths rather than only an everywhere-regular version.
   General-integral stopping/cutoff identities (II.12), including zero and infinite
   stopping times, are proved by source approximation and UCP contraction.
   The general jump identity (II.13) is now proved on one common full-measure event,
   including the source initial jump and closed right endpoints. Absolutely continuous
   finite-measure invariance (II.14) is proved, with independent target usualness and
   no bounded-density requirement. Countable mixture invariance and the two-probability
   common version (II.15) are proved, with the positive-weight restriction explicit.
   Invariance between two possibly incomparable usual filtrations (II.16) is proved
   using source approximation in their intersection. Both whole-path assertions
   of II.18 are proved: locality on path-agreement events and Stieltjes agreement
   on the finite-variation event, neither requiring a full-probability event.
   The path-agreement part of the stopping-interval corollary is proved for `(S,T]`,
   including infinite `T` and without agreement of integrand values at `S`.
   The FV-interval part is also proved from the open-interval BV hypothesis, retaining
   endpoint jumps and allowing infinite upper endpoints with finite-subhorizon bounds.
   Protter II.19 is now proved: integration preserves semimartingales, and the
   iterated general integral agrees with the product-integrand integral up to
   indistinguishability. The full source initial product is retained. The FV
   preservation remark also holds on individual FV paths up to one null set.
   Bounded simple integrands preserve martingales; bounded adapted-caglad integrands
   preserve finite-time L2 martingales, with the sharp L2 bound and initial term.
   The general locally-L2 case of II.20 is now proved by actual masked norm-exit
   cutoffs and the minimum of the integrand/integrator localizing sequences. Initial
   masks commute with integration in both variables; no initial L1/L2 premise is added.
   General local-martingale preservation beyond locally-L2 remains open. Full
   cadlag/caglad increment-only Riemann approximation (II.21) is now proved,
   including the precise initial-product correction and source left-limit
   normalization. Exact ordinary/strict ceiling formulas, right-continuous
   stopped-path convergence and partition-uniform source continuity control
   displaced jumps. No uniform approximation of sampled discontinuous
   integrands is assumed. The general raw QV owner is now constructed as described below.
   General-integral addition, real scaling and subtraction in the integrator are
   now proved, with the source initial value and stopped-difference cancellation retained.
5. General raw QV is now constructed from the source integral, with adaptedness,
   cadlag paths, the initial square and jump-square identity, indistinguishability
   invariance, random-partition UCP convergence, common-event increasing paths,
   local finite variation and `[X^T,X^T] = [X,X]^T`. Increasing paths are proved
   through completed-cell sums at upper projected endpoints, not by assuming
   monotonicity of partial-cell sums. Mixed covariation is now constructed by
   polarization of the same owner: bilinearity, initial/jump products, cadlag/FV
   paths, actual mixed-sum UCP limits, stopping in both or either argument,
   integration by parts and semimartingale products are proved. The common-event
   increment and total-variation Cauchy--Schwarz bounds and weighted II.24--II.25
   theorem are proved, including both absolute-continuity results and separate
   initial-term interfaces. Weights are arbitrary measurable functions and
   energies may be infinite. The expectation/Lp corollary (printed p.70) is
   proved for finite conjugate exponents and both endpoints, with random-energy
   measurability derived from joint measurability of the weights, explicit
   initial atoms and independence of the null-event Stieltjes realization.
   The raw square bracket's continuous component is now adapted, continuous,
   increasing, zero-starting and an FV semimartingale, derived from the same
   original Stieltjes measure. The all-times decomposition proves summability
   of the squared jumps over `(0,t]` and retains the initial square. Version
   invariance and the continuous-process normalization identity are proved.
   Mixed continuous covariation is now polarized from these components, with
   adapted continuous/FV paths, zero initial value, symmetry, diagonal identity,
   version invariance, bilinearity and the absolutely summable mixed-jump
   decomposition retaining the initial product. Continuous square and mixed
   brackets now commute with simultaneous and one-sided stopping, including zero
   and infinity, using the closed-endpoint jump cutoff. II.30's weighted random-
   partition mixed sums now converge in UCP to the source left-limit bracket
   integral, including cadlag weights and partial terminal cells. II.29's
   brackets of general Chapter II integrals are proved, including the two-integral
   product-of-integrands and square-integrand formulas with all initial terms.
   II.27's main continuous-local theorem is proved: continuous raw brackets,
   compensated-square local martingales, exact centering and constancy
   equivalence, without initial moments. II.26's continuous-FV case and II.27
   Corollaries 1--2 are proved: continuous FV local constancy, each ordered
   stopping-interval FV/bracket constancy result (zero/infinite endpoints and
   AE order included), and locally-L2 raw mixed-bracket characterization.
   General II.26 is now proved from actual endpoint limits, Stieltjes jump
   integrals and summable singleton-mass series: raw QV retains the initial
   square and all positive-time squared jumps; the continuous part vanishes.
   The quadratic-pure-jump property has version and stopping invariance and
   allows continuous drift. II.28 is now proved: either quadratic-pure-jump
   argument forces the mixed continuous component to vanish, leaving the
   initial product and actual absolutely summable mixed-jump series. FV and
   continuous-path cases and quadratic-pure-jump linear stability are proved.
   II.27 Corollary 5's main statement is proved on one event for every
   order-connected interval, including open/half-open/unbounded intervals.
   Raw and continuous bracket endpoint equality detect closed-interval
   constancy; arbitrary random endpoints can be substituted. Corollaries
   3--4 (moments/terminal values) are now proved on the actual semimartingale
   domain, with automatic CLM entries; general LM-to-SM remains open. Corollary 5's following
   discontinuous compensated-Poisson example is now proved: exact moments,
   true/local martingale, cadlag/FV paths, semimartingale property and the actual
   canonical bracket `N` for a compatible explicit filtration. Arbitrary
   vanishing meshes identify the square-sum limit; nondegenerate compensated
   intervals are never constant, while the bracket has a flat right interval
   at every time on one event. No martingale or bracket assumption replaces
   these proofs.
   Then derive the
   normalized Klenke 21.70--21.76 interfaces, repair 21.71, and close Exercises
   21.10.2--21.10.3. No separate normalized bracket construction is permitted.
6. Complete the stochastic exponential's uniqueness and the remaining
   applications. Actual product convergence, the raw/continuous formula
   comparison and continuous-case existence/integral equation are proved.
   General cadlag regularity, the positive-time jump identity, and the actual
   finite-variation pure-jump product factor are also proved.
   Adaptedness and semimartingale preservation for general inputs are proved
   without assuming measurable enumerations of the random jump times.
   The general jump-case integral equation is now proved, with the arbitrary
   initial value retained and no division by zero/negative jump factors.
   Pure-jump FV integration is the actual initial-plus-weighted-jump series;
   a proved two-coordinate exponential-product Ito formula gives cancellation.
   Protter II.38's product identity and continuous inverse consequence are
   proved directly from the actual products, independently of uniqueness.
   Arbitrary-initial product corrections, canonical version invariance, and
   the raw-inverse zero-initial guard are explicit.
   The real exponential preserves continuous local martingales. The
   compensated characteristic exponential satisfies its Ito integral
   equation and is a complex local martingale; with continuous bracket
   equal to time it is a true complex martingale by compact norm bounds.
   Conditional characteristic functions, Gaussian increment laws, independence
   from the past and mutual independent increments are now proved. The real
   filtered Levy equivalence (II.39) is closed using the canonical Brownian and
   raw-bracket owners. Its reverse direction derives the square-minus-time
   martingale from Gaussian moments and past independence. The latter condition
   cannot be dropped for enlarged filtrations; full-information failure is
   proved. General usual-filtration transport remains open.
   Deterministic-bracket Gaussian increment laws and past independence are
   proved, including flat intervals. Finite linear combinations have the full
   continuous-bracket double sum and the common-clock orthogonal specialization.
   Their Gaussian projection laws and conditional characteristic functions are
   proved. II.40 is now also closed: joint vector increments have the canonical
   product Gaussian law and are independent of the specified past. Joint
   Gaussianity and cross-time covariance cancellation give mutual independence
   of the entire coordinate processes. No new Brownian owner or unproved
   independence premise is used. The general open-domain harmonic part of II.41 is
   proved using Mathlib's harmonic predicate and Laplacian, with arbitrary
   initial values and a random common continuous clock. The corrected classical
   C2 open-domain subharmonic direction is also proved: actual increasing Ito drift gives a
   masked local submartingale, and compact-time integrable envelopes give a true
   submartingale. Smooth extensions, compact domain exits and the zero-exit
   basepoint correction are constructed; raw clocks are centered by their
   initial value. Nonsmooth potential-theoretic subharmonic functions are not
   covered, and the source's unstated smoothness convention remains under audit.
   The printed unqualified true-submartingale claim is formally
   disproved by `exp(x^2/2)`: its Laplacian is strictly positive but its Brownian
   composition is nonintegrable at time 1. This source correction does not
   close the unqualified II.41 statement. II.42's DDS theorem is proved:
   actual raw-bracket inverse times, the exact stopping-time filtration,
   canonical Brownian law, Gaussian increments independent of the whole past,
   common-event reconstruction and the original clock's stopping property.
   Bounded characteristic exponentials and AE-finite complex optional sampling
   prove the conditional laws, without assuming square moments or a prior
   time-changed-martingale theorem. Common-event clock fibers and proper
   quotient maps allow flat intervals. The proof's auxiliary right-continuation
   step is also proved: the same Brownian process is adapted with independent
   future increments in the usual filtration `G_(s+)`, and the original clock
   remains a family of stopping times. No equality with the unextended `G`
   is assumed.
   II.43's actual area integral, zero initial value, continuous-local preservation,
   mixed brackets and continuous energy are proved. The source terminal Riccati
   coefficients, derivative identities and exponential bound are proved for all
   real parameters. The actual compensated exponent/exponential has proved
   semimartingale, continuous-path, endpoint and norm properties with an explicit
   clock. Both Riccati coefficients satisfy the existing stochastic-integral
   equations along continuous zero-starting FV clocks. The squared-radius
   integral equation and C1 transformed-clock substitution are proved, retaining
   the source initial product and allowing nonzero common raw-clock starts.
   The continuous-FV multiplier and weighted-radius identities now prove the
   actual real-exponent integral representation, including `beta(0)` and the
   radial FV drift. Continuous coordinates may replace left limits in the
   antisymmetric area without zero initial values, by cancellation of the two
   initial products. Continuous-FV multiplier brackets and common-clock
   finite-integral-sum brackets are proved, including two-coordinate interfaces.
   The actual continuous area energy is `J_Q(X^2+Y^2)` under orthogonal common
   continuous brackets, with no zero coordinate start or Brownian-law premise.
   The squared-radius bracket and radius/area orthogonality are proved. The
   compensated exponent's actual complex bilinear bracket is now proved to be
   `J_Q((X^2+Y^2)(alpha^2-u^2))`, including both coordinate and cross calculations.
   Required complex-integral initial-product, version-invariance, real-integrator
   reduction, real-inner-integral associativity and continuous-LM preservation
   interfaces are proved using the existing real integral and localization.
   The actual exponential Ito drift cancellation, complex local-martingale
   property, bounded stopped martingale and inverse-cosh characteristic
   function are now proved. This includes a standard-time interface and a
   canonical independent-Brownian interface with explicit filtration-past
   conditions; its bracket hypotheses are derived, not assumed. The actual
   time-zero law is proved to be Dirac at zero. The positive-time density is
   now proved as well: a sigmoid change of variables and Euler's Beta/Gamma
   reflection formula give the actual Fourier integral; normalization and
   Fourier uniqueness identify the area law. The density has an explicit
   nonzero-time guard, and the measure at zero is Dirac. This closes II.43
   and its density corollary, not the remaining package applications.
   The scalar/vector/complex
   cadlag Ito formulas (II.32--II.33, II.35--II.36) and II.34 Fisk--Stratonovich
   chain rule with its integration-by-parts corollary are proved.
7. Deeper progressive-debut/strict-inclusion results and finer stopping-classification bridges;
   general local Yoeurp, remaining compensator applications and predictable QV;
   special canonical decomposition and the reverse good-integrator-to-classical implication.
   Conditional variation and the quasimartingale predicate are now implemented
   with an explicit terminal-zero tail and separate coordinate integrability.
   The actual sum and global supremum are proved equal to the original strict
   partition formulation, without a second partition owner. Nonnegative
   supermartingales have exact variation equal to their initial mean, and the
   difference of two right-continuous nonnegative supermartingales is a
   quasimartingale under usual conditions (III.17 easy direction).
   The source predictable sigma-field identification and left-continuous adapted
   bridge are now proved, including predictable left limits and indistinguishable
   predictable versions for the merely AE-regular case. The optional and
   progressive fields are now constructed with their source generators,
   the full inclusion chain and the native progressive-predicate equivalence.
   Optional versions, arbitrary optional stopping and finite/explicit-terminal
   stopped-value measurability are proved. Optionality does not imply cadlag
   paths. These do not close the deeper progressive-debut or strict-inclusion
   statements or the remaining stopping classification.
   Protter I.6 is now closed: finite adapted-cadlag samples generate the native
   F_T, with everywhere and usual-filtration AE-cadlag versions. Optional
   samples generate the same field; possibly infinite samples use an explicit
   terminal-field input. The coefficient-activation construction has no
   initial-measurability or integrability premise. Other Chapter I stopping
   and jump bridges remain separately open.
   F_(T-) is now defined with its source generator identity, native stopped-field
   inclusion and zero/finite/infinite deterministic-time identities. III.7 and
   predictable stopping-value measurability are proved. III.5 has exact finite
   and explicit-terminal generator interfaces; zero-terminal samples cannot
   recover the terminal field at infinity. Source AE announcing sequences,
   predictable stopping times and fixed/infinite announcing witnesses are
   implemented. III.6 is proved under initial completeness without imposing
   everywhere convergence or right continuity. Accessibility and total
   inaccessibility now have source finite-graph predicates, restriction
   stability, countable-valued accessibility and null-intersection theorems.
   Full III.3 is proved using a countable essential union: existence,
   stopped-measurable events, reconstruction and almost-sure uniqueness of
   both events and restricted times. The graph includes zero and excludes
   infinity; every stopping graph is optional and its strict future is
   predictable. Positive delays, finite predictable minima/maxima and
   countable predictable suprema now have actual source announcing witnesses,
   including infinity and exceptional zero-target samples. Arbitrary
   decreasing-limit closure is not claimed. Predictable-graph/announcing
   equivalence and finer hitting bridges, and III.4 Meyer's Markov/Feller jump
   classification remain open. The decomposition does not close these gaps.
   Native nonnegative-jump local martingales now have TI jumps, from actual
   UI predictable-jump tests and the countable large-jump covering converse.
   The continuous-sole-compensator iff is proved on the local-IV domain
   under nonnegative positive-time jumps, without an initial moment.
   Original Poisson jumps and each original hitting arrival are TI under
   explicit whole-past increment independence in the specified usual
   filtration. That independence is now derived in the original natural
   filtration from genuine joint increments, finite-grid telescoping and
   whole-past cylinder independence. Count and real-count raw natural
   filtrations agree exactly, and genuine completion retains the original
   process and clocks. TI jumps and original hitting arrivals therefore hold
   in the genuine usual natural filtration, with explicit original coordinate
   measurability. Rate zero and infinite tails remain allowed; arbitrary
   enlarged filtrations remain outside this Poisson conclusion. The later
   general cadlag real-SII theorem closes the same natural-usual TI conclusion
   without Poisson paths; canonical Levy realization/decomposition and
   Meyer--Feller remain outside it.
   F_(T-)-event predictable restriction is now proved under usual conditions,
   via the actual announcing filtration and eventually correct event
   approximations. Increasing stopping sequences have predictable strict-limit
   parts; finite coincidence of such a part with a totally inaccessible time
   is null. The construction preserves the integer caps at infinity and only
   imposes strictness on the retained event. Conditional future and window
   probabilities now have constructed adapted cadlag versions, common-event
   bounds/support vanishing, width comparison and version uniqueness. The
   totally-inaccessible closed-endpoint bridge uses proved absence of fixed
   finite atoms. Zero-width and capped no-hit guards are regression-tested.
   Bounded stopping-time sampling is now proved from conditional locality,
   countable stopping fibers and dominated right-grid limits, with actual
   window-event integral identities and a guarded threshold probability bound.
   Coherent window sequences and the shrinking trigger-event limit are now
   proved. III.10 Lemma 2 is closed: compact-horizon conditional-window
   suprema converge in measure for arbitrary widths tending to zero. This
   includes actual cadlag versions, the fixed-time closed-endpoint bridge,
   version invariance and finiteness before real conversion. Capped no-hit
   guards and the strict random-time sampling endpoint are retained.
   Lemma 3's distinct conditional-increment modulus is now implemented on
   compact horizons and globally for random AE-finite terminal lifetimes,
   with actual existence, version-safe essential suprema and probability/L2
   convergence. The full bounded-supermartingale source domain is now also
   proved without any termination-time assumption, closing Lemma 3. An actual
   terminal conditional martingale leaves a nonnegative potential with
   vanishing means; its whole-future maximal tail controls late increments.
   These results do not substitute for continuous Doob-Meyer existence.
   Protter III.10's discrete energy Lemma 1 is now proved in full under its
   meaningful L1 conditional-tail convention: zero-starting predictable
   increasing processes have terminal second moment at most 2 N^2. No L2
   premise remains. The native bounded-supermartingale Doob part has exact
   conditional remaining means, a sampling-size-independent 8 K^2 bound and
   an actual terminal L2 limit. Actual positive-time large-jump stopping
   enumeration is now proved, including finite attainment, strict ordering,
   exhaustive coverage and escape to infinity. The positive-time TI-jump
   predicate gives TI entries. Missing finite-prefix probabilities tend to
   zero; actual zero-terminal jump coefficients produce adapted cadlag
   residuals with small jumps on their measurable coverage event. Measurable
   two-time short-window envelopes and fixed-cap residual moment estimates
   are proved without a jump-count moment. Conditional bounds are derived
   after pathwise clipping, never by interchanging min and conditioning.
   Actual cadlag conditional envelopes, finite TI-window tail sums and
   fixed-bound moment convergence now close the compact modulus/L2 argument.
   The random-finite global bridge is derived from actual conditional lifetime
   tails, preserving the infinity atom and proving finiteness before real
   conversion. Coherent representatives and the singleton-spike regression
   prevent invalid uncountable AE intersections. Actual dyadic native Doob
   parts now have predictable mesh restrictions, adapted left-continuous
   ceiling extensions, monotone paths, uniform second moments and actual
   fixed-mesh terminal L2 limits. The predictable terminal-difference energy
   estimate is now instantiated with the actual moduli. The all-real-time
   terminal identities, finer-grid predictability and native L2 completeness
   prove terminal convergence across meshes. Actual conditional-remainder
   maximal bounds give UCP-Cauchy and a common locally uniform Cauchy
   subsequence of the original ceiling steps. Their right-limit and
   right-increment formulas include time zero, with an actual modulus bound.
   For bounded cadlag supermartingales with TI positive-time jumps, the actual
   continuous predictable increasing compensator, its exact zero start and
   its closed uniformly integrable cadlag martingale sum are now constructed.
   Continuous finite-variation uniqueness also holds without boundedness.
   Actual capped norm localizers, arbitrary one-sided martingale stopping,
   stopped TI-jump stability, and an actually constructed bounded-jump local
   compensator family with proved stopping consistency are now available.
   Integrable single-jump Class D, negative-jump supermartingales, actual
   clipped continuous compensators, ordered-difference comparison and mean
   clipping-error convergence are proved. The unbounded integrable single-jump
   extension and global Class D patching are now also proved, closing full
   III.10 for zero-initial cadlag Class D supermartingales with TI positive-time
   jumps, without bounded values/jumps. Actual exceptional times, coefficient
   integrability, local compensators, consistency and terminal envelopes are
   constructed internally. General predictable III.11 existence remains open; its
   conditional mean-zero predictable-jump residual is not automatically TI.
   Stopping-family Class D and Class DL are now defined separately, with
   algebra, indistinguishability, stopping, bounded-family equivalence and
   AE-finite sampling bridges proved. Right-continuous true martingales have
   the proved Class D/UI equivalence and Class DL property; nonnegative
   right-continuous submartingales are Class DL. A continuous deterministic
   example separates Class DL from Class D. An adapted, non-right-continuous
   spike separates deterministic UI from Class D and shows why arbitrary
   modifications do not preserve random-time values. The discrete potential
   Doob decomposition (III.9) is now closed: the actual increasing predictable
   part has an integrable terminal limit which closes the UI martingale part,
   and both parts are unique up to indistinguishability, retaining nonzero
   random initial data. Full continuous-compensator III.10 existence and
   continuous FV uniqueness are proved. General predictable Class D III.11
   and general local III.16 are now proved. Full III.12 naturality characterizations,
   III.13 uniqueness, III.14 naturality, bounded-test IV Yoeurp and III.15
   predictable FV local-martingale constancy are proved. Supplied predictable
   FV/local-martingale decomposition parts now have proved uniqueness.
   Their integrable-variation foundation is now proved: actual extended total
   variation measurability and stopping identity, safe finite-lintegral
   characterization, native local-property/unmasked equivalence, actual Jordan
   terminal AE/L1 convergence and Class D with an independent initial L1
   assumption. Positive bounded predictable stopping times now have the actual
   martingale left-limit conditional identity, L1 jumps and zero conditional
   jump mean. Predictable jump coverage is now constructed as described below;
   the broader III.11 existence argument is now completed below. Actual bracket integrable
   variation and terminal AE/L1 convergence are now proved for bounded cadlag
   semimartingale M and integrable-variation A (with separate A0 integrability
   for the terminal). Actual bounded before-field multipliers of one positive
   bounded predictable martingale jump also have zero conditional mean and
   expectation. Whole-bracket UI martingality is now proved by the subsequent
   III.14 naturality argument, not by this single-jump identity alone.
   Naturality is now defined through actual integrable bracket terminal
   existence, with continuous IV examples. UI predictable jump identities now
   cover positive AE-finite unbounded stopping times. Actual finite mixed sums
   have terminal-product mean and variation domination without L2 of the
   second martingale. Their actual bracket limit now inherits terminal-product
   expectation by UI/L1 convergence, and full III.13 uniqueness is proved by
   an actually constructed bounded conditional test martingale. IV and naturality
   linear/version stability are now proved, including legitimate measurability
   of actual sum variation. Positive-time bounded caglad integrands preserve
   IV under the actual stochastic integral, with actual terminal AE/L1 and
   Class D requiring separate initial-product L1. The full III.12 terminal
   characterization is now proved by actual UI of the left-limit integral
   against bounded M and constructed terminal integration-by-parts balance.
   Naturality is also equivalent to martingality of every actual bounded-test
   bracket, with UI and actual terminal-valued arbitrary stopping in the
   forward direction. Predictable Stieltjes duality is now proved for actual
   increasing martingale-difference pairs, with IV required only on one side.
   The actual III.10 unit-jump pair then shows that TI times avoid predictable
   sets with countable fibers. Predictable cadlag FV inputs now have zero TI
   jumps and a constructed countable predictable cover, allowing AE path
   assumptions through a predictable initial-null reset. This closes that
   dependency without self-compensation. The cover now has positive pairwise
   disjoint finite graphs, by exact before-field restrictions. UI jump
   identities and merely L1 before-field multipliers allow infinite lifetimes
   with explicit zero terminal jumps. Actual IV stopped-jump coefficients are
   L1 without initial-value integrability. Exact lifetime-series reindexing
   and finite mixed-jump partial-sum domination by `2 C` times actual variation
   are proved. Dominated convergence to the actual bracket now gives zero
   fixed-time expectations, and its actual terminal L1 convergence closes
   III.14. The bounded-test actual bracket is UI (IV Yoeurp). Independently,
   masked UI localization and actual jump sampling prove III.15 without IV,
   local IV or initial L1, giving uniqueness of supplied predictable FV parts.
   The III.11 regular residual now has a proved signed compact-modulus route
   on the bounded-supermartingale domain: actual shifted projections, coherent
   residuals, Class D stopping-expectation continuity, first-threshold estimates
   and full width-to-zero convergence in probability. The intermediate ordered
   first-threshold proof uses Class D alone, without a uniform source bound.
   Mean-zero predictable jumps still do not give TI occurrence-window estimates,
   and amplitude selection need not preserve conditional centering. The regular
   general Class D construction and the actual predictable jump-mean series
   reduction are now supplied below, completing III.11 existence.
   The bounded regular source case is now closed: actual global probability/L2
   modulus convergence feeds the reused dyadic construction, giving a continuous
   predictable increasing part and a genuine L2 closing variable. The six TI
   source interfaces are preserved. Arbitrary stopping preserves jump-mean
   regularity. Actual compensation of a positive predictable L1 single jump
   is now proved, with predictable cadlag IV part, zero initial value, expected
   variation at most E norm Z, and true UI residual. Accessible countable-jump
   compensation is now constructed from actual disjoint predictable coefficient
   series, with uniform convergence, exact predictability, IV and UI closure.
   Signed TI compensation and disjoint stopped-event classification then give
   the actual general positive single-jump compensator with the same budget.
   Regular Class D continuous decomposition now also holds for bounded positive
   jump norms without bounded process values, using actual norm-exit pieces.
   The unrestricted-jump regular Class D extension is now proved: the actual
   full exit jump leaves a bounded residual, general single-jump compensation
   and actual predictable jump identification bound the compensated residual's
   jumps, and the existing bounded-jump/consistent Class D owners construct the
   global continuous increasing part and its actual integrable terminal.
   Source-jump integrability is proved before conditional centering and
   integral subtraction. No proposed compensator or TI premise is introduced.
   General III.11's predictable jump-mean series is now constructed as described below.
   Its actual positive disjoint predictable test cover, nonpositive
   conditional jump means, and one-jump conditional-mean removal preserving
   supermartingality are now proved. Actual summable step jump formulas and
   the coefficient-moment budget are also proved; the latter explicitly
   requires supermartingality of each finite corrected sum. The finite
   induction and infinite regular reduction are now proved separately. The
   original Class D hypothesis supplies the actual summable moment budget.
   The predictable increasing IV series preserves Class D and supermartingality
   by coordinatewise UI convergence. Actual disjoint collision-event integrals
   cancel the mean sampled jump at every positive predictable test, with both
   sampled jumps proved L1 first. Adding the internally constructed regular
   continuous part proves general Class D III.11, including an arbitrary
   integrable initial value, a true UI martingale and an actual terminal limit.
   The random-initial/random-amplitude predictable-step regression calls this
   actual existence and identifies its output by predictable FV uniqueness.
   Actual conditional variation now has refinement monotonicity after initial
   conditioning, separately for positive/negative components with their terminal
   tails. Actual fixed-horizon essential envelopes, directed integral bounds,
   finite-to-L1 conversion, exact horizon extension and shift variation
   comparison are now proved. The actual whole-future positive/negative envelopes are now
   constructed with the original global variation bound, finiteness/L1 and
   their fixed-time difference equal to X. Their dynamic conditional
   inequalities and true supermartingale coordinate interfaces are now
   independently proved, using restricted essential suprema and event-integral
   conditional order. Their canonical dyadic right limits now give nonnegative
   cadlag supermartingale coordinates without right-continuous expectations
   or individual modification assumptions. The exact difference decomposition
   and both directions of III.17 are proved. The source calls III.18 Rao's
   theorem; that actual local decomposition and its uniqueness are now proved.
   The full III.16 construction uses actual capped exits, Class D stopping,
   constructed local parts, proved stopped consistency, predictable UCP
   patching and the original Protter localization owner. It includes exact
   normalized zero-initial parts, finite-time compensator integrability and
   the sharp mean-drop bound. A lower expectation bound or finite mean limit
   yields an actual integrable terminal and full-time L1 limit. III.18 then
   constructs exact X = M + A with a globally integrable-variation part from
   the actual III.17 coordinates, rather than accepting a proposed decomposition.
   These results close SM-B13 and SM-B14, not the remaining compensator gates.
   General compensator existence is now proved separately: a direct
   conditional-variation bound gives IV-to-quasimartingale, actual Rao yields
   the global-IV compensator, and its remainder's actual integrable envelope
   gives a true UI martingale with the correct initial-value mean identity.
   Actual native stopped compensators have proved consistency; predictable
   UCP patching gives the local-IV compensator and local remainder. Centering
   and existing masked initial-value localization remove any initial L1
   requirement. Uniqueness permits a merely predictable FV competitor.
   The initial-value regression invokes actual existence with arbitrary
   measurable finite, possibly nonintegrable, initial data.
   Predictable weighted jumps of a UI martingale now have a genuinely
   summable moment budget and a UI closed-step series under an actual
   finite-partial coefficient bound, without assuming a bounded/L2/semimartingale
   source or a proposed terminal. General local Yoeurp still requires its
   actual variation-budget localization. Increasing-compensator inheritance
   is now proved globally and locally, including actual existence consumers
   and the original nonintegrable-initial local domain. Explicit counting-
   process compensators and predictable QV remain open.
   The fundamental-local-martingale chain now has actual signed/norm
   large-jump sums with cadlag/FV bounds, exact jumps, adaptedness, countable
   enumeration equality and stopping/event-restriction identities. Bounded
   positive-time jumps give an actual square-integrable fundamental sequence
   with native initial-value masks. Actual global-IV/UI compensation gives
   the beta/2-beta jump bounds without process-value bounds. The large-jump
   local-IV localization and general local compensation jump bound have now
   been completed separately. Actual joint-exit overshoot and bounded optional
   sampling give true expected stopped variation; native stable-bundle
   idempotence handles general local martingales and their initial masks.
   Actual III.29 constructs M=N+D exactly, two local martingales, zero-initial
   local-IV D and bounded-jump locally square-integrable N retaining M(0).
   This proves normalized decomposability and the general LM-to-SM bridge.
   The classical source predicate is now equivalent to decomposable, proving
   III.30; actual Rao and Doob give III.31--III.32 and the submartingale
   corollary. No initial moment, Class D or global UI restriction was added.
   This packet passed 9799 incremental jobs, 10 clean affected/rebuilt
   traces and 24 standard-axiom checks. Source examples, III.33, special
   canonical criteria and the reverse good-integrator implication remain
   open; this is not a whole-package completion or full build.
   Full III.33 is now proved for adapted-caglad integrands and arbitrary
   local martingales, using actual III.29, globally-IV bounded integration
   and native local-IV localization. Initial moments and local L2 are not
   added. The arbitrary-initial constant regression retains the initial
   product and rules out an unjustified UI strengthening. The special
   predicate, III.34 uniqueness and actual Rao/Doob specialness consumers
   are also proved. Bounded-jump FV processes have actual local IV.
   This later packet passed 9805 incremental jobs, 7 clean affected/rebuilt
   traces and 14 standard-axiom checks. It supersedes the III.33 gap above,
   not canonical component selection, III.35 and later criteria, source
   examples or the reverse good-integrator implication.
   Canonical parts and actual III.35 bounded-jump/continuous decomposition
   are now proved, including actual canonical jump bounds and continuity.
   The canonical martingale retains the original initial random value.
   Actual Poisson canonical identification and a second-moment proof of
   classical nonuniqueness give the R29 mathematical distinction. Local
   martingales have masked whole-path L1 envelopes and native local L1 of
   their original running norm supremum. The source-strength unmasked and
   terminal-supremum supplements, III.36--III.37 and general predictable-FV
   local IV remain separate. The p132 running-jump estimate must retain
   the factor two. This packet passed 9812 incremental jobs, 8 clean
   affected/rebuilt traces and 16 standard-axiom checks, without full build
   or push; it supersedes the canonical-selection/III.35 gaps above.
   The III.38 supplement is now proved: the original running norm supremum
   has actual stopped whole-path L1 envelopes and terminal L1, masked without
   initial moments and unmasked with initial L1. The all-times running jump
   supremum and its correct factor-two bound are formalized. Increasing
   bounded/unit-jump counting compensators, integrable random-jump-envelope
   local IV, attained predictable infima, strict-before predictable localizers
   and original first-large-jump predictability are also proved. General
   predictable-FV local IV and III.36--III.37 remain open. This packet passed
   9823 incremental jobs, 13 clean affected/rebuilt traces and 19 standard-axiom
   checks, without full build or push.
   General predictable cadlag FV local IV is now proved, with no original
   initial moment. The actual canonical FV part inherits it. Specialness is
   equivalent to a normalized LM plus adapted cadlag locally-IV decomposition,
   by actual compensation. Specialness implies native local L1 of both
   original running suprema. The actual jump supremum has proved adaptedness
   and closed/masked stopping; a cadlag counterexample requires the factor two.
   FV running-jump local L1 implies local IV, and generic running-norm local L1
   implies running-jump local L1. This closes the predictable-FV gap above,
   not the reverse III.36--III.37 criteria or BD entry. Verification: 9832
   incremental jobs, 10 clean affected/rebuilt traces and 18 standard-axiom
   checks. No full build or push.
   Both III.36--III.37 criteria are now proved on the classical domain:
   actual FV compensation supplies the converses, without initial moments.
   The canonical compensator is exposed coherently with special parts;
   normalized predictable self-compensation, zero jumps at totally inaccessible
   times and continuous compensation for totally inaccessible source jumps
   are proved. The actual predictable quadratic variation, full square
   characterization, native locally-L2 and AE-continuous existence are proved.
   Continuous angle = raw Q - const(X_0^2); the constant-one regression rules
   out the unnormalized identity, and nonintegrable initial squares obstruct UI.
   General raw-bracket-compensated local-martingale products/squares are proved
   without local L2. This closes the preceding classical-converse,
   III.24--III.25 and basic angle-existence gaps, not mixed angle algebra,
   remaining applications, general local Yoeurp or the BD entry. Verification:
   9844 incremental jobs, 13 affected / 13 rebuilt clean traces
   and 31 standard-axiom checks. No full build or push.
   Actual mixed angle construction, full product characterization,
   symmetry/diagonal agreement and polarization are now proved. Its local-IV
   domain follows from the two actual square domains, and hence from native
   locally-L2 inputs; the sum-square domain is constructed, not assumed.
   Compensator linearity/arbitrary stopping and both angle stopping identities
   are proved, retaining zero/infinite times and original initial values.
   Actual Poisson and compensated-Poisson angles equal linear drift under the
   original independence hypotheses; positive rate gives genuinely unequal
   raw/predictable brackets. This closes the basic mixed-domain/polarization/
   stopping gap, not bilinear/one-sided stopping supplements or remaining III.19--III.23 applications, general local Yoeurp, measure/
   filtration change or BD. Verification: 9853 incremental jobs,
   10 affected / 10 rebuilt clean traces and 26 standard-axiom
   checks. No full build or push.
   The further mixed-angle bilinear, source-invariance and one-sided stopping
   supplements are now proved, with each actual transformed domain derived.
   One AE-continuous source gives the actual mixed domain and its equality
   with existing continuous covariation, without a square-angle assumption
   on the other source. A shared continuous FV compensator bridge preserves
   the initial correction and replaces the old private square-only proof.
   Common initial-event masking of the actual raw mixed bracket is proved.
   Verification: 9858 incremental jobs, 7 affected / 7 rebuilt
   clean traces and 17 standard-axiom-only checks. General local Yoeurp,
   counting/hazard applications and the other listed gates remain open.
   No full build or push.
   General local Yoeurp is now proved using actual deterministic variation
   localizers, UI predictable-jump budgets and original raw mask/stopping
   identities. No initial-product moment is imposed; a random-constant
   regression separates centered UI from raw local martingality.
   The nonexplosive counting predicate, actual canonical compensation and
   forward native-hitting arrival representation/localizers are proved.
   Poisson membership and the actual non-Poisson deterministic single jump
   are verified, including the first-one/eventual-infinity arrival sequence.
   Reverse general arrival construction, III.21/III.23 hazard formulas,
   complete III.19/III.20 consumers and the remaining listed gates are open.
   Verification: 9868 incremental jobs, 11 affected / 11 rebuilt
   clean traces and 32 standard-axiom-only checks. No full build or push.
   Reverse extended-arrival construction and exact native-hitting recovery
   are now proved, including eventual infinity and the older all-finite
   Poisson-count coherence. Adaptedness is equivalent to stopping-time
   arrivals. Initial completeness constructs the actual count from common-AE
   valid arrivals, preserving all original arrivals and all-time guarded
   counts on one common event without totalizing explosive raw paths.
   AE-source signed kernel tests, whole-kernel version invariance, UCP and
   actual-integral predictable versions are proved. Predictable FV integrals
   have actual local IV and initial-corrected canonical compensation.
   The everywhere-good increasing-source Chapter II consumer proves L1 and
   expectation equality for centered finite-time actual integrals, using
   the corrected expected absolute Stieltjes condition. Original initial
   products remain explicit and are not assumed integrable.
   Verification: 9880 incremental jobs, 12 affected / 12 rebuilt
   clean traces and 38 standard-axiom-only checks. No full build or push.
   Full AE-source Chapter II consumption, corrected III.20 and hazards remain
   open; the earlier reverse-arrival gap above is superseded by this packet.
   The p114 Theorem-25 reference
   must not be treated as an already proved enumeration theorem; its apparent
   III.25 route involves a self-compensation identification requiring care.
   Printed III.20 additionally needs a predictable-A hypothesis; III.19's
   signed integrand needs actual absolute integrability. The corrected III.19
   signed kernel consumer now constructs the actual increasing compensator on
   the everywhere-good path representation. The full AE-source Chapter II
   bridge is now proved for the original source's actual integral and the
   sole canonical compensator's actual integral, with the initial correction.
   The corrected III.20 consumer is also proved: actual right-value pathwise
   integration equals J + raw covariation, has constructed local IV and has
   actual canonical compensator J. It requires predictable A, and extends
   to native local martingales without adding initial moments. The pathwise
   right/left correction proves variation-measure integrability and absolute
   jump-product summability for cadlag integrands that need not be FV.
   General native FV local martingales have actual local IV; FV specialness
   is equivalent to local IV on the adapted cadlag domain.
   Verification: 9884 incremental jobs, 5 affected / 5 rebuilt
   clean traces and 10 standard-axiom-only checks. No full build or push.
   These results supersede the earlier III.19/III.20 gaps above; III.21/III.23
   hazards and measure/filtration-change applications remain separate work.
   The raw QV/QCov measure/filtration invariance wrappers are now proved,
   as are actual mixed-angle invariance and constructed domains with one
   continuous source. No unconditional discontinuous-angle invariance is
   claimed. Concrete finite-model counterexamples under equivalent laws and
   a larger usual filtration are now proved: the same actual bounded UI/L2
   martingale has an unchanged raw bracket but different actual angles.
   Both angular domains are constructed. Actual angular-domain loss under
   a smaller usual filtration is now proved using the geometric model:
   full information gives a constructed angle equal to raw QV, whereas
   the reveal filtration has the same semimartingale/raw QV but no native
   local-IV domain for that raw bracket.
   Closed single-jump natural information and its full revealed/survival
   event decomposition are proved; a two-point nonmeasurability regression
   rules out the incorrect raw capped-lifetime field at endpoint atoms.
   Actual-integral regressions verify the initial-product and centered-L1
   boundaries in corrected III.19/III.20. Actual raw and usual single-jump CE
   are now proved. The raw natural filtration is right-continuous; null-set
   enlargement preserves right continuity and actual original-L1 CE on the
   genuinely completed space. The ENNReal cumulative hazard, guarded finite
   bounds, capped real right continuity, stopped expectation and strict-survival
   increment balance are proved. The actual finite-capped count minus its
   stopped hazard is now a UI martingale under the positive-survival guard;
   the original stopped hazard is predictable without replacing the process.
   Canonical capped compensator identification is now proved with actual
   source-domain evidence and the initial count atom retained. Unrestricted
   stopped-hazard expectation and L1 identities are proved from almost-everywhere
   positive pre-jump survival; no deterministic survival guard is needed for
   those identities. The actual uncapped remainder is a true martingale;
   the original stopped hazard has common-event finite extended values,
   monotone and cadlag paths. Unrestricted canonical compensation is now
   identified with the actual stopped hazard, also for an arbitrary measurable
   extended lifetime via its actual pushforward law and genuine completed
   usual natural filtration. The full source domains are constructed, without
   a deterministic survival guard. Whole-half-line UI on the canonical law
   follows from an actual integrable extended-hazard supremum, not a mere
   uniform L1 bound. Zero/infinite lifetimes and terminal atoms remain allowed.
   Native martingale pullback uses exact comap filtrations, not injectivity
   or an arbitrary information enlargement. Arbitrary-lifetime UI transport
   is now proved through actual norm-tail identities. The native CDF/Stieltjes
   hazard expression is proved on the almost-surely finite domain, with the
   correct pre-jump denominator and initial-atom exclusion. Continuous CDF
   and original-law null singletons are equivalent. Diffuse stopped paths
   are continuous on one event; the actual logarithmic hazard and the same
   sole canonical log compensator are proved on arbitrary original spaces,
   without a density assumption. Finite extended hazard and positive survival
   are established before the real logarithm identity.
   Actual measure-AC finite positive laws give locally AC stopped hazards
   via the genuine weighted measure and RN primitive, retaining infinite
   lifetimes. The native exponential law gives actual hazard r*t at arbitrary
   positive rate. The CDF-function AC input bridge is now proved using the
   actual integrable derivative, FTC and Stieltjes measure extensionality.
   It gives common-event locally AC paths for the actual original-space
   canonical compensator from the original AE-finite lifetime and CDF alone.
   The original-space exponential compensator is now identified with the
   general rate times the finite stopped clock. This closes III.21 and both
   corollaries, retaining the corrected nonunit-rate factor.
   Conditional-history III.23 and hazard-rate/censored-data applications
   remain open. Infinite preceding arrivals require absorbing actual gaps
   and no age evaluation; independent latent gaps must not be confused with
   these absorbing gaps. The independent-interval corollary also needs its
   corrected first-interval and completed-gap indices.
   III.23 prerequisites now include joint measurability of the actual kernel
   hazard, its genuine joint-law stopped expectation, and common-event finite
   monotone cadlag paths through a measurable positive-survival event. Its
   real mean and global UI are proved using an actual integrable envelope.
   Raw natural-count events before the next arrival have exact measurable
   finite-history traces. Actual measurable positive interarrivals recover
   every arrival by prefix sums, retaining the absorbing infinite tail.
   Conditional-law transport is now proved using native disintegration on
   arbitrary original and history spaces. Actual finite histories are
   measurable at the preceding arrival, and arrival/gap histories generate
   exactly the same sigma field. The raw natural count filtration is proved
   right-continuous by its genuine no-jump windows and frozen observations.
   Delayed activation from stopped-field marks is predictable, and calendar
   stopping has the exact absorbing-gap hazard representation. Actual
   bounded history clocks have the zero survival-increment integral, and
   clocks bounded by calendar time preserve UI. Actual compensated stages
   are now true globally UI martingales in the raw natural count filtration.
   The positive actual arrivals form a native localizing sequence. Exact
   birth-endpoint zero support makes the actual total hazard a genuinely
   locally finite predictable series with zero initial value and common-event
   monotone cadlag paths. Its finite prefix retains the current pending
   stage; stopping at an arrival gives the exact compensated prefix through
   that arrival, using zero at the next birth endpoint. Total local
   martingality in genuine usual augmentation and sole compensator identification
   are now proved, retaining the original probability measure's conditional
   kernels. Actual-gap history gives the same formula on one common event
   for every time; completed-plus-pending finite formulas include count zero
   and all arrival endpoints. The conditional III.23 formula is established
   on the everywhere-valid arrival domain. The corrected independent
   specialization is now proved for positive independent latent durations
   with nonexplosive extended prefixes, with the original marginal hazards,
   the initially empty completed sum and all completed terms retained.
   General adapted counts have everywhere-valid arrival representatives
   with indistinguishable guarded counts, and genuine usual natural
   filtrations are invariant under indistinguishability. The general AE-count
   canonical compensation consumer is now proved: from adaptation to a usual
   source filtration, the original count's sole natural-usual compensator has
   the original-measure conditional-gap finite formula, indexed by the original
   count. No expected-count bound is needed. A genuine continuous density gives
   the conditional right-window hazard-rate limit at positive closed survival.
   Censoring has true unnormalized submeasure identities and domination,
   including ties and infinite lifetimes. The explicit density primitive now
   gives the original sole single-jump compensator as the actual stopped
   density-over-survival integral. Cause-specific hazard has actual dominated
   submeasure semantics, extended mean, real L1, strict-survival increment
   balance and common-event finite monotone cadlag paths. The marked-pair
   raw natural filtration is right-continuous, with the mark revealed only
   at occurrence. Actual marked-count compensation is now proved by a true
   raw martingale and full canonical uniqueness in the genuine usual
   natural filtration. Arbitrary dependent censoring has the true measure
   formula, including ties and infinite lifetimes. The marked density
   integral and global stopped cause-hazard UI are proved. Exact crude-
   window decomposition retains the within-window censoring error, and
   finite absolutely continuous laws have native RN right-window rates
   almost everywhere. The genuine thin-window error now has rate zero a.e.,
   and actual full-real arrival-law AC constructs the true cause RN density
   and crude-window limit. The stopped crude primitive is the sole censored
   compensator, and the original count minus that primitive is locally
   martingale in the genuine usual observed-pair natural filtration.
   The net-rate corollary requires net=crude only a.e. at positive joint
   survival. The printed censoring-rate application is closed at these
   actual domains, not as a pointwise-all-times or enlarged-filtration claim.
   Independent conditional laws and conditional-law
   equality on a history event are proved. Positive diverging extended latent
   prefixes construct actual arrivals, but actual absorbing gaps are equated
   with latent durations only when the preceding prefix is finite.
   The actual evaluated conditional gap laws for arrival/gap histories now
   agree as measures on one common event. Safe elapsed clocks give exact
   original-arrival/gap-event and delayed-hazard identities, including
   infinite preceding arrivals. Their original-space conditional UI and
   zero history/survival increment integrals are proved. The same original
   full-measure event retains all-time finite monotone cadlag hazard paths
   under safe elapsed time, without an uncountable AE quantifier exchange.
   Genuine completion preserves UI, and already right-continuous raw
   filtrations preserve true/UI/native local martingales under usual
   augmentation, retaining their original masks and fundamental sequences.
   The first printed-page-128 process example is proved: the centered
   geometric single jump is UI in an actual usual filtration but not natively
   locally L2. Native local IV similarly forces an L1 increment at a positive
   time with zero-one preceding information, without an initial moment.
   The second printed-page-128 process example is also proved using the
   reciprocal-uniform law: in genuinely completed usual filtrations the
   process is a local martingale when magnitude is initially known, but
   not in the smaller reveal filtration, while remaining a FV semimartingale.
   Actual right-continuous stationary increments independent of the specified
   past now have stationary finite-vector laws after arbitrary genuinely
   finite stopping times, with stopped-field test identities and proved
   sampled-vector AE measurability. Initial-window supremum estimates are
   proved without moments or monotone horizons. Actual stopped-window laws,
   finite announcing-jump limits and finite-time sample measurability are now
   verified. They prove that every positive predictable jump is zero and hence
   that a measurable AE-zero-initial cadlag real SII process has TI jumps in
   the genuine completed usual augmentation of its own natural filtration.
   This is the general SII consumer, not a cadlag realization of the canonical
   Levy coordinate law, a Levy decomposition, or Meyer's Feller theorem.
   The terminal RN density and canonical cadlag/UI/nonnegative density process,
   strict positivity, reciprocal identities, stopping-time formulas and joint
   equivalent-law left-limit localization are proved. True and uniformly
   integrable and local martingales now transfer by multiplication with the
   canonical density. Equivalent-measure raw-bracket Girsanov--Meyer III.39 is
   proved in division-free and right-value Stieltjes forms, with its actual
   initial term. Predictable-bracket III.40 is proved on the actual raw
   locally-integrable-variation domain. For one-way `Q ≪ P`, summable geometric
   lower-density exits are now proved to be a `Q`-localizing sequence, with
   exact positive-time `Z₋` and reciprocal bounds before each exit. Native
   finite-stopping Bayes identities and bounded UI transfer now prove the
   one-way local criterion `Z * X` `P`-local implies `X` `Q`-local, using the
   original masks, density exits and deterministic caps. The predictable
   correction in III.41 is now proved by clipped-reciprocal localization and
   target-law integration, with no reverse absolute-continuity assumption.
   Lenglart--Girsanov III.42 and its zero-density jump compensator remain.
   The III.41 module, aggregate semantic regression and 13-declaration axiom
   audit passed; the audit reports only Lean's standard `propext`,
   `Classical.choice` and `Quot.sound`. Earlier transfer verification passed
   10044 incremental jobs, one clean production rebuild and 7
   standard-axiom-only checks. Earlier SII-TI
   verification: 10033 incremental
   jobs, 7 clean production rebuilds and 11 standard-axiom-only checks.
   No full build or package completion is claimed.
   Earlier natural-Poisson verification: 10020 incremental jobs, 7 affected / 7 rebuilt
   clean traces and 9 standard-axiom-only checks. No full build or push.
   Earlier jump-classification verification: 10014 incremental jobs, 7 affected / 8 rebuilt
   clean traces and 8 standard-axiom-only checks. No full build or push.
   Earlier crude-censoring verification: 10008 incremental jobs, 12 affected / 12 rebuilt
   clean traces and 19 standard-axiom-only checks. No full build or push.
   Earlier marked-compensation verification: 9997 incremental jobs, 9 affected / 9 rebuilt
   clean traces and 13 standard-axiom-only checks. No full build or push.
   Earlier density/cause verification: 9989 incremental jobs, 8 affected / 8 rebuilt
   clean traces and 22 standard-axiom-only checks. No full build or push.
   Earlier general-count verification: 9982 incremental jobs, 5 affected / 5 rebuilt
   clean traces and 5 standard-axiom-only checks. No full build or push.
   Earlier independent-arrival verification: 9978 incremental jobs, 7 affected / 7 rebuilt
   clean traces and 6 standard-axiom-only checks. No full build or push.
   Earlier canonical-arrival verification: 9972 incremental jobs, 9 affected / 9 rebuilt
   clean traces and 11 standard-axiom-only checks. No full build or push.
   Earlier arrival-series verification: 9964 incremental jobs, 9 affected / 9 rebuilt
   clean traces and 11 standard-axiom-only checks. No full build or push.
   Earlier safe-clock verification: 9956 incremental jobs, 7 affected / 7 rebuilt
   clean traces and 9 standard-axiom-only checks. No full build or push.
   Earlier activated-history verification: 9950 incremental jobs, 8 affected / 8 rebuilt
   clean traces and 13 standard-axiom-only checks. No full build or push.
   Earlier kernel/history verification: 9943 incremental jobs, 7 affected / 16 rebuilt
   clean traces and 14 standard-axiom-only checks. No full build or push.
   Earlier III.21-corollary verification: 9938 incremental jobs, 6 affected / 6 rebuilt
   clean traces and 9 standard-axiom-only checks. No full build or push.
   Earlier diffuse-hazard verification: 9933 incremental jobs, 14 affected / 14 rebuilt
   clean traces and 24 standard-axiom-only checks. No full build or push.
   Earlier general-hazard verification: 9920 incremental jobs, 5 affected / 5 rebuilt
   clean traces and 8 standard-axiom-only checks. No full build or push.
   Earlier hazard/domain verification: 9916 incremental jobs, 9 affected / 9 rebuilt
   clean traces and 25 standard-axiom-only checks. No full build or push.
   Earlier native-moment verification: 9908 incremental jobs,
   7 affected / 7 rebuilt clean traces and 24 standard-axiom-only checks.
   Earlier hazard/environment verification: 9902 incremental jobs,
   13 affected / 13 rebuilt clean traces and 49 standard-axiom-only checks.
   Earlier information-only verification:
   Verification: 9890 incremental jobs, 6 affected / 6 rebuilt
   clean traces and 12 standard-axiom-only checks. No full build or push.
8. The terminal RN density and canonical cadlag/UI/nonnegative density process
   with exact current-filtration event integrals are now proved. Fixed-time
   strict positivity is proved under one-way absolute continuity at its natural
   target-law AE measure and under equivalence at the source-law AE measure.
   Fixed-time reciprocal densities under equivalence and multiplication/division
   Bayes formulas are also proved at their exact AE measures. Under equivalence,
   a common event now supports all-time reciprocal products, strict positivity
   and the càdlàg inverse density. Everywhere-finite stopping-time density
   conditioning, exact `F_T` event integrals, positivity and reciprocal formulas
   are proved. A joint forward/reverse capped-exit sequence is localizing under
   both equivalent laws and bounds the positive-time density left limits and
   their reciprocal. Equivalent-law true and uniformly integrable martingales
   and local martingales transfer by multiplication with the canonical density.
   Raw-bracket equivalent-measure Girsanov--Meyer III.39 is also proved, with
   no hidden initial normalization. Predictable-bracket III.40 is proved as
   well. One-way zero-density localization under `Q ≪ P` is proved through
   geometric lower-threshold exits and Borel--Cantelli. Remaining are the
   merely absolutely-continuous III.41 conclusion is proved without
   equivalence. Remaining are Lenglart--Girsanov III.42,
   Kazamaki/Novikov, the Yan/Hahn--Banach
   proof dependency, and the actual Bichteler--Dellacherie equivalence with
   finite-horizon patching.
9. Exact Protter I--III theorem/exercise disposition rows, outstanding semantic
   regressions and final declaration-level dependency/axiom audits.

## Status corrections

- The older README/SOURCE_MAP claim that LSII was fully complete was too broad:
  the Remark 16.23 source correction does not prove the corrected formula.
- Old deferred forward references to Brownian construction, infinite
  divisibility or convolution semigroups are not current missing implementations
  where the later package has already supplied them.
- The printed nearest-neighbor mesh in Klenke 21.56 is insufficient. The active
  partition API explicitly uses maximum adjacent gaps; the counterexample and
  exact correction are recorded in the Semimartingale ledger.
- A successful full library build certifies the committed/proposed Lean
  declarations, not coverage of mathematics that has not yet been encoded.

The 2026-09-12 publication/pause rule records a historical checkpoint. Work has
since resumed. That checkpoint did not relax the mathematical completion gates
for a design document or certify completion of Semimartingale.

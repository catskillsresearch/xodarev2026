# StochLean

StochLean is a Lean 4 library for probability theory and stochastic processes. Its goal is to give
people and software agents working with stochastic processes a directly reusable Lean library,
reducing the time required to formalize and verify related mathematics. It provides a
kernel-checked layer between Mathlib's measure/probability foundations and larger developments in
martingales, Markov processes, Brownian motion, Levy processes, stochastic integration, and
probabilistic applications.

The mathematical coverage baseline is Achim Klenke's *Probability Theory: A Comprehensive Course*,
third edition. Klenke is a coverage and statement source, not a code dependency: canonical Mathlib
APIs are reused whenever they already provide the required semantics.

## Normative specifications and implementation order

Development follows these reviewed handoff specifications:

1. [Klenke Chapters 01-08](docs/StochLean_Klenke_Ch01-08_Design_v0.1.pdf) - probability foundations
   and the first stochastic-process consumers.
2. [Process Core and Information Flow](docs/StochLean_ProcessCore_InformationFlow_Design_v0.1.pdf) -
   process equivalence, stationarity, path semantics, filtrations, measurability, and random times.
3. [Discrete Martingale Calculus and Exchangeability](docs/StochLean_DiscreteMartingaleCalculus_Design_v0.1.pdf) -
   discrete martingale calculus first, followed by exchangeability, reverse martingales, and de
   Finetti theory.
4. [Measure Convergence and Projective Construction](docs/StochLean_MeasureConvergence_ProjectiveConstruction_Design_v0.1.pdf) -
   weak/vague convergence infrastructure, tightness and Prokhorov reuse, kernels and
   Ionescu-Tulcea, and Kolmogorov projective construction.
5. [Markov Processes](docs/StochLean_MarkovProcesses_Design_v0.1.pdf) - future information,
   transition systems, Markov semantics, countable-chain recurrence, coupling, generators, and
   Feller interfaces.
6. [Markov Processes, Kernels, Semigroups, and Convergence](docs/StochLean_MarkovProcesses_Kernels_Semigroups_Design_v0.1.pdf) -
   the consolidated kernel/semigroup specification, source corrections, acceptance suite, and
   dependency ledger for the Markov layer.
7. `StochLean_FourierProbability_ClassicalLimitTheorems_Design_v0.1.pdf` - characteristic
   functions, triangular arrays, Lindeberg--Feller, Kolmogorov three-series, and multivariate CLT.
8. `StochLean_Levy_StationaryIndependentIncrements_Design_v0.1.pdf` - convolution semigroups,
   stationary independent increments, infinite divisibility, compound Poisson laws,
   Levy--Khintchine, and stable laws.
9. `StochLean_BrownianMotion_PathRegularity_Design_v0.2.pdf` - Kolmogorov--Chentsov,
   continuous Brownian realization, path properties, strong Markov/reflection/arcsine results,
   and deterministic Wiener integration.
10. `StochLean_Semimartingale_Core_Design_v0.1.pdf` - the merged Protter Chapters I--III
    and Klenke Section 21.10 package. It supersedes the former continuous-martingale/QV
    design; the single general raw bracket will own the normalized Klenke interfaces.

This order is mandatory. A later package consumes earlier canonical APIs and must not introduce
temporary duplicates merely to compile.

## Fixed global rules

These rules apply to every module and every present or future design document; they are not
relaxed to finish a proof:

- **Pinned baseline:** Lean and Mathlib are pinned to `v4.33.0`. An upgrade triggers a new duplicate
  and semantic audit.
- **No duplicates:** before adding a public declaration, search the pinned Mathlib revision, the
  complete local library, and the approved-external ledger, in that order. A usable canonical
  result forbids a parallel implementation.
- **Mathlib-only dependency boundary:** Mathlib is the only permitted external Lean package in the
  final project dependency graph. Other Lean projects may be inspected solely as implementation
  references. Any adopted proof must be audited at an exact revision, brought into the StochLean
  source tree with its license and attribution, reorganized under the canonical StochLean owner,
  namespace, names, signatures, and APIs, and compiled without importing or linking the external
  package. External source code is never API authority.
- **Functional organization:** files and namespaces are organized by mathematical purpose, never
  by textbook chapter.
- **Canonical representations:** processes remain functions `X : T -> Omega -> E`. Reuse
  Mathlib's `Measure`, `ProbabilityMeasure`, `Kernel`, `Lp`, `Filtration`, `Adapted`,
  `IsProgressive`, `IsStoppingTime`, `HasIndepIncrements`, martingale, and conditional-expectation
  infrastructure.
- **Semantic precision:** pointwise and a.e. statements, modification and indistinguishability,
  one-time/f.d.d./coordinate-product/path-space laws, global and local convergence in measure,
  predictable bracket and pathwise quadratic variation, and bounded and a.s.-finite stopping
  times are kept distinct.
- **Common-event path semantics:** an a.s. path property over uncountable time uses one common
  full-measure event for the entire trajectory.
- **Natural domains:** public theorems carry the genuine measurability, integrability,
  sigma-finiteness, positivity, and finiteness assumptions. Totalized fallback values are never
  used as mathematics.
- **Proof integrity:** project source contains no `sorry`, `admit`, project-defined axiom,
  conclusion-shaped premise, or vacuous surrogate model. Milestone declarations undergo axiom
  inspection.
- **Source corrections:** reviewed errata and semantic corrections override OCR or printed
  shorthand.
- **Minimal imports:** production modules use the narrow stable dependency closure practical for
  maintenance and possible upstreaming.
- **Milestone gate:** a document is complete only when every `BUILD` item is proved, every
  `AUDIT-FIRST`/`BUILD-CANDIDATE` item is resolved, every external item is audited or explicitly
  deferred, semantic regression tests pass, and the coverage map is complete.

## Current implementation status

Status last updated: **2026-09-17**. The first six reviewed handoff milestones are implemented and
audited: **Klenke Chapters 01-08**, **Process Core and Information Flow**, **Discrete Martingale
Calculus and Exchangeability**, **Measure Convergence and Projective Construction**, and the two
consolidated **Markov Processes** specifications. The **Fourier/Classical Limit Theorems** and
**Brownian Motion/Path Regularity** handoffs have their mandatory BUILD results, with the
explicit candidate/deferred gaps retained in the coverage ledger. The **Levy/SII** implementation
includes convolution/SII
construction, compound-Poisson approximation, real and nonnegative Levy--Khintchine theorems,
continuous semigroups, weak closure, affine-triplet transformations, full real stable index and
jump-measure classification, the Gaussian endpoint, and the bounded-support regression.
**Remark 16.23 remains incomplete:** its zero-safe closed forms and necessary location
correction are implemented, but the corrected Gamma/trigonometric integral identity linking
the classified stable Levy measure to its actual exponent is not yet proved. The earlier
full-completion wording was too broad.

**The Semimartingale/SP-03 implementation contract is complete at its declared disposition
boundary.** Every design blocker now has a final disposition, all R01--R38 semantic regressions
are closed (30 theorem-level `PASS` rows and 8 intentional `STRUCTURAL-GUARD` rows), and the
aggregate declaration audit reports only Lean/Mathlib's standard axioms.  The proved named
endpoints include the Bichteler--Dellacherie characterization, Yan separation, the
Lenglart--Girsanov theorem, the Kazamaki and Novikov criteria, and the project-owned Protter and
Klenke interfaces for stochastic exponentials, continuous brackets, stopping moments, and the
21.10.3 counterexample.

This milestone claim is deliberately exact.  The explicit rational-liminf equality in Protter
I.52, the process-level Jacod initial-expansion theorem II.5, and the full Meyer--Feller theorem
III.4 remain `STILL-BLOCKED`; nonsmooth II.41 potential theory, canonical Levy cadlag
realization/decomposition, Klenke Example 21.69(ii), and the stochastic-selection extension of
I.56 remain `DEFERRED`.  None is exported under a weaker surrogate.  The authoritative current
records are the [blocker ledger](docs/SEMIMARTINGALE_BLOCKER_LEDGER.md),
[Protter ledger](docs/SEMIMARTINGALE_PROTTER_LEDGER.md),
[Klenke ledger](docs/SEMIMARTINGALE_KLENKE_LEDGER.md), and
[regression matrix](docs/SEMIMARTINGALE_REGRESSION_MATRIX.md).

The long Semimartingale narrative below is an append-only implementation history.  Its dated
intermediate statements are superseded by the four authoritative ledgers above.

**Historical Semimartingale implementation log.** Implemented foundations include Protter local
martingales and the guarded Klenke bridge, concrete initial-value counterexamples, deterministic
UI localization and integrable-envelope criteria, continuous-time bounded optional sampling,
UI martingale closure and AE-finite unbounded optional sampling, arbitrary stopping and iterated
localization under the usual conditions, continuous closed-level hitting times, corrected
centered/bounded-initial localization (also up to a random lifetime), bounded masked fundamental
sequences and continuous-local/locally-L2 equivalence, finite/random partitions, UCP bridges,
variation exponent/total-variation limits, exact infinite-partition restriction transport,
completed-cell all-times extraction, Brownian and square-minus-time martingales, strong Brownian
QV and independent cross-QV for arbitrary admissible sequences on a common all-times event,
infinite Brownian variation on every nondegenerate interval, representation-independent
elementary integration with the sharp random-partition L2 estimate (including its initial term),
good-integrator linear and localization stability, and the actual semimartingale theorems for
finite-time L2 martingales, locally L2 cadlag martingales, continuous local martingales,
adapted cadlag finite-variation processes, Poisson processes and decomposable processes.
Brownian laws, actual continuous paths and future-increment independence now
transfer to the genuine completed usual augmentation. The same process is a
true martingale, continuous local martingale and semimartingale there, with
canonical raw bracket `t`; a natural-filtration entry point derives the past
independence. This is not a claim about arbitrary enlarged filtrations.
Klenke's C1 composition formula for deterministic quadratic variation is proved:
the new limit is the actual Stieltjes integral of the squared derivative against
the original limit. Continuity, monotonicity and zero initial value are verified;
no finite-variation assumption on the original path or C2 assumption is added.
A continuous deterministic path now has proved QV limits 0 and 1 along two
genuine nested admissible infinite partition sequences. The Brownian theorem's
probability-one event therefore cannot be chosen uniformly over all sequences.
A separate continuous-path example has no QV limit along one nested admissible
sequence: its even and odd square sums stay on opposite sides of a fixed gap.
Continuous-time Doob estimates cover arbitrary finite sampling sets for `p > 1`.
For a right-continuous Banach-valued martingale with an L2 terminal value, a
measurable L2 envelope controls the entire finite interval on one common event,
with squared integral at most four times the terminal second moment. The actual
extended running supremum is proved finite before conversion to real values.
For true cadlag martingales square-integrable at every finite time, the actual
raw bracket is now proved integrable with `E([X,X]_t) = E(X_t^2)`, retaining
the initial square. The reverse and infinite-terminal results are also proved
on the actual semimartingale/local-martingale domain, as detailed below.
Raw quadratic variation now controls every individual jump, including the
initial jump, on one all-times event. If the raw bracket is integrable at each
finite time, a local martingale with an actual semimartingale witness admits
constructed square-integrable martingale localizations. The proof handles jump
overshoots and does not discard arbitrary initial values.
The full finite-time moment equivalence is now proved on the actual
semimartingale/local-martingale domain, including true martingality of the
original process and of its compensated square. The continuous-local-martingale
entry point constructs its semimartingale witness internally. The general
LM-to-semimartingale bridge remains open; the infinite-terminal source result
is proved on the existing semimartingale domain.
The normalized continuous-bracket interfaces now give Klenke's true
compensated-square martingale and the second-moment difference formula. Their
L2 criterion (Klenke 21.76) explicitly includes the initial value's L2 condition. A compensated
Poisson regression proves that a zero continuous bracket does not justify
applying the continuous-path compensated-square theorem to a jump process.
The extended terminal raw bracket now has a measurable countable-supremum
owner, an almost-sure limit over the entire half-line, and a monotone-convergence
integral identity. Finite expected terminal energy implies true finite-time L2
martingality with uniformly bounded second moments.
Finite expected terminal energy is now equivalent to true martingality with
uniformly bounded second moments on the existing semimartingale domain. A
global Doob L2 envelope controls all times on one event, including measurable
evaluations at unbounded random times. Brownian finite-time L2 is explicitly
distinguished from this global bound.
An actual L2 closing variable is now constructed, with almost-sure and L2
convergence along integer times and conditional-expectation closure at every
real time. Its second moment equals expected terminal raw energy. Whole-half-line
L2 and almost-sure convergence are now proved by conditional-expectation
contraction and a tail Doob/Borel-Cantelli argument. Protter II.27 Corollary 4
is implemented on the existing semimartingale domain, with an automatic
continuous-local-martingale entry. Removing the general local-martingale
semimartingale witness still requires III.30. A continuous oscillating-path
regression continues to guard against inferring this result from integer
convergence alone.
Stopped values can now take an explicitly supplied terminal value on the
event of infinite stopping, retaining Mathlib's existing owner at finite
times. Truncations converge to this value under an actual full-time limit
hypothesis. Optional sampling now permits both times to be infinite, including
AE-only ordering, using the actual terminal variable. It provides UI stopping
families, terminal conditional-expectation representations and Lp control.
Finite expected raw terminal energy constructs the required terminal variable
and UI hypotheses automatically, with L2 values at every stopping time.
General UI terminal construction is now proved without second moments: a
right-continuous UI martingale has an actual integrable terminal variable,
full-half-line AE and L1 convergence, and all-time conditional-expectation
closure. This also supplies the terminal variable for possibly infinite
optional sampling without a limit premise. General L1-bounded right-continuous
submartingales and supermartingales now have an actual integrable almost-sure
limit over the whole half-line, without uniform integrability or L2 assumptions
(Protter I.10). This does not assert L1 convergence or a closing identity.
The independent supermartingale sampling and regularization results are also
proved, with their precise hypotheses described below.
An arbitrary integrable closing variable now has a proved actual terminal
projection onto the sigma-field generated by all finite-time filtrations
(the closed-martingale part of Protter I.10). The explicit extended-time
martingale/UI equivalence of I.13 is proved using that terminal sigma-field.
A symmetric two-point example shows why an arbitrary closing variable cannot
silently replace its terminal projection. The book's ambient-event definition
of a stopping sigma-field differs from Mathlib's native owner at infinity.
The I.16 native-owner correction is now explicit: projected terminal values
are integrable and satisfy optional sampling and conditional-expectation
representation from any integrable closing input. An unprojected input is
allowed when it is terminal-field measurable. A two-point usual-filtration
regression rejects the unrestricted unprojected formula at two infinite times.
Weak L1 Doob inequalities are proved for arbitrary finite sampling sets, the
extended dense running supremum and all-time exceedances on finite horizons.
They require only first moments, work for Banach-valued martingales, and retain
the initial variable. A public arbitrary-index norm-submartingale interface
reuses conditional Jensen. Global and tail weak L1 estimates now control every
later time. Vanishing probabilities of arbitrarily late deviations, followed
by a countable collection of error scales, prove the actual UI half-line
limit (Protter I.12 and the UI/actual-limit-closing equivalence of I.13).
The generic Lp contraction proof also supplies the existing L2 interface.
Submartingales and supermartingales now have monotone reindexing interfaces.
Doob upcrossing estimates on arbitrary finite time partitions retain the final
sample and the finite measure's total mass, using only the endpoint first
moment. Their global dense-grid bound now supplies the general L1-bounded
convergence theorem, including the non-UI scope.
The native upcrossing count is now proved monotone under order-preserving
sampling and finite-partition refinement, including increasing horizons.
Its value depends on the endpoint set, not on repeated endpoint enumeration.
The expanding dyadic grids have increasing endpoint sets and approach each
time from the right. Finite expected dense upcrossings give one common event
for all rational levels; late oscillations would increase an attained maximal
count. This rules out excursions between integer observations. Regressions
cover a genuine non-martingale supermartingale, non-L2 initial values, arbitrary
sample-dependent escaping clocks, and the continuous integer-only counterexample.
Bounded stopping values of right-continuous submartingales and supermartingales
are now proved integrable from finite-time first moments alone. The proof uses
the original upper approximations, exact finite-partition index stopping,
one-sided countable-range conditional bounds and Fatou's lemma. No global L1
bound, nonnegativity, UI or usual-filtration assumption is added to integrability.
The general two-stopping-time conditional inequality (Protter I.17) is now
proved for progressive right-continuous processes and, under the usual
conditions, for the original processes with almost surely right-continuous paths.
The native stopping-time interface permits AE ordering and AE deterministic
bounds while retaining the original stopping sigma-field.
Protter's stopping-value characterization (I.21) is now proved: an adapted
process whose integrable stopped values all have the same expectation,
including at infinity, is a uniformly integrable martingale closed by the
explicit terminal input. The source zero-mean statement is a corollary; no
zero initial value is imposed. Deterministic-time tests alone are insufficient.
Jensen's inequality now supplies the two convex process-transform corollaries
of Protter I.19. Convex integrable transformations of finite-dimensional
martingales are submartingales; submartingale inputs additionally require a
nondecreasing transformation. Transformed integrability remains explicit.
Doob's whole-half-line Lp maximal inequality (Protter I.20) now covers every
real p > 1 and nonnegative submartingales, including coordinatewise AE
nonnegativity. The actual extended all-time supremum is bounded before any
conversion to real values; a finite uniform Lp bound supplies a measurable
Lp envelope on one common event. The Banach-valued martingale norm form is
also proved. No global boundedness, UI or L2 assumption is added to the
extended inequality.
Reverse supermartingales with expectations bounded above are now proved
uniformly integrable; reverse submartingales use the dual lower bound. The
proof derives the L1 bound and small conditional residuals from these hypotheses.
It requires neither nonnegative values nor L2 initial data. Applying this result
to the existing decreasing dyadic upper approximations proves their UI and L1
convergence, completing bounded one-sided optional sampling. This is UI of each
approximation sequence, not a Class D assertion for all bounded stopping times.
For lower-closed supermartingales, the conditional lower bound now holds at
bounded stopping times, with a first-moment bound independent of the horizon.
The actual integrable full-time limit dominates the closing input's terminal
projection. Stopped values are integrable even at possibly infinite stopping
times, using either the actual limit or the closing projection there.
The two-time conditional inequality at unbounded times (I.16) is now proved,
including two possibly infinite, AE-ordered stopping times. The native owner
uses the closing input's terminal projection; using the input itself requires
terminal-filtration measurability. Nonnegative supermartingales may use zero
as their terminal closing value. Lower closure is not an equality with the
actual path limit or an assertion of UI.
Antitone deterministic samples of a submartingale or supermartingale are
uniformly integrable without path regularity or a global first-moment bound.
For right-continuous paths, samples approaching a time from the right converge
in L1, and the expectation function is right-continuous. Under usual conditions,
this proves the necessary direction of Doob regularization (I.9), including
when only a right-continuous modification is given. The converse is now proved
as well: right-continuous expectations give a cadlag modification of the same
one-sided martingale class, unique among right-continuous modifications up to
indistinguishability. Every true martingale has such a version under usual
conditions, and an already right-continuous one has cadlag paths.
Signed one-sided weak maximal estimates now control arbitrary finite sampling
sets using only the initial expectation and terminal first moment. Countable
sampling families are almost surely locally bounded on one common event, and
clipped processes have finite rational-level upcrossings on every integer
horizon. These prerequisites assume no path regularity; they do not assert
boundedness of all real-time values of an unregularized process.
On one common event, every bounded monotone or antitone sequence in the
existing dyadic skeleton now has a finite limit. Finite-prefix embedding and
time reversal prove this simultaneously for all such sequences. Actual one-sided
filter limits and their cadlag right-limit extension are now constructed on
the existing dyadic skeleton. Usual-filtration adaptation, L1 sampling and the
modification identity under right-continuous expectations are all proved.
Without the expectation condition, the extension may change the original
process at zero. No L2, UI or global first-moment assumption is added to I.9.
The stopping-time conditional-expectation operators now commute (the second
corollary to Protter I.18): either order equals conditioning at the minimum
stopping time. This includes two infinite times and unordered stopping times,
uses the native terminal sigma-field, and needs no regularity or usual conditions.
Class D and Class DL now have distinct stopping-family definitions. Class D
uses all finite stopping times; Class DL uses a separate UI estimate on each
finite horizon. Algebra, stopping, indistinguishable-version invariance,
bounded-family equivalence and extension to AE-finite stopping families are
proved. Right-continuous true martingales are Class DL and are Class D exactly
when their deterministic-time family is UI. Nonnegative right-continuous
submartingales are Class DL. Neither general deterministic-time UI nor Class DL
is silently promoted to Class D. Protter III.9's discrete potential Doob
decomposition is proved: the actual increasing predictable part converges to
an integrable terminal variable that closes the UI martingale part, retaining
the original initial value. Uniqueness permits AE decomposition identities and
initial normalization. Continuous-time Doob-Meyer existence remains open.
The pre-stopping sigma-field `F_(T-)` now has its source generator definition,
inclusion in the native stopped field, comparison-event measurability and
zero/finite/infinite deterministic-time identities. Predictable evaluations
are measurable in this field. Finite predictable evaluations generate it;
at infinity the full generator identity uses explicitly supplied terminal
information. Zero-terminal values alone lose that information. Announcing
sequences retain the source almost-sure convergence convention, and generate
`F_(T-)` under initial completeness alone (Protter III.6). Fixed times and
infinity are predictable stopping times. The source optional and progressive
sigma-fields are now constructed, with the full predictable/optional/progressive/
product inclusion chain. Native progressive measurability is equivalent to
measurability in the progressive field, which is generated by real progressive
processes. In the constant ambient filtration it equals the product field.
Optional processes are adapted and progressive, are stable under arbitrary
stopping, and have measurable finite or explicitly terminal-valued samples.
AE-cadlag adapted processes have indistinguishable optional versions under
usual conditions. Optionality does not imply right-continuous paths. Deeper
progressive results and finer stopping-classification bridges remain open.
Accessible and totally inaccessible stopping times are now defined by finite
predictable-graph coverage and null intersections. Protter III.3 is proved:
every stopping time has a stopped-measurable accessible/totally-inaccessible
decomposition, with reconstruction and almost-sure uniqueness of both events
and restricted times. The proof uses a countable essential union and needs
only an s-finite measure, not usualness. Zero belongs to the finite graph;
infinity belongs to both classes but has no finite graph. Predictable-graph
equivalence and Meyer's Markov/Feller jump classification remain open.
Positive deterministic delays are predictable, including infinite original
times via explicitly capped announcing sequences. Predictable times are
closed under finite minima/maxima and countable suprema. The proofs retain
AE announcing convergence; exceptional zero-target samples are capped before
forming maxima. No decreasing-limit closure is claimed.
Under usual conditions, restriction of a predictable time to an
`F_(T-)`-measurable event is now proved predictable. A monotone stopping-time
limit restricted to its strictly announced event is predictable as well;
its finite coincidence with a totally inaccessible time has measure zero.
The construction uses eventually correct event approximations, tail infima
and integer caps. General `F_T` measurability is not substituted for `F_(T-)`.
Conditional future and stopping-window probabilities now have constructed
adapted cadlag versions under usual conditions. Their bounds, vanishing
after the stopping time and width monotonicity hold simultaneously in time;
versions are unique up to indistinguishability. Totally inaccessible times
have no deterministic finite atoms, permitting the source closed lower
endpoint. Arbitrary coordinate representatives are not presumed cadlag.
Protter III.10 Lemma 2's uniform small-window estimate is now proved: on every
compact horizon the running supremum of these conditional probabilities
converges to zero in measure as the width tends to zero. The proof constructs
coherent decreasing versions, retains the actual first-hit trigger event and
excludes a predictable strict-limit collision. The closed endpoint is changed
only at deterministic times; bounded random-time sampling stays left-open.
Finiteness is proved before taking a real-valued supremum. The distinct
conditional-increment modulus is addressed separately below.
Positive-time totally inaccessible jumps now have a process-level coverage
definition. Actual large jumps of a cadlag adapted process are enumerated by
stopping times: finite entries are genuine, distinct and exhaustive, and the
sequence escapes every finite horizon. The initial value is excluded from
this positive-time enumeration. Fixed-prefix residuals use actual stopped
jump coefficients with zero at infinity. Their small-jump coverage events,
short-window oscillation envelopes and fixed-cap second-moment estimates are
constructed without a moment assumption on the total jump count.
Conditional increment moduli are now defined by measurable essential suprema,
with existence, almost-sure uniqueness and coherent representatives. For a
bounded adapted cadlag process with totally inaccessible positive-time jumps,
compact moduli converge to zero in probability and L2. The whole-half-line
result is also proved when paths are constant after an almost surely finite
stopping time; this time need not have a deterministic bound. Actual tail
conditional martingales justify that extension. Arbitrary coordinate versions
are not assigned a measurable uncountable supremum. For bounded cadlag
supermartingales the global probability/L2 conclusion is now proved without
any termination-time assumption, closing Protter III.10 Lemma 3 on its source
domain. An actual terminal conditional martingale leaves a nonnegative
potential with vanishing means, which controls all late increments.
The native dyadic Doob parts now have left-continuous ceiling extensions,
proved predictability on each mesh, monotone paths and uniform second moments.
Actual terminal identities, finer-grid predictability and conditional moduli
now give L2 convergence of the terminal variables across meshes. Their
remaining conditional differences also give global maximal bounds, proving
UCP-Cauchy convergence and a common-event locally uniform Cauchy subsequence
for the original ceiling steps. Right-limit formulas and the vanishing
right-increment bound include time zero; left jumps are not substituted.
For a bounded cadlag supermartingale with totally inaccessible positive-time
jumps, the continuous predictable increasing compensator is now constructed.
It starts exactly at zero, is the actual dyadic UCP limit, and its sum with
the original process is a uniformly integrable cadlag martingale with an
actual L2 closing variable. Continuous finite-variation uniqueness is proved
without a boundedness assumption. A descending-ramp test identifies the
constructed nonzero compensator while preserving the source initial value 1.
Arbitrary stopping now preserves right-continuous supermartingales and
submartingales under usual conditions, without a lifetime bound or Class D.
Actual capped norm exits localize cadlag paths; bounded jump norms control
overshoot, while an unbounded stopping jump is explicitly retained otherwise.
For bounded jump norms, each stopped process has an actually constructed
continuous compensator, and stopping consistency follows from uniqueness.
Integrable single jumps have Class D and negative ones are supermartingales.
Clipped single-jump compensators are constructed, with ordered-difference
comparison and a vanishing mean clipping error proved.
Protter III.10 is now proved on its full source domain: a cadlag Class D
supermartingale starting at zero with totally inaccessible positive-time
jumps has an actually constructed continuous predictable increasing
compensator. Neither the process nor its jumps need be bounded. The sum is
a true uniformly integrable cadlag martingale; the increasing part also has
an actual integrable terminal envelope and all-time AE/L1 convergence.
Unbounded integrable single jumps are handled by actual clipping limits;
the selected large jumps, their integrability, local compensators and their
stopping consistency are all constructed internally. A random-amplitude ramp
regression calls this full theorem without a deterministic amplitude bound.
Integrable variation now retains actual almost-sure finiteness before real
conversion, and is equivalent to a finite expected extended total variation.
Its local form reuses native localization; the positive-lifetime mask can be
removed for variation without imposing an integrable or zero initial value.
Stopped variation retains endpoint jumps and uses the actual terminal variation
at infinity. With an integrable initial value, the actual Jordan decomposition
constructs the full-time AE/L1 terminal limit and proves Class D. Regressions
separate infinite variation from its totalized real conversion and zero variation
from integrability of a Gaussian random initial value.
At positive bounded predictable stopping times, actual martingale left limits
are identified with before-field conditional expectations; actual jumps are
integrable and have conditional mean zero, without asserting they vanish.
The actual mixed bracket of a globally bounded cadlag semimartingale and an
integrable-variation process now has integrable variation, bounded by twice
the process bound times the integrator's total variation. Its actual terminal
AE/L1 limit and Class D property follow when the initial value is integrable;
the raw initial product is retained. Actual bounded predictable jumps also
admit bounded before-field multipliers with integrable products and zero
conditional mean and expectation. The full bounded-test IV Yoeurp conclusion
is now proved below from naturality.
Naturality now has an explicit nonvacuous definition using the actual raw
bracket and an existing integrable terminal limit; continuous zero-initial
integrable-variation processes are natural. UI martingales also have the
predictable left-limit and conditional jump identities at positive AE-finite
stopping times without a deterministic bound. Actual finite mixed sums have
terminal-product expectation with only L1 integrability of the second
martingale, and are controlled by its actual variation.
Natural-martingale uniqueness (Protter III.13) is now proved: a natural
martingale is indistinguishable from zero. The proof constructs an actual
bounded conditional test martingale and passes actual mixed sums to their
raw bracket by L1 domination; it does not require L2 of the original process.
Integrable variation and naturality now have proved linear algebra and
indistinguishable-version stability. Actual sum variation measurability is
derived from adapted cadlag paths under usual conditions, not from domination
alone. A caglad integrand bounded at positive times preserves integrable
variation under the actual stochastic integral; terminal AE/L1 convergence
and Class D follow with separate integrability of the initial product.
The full III.12 terminal-integral characterization is now proved. All terminal
variables are constructed from the original processes, and the integral
against the bounded martingale is proved genuinely UI using an integrable
envelope. Naturality is also equivalent to martingality of every actual
bounded-test raw bracket; its forward direction gives UI and handles arbitrary
stopping times with the actual terminal value at infinity.
Predictable cadlag finite-variation processes now have a constructed countable
predictable cover of their positive jumps. The proof first derives predictable
Stieltjes duality from actual martingale increments, then uses the constructed
continuous compensator of a TI unit jump to exclude TI jumps. It does not
assume naturality or self-compensation. Continuous variation is proved null on
countable fibers; unit-step variation is Dirac at positive time and zero at time
zero. Discontinuous deterministic steps are also proved natural directly.
This cover now has positive, pairwise-disjoint finite graphs, constructed by
legitimate before-field restrictions. Actual jump coefficients of IV processes
are L1 without initial-value integrability. UI predictable-jump identities and
L1 before-field multipliers now allow infinite lifetimes with explicit zero
terminal jumps. Exact lifetime reindexing and finite mixed-jump sums have the
proved integrable envelope `2 C` times actual total variation.
Protter III.14 is now proved: a zero-initial predictable cadlag process of
integrable variation is natural. Actual disjoint jump sums and dominated
convergence give zero bracket means, and the constructed actual L1 terminal
gives naturality. The actual bracket with every bounded cadlag test martingale
is consequently a UI martingale (the bounded-test IV form of Yoeurp's lemma).
Protter III.15 is also proved: every predictable finite-variation local
martingale is indistinguishable from its initial-value process. This needs
neither integrable variation nor integrability of the initial value. Supplied
predictable FV local-martingale decompositions therefore have unique parts
when their FV initial values agree. The general Class D existence construction
is now also proved, as described below.
The signed conditional-modulus argument now handles bounded cadlag
supermartingales whose positive predictable jumps have mean zero, without a TI
hypothesis. Actual shifted conditional projections, coherent residuals and
valid stopping identities are constructed internally. The first-threshold
estimate uses Class D stopping-expectation continuity; the compact modulus
converges in probability for the full width-to-zero filter.
Conditional variation and the quasimartingale predicate now retain the explicit
terminal-zero tail, separate coordinate integrability, and extended variation.
Their partition supremum is proved equal to the original strict-partition
supremum. The difference of two nonnegative right-continuous supermartingales
is a quasimartingale (the easy direction of Protter III.17).
The global conditional modulus now converges in probability and L2 on this
regular bounded domain. The actual dyadic construction gives a continuous
predictable increasing Doob part and an L2 closing variable; the original TI
interfaces remain unchanged. Arbitrary stopping preserves the predictable
jump-mean condition. An integrable jump at a positive predictable lifetime
has an explicitly constructed predictable compensator of integrable variation,
with expected variation at most the coefficient's first absolute moment.
Subtracting it gives a true UI martingale. Conditional variation and its
positive/negative components also have proved refinement monotonicity after
conditioning at the initial field, including their terminal-zero tails.
The regular continuous Doob theorem now extends to Class D supermartingales
with bounded positive-time jumps, even when their values are unbounded. Actual
norm-exit decompositions and stopped consistency are constructed internally.
An arbitrary integrable jump at a positive stopping time now has an actual
predictable cadlag IV compensator with expected variation at most E norm D
and a true UI residual. The proof constructs accessible coefficient series
and continuous signed TI compensation, with disjoint first-moment budgets.
Actual signed lifetime-step series have proved uniform convergence, cadlag
paths, predictability, variation bounds and UI closure. Directed essential
envelopes of the original partition families now have integral bounds and,
under finite bounds, proved finiteness and L1 real-valued representatives.
Exact horizon extensions and shifts preserve the source terminal tails.
The regular Class D continuous Doob theorem now holds without any bound on
values or jumps. The actual full exit jump is compensated, the residual's
predictable jumps are bounded through conditional expectations, and actual
local continuous increasing parts are patched by uniqueness. The result has
a true UI martingale and a constructed integrable terminal for its increasing
part. Class D also gives integrability of actual positive predictable jumps
at possibly infinite lifetimes, with explicit zero terminal sampling.
The two actual whole-future conditional-variation envelopes are now finite
and L1 under finite global variation, and their difference equals the
original process at each fixed time. Their true supermartingale inequalities
are now proved through conditional bounds for actual directed essential suprema;
their actual cadlag right-limit construction is now proved as well.
For general predictable Doob-Meyer, an actual positive disjoint predictable
sequence now covers each fixed predictable jump test almost surely. Class D
supermartingale jumps have nonpositive before-conditional means, and removing
one such mean preserves supermartingality. Actual summable step series have
exact jump formulas; a uniform first-moment budget follows when the finite
corrected sums have been proved supermartingales. That finite induction and
the actual infinite predictable correction are now constructed. Class D gives
the summable moment budget, and coordinatewise UI limits retain the true
supermartingale inequalities. Predictable jump tests prove regularity of the
residual, without replacing it by a totally-inaccessible-jump assumption.
The general Class D Doob--Meyer decomposition (Protter III.11) is now proved:
the predictable increasing part is cadlag, starts exactly at zero, has
integrable whole-half-line variation and an actual integrable terminal limit.
The true UI martingale retains the original arbitrary integrable initial value.
An unbounded random-amplitude predictable jump regression invokes the actual
construction and identifies its compensator by uniqueness; the unit case has
mean predictable jump -1 and is outside the former regular/TI subdomains.
Quasimartingales now have an exact difference decomposition into nonnegative
cadlag supermartingales, with both first moments bounded by the original
conditional variation. This proves both directions of III.17. The coordinate
right limits require neither right-continuous expectations nor individual
modification identities. The general local Doob--Meyer theorem (III.16) is
now proved as well: actual capped norm exits construct consistent predictable
parts, with locally integrable variation, exact zero initial value, and a
local-martingale residual. The normalized form X = X(0) + M - A has unique
parts, and finite-time compensator means are bounded by the source mean drop.
A lower bound, or a finite limit, of source expectations constructs an actual
integrable terminal compensator and whole-half-line L1 convergence.
Rao's theorem (III.18) is now proved from III.16 and III.17, with an exact
X = M + A identity, unique predictable variation and local-martingale parts,
and even globally integrable variation of A on the global quasimartingale
domain. A deterministic source X(t) = -t regression tests the non-Class-D
domain of the actual local construction.
General predictable compensators are now constructed for every adapted cadlag
process of locally integrable variation, with exact zero initial value,
locally integrable variation and a local-martingale remainder, uniquely up to
indistinguishability. No integrability of the original initial random value is
required. For globally integrable variation and an integrable initial value,
the remainder is a true UI martingale and E[A(t)] = E[X(t)] - E[X(0)].
The initial-value regression calls actual existence even for nonintegrable
initial data and proves that a true UI remainder would then be impossible.
An actual UI martingale's predictable weighted jump series is also a UI
martingale under a deterministic finite-partial-sum coefficient budget.
Its terminal, coefficient integrability and genuine moment summability are
constructed, with no boundedness, L2 or semimartingale premise on the source.
Increasing locally integrable-variation processes now have increasing
predictable compensators, without an initial moment assumption. Actual signed
and norm large-jump sums have proved cadlag paths, compact variation bounds,
adaptedness, exact jumps, and stopping/event-restriction identities. Their
countable enumeration is proved equal to the original positive-time sum.
Bounded positive-time jumps give an actual bounded fundamental sequence and
local square integrability for a local martingale, even with an arbitrary
initial value. For a UI martingale and a global-IV removed process, actual
compensation gives the positive-time residual jump bound 2 beta.
The fundamental local-martingale decomposition is now constructed: for every
beta > 0, M = N + D exactly, where N and D are local martingales, D has locally
integrable variation and starts at zero, N retains M's initial value, and N's
positive-time jumps have norm at most 2 beta. The locally square-integrable
property of N is proved, not assumed. No initial moment is required.
Every local martingale is therefore a source semimartingale. The classical
and decomposable predicates are proved equivalent, and classical processes,
cadlag quasimartingales, supermartingales and submartingales are semimartingales
in the original good-integrator sense (Protter III.29--III.32).
The Chapter II integral now preserves every local martingale for adapted
caglad integrands (Protter III.33), with no boundedness, initial-moment or
local-L2 restriction. A regression retains the possibly nonintegrable initial
product for an arbitrary initial-measurable constant integrator. Special
semimartingales and uniqueness of both normalized predictable decomposition
parts are implemented (III.34); actual Rao and Doob constructions give special
quasimartingales and cadlag supermartingales. Bounded-jump FV processes now
have actual locally integrable variation.
Classical semimartingales with bounded positive-time jumps now have an
actually constructed predictable decomposition (III.35), and continuous
classical processes have continuous parts. The unique canonical parts are
available as proof-guarded functions: the martingale retains the original
initial value and the predictable FV part starts at zero. Their version
invariance, continuous-path property and sharp jump bounds are proved.
Local martingales have actual masked localizations with integrable whole-path
envelopes; their original running norm supremum is locally integrable in the
native masked sense. Poisson canonical parts are identified with the compensated
count and linear drift, while a second-moment argument proves nonuniqueness
of ordinary classical decompositions.
The original running norm supremum now has actual stopped whole-path L1
envelopes and an integrable terminal supremum (III.38). Native masked stopping
needs no initial moment; ordinary stopping explicitly requires initial L1.
The actual all-times running jump supremum includes the initial jump and
satisfies the correct factor-two path bound. Increasing bounded-jump and
unit-jump natural-valued counting processes have unique predictable
compensators without initial moments. Signed predictable Stieltjes tests
are proved for actual increasing compensators on the everywhere-good path
representation, under finite expected absolute integral.
Every predictable cadlag FV process now has locally integrable variation,
without initial moments. This applies to the actual canonical FV part of a
special semimartingale. Specialness is equivalent to having a normalized
local-martingale plus adapted cadlag locally-IV decomposition, whose
predictable part is genuinely constructed by compensation.
Special semimartingales have native whole-path L1 envelopes and locally
integrable original running norm and jump suprema. The actual jump supremum
is now proved adapted and compatible with closed and masked stopping.
Local integrability of running jumps gives local IV for FV processes; local
integrability of running norms implies that of running jumps for any adapted
cadlag process. A cadlag counterexample proves that the factor two is necessary.
Both running-supremum criteria now characterize specialness on the classical
semimartingale domain. Actual compensation, not a proposed predictable part,
proves the converses. Extending this entry point to every good integrator
still requires the separate Bichteler--Dellacherie theorem.
The unique predictable compensator is now a canonical object on its proved
locally-IV domain, coherent with the canonical special decomposition.
It has no jump at a totally inaccessible time; a source with only totally
inaccessible positive jumps has a continuous compensator. Predictable sources
are identified with their compensators after subtracting the original initial value.
Predictable quadratic variation is constructed as the compensator of the
actual raw bracket. Its existence is proved for native locally-square-integrable
local martingales and for AE-continuous semimartingales, without initial moments.
General local-martingale squares and products minus their raw brackets are local
martingales; the actual angle also compensates the square on its existence domain.
For continuous sources, the angle equals the raw bracket minus the initial
square. A genuine constant-one regression rules out the unnormalized equality.
Mixed predictable covariation is now the same canonical compensator applied
to the actual raw mixed bracket. Its existence follows from the two square
domains, including native locally-square-integrable martingales. Symmetry,
diagonal agreement, full product characterization and polarization of the
actual selected processes are proved; no monotonicity is asserted for mixed
covariation. Compensator linearity and arbitrary stopping, and stopping of
both square and mixed angles, retain zero and infinite lifetimes.
The actual Poisson and compensated-Poisson angles equal their linear drift
under the stated past-independence assumption. Positive rate makes the raw
and predictable brackets genuinely different, by the Poisson second moment.
The mixed angle is bilinear on its actual constructed domains, invariant
under indistinguishable source versions, and compatible with stopping either
argument. If one source is AE-continuous, its actual mixed angle exists and
equals the existing continuous covariation, without a square-angle domain
for the other source. The original initial product is subtracted correctly.
Continuous FV compensation is now a shared interface for square and mixed
angles. Raw mixed brackets also commute with a common initial event mask.
Yoeurp's lemma is now proved for general native local martingales and
predictable cadlag finite-variation processes. Actual deterministic
variation-budget localizers and the existing UI predictable-jump series
prove it without initial moments. A regression separates the centered UI
bracket from the potentially nonintegrable original initial product.
The nonexplosive counting-process definition, its actual compensator,
actual hitting-time arrivals and their finite-support count representation
are proved. Eventual infinite arrival times are allowed. Poisson processes
enter this domain, while a deterministic single-jump example is proved
non-Poisson and has itself as its actual compensator.
The reverse nonexplosive arrival construction is proved, including exact
native-hitting recovery and adaptedness precisely when each original
arrival is a stopping time. Initial completeness alone extends this to
common-AE valid stopping-time arrivals through a legal all-path version.
A predictable UCP limit and the actual integral against a predictable
integrator have genuinely predictable versions. Predictable FV integration
has actual locally integrable variation, and its canonical compensator is
the integral minus the original initial product, without an initial moment.
Signed kernel tests now accept AE-monotone/cadlag sources through actual
versions. On everywhere-good increasing sources the finite-time Chapter II
consumer proves integrability and equality of expected centered integrals
under the corrected expected-absolute-integral condition.
The full corrected III.19 consumer now uses the original AE-regular
source's actual integral and the sole canonical compensator's actual integral.
It constructs a legal source-kernel version and proves centered L1 and
expectation equality without assuming integrability of the initial product.
The corrected III.20 formula is proved on the predictable FV domain and
extended to native local martingales. The literal left integral plus raw
covariation is identified with the actual pathwise right-value integral;
its actual canonical compensator equals the left integral. The original
raw initial product is retained. Local martingales with FV paths have
locally integrable variation, and specialness is equivalent to local IV
on the adapted cadlag FV domain.
Raw QV/QCov are proved invariant under absolutely continuous measure
changes and between usual semimartingale filtrations; the target measure's
semimartingale domain is constructed. With one continuous source, both
actual mixed-angle domains and their environment invariance are also proved.
No such invariance is asserted for general discontinuous angles.
The exact raw natural information of a closed single-jump count is now
identified with its censored lifetime, including the observation endpoint.
A two-point nonmeasurability regression shows why capping the lifetime at
the observation time loses information. Further actual-integral regressions
verify the original initial-product and centered-integrability distinctions.
Actual counterexamples now show that predictable QV can change under
equivalent probability laws or a larger usual filtration, even when the
same bounded process remains a UI/L2 martingale in both environments.
Raw QV stays unchanged and both actual angular domains are constructed.
Single-jump conditional expectation is proved for both the raw natural
filtration and its genuine usual augmentation. Right continuity and
completion are handled separately, including the closed occurrence endpoint.
The cumulative hazard uses extended nonnegative values and pre-jump survival;
finite-horizon bounds, stopped expectations and survival-increment balance
are proved before conversion to real values. Native local moments at a
positive time with zero-one preceding information imply an actual moment
there. Revealing the centered geometric variable at time one now gives an
actual UI martingale in a usual filtration which is not locally square
integrable, even with native masked localization. Local integrable variation
similarly forces integrability of the increment from zero at a positive
time with zero-one preceding information, without imposing an initial moment.
A symmetric reciprocal-uniform variable has an atomless law and infinite
first absolute moment. Its actual single-jump process is now a local
martingale when the magnitude is initially known, but not in the smaller
usual reveal filtration; it remains a finite-variation semimartingale there.
Both filtrations use the genuinely completed probability space.
The geometric model also shows that shrinking a usual filtration can remove
the actual angular domain, although the raw QV and semimartingale remain.
The larger full-information filtration has a constructed angle equal to raw QV.
Under a positive pre-jump survival bound at a finite cap, the actual closed
count minus its stopped hazard is now a UI martingale. The original stopped
hazard is predictable, without a version replacement. Completion preserves
UI, and an already right-continuous filtration's true, UI and local martingales
survive genuine usual augmentation with their original localization masks.
The sole canonical compensator of the finite-capped closed count is now
identified with its actual stopped hazard under the positive-survival guard,
including a possible initial count atom in the martingale remainder.
The stopped-hazard expectation and L1 identity no longer need that guard:
pre-jump survival is positive at almost every lifetime, including a terminal atom.
The uncapped count minus hazard is a true martingale in the raw natural
filtration, and the actual stopped hazard is finite, monotone and cadlag
on one common event. The sole canonical compensator is now identified with
the original uncapped stopped hazard, both on the lifetime space and for any
measurable extended lifetime on an arbitrary probability space, in its
genuinely completed usual natural filtration. No deterministic survival guard
is required, and zero and infinite lifetimes remain allowed.
The canonical compensated count is uniformly integrable over the whole
half-line, by an actual integrable hazard envelope. Native martingales also
pull back along measure-preserving maps when the filtrations are exact comaps.
Uniform integrability now transfers to an arbitrary original lifetime space
through the actual measure-preserving map. Almost-surely finite lifetime laws
have the actual native CDF/Stieltjes hazard expression with the pre-jump
denominator and the original `(0,t]` interval. Diffuse laws have continuous
stopped hazard paths and the actual logarithmic compensator on the genuine
usual completion. CDF continuity is equivalent to the original law's null
singleton condition; no density is required. Real logarithms are used only
after proving positive survival and finite extended hazard.
Absolute continuity of each actual finite positive lifetime measure gives
locally absolutely continuous stopped hazards via a genuine RN primitive.
The native exponential law with any positive rate gives cumulative hazard
`r*t`, with its rate retained. The CDF-function absolute-continuity hypothesis
now gives locally absolutely continuous paths of the actual original-space
compensator, via the original derivative and fundamental theorem of calculus.
For a lifetime with the native exponential law, that same compensator is the
rate times its actual stopped clock. These complete III.21's two corollaries,
in addition to the integral and continuous-law logarithmic formulas.
The original cumulative hazard is now jointly measurable for a lifetime
kernel. Its actual history/lifetime law gives the stopped-hazard mean,
common-event finite monotone cadlag paths, and a genuine integrable envelope
for uniform integrability. Before the next indexed arrival, every raw
natural-count event is represented by its actual finite arrival history.
Actual interarrival durations are positive and recover all original arrivals
by prefix sums, with an explicit absorbing infinite tail.
The actual count's raw natural filtration is now proved right-continuous
by freezing observations in its pathwise no-jump windows. Each finite
history is measurable at its actual preceding arrival, and arrival/gap
histories generate exactly the same sigma algebra. Native conditional
lifetime laws transfer the real mean, UI and common-event paths to the
original space without standard Borel assumptions on that space or history.
Stopped-field history gives predictable delayed kernel hazards, with exact
calendar-stop/absorbing-gap clock identities. Bounded history clocks have
actual survival-increment integral identities and preserve global UI.
Conditioning on actual arrival history or actual gap history now gives the
same evaluated native conditional law on one common event. Safe elapsed
clocks are measurable, monotone and calendar-bounded, including infinite
starting times; they identify the original arrival events and delayed hazards
with actual gap-clock expressions. Conditional clock UI and zero-increment
integrals now hold on the original space, and the safe clock preserves the
hazard's common-event finite monotone cadlag paths.
Each actual arrival indicator minus its delayed conditional hazard is now
a true globally UI martingale in the raw natural count filtration. The
original positive arrivals form a native localizing sequence. Birth-endpoint
zero support makes the total hazard a genuinely locally finite predictable
series with zero initial value and common-event monotone cadlag paths.
Its finite prefix retains the current pending stage; stopping at an actual
arrival gives the exact shorter prefix of compensated indicators.
The total compensated count is now a local martingale in the genuine usual
natural augmentation. The actual count's domain and full uniqueness identify
its sole canonical compensator with the original conditional-hazard series,
whether conditioned on preceding arrivals or actual gaps. Its completed-
plus-pending finite formula includes the initial interval and arrival endpoints.
All conditional laws are computed under the original measure. Independent
laws and finite-past recovery of latent durations provide prerequisites for
the independent-interval specialization. That specialization is now proved
for positive independent latent durations with nonexplosive extended prefixes:
the sole compensator has the corrected completed-plus-pending marginal-hazard
formula, including count zero. Absorbing infinite tails do not require false
global independence of the actual gaps. General adapted counts now have
everywhere-valid arrival representatives with indistinguishable counts;
indistinguishable processes have equal genuine usual natural filtrations.
The general AE-count entry point now identifies the original count's sole
compensator in its genuine usual natural filtration. Its actual arrival
representative retains all original hitting times on a common event; the
original count selects the completed and pending terms. A true continuous
density also gives the conditional small-window hazard-rate limit. Censoring
has actual, unnormalized observation and arrival submeasures, with ties
assigned to arrivals and retained by the compensation formulas below.
The explicit density primitive now identifies the original single-jump
compensator with the stopped density-over-survival integral, including
initial atoms and infinite lifetimes. A distinct cause-specific hazard uses
the true arrival submeasure and the full observation survival denominator;
its actual expectation, L1 and common-event monotone cadlag paths are proved.
The marked pair's genuine raw natural filtration is right-continuous.
The marked count minus its actual cause hazard is now a true martingale;
canonical uniqueness identifies its sole compensator in the genuine usual
natural filtration. Arbitrary dependent censoring has the corresponding
actual measure formula, with ties assigned to arrivals. The marked density
formula and global uniform integrability of the stopped cause hazard are proved.
Crude-window probabilities are decomposed exactly into the cause window and
the extra within-window censoring term. Finite absolutely continuous laws
have their native RN right-window rate almost everywhere.
The actual within-window censoring error now has rate zero almost everywhere.
Absolute continuity of the original real arrival law constructs the true cause
RN density and identifies the genuine crude-window limit almost everywhere.
Its stopped integral is the sole censored compensator, and subtracting it from
the original observed arrival count gives a local martingale. The net-rate
corollary requires net and crude rates to agree only where joint survival is
positive; no equality after the risk set disappears is imposed.
This closes the printed dependent-censoring rate application, without asserting
pointwise limits at all censoring atoms or arbitrary-filtration invariance.
Native local martingales with nonnegative positive-time jumps now have
totally inaccessible jumps, via actual UI localization and predictable tests.
On the locally integrable-variation domain, this gives the precise equivalence
between nonnegative-jump sources having totally inaccessible jumps and their
sole canonical compensator being continuous.
For Poisson processes, both the original jumps and every original hitting
arrival are totally inaccessible when future increments are independent of
the specified past. Rate zero and infinite arrival tails remain allowed.
That whole-past independence is now derived from the genuine joint independent
increments. The raw natural filtrations of the original count and its real
cast agree exactly, and genuine completion retains the same Poisson process.
Consequently both its jumps and its original hitting arrivals are totally
inaccessible in the usual augmentation of its original natural filtration.
Original coordinate measurability is explicit; no arbitrary-enlarged-filtration
claim is made.
Actual finite future-increment vectors now retain their stationary laws after
every genuinely finite stopping time when increments are independent of the
specified past. Bounded continuous vector tests also have the stationary mean
given the original stopped field. Joint independence and sampled-vector AE
measurability are proved, not supplied as assumptions. No usualness, initial
normalization, moments or deterministic stopping bound is imposed.
The original centered running supremum vanishes on shrinking initial windows,
without monotonicity of the horizons.
Finite announcing times and uniform stopped-window laws now show that every
positive-time predictable jump of a cadlag stationary-increment process whose
increments are independent of the stated past vanishes. Integer truncation and
the existing predictable-test classification give actual totally inaccessible
jumps. For a measurable, AE-zero-initial real SII process, genuine completion
and the usual augmentation of its own natural filtration supply the canonical
consumer without replacing the process. This closes general cadlag real-SII
total inaccessibility, but it does not construct a cadlag realization from a
Levy triplet or prove Levy decomposition or Meyer's strong-Markov/Feller theorem.
The III.8 foundation now also constructs the terminal real RN density and its
canonical cadlag conditional-expectation density process under usual conditions.
It is a true uniformly integrable martingale, is simultaneously nonnegative,
and integrates to the target law on every current-filtration event. Under
`Q ≪ P`, every fixed-time density is strictly positive `Q`-almost surely; under
equivalence it is also strictly positive `P`-almost surely. These are
coordinatewise statements, not an uncountable-time pathwise assertion. At each
fixed time the forward and reverse density processes are reciprocal under
equivalent laws. Bayes' formula is proved first without division under `Q ≪ P`,
then in quotient form on the natural `Q`-AE domain (and `P`-AE under
equivalence). Right-continuous modification uniqueness upgrades the reciprocal
identity to one common event at all times, proving all-time strict positivity
and a càdlàg inverse process under equivalence. At every everywhere-finite
stopping time, the sampled density is the conditional expectation on the native
stopping field and integrates to the target law on every stopping-time event;
its exact strict-positivity and reciprocal AE statements are also proved.
The joint capped-exit sequence for `Z` and the reverse density is localizing
under both equivalent laws. It controls both density left limits and proves
`Z_{t-} > 0` with the exact reciprocal identity for every positive time on a
common event. Multiplication by `Z` now transfers true martingales and uniformly
integrable martingales from the target law to the source law under equivalence,
using the division-free Bayes identity and an actual integrable closing
variable. The same result for local martingales is obtained from their native
masked fundamental sequences. Protter III.39 is now proved under equivalence:
the raw-covariation correction has a division-free reverse-density form and an
exact right-value Stieltjes representation. Its true initial term is retained,
so no `Z_0 = 1` assumption is hidden. Protter III.40 is also proved on the
actual locally-integrable raw-covariation domain: the canonical predictable
bracket is integrated against the reverse density left limit, which equals
`1/Z_-` at every positive time on one target-full-measure event. Under merely
one-way `Q ≪ P`, a separate first-lower-threshold sequence now stops `Z` before
it enters `(−∞, 2⁻⁽ⁿ⁺¹⁾)`. Exact finite-stopping density integrals and
Borel--Cantelli prove that this sequence tends to infinity `Q`-almost surely;
up to each exit, every positive-time `Z_-` is bounded below and `1/Z_-` is
locally bounded. Finite-stopping integrability and Bayes identities now also
give the one-way density criterion: if `Z * X` is a `P`-local martingale, then
`X` is a `Q`-local martingale. Its proof retains the native initial masks and
uses the common minimum of the source localizer, the lower-density exits and
deterministic caps. Protter III.41 is now proved as a genuinely one-way result:
the predictable covariation correction is integrated against the target-law
`1/Z_-`, while globally regular clipped reciprocals justify the source-law
product algebra on every lower-density window. No reverse density or hidden
equivalence assumption is used.
The incremental check and axiom counts at that stage are recorded in the dated
Semimartingale status entry.  The then-open Lenglart--Girsanov III.42,
Kazamaki--Novikov and Bichteler--Dellacherie gates were closed later; the
2026-09-17 ledgers above supersede this historical checkpoint.  No full build
was run for that intermediate stage.
Conditional window sampling is now proved at every bounded stopping time:
the sampled process is the conditional probability of the corresponding
random-time window given `F_S`. Its integral on an `F_S` event equals the
window-event probability, yielding the threshold bound on the actual trigger
event. Countable stopping fibers and dominated right-grid limits prove this
without assuming an optional-projection theorem or a martingale input.
For finite stopping times, the native `F_T` is now proved equal to the field
generated by adapted cadlag samples (Protter I.6), equivalently by optional
samples. The source AE-cadlag version is proved under usual conditions.
The construction reveals arbitrary `F_T`-measurable coefficients at the
stopping time, with no premature `F_0` measurability or integrability premise.
At arbitrary, possibly infinite times the optional generator identity retains
explicit terminal-filtration-measurable input.
The discrete predictable-increasing-process energy lemma used in Protter
III.10 is now proved: a zero-starting increasing predictable process with
integrable terminal limit and conditional remaining means bounded by `N`
has terminal second moment at most `2 N^2`. Terminal L2 is derived by
truncation and Fatou, not assumed. For a discrete supermartingale bounded
by `K`, the existing increasing Doob part has an actual terminal L2 limit
and the uniform bound `8 K^2`. These are prerequisites, not a claim of
continuous-time Doob-Meyer existence or predictability of a limiting compensator.
Absolute-continuous finite-measure changes, finite-mass countable mixtures and Stricker
filtration shrinkage are proved. Random variation need not be integrable.
Source left-limit/jump conventions, strict-before-stopping patching, and predictable
measurability of left-continuous adapted processes are proved. The source caglad-generated
predictable sigma-field is identified with Mathlib's existing owner, and the full source
simple-predictable class is adapted, caglad and predictable, including repeated endpoints.
The elementary integral process has a first-exit maximal estimate and full UCP continuity
on the simple predictable source class (Protter II.11), including a UCP-Cauchy estimate.
Corrected source UCP density (Protter II.10) is also proved using actual finite oscillation
partitions, with the first interval and independent initial value retained. Sequential UCP
completeness for adapted cadlag processes is proved under usual conditions and a finite measure:
the limit is constructed, adapted, and everywhere cadlag after one initial null-set reset.
The Chapter II stochastic integral is now constructed as the unique cadlag UCP limit of
elementary integrals. It is linear up to indistinguishability, continuous in UCP on the
adapted-caglad domain, independent of the simple approximation, and starts at `H_0 X_0`.
It is invariant under indistinguishable integrators and agrees with the pathwise
Lebesgue-Stieltjes integral on common-event finite-variation paths (Protter II.17).
Stopping the integral, stopping the integrator and closed-interval cutoff agree
(Protter II.12), including zero and infinite stopping times. The jump formula
`Delta(H . X) = H Delta(X)` (II.13) holds on one common full-measure event,
including time zero. Absolutely continuous finite changes of measure preserve the
integral (II.14), with target usual conditions explicit. The integral under a countable
probability mixture agrees with every positive-weight component integral, and any two
probabilities admit a common adapted cadlag integral version (II.15 and its corollary).
The integral is also invariant between any two usual filtrations to which the integrand
is adapted and under which the integrator is a semimartingale (II.16); neither filtration
needs to contain the other. Local behavior on path-agreement events and pathwise
Stieltjes agreement on the finite-variation event are proved (II.18), without requiring
these events to have full probability. The path-agreement assertion also holds for
stochastic intervals `(S,T]`, allowing `T = infinity` and distinct integrand values
at `S` (II.18 corollary). The corollary's FV assertion is also proved from BV
on the open interval, retaining the right-endpoint jump; an infinite upper endpoint
only requires finite-subhorizon variation bounds. Integration preserves
semimartingales, and iterated integration equals integration against the product
of the two adapted-caglad integrands (II.19), including the full initial term.
Finite variation is also preserved, even on individual FV paths up to one null
set. Bounded simple integrands preserve martingales, and bounded adapted-caglad
integrands preserve finite-time square-integrable martingales, with the sharp
L2 bound and without deleting the initial value. General adapted-caglad integration
preserves locally square-integrable martingales (II.20), by explicit masked joint
localization; no initial integrability assumption is imposed. General local-martingale
preservation beyond the locally-L2 case remains open. Random-partition Riemann
approximation is proved for general adapted cadlag and caglad integrands (II.21).
The increment-only sums converge to the integral of the source left-limit process.
For caglad integrands this is also the original integral minus `Y_0 X_0`.
The proof controls displaced jumps and the initial sampling cell; it does not
assume uniform convergence of sampled discontinuous integrands. Neither initial
random variable must vanish or satisfy a separate integrability bound.
The canonical raw quadratic variation is now constructed as
`[X,X] = X^2 - 2 (X_- . X)`. It is adapted and cadlag, has increasing paths on
one common full-measure event, starts at `X_0^2`, and has jump `(Delta X)^2`.
Actual random-partition square sums, including the initial square, converge
to it in UCP. Stopping commutes with this quadratic variation, including zero
and infinite stopping times. Mixed covariation is now defined by polarization of
this same owner, with its initial product, cadlag/FV paths, bilinearity, jump
products, random-partition UCP limits and stopping in either argument proved.
Integration by parts and closure of semimartingales under products are proved.
The common-event Cauchy--Schwarz increment and total-variation bounds and the
weighted Kunita--Watanabe inequality are proved, for arbitrary measurable weights
and possibly infinite energies. Increment-measure and explicit-initial-term
interfaces remain distinct. The expectation/Lp corollary is proved, including
both L1/L-infinity endpoints and measurable random energies for arbitrary jointly
measurable weights; no adaptedness or moment assumption on the weights is added.
Its value is independent of the null-event Stieltjes version. The continuous
part of the raw square bracket is now constructed from that same measure: it
is adapted, continuous, increasing, zero-starting and a finite-variation
semimartingale. The exact decomposition retains the initial square and the
summable squared jumps over `(0,t]`; indistinguishable versions and continuous
processes have the corresponding invariance and normalization identities.
Mixed continuous covariation is also constructed by polarization of these same
components. It is adapted, continuous, zero-starting and FV, with bilinearity,
version invariance, the correct diagonal and an absolutely summable mixed-jump
decomposition retaining the initial product. Continuous square and mixed brackets
commute with stopping, including stopping either mixed argument alone. Closed
stopping retains the endpoint jump, including at zero; infinite stopping is also
covered. Protter II.30's actual weighted mixed-increment sums now converge in UCP
to the integral of the source left limit against the raw mixed bracket. Cadlag
weights and random partitions are allowed, without boundedness or moment
assumptions; the partial terminal cell is retained. Protter II.29 is also proved:
the covariation of two Chapter II integrals is the integral of the product of
their integrands against the raw mixed bracket, and the diagonal gives the
corresponding square-integrand formula. All source initial products survive.
For continuous local martingales, the raw square bracket is continuous and
`X^2 - [X,X]` is a continuous local martingale. Centering subtracts exactly
`X_0^2` from the raw bracket. Consequently `[X,X] = X_0^2` if and only if
`X = X_0`, up to indistinguishability, without an initial moment assumption
(Protter II.27's main theorem). Corollaries 1--2 are also proved: continuous
FV local martingales are constant; finite variation or a flat bracket on an
ordered stopping interval forces constancy there; and the raw mixed bracket
of locally-L2 martingales is uniquely characterized by its local-martingale
residual, FV paths, jumps and initial product. Zero/infinite stopping times
and AE order are allowed. Corollary 5's single-event all-intervals constancy
theorem is proved, including open, half-open and unbounded intervals. Equal
bracket endpoints detect process constancy on the entire closed interval;
arbitrary random endpoints can be substituted without measurability or
stopping assumptions. The moment/terminal corollaries are proved on the
actual semimartingale domain, as detailed above. The
discontinuous compensated-Poisson source counterexample is also proved below.
Protter II.26 is proved for general cadlag FV paths: raw QV is the initial
square plus the actual squared-jump series, and its continuous part is zero.
The proof includes path-local FV agreement, countable jump support, absolute
jump summability and the distinction between left and right endpoint limits.
Quadratic pure jump is a property of this same bracket, invariant under
indistinguishable versions and stopping; it includes continuous FV drift.
Protter II.28 is proved: if either semimartingale is quadratic pure jump,
their raw mixed bracket is the initial product plus the actual absolutely
summable mixed-jump series. A continuous FV argument leaves only the initial
product, even against a discontinuous semimartingale. Quadratic pure jump is
also stable under addition, subtraction and real scaling.
No competing normalized bracket is built.
The constructed integral is linear in the semimartingale integrator as well:
addition, real scalar multiplication and subtraction hold up to indistinguishability.
These statements retain the source initial term; subtracting two stopped integrators
removes their shared initial value, including at zero or infinite stopping times.
Canonical total/positive/negative variation processes and their random Stieltjes measures
are constructed. The pathwise finite-variation integral has the source initial term,
linearity, variation bounds and dominated convergence; it is measurable, and adapted for
progressive integrands. Local pathwise integrability gives cadlag finite-variation integral
paths and their semimartingale property. The full source simple-predictable class has
proved pathwise integrability and exact agreement with elementary integration, including
repeated endpoints and arbitrary finite coefficients. Continuous-FV C1 change of variables
and its substitution corollary are proved. Protter II.31's right-continuous FV
C1 formula is also proved, with an absolutely summable jump correction and
finite-variation preservation. Its Chapter II integral interface subtracts
the exact source initial term `f'(0) X_0`; no initial moments are imposed.
The continuous-semimartingale Itô formula and C2 semimartingale preservation
are proved from actual Taylor sums and the existing raw quadratic variation,
without initial moments or global derivative bounds. The general cadlag
raw-bracket Itô identity and C2 semimartingale preservation are also proved,
with actual absolutely summable, finite-variation jump corrections. The
equivalent continuous-bracket formula is proved by decomposing the existing
integral into its continuous part and absolutely summable weighted jumps,
with the initial term separate. This closes the one-dimensional C2 theorem
II.32. The multidimensional extension II.33 is also proved. Its deterministic foundation
now includes a Fréchet Taylor error coefficient continuous on the diagonal
and compact metric-space càdlàg separation estimates. Vector Taylor sums,
their actual jump-series limits and absolute summability of coordinate-
semimartingale jump corrections are proved. The full finite-coordinate raw-
and continuous-bracket formulas, both ordered mixed Hessian terms, and C2
semimartingale preservation are proved on common events for all finite times.
Weighted mixed-bracket integrals split into their initial product, continuous
part and actual absolutely summable jump series. Adapted everywhere-caglad integrands have
derived compact path bounds and local Stieltjes integrability; their FV integral is
progressive and a semimartingale without a separately supplied integrability premise.
The full FV integral satisfies `Delta(H . X) = H Delta X` at every time,
including the separate source initial jump, also on one common probability-one event.
Stopping the FV integral, cutting off the integrand on `[0,tau]`, and stopping the
integrator give the same process, including zero and infinite stopping times.
FV integration is path-local, invariant under indistinguishable changes, and
UCP-continuous on the adapted-caglad class without an expected-variation bound.
Continuous-integrand Stieltjes sums converge along random finite partitions
with arbitrary within-cell tags, including endpoint tags and repeated cells.
The continuous-local example does not assume integrability of the unmasked initial value.
The source Fisk--Stratonovich integral, its semimartingale and jump properties,
and Protter II.34's C3 change-of-variables theorem are proved. The correction
uses continuous covariation and vanishes with either finite-variation argument.
Integration by parts includes the actual jump-product series; if either
argument is continuous, the classical form follows. Complex coordinate
semimartingales, their adapted caglad source left limits, and complex
integration through the existing real integrals are constructed. Entire
analytic transformations preserve this coordinate predicate, and real
linear functionals commute with complex-integrand integration. Protter II.35--II.36's
complex-analytic Itô formulas are proved: the cadlag formula uses the complex
bilinear continuous bracket and the actual absolutely convergent jump correction;
the continuous case also uses the original raw bracket through a proved
zero-plus integral comparison. The complex bilinear bracket is distinct from
the nonnegative real energy bracket. The stochastic-exponential product now has
proved convergence, equivalent raw/continuous-bracket expressions and an exact
minus-one-jump zero criterion. For continuous integrators it is a strictly positive
continuous semimartingale satisfying the source integral equation. For general cadlag
integrators the same product-defined process is adapted and a semimartingale, and
now satisfies the integral equation, including zero and negative jump multipliers.
The proof retains `exp(X(0))` and adds no initial-moment assumption. Protter II.38's
product identity and continuous inverse formula are also proved, with explicit
initial-value corrections where the raw bracket is used. The stochastic exponential of a
continuous local martingale is a continuous local martingale. The compensated
complex characteristic exponential is also proved to be a local martingale;
when the continuous bracket is time it is a true martingale. Levy's real Brownian
characterization is proved in both directions, with the specified filtration's
past-independence condition retained. Deterministic continuous brackets also
give Gaussian increments independent of the past, allowing flat clock intervals.
Finite linear combinations have the full double-sum continuous-bracket formula;
orthogonal coordinates give the expected Gaussian projection laws. Levy's
multidimensional characterization is also proved: the joint increments have
the product Gaussian law, and the entire coordinate processes are mutually
independent. Zero-dimensional vectors and repeated times are included.
For a common continuous bracket and zero cross brackets, harmonic functions
on an arbitrary open domain preserve continuous local martingales whose
paths stay in that domain. The proof uses
Mathlib's Laplacian and harmonic predicate, with no initial-moment assumption.
The unqualified subharmonic claim in Protter II.41 has a formal counterexample:
`exp(x^2/2)` has strictly positive Laplacian, but its Brownian composition is
not integrable at time 1. The corrected classical C2 open-domain theorem is proved:
nonnegative Laplacian gives an actual masked local submartingale, and a
common-event integrable envelope on each compact time interval gives a true
submartingale. Compact domain exits, smooth extensions and the zero-exit
initial-event branch are constructed. Raw common clocks are centered by their
initial value, not assumed to start at zero. Nonsmooth potential-theoretic
subharmonic functions are not covered; their source interpretation remains under audit.
Dambis--Dubins--Schwarz is proved for zero-starting continuous local martingales
with unbounded quadratic variation. The actual raw-bracket inverse gives a
Brownian motion adapted to `F_(T_s)`, with Gaussian increments independent of
that entire past. Clock substitution recovers the original process on one
event, and the original clock gives stopping times in the sampled filtration.
Flat clock intervals and a positive inverse time at level zero are allowed.
The same Brownian process is also proved adapted with independent future
increments in the right-continuation `G_(s+)`, which is usual; the original
clock remains a family of stopping times there. No equality `G = G_+` is assumed.
The compensated Poisson process `N_t - rate*t` is a proved true martingale
when future real increments are independent of the chosen filtration's past.
Its first moments, cadlag/FV paths and semimartingale property are derived.
Its canonical raw bracket is proved to be `N`, by identifying square-sum
probability limits. At unit rate, the compensated path is nonconstant on every
nondegenerate interval, while the bracket has a nontrivial constant right
neighborhood at every time on one event. This proves the source counterexample
after II.27 Corollary 5 and rules out a continuous-local-martingale property.
For Levy's stochastic area, the actual antisymmetric integral, zero start,
continuous-local-martingale preservation, mixed brackets and continuous energy
are proved. The terminal Riccati functions and exponential bound are also
proved for every real Fourier parameter. The characteristic function
`E[exp(i u A_t)] = 1 / cosh(u t)` is now proved for independent Brownian
coordinates under an explicit usual filtration with independent future
increments. Its positive-time density is also proved:
`1 / (2 t cosh(pi x / (2 t)))`. The law at time zero is Dirac at zero.
The actual compensated area exponential has proved semimartingale, continuity,
initial/terminal and norm properties. Its Riccati coefficients satisfy the
existing stochastic-integral equations along continuous zero-starting FV
clocks. The actual exponential Ito drift cancellation and complex
local-martingale conclusion are proved.
The squared-radius integral equation and C1 finite-variation clock substitution
are proved, with the source initial product retained. In particular, integrating
against a constant does not in general give zero.
The continuous-FV multiplier formula, C1-weighted squared-radius equation and
actual integral representation of the area exponent's real part are proved.
The latter identifies the radial FV drift canceled by the complex bracket
in the exponential's Ito formula.
Continuous brackets under C1 FV-clock multipliers, isotropic finite sums of
actual stochastic integrals and their two-coordinate interfaces are proved.
The area energy under a common orthogonal clock is the clock integral of
`X^2 + Y^2`, without Brownian-law or zero-initial-coordinate assumptions.
For zero-starting coordinates with a common raw FV clock, the squared-radius
bracket and its zero mixed bracket with area are proved. The compensated
exponent's actual complex bilinear bracket is
`J_Q((X^2+Y^2)(alpha^2-u^2))`. The norm bound upgrades the stopped exponential
to a true martingale and gives the inverse-cosh characteristic function at
any deterministic terminal level of the common raw clock.
The complex integral now has initial-product, version-invariance, real-integrator
reduction and real-inner-integral associativity interfaces, all derived from the
existing real owner. Continuous real local martingales admit complex caglad
integrands without an additional local-L2 hypothesis. The Brownian interface
derives its canonical brackets from the existing Brownian law and independent
normalized sums. The area at time zero has the Dirac law at zero; it is not
covered by the positive-time density formula. The density is normalized and
identified by Fourier uniqueness using a proved sigmoid/Beta/Gamma integral.
Stochastic-exponential uniqueness, Lenglart--Girsanov III.42,
Kazamaki--Novikov and Bichteler--Dellacherie were subsequently proved.  See
[the implementation ledger](docs/SEMIMARTINGALE_STATUS.md), the four
authoritative Semimartingale closure ledgers linked above, and
[the all-design gap inventory](docs/DESIGN_GAPS.md).

### Formalized mathematical definitions

- Probability generating functions, factorial moments, random sums, multinomial laws,
  Poissonization, and Galton-Watson extinction probabilities.
- Empirical distribution functions and empirical probability measures.
- Global and sigma-finite local convergence in measure, fast local convergence, exhaustion
  pseudometrics and a.e.-class metrics, and sigma-finite uniform integrability.
- Process modification and indistinguishability; finite-dimensional, coordinate-product, and
  path-space laws; stationarity and stationary increments.
- Common-event continuous, left-continuous, right-continuous, cadlag, caglad, monotone,
  locally finite-variation and finite-total-variation path properties.
- Total, positive and negative variation processes; their locally finite random Stieltjes
  increment measures; and the pathwise finite-variation integral with a separate initial term.
- Natural filtrations, usual conditions and usual augmentation, adaptedness, progressive
  measurability, random times, stopped processes, and open-set first hitting times
  of right-continuous processes.
- Source left-limit and jump processes with `X_(0-) = 0`; strict-before-stopping `X^(T-)`
  with no evaluation at infinity, and strict-past predictable sampling grids.
  The caglad right-limit process retains a separate source initial value; it is cadlag
  and adapted under a right-continuous filtration on its stated regularity domain.
- Poisson processes, arrival times, finite increment laws, and uniform-point representations.
- Discrete stochastic integrals, pathwise and predictable quadratic variation, stopped brackets,
  reverse martingales, and binary predictable representations.
- Protter masked local martingales, reducing/fundamental sequences, guarded unmasked Klenke
  localization, and finite-time square-integrable martingales.
- Class D and Class DL stopping-family predicates, and nonnegative supermartingale
  potentials with vanishing expectations (continuous-time cadlag paths are separate).
- Pre-stopping sigma-fields, source announcing sequences and predictable stopping times,
  with explicit terminal-value rather than implicit infinite-time evaluation.
- Optional and progressive sigma-fields, and strongly optional processes, compatible with
  the existing Mathlib predictable/progressive process predicates.
- Finite deterministic and stopping-time partitions, lossless finite-horizon restriction of
  locally finite endpoint sets, corrected adjacent-gap mesh, deterministic variation sums, and
  compact-by-compact UCP convergence; endpoint refinement/projection, repeated-endpoint
  invariance, uniform/dyadic admissible partitions and completed-cell sums.
- Source simple predictable processes, their exact submodule and representation-independent
  elementary integral linear map, good integrators, total semimartingales and ordinary
  semimartingales; decomposable processes
  with locally square-integrable martingale and adapted finite-variation components.
  Source representations now include common stopping-time refinements and Borel coefficient
  operations fixing zero, plus closed stopping-time cutoffs (including infinity), with the
  separate initial coefficient preserved.
  The source elementary integral process `J_X(H)` reuses that integral at deterministic stops;
  it has the proved initial/terminal conventions, adaptedness, cadlag paths, stopping identities
  and agreement with the pathwise finite-variation integral on its domain.
  The constructed Chapter II adapted-caglad stochastic integral extends that source operator;
  arbitrary predictable integration is not supplied yet.
- Canonical raw and continuous real quadratic variations and covariations, the source
  Fisk--Stratonovich integral, coordinate complex semimartingales and stochastic integrals,
  complex bilinear square brackets, and distinct nonnegative real energy brackets.
  Complex local martingales reuse the real masked coordinate predicates, and the
  compensated characteristic exponential uses the existing continuous real bracket.
- The antisymmetric stochastic area `integral X_- dY - integral Y_- dX`, with
  Protter's twice-signed-area normalization and no new integral owner.
- The normalized hyperbolic-secant density and its zero-safe probability measure,
  with Dirac at zero for zero scale.
- The product expression for the Doléans--Dade stochastic exponential, with proved
  convergence, cadlag paths, the positive-time jump identity, and a finite-variation
  pure-jump product factor. Adaptedness and semimartingale preservation are proved for
  general cadlag inputs. Its general integral equation is proved, retaining
  `exp(X(0))` and allowing zero/negative jump multipliers. The product identity,
  continuous inverse formulas, version invariance, and uniqueness are proved.
- Finite-dimensional exchangeability, symmetrization, invariant and tail sigma-fields,
  conditional i.i.d. representations, and empirical-measure factorization.
- Weak and vague convergence of measures, tightness interfaces, convergence in distribution, and
  almost-sure weak convergence of empirical measures.
- Product-coordinate and cylinder sigma-fields, Ionescu-Tulcea trajectory measures, and
  arbitrary-index standard-Borel projective constructions.
- Future sigma-fields; forward-time transition systems; homogeneous Markov semigroups; kernel-free
  event-form Markov properties; transition representations; and canonical discrete chain path
  kernels and laws.
- Strictly positive hitting and return times, reachability and communication, recurrence and
  transience, Green kernels, excursion occupation measures, invariant probabilities, periods,
  aperiodicity, and positive/null recurrence.
- Probability couplings, event and full total-variation distances, path couplings, successful
  couplings, semantic independent-coalescent kernels, and convergence-to-equilibrium predicates.
- Q-matrices, exit rates, explicit uniformization rates, safe zero-rate kernels, Poisson-mixture
  semigroups, generator recovery, canonical bounded-Q semigroups, and rate-independent
  uniformization.
- Feller semigroups on Mathlib's `ZeroAtInftyContinuousMap`, their contraction operators, operator
  semigroup laws, vague/weak transition-law continuity, and stochastic continuity at zero.
- Real triangular arrays with separate row nonemptiness, measurability, row independence,
  centeredness, variance normalization, nullness, positive-scale Lindeberg, and Lyapunov
  predicates; ordered random series and exact three-series truncation semantics.
- Probability-law convolution, convolution powers, basic and continuous convolution-semigroup
  predicates, stationary independent increments, and increment-law families.
- Law-first infinite divisibility, zero-safe finite-intensity compound Poisson laws, minimal Levy
  measures with derived sigma-finiteness, fixed-truncation Levy triplets, internal weighted-root
  triplet extraction, deterministic/positive-jump Levy pairs, continuous Levy semigroups, and
  broad/strict/indexed stable-law predicates; two-sided power-law stable Levy measures; safe
  Gamma/trigonometric stable-exponent expressions with an explicit location parameter.
- Canonical Mathlib pre-Brownian/Brownian predicates; a project-owned continuous canonical
  realization; common-event local Holder regularity below one half; Brownian bridges and
  deterministic Wiener bridges; Gaussian increment laws; zero-safe time inversion; measurable
  running suprema and last-zero functionals; dyadic Schauder approximations; and the linear
  isometric deterministic Wiener integral on the `L2` quotient.

### Formalized named theorems

- Paley-Zygmund inequality.
- Wald's identity and the Blackwell-Girshick variance identity.
- Kolmogorov maximal inequality.
- Glivenko-Cantelli theorem.
- Borel-Cantelli fast-convergence criterion.
- de la Vallee-Poussin criterion and Vitali convergence theorem.
- Doob maximal inequality.
- Doob cadlag regularization under usual conditions, with same-class preservation
  and uniqueness up to indistinguishability.
- Doob decomposition of discrete potentials, with the actual integrable terminal
  compensating variable and a closed uniformly integrable martingale part.
- Doob--Meyer decomposition for cadlag Class D supermartingales and the general
  local decomposition, including predictable-part uniqueness and the
  integrable-terminal conclusion under a lower expectation bound.
- Rao decomposition of quasimartingales into a local martingale and a unique
  normalized predictable integrable-variation part.
- Doob optional sampling theorem: discrete-time interfaces, bounded continuous-time
  martingale sampling, and UI sampling at AE-finite times, including AE ordering.
- Discrete Ito isometry for square-integrable martingales and sectionwise essentially bounded
  predictable integrands; this is separate from the constructed continuous-time integral.
- Itô's formula for scalar and finite-dimensional cadlag semimartingales and entire analytic
  functions of complex semimartingales, including the continuous cases and actual jump corrections.
- Fisk--Stratonovich change of variables on the source C3 semimartingale-integrand domain.
- Stricker's theorem: shrinking a filtration preserves semimartingales when the process
  remains adapted.
- de Finetti representation theorem and the Hewitt-Savage zero-one law.
- Prokhorov and Slutsky theorems through canonical Mathlib reuse and StochLean bridges.
- Ionescu-Tulcea and Kolmogorov extension theorems through audited canonical dependencies and
  StochLean facades.
- Chapman-Kolmogorov equations and Kac's formula for irreducible positive recurrent chains.
- Lyapunov's implication for triangular arrays.
- Lindeberg--Feller central limit theorem (forward direction).
- Kolmogorov's three-series theorem.
- Kolmogorov--Chentsov theorem.
- Blumenthal's zero--one law for the Brownian germ sigma-field.
- Paley--Wiener--Zygmund nowhere differentiability theorem.
- Brownian strong Markov theorem for finite future cylinders.
- Brownian reflection principle.
- Levy's arcsine law for the last zero before a deterministic horizon.
- Levy's real Brownian characterization by continuous local martingales and the
  canonical raw quadratic variation, with adaptedness and past independence explicit.
- Levy's multidimensional Brownian characterization by orthogonal continuous
  local martingales, including independence of the entire coordinate processes.
- Dambis--Dubins--Schwarz time change, with the source raw bracket, stopping-time
  filtration, Gaussian past-independent increments and common-event reconstruction.
- Levy's stochastic-area characteristic function for independent Brownian
  motions and its positive-time density, with the source twice-signed-area normalization.
- Levy--Khintchine theorem for real infinitely divisible laws, including existence, uniqueness,
  and the nonnegative-law specialization.
- Yan's separation theorem and the Bichteler--Dellacherie characterization of semimartingales.
- Lenglart--Girsanov change of measure, including the one-way absolutely-continuous correction.
- Kazamaki's and Novikov's criteria for uniformly integrable stochastic exponentials.

The structural de Finetti theorem and Lévy downward convergence are maintained inside this
repository under `StochLean/Internal/Exchangeability`; the public API remains the smaller
StochLean facade. The implementation is an attribution-preserving internal port of the audited
Apache-2.0 proof lineage recorded in that directory. The audited Kolmogorov-extension proof
closure is likewise maintained under `StochLean/Internal/KolmogorovExtension`. Brownian
regularity support is internal under `StochLean/Internal/Brownian`. The final Lake graph contains
no Lean dependency other than Mathlib.

All declarations in the completed milestones build without placeholders. The former external
`exchangeability` and `checkdecls` dependency has been removed: reverse-martingale convergence,
contractability, conditional independence, directing measures, finite-product factorization, and
de Finetti now compile as project-owned modules against the pinned Mathlib v4.33.0 baseline.
`Audit/NewDesignAxioms.lean` remains a focused trust check for the newer foundation modules.

### Project plan

The planned scope of this repository includes stochastic-process foundations, Markov processes and
semigroups, Brownian and Levy processes, path-space and Skorokhod weak convergence,
continuous-time martingales, semimartingales, and stochastic integration. Stochastic differential
calculus and stochastic differential equations (SDEs) will be developed in a separate package so
that this library can remain a focused and reusable stochastic-process foundation. Every new area
will retain the same audit-first milestone gate.

The detailed, theorem-level status is maintained in [SOURCE_MAP.md](SOURCE_MAP.md), while duplicate
decisions and exact Mathlib reuse are recorded in [MATHLIB_AUDIT.md](MATHLIB_AUDIT.md). README and
ledger status are updated at every document milestone before the corresponding push attempt.

## Repository layout

```text
StochLean/
  Internal/Exchangeability/              internal reverse-martingale and de Finetti engine
  ForMathlib/MeasureTheory/Function/   generic convergence and UI extensions
  ForMathlib/MeasureTheory/Measure/    locally finite and vague-convergence extensions
  Probability/Branching/              Galton-Watson foundations
  Probability/Convergence/            discrete and local convergence bridges
  Probability/EmpiricalProcess/       empirical CDF and Glivenko-Cantelli
  Probability/GeneratingFunction/     PGF and law-level random sums
  Probability/LimitTheorems/          Poisson approximation
  Probability/Series/                 ordered random series and three-series foundations
  Probability/Convolution/            probability-law convolution semigroups
  Probability/InfinitelyDivisible/    compound Poisson, Levy measures/triplets, stable laws
  Probability/Brownian/               canonical Brownian bridges and transformations
  Probability/Martingale/             discrete calculus, stopping, inequalities, convergence
  Probability/Exchangeability/        symmetry, reverse limits, empirical laws, de Finetti
  Probability/MeasureConvergence/      weak-convergence bridges and empirical weak limits
  Probability/Coupling/                generic couplings and total-variation bounds
  Probability/Markov/                  transition systems, chains, recurrence, coupling,
                                      generators, convergence, and Feller semigroups
  MeasureTheory/Constructions/         projective constructions and extension facades
  Probability/Process/                process laws, paths, filtrations, measurability, stopping,
                                      increments, and Poisson processes
Audit/Axioms.lean                      kernel dependency checks
docs/                                  normative handoff specifications
```

## Build and trust checks

```text
lake update
lake build
lake env lean Audit/Axioms.lean
lake env lean Audit/NewDesignAxioms.lean
```

The repository additionally scans project sources for `sorry`, `admit`, and project-defined
`axiom` declarations and records source coverage before a milestone is considered complete.

The checked-in operational defaults are `--memory=24000` and `--threads=3`: the project budget is
24 GB of total build memory and three Lean worker threads. These limits are configurable defaults,
not mathematical or API requirements; developers may lower or raise them in `lakefile.toml`. Lean's
`--memory` flag is enforced per compiler process, so a host requiring a hard process-group-wide
24 GB ceiling should also serialize Lake compilation jobs or apply an operating-system memory cap.
The earlier 20 GB / one-thread settings remain the documented optional conservative configuration
for memory-constrained or highly contended hosts.

## Commit and push policy

- Work is committed locally in coherent, verified increments.
- README, source map, audit ledger, and axiom audit are synchronized whenever a document reaches
  its completion gate.
- A GitHub push is attempted after each complete design document.
- If GitHub is unavailable, the push is skipped without blocking local construction. The next
  completed document is committed normally, and all pending commits are pushed together at the
  following document boundary.

## License and provenance

StochLean is released under the [Apache License 2.0](LICENSE). Klenke's book is used only as a
mathematical reference and is not distributed in this repository. The included design handoffs
contain the approved coverage and source-correction ledger, not copyrighted textbook content.

## Project notice

The project has undergone an initial review, but omissions and errors may still remain. If you find
an issue, please notify the author so that the library and its documentation can be corrected and
completed.

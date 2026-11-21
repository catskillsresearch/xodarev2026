# Protter Chapters I--III disposition ledger

This is the exact numbered-source disposition required by the SP-03 completion
gate.  `RESOLVED` means that the cited project owner contains a compiled
theorem or a checked bridge to a canonical Mathlib result.  `STILL-BLOCKED`
means that the source statement is deliberately not claimed.  `DEFERRED` and
`APPLICATION` are explicit final dispositions permitted by the design; they
are not implementation claims.

The detailed mathematical descriptions and declaration names remain in
[`SOURCE_MAP.md`](../SOURCE_MAP.md).  This matrix prevents historical prose in
the append-only status log from being read as the current package boundary.

## Chapter I theorems

| Source | Final disposition | Owner or precise boundary |
| --- | --- | --- |
| I.1 | RESOLVED | `Probability/Process/Stopping/Basic.lean` |
| I.2 | RESOLVED | `Probability/Process/Equivalence.lean` |
| I.3 | RESOLVED | `Probability/Process/Stopping/Hitting.lean` |
| I.4 | RESOLVED | `Probability/Process/Stopping/Hitting.lean` |
| I.5 | RESOLVED | `Probability/Process/Stopping/Basic.lean` |
| I.6 | RESOLVED | `Probability/Process/Stopping/MeasurableSpace.lean` and stopped-field generators |
| I.7 | RESOLVED | `Probability/Process/Stopping/Before.lean` and localization owners |
| I.8 | RESOLVED (REUSE) | Mathlib monotone-class infrastructure |
| I.9 | RESOLVED | `Probability/Martingale/Convergence/Regularization.lean` |
| I.10 | RESOLVED | continuous-time martingale convergence owners |
| I.11 | RESOLVED | uniform-integrability owners under `ForMathlib/MeasureTheory/Function` |
| I.12 | RESOLVED | `Probability/Martingale/Convergence/ContinuousClosingProjection.lean` |
| I.13 | RESOLVED | `Probability/Martingale/Convergence/ContinuousClosure.lean` |
| I.14 | RESOLVED (REUSE) | Mathlib reverse/backwards martingale convergence |
| I.15 | RESOLVED | continuous conditional-expectation martingale bridge |
| I.16 | RESOLVED | `Probability/Martingale/OptionalSampling/ContinuousUnbounded.lean` and terminal-valued stopping |
| I.17 | RESOLVED | `Probability/Martingale/OptionalSampling/ContinuousOneSidedUsual.lean` |
| I.18 | RESOLVED | `Probability/Martingale/OptionalSampling/ContinuousUniformIntegrable.lean` |
| I.19 | RESOLVED (REUSE/BRIDGE) | Mathlib conditional Jensen plus process bridge |
| I.20 | RESOLVED | continuous-time Doob inequalities |
| I.21 | RESOLVED | stopping-value characterization and measurability owners |
| I.22 | RESOLVED | counting-process stopping-time bridge |
| I.23 | RESOLVED | Poisson martingale owners |
| I.24 | RESOLVED | Poisson compensated-martingale owners |
| I.25 | RESOLVED | Poisson natural-filtration owners |
| I.26 | RESOLVED | project-owned Brownian construction/path regularity |
| I.27 | RESOLVED | `Probability/Brownian/Reflection.lean` |
| I.28 | RESOLVED | Brownian strong quadratic-variation owners |
| I.29 | RESOLVED | `Probability/Brownian/InfiniteVariation.lean` |
| I.30 | DEFERRED | canonical cadlag Levy realization remains with the Levy/SII owner |
| I.31 | RESOLVED on the project SII domain | independent-increment natural-filtration owners |
| I.32 | RESOLVED on finite-future cylinders; DEFERRED in full generality | finite-stopping/future-law owners; no generic Feller realization claim |
| I.33 | RESOLVED | Brownian reflection principle |
| I.34 | RESOLVED on implemented Levy-process domain | Levy moment owner |
| I.35 | DEFERRED | canonical path jump measure belongs to the Levy/PPP layer |
| I.36 | DEFERRED | Levy jump-integral process construction belongs to the Levy/PPP layer |
| I.37 | DEFERRED | same Levy/PPP owner |
| I.38 | DEFERRED | same Levy/PPP owner |
| I.39 | DEFERRED | same Levy/PPP owner |
| I.40 | DEFERRED | canonical Levy large/small-jump decomposition |
| I.41 | DEFERRED | compensated bounded-jump construction in the canonical Levy realization |
| I.42 | DEFERRED | full Levy decomposition theorem |
| I.43 | DEFERRED | Levy-measure moment application |
| I.44 | RESOLVED for law characterization; DEFERRED for canonical process realization | project Levy--Khintchine vs path realization boundary |
| I.45 | RESOLVED on implemented Markov interfaces | `Probability/Markov` |
| I.46 | STILL-BLOCKED | generic continuous-time Feller-to-strong-Markov realization bridge is absent |
| I.47 | DEFERRED | generic Feller/Markov realization refinement |
| I.48 | RESOLVED | `Probability/Process/LocalMartingale/Stability.lean` |
| I.49 | RESOLVED | `Probability/Process/LocalMartingale/Localization.lean` |
| I.50 | RESOLVED | `Probability/Process/LocalMartingale/Localization.lean` |
| I.51 | RESOLVED | `Probability/Process/LocalMartingale/Bounded.lean` |
| I.52 | STILL-BLOCKED at the source explicit formula | `FiniteVariation/ProtterDensity.lean` proves RN existence/recovery and a measurable rational-liminf candidate; the missing bridge is one-sided rational differentiation for an arbitrary locally finite Stieltjes reference measure |
| I.53 | RESOLVED | FV Stieltjes integral owner |
| I.54 | RESOLVED | FV change-of-variables/substitution owner |
| I.55 | RESOLVED (REUSE) | Mathlib Banach--Steinhaus/uniform boundedness |
| I.56 | RESOLVED | `Analysis/PathVariation/NaiveIntegrationImpossible.lean` |

## Chapter II theorems

| Source | Final disposition | Owner or precise boundary |
| --- | --- | --- |
| II.1 | RESOLVED | canonical simple predictable processes and good-integrator semantics |
| II.2 | RESOLVED | `Semimartingale/AbsoluteContinuity.lean` |
| II.3 | RESOLVED | `Semimartingale/Mixture.lean` |
| II.4 | RESOLVED | `Semimartingale/Stricker.lean` |
| II.5 | STILL-BLOCKED | `Semimartingale/JacodCountableExpansion.lean` closes the sigma-field/restricted-measure core; lifting finite stopping-time simple representations through completion is still missing, so the process theorem is not claimed |
| II.6 | RESOLVED | localization and stopping-before owners |
| II.7 | RESOLVED | adapted cadlag finite-variation processes are semimartingales |
| II.8 | RESOLVED | L2/local-L2/continuous-local-martingale entry points |
| II.9 | RESOLVED | decomposable implies native semimartingale |
| II.10 | RESOLVED with recorded source correction | UCP completeness/approximation owners |
| II.11 | RESOLVED | full source UCP continuity |
| II.12 | RESOLVED | stopping of the constructed stochastic integral |
| II.13 | RESOLVED | jump identity |
| II.14 | RESOLVED | absolutely-continuous measure invariance |
| II.15 | RESOLVED | mixture invariance |
| II.16 | RESOLVED | filtration invariance |
| II.17 | RESOLVED | finite-variation agreement |
| II.18 | RESOLVED | local behavior/version invariance |
| II.19 | RESOLVED | associativity on the Chapter II adapted-caglad domain |
| II.20 | RESOLVED | locally square-integrable local-martingale preservation |
| II.21 | RESOLVED | Riemann/source-sum approximation interfaces |
| II.22 | RESOLVED | canonical raw quadratic variation |
| II.23 | RESOLVED | canonical mixed covariation |
| II.24 | RESOLVED | bracket algebra under deterministic transforms |
| II.25 | RESOLVED | Kunita--Watanabe inequality |
| II.26 | RESOLVED | FV bracket/jump formula |
| II.27 | RESOLVED | continuous-local-martingale bracket/moment block |
| II.28 | RESOLVED | quadratic pure-jump block |
| II.29 | RESOLVED | bracket of stochastic integrals |
| II.30 | RESOLVED | left-weighted mixed bracket identity |
| II.31 | RESOLVED | FV change of variables |
| II.32 | RESOLVED | scalar Ito formula, including jumps |
| II.33 | RESOLVED | finite-dimensional Ito formula |
| II.34 | RESOLVED | Fisk--Stratonovich with continuous covariation |
| II.35 | RESOLVED | complex continuous formula |
| II.36 | RESOLVED | complex cadlag formula |
| II.37 | RESOLVED | stochastic-exponential equation existence and uniqueness; `StochasticExponential/Uniqueness.lean` uses a nonvanishing auxiliary exponential and a proved pure-jump Volterra zero lemma |
| II.38 | RESOLVED | stochastic-exponential product/inverse identities |
| II.39 | RESOLVED | exponential-martingale equivalence on its legal domain |
| II.40 | RESOLVED | Levy Brownian characterization, scalar and multidimensional |
| II.41 | RESOLVED for the corrected C2/harmonic/subharmonic domains; DEFERRED for nonsmooth potential theory | the printed unqualified true-submartingale reading needs integrability and is not claimed |
| II.42 | RESOLVED | Dambis--Dubins--Schwarz |
| II.43 | RESOLVED | Levy stochastic-area characteristic function and density |

## Chapter III theorems

| Source | Final disposition | Owner or precise boundary |
| --- | --- | --- |
| III.1 | RESOLVED | BD equivalence plus predictable/optional/progressive bridges; strict progressive counterexample in `Measurability/ProgressiveStrict.lean` |
| III.2 | RESOLVED | canonical special-decomposition uniqueness |
| III.3 | RESOLVED | accessible/totally-inaccessible decomposition |
| III.4 | STILL-BLOCKED | `Stopping/MeyerFellerCore.lean` proves the exact jump-event split core; generic continuous-time strong-Markov/Feller natural-filtration linkage and predictability of the complement part are absent |
| III.5 | RESOLVED | pre-stopping-field characterization |
| III.6 | RESOLVED | announcing-sequence field identity |
| III.7 | RESOLVED | before-field event transport |
| III.8 | RESOLVED | predictable evaluation is before-field measurable |
| III.9 | RESOLVED | discrete potential Doob decomposition |
| III.10 | RESOLVED | continuous Class-D Doob--Meyer case |
| III.11 | RESOLVED | general Class-D Doob--Meyer |
| III.12 | RESOLVED | natural FV characterization |
| III.13 | RESOLVED | naturality characterization |
| III.14 | RESOLVED | predictable/natural FV bridge |
| III.15 | RESOLVED | FV local martingales are constant on the normalized domain |
| III.16 | RESOLVED | local Doob--Meyer |
| III.17 | RESOLVED | quasimartingale conditional-variation equivalence |
| III.18 | RESOLVED | Rao decomposition |
| III.19 | RESOLVED | compensator moment identity |
| III.20 | RESOLVED with source predictability correction | compensator conditional formula |
| III.21 | RESOLVED | single-jump hazard/compensator application |
| III.22 | RESOLVED | nonexplosive counting-process compensator |
| III.23 | RESOLVED | counting-process information/compensation application |
| III.24 | RESOLVED | locally integrable increasing-process compensation |
| III.25 | RESOLVED | predictable FV local-martingale criterion |
| III.26 | RESOLVED | totally-inaccessible stopping compensation |
| III.27 | RESOLVED | Le Jan theorem owner |
| III.28 | RESOLVED | predictable stopped-value interface |
| III.29 | RESOLVED | Fundamental Theorem of Local Martingales |
| III.30 | RESOLVED | classical semimartingales are native semimartingales |
| III.31 | RESOLVED | cadlag quasimartingales are semimartingales |
| III.32 | RESOLVED | cadlag supermartingales are semimartingales |
| III.33 | RESOLVED | local-martingale stochastic integral |
| III.34 | RESOLVED | uniqueness of special decomposition |
| III.35 | RESOLVED | bounded-jump specialness |
| III.36 | RESOLVED | running-jump criterion |
| III.37 | RESOLVED | running-supremum criterion |
| III.38 | RESOLVED | local-martingale running-supremum/FV decomposition |
| III.39 | RESOLVED | equivalent-measure Girsanov--Meyer |
| III.40 | RESOLVED | predictable Girsanov under equivalence |
| III.41 | RESOLVED | merely absolutely-continuous predictable Girsanov with zero-density localization |
| III.42 | RESOLVED | Lenglart--Girsanov raw correction and density-killing compensator |
| III.43 | RESOLVED | bounded-stopping stochastic-exponential criterion |
| III.44 | RESOLVED | Kazamaki criterion |
| III.45 | RESOLVED | Novikov criterion |
| III.46 | APPLICATION | Brownian change-of-measure acceptance theorem; no SDE package is inferred |
| III.47 | RESOLVED | Bichteler--Dellacherie, proved from Yan/Rao/Girsanov and finite-horizon patching |

## Exercise disposition rows

Every exercise number below is explicit.  Unless an owner is named, the final
design disposition is `APPLICATION/ACCEPTANCE`; such a row does not assert a
new public theorem.  Load-bearing exercise results were promoted to production
owners before closure.

### Chapter I exercises

| Source | Final disposition |
| --- | --- |
| I.Ex.1 | RESOLVED: stopping-field monotonicity |
| I.Ex.2 | APPLICATION/ACCEPTANCE |
| I.Ex.3 | RESOLVED: countable sup/inf stopping-time algebra |
| I.Ex.4 | RESOLVED: decreasing stopping limits under right continuity |
| I.Ex.5 | APPLICATION/ACCEPTANCE |
| I.Ex.6 | APPLICATION/ACCEPTANCE |
| I.Ex.7 | RESOLVED: Poisson local-martingale bridge |
| I.Ex.8 | APPLICATION/ACCEPTANCE |
| I.Ex.9 | APPLICATION/ACCEPTANCE |
| I.Ex.10 | APPLICATION/ACCEPTANCE |
| I.Ex.11 | RESOLVED in the Levy/SII construction |
| I.Ex.12 | APPLICATION/ACCEPTANCE |
| I.Ex.13 | APPLICATION/ACCEPTANCE |
| I.Ex.14 | APPLICATION/ACCEPTANCE |
| I.Ex.15 | APPLICATION/ACCEPTANCE |
| I.Ex.16 | APPLICATION/ACCEPTANCE |
| I.Ex.17 | RESOLVED: cadlag large-jump localization |
| I.Ex.18 | DEFERRED to the Levy/PPP owner |
| I.Ex.19 | RESOLVED: continuous hitting-time predictability |
| I.Ex.20 | APPLICATION/ACCEPTANCE |
| I.Ex.21 | APPLICATION/ACCEPTANCE |
| I.Ex.22 | APPLICATION/ACCEPTANCE |
| I.Ex.23 | APPLICATION/ACCEPTANCE |
| I.Ex.24 | APPLICATION/ACCEPTANCE |
| I.Ex.25 | DEFERRED to the Levy realization owner |
| I.Ex.26 | DEFERRED to the Levy realization owner |
| I.Ex.27 | RESOLVED: before-field inclusion |
| I.Ex.28 | DEFERRED to the Levy/PPP owner |
| I.Ex.29 | APPLICATION/ACCEPTANCE |
| I.Ex.30 | DEFERRED to the Levy realization owner |
| I.Ex.31 | DEFERRED to the Levy realization owner |

### Chapter II exercises

| Source | Final disposition |
| --- | --- |
| II.Ex.1 | APPLICATION/ACCEPTANCE |
| II.Ex.2 | RESOLVED by absolute-continuity stability |
| II.Ex.3 | RESOLVED by independent Brownian cross-variation |
| II.Ex.4 | APPLICATION/ACCEPTANCE |
| II.Ex.5 | APPLICATION/ACCEPTANCE |
| II.Ex.6 | RESOLVED as a semantic convergence-mode guard |
| II.Ex.7 | APPLICATION/ACCEPTANCE |
| II.Ex.8 | APPLICATION/ACCEPTANCE |
| II.Ex.9 | APPLICATION/ACCEPTANCE |
| II.Ex.10 | RESOLVED by measure-change invariance |
| II.Ex.11 | RESOLVED by the Brownian first-hit counterexample pattern |
| II.Ex.12 | APPLICATION/ACCEPTANCE |
| II.Ex.13 | RESOLVED by stochastic-integral UCP continuity |
| II.Ex.14 | APPLICATION/ACCEPTANCE |
| II.Ex.15 | APPLICATION/ACCEPTANCE |
| II.Ex.16 | APPLICATION/ACCEPTANCE |
| II.Ex.17 | APPLICATION/ACCEPTANCE |
| II.Ex.18 | APPLICATION/ACCEPTANCE |
| II.Ex.19 | APPLICATION/ACCEPTANCE |
| II.Ex.20 | APPLICATION/ACCEPTANCE |
| II.Ex.21 | APPLICATION/ACCEPTANCE |
| II.Ex.22 | APPLICATION/ACCEPTANCE |
| II.Ex.23 | APPLICATION/ACCEPTANCE |
| II.Ex.24 | APPLICATION/ACCEPTANCE |
| II.Ex.25 | APPLICATION/ACCEPTANCE |
| II.Ex.26 | APPLICATION/ACCEPTANCE |
| II.Ex.27 | APPLICATION/ACCEPTANCE |
| II.Ex.28 | RESOLVED on the continuous-semimartingale domain |
| II.Ex.29 | APPLICATION/ACCEPTANCE |
| II.Ex.30 | APPLICATION/ACCEPTANCE |
| II.Ex.31 | APPLICATION/ACCEPTANCE |
| II.Ex.32 | RESOLVED by usual-augmentation owners |
| II.Ex.33 | RESOLVED by filtration-transfer owners |
| II.Ex.34 | RESOLVED by local-martingale filtration-transfer owners |

### Chapter III exercises

| Source | Final disposition |
| --- | --- |
| III.Ex.1 | RESOLVED: finite predictable-time lattice closure |
| III.Ex.2 | APPLICATION/ACCEPTANCE |
| III.Ex.3 | RESOLVED: predictable restriction/equality graph |
| III.Ex.4 | RESOLVED: predictable is optional |
| III.Ex.5 | RESOLVED: optional is progressive on the implemented bridge |
| III.Ex.6 | RESOLVED: stochastic intervals |
| III.Ex.7 | RESOLVED: announcing-sequence refinements |
| III.Ex.8 | DEFERRED: full quasi-left-continuity package |
| III.Ex.9 | DEFERRED to canonical Levy realization |
| III.Ex.10 | APPLICATION/ACCEPTANCE |
| III.Ex.11 | APPLICATION/ACCEPTANCE |
| III.Ex.12 | RESOLVED: predictable FV jump/integral bridge |
| III.Ex.13 | RESOLVED on the natural counting-process domain |
| III.Ex.14 | RESOLVED: exponential single-jump hazard |
| III.Ex.15 | RESOLVED: compound marked-jump compensation |
| III.Ex.16 | RESOLVED: exponential hazard rate |
| III.Ex.17 | RESOLVED: censoring/hazard compensation |
| III.Ex.18 | APPLICATION/ACCEPTANCE |
| III.Ex.19 | RESOLVED on the special-semimartingale domain |
| III.Ex.20 | RESOLVED by local specialness/canonical patching |
| III.Ex.21 | RESOLVED by the equivalent-measure density owners |
| III.Ex.22 | APPLICATION/ACCEPTANCE |
| III.Ex.23 | APPLICATION/ACCEPTANCE |
| III.Ex.24 | RESOLVED: one-jump information environment |
| III.Ex.25 | APPLICATION/ACCEPTANCE |
| III.Ex.26 | RESOLVED: increasing-process compensator tests |
| III.Ex.27 | APPLICATION/ACCEPTANCE |
| III.Ex.28 | APPLICATION/ACCEPTANCE |
| III.Ex.29 | APPLICATION/ACCEPTANCE |
| III.Ex.30 | APPLICATION/ACCEPTANCE |
| III.Ex.31 | DEFERRED with Meyer III.4's generic Feller bridge |
| III.Ex.32 | APPLICATION/ACCEPTANCE |
| III.Ex.33 | APPLICATION/ACCEPTANCE |
| III.Ex.34 | APPLICATION/ACCEPTANCE |
| III.Ex.35 | APPLICATION/ACCEPTANCE |
| III.Ex.36 | RESOLVED: before-field martingale-jump generator |
| III.Ex.37 | RESOLVED: optional/predictable sigma-field bridge |

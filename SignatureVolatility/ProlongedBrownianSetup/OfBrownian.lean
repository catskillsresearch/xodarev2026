module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic
public import SignatureVolatility.TimeReindex


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace SignatureVolatility

/-- A `d`-dimensional Brownian driver on `ℝ≥0`, packaged for reindexing to the
signature-volatility `ℝ`-time API. Coordinates are one-dimensional Brownian
motions in the sense of Mathlib's `IsBrownianReal`, with **everywhere**-continuous
paths and coordinate **processes** that are mutually independent (so `W` is a
`d`-dimensional Brownian motion in its own joint filtration and joint-filtration
martingale calculi are available; a.s.-only continuity and coordinates that are
independent at each fixed time but entangled across times — e.g. one coordinate
anticipating the future of another — are excluded). -/
structure MultiBrownian (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) where
  /-- Coordinate processes on Mathlib time `ℝ≥0`. -/
  Wnn : ℝ≥0 → Ω → Fin d → ℝ
  isBrownian : ∀ i : Fin d, IsBrownianReal (fun t ω => Wnn t ω i) P
  Wnn_zero : ∀ ω i, Wnn 0 ω i = 0
  Wnn_meas : ∀ t i, Measurable (fun ω => Wnn t ω i)
  /-- Paths are continuous at every `ω` (not merely almost every). -/
  pathContinuous : ∀ (i : Fin d) (ω : Ω), Continuous fun t : ℝ≥0 => Wnn t ω i
  /-- The coordinate **processes** `ω ↦ (t ↦ W_t^i(ω))` are mutually independent (path space
  `ℝ≥0 → ℝ` with the product σ-algebra). Strictly stronger than independence of the coordinates
  at each fixed time (`coordsIndep_eval`): it rules out future-entangled coordinates, for which
  an integrand `σ(t, W_t)` would anticipate the driver and Novikov / the Doléans SDE fail. -/
  coordsIndep : iIndepFun (fun i : Fin d => fun ω => fun t : ℝ≥0 => Wnn t ω i) P

namespace MultiBrownian

/-- Fixed-time independence of the coordinates (the former, weaker, structure field). -/
lemma coordsIndep_eval {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (B : MultiBrownian Ω P d) (t : ℝ≥0) :
    iIndepFun (fun i : Fin d => fun ω => B.Wnn t ω i) P :=
  B.coordsIndep.comp (fun _ f => f t) fun _ => measurable_pi_apply t

/-- Joint independence of any finite-dimensional time marginals of distinct coordinates: the
vectors `(W^i_{t})_{t ∈ I}` are independent across `i`. -/
lemma coordsIndep_restrict {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} (B : MultiBrownian Ω P d) (I : Finset ℝ≥0) :
    iIndepFun (fun i : Fin d => fun ω => I.restrict fun t => B.Wnn t ω i) P :=
  B.coordsIndep.comp (fun _ f => I.restrict f) fun _ => Finset.measurable_restrict I

/-- Reindexed driver `ℝ → Ω → Fin d → ℝ` (negative times read time `0`). -/
def W {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) : ℝ → Ω → Fin d → ℝ :=
  reindexProcessFin B.Wnn

lemma W_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (ω : Ω) (i : Fin d) : W B 0 ω i = 0 := by
  change B.Wnn (Real.toNNReal 0) ω i = 0
  simpa [Real.toNNReal_zero] using B.Wnn_zero ω i

lemma W_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (i : Fin d) :
    Measurable (fun ω => W B t ω i) :=
  measurable_reindexProcessFin B.Wnn_meas t i

lemma W_eq_Wnn_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) (i : Fin d) :
    W B t ω i = B.Wnn ⟨t, ht⟩ ω i := by
  change B.Wnn (Real.toNNReal t) ω i = B.Wnn ⟨t, ht⟩ ω i
  rw [Real.toNNReal_of_nonneg ht]
  rfl

/-- Time-augmented path `(t, W_t) ∈ ℝ^{d+1}`. -/
def wAug {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) : Fin (d + 1) → ℝ :=
  fun j =>
    if h : (j : ℕ) = 0 then t
    else W B t ω ⟨j.1 - 1, by
      have hj : (j : ℕ) < d + 1 := j.isLt
      have hne : (j : ℕ) ≠ 0 := h
      omega⟩

lemma wAug_time {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) :
    wAug B t ω ⟨0, Nat.succ_pos _⟩ = t := by
  simp [wAug]

lemma wAug_space {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (ω : Ω) (i : Fin d) :
    wAug B t ω ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩ = W B t ω i := by
  simp [wAug]

lemma wAug_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
    (B : MultiBrownian Ω P d) (t : ℝ) (j : Fin (d + 1)) :
    Measurable (fun ω => wAug B t ω j) := by
  classical
  by_cases h : (j : ℕ) = 0
  · simp [wAug, h]
  · simp only [wAug, h, ↓reduceDIte]
    exact W_meas B t _

end MultiBrownian

end SignatureVolatility

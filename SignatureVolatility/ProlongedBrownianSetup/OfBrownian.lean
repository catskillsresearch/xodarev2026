module

public import Mathlib.Probability.BrownianMotion.Basic
public import SignatureVolatility.TimeReindex


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace SignatureVolatility

/-- A `d`-dimensional Brownian driver on `ℝ≥0`, packaged for reindexing to the
signature-volatility `ℝ`-time API. Coordinates are one-dimensional Brownian
motions in the sense of Mathlib's `IsBrownianReal`. -/
structure MultiBrownian (Ω : Type*) [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) where
  /-- Coordinate processes on Mathlib time `ℝ≥0`. -/
  Wnn : ℝ≥0 → Ω → Fin d → ℝ
  isBrownian : ∀ i : Fin d, IsBrownianReal (fun t ω => Wnn t ω i) P
  Wnn_zero : ∀ ω i, Wnn 0 ω i = 0
  Wnn_meas : ∀ t i, Measurable (fun ω => Wnn t ω i)

namespace MultiBrownian

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

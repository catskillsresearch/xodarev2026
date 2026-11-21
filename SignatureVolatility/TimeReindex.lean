module

public import Mathlib


@[expose] public section

open MeasureTheory
open scoped NNReal

namespace SignatureVolatility

/-- Clamp a real time to nonnegative (`max t 0`). -/
noncomputable def toNNRealTime (t : ℝ) : ℝ≥0 := Real.toNNReal t

/-- Coerce nonnegative time back to `ℝ`. -/
def ofNNRealTime (t : ℝ≥0) : ℝ := (t : ℝ)

@[simp] lemma ofNNRealTime_toNNRealTime_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ofNNRealTime (toNNRealTime t) = t := by
  simp [ofNNRealTime, toNNRealTime, Real.coe_toNNReal _ ht]

@[simp] lemma toNNRealTime_ofNNRealTime (t : ℝ≥0) :
    toNNRealTime (ofNNRealTime t) = t := by
  simp [ofNNRealTime, toNNRealTime]

/-- Reindex a Mathlib/MathFin process `ℝ≥0 → Ω → α` to our `ℝ`-time indexing
(times `< 0` read the value at `0`). -/
noncomputable def reindexProcess {Ω α : Type*} (X : ℝ≥0 → Ω → α) : ℝ → Ω → α :=
  fun t ω => X (toNNRealTime t) ω

/-- Coordinatewise reindex for `Fin d`-valued drivers. -/
noncomputable def reindexProcessFin {Ω : Type*} {d : ℕ}
    (X : ℝ≥0 → Ω → Fin d → ℝ) : ℝ → Ω → Fin d → ℝ :=
  fun t ω i => X (toNNRealTime t) ω i

lemma measurable_reindexProcess {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {X : ℝ≥0 → Ω → α} (hX : ∀ t, Measurable (X t)) (t : ℝ) :
    Measurable (reindexProcess X t) :=
  hX _

lemma measurable_reindexProcessFin {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → Fin d → ℝ} (hX : ∀ t i, Measurable (fun ω => X t ω i))
    (t : ℝ) (i : Fin d) :
    Measurable (fun ω => reindexProcessFin X t ω i) :=
  hX _ _

end SignatureVolatility

module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable


@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace SignatureVolatility

/-!
# Adapted continuous versions along left dyadic approximants

For a process `X : ℝ → Ω → ℝ`, `contVersion X t ω` is the limit of `X (⌊t 2ⁿ⌋₊ / 2ⁿ) ω` as
`n → ∞` (Lean's `limUnder` junk value if the limit does not exist). It only reads `X` at times
`≤ t`, so it preserves adaptedness, and it agrees with `X t ω` whenever `X (·) ω` is continuous
at `t` (`contVersion_eq_of_continuousAt`). Iterated integrals are built level by level from
their continuous versions, as for the paper's continuous signature `Ŵ`.
-/

/-- Left dyadic approximant `⌊t 2ⁿ⌋₊ / 2ⁿ` of `t`. -/
def dyadicFloor (n : ℕ) (t : ℝ) : ℝ := (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n

lemma dyadicFloor_nonneg (n : ℕ) (t : ℝ) : 0 ≤ dyadicFloor n t := by
  unfold dyadicFloor; positivity

lemma dyadicFloor_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : dyadicFloor n t ≤ t := by
  unfold dyadicFloor
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

lemma sub_dyadicFloor_le (t : ℝ) (n : ℕ) : t - dyadicFloor n t ≤ 1 / 2 ^ n := by
  unfold dyadicFloor
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl := Nat.lt_floor_add_one (t * 2 ^ n)
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ h2]
  linarith

lemma tendsto_dyadicFloor {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => dyadicFloor n t) atTop (𝓝 t) := by
  have h1 : Tendsto (fun n : ℕ => t - 1 / 2 ^ n) atTop (𝓝 t) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
      simpa [one_div, Function.comp_def] using this
    simpa using (tendsto_const_nhds (x := t)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun n => ?_)
    (fun n => dyadicFloor_le ht n)
  linarith [sub_dyadicFloor_le t n]

variable {Ω : Type*}

/-- Continuous version of `X` read along left dyadic approximants. -/
def contVersion (X : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun n => X (dyadicFloor n t) ω

lemma measurable_contVersion {m : MeasurableSpace Ω} (X : ℝ → Ω → ℝ) (t : ℝ)
    (hX : ∀ n, Measurable[m] (X (dyadicFloor n t))) : Measurable[m] (contVersion X t) :=
  haveI : T0Space ℝ := T6Space.toT0Space
  (StronglyMeasurable.limUnder fun n => (hX n).stronglyMeasurable).measurable

lemma contVersion_eq_of_tendsto {X : ℝ → Ω → ℝ} {t : ℝ} {ω : Ω} {a : ℝ}
    (h : Tendsto (fun n => X (dyadicFloor n t) ω) atTop (𝓝 a)) : contVersion X t ω = a :=
  h.limUnder_eq

lemma contVersion_eq_of_continuousWithinAt {X : ℝ → Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (h : ContinuousWithinAt (fun u => X u ω) (Set.Iic t) t) : contVersion X t ω = X t ω :=
  contVersion_eq_of_tendsto (h.tendsto.comp (tendsto_nhdsWithin_iff.2
    ⟨tendsto_dyadicFloor ht, Eventually.of_forall fun n => dyadicFloor_le ht n⟩))

end SignatureVolatility

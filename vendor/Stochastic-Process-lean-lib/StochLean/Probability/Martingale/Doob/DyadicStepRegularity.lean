/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicApproximation
public import StochLean.Probability.Martingale.Doob.GlobalConditionalModulus
public import StochLean.Probability.Process.Stopping.DyadicMonotone
public import StochLean.Probability.Process.Path.RightLimit

/-! # Exact grid recovery and right limits of the dyadic Doob steps

The original step process still uses the ceiling index. Nested upper grids
preserve its values exactly. The floor index below describes only its strict
right limit, including the possibly nonzero limit at zero. Right increments
are expressed through the existing `rightLimitProcess`, not through the
left-jump process and not through a new jump selector.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A finer upper grid does not change the coarse ceiling index. -/
theorem dyadicDoob_ceil_finer_rightGrid {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * dyadicRightGrid m t) =
      Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    have hle := antitone_dyadicRightGrid t hnm
    change dyadicRightGrid m t ≤ dyadicRightGrid n t at hle
    rw [dyadicRightGrid_eq n t] at hle
    have hp : ((2 ^ n : ℕ) : ℝ≥0) ≠ 0 := by positivity
    calc
      _ ≤ ((2 ^ n : ℕ) : ℝ≥0) *
          ((Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) : ℝ≥0) / (2 ^ n : ℕ)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hp]
  · exact Nat.ceil_mono
      (mul_le_mul_of_nonneg_left (le_dyadicRightGrid m t) (by positivity))

variable (X : ℝ≥0 → Ω → ℝ) (F : Filtration ℝ≥0 mΩ) (P : Measure Ω)

/-- Exact recovery at a finer ceiling time, not a continuity approximation. -/
theorem dyadicDoobStep_finer_rightGrid {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    dyadicDoobStep X F P n (dyadicRightGrid m t) = dyadicDoobStep X F P n t := by
  simp only [dyadicDoobStep, dyadicDoob_ceil_finer_rightGrid hnm t]

/-- The whole-half-line supremum of a two-mesh difference is recovered
exactly on any common finer grid. No raw supremum is converted to a real. -/
theorem iSup_norm_dyadicDoobStep_sub_eq_finer_grid {n m r : ℕ}
    (hnr : n ≤ r) (hmr : m ≤ r) (ω : Ω) :
    (⨆ t : ℝ≥0, ENNReal.ofReal
      ‖dyadicDoobStep X F P n t ω - dyadicDoobStep X F P m t ω‖) =
      ⨆ k : ℕ, ENNReal.ofReal
        ‖dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ r : ℕ)) ω -
          dyadicDoobStep X F P m ((k : ℝ≥0) / (2 ^ r : ℕ)) ω‖ := by
  apply le_antisymm
  · apply iSup_le
    intro t
    rw [← dyadicDoobStep_finer_rightGrid X F P hnr t,
      ← dyadicDoobStep_finer_rightGrid X F P hmr t, dyadicRightGrid_eq]
    exact le_iSup_of_le (Nat.ceil (((2 ^ r : ℕ) : ℝ≥0) * t)) le_rfl
  · exact iSup_le fun k ↦ le_iSup_of_le ((k : ℝ≥0) / (2 ^ r : ℕ)) le_rfl

/-- The strict right limit is the next coefficient after the floor index.
This formula describes a limit; it does not redefine the original process. -/
theorem dyadicDoobStep_tendsto_right (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun s ↦ dyadicDoobStep X F P n s ω) (𝓝[>] t)
      (𝓝 (dyadicDoobIncreasing X F P n
        (Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) + 1) ω)) := by
  let k := Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t)
  have hp : (0 : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0) := by positivity
  have hlo : (k : ℝ≥0) / (2 ^ n : ℕ) ≤ t := by
    apply (div_le_iff₀ hp).mpr
    have h : (k : ℝ≥0) ≤ ((2 ^ n : ℕ) : ℝ≥0) * t := Nat.floor_le bot_le
    simpa only [mul_comm] using h
  have hhi : t < ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ) := by
    apply (lt_div_iff₀ hp).mpr
    have h : ((2 ^ n : ℕ) : ℝ≥0) * t < (k : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hhi)] with s hs hs'
  have hts : t < s := hs
  have hsu : s < ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ) := hs'
  exact (congrFun (dyadicDoobStep_eq_on_Ioc X F P n k
    (hlo.trans_lt hts) hsu.le) ω).symm

theorem dyadicDoobStep_isCagladPath (n : ℕ) (ω : Ω) :
    IsCagladPath (fun t ↦ dyadicDoobStep X F P n t ω) :=
  ⟨dyadicDoobStep_isLeftContinuousPath X F P n ω,
    fun t ↦ ⟨_, dyadicDoobStep_tendsto_right X F P n t ω⟩⟩

theorem rightLimitProcess_dyadicDoobStep (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    rightLimitProcess (dyadicDoobStep X F P n) t ω =
      dyadicDoobIncreasing X F P n (Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) + 1) ω :=
  rightLim_eq_of_tendsto (dyadicDoobStep_tendsto_right X F P n t ω)

/-- The right increment is a single native conditional decrement at grid
points and vanishes off the grid. Equality of floor and ceiling detects the
grid; in particular it includes time zero. -/
theorem rightLimitProcess_dyadicDoobStep_sub (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    rightLimitProcess (dyadicDoobStep X F P n) t ω - dyadicDoobStep X F P n t ω =
      if Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) = Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t)
      then P[X ((Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) : ℝ≥0) / (2 ^ n : ℕ)) -
        X (((Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ)) |
        F ((Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) : ℝ≥0) / (2 ^ n : ℕ))] ω
      else 0 := by
  rw [rightLimitProcess_dyadicDoobStep, dyadicDoobStep]
  split_ifs with h
  · rw [h]
    exact congrFun (dyadicDoobIncreasing_increment X F P n _) ω
  · have hceil := Nat.ceil_le_floor_add_one (((2 ^ n : ℕ) : ℝ≥0) * t)
    have hfloor := Nat.floor_le_ceil (((2 ^ n : ℕ) : ℝ≥0) * t)
    have he : Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) =
        Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) + 1 := by omega
    rw [he, sub_self]

/-- Every grid point, including the initial point, has exactly the next
conditional decrement as its right increment. -/
theorem rightLimitProcess_dyadicDoobStep_sub_at_grid (n k : ℕ) :
    rightLimitProcess (dyadicDoobStep X F P n) ((k : ℝ≥0) / (2 ^ n : ℕ)) -
      dyadicDoobStep X F P n ((k : ℝ≥0) / (2 ^ n : ℕ)) =
      P[X ((k : ℝ≥0) / (2 ^ n : ℕ)) -
        X (((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ)) |
        F ((k : ℝ≥0) / (2 ^ n : ℕ))] := by
  funext ω
  have hp : ((2 ^ n : ℕ) : ℝ≥0) ≠ 0 := by positivity
  have hc : ((2 ^ n : ℕ) : ℝ≥0) * ((k : ℝ≥0) / (2 ^ n : ℕ)) = (k : ℝ≥0) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hp]
  simpa only [hc, Nat.ceil_natCast, Nat.floor_natCast, if_true, Pi.sub_apply] using
    rightLimitProcess_dyadicDoobStep_sub X F P n ((k : ℝ≥0) / (2 ^ n : ℕ)) ω

/-- The initial right limit is not normalized to the zero initial value. -/
theorem rightLimitProcess_dyadicDoobStep_zero (n : ℕ) :
    rightLimitProcess (dyadicDoobStep X F P n) 0 =
      P[X 0 - X ((1 / 2 : ℝ≥0) ^ n) | F 0] := by
  simpa only [Nat.cast_zero, zero_div, dyadicDoobStep_zero, sub_zero,
    Nat.zero_add, Nat.cast_one, div_pow, one_pow, Nat.cast_pow, Nat.cast_ofNat] using
    rightLimitProcess_dyadicDoobStep_sub_at_grid X F P n 0

variable {X F P}

/-- Only countably many coefficient bounds are intersected. They control
the right increments at all real times on one common full-measure event. -/
theorem Supermartingale.ae_forall_norm_rightLimitProcess_dyadicDoobStep_sub_le
    (hX : Supermartingale X F P) (n : ℕ) {G : Ω → ℝ≥0∞}
    (hG : IsGlobalConditionalIncrementModulus F P X ((1 / 2 : ℝ≥0) ^ n) G)
    (hGfin : ∀ᵐ ω ∂P, G ω ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ‖rightLimitProcess (dyadicDoobStep X F P n) t ω -
        dyadicDoobStep X F P n t ω‖ ≤ (G ω).toReal := by
  have hcoeff (k : ℕ) : ∀ᵐ ω ∂P,
      ‖dyadicDoobIncreasing X F P n (k + 1) ω -
        dyadicDoobIncreasing X F P n k ω‖ ≤ (G ω).toReal := by
    have htime : ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ) =
        (k : ℝ≥0) / (2 ^ n : ℕ) + (1 / 2 : ℝ≥0) ^ n := by
      rw [Nat.cast_add, Nat.cast_one, add_div]
      simp
    have hle : (k : ℝ≥0) / (2 ^ n : ℕ) ≤
        ((k + 1 : ℕ) : ℝ≥0) / (2 ^ n : ℕ) := by rw [htime]; exact le_add_of_nonneg_right bot_le
    have hb := hG.conditional_increment_le hle htime.le
    filter_upwards [(hX.dyadic_restriction n).neg.monotone_predictablePart, hb, hGfin]
      with ω hm hbω hf
    have hn : 0 ≤ dyadicDoobIncreasing X F P n (k + 1) ω -
        dyadicDoobIncreasing X F P n k ω := sub_nonneg.mpr (hm k.le_succ)
    have he := congrFun (dyadicDoobIncreasing_increment X F P n k) ω
    change dyadicDoobIncreasing X F P n (k + 1) ω -
      dyadicDoobIncreasing X F P n k ω = _ at he
    rw [← he] at hbω
    simpa only [ENNReal.toReal_ofReal hn, Real.norm_of_nonneg hn] using
      ENNReal.toReal_mono hf hbω
  filter_upwards [ae_all_iff.mpr hcoeff] with ω hω t
  rw [rightLimitProcess_dyadicDoobStep_sub]
  split_ifs with h
  · have he := congrFun (dyadicDoobIncreasing_increment X F P n
      (Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t))) ω
    change dyadicDoobIncreasing X F P n
      (Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t) + 1) ω -
      dyadicDoobIncreasing X F P n (Nat.floor (((2 ^ n : ℕ) : ℝ≥0) * t)) ω = _ at he
    rw [← he]
    exact hω _
  · simpa only [norm_zero] using ENNReal.toReal_nonneg

/-- For a bounded process, finiteness of the actual modulus is derived
before using its real value in the common-event right-increment estimate. -/
theorem Supermartingale.ae_forall_norm_rightLimitProcess_dyadicDoobStep_sub_le_of_bound
    [IsFiniteMeasure P] (hX : Supermartingale X F P) (n : ℕ) {N : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) {G : Ω → ℝ≥0∞}
    (hG : IsGlobalConditionalIncrementModulus F P X ((1 / 2 : ℝ≥0) ^ n) G) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ‖rightLimitProcess (dyadicDoobStep X F P n) t ω -
        dyadicDoobStep X F P n t ω‖ ≤ (G ω).toReal :=
  hX.ae_forall_norm_rightLimitProcess_dyadicDoobStep_sub_le n hG
    (hG.ae_ne_top_of_norm_bound hX.integrable hb)

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Stopping
public import StochLean.Probability.Process.Stopping.Finite

/-!
# Upper-grid approximations of finite stopping times

These generic helpers were originally used in the Brownian strong Markov
proof. They now live at the stopping-time owner so optional sampling and
localization reuse the same construction. Existing public names are retained.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The source-standard upper dyadic approximation `2⁻ⁿ ⌈2ⁿ t⌉`. -/
noncomputable def dyadicRightGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  rightGrid (2 ^ n - 1) t

theorem dyadicRightGrid_eq (n : ℕ) (t : ℝ≥0) :
    dyadicRightGrid n t =
      (Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) : ℝ≥0) / (2 ^ n : ℕ) := by
  simp only [dyadicRightGrid, rightGrid]
  rw [Nat.sub_add_cancel (Nat.one_le_pow n 2 (by norm_num))]

theorem le_dyadicRightGrid (n : ℕ) (t : ℝ≥0) : t ≤ dyadicRightGrid n t := by
  exact le_rightGrid (2 ^ n - 1) t

theorem countable_range_dyadicRightGrid (n : ℕ) :
    (Set.range (dyadicRightGrid n)).Countable := by
  exact countable_range_rightGrid (2 ^ n - 1)

theorem tendsto_dyadicRightGrid (t : ℝ≥0) :
    Tendsto (fun n ↦ dyadicRightGrid n t) atTop (nhds t) := by
  apply (tendsto_rightGrid t).comp
  exact (tendsto_sub_atTop_nat 1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by norm_num))

/-- Upper right-grid approximation preserves the stopping-time property for finite
`ℝ≥0`-valued stopping times. -/
theorem stoppingTime_rightGridFinite
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ (rightGrid n (τ ω) : WithTop ℝ≥0)) := by
  intro u
  let m : ℕ := n + 1
  have hm : (0 : ℝ≥0) < (m : ℝ≥0) := by positivity
  have hevent : {ω | (rightGrid n (τ ω) : WithTop ℝ≥0) ≤ u} =
      ⋃ k : {k : ℕ // (k : ℝ≥0) / m ≤ u},
        {ω | (τ ω : WithTop ℝ≥0) ≤ ((k.1 : ℝ≥0) / m : ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have h' : rightGrid n (τ ω) ≤ u := WithTop.coe_le_coe.mp h
      refine ⟨⟨Nat.ceil ((m : ℝ≥0) * τ ω), ?_⟩, ?_⟩
      · simpa only [m, rightGrid] using h'
      · exact_mod_cast le_rightGrid n (τ ω)
    · rintro ⟨k, hk⟩
      have hk' : τ ω ≤ (k.1 : ℝ≥0) / m := WithTop.coe_le_coe.mp hk
      have hmul : (m : ℝ≥0) * τ ω ≤ k.1 := by
        have h := (le_div_iff₀ hm).mp hk'
        simpa [mul_comm] using h
      have hceil : Nat.ceil ((m : ℝ≥0) * τ ω) ≤ k.1 := Nat.ceil_le.mpr hmul
      apply WithTop.coe_le_coe.mpr
      calc
        rightGrid n (τ ω) =
            (Nat.ceil ((m : ℝ≥0) * τ ω) : ℝ≥0) / m := by rfl
        _ ≤ (k.1 : ℝ≥0) / m := by gcongr
        _ ≤ u := k.2
  rw [hevent]
  exact MeasurableSet.iUnion fun k ↦
    ℱ.mono k.2 _ (hτ ((k.1 : ℝ≥0) / m))

theorem stoppingTime_dyadicRightGridFinite
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ (dyadicRightGrid n (τ ω) : WithTop ℝ≥0)) := by
  exact stoppingTime_rightGridFinite hτ (2 ^ n - 1)

namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

/-- Countable-range upper approximation, capped at a deterministic finite horizon. -/
noncomputable def upperApprox (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    FiniteStoppingTime F :=
  (⟨fun ω ↦ rightGrid n (τ ω), stoppingTime_rightGridFinite τ.isStoppingTime n⟩ :
    FiniteStoppingTime F).min (const F T)

@[simp] theorem upperApprox_apply (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    τ.upperApprox T n ω = Min.min (rightGrid n (τ ω)) T := rfl

theorem upperApprox_le_horizon (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    τ.upperApprox T n ω ≤ T := min_le_right _ _

theorem le_upperApprox (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (n : ℕ) (ω : Ω) : τ ω ≤ τ.upperApprox T n ω :=
  le_min (le_rightGrid n (τ ω)) (hτ ω)

theorem countable_range_upperApprox (τ : FiniteStoppingTime F) (T : ℝ≥0) (n : ℕ) :
    (Set.range (τ.upperApprox T n)).Countable := by
  apply ((countable_range_rightGrid n).image (fun t ↦ Min.min t T)).mono
  rintro t ⟨ω, rfl⟩
  exact ⟨rightGrid n (τ ω), ⟨τ ω, rfl⟩, rfl⟩

theorem tendsto_upperApprox (τ : FiniteStoppingTime F) {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T)
    (ω : Ω) : Tendsto (fun n ↦ τ.upperApprox T n ω) atTop
      (nhdsWithin (τ ω) (Set.Ici (τ ω))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n ↦ τ.le_upperApprox hτ n ω⟩
  simpa only [upperApprox_apply, min_eq_left (hτ ω)] using
    (tendsto_rightGrid (τ ω)).min (tendsto_const_nhds (x := T))

end FiniteStoppingTime

end ProbabilityTheory

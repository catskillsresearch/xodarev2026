/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.ConditionalIncrementDifference
public import StochLean.Probability.Martingale.Doob.DyadicTerminalIdentity
public import StochLean.Probability.Martingale.Doob.DyadicRefinement
public import StochLean.Probability.Martingale.Doob.SupermartingaleConditionalModulus

/-! # Actual terminal-difference energy of dyadic Doob approximants

The two actual terminal identities yield their conditional remaining-difference
bound from the actual global conditional moduli. Sampling both ceiling extensions
on the finer grid preserves predictability. The generic energy inequality then
applies to these actual approximants, with no energy or Cauchy certificate input.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

theorem dyadicDoob_rightGrid_le (n : ℕ) (t : ℝ≥0) :
    dyadicRightGrid n t ≤ t + 1 / ((2 ^ n : ℕ) : ℝ≥0) := by
  have h := (rightGrid_lt (2 ^ n - 1) t).le
  simpa only [dyadicRightGrid, Nat.sub_add_cancel (Nat.one_le_pow n 2 (by norm_num))] using h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z U V : Ω → ℝ} {N : ℝ}

theorem Supermartingale.condExp_dyadicDoob_terminal_difference
    (hX : Supermartingale X F P) (n m : ℕ)
    (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (hlV : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P m k ω) atTop (𝓝 (V ω)))
    (t : ℝ≥0) :
    P[(U - dyadicDoobStep X F P n t) - (V - dyadicDoobStep X F P m t) | F t] =ᵐ[P]
      P[X (dyadicRightGrid n t) - X (dyadicRightGrid m t) | F t] := by
  have heU := hX.condExp_dyadicDoob_terminal_sub_step n hb hZ hU hlZ hlU t
  have heV := hX.condExp_dyadicDoob_terminal_sub_step m hb hZ hV hlZ hlV t
  have hsub := condExp_sub
    ((hU.integrable (by norm_num)).sub (dyadicDoobStep_integrable X F P n t))
    ((hV.integrable (by norm_num)).sub (dyadicDoobStep_integrable X F P m t)) (F t)
  have hsubX := condExp_sub ((hX.integrable (dyadicRightGrid n t)).sub hZ)
    ((hX.integrable (dyadicRightGrid m t)).sub hZ) (F t)
  have he : (X (dyadicRightGrid n t) - Z) - (X (dyadicRightGrid m t) - Z) =
      X (dyadicRightGrid n t) - X (dyadicRightGrid m t) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  rw [he] at hsubX
  exact hsub.trans ((heU.sub heV).trans hsubX.symm)

theorem Supermartingale.norm_condExp_dyadicDoob_terminal_difference_le_moduli
    (hX : Supermartingale X F P) (n m : ℕ)
    (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (hlV : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P m k ω) atTop (𝓝 (V ω)))
    {G H : Ω → ℝ≥0∞}
    (hG : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ n : ℕ) : ℝ≥0)) G)
    (hH : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ m : ℕ) : ℝ≥0)) H)
    (hGi : Integrable (fun ω ↦ (G ω).toReal) P)
    (hHi : Integrable (fun ω ↦ (H ω).toReal) P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ‖P[(U - dyadicDoobStep X F P n t) - (V - dyadicDoobStep X F P m t) | F t] ω‖ ≤
        P[(fun ω ↦ (G ω).toReal + (H ω).toReal) | F t] ω := by
  have he := hX.condExp_dyadicDoob_terminal_difference n m hb hZ hU hV hlZ hlU hlV t
  have hbnd := hX.norm_condExp_sub_le_condExp_globalConditionalModuli hG hH
    (hG.ae_ne_top_of_norm_bound hX.integrable hb)
    (hH.ae_ne_top_of_norm_bound hX.integrable hb) hGi hHi
    (le_dyadicRightGrid n t) (dyadicDoob_rightGrid_le n t)
    (le_dyadicRightGrid m t) (dyadicDoob_rightGrid_le m t)
  filter_upwards [he, hbnd] with ω heω hω
  simpa only [heω] using hω

theorem Supermartingale.integral_sq_dyadicDoob_terminal_sub_le
    (hX : Supermartingale X F P) {n m : ℕ} (hnm : n ≤ m)
    (hb : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (hlV : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P m k ω) atTop (𝓝 (V ω)))
    {G H : Ω → ℝ≥0∞}
    (hG : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ n : ℕ) : ℝ≥0)) G)
    (hH : IsGlobalConditionalIncrementModulus F P X (1 / ((2 ^ m : ℕ) : ℝ≥0)) H)
    (hG2 : MemLp (fun ω ↦ (G ω).toReal) 2 P)
    (hH2 : MemLp (fun ω ↦ (H ω).toReal) 2 P) :
    (∫ ω, (U ω - V ω) ^ 2 ∂P) ≤
      2 * ∫ ω, ((G ω).toReal + (H ω).toReal) * (U ω + V ω) ∂P := by
  apply IsStronglyPredictable.integral_sq_sub_terminal_le_of_condExp_tail_norm_bound
      (dyadicDoobStep_isStronglyPredictable_on_fine_grid X F P hnm)
      (dyadicDoobStep_isStronglyPredictable_on_fine_grid X F P (le_refl m))
      (hX.dyadicDoobStep_monotone_on_fine_grid n m)
      (hX.dyadicDoobStep_monotone_on_fine_grid m m)
      (Eventually.of_forall fun ω ↦ by simp)
      (Eventually.of_forall fun ω ↦ by simp)
      hU hV (hG2.add hH2)
      (Eventually.of_forall fun _ ↦ add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (dyadicDoobStep_tendsto_on_fine_grid X F P n m hlU)
      (dyadicDoobStep_tendsto_on_fine_grid X F P m m hlV)
  intro k
  exact hX.norm_condExp_dyadicDoob_terminal_difference_le_moduli n m hb hZ hU hV
    hlZ hlU hlV hG hH (hG2.integrable (by norm_num)) (hH2.integrable (by norm_num))
    ((k : ℝ≥0) / (2 ^ m : ℕ))

end MeasureTheory

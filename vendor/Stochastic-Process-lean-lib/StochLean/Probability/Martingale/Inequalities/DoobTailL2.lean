/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousL2Convergence

/-! # An L2 envelope for the entire martingale tail

Freeze the process before a deterministic starting time and use the reindexed
filtration. Conditional expectation bounds its increments by the closing
error. The global Doob theorem then controls every later time on one event.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}

theorem exists_memLp_two_tailEnvelope (hX : Martingale X F P)
    (hc : HasRightContinuousPaths X P) (hZ : MemLp Z 2 P)
    (hclose : ∀ t, X t =ᵐ[P] P[Z | F t]) (s : ℝ≥0) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ ω, 0 ≤ g ω) ∧ MemLp g 2 P ∧
      (∀ᵐ ω ∂P, ∀ t, s ≤ t → ‖X t ω - X s ω‖ ≤ g ω) ∧
      (∫ ω, g ω ^ 2 ∂P) ≤ 4 * ∫ ω, (X s ω - Z ω) ^ 2 ∂P := by
  let e (t : ℝ≥0) := max s t
  have he : Monotone e := fun _ _ h ↦ max_le_max_left s h
  have hec : Continuous e := continuous_const.max continuous_id
  let G := F.reindex e he
  let Y (t : ℝ≥0) (ω : Ω) := X (e t) ω - X s ω
  have hXs : StronglyMeasurable[G 0] (X s) := by
    change StronglyMeasurable[F (max s 0)] (X s)
    rw [max_eq_left (show (0 : ℝ≥0) ≤ s from bot_le)]
    exact hX.stronglyAdapted s
  have hY : Martingale Y G P := (hX.reindex e he).sub
    (martingale_const_fun G P hXs (hX.integrable s))
  have hYc : HasRightContinuousPaths Y P := by
    filter_upwards [hc] with ω hω t
    exact ((hω (e t)).comp hec.continuousWithinAt (fun u hu ↦ he hu)).sub
      continuousWithinAt_const
  have hL (t : ℝ≥0) : MemLp (X t) 2 P :=
    (hZ.condExp (by norm_num)).ae_eq (hclose t).symm
  have hYL (t : ℝ≥0) : MemLp (Y t) 2 P := (hL (e t)).sub (hL s)
  have hb (t : ℝ≥0) : (∫ ω, ‖Y t ω‖ ^ 2 ∂P) ≤ ∫ ω, (X s ω - Z ω) ^ 2 ∂P := by
    have h := integral_sq_le_of_eLpNorm_two_le (hYL t) ((hL s).sub hZ)
      (hX.eLpNorm_increment_le_closing_error (hZ.integrable (by norm_num)) hclose
        (le_max_left s t))
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using h
  obtain ⟨g, hgm, hgn, hgl, hgb, hgi⟩ := hY.exists_memLp_two_globalEnvelope hYc hYL hb
  refine ⟨g, hgm, hgn, hgl, ?_, hgi⟩
  filter_upwards [hgb] with ω hω t hst
  simpa only [Y, e, max_eq_right hst] using hω t

end MeasureTheory.Martingale

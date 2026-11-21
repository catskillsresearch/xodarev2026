/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.DambisDubinsSchwarzRaw
public import StochLean.Probability.Process.Filtration.IndependentIncrementsRightCont

/-! # The right-continuation step in Protter's DDS proof

The same actual raw-clock inverse and Brownian process work in `H_s = G_(s+)`,
where `G_s = F_(T_s)`. The right continuation is usual, future Gaussian increments
remain independent of its past, and the original clock remains a family of
stopping times. This does not assert that the original sampled `G` equals `H`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.dambis_dubins_schwarz_rightCont
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (h0 : X 0 =ᵐ[P] 0)
    (hu : ∀ᵐ ω ∂P, Tendsto
      ((hM.isSemimartingale hF).quadraticVariation hF · ω) atTop atTop) :
    let Q := (hM.isSemimartingale hF).quadraticVariation hF
    let τ := fun s : ℝ≥0 ↦ hittingAfter Q (Ioi (s : ℝ)) 0
    let B := fun s ↦ stoppedValue X (τ s)
    ∃ (hτ : ∀ s, IsStoppingTime F (τ s)) (hm : Monotone τ),
      let G := F.stoppingTimeReindex τ hτ hm
      let H := G.rightCont
      H.IsUsual P ∧ (∀ᵐ ω ∂P, ∀ s, τ s ω ≠ ⊤) ∧
      IsBrownianReal B P ∧ Adapted H B ∧
      (∀ s t, s ≤ t → Indep (H s)
        (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) ∧
      Indistinguishable (fun t ω ↦ B (Q t ω).toNNReal ω) X P ∧
      Indistinguishable (fun s ↦ stoppedValue Q (τ s)) (fun s _ ↦ (s : ℝ)) P ∧
      ∀ t, IsStoppingTime H (fun ω ↦ ((Q t ω).toNNReal : WithTop ℝ≥0)) := by
  obtain ⟨hτ, hm, hfin, hB, ha, hi, hrec, hlevel, hstop⟩ :=
    hM.dambis_dubins_schwarz hF h0 hu
  let Q := (hM.isSemimartingale hF).quadraticVariation hF
  let τ := fun s : ℝ≥0 ↦ hittingAfter Q (Ioi (s : ℝ)) 0
  let G := F.stoppingTimeReindex τ hτ hm
  have hG0 : F 0 ≤ G 0 :=
    (hτ 0).le_measurableSpace_of_const_le (fun _ ↦ bot_le)
  have hH : G.rightCont.IsUsual P := ⟨inferInstance, fun A hA ↦
    G.le_rightCont 0 A (hG0 A (hF.complete_initial A hA))⟩
  refine ⟨hτ, hm, hH, hfin, hB, ?_, ?_, hrec, hlevel, ?_⟩
  · intro s
    exact (ha s).mono (G.le_rightCont s) le_rfl
  · intro s t hst
    exact HasRightContinuousPaths.indep_increment_rightCont
      (hB.cont.mono fun _ hc _ ↦ hc.continuousWithinAt) ha hi hst
  · intro t s
    exact G.le_rightCont s _ (hstop t s)

end ProbabilityTheory

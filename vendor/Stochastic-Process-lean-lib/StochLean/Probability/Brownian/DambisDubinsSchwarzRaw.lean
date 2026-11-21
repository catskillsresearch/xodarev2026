/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.DambisDubinsSchwarz
public import StochLean.Probability.Process.Stopping.MeasurableSpaceCongruence

/-! # Dambis--Dubins--Schwarz with the source raw bracket

This is Protter II.42 with the actual strict-upper-level hitting times of the
raw quadratic variation and the exact stopping-time filtration `F_(T_s)`.
Completeness, not mere equality in law, transports the filtration. The original
clock is viewed in nonnegative time using `Real.toNNReal`; its nonnegativity and
equality with the continuous bracket hold on one common full-measure event.
No right continuity of the sampled filtration is asserted here.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsContinuousLocalMartingale.dambis_dubins_schwarz
    (hM : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P)
    (h0 : X 0 =ᵐ[P] 0)
    (hu : ∀ᵐ ω ∂P, Tendsto
      ((hM.isSemimartingale hF).quadraticVariation hF · ω) atTop atTop) :
    let Q := (hM.isSemimartingale hF).quadraticVariation hF
    let τ := fun s : ℝ≥0 ↦ hittingAfter Q (Ioi (s : ℝ)) 0
    let B := fun s ↦ stoppedValue X (τ s)
    ∃ (hτ : ∀ s, IsStoppingTime F (τ s)) (hm : Monotone τ),
      let G := F.stoppingTimeReindex τ hτ hm
      (∀ᵐ ω ∂P, ∀ s, τ s ω ≠ ⊤) ∧
      IsBrownianReal B P ∧ Adapted G B ∧
      (∀ s t, s ≤ t → Indep (G s)
        (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) P) ∧
      Indistinguishable (fun t ω ↦ B (Q t ω).toNNReal ω) X P ∧
      Indistinguishable (fun s ↦ stoppedValue Q (τ s)) (fun s _ ↦ (s : ℝ)) P ∧
      ∀ t, IsStoppingTime G (fun ω ↦ ((Q t ω).toNNReal : WithTop ℝ≥0)) := by
  let hS := hM.isSemimartingale hF
  let Q := hS.quadraticVariation hF
  let A := hS.continuousBracketClock hF
  let T := clockInverseTime A
  let τ := fun s : ℝ≥0 ↦ hittingAfter Q (Ioi (s : ℝ)) 0
  let C := fun s ↦ stoppedValue X (T s)
  let B := fun s ↦ stoppedValue X (τ s)
  have heT : ∀ᵐ ω ∂P, ∀ s, T s ω = τ s ω := hM.raw_inverse_times_eq_clock hF h0
  have heQ : ∀ᵐ ω ∂P, ∀ t, (A t ω : ℝ) = Q t ω := by
    filter_upwards [h0, hS.continuousQuadraticVariation_eq_of_continuous hF hM.2]
      with ω hω hq t
    rw [hS.coe_continuousBracketClock hF, hq t]
    simp only [hω, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero, Q]
  have heA : ∀ᵐ ω ∂P, ∀ t, A t ω = (Q t ω).toNNReal := by
    filter_upwards [heQ] with ω hω t
    rw [← hω t, Real.toNNReal_coe]
  have heB : Indistinguishable C B P := by
    filter_upwards [heT] with ω hω s
    change X (T s ω).untopA ω = X (τ s ω).untopA ω
    rw [hω s]
  obtain ⟨hT, hfin, hcC, _, hrec, hlevels, hstop⟩ :=
    hM.inverse_quadraticVariation_timeChange hF hu
  have hτ : ∀ s, IsStoppingTime F (τ s) := fun s ↦
    (hT s).congr_ae_of_usual hF (heT.mono fun _ h ↦ h s)
  have hm : Monotone τ := fun s t hst ↦
    hittingAfter_anti Q 0 (Ioi_subset_Ioi (show (s : ℝ) ≤ (t : ℝ) from hst))
  let G := F.stoppingTimeReindex τ hτ hm
  have hspace (s : ℝ≥0) : (hT s).measurableSpace = G s :=
    (hT s).measurableSpace_congr_ae_of_usual (hτ s) hF (heT.mono fun _ h ↦ h s)
  have hcomplete (s : ℝ≥0) : IsCompleteSubMeasurableSpace P (G s) := fun a ha ↦
    (hτ s).le_measurableSpace_of_const_le (fun _ ↦ bot_le) a (hF.complete_initial a ha)
  have haB : Adapted G B := fun s ↦
    hM.1.1.measurable_stoppedValue_of_leftContinuous_usual hF
      (hM.2.mono fun _ h _ ↦ h.continuousWithinAt) (hτ s)
  have hBrownian : IsBrownianReal B P :=
    ⟨(hM.isBrownianReal_inverse_clock hF h0 hu).toIsPreBrownianReal.congr heB.ae_eq,
      HasContinuousPaths.congr heB hcC⟩
  refine ⟨hτ, hm, ?_, hBrownian, haB, ?_, ?_, ?_, ?_⟩
  · filter_upwards [heT, hfin] with ω he hf s
    change τ s ω ≠ ⊤
    rw [← he s]
    exact hf s
  · intro s t hst
    apply indep_comap_of_condExp_characteristic (ν := gaussianReal 0 (t - s))
      (G.le s) ((haB.measurable (i := t)).sub (haB.measurable (i := s)))
    intro u
    rw [← hspace s]
    apply Filter.EventuallyEq.trans (condExp_congr_ae ?_)
      (hM.condExp_inverse_clock_increment_gaussian hF hu hst u)
    filter_upwards [heB] with ω he
    change Complex.exp (Complex.I * (u : ℂ) * ((B t ω - B s ω : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (u : ℂ) * ((C t ω - C s ω : ℝ) : ℂ))
    rw [he s, he t]
  · filter_upwards [heB, heA, hrec] with ω he ha hr t
    change B (Q t ω).toNNReal ω = X t ω
    rw [← ha t, ← he]
    exact hr t
  · filter_upwards [heT, heQ, hlevels] with ω ht hq hl s
    change Q (τ s ω).untopA ω = (s : ℝ)
    rw [← ht s, ← hq]
    exact congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) (hl s)
  · intro t s
    have hc : MeasurableSet[G s] {ω | (A t ω : WithTop ℝ≥0) ≤ s} := by
      rw [← hspace s]
      exact hstop t s
    let : MeasurableSpace Ω := G s
    apply measurableSet_setOfPred.mpr
    apply (hcomplete s).measurable_congr_ae (measurableSet_setOfPred.mp hc)
    filter_upwards [heA] with ω he
    exact congrArg (fun r : ℝ≥0 ↦ (r : WithTop ℝ≥0) ≤ s) (he t)

end ProbabilityTheory

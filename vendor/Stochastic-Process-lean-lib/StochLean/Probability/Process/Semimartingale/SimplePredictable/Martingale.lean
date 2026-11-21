/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.OptionalSampling.ContinuousWeightedIncrement
public import
  StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegralProcessRegularity
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.L2

/-! # Bounded elementary integrands preserve martingales

Random endpoints need not be deterministically bounded. Conditional increments
are computed after raising each endpoint to the conditioning time. Coefficients
on empty cells are normalized only when deducing a coefficient bound from a
process bound. The initial coefficient and initial martingale value are retained.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

theorem SimplePredictableRep.martingale_integralProcess_of_coefficients
    (H : SimplePredictableRep F) (hX : Martingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ)
    (hinit : ∀ᵐ ω ∂P, ‖H.initial ω‖ ≤ C)
    (hb : ∀ i, ∀ᵐ ω ∂P, ‖H.coefficient i ω‖ ≤ C) :
    Martingale (H.integralProcess X) F P := by
  classical
  have hiStop (a : FiniteStoppingTime F) (T : ℝ≥0) :
      Integrable (fun ω ↦ X (min (a ω) T) ω) P :=
    integrable_condExp.congr
      (hX.finiteStoppingTime_min_ae_eq_condExp_terminal hF hr a T).symm
  have hmC (i : Fin H.partition.size) : Measurable (H.coefficient i) :=
    (H.measurable_coefficient i).mono (H.partition.point i.castSucc).measurableSpace_le le_rfl
  have hiJ (T : ℝ≥0) : Integrable (H.integralProcess X T) P := by
    have hi0 : Integrable (fun ω ↦ H.initial ω * X 0 ω) P :=
      (hX.integrable 0).bdd_smul C
        (H.measurable_initial.mono (F.le 0) le_rfl).aestronglyMeasurable hinit
    have hiterm (i : Fin H.partition.size) : Integrable (fun ω ↦ H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) T) ω -
          X (min (H.partition.point i.castSucc ω) T) ω)) P :=
      ((hiStop (H.partition.point i.succ) T).sub
        (hiStop (H.partition.point i.castSucc) T)).bdd_smul C (hmC i).aestronglyMeasurable (hb i)
    have his : Integrable (fun ω ↦ ∑ i, H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) T) ω -
          X (min (H.partition.point i.castSucc ω) T) ω)) P := by
      rw [show (fun ω ↦ ∑ i, H.coefficient i ω *
          (X (min (H.partition.point i.succ ω) T) ω -
            X (min (H.partition.point i.castSucc ω) T) ω)) =
          ∑ i : Fin H.partition.size, (fun ω ↦ H.coefficient i ω *
            (X (min (H.partition.point i.succ ω) T) ω -
              X (min (H.partition.point i.castSucc ω) T) ω)) by
        funext ω
        simp only [Finset.sum_apply]]
      exact integrable_finsetSum' _ (fun i _ ↦ hiterm i)
    convert! hi0.add his using 1
    funext ω
    exact H.integralProcess_apply X T ω
  have haJ := (H.adapted_integralProcess hX.stronglyAdapted.adapted hF hr).stronglyAdapted
  refine ⟨haJ, fun s t hst ↦ ?_⟩
  let a (i : Fin H.partition.size) :=
    (H.partition.point i.castSucc).max (FiniteStoppingTime.const F s)
  let b (i : Fin H.partition.size) := (H.partition.point i.succ).max (FiniteStoppingTime.const F s)
  let U (i : Fin H.partition.size) : Ω → ℝ := fun ω ↦ H.coefficient i ω *
    (X (min (b i ω) t) ω - X (min (a i ω) t) ω)
  have hiU (i : Fin H.partition.size) : Integrable (U i) P :=
    ((hiStop (b i) t).sub (hiStop (a i) t)).bdd_smul C (hmC i).aestronglyMeasurable (hb i)
  have hzU (i : Fin H.partition.size) : P[U i | F s] =ᵐ[P] 0 := by
    have hca : Measurable[(a i).measurableSpace] (H.coefficient i) :=
      (H.measurable_coefficient i).mono
        ((H.partition.point i.castSucc).isStoppingTime.measurableSpace_mono
          (a i).isStoppingTime (fun ω ↦ WithTop.coe_le_coe.mpr (le_max_left _ _))) le_rfl
    exact hX.condExp_weighted_finiteStoppingTime_increment_min_of_le hF hr (a i) (b i)
      (fun ω ↦ max_le_max_right s (H.partition.monotone_point ω (Fin.castSucc_le_succ i)))
      t hca C (hb i) (fun _ ↦ le_max_right _ _)
  have heq : H.integralProcess X t - H.integralProcess X s = fun ω ↦ ∑ i, U i ω := by
    funext ω
    change H.integralProcess X t ω - H.integralProcess X s ω = _
    rw [H.integralProcess_apply, H.integralProcess_apply, add_sub_add_left_eq_sub,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hmin (v : ℝ≥0) : X (min v t) ω - X (min v s) ω =
        X (min (max v s) t) ω - X s ω := by
      by_cases hv : v ≤ s
      · simp only [min_eq_left hv, min_eq_left (hv.trans hst), max_eq_right hv,
          min_eq_left hst, sub_self]
      · simp only [min_eq_right (le_of_not_ge hv), max_eq_left (le_of_not_ge hv)]
    change H.coefficient i ω * (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω) -
      H.coefficient i ω * (X (min (H.partition.point i.succ ω) s) ω -
        X (min (H.partition.point i.castSucc ω) s) ω) = _
    rw [← mul_sub]
    change H.coefficient i ω * _ = H.coefficient i ω *
      (X (min (max (H.partition.point i.succ ω) s) t) ω -
        X (min (max (H.partition.point i.castSucc ω) s) t) ω)
    congr 1
    calc
      _ = (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.succ ω) s) ω) -
        (X (min (H.partition.point i.castSucc ω) t) ω -
          X (min (H.partition.point i.castSucc ω) s) ω) := by ring
      _ = _ := by rw [hmin, hmin]; ring
  have hz : P[H.integralProcess X t - H.integralProcess X s | F s] =ᵐ[P] 0 := by
    rw [heq]
    rw [show (fun ω ↦ ∑ i, U i ω) = ∑ i, U i by
      funext ω
      simp only [Finset.sum_apply]]
    have hsum := condExp_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset (Fin H.partition.size))) ↦
      hiU i) (F s)
    filter_upwards [hsum, ae_all_iff.mpr hzU] with ω hsumω hω
    rw [hsumω]
    simp only [Finset.sum_apply, hω, Pi.zero_apply, Finset.sum_const_zero]
  have hself : P[H.integralProcess X s | F s] = H.integralProcess X s :=
    condExp_of_stronglyMeasurable (F.le s) (haJ s) (hiJ s)
  filter_upwards [condExp_sub (hiJ t) (hiJ s) (F s), hz] with ω hsub hzω
  rw [hself] at hsub
  change P[H.integralProcess X t - H.integralProcess X s | F s] ω =
    P[H.integralProcess X t | F s] ω - H.integralProcess X s ω at hsub
  exact sub_eq_zero.mp (hsub.symm.trans hzω)

theorem SimplePredictableRep.martingale_integralProcess
    (H : SimplePredictableRep F) (hX : Martingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ≥0)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) : Martingale (H.integralProcess X) F P := by
  have heq := H.removeEmptyIntervals.integralProcess_congr H H.toProcess_removeEmptyIntervals X
  rw [← heq]
  apply H.removeEmptyIntervals.martingale_integralProcess_of_coefficients hX hF hr C
  · apply ae_of_all
    intro ω
    change ‖H.initial ω‖ ≤ (C : ℝ)
    simpa only [H.toProcess_zero] using hb 0 ω
  · intro i
    exact ae_of_all P (H.norm_coefficient_removeEmptyIntervals_le C.coe_nonneg hb i)

theorem IsSimplePredictable.martingale_elementaryIntegralProcess {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (hX : Martingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    Martingale (hH.elementaryIntegralProcess X) F P :=
  hH.choose.martingale_integralProcess hX hF hr C (by simpa only [hH.choose_spec] using hb)

theorem IsSimplePredictable.isSquareIntegrableMartingale_elementaryIntegralProcess
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (hX : IsSquareIntegrableMartingale X F P) (hF : F.IsUsual P)
    (hr : HasRightContinuousPaths X P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    IsSquareIntegrableMartingale (hH.elementaryIntegralProcess X) F P :=
  ⟨hH.martingale_elementaryIntegralProcess hX.1 hF hr C hb,
    fun t ↦ hH.memLp_elementaryIntegral_min_const hX.1 hF hr t (hX.2 t) C hb⟩

end ProbabilityTheory

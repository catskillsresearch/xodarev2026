/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.CrossSums
public import StochLean.Probability.Process.Partition.CrossSumsRegularity
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.OneSidedStopping
public import StochLean.Probability.Process.UCP.CadlagMultiplication

/-! # Bracket sums of simple integrals: the simple case of Protter II.29

Finite random coefficients multiply genuine stopped mixed-sum limits. They
need not be bounded or integrable. The source initial product is retained.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

theorem tendstoUCP_quadraticCovariationSum_integralProcess (H : SimplePredictableRep F)
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).quadraticCovariationSumProcess (H.integralProcess X) Y)
      atTop (H.integralProcess (hX.quadraticCovariation hY hF)) := by
  let B := hX.quadraticCovariation hY hF
  let hB := hX.isSemimartingale_quadraticCovariation hY hF
  let R := fun (τ : FiniteStoppingTime F) n ↦
    (π n).quadraticCovariationSumProcess (stoppedProcess X τ.withTop) Y
  let A := fun (τ : FiniteStoppingTime F) ↦ stoppedProcess B τ.withTop
  have hR (τ : FiniteStoppingTime F) : TendstoUCP P (R τ) atTop (A τ) :=
    ((hX.stoppedProcess hF τ.isStoppingTime).tendstoUCP_quadraticCovariationSumProcess
      hY hF hπ).congr_right (hX.quadraticCovariation_stoppedProcess_left hY hF τ.isStoppingTime)
  have hmR (τ : FiniteStoppingTime F) (n : ℕ) : ∀ t, Measurable (R τ n t) := by
    let hS := hX.stoppedProcess hF τ.isStoppingTime
    intro t
    exact ((π n).adapted_quadraticCovariationSumProcess hS.adapted hY.adapted hF
      hS.hasCadlagPaths.hasRightContinuousPaths hY.hasCadlagPaths.hasRightContinuousPaths t).mono
        (F.le t) le_rfl
  have hrR (τ : FiniteStoppingTime F) (n : ℕ) : HasCadlagPaths (R τ n) P :=
    (π n).hasCadlagPaths_quadraticCovariationSumProcess
      (hX.hasCadlagPaths.stoppedProcess τ.withTop) hY.hasCadlagPaths
  have hmA (τ : FiniteStoppingTime F) : ∀ t, Measurable (A τ t) := fun t ↦
    ((hB.stoppedProcess hF τ.isStoppingTime).adapted t).mono (F.le t) le_rfl
  have hrA (τ : FiniteStoppingTime F) : HasCadlagPaths (A τ) P :=
    hB.hasCadlagPaths.stoppedProcess τ.withTop
  let C := fun (i : Fin H.partition.size) n t ω ↦ H.coefficient i ω *
    (R (H.partition.point i.succ) n t ω - R (H.partition.point i.castSucc) n t ω)
  let D := fun (i : Fin H.partition.size) t ω ↦ H.coefficient i ω *
    (A (H.partition.point i.succ) t ω - A (H.partition.point i.castSucc) t ω)
  have hcell (i : Fin H.partition.size) : TendstoUCP P (C i) atTop (D i) := by
    have hc : Measurable (H.coefficient i) :=
      (H.measurable_coefficient i).mono (H.partition.point i.castSucc).measurableSpace_le le_rfl
    exact TendstoUCP.mul_left_of_cadlag
      ((hR (H.partition.point i.succ)).sub (hR (H.partition.point i.castSucc)))
        (fun n t ↦ (hmR _ n t).sub (hmR _ n t))
        (fun t ↦ (hmA _ t).sub (hmA _ t)) (fun _ ↦ hc)
        (fun n ↦ (hrR _ n).sub (hrR _ n)) ((hrA _).sub (hrA _))
        (ae_of_all _ fun _ ↦ IsContinuousPath.isCadlagPath continuous_const)
  have hsum (s : Finset (Fin H.partition.size)) :
      TendstoUCP P (fun n ↦ ∑ i ∈ s, C i n) atTop (∑ i ∈ s, D i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using tendstoUCP_const atTop (0 : ℝ≥0 → Ω → ℝ)
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hcell i).add ih
  have hu := (tendstoUCP_const atTop (fun (_ : ℝ≥0) ω ↦ H.initial ω * X 0 ω * Y 0 ω)).add
    (hsum univ)
  have heq : Indistinguishable
      ((fun (_ : ℝ≥0) ω ↦ H.initial ω * X 0 ω * Y 0 ω) + ∑ i, D i)
      (H.integralProcess B) P := by
    filter_upwards [hX.quadraticCovariation_zero_ae hY hF] with ω h0 t
    simp only [Pi.add_apply, Finset.sum_apply, integralProcess_apply, D, A,
      FiniteStoppingTime.stoppedProcess_eq]
    rw [show B 0 ω = X 0 ω * Y 0 ω from h0, mul_assoc]
    simp only [min_comm]
  have hleft (n : ℕ) : Indistinguishable
      ((fun (_ : ℝ≥0) ω ↦ H.initial ω * X 0 ω * Y 0 ω) + ∑ i, C i n)
      ((π n).quadraticCovariationSumProcess (H.integralProcess X) Y) P := by
    apply ae_of_all
    intro ω t
    rw [H.quadraticCovariationSumProcess_integralProcess]
    simp only [Pi.add_apply, Finset.sum_apply, C, R]
  exact (hu.congr_left hleft).congr_right heq

end ProbabilityTheory.SimplePredictableRep

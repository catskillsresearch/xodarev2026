/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Basic
public import StochLean.Probability.Process.Stopping.Filtration

/-! # Stricker's filtration-shrinkage theorem

Source stopping partitions and their coefficient measurability embed into a larger
filtration without changing the process or its elementary integral. Thus a smaller
filtration preserves semimartingales whenever the integrator remains adapted.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F G : Filtration ℝ≥0 mΩ}
  {P : Measure Ω}

def StoppingTimePartition.mapFiltration (π : StoppingTimePartition F) (hFG : ∀ t, F t ≤ G t) :
    StoppingTimePartition G where
  size := π.size
  point := fun i ↦ (π.point i).mapFiltration hFG
  monotone_point := π.monotone_point
  first_eq_zero := π.first_eq_zero

def SimplePredictableRep.mapFiltration (H : SimplePredictableRep F) (hFG : ∀ t, F t ≤ G t) :
    SimplePredictableRep G where
  partition := H.partition.mapFiltration hFG
  initial := H.initial
  measurable_initial := H.measurable_initial.mono (hFG 0) le_rfl
  coefficient := H.coefficient
  measurable_coefficient := fun i ↦ (H.measurable_coefficient i).mono
    ((H.partition.point i.castSucc).measurableSpace_le_mapFiltration hFG) le_rfl

@[simp] theorem SimplePredictableRep.toProcess_mapFiltration (H : SimplePredictableRep F)
    (hFG : ∀ t, F t ≤ G t) : (H.mapFiltration hFG).toProcess = H.toProcess := rfl

@[simp] theorem SimplePredictableRep.integral_mapFiltration (H : SimplePredictableRep F)
    (hFG : ∀ t, F t ≤ G t) (X : ℝ≥0 → Ω → ℝ) :
    (H.mapFiltration hFG).integral X = H.integral X := rfl

theorem IsSimplePredictable.monoFiltration {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F)
    (hFG : ∀ t, F t ≤ G t) : IsSimplePredictable H G :=
  ⟨hH.choose.mapFiltration hFG, hH.choose_spec⟩

theorem IsSimplePredictable.elementaryIntegral_monoFiltration {H : ℝ≥0 → Ω → ℝ}
    (hH : IsSimplePredictable H F) (hFG : ∀ t, F t ≤ G t) (X : ℝ≥0 → Ω → ℝ) :
    (hH.monoFiltration hFG).elementaryIntegral X = hH.elementaryIntegral X := by
  rw [IsSimplePredictable.elementaryIntegral_eq _ (hH.choose.mapFiltration hFG)
    hH.choose_spec, SimplePredictableRep.integral_mapFiltration]
  rfl

theorem IsGoodIntegrator.shrinkFiltration {X : ℝ≥0 → Ω → ℝ} (hX : IsGoodIntegrator X G P)
    (hFG : ∀ t, F t ≤ G t) : IsGoodIntegrator X F P := by
  intro H hH hu
  have h := hX H (fun n ↦ (hH n).monoFiltration hFG) hu
  have heq : (fun n ↦ ((hH n).monoFiltration hFG).elementaryIntegral X) =
      (fun n ↦ (hH n).elementaryIntegral X) :=
    funext (fun n ↦ (hH n).elementaryIntegral_monoFiltration hFG X)
  rw [heq] at h
  exact h

theorem IsTotalSemimartingale.stricker {X : ℝ≥0 → Ω → ℝ} (hX : IsTotalSemimartingale X G P)
    (hFG : ∀ t, F t ≤ G t) (ha : Adapted F X) : IsTotalSemimartingale X F P :=
  ⟨ha, hX.2.1, hX.2.2.shrinkFiltration hFG⟩

theorem IsSemimartingale.stricker {X : ℝ≥0 → Ω → ℝ} (hX : IsSemimartingale X G P)
    (hFG : ∀ t, F t ≤ G t) (ha : Adapted F X) : IsSemimartingale X F P := by
  intro T
  apply (hX T).stricker hFG
  intro t
  change Measurable[F t] (fun ω ↦ X (min t T) ω)
  exact (ha _).mono (F.mono (min_le_left t T)) le_rfl

end ProbabilityTheory

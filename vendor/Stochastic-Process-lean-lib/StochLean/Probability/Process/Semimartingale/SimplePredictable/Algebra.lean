/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.SimplePredictable.Refinement
public import StochLean.Probability.Process.Semimartingale.SimplePredictable.IntegratorAlgebra

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

/-- Combine the two repartitioned coefficient families on one proposed partition. -/
noncomputable def combineOn (H K : SimplePredictableRep F) (ρ : StoppingTimePartition F)
    (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) : SimplePredictableRep F where
  partition := ρ
  initial := fun ω ↦ φ (H.initial ω) (K.initial ω)
  measurable_initial := hφ.comp (H.measurable_initial.prodMk K.measurable_initial)
  coefficient := fun i ω ↦ φ ((H.repartition ρ).coefficient i ω)
    ((K.repartition ρ).coefficient i ω)
  measurable_coefficient := fun i ↦ hφ.comp
    (((H.repartition ρ).measurable_coefficient i).prodMk
      ((K.repartition ρ).measurable_coefficient i))

theorem toProcess_combineOn (H K : SimplePredictableRep F) (ρ : StoppingTimePartition F)
    (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (h0 : φ 0 0 = 0) :
    (H.combineOn K ρ φ hφ).toProcess =
      fun t ω ↦ φ ((H.repartition ρ).toProcess t ω) ((K.repartition ρ).toProcess t ω) := by
  funext t ω
  by_cases ht : t = 0
  · subst t
    simp only [toProcess_zero]
    rfl
  by_cases hterm : t ≤ ρ.terminal ω
  · have hcell : ∃ i : Fin ρ.size, ρ.point i.castSucc ω < t ∧ t ≤ ρ.point i.succ ω :=
      (ρ.path ω).exists_cell ⟨lt_of_le_of_ne bot_le (Ne.symm ht), hterm⟩
    obtain ⟨i, hi⟩ := hcell
    rw [(H.combineOn K ρ φ hφ).toProcess_eq_coefficient_of_mem_cell (i := i) hi,
      (H.repartition ρ).toProcess_eq_coefficient_of_mem_cell (i := i) hi,
      (K.repartition ρ).toProcess_eq_coefficient_of_mem_cell (i := i) hi]
    rfl
  · have hρt := lt_of_not_ge hterm
    rw [(H.combineOn K ρ φ hφ).toProcess_eq_zero_of_terminal_lt hρt,
      (H.repartition ρ).toProcess_eq_zero_of_terminal_lt hρt,
      (K.repartition ρ).toProcess_eq_zero_of_terminal_lt hρt, h0]

/-- A common-refinement realization of a binary Borel operation. -/
noncomputable def combine (H K : SimplePredictableRep F) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) : SimplePredictableRep F :=
  H.combineOn K (H.partition.exists_common_refinement K.partition).choose φ hφ

theorem toProcess_combine (H K : SimplePredictableRep F) (φ : ℝ → ℝ → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (h0 : φ 0 0 = 0) :
    (H.combine K φ hφ).toProcess = fun t ω ↦ φ (H.toProcess t ω) (K.toProcess t ω) := by
  obtain ⟨hH, hK⟩ := (H.partition.exists_common_refinement K.partition).choose_spec
  rw [combine, toProcess_combineOn H K _ φ hφ h0,
    H.toProcess_repartition hH, K.toProcess_repartition hK]

theorem integral_combineOn_add (H K : SimplePredictableRep F) (ρ : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → ℝ) :
    (H.combineOn K ρ (· + ·) (measurable_fst.add measurable_snd)).integral X =
      fun ω ↦ (H.repartition ρ).integral X ω + (K.repartition ρ).integral X ω := by
  funext ω
  change (H.initial ω + K.initial ω) * X 0 ω +
    (∑ i : Fin ρ.size, ((H.repartition ρ).coefficient i ω +
      (K.repartition ρ).coefficient i ω) *
        (X (ρ.point i.succ ω) ω - X (ρ.point i.castSucc ω) ω)) =
    (H.initial ω * X 0 ω + ∑ i : Fin ρ.size, (H.repartition ρ).coefficient i ω *
      (X (ρ.point i.succ ω) ω - X (ρ.point i.castSucc ω) ω)) +
    (K.initial ω * X 0 ω + ∑ i : Fin ρ.size, (K.repartition ρ).coefficient i ω *
      (X (ρ.point i.succ ω) ω - X (ρ.point i.castSucc ω) ω))
  simp only [add_mul, sum_add_distrib]
  ring

theorem integral_combine_add (H K : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    (H.combine K (· + ·) (measurable_fst.add measurable_snd)).integral X =
      fun ω ↦ H.integral X ω + K.integral X ω := by
  obtain ⟨hH, hK⟩ := (H.partition.exists_common_refinement K.partition).choose_spec
  change (H.combineOn K (H.partition.exists_common_refinement K.partition).choose
    (fun a b : ℝ ↦ a + b) _).integral X = _
  rw [integral_combineOn_add, H.integral_repartition hH, K.integral_repartition hK]

/-- Scalar multiplication does not require a new stopping partition. -/
def scale (H : SimplePredictableRep F) (c : ℝ) : SimplePredictableRep F where
  partition := H.partition
  initial := fun ω ↦ c * H.initial ω
  measurable_initial := measurable_const.mul H.measurable_initial
  coefficient := fun i ω ↦ c * H.coefficient i ω
  measurable_coefficient := fun i ↦ measurable_const.mul (H.measurable_coefficient i)

theorem toProcess_scale (H : SimplePredictableRep F) (c : ℝ) :
    (H.scale c).toProcess = fun t ω ↦ c * H.toProcess t ω := by
  funext t ω
  change (if t = 0 then c * H.initial ω else ∑ i : Fin H.partition.size,
    if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then c * H.coefficient i ω else 0) = c * H.toProcess t ω
  rw [toProcess]
  split_ifs with ht
  · rfl
  · rw [mul_sum]
    apply sum_congr rfl
    intro i _
    split_ifs
    · rfl
    · exact (mul_zero c).symm

theorem integral_scale (H : SimplePredictableRep F) (c : ℝ) (X : ℝ≥0 → Ω → ℝ) :
    (H.scale c).integral X = fun ω ↦ c * H.integral X ω := by
  funext ω
  change (c * H.initial ω) * X 0 ω + ∑ i : Fin H.partition.size,
    (c * H.coefficient i ω) * (X (H.partition.point i.succ ω) ω -
      X (H.partition.point i.castSucc ω) ω) =
    c * (H.initial ω * X 0 ω + ∑ i : Fin H.partition.size, H.coefficient i ω *
      (X (H.partition.point i.succ ω) ω - X (H.partition.point i.castSucc ω) ω))
  simp only [mul_add, mul_sum, mul_assoc]

theorem integral_smul_integrator (H : SimplePredictableRep F) (c : ℝ)
    (X : ℝ≥0 → Ω → ℝ) :
    H.integral (c • X) = fun ω ↦ c * H.integral X ω :=
  H.integral_const_mul_integrator c X

end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

theorem map₂ (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F)
    (φ : ℝ → ℝ → ℝ) (hφ : Measurable (Function.uncurry φ)) (h0 : φ 0 0 = 0) :
    IsSimplePredictable (fun t ω ↦ φ (H t ω) (K t ω)) F := by
  refine ⟨hH.choose.combine hK.choose φ hφ, ?_⟩
  rw [SimplePredictableRep.toProcess_combine _ _ φ hφ h0, hH.choose_spec, hK.choose_spec]

theorem add (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F) :
    IsSimplePredictable (H + K) F :=
  hH.map₂ hK (· + ·) (measurable_fst.add measurable_snd) (add_zero 0)

theorem mul (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F) :
    IsSimplePredictable (H * K) F :=
  hH.map₂ hK (· * ·) (measurable_fst.mul measurable_snd) (mul_zero 0)

theorem smul (hH : IsSimplePredictable H F) (c : ℝ) : IsSimplePredictable (c • H) F := by
  refine ⟨hH.choose.scale c, ?_⟩
  rw [SimplePredictableRep.toProcess_scale, hH.choose_spec]
  rfl

theorem neg (hH : IsSimplePredictable H F) : IsSimplePredictable (-H) F := by
  simpa only [neg_one_smul] using hH.smul (-1)

theorem sub (hH : IsSimplePredictable H F) (hK : IsSimplePredictable K F) :
    IsSimplePredictable (H - K) F := by
  simpa only [sub_eq_add_neg] using hH.add hK.neg

theorem elementaryIntegral_add (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    (hH.add hK).elementaryIntegral X =
      fun ω ↦ hH.elementaryIntegral X ω + hK.elementaryIntegral X ω := by
  have heq : (hH.choose.combine hK.choose (· + ·)
      (measurable_fst.add measurable_snd)).toProcess = H + K := by
    funext t ω
    calc
      _ = hH.choose.toProcess t ω + hK.choose.toProcess t ω :=
        congrFun (congrFun (hH.choose.toProcess_combine hK.choose
          (fun a b : ℝ ↦ a + b) (measurable_fst.add measurable_snd) (add_zero 0)) t) ω
      _ = (H + K) t ω := congrArg₂ (· + ·)
        (congrFun (congrFun hH.choose_spec t) ω) (congrFun (congrFun hK.choose_spec t) ω)
  rw [elementaryIntegral_eq _ _ heq, SimplePredictableRep.integral_combine_add]
  rfl

theorem elementaryIntegral_smul (hH : IsSimplePredictable H F) (c : ℝ)
    (X : ℝ≥0 → Ω → ℝ) :
    (hH.smul c).elementaryIntegral X = fun ω ↦ c * hH.elementaryIntegral X ω := by
  have heq : (hH.choose.scale c).toProcess = c • H := by
    rw [SimplePredictableRep.toProcess_scale, hH.choose_spec]
    rfl
  rw [elementaryIntegral_eq _ _ heq, SimplePredictableRep.integral_scale]
  rfl

theorem elementaryIntegral_smul_integrator (hH : IsSimplePredictable H F) (c : ℝ)
    (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral (c • X) = fun ω ↦ c * hH.elementaryIntegral X ω :=
  hH.choose.integral_smul_integrator c X

theorem elementaryIntegral_congr (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (hHK : H = K) (X : ℝ≥0 → Ω → ℝ) :
    hH.elementaryIntegral X = hK.elementaryIntegral X := by
  subst K
  rfl

theorem elementaryIntegral_neg (hH : IsSimplePredictable H F) (X : ℝ≥0 → Ω → ℝ) :
    hH.neg.elementaryIntegral X = fun ω ↦ -hH.elementaryIntegral X ω := by
  have heq : (-H : ℝ≥0 → Ω → ℝ) = (-1 : ℝ) • H := by simp
  rw [hH.neg.elementaryIntegral_congr (hH.smul (-1)) heq X, hH.elementaryIntegral_smul]
  funext ω
  ring

theorem elementaryIntegral_sub (hH : IsSimplePredictable H F)
    (hK : IsSimplePredictable K F) (X : ℝ≥0 → Ω → ℝ) :
    (hH.sub hK).elementaryIntegral X =
      fun ω ↦ hH.elementaryIntegral X ω - hK.elementaryIntegral X ω := by
  rw [(hH.sub hK).elementaryIntegral_congr (hH.add hK.neg) (sub_eq_add_neg H K) X,
    hH.elementaryIntegral_add hK.neg X, hK.elementaryIntegral_neg X]
  rfl

end IsSimplePredictable
end ProbabilityTheory

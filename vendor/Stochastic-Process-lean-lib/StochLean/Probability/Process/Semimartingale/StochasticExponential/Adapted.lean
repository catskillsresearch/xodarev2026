/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.StochasticExponential.Basic
public import StochLean.Probability.Process.Semimartingale.QuadraticVariation.Atoms
public import StochLean.Probability.Process.Measurability.CadlagVersion
public import StochLean.Probability.Process.Measurability.CappedJump
public import StochLean.Analysis.PathVariation.MeasurableExponentialJumpProduct

/-! # Adaptedness of the actual stochastic exponential and jump product

The finite-horizon raw-bracket measure supplies the sample-dependent jump
atoms. Joint measurability uses capped paths and only the horizon sigma-field.
A single initial null set is removed and restored by usual completeness.
Thus adaptedness is proved, not inferred from an uncountable product of
coordinatewise measurable random variables.
-/

@[expose] public section

open MeasureTheory StochLean Set Function
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.adapted_stochasticExponentialJumpProduct
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (stochasticExponentialJumpProduct X) := by
  classical
  obtain ⟨Y, hXY, hYp, hYc⟩ :=
    hX.adapted.stronglyAdapted.exists_cadlag_indistinguishable_of_usual hF hX.hasCadlagPaths
  let D := Classical.choice (hX.nonempty_bracketRealization hX hF)
  let G : Ω → Prop := fun ω ↦
    (∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ jumpProcess Y s ω ^ 2)) ∧
    (∀ s : ℝ≥0, 0 < s → (D.left ω).measure {s} =
      ENNReal.ofReal (jumpProcess Y s ω ^ 2))
  have hG : ∀ᵐ ω ∂P, G ω := by
    filter_upwards [hX.summable_sq_jumps hF, D.left_singleton_eq_sq_jump,
      hXY.jumpProcess] with ω hs hm he
    constructor
    · intro T
      simpa only [← he] using hs T
    · intro s hs0
      simpa only [← he] using hm s hs0
  have hbad : MeasurableSet[F 0] {ω | ¬G ω} := hF.complete_initial _ (ae_iff.mp hG)
  have hgood : MeasurableSet[F 0] {ω | G ω} := by
    simpa only [compl_ofPred, not_not] using hbad.compl
  intro T
  have hcap := hYp.stronglyAdapted.adapted.measurable_capped_jumpProcess_of_cadlag hYc T
  have hGT : MeasurableSet[F T] {ω | G ω} := F.mono bot_le _ hgood
  let : MeasurableSpace Ω := F T
  let κ : Kernel Ω ℝ≥0 := ⟨fun ω ↦ (D.left ω).measure.restrict (Iic T),
    measurable_stieltjesMeasure_restrict_Iic_of_measurable_upTo T
      (fun s hs ↦ (D.left_adapted s).mono (F.mono hs) le_rfl)⟩
  have hκ (ω : Ω) : IsFiniteMeasure (κ ω) := by
    refine ⟨?_⟩
    change ((D.left ω).measure.restrict (Iic T)) univ < ⊤
    rw [Measure.restrict_apply_univ, stieltjesMeasure_Iic_nnreal]
    exact ENNReal.ofReal_lt_top
  let U : Ω → ℝ≥0 → ℝ := fun ω s ↦ if G ω then jumpProcess Y (min s T) ω else 0
  have hU : Measurable (uncurry U) :=
    Measurable.ite (hGT.preimage measurable_fst) hcap measurable_const
  have hUs (ω : Ω) : Summable (fun s : Ioc 0 T ↦ U ω s ^ 2) := by
    by_cases hg : G ω
    · have he (s : Ioc 0 T) : U ω s = jumpProcess Y s ω := by
        simp only [U, if_pos hg, min_eq_left s.2.2]
      simpa only [he] using hg.1 T
    · simp only [U, if_neg hg, zero_pow (by decide : 2 ≠ 0)]
      exact summable_zero
  have hUz (ω : Ω) (s : ℝ≥0) (hs : s ∈ Ioc 0 T) (hz : κ ω {s} = 0) :
      U ω s = 0 := by
    by_cases hg : G ω
    · have hm : κ ω {s} = (D.left ω).measure {s} := by
        change ((D.left ω).measure.restrict (Iic T)) {s} = _
        rw [Measure.restrict_apply (measurableSet_singleton s),
          inter_eq_left.mpr (singleton_subset_iff.mpr (Set.mem_Iic.mpr hs.2))]
      have he : ENNReal.ofReal (jumpProcess Y s ω ^ 2) = 0 :=
        (hg.2 s hs.1).symm.trans (hm.symm.trans hz)
      have hsq : jumpProcess Y s ω ^ 2 = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp he) (sq_nonneg _)
      have hj : jumpProcess Y s ω = 0 := sq_eq_zero_iff.mp hsq
      simp only [U, if_pos hg, min_eq_left hs.2, hj]
    · exact if_neg hg
  have hp := measurable_tprod_exponentialJumpFactor_Ioc_of_kernel_atoms κ hκ T hU hUs hUz
  have he : (fun ω ↦ ∏' s : Ioc 0 T, exponentialJumpFactor (U ω s)) =ᵐ[P]
      stochasticExponentialJumpProduct X T := by
    filter_upwards [hG, hXY.jumpProcess] with ω hg hj
    apply tprod_congr
    intro s
    simp only [U, if_pos hg, min_eq_left s.2.2, ← hj]
  have hc : IsCompleteSubMeasurableSpace P (F T) :=
    fun s hs ↦ F.mono bot_le s (hF.complete_initial s hs)
  exact hc.measurable_congr_ae hp he

theorem IsSemimartingale.adapted_stochasticExponential
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (hX.stochasticExponential hF) := by
  intro t
  exact ((hX.adapted t).sub ((hX.adapted_continuousQuadraticVariation hF t).const_mul
    (1 / 2))).exp.mul (hX.adapted_stochasticExponentialJumpProduct hF t)

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import
  StochLean.Probability.Process.Semimartingale.QuadraticCovariation.IsotropicStochasticIntegral
public import Mathlib.Data.Fin.VecNotation

/-! # Two-coordinate interfaces for isotropic stochastic-integral brackets

These are finite-family specializations of the existing contraction, not new
bracket definitions. Orthogonality is a bracket hypothesis, not an independence
or Brownian-law assumption.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y Q H K L M : ℝ≥0 → Ω → ℝ}

theorem IsSemimartingale.continuousQuadraticCovariation_stochasticIntegral_pair
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P)
    (haL : Adapted F L) (hrL : HasCagladPaths L P)
    (haM : Adapted F M) (hrM : HasCagladPaths M P) :
    let hJ := (hX.isSemimartingale_stochasticIntegral hF haH hrH).add
      (hY.isSemimartingale_stochasticIntegral hF haK hrK)
    let hN := (hX.isSemimartingale_stochasticIntegral hF haL hrL).add
      (hY.isSemimartingale_stochasticIntegral hF haM hrM)
    Indistinguishable (hJ.continuousQuadraticCovariation hN hF)
      (hQ.stochasticIntegral hF
        (fun t ↦ ((haH t).mul (haL t)).add ((haK t).mul (haM t)))
        ((hrH.mul hrL).add (hrK.mul hrM))) P := by
  let Z : Fin 2 → ℝ≥0 → Ω → ℝ := ![X, Y]
  let A : Fin 2 → ℝ≥0 → Ω → ℝ := ![H, K]
  let B : Fin 2 → ℝ≥0 → Ω → ℝ := ![L, M]
  have hZ : ∀ i, IsSemimartingale (Z i) F P := by
    intro i
    fin_cases i
    · exact hX
    · exact hY
  have hd : ∀ i,
      Indistinguishable ((hZ i).continuousQuadraticCovariation (hZ i) hF) Q P := by
    intro i
    fin_cases i
    · exact (hX.continuousQuadraticCovariation_self hF).trans hqX
    · exact (hY.continuousQuadraticCovariation_self hF).trans hqY
  have hz : ∀ i j, i ≠ j →
      Indistinguishable ((hZ i).continuousQuadraticCovariation (hZ j) hF) 0 P := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ho
    · exact (hY.continuousQuadraticCovariation_comm hX hF).trans ho
    · exact (hij rfl).elim
  have haA : ∀ i, Adapted F (A i) := by
    intro i
    fin_cases i
    · exact haH
    · exact haK
  have hrA : ∀ i, HasCagladPaths (A i) P := by
    intro i
    fin_cases i
    · exact hrH
    · exact hrK
  have haB : ∀ i, Adapted F (B i) := by
    intro i
    fin_cases i
    · exact haL
    · exact haM
  have hrB : ∀ i, HasCagladPaths (B i) P := by
    intro i
    fin_cases i
    · exact hrL
    · exact hrM
  have hi := continuousQuadraticCovariation_sum_stochasticIntegral_of_isotropic
    hZ hQ hF hd hz haA hrA haB hrB
  have heJ : (∑ i, (hZ i).stochasticIntegral hF (haA i) (hrA i)) =
      hX.stochasticIntegral hF haH hrH + hY.stochasticIntegral hF haK hrK := by
    simp only [Fin.sum_univ_two, Z, A, Matrix.cons_val_zero, Matrix.cons_val_one]
  have heN : (∑ i, (hZ i).stochasticIntegral hF (haB i) (hrB i)) =
      hX.stochasticIntegral hF haL hrL + hY.stochasticIntegral hF haM hrM := by
    simp only [Fin.sum_univ_two, Z, B, Matrix.cons_val_zero, Matrix.cons_val_one]
  have heHK : (fun t ω ↦ ∑ i, A i t ω * B i t ω) =
      (fun t ω ↦ H t ω * L t ω + K t ω * M t ω) := by
    funext t ω
    simp only [Fin.sum_univ_two, A, B, Matrix.cons_val_zero, Matrix.cons_val_one]
  let hJ := (hX.isSemimartingale_stochasticIntegral hF haH hrH).add
    (hY.isSemimartingale_stochasticIntegral hF haK hrK)
  let hN := (hX.isSemimartingale_stochasticIntegral hF haL hrL).add
    (hY.isSemimartingale_stochasticIntegral hF haM hrM)
  have hb := hJ.continuousQuadraticCovariation_congr hN
    (isSemimartingale_finset_sum univ
      (fun i ↦ (hZ i).isSemimartingale_stochasticIntegral hF (haA i) (hrA i)))
    (isSemimartingale_finset_sum univ
      (fun i ↦ (hZ i).isSemimartingale_stochasticIntegral hF (haB i) (hrB i))) hF
    (Eventually.of_forall fun ω t ↦ congrFun (congrFun heJ.symm t) ω)
    (Eventually.of_forall fun ω t ↦ congrFun (congrFun heN.symm t) ω)
  have hc := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ Finset.measurable_sum univ (fun i _ ↦ (haA i t).mul (haB i t)))
    (HasCagladPaths.finset_sum univ (fun i _ ↦ (hrA i).mul (hrB i)))
    (fun t ↦ ((haH t).mul (haL t)).add ((haK t).mul (haM t)))
    ((hrH.mul hrL).add (hrK.mul hrM))
    (Eventually.of_forall fun ω t ↦ congrFun (congrFun heHK t) ω)
  exact hb.trans (hi.trans hc)

theorem IsSemimartingale.continuousQuadraticVariation_stochasticIntegral_pair
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P)
    (hQ : IsSemimartingale Q F P) (hF : F.IsUsual P)
    (hqX : Indistinguishable (hX.continuousQuadraticVariation hF) Q P)
    (hqY : Indistinguishable (hY.continuousQuadraticVariation hF) Q P)
    (ho : Indistinguishable (hX.continuousQuadraticCovariation hY hF) 0 P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : Adapted F K) (hrK : HasCagladPaths K P) :
    let hJ := (hX.isSemimartingale_stochasticIntegral hF haH hrH).add
      (hY.isSemimartingale_stochasticIntegral hF haK hrK)
    Indistinguishable (hJ.continuousQuadraticVariation hF)
      (hQ.stochasticIntegral (H := fun t ω ↦ H t ω ^ 2 + K t ω ^ 2) hF
        (fun t ↦ ((haH t).pow_const 2).add ((haK t).pow_const 2))
        (by simpa only [pow_two, Pi.mul_def, Pi.add_def]
          using (hrH.mul hrH).add (hrK.mul hrK))) P := by
  let hJ := (hX.isSemimartingale_stochasticIntegral hF haH hrH).add
    (hY.isSemimartingale_stochasticIntegral hF haK hrK)
  have hi := hX.continuousQuadraticCovariation_stochasticIntegral_pair hY hQ hF hqX hqY ho
    haH hrH haK hrK haH hrH haK hrK
  have he := hQ.stochasticIntegral_congr_integrand hF
    (fun t ↦ ((haH t).mul (haH t)).add ((haK t).mul (haK t)))
    ((hrH.mul hrH).add (hrK.mul hrK))
    (fun t ↦ ((haH t).pow_const 2).add ((haK t).pow_const 2))
    (by simpa only [pow_two, Pi.mul_def, Pi.add_def] using (hrH.mul hrH).add (hrK.mul hrK))
    (Eventually.of_forall fun _ _ ↦ by simp only [pow_two, Pi.mul_apply, Pi.add_apply])
  exact (hJ.continuousQuadraticCovariation_self hF).symm.trans (hi.trans he)

end ProbabilityTheory

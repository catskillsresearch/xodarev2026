/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.OneLargeJump
public import StochLean.Probability.Martingale.Doob.ContinuousClassDLocalization
public import StochLean.Probability.Process.Stopping.SingleJumpLocalization

/-! # Continuous Doob decomposition for Class D supermartingales

This is Protter III.10 on its full source domain. No bound on the process
or its jump amplitudes is imposed. Each actual capped norm exit has one
possibly unbounded jump with a proved integrable amplitude. Actual single
jump compensation and the bounded-jump theorem construct its compensator.
Martingale stopping and continuous FV uniqueness prove local consistency;
the Class D localization theorem then constructs and closes the global sum.

The final hypotheses contain no proposed compensator, local decomposition,
consistency condition, terminal variable, or convergence certificate.
Uniqueness is supplied by the existing continuous FV compensator theorem.
The general predictable, possibly discontinuous III.11 theorem is separate.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- The full continuous-compensator Class D theorem, without bounded process
values or bounded jumps. The increasing part and its actual integrable
terminal limit are constructed from the original supermartingale alone. -/
theorem Supermartingale.exists_continuous_doob_decomposition_of_classD
    (hX : Supermartingale X F P) (hXD : IsClassD X F P) (hF : F.IsUsual P)
    (hc : HasCadlagPaths X P) (hJ : HasTotallyInaccessibleJumps F X P)
    (h0 : X 0 =ᵐ[P] 0) :
    ∃ (A : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Adapted F A ∧ IsStronglyPredictable F A ∧ (∀ ω, Continuous (A · ω)) ∧
      A 0 = 0 ∧ HasMonotonePaths A P ∧ HasFiniteVariationPaths A P ∧
      IsClassD A F P ∧ Martingale (X + A) F P ∧ HasCadlagPaths (X + A) P ∧
      UniformIntegrable (X + A) 1 P ∧ Integrable Z P ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω ∧ A t ω ≤ Z ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ A t ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun t : ℝ≥0 ↦ eLpNorm (A t - Z) 1 P) atTop (𝓝 0) := by
  let τ := cappedNormExitSequence X
  have hτ : IsPreLocalizingSequence F τ P :=
    (hX.stronglyAdapted.adapted.isLocalizingSequence_cappedNormExitSequence hF hc).1
  have hlocal (n : ℕ) : ∃ A : ℝ≥0 → Ω → ℝ,
      Adapted F A ∧ (∀ ω, Continuous (A · ω)) ∧ A 0 = 0 ∧ HasMonotonePaths A P ∧
      Martingale (stoppedProcess X (τ n) + A) F P ∧
      HasCadlagPaths (stoppedProcess X (τ n) + A) P := by
    obtain ⟨σ, hσ, hmσ, hiσ, hbound⟩ :=
      hJ.exists_integrable_single_jump_at_norm_exit hXD hX.stronglyAdapted.adapted hF hc h0 n
    have hs := hX.stoppedProcess_of_usual hF hc.hasRightContinuousPaths (hτ.isStoppingTime n)
    have hs0 : stoppedProcess X (τ n) 0 =ᵐ[P] 0 := by
      filter_upwards [h0] with ω hω
      exact (stoppedProcess_eq_of_le (u := X) (τ := τ n)
        (i := (0 : ℝ≥0)) (ω := ω) bot_le).trans hω
    obtain ⟨A, _, ha, _, hAc, hA0, hAm, _, _, hM, hMc, _, _, _, _, _⟩ :=
      hs.exists_continuous_doob_decomposition_of_one_large_jump
        (hXD.stoppedProcess (hτ.isStoppingTime n)) hF (hc.stoppedProcess (τ n))
        (hJ.stoppedProcess hc (τ n)) hs0 hσ hmσ hiσ
        (by positivity : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ)) hbound
    exact ⟨A, ha, hAc, hA0, hAm, hM, hMc⟩
  choose B hBa hBc hB0 hBm hMn hMc using hlocal
  have hcons : ∀ n m, n ≤ m →
      Indistinguishable (stoppedProcess (B m) (τ n)) (B n) P := by
    intro n m hnm
    have hstop := (hMn m).stoppedProcess_of_usual hF (hMc m).hasRightContinuousPaths
      (hτ.isStoppingTime n)
    have hMsmall : Martingale (stoppedProcess X (τ n) + stoppedProcess (B m) (τ n)) F P := by
      have hnmτ : τ n ≤ τ m := monotone_cappedNormExitSequence X hnm
      have he : stoppedProcess (stoppedProcess X (τ m)) (τ n) = stoppedProcess X (τ n) :=
        stoppedProcess_stoppedProcess_of_le_right hnmτ
      simpa only [stoppedProcess_add, he] using hstop
    have hBmc : HasContinuousPaths (B m) P := Eventually.of_forall (hBc m)
    have hs0 : stoppedProcess (B m) (τ n) 0 =ᵐ[P] 0 := by
      refine Eventually.of_forall fun ω ↦ ?_
      exact (stoppedProcess_eq_of_le (u := B m) (τ := τ n)
        (i := (0 : ℝ≥0)) (ω := ω) bot_le).trans (congrFun (hB0 m) ω)
    exact indistinguishable_of_continuous_finiteVariation_martingale_add_zero hF
      hMsmall (hMn n) (hBmc.stoppedProcess (τ n)) (Eventually.of_forall (hBc n))
      ((hBm m).stoppedProcess (τ n)).hasFiniteVariationPaths (hBm n).hasFiniteVariationPaths
      hs0 (Eventually.of_forall fun ω ↦ congrFun (hB0 n) ω)
  exact exists_continuous_doob_decomposition_of_consistent_classD_localization
    hX.stronglyAdapted.adapted hXD hF hc h0 hτ hBa hBc hB0 hBm hMn hcons

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Analysis.PathVariation.QuadraticVariationStieltjes
public import StochLean.Analysis.PathVariation.ContinuousPairBounds
public import StochLean.Analysis.PathVariation.IncreasingIntegral
public import StochLean.ForMathlib.Analysis.DSlopeContinuous

/-! # C1 composition of deterministic quadratic variation: Klenke 21.62

The squared differentiated slope has a continuous diagonal extension. Its
error vanishes against bounded square sums, while the diagonal term converges
to the actual Lebesgue–Stieltjes integral. Only C1, not C2, is required.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean

theorem tendsto_diagonalWeightedQuadraticVariationSum_zero {T : ℝ≥0}
    {π : ℕ → TimePartition T} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2))
    (hdiag : ∀ a, Φ a a = 0)
    (hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    {q : ℝ} (hQ : HasQuadraticVariationAlong π x q) :
    Tendsto (fun n ↦ ∑ i : Fin (π n).size,
      Φ (x ((π n).left i)) (x ((π n).right i)) * ((π n).increment x i) ^ 2)
      atTop (𝓝 0) := by
  let B : ℝ := |q| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : ∀ᶠ n in atTop, quadraticVariationSum (π n) x ≤ B :=
    (hQ.eventually_lt_const (show q < B from
      (le_abs_self _).trans_lt (lt_add_one _))).mono fun _ hn ↦ hn.le
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / (B + 1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := exists_pair_diagonal_modulus_of_continuous hx hΦ hdiag he
  filter_upwards [hm.eventually_lt_const hδ, hb] with n hn hnb
  rw [dist_zero_right]
  calc
    _ ≤ ∑ i : Fin (π n).size,
        ‖Φ (x ((π n).left i)) (x ((π n).right i)) * ((π n).increment x i) ^ 2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin (π n).size, ε / (B + 1) * ((π n).increment x i) ^ 2 := by
      apply sum_le_sum
      intro i _
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply (hmod _ ⟨bot_le, (π n).point_le_horizon _⟩
        _ ⟨bot_le, (π n).point_le_horizon _⟩ _).le
      calc
        _ = ((π n).gap i : ℝ) := by rw [dist_comm]; exact (π n).dist_right_left_eq_gap i
        _ ≤ (π n).mesh := by exact_mod_cast (π n).gap_le_mesh i
        _ < δ := hn
    _ = ε / (B + 1) * quadraticVariationSum (π n) x := (mul_sum ..).symm
    _ ≤ ε / (B + 1) * B := mul_le_mul_of_nonneg_left hnb he.le
    _ < ε / (B + 1) * (B + 1) := mul_lt_mul_of_pos_left (lt_add_one B) he
    _ = ε := div_mul_cancel₀ _ (by linarith)

theorem hasQuadraticVariationAlong_contDiff_of_stieltjes
    {π : ℕ → LocallyFinitePartition} {T : ℝ≥0} {x A : ℝ≥0 → ℝ}
    (hx : ContinuousOn x (Icc 0 T))
    (hm : Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hQ : ∀ s ≤ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict s) x (A s))
    {hv : LocallyBoundedVariationOn A univ} {hr : ∀ t, ContinuousWithinAt A (Ici t) t}
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) (f ∘ x)
      (pathStieltjesIntegral A hv hr (fun t ↦ deriv f (x t) ^ 2) T) := by
  let Φ : ℝ → ℝ → ℝ := fun a b ↦ dslope f a b ^ 2 - deriv f b ^ 2
  have hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2) :=
    ((continuous_dslope_of_contDiff hf).pow 2).sub
      ((hf.continuous_deriv_one.comp continuous_snd).pow 2)
  have hdiag (a : ℝ) : Φ a a = 0 := by simp only [Φ, dslope_same, sub_self]
  have he := tendsto_diagonalWeightedQuadraticVariationSum_zero hx hΦ hdiag hm (hQ T le_rfl)
  have hw := tendsto_weightedQuadraticVariationSum_right (hv := hv) (hr := hr)
    (f := fun t ↦ deriv f (x t) ^ 2) hx hm hQ
    ((hf.continuous_deriv_one.comp_continuousOn hx).pow 2)
  have hsum (n : ℕ) :
      (∑ i : Fin ((π n).restrict T).size,
        deriv f (x (((π n).restrict T).right i)) ^ 2 * (((π n).restrict T).increment x i) ^ 2) +
      (∑ i : Fin ((π n).restrict T).size,
        Φ (x (((π n).restrict T).left i)) (x (((π n).restrict T).right i)) *
          (((π n).restrict T).increment x i) ^ 2) =
      quadraticVariationSum ((π n).restrict T) (f ∘ x) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have hd : dslope f (x (((π n).restrict T).left i))
        (x (((π n).restrict T).right i)) * (((π n).restrict T).increment x i) =
          (((π n).restrict T).increment (f ∘ x) i) := by
      simpa only [TimePartition.increment, Function.comp_def, smul_eq_mul, mul_comm] using
        sub_smul_dslope f (x (((π n).restrict T).left i)) (x (((π n).restrict T).right i))
    rw [← hd]
    dsimp only [Φ]
    ring
  simpa only [HasQuadraticVariationAlong, add_zero] using (hw.add he).congr hsum

theorem continuous_pathStieltjesIntegral_of_continuous {x f : ℝ≥0 → ℝ}
    {hv : LocallyBoundedVariationOn x univ} {hr : ∀ t, ContinuousWithinAt x (Ici t) t}
    (hx : Continuous x) (hf : Continuous f) :
    Continuous (pathStieltjesIntegral x hv hr f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let π : ℕ → TimePartition (t + 1) :=
    fun n ↦ (LocallyFinitePartition.dyadic n).restrict (t + 1)
  have hm : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp
      (LocallyFinitePartition.dyadic_admissible.restrict_mesh_tendsto (fun _ ↦ t + 1))
  have hs (n : ℕ) : Continuous (stieltjesLeftSum (π n) x f) := by
    unfold stieltjesLeftSum
    fun_prop
  have hc : ContinuousOn (pathStieltjesIntegral x hv hr f) (Icc 0 (t + 1)) :=
    (tendstoUniformlyOn_stieltjesLeftSum (x := x) (hx := hv) (hr := hr)
      hf.continuousOn hm).continuousOn (Eventually.of_forall
        (fun n ↦ (hs n).continuousOn)).frequently
  apply (hc t ⟨bot_le, (lt_add_one t).le⟩).continuousAt
  change Icc (⊥ : ℝ≥0) (t + 1) ∈ 𝓝 t
  rw [Set.Icc_bot]
  exact Iic_mem_nhds (lt_add_one t)

/-- C1 closure, with the continuous increasing limit explicitly equal to the
actual Stieltjes integral. Mesh convergence suffices; source admissibility is stronger. -/
theorem contDiff_quadraticVariation_restrict {π : ℕ → LocallyFinitePartition}
    {x A : ℝ≥0 → ℝ} (hx : Continuous x) (hA : Continuous A)
    (hm : ∀ T, Tendsto (fun n ↦ (((π n).restrict T).mesh : ℝ)) atTop (𝓝 0))
    (hQ : ∀ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) x (A T))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    let hv := locallyBoundedVariationOn_quadraticVariation_restrict_limit hx hm hQ
    let B := pathStieltjesIntegral A hv (fun _ ↦ hA.continuousWithinAt)
      (fun t ↦ deriv f (x t) ^ 2)
    Continuous (f ∘ x) ∧ Continuous B ∧ B 0 = 0 ∧ Monotone B ∧
      ∀ T, HasQuadraticVariationAlong (fun n ↦ (π n).restrict T) (f ∘ x) (B T) := by
  dsimp only
  have hw : Continuous (fun t ↦ deriv f (x t) ^ 2) := (hf.continuous_deriv_one.comp hx).pow 2
  refine ⟨hf.continuous.comp hx, continuous_pathStieltjesIntegral_of_continuous hA hw, ?_, ?_, ?_⟩
  · rw [pathStieltjesIntegral_zero, quadraticVariation_restrict_limit_zero hQ, mul_zero]
  · exact monotone_pathStieltjesIntegral_of_nonneg
      (monotone_quadraticVariation_restrict_limit hx hm hQ) _ _
      (fun _ ↦ integrableOn_variationStieltjes_of_continuousOn hw.continuousOn)
      (fun _ ↦ sq_nonneg _)
  · intro T
    exact hasQuadraticVariationAlong_contDiff_of_stieltjes hx.continuousOn (hm T)
      (fun s _ ↦ hQ s) hf

end StochLean

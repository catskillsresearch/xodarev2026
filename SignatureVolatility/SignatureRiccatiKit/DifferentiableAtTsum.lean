module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.DiffContOnCl

/-!
# C3a. A locally uniformly convergent series of entire functions is entire
-/

@[expose] public section

noncomputable section

open Complex Filter Topology MeasureTheory Metric Set
open scoped ENNReal NNReal Interval

namespace SignatureVolatility

/-- On each ball `Metric.ball z₀ 1`, a summable majorant of the form
`C exp ‖z‖` is z-independent, so the tsum is differentiable at `z₀`. -/
lemma differentiableAt_tsum_of_locallyUniform (term : ℕ → ℂ → ℂ)
    (hterm : ∀ n, Differentiable ℂ (term n)) {C : ℝ}
    (hbound : ∀ z : ℂ, Summable (fun n : ℕ => ‖term n z‖) ∧
      ∑' n : ℕ, ‖term n z‖ ≤ C * Real.exp ‖z‖)
    (z₀ : ℂ) :
    DifferentiableAt ℂ (fun z => ∑' n : ℕ, term n z) z₀ := by
  let G : ℂ → ℂ := fun z => ∑' n : ℕ, term n z
  let S : ℕ → ℂ → ℂ := fun N z => ∑ n ∈ Finset.range N, term n z
  have hS_diff : ∀ N, Differentiable ℂ (S N) := fun N =>
    Differentiable.fun_sum fun n _ => hterm n
  have hS_tendsto : ∀ z, Tendsto (fun N => S N z) atTop (𝓝 (G z)) := fun z =>
    (hbound z).1.of_norm.hasSum.tendsto_sum_nat
  have hS_norm : ∀ N z, ‖S N z‖ ≤ C * Real.exp ‖z‖ := fun N z =>
    (norm_sum_le _ _).trans <|
      ((hbound z).1.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)).trans (hbound z).2
  have hG_norm : ∀ z, ‖G z‖ ≤ C * Real.exp ‖z‖ := fun z =>
    (norm_tsum_le_tsum_norm (hbound z).1).trans (hbound z).2
  have hC0 : 0 ≤ C := by
    have h0 := (hbound 0).2
    have hnn : 0 ≤ ∑' n, ‖term n 0‖ := tsum_nonneg fun _ => norm_nonneg _
    simp only [norm_zero, Real.exp_zero, mul_one] at h0
    linarith
  set M : ℝ := C * Real.exp (‖z₀‖ + 2)
  have hnorm_on_circle : ∀ w : ℂ, ‖w - z₀‖ = 2 → ‖w‖ ≤ ‖z₀‖ + 2 := fun w hw => by
    calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by ring_nf
      _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
      _ = ‖z₀‖ + 2 := by rw [hw]
  have hM_S : ∀ (N : ℕ) (w : ℂ), ‖w - z₀‖ = 2 → ‖S N w‖ ≤ M := fun N w hw =>
    (hS_norm N w).trans <| mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hnorm_on_circle w hw)) hC0
  have hM_G : ∀ w : ℂ, ‖w - z₀‖ = 2 → ‖G w‖ ≤ M := fun w hw =>
    (hG_norm w).trans <| mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hnorm_on_circle w hw)) hC0
  have hmap_dist : ∀ θ : ℝ, ‖circleMap z₀ 2 θ - z₀‖ = 2 := fun θ => by
    simp [circleMap]
  have hdist_z : ∀ {z : ℂ} (_hz : z ∈ ball z₀ 1) (θ : ℝ), 1 ≤ ‖circleMap z₀ 2 θ - z‖ :=
    fun {z} hz θ => by
      have h2 : ‖z - z₀‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
      have htri : ‖circleMap z₀ 2 θ - z₀‖ - ‖z - z₀‖ ≤
          ‖(circleMap z₀ 2 θ - z₀) - (z - z₀)‖ := norm_sub_norm_le _ _
      rw [show (circleMap z₀ 2 θ - z₀) - (z - z₀) = circleMap z₀ 2 θ - z by ring] at htri
      have : (2 : ℝ) - ‖z - z₀‖ ≤ ‖circleMap z₀ 2 θ - z‖ := by
        simpa [hmap_dist θ] using htri
      linarith
  have hderiv_cont : Continuous fun θ : ℝ => deriv (circleMap z₀ 2) θ := by
    simp only [funext (deriv_circleMap z₀ 2)]
    exact (continuous_circleMap 0 2).mul continuous_const
  -- Cauchy's formula for the partial sums, in Mathlib's `(2πI) • f z = ∮` form
  have hSN : ∀ (N : ℕ) {z : ℂ} (hz : z ∈ ball z₀ 2),
      (2 * Real.pi * Complex.I : ℂ) • S N z =
        ∮ w in C(z₀, 2), (w - z)⁻¹ • S N w := fun N _ hz =>
    ((hS_diff N).diffContOnCl.circleIntegral_sub_inv_smul hz).symm
  -- The Cauchy integrals of `S N` converge to that of `G` by dominated convergence
  have hlim_int : ∀ {z : ℂ} (hz : z ∈ ball z₀ 1),
      Tendsto (fun N : ℕ => ∮ w in C(z₀, 2), (w - z)⁻¹ • S N w) atTop
        (𝓝 (∮ w in C(z₀, 2), (w - z)⁻¹ • G w)) := by
    intro z hz
    have hz2 : z ∈ ball z₀ 2 := ball_subset_ball (by norm_num) hz
    simp only [circleIntegral]
    simp_rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine (tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioc 0 (2 * Real.pi)))
      (bound := fun _ => (2 : ℝ) * M)
      (F := fun N θ =>
        deriv (circleMap z₀ 2) θ • (circleMap z₀ 2 θ - z)⁻¹ • S N (circleMap z₀ 2 θ))
      (f := fun θ =>
        deriv (circleMap z₀ 2) θ • (circleMap z₀ 2 θ - z)⁻¹ • G (circleMap z₀ 2 θ))
      ?_ ?_ ?_ ?_)
    · intro N
      have hinvc : Continuous fun θ : ℝ => (circleMap z₀ 2 θ - z)⁻¹ := by
        refine Continuous.inv₀
            ((continuous_circleMap z₀ 2).sub (continuous_const : Continuous fun _ : ℝ => z))
            fun θ => ?_
        have hle : 1 ≤ ‖circleMap z₀ 2 θ - z‖ := hdist_z hz θ
        exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hle))
      have hleft : Continuous fun θ : ℝ =>
          deriv (circleMap z₀ 2) θ • (circleMap z₀ 2 θ - z)⁻¹ :=
        hderiv_cont.smul hinvc
      have hπ : Continuous fun θ : ℝ =>
          deriv (circleMap z₀ 2) θ • (circleMap z₀ 2 θ - z)⁻¹ •
            S N (circleMap z₀ 2 θ) := by
        have h := hleft.smul ((hS_diff N).continuous.comp (continuous_circleMap z₀ 2))
        convert h using 1
        ext θ
        simp [deriv_circleMap, mul_assoc]
      exact hπ.aestronglyMeasurable
    · exact intervalIntegrable_const.1
    · intro N
      filter_upwards with θ
      have hd : 1 ≤ ‖circleMap z₀ 2 θ - z‖ := hdist_z hz θ
      rw [norm_smul, norm_smul, norm_inv, deriv_circleMap, norm_mul, norm_circleMap_zero,
        Complex.norm_I, mul_one, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hinv : ‖circleMap z₀ 2 θ - z‖⁻¹ ≤ (1 : ℝ) := by
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hd
      have hSb : ‖S N (circleMap z₀ 2 θ)‖ ≤ M := hM_S N _ (hmap_dist θ)
      have hnnM : 0 ≤ M := mul_nonneg hC0 (Real.exp_nonneg _)
      calc 2 * (‖circleMap z₀ 2 θ - z‖⁻¹ * ‖S N (circleMap z₀ 2 θ)‖)
          ≤ 2 * (1 * M) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hinv hSb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)) (by norm_num)
        _ = 2 * M := by ring
    · filter_upwards with θ
      exact tendsto_const_nhds.smul (tendsto_const_nhds.smul (hS_tendsto _))
  have hG_cauchy : ∀ z ∈ ball z₀ 1,
      G z = (2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(z₀, 2), (w - z)⁻¹ • G w := by
    intro z hz
    have hz2 : z ∈ ball z₀ 2 := ball_subset_ball (by norm_num) hz
    have hlim_lhs : Tendsto (fun N : ℕ => (2 * Real.pi * Complex.I : ℂ) • S N z) atTop
        (𝓝 ((2 * Real.pi * Complex.I : ℂ) • G z)) :=
      tendsto_const_nhds.smul (hS_tendsto z)
    have hlim_rhs := hlim_int hz
    have heq : (2 * Real.pi * Complex.I : ℂ) • G z =
        ∮ w in C(z₀, 2), (w - z)⁻¹ • G w :=
      tendsto_nhds_unique (hlim_lhs.congr fun N => hSN N hz2) hlim_rhs
    have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    calc G z
        = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • G z) :=
          (inv_smul_smul₀ hI _).symm
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(z₀, 2), (w - z)⁻¹ • G w := by
          rw [heq]
  -- `G` is circle-integrable as a bounded measurable limit of continuous functions
  have hG_int : CircleIntegrable G z₀ 2 := by
    rw [circleIntegrable_def]
    have hmeas : AEStronglyMeasurable (fun θ => G (circleMap z₀ 2 θ))
        (volume.restrict (uIoc 0 (2 * Real.pi))) :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun N => ((hS_diff N).continuous.comp (continuous_circleMap z₀ 2)).aestronglyMeasurable)
        (ae_of_all _ fun θ => hS_tendsto _)
    exact IntervalIntegrable.mono_fun' (f := fun θ => G (circleMap z₀ 2 θ))
      (g := fun _ : ℝ => M) intervalIntegrable_const hmeas
      (ae_of_all _ fun θ => hM_G _ (hmap_dist θ))
  have hps := hasFPowerSeriesOn_cauchy_integral (R := 2) hG_int
      (by norm_num : (0 : ℝ≥0) < 2)
  have hC_at : DifferentiableAt ℂ
      (fun z => (2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(z₀, 2), (w - z)⁻¹ • G w) z₀ :=
    hps.differentiableOn.differentiableAt (by
      rw [Metric.eball_coe (x := z₀) (ε := (2 : ℝ≥0))]
      exact ball_mem_nhds z₀ (by norm_num))
  exact hC_at.congr_of_eventuallyEq
    (eventually_of_mem (ball_mem_nhds z₀ zero_lt_one) hG_cauchy)

end SignatureVolatility

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousClosure
public import StochLean.Probability.Martingale.Inequalities.DoobGlobalL2
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableOperations

/-! # An actual L2 closing variable for continuous-time martingales

Discrete convergence constructs the closing variable. A global L2 envelope
gives uniform integrability in L2, hence integer-time L2 convergence and
convergence of second moments. The tower property closes every real-time
coordinate. Integer-time almost-sure convergence is stated as such; no
whole-half-line almost-sure convergence is inferred from it here.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem exists_memLp_two_closing_of_globalEnvelope (hX : Martingale X F P)
    {g : Ω → ℝ} (hg : MemLp g 2 P) (hb : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ g ω) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 2 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧ (∀ᵐ ω ∂P, ‖Z ω‖ ≤ g ω) := by
  have hmeas (t : ℝ≥0) : AEStronglyMeasurable (X t) P :=
    ((hX.stronglyAdapted t).mono (F.le t)).aestronglyMeasurable
  have hdom (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖X t ω‖ ≤ ‖g ω‖ :=
    hb.mono fun ω hω ↦ (hω t).trans (le_abs_self _)
  have hu1 : UniformIntegrable X 1 P :=
    (uniformIntegrable_const le_rfl (by simp)
      (hg.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))).mono_norm hmeas hdom
  have hu2 : UniformIntegrable X 2 P :=
    (uniformIntegrable_const (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hg).mono_norm
      hmeas hdom
  let e : ℕ → ℝ≥0 := Nat.cast
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hm : Martingale (fun n ↦ X (e n)) G P := hX.reindex e he
  let Z := G.limitProcess (fun n ↦ X (e n)) P
  have hu1n := hu1.reindex e
  have hu2n := hu2.reindex e
  obtain ⟨C, hC⟩ := hu1n.2.2
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 (Z ω)) :=
    hm.submartingale.ae_tendsto_limitProcess hC
  have hZ : MemLp Z 2 P := hu2n.memLp_of_ae_tendsto hlim
  refine ⟨Z, hZ, hlim, ?_, ?_, ?_⟩
  · exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      (fun n ↦ hmeas (e n)) hZ hu2n.2.1 hlim
  · intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hmZ : X (e n) =ᵐ[P] P[Z | F (e n)] := hm.ae_eq_condExp_limitProcess hu1n n
    exact (hX.condExp_ae_eq hn).symm.trans ((condExp_congr_ae hmZ).trans
      (condExp_condExp_of_le (F.mono hn) (F.le (e n))))
  · filter_upwards [hlim, hb] with ω hω hbω
    exact le_of_tendsto' hω.norm (fun n ↦ hbω (e n))

/-- The second moments converge to that of the actual closing variable.
The pathwise and L2 convergence assertions here are explicitly integer-time. -/
theorem exists_memLp_two_closing_and_second_moment_limit
    (hX : Martingale X F P) (hc : HasRightContinuousPaths X P)
    (hL : ∀ t, MemLp (X t) 2 P) {C : ℝ} (hb : ∀ t, (∫ ω, X t ω ^ 2 ∂P) ≤ C) :
    ∃ Z : Ω → ℝ, MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 2 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) ∧
      Tendsto (fun n : ℕ ↦ ∫ ω, X (n : ℝ≥0) ω ^ 2 ∂P) atTop
        (𝓝 (∫ ω, Z ω ^ 2 ∂P)) ∧ (∫ ω, Z ω ^ 2 ∂P) ≤ C := by
  obtain ⟨g, _, _, hg, hbg, _⟩ := hX.exists_memLp_two_globalEnvelope hc hL
    (by simpa only [Real.norm_eq_abs, sq_abs] using hb)
  obtain ⟨Z, hZ, hlim, hLp, hclose, _⟩ := hX.exists_memLp_two_closing_of_globalEnvelope hg hbg
  have hE : Tendsto (fun n : ℕ ↦ ∫ ω, X (n : ℝ≥0) ω ^ 2 ∂P) atTop
      (𝓝 (∫ ω, Z ω ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω ↦ g ω ^ 2)
      (fun n ↦ show AEStronglyMeasurable (fun ω ↦ X (n : ℝ≥0) ω ^ 2) P from
        (hL (n : ℝ≥0)).aestronglyMeasurable.pow 2) hg.integrable_sq
    · intro n
      filter_upwards [hbg] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hω (n : ℝ≥0)))).mpr
        (hω (n : ℝ≥0))
      simpa only [Real.norm_eq_abs, sq_abs] using h
    · exact hlim.mono fun _ hω ↦ hω.pow 2
  exact ⟨Z, hZ, hlim, hLp, hclose, hE, le_of_tendsto' hE (fun n ↦ hb (n : ℝ≥0))⟩

end MeasureTheory.Martingale

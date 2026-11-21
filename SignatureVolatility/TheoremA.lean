import SignatureVolatility.ItoCalculusKit
import SignatureVolatility.Preliminaries
import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
import SignatureVolatility.SignaturePriceSolution
import SignatureVolatility.SignatureVolatilityModel
import SignatureVolatility.SignatureVolatilityModel.Sigma

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

theorem theorem_A {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (M : SignatureVolatilityModel) (setup : ProlongedBrownianSetup Ω ℙ M.d M.T)
    (ito : ItoCalculusKit Ω ℙ M.d M.T setup) :
    ∃ (sol : SignaturePriceSolution M setup ito),
      ∀ (S_tilde : ℝ → Ω → ℝ),
        (∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
          S_tilde t ω = M.s₀ + ito.itoInt (fun s ω' => S_tilde s ω' *
              SignatureVolatilityModel.sigma M setup s ω') t ω) →
        ∀ᵐ ω ∂ℙ, ∀ t ∈ Icc 0 M.T, S_tilde t ω = sol.S t ω := by
  obtain ⟨hmart, hsup, hquad⟩ :=
    ito.novikov_doob_l2_martingale M.w M.h2 M.ℓ M.h1 M.s₀ M.hs₀
  let σ : ℝ → Ω → ℝ := SignatureVolatilityModel.sigma M setup
  let S : ℝ → Ω → ℝ := fun t ω => M.s₀ * ito.doleansExp σ t ω
  have hS_zero : ∀ ω, S 0 ω = M.s₀ := by
    intro ω
    simp [S, ito.doleansExp_def, ito.itoInt_zero, ito.quadVar_zero]
  have hS_meas : ∀ t, Measurable (S t) := by
    intro t
    have heq : S t = fun ω => M.s₀ * Real.exp (ito.itoInt σ t ω - (1 / 2 : ℝ) * ito.quadVar σ t ω) := by
      ext ω; simp [S, ito.doleansExp_def]
    rw [heq]
    exact measurable_const.mul
      (Real.measurable_exp.comp ((ito.itoInt_meas σ t).sub (measurable_const.mul (ito.quadVar_meas σ t))))
  have hS_adapt : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
      Measurable[setup.signatureFiltration.σAlg t] (S s.1) := by
    intro t s
    have heq : S s.1 =
        fun ω => M.s₀ * Real.exp (ito.itoInt σ s.1 ω - (1 / 2 : ℝ) * ito.quadVar σ s.1 ω) := by
      ext ω; simp [S, ito.doleansExp_def]
    rw [heq]
    exact measurable_const.mul
      (Real.measurable_exp.comp
        ((ito.itoInt_adapted σ t s).sub (measurable_const.mul (ito.quadVar_adapted σ t s))))
  have hS_pos : ∀ t ω, 0 < S t ω := by
    intro t ω
    simp only [S, ito.doleansExp_def]
    exact mul_pos M.hs₀ (Real.exp_pos _)
  have hsde : ∀ t ∈ Icc 0 M.T, ∀ᵐ ω ∂ℙ,
      S t ω = M.s₀ + ito.itoInt (fun s ω' => S s ω' * σ s ω') t ω :=
    ito.doleans_sde M.s₀ σ hquad
  let sol : SignaturePriceSolution M setup ito :=
    { S := S
      S_zero := hS_zero
      S_meas := hS_meas
      S_adapted := hS_adapt
      S_strictly_pos := hS_pos
      doleans_repr := fun t ω => by
        simpa [S, ito.doleansExp_def, σ] using rfl
      solves_sde := hsde
      sup_l2_integrable := hsup
      is_martingale := hmart }
  refine ⟨sol, fun S_tilde hS_tilde => ?_⟩
  obtain ⟨f, hf_cont, hf_nonneg, hf_bound, hexhaust⟩ :=
    ito.stopped_l2_localisation M.w M.ℓ M.s₀ S_tilde S hS_tilde hsde
  apply hexhaust
  intro k t ht
  exact gronwall_zero_of_continuousOn M.hT.le (sq_nonneg _)
    (hf_cont k) (hf_nonneg k) (hf_bound k) t ht

end SignatureVolatility
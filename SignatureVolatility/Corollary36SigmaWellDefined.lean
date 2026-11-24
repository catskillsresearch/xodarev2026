module

public import SignatureVolatility.DualPairingLeNormWDualMulNormW
public import SignatureVolatility.Lemma32SignatureInTw
public import SignatureVolatility.MemTwDualOfMemL2w
public import SignatureVolatility.SignatureVolatilityModel.Sigma


@[expose] public section


open MeasureTheory

namespace SignatureVolatility

theorem corollary_3_6_sigma_well_defined {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] (M : SignatureVolatilityModel)
    (setup : ProlongedBrownianSetup Ω ℙ M.d M.T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ M.T) :
    (∀ᵐ ω ∂ℙ, |SignatureVolatilityModel.sigma M setup t ω| ≤
        norm2w M.w M.ℓ * normW M.w (setup.W_hat t ω)) ∧
      Integrable (fun ω => (normW M.w (setup.W_hat t ω)) ^ (2 : ℝ)) ℙ := by
  obtain ⟨hTw, hint2⟩ := lemma_3_2_signature_in_Tw setup M.h2 (by norm_num : (1 : ℝ) ≤ 2) ht0 htT
  obtain ⟨hDual, hDual_le⟩ := memTwDual_of_memL2w M.w M.h1.mem_l2w
  refine ⟨hTw.mono fun ω hω => ?_, hint2⟩
  dsimp [SignatureVolatilityModel.sigma]
  have hpair := (dualPairing_le_normWDual_mul_normW M.w hDual hω).2
  exact hpair.trans (mul_le_mul_of_nonneg_right hDual_le (normW.nonneg M.w _))

end SignatureVolatility

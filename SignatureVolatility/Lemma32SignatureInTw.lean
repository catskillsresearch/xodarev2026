module

public import SignatureVolatility.HypH2
public import SignatureVolatility.MemTw
public import SignatureVolatility.NormW
public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.WHat
public import SignatureVolatility.Weight


@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

theorem lemma_3_2_signature_in_Tw {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {d : ℕ} {T : ℝ}
    (setup : ProlongedBrownianSetup Ω ℙ d T) {w : Weight} (hw : HypH2 w)
    {p : ℝ} (hp : 1 ≤ p) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    (∀ ω, MemTw w (setup.W_hat t ω)) ∧
      Integrable (fun ω => (normW w (setup.W_hat t ω)) ^ p) ℙ := by
  obtain ⟨C_p, R_p, _, hRp, hctrl⟩ := setup.factorial_moment_control p hp
  have hsum : Summable (fun n : ℕ => w n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) := by
    have hrew : (fun n : ℕ => w n * (C_p * (R_p ^ n / (n.factorial : ℝ)))) =
        fun n : ℕ => C_p * (w n * (R_p ^ n / (n.factorial : ℝ))) := by
      ext n; ring
    rw [hrew]
    exact (hw.subfactorial_nonneg hRp).mul_left C_p
  obtain ⟨hmem, hint, _⟩ := hctrl w (fun n => (w.pos n).le) hsum ht0 htT
  exact ⟨hmem, hint⟩

end SignatureVolatility

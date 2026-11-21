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
  obtain ⟨r, hr⟩ := hw.le_geometric
  obtain ⟨hmem, hint⟩ :=
    setup.factorial_moment_control p hp w (fun n => (w.pos n).le) ⟨r, hr⟩ ht0 htT
  exact ⟨hmem, hint⟩

end SignatureVolatility

import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ProlongedBrownianSetup.WHat
import SignatureVolatility.GeneratedFiltration
import SignatureVolatility.IndexedFiltration
import SignatureVolatility.PriceFiltration


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace ProlongedBrownianSetup

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

def signatureFiltration (setup : ProlongedBrownianSetup Ω ℙ d T) : IndexedFiltration Ω :=
  generatedFiltration (fun u I ω => (setup.W_hat u ω).coeff I) (setup.sig_meas 0)

namespace signatureFiltration

lemma priceFiltration_le {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {d : ℕ} {T : ℝ}
    (setup : ProlongedBrownianSetup Ω ℙ d T) (S : ℝ → Ω → ℝ)
    (hS_meas : ∀ t, Measurable (S t))
    (hS_adapt : ∀ t (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}),
      Measurable[setup.signatureFiltration.σAlg t] (S s.1)) (t : ℝ) :
    (priceFiltration S hS_meas).σAlg t ≤ setup.signatureFiltration.σAlg t :=
  iSup_le fun s => iSup_le fun _ => (hS_adapt t s).comap_le

/-! ## Section 2.5: Signature Cumulant / Affine Riccati Operator `ℛ` -/

end signatureFiltration

end ProlongedBrownianSetup

end SignatureVolatility

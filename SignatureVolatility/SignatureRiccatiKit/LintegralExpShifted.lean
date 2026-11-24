module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.ItoCalculusKit.ExpSupermartingale

/-!
# B1a. `E exp(Φ(x,s)) ≤ 1` by the existing Doléans bound, with `H_r = (x + W_r)²`
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Exact copy of the Pillar A bound, with the integrand shifted by `x`. -/
lemma lintegral_exp_shiftedExponent_le_one {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s x ω)) ∂P ≤ 1 := by
  sorry

end SignatureVolatility

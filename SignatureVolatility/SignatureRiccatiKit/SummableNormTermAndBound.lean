module

public import SignatureVolatility.SignatureRiccatiKit.CondSigPoly
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# C1b. Contraction-preimage bound: `∑_I ‖P_{I,t}(z)‖` is of exponential type `≤ 1`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grouping contractions by the target word `J ∈ {0, l₁}^m` gives
`∑_n ∑_{|I|=n} ‖condSigPoly I t z‖ ≤ 2 exp(((3+d)/2) t) exp ‖z‖`,
and hence summability of the `φ`-weighted level sums. -/
lemma summable_norm_term_and_bound {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t)
    {phi : ExtTensorAlgebra (d + 1)} {K : ℝ}
    (hcoeff : ∀ I : Word (d + 1), |phi.coeff I| ≤ K)
    (hG_mgf : ∫ y : ℝ, Real.exp (Real.sqrt t * |y|) ∂(gaussianReal 0 1) ≤
      2 * Real.exp (t / 2))
    (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖∑ I ∈ wordsOfLength (d + 1) n, (phi.coeff I : ℂ) * condSigPoly hd t I z‖) ∧
      ∑' n : ℕ,
          ‖∑ I ∈ wordsOfLength (d + 1) n,
            (phi.coeff I : ℂ) * condSigPoly hd t I z‖ ≤
        (K * (2 * Real.exp (((3 + (d : ℝ)) / 2) * t))) * Real.exp ‖z‖ := by
  sorry

end SignatureVolatility

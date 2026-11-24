module

public import SignatureVolatility.SignatureRiccatiKit.ComplexTilt
public import SignatureVolatility.SignatureRiccatiKit.FawcettHermite
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion

/-!
# Conditional signature polynomial `P_{I,t}` via contractions and Hermite polynomials
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Reuse the monic Hermite core from C1. -/
abbrev hermitePoly (k : ℕ) (t : ℝ) (z : ℂ) : ℂ := monicHermite k t z

/-- Exact conditional-expectation polynomial `P_{I,t}(z)` for word `I`,
summing Carbon's contraction list of `I.reverse`. -/
noncomputable def condSigPoly {d : ℕ} (hd : 0 < d) (t : ℝ)
    (I : Word (d + 1)) (z : ℂ) : ℂ :=
  ((contractions I.reverse).map fun p =>
    if onlyZeroOrOne hd p.2 then
      (p.1 : ℂ) *
        ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) *
        hermitePoly (countOnes hd p.2) t z
    else 0).sum

lemma differentiable_condSigPoly {d : ℕ} (hd : 0 < d) (t : ℝ)
    (I : Word (d + 1)) :
    Differentiable ℂ (condSigPoly hd t I) := by
  unfold condSigPoly hermitePoly
  induction contractions I.reverse with
  | nil => simpa using differentiable_const (0 : ℂ)
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Differentiable.add ?_ ih
    split_ifs
    · exact ((differentiable_const _).mul (differentiable_const _)).mul
        (monicHermite_differentiable _ t)
    · exact differentiable_const 0

end SignatureVolatility

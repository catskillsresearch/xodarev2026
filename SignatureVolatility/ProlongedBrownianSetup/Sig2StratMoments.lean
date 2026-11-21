module

public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.ProlongedBrownianSetup.Sig2Strat


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Appendix A / Proposition `prop:signature-moment` for `sig2Strat`

Factorial decay of Brownian Stratonovich iterated integrals against geometric weights
`w_n ≤ r^n`, supplying `ProlongedBrownianSetup.factorial_moment_control`.

**Status: HOLE.** Needs word-level `L^p` bounds
`(𝔼|⟨e_I, 𝒲_t⟩|^p)^{1/p} ≲ C^{|I|} / ((|I|/2)!)^{1/2}` (Friz–Victoir / Friz–Hairer).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Pathwise summability + `L^p` integrability of the weighted level series of `sig2Strat 0 t`. -/
lemma sig2Strat_factorial_moment_control (B : MultiBrownian Ω P d) {T : ℝ} (_hT : 0 < T)
    (p : ℝ) (_hp : 1 ≤ p) (w_fn : ℕ → ℝ) (_hw0 : ∀ n, 0 ≤ w_fn n)
    (_hgeom : ∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n)
    ⦃t : ℝ⦄ (_ht0 : 0 ≤ t) (_htT : t ≤ T) :
    (∀ ω, Summable (fun n : ℕ => w_fn n * (sig2Strat B 0 t ω).levelNorm n)) ∧
      Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2Strat B 0 t ω).levelNorm n) ^ p) P := by
  -- Appendix A factorial decay ⇒ geometric weights summable; Minkowski for `L^p`.
  sorry

end SignatureVolatility

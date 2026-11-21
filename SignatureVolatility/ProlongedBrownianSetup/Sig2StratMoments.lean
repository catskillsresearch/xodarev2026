module

public import SignatureVolatility.ProlongedBrownianSetup.Sig2Strat


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Appendix A / Proposition `prop:signature-moment` for `sig2Strat`

Geometric-weight factorial moment control for `sig2Strat` (`w_n ≤ r^n`), supplying
`ProlongedBrownianSetup.factorial_moment_control`. Reduces to the chordal
`sig2OfBrownian_geometric_moment_control` because `sig2Strat := sig2OfBrownian`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Pathwise summability + `L^p` integrability of the weighted level series of `sig2Strat 0 t`. -/
lemma sig2Strat_factorial_moment_control (B : MultiBrownian Ω P d) {T : ℝ} (_hT : 0 < T)
    (p : ℝ) (_hp : 1 ≤ p) (w_fn : ℕ → ℝ) (_hw0 : ∀ n, 0 ≤ w_fn n)
    (_hgeom : ∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n)
    ⦃t : ℝ⦄ (_ht0 : 0 ≤ t) (_htT : t ≤ T) :
    (∀ ω, Summable (fun n : ℕ => w_fn n * (sig2Strat B 0 t ω).levelNorm n)) ∧
      Integrable (fun ω => (∑' n : ℕ, w_fn n * (sig2Strat B 0 t ω).levelNorm n) ^ p) P := by
  obtain ⟨r, hwr⟩ := _hgeom
  simpa [sig2Strat] using
    sig2OfBrownian_geometric_moment_control B (zero_le_one.trans _hp) _hw0 hwr t

end SignatureVolatility

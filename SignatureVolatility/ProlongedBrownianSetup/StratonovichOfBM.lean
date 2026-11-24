module

public import SignatureVolatility.ProlongedBrownianSetup.PaperSig


@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Paper Stratonovich signature of `(t, W)` as a `ProlongedBrownianSetup`

Packs `paperSig2` (iterated Stratonovich integrals of `X = (t, W_t)` in the paper's word order)
into `ProlongedBrownianSetup`. Chen, shuffle, factorial moments and the signature dynamics are
the theorems `paperSig2_*` of `PaperSig`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Paper goal.** `ProlongedBrownianSetup` whose `sig2` is the Stratonovich/Itô signature of
`(t, W_t)`, discharging Chen, shuffle, adaptedness, and Appendix A factorial moments. -/
noncomputable def prolongedBrownianSetup_stratonovich_of_brownian {T : ℝ}
    (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ProlongedBrownianSetup Ω P d T where
  hT_pos := hT
  W := MultiBrownian.W B
  W_zero := MultiBrownian.W_zero B
  W_meas := MultiBrownian.W_meas B
  sig2 := paperSig2 B
  sig_meas := measurable_paperSig2_coeff B
  sig2_empty := paperSig2_empty B
  sig2_time := paperSig2_time B
  sig2_space := paperSig2_space B
  sig_adapted_to_W := fun _t s I =>
    measurable_paperSig2_coeff_pathFiltration B le_rfl s.2.1 s.2.2 I
  stratonovich_chen := fun _s _t hs hst _ => paperSig2_chen B hs hst
  stratonovich_shuffle := fun _t ht0 _ I J => paperSig2_shuffle B ht0 I J
  stratonovich_dynamics := fun I j _t ht0 _ => paperSig2_dynamics B I j ht0
  factorial_moment_control := fun p hp w_fn hw0 hgeom _t ht0 _ =>
    paperSig2_factorial_moment_control B p hp w_fn hw0 hgeom ht0

end SignatureVolatility

module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.OfBrownian
public import SignatureVolatility.ProlongedBrownianSetup.Sig2Strat
public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratChenShuffle
public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratMoments


@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Paper-strength Stratonovich / geometric signature of `(t, W)` (Phase 1)

Packs `sig2Strat` (multiplicative chordal / resolution-0 geometric lift of `(t, W)`, with
Chen/shuffle from dyadic algebra and level ≤1 match to Itô+conversion) into
`ProlongedBrownianSetup`. Analytic content lives in the imported submodules; this file
is only the assembler (no local proof holes).
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
  sig2 := sig2Strat B
  sig_meas := sig2Strat_meas B
  sig2_empty := sig2Strat_empty B
  sig2_time := sig2Strat_time B
  sig2_space := sig2Strat_space B
  sig_adapted_to_W := sig2Strat_adapted B
  stratonovich_chen := fun _s _t hs hst htT ω => sig2Strat_chen B (T := T) hs hst htT ω
  stratonovich_shuffle := fun _t ht0 htT I J ω =>
    sig2Strat_shuffle B (T := T) ht0 htT I J ω
  factorial_moment_control := fun p hp w_fn hw0 hgeom _t ht0 htT =>
    sig2Strat_factorial_moment_control B hT p hp w_fn hw0 hgeom ht0 htT

end SignatureVolatility

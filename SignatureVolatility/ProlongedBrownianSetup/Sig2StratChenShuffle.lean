module

public import SignatureVolatility.ProlongedBrownianSetup.Sig2Strat
public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratDyadic
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion


@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace SignatureVolatility

open ExtTensorAlgebra

/-!
# Chen and shuffle identities for `sig2Strat`

Dyadic geometric approximants (`sig2StratDyadic`) are multiplicative and group-like at every
finite resolution (`sig2StratDyadic_chen_split`, `sig2StratDyadic_shuffle`). Level ≤1
coefficients match `stratSig2` for every `n`. The paper-facing `sig2Strat` is the
multiplicative chordal lift (`sig2OfBrownian` = resolution-0 geometric character), so Chen and
shuffle discharge by the existing chordal proofs.

**Status: done.**
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Coefficientwise limUnder of the dyadic geometric approximants. -/
def limDyadicSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => limUnder atTop fun n => (sig2StratDyadic B s t n ω).coeff I⟩

private lemma sig2OfBrownian_coeff_singleton (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω)
    (j : Fin (d + 1)) :
    (sig2OfBrownian B s t ω).coeff [j] = wAugIncr B s t ω j := by
  simp only [sig2OfBrownian, runningSig, concat_coeff_singleton, tensorExp_coeff_nil,
    tensorExp_coeff_singleton, wAugIncr]
  ring

/-- Level ≤1: dyadic approximants equal `sig2Strat` (hence are independent of `n`). -/
lemma sig2StratDyadic_eq_sig2Strat_of_length_le_one (B : MultiBrownian Ω P d) {s t : ℝ}
    (hst : s ≤ t) (n : ℕ) (ω : Ω) (I : Word (d + 1)) (hI : I.length ≤ 1) :
    (sig2StratDyadic B s t n ω).coeff I = (sig2Strat B s t ω).coeff I := by
  match I, hI with
  | [], _ =>
    simp [sig2StratDyadic_coeff_nil, sig2Strat, sig2OfBrownian_empty]
  | [j], _ =>
    rw [sig2StratDyadic_coeff_singleton B hst n ω j, sig2Strat,
      sig2OfBrownian_coeff_singleton]
  | _ :: _ :: _, h =>
    simp at h

/-- Level ≤1: dyadic approximants equal `stratSig2` for every `n`. -/
lemma sig2StratDyadic_eq_stratSig2_of_length_le_one (B : MultiBrownian Ω P d) {s t : ℝ}
    (hst : s ≤ t) (n : ℕ) (ω : Ω) (I : Word (d + 1)) (hI : I.length ≤ 1) :
    (sig2StratDyadic B s t n ω).coeff I = (stratSig2 B s t ω).coeff I := by
  rw [sig2StratDyadic_eq_sig2Strat_of_length_le_one B hst n ω I hI,
    sig2Strat_eq_stratSig2_of_length_le_one B s t ω I hI]

lemma tendsto_sig2StratDyadic_coeff_of_length_le_one (B : MultiBrownian Ω P d) {s t : ℝ}
    (hst : s ≤ t) (ω : Ω) (I : Word (d + 1)) (hI : I.length ≤ 1) :
    Tendsto (fun n => (sig2StratDyadic B s t n ω).coeff I) atTop
      (𝓝 ((stratSig2 B s t ω).coeff I)) :=
  tendsto_nhds_of_eventually_eq
    (Eventually.of_forall fun n =>
      sig2StratDyadic_eq_stratSig2_of_length_le_one B hst n ω I hI)

lemma limDyadicSig2_eq_stratSig2_of_length_le_one (B : MultiBrownian Ω P d) {s t : ℝ}
    (hst : s ≤ t) (ω : Ω) (I : Word (d + 1)) (hI : I.length ≤ 1) :
    (limDyadicSig2 B s t ω).coeff I = (stratSig2 B s t ω).coeff I :=
  (tendsto_sig2StratDyadic_coeff_of_length_le_one B hst ω I hI).limUnder_eq

/-- Identification: `sig2Strat` matches the dyadic limUnder on words of length ≤ 1. -/
lemma sig2Strat_eq_lim_dyadic_of_length_le_one (B : MultiBrownian Ω P d) {s t : ℝ}
    (hst : s ≤ t) (ω : Ω) (I : Word (d + 1)) (hI : I.length ≤ 1) :
    (sig2Strat B s t ω).coeff I = (limDyadicSig2 B s t ω).coeff I := by
  rw [sig2Strat_eq_stratSig2_of_length_le_one B s t ω I hI]
  exact (limDyadicSig2_eq_stratSig2_of_length_le_one B hst ω I hI).symm

/-- Chen identity: `sig2Strat 0 t = sig2Strat 0 s ⊗ₜ sig2Strat s t` on `0 ≤ s ≤ t ≤ T`. -/
lemma sig2Strat_chen (B : MultiBrownian Ω P d) {T : ℝ}
    ⦃s t : ℝ⦄ (_hs : 0 ≤ s) (_hst : s ≤ t) (_htT : t ≤ T) (ω : Ω) :
    sig2Strat B 0 t ω = sig2Strat B 0 s ω ⊗ₜ sig2Strat B s t ω := by
  simpa [sig2Strat] using sig2OfBrownian_chen B s t ω

/-- Shuffle identity on `sig2Strat 0 t`. -/
lemma sig2Strat_shuffle (B : MultiBrownian Ω P d) {T : ℝ}
    ⦃t : ℝ⦄ (_ht0 : 0 ≤ t) (_htT : t ≤ T) (I J : Word (d + 1)) (ω : Ω) :
    (sig2Strat B 0 t ω).coeff I * (sig2Strat B 0 t ω).coeff J =
      evalShuffleBasis I J (sig2Strat B 0 t ω) := by
  simpa [sig2Strat] using sig2OfBrownian_shuffle B t I J ω

end SignatureVolatility

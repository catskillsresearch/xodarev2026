module

public import SignatureVolatility.GeneratedFiltration
public import SignatureVolatility.ProlongedBrownianSetup.SignatureOfBM
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion


@[expose] public section

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Two-parameter signature `sig2Strat` of `(t, W)`

Paper-facing `sig2Strat` is the multiplicative chordal / resolution-0 geometric lift
(`sig2OfBrownian`), which is group-like and satisfies Chen pathwise for all `ω`. Level ≤1
matches `stratSig2` (Itô word integrals + Stratonovich conversion). Dyadic refinements and
their algebra live in `Sig2StratDyadic`; Chen/shuffle discharge is in `Sig2StratChenShuffle`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Two-parameter signature of the prolonged Brownian path (multiplicative chordal lift). -/
def sig2Strat (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  sig2OfBrownian B s t ω

lemma sig2Strat_meas (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (sig2Strat B s t ω).coeff I) :=
  sig2OfBrownian_meas B s t I

lemma sig2Strat_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (sig2Strat B s t ω).coeff [] = 1 :=
  sig2OfBrownian_empty B s t ω

lemma sig2Strat_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (sig2Strat B s t ω).coeff [0] = t - s :=
  sig2OfBrownian_time B s t ω

lemma sig2Strat_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (sig2Strat B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  sig2OfBrownian_space B s t ω i

/-- Adaptedness: `sig2Strat 0 s` is measurable w.r.t. the path of `W` up to `t ≥ s`. -/
lemma sig2Strat_adapted (B : MultiBrownian Ω P d) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t})
    (I : Word (d + 1)) :
    Measurable[(generatedFiltration (fun u i ω => MultiBrownian.W B u ω i)
      (MultiBrownian.W_meas B)).σAlg t] (fun ω => (sig2Strat B 0 s.1 ω).coeff I) :=
  sig2OfBrownian_adapted B t s I

/-- Level ≤1 agreement with the Itô + conversion series `stratSig2`. -/
lemma sig2Strat_eq_stratSig2_of_length_le_one (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω)
    (I : Word (d + 1)) (hI : I.length ≤ 1) :
    (sig2Strat B s t ω).coeff I = (stratSig2 B s t ω).coeff I := by
  match I, hI with
  | [], _ =>
    simp [sig2Strat, sig2OfBrownian_empty, stratSig2, stratWordIntegral_empty]
  | [j], _ =>
    cases j using Fin.cases with
    | zero =>
      simp [sig2Strat, sig2OfBrownian_time, stratSig2, stratWordIntegral_time]
    | succ i =>
      simp [sig2Strat, sig2OfBrownian_space, stratSig2, stratWordIntegral_space]
  | _ :: _ :: _, h =>
    simp at h

end SignatureVolatility

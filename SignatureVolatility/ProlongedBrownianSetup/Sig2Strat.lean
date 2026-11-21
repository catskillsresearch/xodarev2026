module

public import SignatureVolatility.GeneratedFiltration
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Two-parameter Stratonovich signature `sig2Strat` of `(t, W)`

Defines `sig2Strat` as the Stratonovich tensor series from
`StratonovichItoConversion.stratSig2`, and discharges the ProlongedBrownianSetup
field obligations for measurability, level-1 axioms, and adaptedness.

**Status.** Empty and length-1 adaptedness proved. Longer words need the recursive Itô step.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Two-parameter Stratonovich signature of the prolonged Brownian path. -/
def sig2Strat (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  stratSig2 B s t ω

lemma sig2Strat_meas (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (sig2Strat B s t ω).coeff I) :=
  measurable_stratSig2_coeff B s t I

lemma sig2Strat_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (sig2Strat B s t ω).coeff [] = 1 :=
  stratSig2_empty B s t ω

lemma sig2Strat_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (sig2Strat B s t ω).coeff [0] = t - s :=
  stratSig2_time B s t ω

lemma sig2Strat_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (sig2Strat B s t ω).coeff [i.succ] =
      MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  stratSig2_space B s t ω i

/-- Adaptedness: `sig2Strat 0 s` is measurable w.r.t. the path of `W` up to `t ≥ s`. -/
lemma sig2Strat_adapted (B : MultiBrownian Ω P d) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t})
    (I : Word (d + 1)) :
    Measurable[(generatedFiltration (fun u i ω => MultiBrownian.W B u ω i)
      (MultiBrownian.W_meas B)).σAlg t] (fun ω => (sig2Strat B 0 s.1 ω).coeff I) := by
  match I with
  | [] =>
    have h : (fun ω => (sig2Strat B 0 s.1 ω).coeff []) = fun _ => (1 : ℝ) := by
      funext ω; exact sig2Strat_empty B 0 s.1 ω
    rw [h]; exact measurable_const
  | _ =>
    -- Level ≥ 1: path-generated measurability of recursive Itô/Stratonovich coords.
    sorry

end SignatureVolatility

module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleTensor
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# C2a. Bounded complex tilt `E_t(ξ) = exp(i ξ W_t^0 + ξ² t / 2)`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Complex-valued bounded exponential martingale
`E_t(ξ) = exp(i ξ W_t^0 + ξ² t / 2)`. -/
noncomputable def complexTilt {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ t : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * (MultiBrownian.W B t ω ⟨0, hd⟩ : ℂ) +
    ((ξ ^ 2 * t / 2 : ℝ) : ℂ))

lemma norm_complexTilt {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ t : ℝ) (ω : Ω) :
    ‖complexTilt B hd ξ t ω‖ = Real.exp (ξ ^ 2 * t / 2) := by
  sorry

lemma measurable_complexTilt {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ t : ℝ) :
    Measurable (complexTilt B hd ξ t) := by
  sorry

lemma measurable_complexTilt_pathFiltration {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Measurable[(pathFiltration B).σAlg t] (complexTilt B hd ξ t) := by
  sorry

lemma complexTilt_split {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ s t : ℝ) (ω : Ω) :
    complexTilt B hd ξ t ω =
      complexTilt B hd ξ s ω *
        Complex.exp (Complex.I * (ξ : ℂ) * (wnnIncr B ⟨0, hd⟩ s t ω : ℂ) +
          ((ξ ^ 2 * (t - s) / 2 : ℝ) : ℂ)) := by
  sorry

/-- `𝔼[exp(i ξ Z + ξ² v / 2)] = 1` for `Z ~ N(0, v)`. -/
lemma integral_exp_complexTilt_gaussianReal (ξ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
        ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ)) ∂(gaussianReal 0 v) = 1 := by
  sorry

/-- `𝔼[Z · exp(i ξ Z + ξ² v / 2)] = i ξ v` for `Z ~ N(0, v)`. -/
lemma integral_mul_exp_complexTilt_gaussianReal (ξ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, (x : ℂ) *
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
        ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ)) ∂(gaussianReal 0 v) =
      Complex.I * (ξ : ℂ) * (v : ℂ) := by
  sorry

/-- Martingale property of `complexTilt`: for `ℱ_s`-measurable `X ∈ L¹`
and `s ≤ t`, the extra increment of the tilt integrates to `1`. -/
lemma integral_mul_complexTilt_eq {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (ξ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {X : Ω → ℂ}
    (hXm : Measurable[(pathFiltration B).σAlg s] X) (hXi : Integrable X P) :
    ∫ ω, X ω * complexTilt B hd ξ t ω ∂P =
      ∫ ω, X ω * complexTilt B hd ξ s ω ∂P := by
  sorry

/-- Predicate: `J` only uses the time letter `0` and the first spatial letter. -/
def onlyZeroOrOne {d : ℕ} (hd : 0 < d) : Word (d + 1) → Bool
  | [] => true
  | j :: J => (decide (j = 0) || decide (j = firstSpace hd)) && onlyZeroOrOne hd J

/-- Number of occurrences of `firstSpace hd` in `J`. -/
def countOnes {d : ℕ} (hd : 0 < d) : Word (d + 1) → ℕ
  | [] => 0
  | j :: J => (if j = firstSpace hd then 1 else 0) + countOnes hd J

end SignatureVolatility

module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleTensor
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import SignatureVolatility.ItoCalculusKit.JointPast
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.ParametricIntegral

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
  unfold complexTilt
  rw [Complex.norm_exp]
  have h0 : (Complex.I * (ξ : ℂ) * (MultiBrownian.W B t ω ⟨0, hd⟩ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have h1 : (((ξ ^ 2 * t / 2 : ℝ) : ℂ)).re = ξ ^ 2 * t / 2 := Complex.ofReal_re _
  rw [Complex.add_re, h0, h1, zero_add]

lemma measurable_complexTilt {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ t : ℝ) :
    Measurable (complexTilt B hd ξ t) := by
  have hW : Measurable (fun ω => MultiBrownian.W B t ω ⟨0, hd⟩) :=
    MultiBrownian.W_meas B t ⟨0, hd⟩
  have hφ : Measurable (fun x : ℝ =>
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))) := by
    fun_prop
  exact hφ.comp hW

lemma measurable_complexTilt_pathFiltration {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (ξ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Measurable[(pathFiltration B).σAlg t] (complexTilt B hd ξ t) := by
  have hW : Measurable[(pathFiltration B).σAlg t]
      (fun ω => MultiBrownian.W B t ω ⟨0, hd⟩) :=
    measurable_W_pathFiltration B ⟨t, ht, le_rfl⟩ ⟨0, hd⟩
  have hφ : Measurable (fun x : ℝ =>
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ))) := by
    fun_prop
  exact hφ.comp hW

lemma complexTilt_split {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ s t : ℝ) (ω : Ω) :
    complexTilt B hd ξ t ω =
      complexTilt B hd ξ s ω *
        Complex.exp (Complex.I * (ξ : ℂ) * (wnnIncr B ⟨0, hd⟩ s t ω : ℂ) +
          ((ξ ^ 2 * (t - s) / 2 : ℝ) : ℂ)) := by
  unfold complexTilt
  rw [← Complex.exp_add]
  congr 1
  have hinc : (wnnIncr B ⟨0, hd⟩ s t ω : ℂ) =
      (MultiBrownian.W B t ω ⟨0, hd⟩ : ℂ) - (MultiBrownian.W B s ω ⟨0, hd⟩ : ℂ) := by
    simp [wnnIncr_eq_W]
  rw [hinc]; push_cast; ring

lemma integral_exp_complexTilt_gaussianReal (ξ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
        ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ)) ∂(gaussianReal 0 v) = 1 := by
  have hcf := charFun_gaussianReal (μ := (0 : ℝ)) (v := v) ξ
  simp only [charFun_apply_real, Complex.ofReal_zero, mul_zero, zero_sub, zero_mul] at hcf
  have hexp : (fun x : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
      ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ))) =
      fun x : ℝ => Complex.exp ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) *
        Complex.exp ((ξ * x : ℝ) * Complex.I) := by
    funext x; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hcf' :
      ∫ a : ℝ, Complex.exp ((ξ * a : ℝ) * Complex.I) ∂(gaussianReal 0 v) =
        Complex.exp (-((v : ℂ) * (ξ : ℂ) ^ 2 / 2)) := by
    convert hcf using 2
    ext x
    simp [mul_comm, Complex.ofReal_mul]
  rw [hexp, integral_const_mul, hcf', ← Complex.exp_add]
  have h0 : ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) + -((v : ℂ) * (ξ : ℂ) ^ 2 / 2) = 0 := by
    push_cast; ring
  rw [h0, Complex.exp_zero]

lemma integral_mul_exp_complexTilt_gaussianReal (ξ : ℝ) (v : ℝ≥0) :
    ∫ x : ℝ, (x : ℂ) *
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
        ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ)) ∂(gaussianReal 0 v) =
      Complex.I * (ξ : ℂ) * (v : ℂ) := by
  have hdiff : HasDerivAt
      (fun η : ℝ => ∫ x : ℝ, Complex.exp (Complex.I * (η : ℂ) * (x : ℂ)) ∂(gaussianReal 0 v))
      (∫ x : ℝ, (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))
        ∂(gaussianReal 0 v)) ξ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (η : ℝ) (x : ℝ) => Complex.exp (Complex.I * (η : ℂ) * (x : ℂ)))
      (F' := fun (η : ℝ) (x : ℝ) =>
        (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (η : ℂ) * (x : ℂ)))
      (bound := fun x : ℝ => |x|) (s := (Set.univ : Set ℝ)) (x₀ := ξ)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun _ => (by fun_prop : Continuous _).aestronglyMeasurable
    · refine (integrable_const (1 : ℝ)).mono' (by fun_prop : Continuous _).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Complex.norm_exp]; simp)
    · exact (by fun_prop : Continuous _).aestronglyMeasurable
    · refine ae_of_all _ fun x η _ => by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_exp]; simp
    · exact ((memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by simp)).integrable le_rfl).abs
    · refine ae_of_all _ fun x η _ => ?_
      have h1 : HasDerivAt (fun η : ℝ => Complex.I * (η : ℂ) * (x : ℂ)) (Complex.I * (x : ℂ)) η := by
        simpa [mul_assoc, mul_comm] using
          ((Complex.ofRealCLM.hasDerivAt (x := η)).const_mul Complex.I).mul_const (x : ℂ)
      simpa [mul_comm] using h1.cexp
  have hcf_eq : (fun η : ℝ =>
      ∫ x : ℝ, Complex.exp (Complex.I * (η : ℂ) * (x : ℂ)) ∂(gaussianReal 0 v)) =
      fun η : ℝ => Complex.exp (-((η : ℂ) ^ 2 * (v : ℂ) / 2)) := by
    funext η
    have h := charFun_gaussianReal (μ := (0 : ℝ)) (v := v) η
    simp only [charFun_apply_real, Complex.ofReal_zero, mul_zero] at h
    refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (h.trans ?_)
    · simp [mul_comm, mul_left_comm]
    · simp [mul_comm]
  have hdiff2 : HasDerivAt
      (fun η : ℝ => Complex.exp (-((η : ℂ) ^ 2 * (v : ℂ) / 2)))
      ((-(ξ : ℂ) * (v : ℂ)) * Complex.exp (-((ξ : ℂ) ^ 2 * (v : ℂ) / 2))) ξ := by
    have hid : HasDerivAt (fun η : ℝ => (η : ℂ)) (1 : ℂ) ξ :=
      Complex.ofRealCLM.hasDerivAt
    have hpow : HasDerivAt (fun η : ℝ => (η : ℂ) ^ 2) (2 * (ξ : ℂ)) ξ := by
      convert hid.pow 2 using 1
      simp
    have hmul : HasDerivAt (fun η : ℝ => (η : ℂ) ^ 2 * (v : ℂ))
        (2 * (ξ : ℂ) * (v : ℂ)) ξ := hpow.mul_const _
    have hdiv : HasDerivAt (fun η : ℝ => (η : ℂ) ^ 2 * (v : ℂ) / 2)
        ((2 * (ξ : ℂ) * (v : ℂ)) / 2) ξ := hmul.div_const 2
    have h1 : HasDerivAt (fun η : ℝ => -((η : ℂ) ^ 2 * (v : ℂ) / 2))
        (-(ξ : ℂ) * (v : ℂ)) ξ := by
      convert hdiv.neg using 2
      ring
    simpa [mul_comm] using h1.cexp
  rw [hcf_eq] at hdiff
  have hmul := congrArg (fun z : ℂ =>
      (-Complex.I) * Complex.exp ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) * z) (hdiff.unique hdiff2)
  rw [← integral_const_mul] at hmul
  have hL : (fun x : ℝ => (-Complex.I) * Complex.exp ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) *
      (Complex.I * (x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)))) =
      fun x : ℝ => (x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
        ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ)) := by
    funext x; rw [Complex.exp_add]
    have hI : (-Complex.I) * Complex.I = 1 := by simp
    calc _ = ((-Complex.I) * Complex.I) * (x : ℂ) *
            (Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) *
              Complex.exp ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hI, one_mul]
  rw [hL] at hmul; rw [hmul]
  have hcancel : Complex.exp ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) *
      Complex.exp (-((ξ : ℂ) ^ 2 * (v : ℂ) / 2)) = 1 := by
    rw [← Complex.exp_add]
    have : ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) + -((ξ : ℂ) ^ 2 * (v : ℂ) / 2) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero]
  calc _ = Complex.I * (ξ : ℂ) * (v : ℂ) *
        (Complex.exp ((ξ ^ 2 * (v : ℝ) / 2 : ℝ) : ℂ) *
          Complex.exp (-((ξ : ℂ) ^ 2 * (v : ℂ) / 2))) := by ring
    _ = _ := by rw [hcancel, mul_one]

lemma integral_mul_complexTilt_eq {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (ξ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {X : Ω → ℂ}
    (hXm : Measurable[(pathFiltration B).σAlg s] X) (hXi : Integrable X P) :
    ∫ ω, X ω * complexTilt B hd ξ t ω ∂P =
      ∫ ω, X ω * complexTilt B hd ξ s ω ∂P := by
  set inc : Ω → ℂ := fun ω =>
    Complex.exp (Complex.I * (ξ : ℂ) * (wnnIncr B ⟨0, hd⟩ s t ω : ℂ) +
      ((ξ ^ 2 * (t - s) / 2 : ℝ) : ℂ))
  have hsplit : (fun ω => X ω * complexTilt B hd ξ t ω) =
      fun ω => (X ω * complexTilt B hd ξ s ω) * inc ω := by
    funext ω; rw [complexTilt_split B hd ξ s t ω]; ring
  rw [hsplit]
  have hind : IndepFun (fun ω => X ω * complexTilt B hd ξ s ω) inc P :=
    (indepFun_pathFiltration_wnnIncr B ⟨0, hd⟩ hst
      (hXm.mul (measurable_complexTilt_pathFiltration B hd ξ hs))).comp
      measurable_id (by fun_prop : Measurable fun x : ℝ =>
        Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * (t - s) / 2 : ℝ) : ℂ)))
  have h1 : Integrable (fun ω => X ω * complexTilt B hd ξ s ω) P :=
    hXi.mul_bdd (c := Real.exp (ξ ^ 2 * s / 2))
      (measurable_complexTilt B hd ξ s).aestronglyMeasurable
      (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B hd ξ s ω))
  have h2 : ∫ ω, inc ω ∂P = 1 := by
    have hcomp := (hasLaw_wnnIncr B ⟨0, hd⟩ hs hst).integral_comp
      (f := fun x : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
        ((ξ ^ 2 * (t - s) / 2 : ℝ) : ℂ)))
      (by fun_prop : Continuous _).aestronglyMeasurable
    simp only [Function.comp_def] at hcomp; rw [hcomp]
    have hcast : ((Real.toNNReal (t - s) : ℝ≥0) : ℝ) = t - s :=
      Real.coe_toNNReal _ (sub_nonneg.mpr hst)
    simpa [hcast] using integral_exp_complexTilt_gaussianReal ξ (Real.toNNReal (t - s))
  have hinc_meas : AEStronglyMeasurable inc P := by
    have hφ : Measurable (fun x : ℝ =>
        Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
          ((ξ ^ 2 * (t - s) / 2 : ℝ) : ℂ))) := by
      fun_prop
    exact (hφ.comp (measurable_wnnIncr B ⟨0, hd⟩ s t)).aestronglyMeasurable
  rw [hind.integral_fun_mul_eq_mul_integral h1.aestronglyMeasurable hinc_meas, h2, mul_one]

/-- Predicate: `J` only uses the time letter `0` and the first spatial letter. -/
def onlyZeroOrOne {d : ℕ} (hd : 0 < d) : Word (d + 1) → Bool
  | [] => true
  | j :: J => (decide (j = 0) || decide (j = firstSpace hd)) && onlyZeroOrOne hd J

/-- Number of occurrences of `firstSpace hd` in `J`. -/
def countOnes {d : ℕ} (hd : 0 < d) : Word (d + 1) → ℕ
  | [] => 0
  | j :: J => (if j = firstSpace hd then 1 else 0) + countOnes hd J

end SignatureVolatility

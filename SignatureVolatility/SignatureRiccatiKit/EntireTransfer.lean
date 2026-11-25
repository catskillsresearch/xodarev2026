module

public import SignatureVolatility.SignatureRiccatiKit.CondSigPoly
public import SignatureVolatility.SignatureRiccatiKit.CondSigPolyIdentification
public import SignatureVolatility.SignatureRiccatiKit.SummableNormTermAndBound
public import SignatureVolatility.SignatureRiccatiKit.DifferentiableAtTsum
public import SignatureVolatility.SignatureRiccatiKit.FourierUniquenessGaussian
public import SignatureVolatility.SignatureRiccatiKit.IteratedDerivGaussian
public import SignatureVolatility.SignatureRiccatiKit.ComplexTilt
public import SignatureVolatility.SignatureRiccatiKit.FawcettHermite
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichOfBM
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.MemTw
public import SignatureVolatility.NormW
public import SignatureVolatility.DualPairing
public import SignatureVolatility.SignatureVolatilityModel
public import SignatureVolatility.ExtTensorAlgebra.LevelInner
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.WordsOfLength
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.ComplexMGF


/-!
# C3. Transfer from the tilted word expansion to `f`

Given `⟨φ, Ŵ_t⟩ = f(W_t^0)` a.s. for an a.e.-measurable `f`, Fourier uniqueness
against the complex tilt yields that `f` agrees Lebesgue-a.e. with an entire
function of exponential type `≤ 1`. The extra hypothesis
`hf : AEMeasurable f volume` is an internal obligation: without it the
statement is false (Vitali-set counterexample). It is discharged at the
call site from the measurability of `log ∘ v₁`, and does not appear on
`not_affine_riccati_duality_mpr`. No Girsanov identification is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Finset Set
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

open ExtTensorAlgebra

private lemma paperSetup_sig2_eq {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    (t : ℝ) (ω : Ω) : (paperSetup B hT).sig2 0 t ω = paperSig2 B 0 t ω :=
  rfl

private lemma measurable_paperSig2_levelNorm {d : ℕ} (B : MultiBrownian Ω P d)
    (t : ℝ) (n : ℕ) : Measurable fun ω => (paperSig2 B 0 t ω).levelNorm n := by
  simp only [levelNorm, levelNormSq]
  exact (Finset.measurable_sum _ fun I _ =>
    (measurable_paperSig2_coeff B 0 t I).pow_const 2).sqrt

private lemma integrable_ofReal_pow_gaussianReal (m : ℕ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => (x : ℂ) ^ m) (gaussianReal 0 v) := by
  have hbd : Integrable (fun x : ℝ => |x| ^ m) (gaussianReal 0 v) := by
    have hLp : MemLp (id : ℝ → ℝ) (m : ℝ≥0∞) (gaussianReal 0 v) :=
      memLp_id_gaussianReal' (μ := 0) (v := v) (m : ℝ≥0∞) (ENNReal.natCast_ne_top m)
    have hint := hLp.integrable_norm_rpow'
    simpa [Real.norm_eq_abs, ENNReal.toReal_natCast] using hint
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ m) (gaussianReal 0 v) :=
    (Complex.continuous_ofReal.pow m).aestronglyMeasurable
  refine Integrable.mono' hbd hmeas (ae_of_all _ fun x => ?_)
  simp [Complex.norm_real, Real.norm_eq_abs, norm_pow]

private lemma integrable_monicHermite_gaussianReal (k : ℕ) {t : ℝ} (_ht : 0 ≤ t) :
    Integrable (fun x : ℝ => monicHermite k t (x : ℂ))
      (gaussianReal 0 (Real.toNNReal t)) := by
  simp_rw [monicHermite_eq_sum]
  refine integrable_finsetSum _ fun m _ => ?_
  have hx := integrable_ofReal_pow_gaussianReal (k - m) t.toNNReal
  convert hx.const_mul ((k.choose m : ℂ) * (I * (Real.sqrt t : ℂ)) ^ m *
      ∫ y : ℝ, (y : ℂ) ^ m ∂gaussianReal 0 1) using 1
  funext (x : ℝ)
  ring

private lemma integrable_condSigPoly_gaussianReal {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : 0 ≤ t) (I : Word (d + 1)) :
    Integrable (fun x : ℝ => condSigPoly hd t I (x : ℂ))
      (gaussianReal 0 t.toNNReal) := by
  have hterm (p : ℝ × Word (d + 1)) :
      Integrable (fun x : ℝ =>
        (if onlyZeroOrOne hd p.2 then
          (p.1 : ℂ) *
            ((t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ) : ℝ) : ℂ) *
            monicHermite (countOnes hd p.2) t (x : ℂ)
        else 0)) (gaussianReal 0 t.toNNReal) := by
    split_ifs
    · exact (integrable_monicHermite_gaussianReal _ ht).const_mul _
    · exact integrable_const (0 : ℂ)
  unfold condSigPoly hermitePoly
  induction contractions I.reverse with
  | nil =>
    simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hterm p).add ih

/-- **C3.** Transfer of the word-polynomial expansion to a measurable `f` with
`⟨φ, Ŵ_t⟩ = f(W_t^0)` a.s. The conclusion is exactly that of Pillar C.
The hypothesis `hf` is required (without it a Vitali-set counterexample
exists) and is discharged at the call site from existing measurability. -/
lemma fawcett_transfer_to_f (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ M.T)
    {phi : ExtTensorAlgebra (M.d + 1)} (hphi : MemTw M.w phi) {f : ℝ → ℝ}
    (hf : AEMeasurable f volume)
    (hfeq : (fun ω => dualPairing phi ((paperSetup B M.hT).W_hat t ω)) =ᵐ[P]
      fun ω => f (MultiBrownian.W B t ω ⟨0, M.hd⟩)) :
    ∃ (G : ℂ → ℂ) (C : ℝ), Differentiable ℂ G ∧ 0 ≤ C ∧
      (∀ z : ℂ, ‖G z‖ ≤ C * Real.exp ‖z‖) ∧
      (∀ᵐ x : ℝ ∂volume, G x = (f x : ℂ)) := by
  set Kphi : ℝ := normW M.w phi
  have hKphi0 : 0 ≤ Kphi := tsum_nonneg fun n => mul_nonneg (M.w.pos n).le (levelNorm.nonneg _ _)
  have hcoeff : ∀ I : Word (M.d + 1), |phi.coeff I| ≤ Kphi := fun I => by
    have hw1 : 1 ≤ M.w I.length := by simpa [M.w.w_zero] using M.w.mono (Nat.zero_le _)
    have hsq : phi.coeff I ^ 2 ≤ phi.levelNormSq I.length :=
      Finset.single_le_sum (fun J _ => sq_nonneg (phi.coeff J)) (wordsOfLength.mem.mpr rfl)
    calc |phi.coeff I| ≤ phi.levelNorm I.length := Real.abs_le_sqrt hsq
      _ ≤ M.w I.length * phi.levelNorm I.length := le_mul_of_one_le_left (levelNorm.nonneg _ _) hw1
      _ ≤ Kphi := hphi.le_tsum I.length fun n _ => mul_nonneg (M.w.pos n).le (levelNorm.nonneg _ _)
  have hG_mgf : ∫ y : ℝ, Real.exp (Real.sqrt t * |y|) ∂(gaussianReal 0 1) ≤ 2 * Real.exp (t / 2) := by
    have h1 : ∀ y : ℝ, Real.exp (Real.sqrt t * |y|) ≤
        Real.exp (Real.sqrt t * y) + Real.exp (-(Real.sqrt t) * y) := fun y => by
      rcases le_total 0 y with hy | hy
      · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-(Real.sqrt t) * y)]
      · rw [abs_of_nonpos hy, mul_neg, ← neg_mul]; linarith [Real.exp_pos (Real.sqrt t * y)]
    have hi1 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (Real.sqrt t)
    have hi2 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-(Real.sqrt t))
    calc ∫ y : ℝ, Real.exp (Real.sqrt t * |y|) ∂(gaussianReal 0 1)
        ≤ ∫ y : ℝ, (Real.exp (Real.sqrt t * y) + Real.exp (-(Real.sqrt t) * y)) ∂(gaussianReal 0 1) :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => (Real.exp_pos _).le) (hi1.add hi2) (ae_of_all _ h1)
      _ = Real.exp (t / 2) + Real.exp (t / 2) := by
          rw [integral_add hi1 hi2]
          have hmgf (c : ℝ) :
              ∫ y : ℝ, Real.exp (c * y) ∂(gaussianReal 0 1) = Real.exp (c ^ 2 / 2) := by
            simpa [mgf] using congrArg (fun g => g c) (mgf_id_gaussianReal (μ := 0) (v := 1))
          rw [hmgf (Real.sqrt t), hmgf (-(Real.sqrt t)), Real.sq_sqrt ht0.le, neg_sq, Real.sq_sqrt ht0.le]
      _ = 2 * Real.exp (t / 2) := by ring
  set C₀ : ℝ := 2 * Real.exp (((3 + (M.d : ℝ)) / 2) * t)
  have hC₀0 : 0 ≤ C₀ := by positivity
  let term (n : ℕ) (z : ℂ) : ℂ :=
    ∑ I ∈ wordsOfLength (M.d + 1) n, (phi.coeff I : ℂ) * condSigPoly M.hd t I z
  let G : ℂ → ℂ := fun z => ∑' n : ℕ, term n z
  have hbound : ∀ z : ℂ, Summable (fun n => ‖term n z‖) ∧ ∑' n, ‖term n z‖ ≤ (Kphi * C₀) * Real.exp ‖z‖ :=
    fun z => summable_norm_term_and_bound M.hd ht0.le hcoeff hG_mgf z
  have hG_diff : Differentiable ℂ G := fun z₀ =>
    differentiableAt_tsum_of_locallyUniform term
      (fun n => Differentiable.fun_sum fun I _ =>
        (differentiable_const _).mul (differentiable_condSigPoly M.hd t I)) hbound z₀
  have hG_bd : ∀ z : ℂ, ‖G z‖ ≤ (Kphi * C₀) * Real.exp ‖z‖ := fun z =>
    (norm_tsum_le_tsum_norm (hbound z).1).trans (hbound z).2
  -- Law of `W_t^0` is `gaussianReal 0 t.toNNReal`
  set γ := gaussianReal 0 (Real.toNNReal t)
  have hv_ne : Real.toNNReal t ≠ 0 := (Real.toNNReal_pos.mpr ht0).ne'
  have hlaw : HasLaw (fun ω => MultiBrownian.W B t ω ⟨0, M.hd⟩) γ P := by
    simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using hasLaw_wnnIncr B ⟨0, M.hd⟩ le_rfl ht0.le
  -- `γ ≪ volume`, so `f` is `AEMeasurable` for `γ`
  have hf_γ : AEMeasurable f γ := by
    rw [show γ = volume.withDensity (gaussianPDF 0 (Real.toNNReal t)) from gaussianReal_of_var_ne_zero 0 hv_ne]
    exact hf.mono_ac (withDensity_absolutelyContinuous _ _)
  -- `dualPairing phi (W_hat t)` is `P`-integrable via `factorial_moment_control`
  have hfac := (paperSetup B M.hT).factorial_moment_control 1 le_rfl (fun _ => 1)
    (fun _ => zero_le_one) ⟨1, fun _ => by simp⟩ ht0.le htT
  have hcs_level : ∀ n ω, |phi.levelInner (paperSig2 B 0 t ω) n| ≤
      Kphi * (paperSig2 B 0 t ω).levelNorm n := fun n ω => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (wordsOfLength (M.d + 1) n)
      (fun I => phi.coeff I) (fun I => (paperSig2 B 0 t ω).coeff I)
    have hle : |phi.levelInner (paperSig2 B 0 t ω) n| ≤
        phi.levelNorm n * (paperSig2 B 0 t ω).levelNorm n := by
      unfold levelInner levelNorm levelNormSq
      rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact Real.abs_le_sqrt hcs
    have hpn : phi.levelNorm n ≤ Kphi := by
      have hw1 : 1 ≤ M.w n := by simpa [M.w.w_zero] using M.w.mono (Nat.zero_le n)
      exact (le_mul_of_one_le_left (levelNorm.nonneg _ _) hw1).trans
        (hphi.le_tsum n fun k _ => mul_nonneg (M.w.pos k).le (levelNorm.nonneg _ _))
    exact hle.trans (mul_le_mul_of_nonneg_right hpn (levelNorm.nonneg _ _))
  have hdp_int : Integrable (fun ω => dualPairing phi ((paperSetup B M.hT).W_hat t ω)) P := by
    have hW1 : Integrable (fun ω => ∑' n, (paperSig2 B 0 t ω).levelNorm n) P := by
      simpa [paperSetup_sig2_eq] using hfac.2
    refine (hW1.const_mul Kphi).mono' ?_ ?_
    · refine AEStronglyMeasurable.tsum fun n => ?_
      exact (Finset.measurable_sum _ fun I _ =>
        measurable_const.mul (measurable_paperSig2_coeff B 0 t I)).aestronglyMeasurable
    · filter_upwards [hfac.1] with ω hω
      have hsumm_w : Summable (fun n => (paperSig2 B 0 t ω).levelNorm n) := by simpa [paperSetup_sig2_eq, one_mul] using hω
      have hsumm_in : Summable (fun n => ‖phi.levelInner (paperSig2 B 0 t ω) n‖) :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
          simpa [Real.norm_eq_abs] using hcs_level n ω) (hsumm_w.mul_left Kphi)
      calc ‖dualPairing phi ((paperSetup B M.hT).W_hat t ω)‖
          ≤ ∑' n, ‖phi.levelInner (paperSig2 B 0 t ω) n‖ := norm_tsum_le_tsum_norm hsumm_in
        _ ≤ ∑' n, Kphi * (paperSig2 B 0 t ω).levelNorm n :=
            hsumm_in.tsum_le_tsum (fun n => by simpa [Real.norm_eq_abs] using hcs_level n ω)
              (hsumm_w.mul_left Kphi)
        _ = Kphi * ∑' n, (paperSig2 B 0 t ω).levelNorm n := tsum_mul_left
  -- `f` and `G` are `γ`-integrable
  have hf_int_γ : Integrable (fun x : ℝ => (f x : ℂ)) γ := by
    have hcomp : Integrable (fun ω => f (MultiBrownian.W B t ω ⟨0, M.hd⟩)) P :=
      hdp_int.congr hfeq
    have hsm : AEStronglyMeasurable f
        (P.map (fun ω => MultiBrownian.W B t ω ⟨0, M.hd⟩)) := by
      rw [hlaw.map_eq]; exact hf_γ.aestronglyMeasurable
    have hfR : Integrable f γ := by
      rw [← hlaw.map_eq]
      exact (integrable_map_measure hsm hlaw.aemeasurable).mpr
        (by simpa [Function.comp_def] using hcomp)
    exact hfR.ofReal
  have hexp_abs_γ : Integrable (fun x : ℝ => Real.exp |x|) γ := by
    refine ((integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal t) 1).add
      (integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal t) (-1))).mono'
      (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have hbound : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
      · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]
    simpa [Pi.add_apply, one_mul, neg_one_mul] using hbound
  have hG_int_γ : Integrable (fun x : ℝ => G x) γ :=
    (hexp_abs_γ.const_mul (Kphi * C₀)).mono'
      (hG_diff.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hG_bd x)
  -- Show Fourier transform of `(f - G)` against `γ` vanishes at every `ξ : ℝ`
  have hfourier : ∀ ξ : ℝ,
      ∫ x : ℝ, ((f x : ℂ) - G x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂γ = 0 := by
    intro ξ
    set E_bd : ℝ := Real.exp (ξ ^ 2 * t / 2)
    have hne : Complex.exp ((ξ ^ 2 * t / 2 : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
    suffices h : ∫ ω, ((f (MultiBrownian.W B t ω ⟨0, M.hd⟩) : ℂ) -
        G (MultiBrownian.W B t ω ⟨0, M.hd⟩)) * complexTilt B M.hd ξ t ω ∂P = 0 by
      have hcomp := hlaw.integral_comp
        (f := fun x : ℝ => ((f x : ℂ) - G x) *
          Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)))
        (((Complex.continuous_ofReal.aemeasurable.comp_aemeasurable hf_γ).aestronglyMeasurable.sub
          (hG_diff.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable).mul
          (by fun_prop : Continuous _).aestronglyMeasurable)
      simp only [Function.comp_def, complexTilt] at hcomp h
      rw [hcomp] at h
      have hpull : ∫ x : ℝ, ((f x : ℂ) - G x) *
            Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)) ∂γ =
          Complex.exp ((ξ ^ 2 * t / 2 : ℝ) : ℂ) *
            ∫ x : ℝ, ((f x : ℂ) - G x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂γ := by
        rw [← integral_const_mul]; congr 1; funext x; rw [Complex.exp_add]; ring
      rw [hpull] at h
      exact (mul_eq_zero.mp h).resolve_left hne
    -- Evaluate LHS via `integral_tsum`
    have hL : ∫ ω, (f (MultiBrownian.W B t ω ⟨0, M.hd⟩) : ℂ) * complexTilt B M.hd ξ t ω ∂P =
        ∑' n : ℕ, ∑ I ∈ wordsOfLength (M.d + 1) n, (phi.coeff I : ℂ) *
          ∫ ω, ((paperSig2 B 0 t ω).coeff I : ℂ) * complexTilt B M.hd ξ t ω ∂P := by
      have hfeqC :
          (fun ω => (f (MultiBrownian.W B t ω ⟨0, M.hd⟩) : ℂ) * complexTilt B M.hd ξ t ω) =ᵐ[P]
            fun ω => (dualPairing phi ((paperSetup B M.hT).W_hat t ω) : ℂ) *
              complexTilt B M.hd ξ t ω :=
        hfeq.symm.mono fun ω hω => by
          simp only [hω]
      rw [integral_congr_ae hfeqC]
      have hpt : ∀ᵐ ω ∂P, ((dualPairing phi ((paperSetup B M.hT).W_hat t ω) : ℝ) : ℂ) *
            complexTilt B M.hd ξ t ω =
          ∑' n : ℕ, ((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ) * complexTilt B M.hd ξ t ω := by
        filter_upwards [hfac.1] with ω hω
        have hsumm_w : Summable (fun n => (paperSig2 B 0 t ω).levelNorm n) := by simpa [paperSetup_sig2_eq, one_mul] using hω
        have hsumm_in : Summable (fun n => phi.levelInner (paperSig2 B 0 t ω) n) :=
          Summable.of_norm_bounded (hsumm_w.mul_left Kphi) fun n => by
            simpa [Real.norm_eq_abs] using hcs_level n ω
        change ((∑' n, phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ) * _ = _
        rw [Complex.ofReal_tsum, ← tsum_mul_right]
      rw [integral_congr_ae hpt, integral_tsum]
      · congr 1; funext n
        simp only [levelInner, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun I _ => ?_
          simp_rw [mul_assoc]
          exact integral_const_mul _ _
        · intro I _
          exact (((memLp_paperSig2_coeff B ht0.le I le_rfl).integrable (by norm_num)).ofReal.const_mul _).mul_bdd
            (measurable_complexTilt B M.hd ξ t).aestronglyMeasurable
            (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B M.hd ξ t ω))
      · intro n
        exact ((Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun I _ =>
          measurable_const.mul (measurable_paperSig2_coeff B 0 t I))).mul
          (measurable_complexTilt B M.hd ξ t)).aestronglyMeasurable
      · -- `∑' n, ∫⁻ ω, ‖levelInner_n * E_t‖ₑ < ⊤` from `hfac.2`
        have hmeas_n (n : ℕ) :
            AEMeasurable (fun ω =>
              ‖((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ) *
                complexTilt B M.hd ξ t ω‖ₑ) P := by
          have h1 : Measurable fun ω => phi.levelInner (paperSig2 B 0 t ω) n := by
            unfold levelInner
            exact Finset.measurable_sum _ fun I _ =>
              measurable_const.mul (measurable_paperSig2_coeff B 0 t I)
          exact ((Complex.measurable_ofReal.comp h1).mul
            (measurable_complexTilt B M.hd ξ t)).enorm.aemeasurable
        rw [← lintegral_tsum hmeas_n]
        have hmeas_tsum : Measurable fun ω =>
            ∑' n, ENNReal.ofReal ((paperSig2 B 0 t ω).levelNorm n) :=
          Measurable.tsum fun n =>
            (measurable_paperSig2_levelNorm B t n).ennreal_ofReal
        have hW1 : Integrable (fun ω => ∑' n, (paperSig2 B 0 t ω).levelNorm n) P := by
          simpa [paperSetup_sig2_eq] using hfac.2
        have hle : ∫⁻ ω, ∑' n, ‖((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ) *
              complexTilt B M.hd ξ t ω‖ₑ ∂P ≤
            ENNReal.ofReal (E_bd * Kphi) *
              ∫⁻ ω, ∑' n, ENNReal.ofReal ((paperSig2 B 0 t ω).levelNorm n) ∂P := by
          rw [← lintegral_const_mul _ hmeas_tsum]
          refine lintegral_mono_ae ?_
          filter_upwards [hfac.1] with ω hω
          have hsumm_w : Summable (fun n => (paperSig2 B 0 t ω).levelNorm n) := by
            simpa [paperSetup_sig2_eq, one_mul] using hω
          calc ∑' n, ‖((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ) *
                complexTilt B M.hd ξ t ω‖ₑ
              ≤ ∑' n, ENNReal.ofReal (E_bd * Kphi) *
                  ENNReal.ofReal ((paperSig2 B 0 t ω).levelNorm n) := by
                refine ENNReal.tsum_le_tsum fun n => ?_
                have hnn : 0 ≤ E_bd * Kphi := mul_nonneg (Real.exp_pos _).le hKphi0
                have hL : ‖((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ) *
                      complexTilt B M.hd ξ t ω‖ₑ =
                    ENNReal.ofReal (|phi.levelInner (paperSig2 B 0 t ω) n| * E_bd) := by
                  rw [enorm_mul]
                  have h1 : ‖((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ)‖ₑ =
                      ENNReal.ofReal |phi.levelInner (paperSig2 B 0 t ω) n| :=
                    (ofReal_norm ((phi.levelInner (paperSig2 B 0 t ω) n : ℝ) : ℂ)).symm.trans
                      (congrArg ENNReal.ofReal (by rw [Complex.norm_real, Real.norm_eq_abs]))
                  have h2 : ‖complexTilt B M.hd ξ t ω‖ₑ = ENNReal.ofReal E_bd :=
                    (ofReal_norm (complexTilt B M.hd ξ t ω)).symm.trans
                      (congrArg ENNReal.ofReal (norm_complexTilt B M.hd ξ t ω))
                  rw [h1, h2, ← ENNReal.ofReal_mul (abs_nonneg _)]
                rw [hL, ← ENNReal.ofReal_mul hnn]
                exact ENNReal.ofReal_le_ofReal <| by
                  calc |phi.levelInner (paperSig2 B 0 t ω) n| * E_bd
                      ≤ (Kphi * (paperSig2 B 0 t ω).levelNorm n) * E_bd :=
                        mul_le_mul_of_nonneg_right (hcs_level n ω) (Real.exp_pos _).le
                    _ = E_bd * Kphi * (paperSig2 B 0 t ω).levelNorm n := by ring
            _ = ENNReal.ofReal (E_bd * Kphi) * ∑' n, ENNReal.ofReal ((paperSig2 B 0 t ω).levelNorm n) :=
                ENNReal.tsum_mul_left
        exact (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top <| by
          have hagree : (fun ω => ∑' n, ENNReal.ofReal ((paperSig2 B 0 t ω).levelNorm n)) =ᵐ[P]
              fun ω => ENNReal.ofReal (∑' n, (paperSig2 B 0 t ω).levelNorm n) := by
            filter_upwards [hfac.1] with ω hω
            have hsumm_w : Summable (fun n => (paperSig2 B 0 t ω).levelNorm n) := by
              simpa [paperSetup_sig2_eq, one_mul] using hω
            exact (ENNReal.ofReal_tsum_of_nonneg (fun n => levelNorm.nonneg _ _) hsumm_w).symm
          rw [lintegral_congr_ae hagree,
            ← ofReal_integral_eq_lintegral_ofReal hW1
              (ae_of_all _ fun _ => tsum_nonneg fun _ => levelNorm.nonneg _ _)]
          exact ENNReal.ofReal_lt_top)).ne
    -- Evaluate RHS via `integral_tsum`
    have hR : ∫ ω, G (MultiBrownian.W B t ω ⟨0, M.hd⟩) * complexTilt B M.hd ξ t ω ∂P =
        ∑' n : ℕ, ∑ I ∈ wordsOfLength (M.d + 1) n, (phi.coeff I : ℂ) *
          ∫ ω, condSigPoly M.hd t I (MultiBrownian.W B t ω ⟨0, M.hd⟩) *
            complexTilt B M.hd ξ t ω ∂P := by
      have hpt : ∀ ω, G (MultiBrownian.W B t ω ⟨0, M.hd⟩) * complexTilt B M.hd ξ t ω =
          ∑' n : ℕ, term n (MultiBrownian.W B t ω ⟨0, M.hd⟩) * complexTilt B M.hd ξ t ω := fun ω => by
        simp only [G, tsum_mul_right]
      simp_rw [hpt]
      rw [integral_tsum]
      · congr 1; funext n
        simp only [term, Finset.sum_mul]
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun I _ => ?_
          simp_rw [mul_assoc]
          exact integral_const_mul _ _
        · intro I _
          have hI_int : Integrable (fun ω => condSigPoly M.hd t I (MultiBrownian.W B t ω ⟨0, M.hd⟩)) P := by
            simpa [Function.comp_def] using
              hlaw.integrable_comp (integrable_condSigPoly_gaussianReal M.hd ht0.le I)
          exact (hI_int.const_mul _).mul_bdd (measurable_complexTilt B M.hd ξ t).aestronglyMeasurable
            (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B M.hd ξ t ω))
      · intro n
        exact ((((Differentiable.fun_sum fun I _ => (differentiable_const _).mul
          (differentiable_condSigPoly M.hd t I)).continuous.comp Complex.continuous_ofReal).measurable.comp
          (MultiBrownian.W_meas B t ⟨0, M.hd⟩)).mul (measurable_complexTilt B M.hd ξ t)).aestronglyMeasurable
      · have hmeas_term (n : ℕ) :
            AEMeasurable (fun ω =>
              ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩) *
                complexTilt B M.hd ξ t ω‖ₑ) P := by
          have hcont : Continuous fun x : ℝ => term n (x : ℂ) :=
            ((Differentiable.fun_sum fun I _ => (differentiable_const _).mul
              (differentiable_condSigPoly M.hd t I)).continuous.comp
              Complex.continuous_ofReal)
          exact ((hcont.measurable.comp (MultiBrownian.W_meas B t ⟨0, M.hd⟩)).mul
            (measurable_complexTilt B M.hd ξ t)).enorm.aemeasurable
        rw [← lintegral_tsum hmeas_term]
        have hexp_P : Integrable (fun ω => Real.exp |MultiBrownian.W B t ω ⟨0, M.hd⟩|) P := by
          simpa [Function.comp_def] using hlaw.integrable_comp hexp_abs_γ
        have hle : ∫⁻ ω, ∑' n, ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩) *
              complexTilt B M.hd ξ t ω‖ₑ ∂P ≤
            ENNReal.ofReal (E_bd * (Kphi * C₀)) *
              ∫⁻ ω, ENNReal.ofReal (Real.exp |MultiBrownian.W B t ω ⟨0, M.hd⟩|) ∂P := by
          have hmeas_exp : Measurable fun ω =>
              ENNReal.ofReal (Real.exp |MultiBrownian.W B t ω ⟨0, M.hd⟩|) :=
            ENNReal.measurable_ofReal.comp
              (Real.measurable_exp.comp
                (continuous_abs.measurable.comp (MultiBrownian.W_meas B t ⟨0, M.hd⟩)))
          rw [← lintegral_const_mul _ hmeas_exp]
          refine lintegral_mono fun ω => ?_
          have hb := hbound (MultiBrownian.W B t ω ⟨0, M.hd⟩)
          calc ∑' n, ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩) * complexTilt B M.hd ξ t ω‖ₑ
              = ENNReal.ofReal (∑' n, ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩)‖ * E_bd) := by
                have hpt (n : ℕ) :
                    ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩) * complexTilt B M.hd ξ t ω‖ₑ =
                      ENNReal.ofReal (‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩)‖ * E_bd) := by
                  have h1 := (ofReal_norm (term n (MultiBrownian.W B t ω ⟨0, M.hd⟩))).symm
                  have h2 := (ofReal_norm (complexTilt B M.hd ξ t ω)).symm.trans
                    (congrArg ENNReal.ofReal (norm_complexTilt B M.hd ξ t ω))
                  rw [enorm_mul, h1, h2, ← ENNReal.ofReal_mul (norm_nonneg _)]
                simp_rw [hpt]
                exact (ENNReal.ofReal_tsum_of_nonneg
                  (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
                  (hb.1.mul_right E_bd)).symm
            _ = ENNReal.ofReal ((∑' n, ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩)‖) * E_bd) := by
                rw [tsum_mul_right]
            _ ≤ ENNReal.ofReal ((E_bd * (Kphi * C₀)) * Real.exp |MultiBrownian.W B t ω ⟨0, M.hd⟩|) := by
                apply ENNReal.ofReal_le_ofReal
                have h2 : ∑' n, ‖term n (MultiBrownian.W B t ω ⟨0, M.hd⟩)‖ ≤
                    (Kphi * C₀) * Real.exp |MultiBrownian.W B t ω ⟨0, M.hd⟩| := by
                  simpa [Complex.norm_real, Real.norm_eq_abs] using hb.2
                nlinarith [Real.exp_pos (ξ ^ 2 * t / 2)]
            _ = _ := ENNReal.ofReal_mul (by positivity)
        exact (hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top <| by
          rw [← ofReal_integral_eq_lintegral_ofReal hexp_P (ae_of_all _ fun _ => (Real.exp_pos _).le)]
          exact ENNReal.ofReal_lt_top)).ne
    -- Subtract LHS and RHS and apply `integral_paperSig2_eq_condSigPoly`
    have hf_P : Integrable (fun ω => (f (MultiBrownian.W B t ω ⟨0, M.hd⟩) : ℂ) *
        complexTilt B M.hd ξ t ω) P :=
      (hdp_int.congr hfeq).ofReal.mul_bdd (measurable_complexTilt B M.hd ξ t).aestronglyMeasurable
        (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B M.hd ξ t ω))
    have hG_P : Integrable (fun ω => G (MultiBrownian.W B t ω ⟨0, M.hd⟩) *
        complexTilt B M.hd ξ t ω) P := by
      have hG_comp : Integrable (fun ω => G (MultiBrownian.W B t ω ⟨0, M.hd⟩)) P := by
        simpa [Function.comp_def] using hlaw.integrable_comp hG_int_γ
      exact hG_comp.mul_bdd (measurable_complexTilt B M.hd ξ t).aestronglyMeasurable
        (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B M.hd ξ t ω))
    simp_rw [sub_mul]
    rw [integral_sub hf_P hG_P, hL, hR]
    simp_rw [integral_paperSig2_eq_condSigPoly B M.hd ht0.le _ ξ, sub_self]
  -- Apply Fourier uniqueness (`ae_eq_of_fourier_zero_gaussianReal`) and pass from `γ` to `volume`
  have hae_γ : ∀ᵐ x : ℝ ∂γ, G x = (f x : ℂ) :=
    ae_eq_of_fourier_zero_gaussianReal ht0 (hf_int_γ.sub hG_int_γ) hfourier
  have hae_vol : ∀ᵐ x : ℝ ∂volume, G x = (f x : ℂ) := by
    rw [show γ = volume.withDensity (gaussianPDF 0 (Real.toNNReal t)) from gaussianReal_of_var_ne_zero 0 hv_ne,
      ae_withDensity_iff (measurable_gaussianPDF 0 _)] at hae_γ
    filter_upwards [hae_γ] with x hx
    exact hx (gaussianPDF_pos 0 hv_ne x).ne'
  exact ⟨G, Kphi * C₀, hG_diff, mul_nonneg hKphi0 hC₀0, hG_bd, hae_vol⟩

end SignatureVolatility

module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1PosLe
public import SignatureVolatility.ItoCalculusKit.CrossVariation
public import SignatureVolatility.ItoCalculusKit.EvenTransform
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# B2. Quartic lower bound on `log v₁`

Jensen's inequality gives `𝔼[Φ] ≤ log v₁`. The mean `𝔼[Φ]` is evaluated by
Fubini and the Gaussian moments of `W_r`, yielding the exact identity
`𝔼[Φ(x, s₀)] = -½(s₀ x⁴ + 3 s₀² x² + s₀³)` at `s₀ = T/2`. The polynomial
bound `-C(1+|x|⁴) ≤ log v₁` follows at once.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma iteratedDeriv_four_exp_half_sq :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 3 := by
  have hd1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_exp (by fun_prop)]
    have : deriv (fun t : ℝ => t ^ 2 / 2) t = t := by
      rw [deriv_div_const]
      simp
    rw [this]
    ring
  have hd2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_id'', hd1]
    ring
  have hd3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hd1]
    have : deriv (fun t : ℝ => 1 + t ^ 2) t = 2 * t := by simp
    rw [this]
    ring
  have hd4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hd1]
    have : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
      have h1 : HasDerivAt (fun s : ℝ => 3 * s) 3 t := by
        simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
      have h2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
        simpa [pow_two] using hasDerivAt_pow 3 t
      exact (h1.add h2).deriv
    rw [this]
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero, hd1, hd2, hd3, hd4]
  simp [Real.exp_zero]

private lemma gaussMoment_two : gaussMoment 2 = 3 := by
  have h0 : 0 ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp [integrableExpSet_fun_id_gaussianReal]
  have hmom : gaussMoment 2 =
      iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
    rw [gaussMoment, show (2 * 2 : ℕ) = 4 from rfl]
    have h := iteratedDeriv_mgf_zero h0 4
    simpa [Pi.pow_apply] using h.symm
  have harg (t : ℝ) : (0 : ℝ) * t + (1 : NNReal) * t ^ 2 / 2 = t ^ 2 / 2 := by
    rw [NNReal.coe_one]
    ring
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
    funext t
    rw [mgf_fun_id_gaussianReal]
    change Real.exp (0 * t + (1 : NNReal) * t ^ 2 / 2) = Real.exp (t ^ 2 / 2)
    rw [harg t]
  rw [hmom, hmgf, iteratedDeriv_four_exp_half_sq]

private lemma integral_pow_odd_gaussianReal_zero (v : ℝ≥0) (k : ℕ) :
    ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) = 0 := by
  have hLp : MemLp (id : ℝ → ℝ) (2 * k + 1 : ℕ) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := v) ((2 * k + 1 : ℕ) : ℝ≥0∞)
      (ENNReal.natCast_ne_top _)
  have hnorm : Integrable (fun y : ℝ => |y| ^ (2 * k + 1)) (gaussianReal 0 v) := by
    simpa [Real.norm_eq_abs] using hLp.integrable_norm_pow (by simp)
  have hint : Integrable (fun y : ℝ => y ^ (2 * k + 1)) (gaussianReal 0 v) :=
    hnorm.mono' (by fun_prop) (ae_of_all _ fun y => by simp)
  have hsym : (gaussianReal 0 v).map (fun y => -y) = gaussianReal 0 v := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
  have hμ : AEStronglyMeasurable (fun y : ℝ => y ^ (2 * k + 1))
      ((gaussianReal 0 v).map Neg.neg) := by
    rw [hsym]; exact hint.aestronglyMeasurable
  have hmap : ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) =
      ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) := by
    calc ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v)
        = ∫ y, y ^ (2 * k + 1) ∂((gaussianReal 0 v).map fun y => -y) :=
          congrArg (fun ν => ∫ y, y ^ (2 * k + 1) ∂ν) hsym.symm
      _ = ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) :=
          integral_map (G := ℝ) measurable_neg.aemeasurable hμ
  have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
  have hpow : ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) =
      ∫ y, -(y ^ (2 * k + 1)) ∂(gaussianReal 0 v) :=
    integral_congr_ae (ae_of_all _ fun y => Odd.neg_pow hodd y)
  have hneg : ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) =
      -(∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v)) := by
    calc ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v)
        = ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) := hmap
      _ = ∫ y, -(y ^ (2 * k + 1)) ∂(gaussianReal 0 v) := hpow
      _ = -∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) :=
          integral_neg (fun y : ℝ => y ^ (2 * k + 1))
  linarith

private lemma W_eq_wnnIncr_zero {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ}
    (_hr : 0 ≤ r) (ω : Ω) :
    MultiBrownian.W B r ω k = wnnIncr B k 0 r ω := by
  simp only [wnnIncr, MultiBrownian.W, reindexProcessFin, toNNRealTime, Real.toNNReal_zero]
  rw [B.Wnn_zero, sub_zero]

private lemma hasLaw_W {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ} (hr : 0 ≤ r) :
    HasLaw (fun ω => MultiBrownian.W B r ω k) (gaussianReal 0 (Real.toNNReal r)) P := by
  convert hasLaw_wnnIncr B k le_rfl hr using 1
  · funext ω; exact W_eq_wnnIncr_zero B k hr ω
  · rw [sub_zero]

private lemma integral_W {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ} (hr : 0 ≤ r) :
    ∫ ω, MultiBrownian.W B r ω k ∂P = 0 := by
  simp_rw [W_eq_wnnIncr_zero B k hr]
  exact integral_wnnIncr B k le_rfl hr

private lemma integral_W_sq {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ} (hr : 0 ≤ r) :
    ∫ ω, MultiBrownian.W B r ω k ^ 2 ∂P = r := by
  simp_rw [W_eq_wnnIncr_zero B k hr]
  simpa using integral_wnnIncr_sq B k le_rfl hr

private lemma integral_W_pow3 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ}
    (hr : 0 ≤ r) : ∫ ω, MultiBrownian.W B r ω k ^ 3 ∂P = 0 := by
  have h := (hasLaw_W B k hr).integral_comp (f := fun y : ℝ => y ^ 3)
    (measurable_id.pow_const 3).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, show (3 : ℕ) = 2 * 1 + 1 from rfl]
  exact integral_pow_odd_gaussianReal_zero _ 1

private lemma integral_W_pow4 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ}
    (hr : 0 ≤ r) : ∫ ω, MultiBrownian.W B r ω k ^ 4 ∂P = 3 * r ^ 2 := by
  have h := integral_wnnIncr_pow_even B k 2 le_rfl hr
  simp only [gaussMoment_two] at h
  simp_rw [W_eq_wnnIncr_zero B k hr]
  simpa using h

private lemma integrable_W_pow {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => MultiBrownian.W B r ω k ^ n) P := by
  have hLp : MemLp (id : ℝ → ℝ) n (gaussianReal 0 (Real.toNNReal r)) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := Real.toNNReal r) (n : ℝ≥0∞)
      (ENNReal.natCast_ne_top _)
  by_cases hn : n = 0
  · subst hn; exact integrable_const _
  have hnorm : Integrable (fun y : ℝ => |y| ^ n) (gaussianReal 0 (Real.toNNReal r)) := by
    simpa [Real.norm_eq_abs] using hLp.integrable_norm_pow hn
  have hy : Integrable (fun y : ℝ => y ^ n) (gaussianReal 0 (Real.toNNReal r)) :=
    hnorm.mono' (by fun_prop) (ae_of_all _ fun y => by simp)
  exact (hasLaw_W B k hr).integrable_comp hy

private lemma integrable_addW_pow {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    Integrable (fun ω => (x + MultiBrownian.W B r ω k) ^ n) P := by
  have hex : (fun ω => (x + MultiBrownian.W B r ω k) ^ n) =
      fun ω => ∑ m ∈ Finset.range (n + 1),
        (x ^ m * (n.choose m : ℝ)) * MultiBrownian.W B r ω k ^ (n - m) := by
    funext ω
    simp only [add_pow]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hex]
  exact integrable_finsetSum _ fun m _ =>
    (integrable_W_pow B k (n - m) hr).const_mul (x ^ m * (n.choose m : ℝ))


omit [IsProbabilityMeasure P] in
private lemma integral_add₃ {f0 f1 f2 f3 : Ω → ℝ}
    (I0 : Integrable f0 P) (I1 : Integrable f1 P) (I2 : Integrable f2 P)
    (I3 : Integrable f3 P) :
    ∫ ω, f0 ω + f1 ω + f2 ω + f3 ω ∂P =
      ∫ ω, f0 ω ∂P + ∫ ω, f1 ω ∂P + ∫ ω, f2 ω ∂P + ∫ ω, f3 ω ∂P := by
  have I01 : Integrable (fun ω => f0 ω + f1 ω) P := I0.add I1
  have I012 : Integrable (fun ω => f0 ω + f1 ω + f2 ω) P := I01.add I2
  rw [integral_add I012 I3, integral_add I01 I2, integral_add I0 I1]

omit [IsProbabilityMeasure P] in
private lemma integral_add₄ {f0 f1 f2 f3 f4 : Ω → ℝ}
    (I0 : Integrable f0 P) (I1 : Integrable f1 P) (I2 : Integrable f2 P)
    (I3 : Integrable f3 P) (I4 : Integrable f4 P) :
    ∫ ω, f0 ω + f1 ω + f2 ω + f3 ω + f4 ω ∂P =
      ∫ ω, f0 ω ∂P + ∫ ω, f1 ω ∂P + ∫ ω, f2 ω ∂P + ∫ ω, f3 ω ∂P +
        ∫ ω, f4 ω ∂P := by
  have I01 : Integrable (fun ω => f0 ω + f1 ω) P := I0.add I1
  have I012 : Integrable (fun ω => f0 ω + f1 ω + f2 ω) P := I01.add I2
  have I0123 : Integrable (fun ω => f0 ω + f1 ω + f2 ω + f3 ω) P := I012.add I3
  rw [integral_add I0123 I4, integral_add I012 I3, integral_add I01 I2, integral_add I0 I1]

private lemma integral_addW_pow3 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ}
    (hr : 0 ≤ r) (x : ℝ) :
    ∫ ω, (x + MultiBrownian.W B r ω k) ^ 3 ∂P = x ^ 3 + 3 * x * r := by
  have I0 : Integrable (fun _ : Ω => x ^ 3) P := integrable_const _
  have hW1 : Integrable (fun ω => MultiBrownian.W B r ω k) P :=
    (integrable_W_pow B k 1 hr).congr (ae_of_all _ fun ω => pow_one _)
  have I1 : Integrable (fun ω => 3 * x ^ 2 * MultiBrownian.W B r ω k) P :=
    hW1.const_mul _
  have I2 : Integrable (fun ω => 3 * x * MultiBrownian.W B r ω k ^ 2) P :=
    (integrable_W_pow B k 2 hr).const_mul _
  have I3 : Integrable (fun ω => MultiBrownian.W B r ω k ^ 3) P :=
    integrable_W_pow B k 3 hr
  have hcongr : (fun ω => (x + MultiBrownian.W B r ω k) ^ 3) =ᵐ[P]
      fun ω => x ^ 3 + 3 * x ^ 2 * MultiBrownian.W B r ω k +
        3 * x * MultiBrownian.W B r ω k ^ 2 + MultiBrownian.W B r ω k ^ 3 :=
    ae_of_all _ fun ω => by ring
  rw [integral_congr_ae hcongr, integral_add₃ I0 I1 I2 I3, integral_const,
    integral_const_mul, integral_const_mul, integral_W B k hr, integral_W_sq B k hr,
    integral_W_pow3 B k hr]
  simp

private lemma integral_addW_pow4 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ}
    (hr : 0 ≤ r) (x : ℝ) :
    ∫ ω, (x + MultiBrownian.W B r ω k) ^ 4 ∂P = x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2 := by
  have I0 : Integrable (fun _ : Ω => x ^ 4) P := integrable_const _
  have hW1 : Integrable (fun ω => MultiBrownian.W B r ω k) P :=
    (integrable_W_pow B k 1 hr).congr (ae_of_all _ fun ω => pow_one _)
  have I1 : Integrable (fun ω => 4 * x ^ 3 * MultiBrownian.W B r ω k) P :=
    hW1.const_mul _
  have I2 : Integrable (fun ω => 6 * x ^ 2 * MultiBrownian.W B r ω k ^ 2) P :=
    (integrable_W_pow B k 2 hr).const_mul _
  have I3 : Integrable (fun ω => 4 * x * MultiBrownian.W B r ω k ^ 3) P :=
    (integrable_W_pow B k 3 hr).const_mul _
  have I4 : Integrable (fun ω => MultiBrownian.W B r ω k ^ 4) P :=
    integrable_W_pow B k 4 hr
  have hcongr : (fun ω => (x + MultiBrownian.W B r ω k) ^ 4) =ᵐ[P]
      fun ω => x ^ 4 + 4 * x ^ 3 * MultiBrownian.W B r ω k +
        6 * x ^ 2 * MultiBrownian.W B r ω k ^ 2 +
        4 * x * MultiBrownian.W B r ω k ^ 3 + MultiBrownian.W B r ω k ^ 4 :=
    ae_of_all _ fun ω => by ring
  rw [integral_congr_ae hcongr, integral_add₄ I0 I1 I2 I3 I4, integral_const,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_W B k hr,
    integral_W_sq B k hr, integral_W_pow3 B k hr, integral_W_pow4 B k hr]
  simp

private lemma continuous_W_coord_logb {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (ω : Ω) :
    Continuous fun t : ℝ => MultiBrownian.W B t ω k :=
  (B.pathContinuous k ω).comp continuous_real_toNNReal

private lemma measurable_uncurry_addW_pow {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    (n : ℕ) (x : ℝ) :
    Measurable fun p : ℝ × Ω => (x + MultiBrownian.W B p.1 p.2 k) ^ n :=
  ((measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_W_coord_logb B k ω) (fun r => MultiBrownian.W_meas B r k)).const_add
    x).pow_const n

private lemma integrable_uncurry_addW_pow4 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Integrable (fun p : ℝ × Ω => (x + MultiBrownian.W B p.1 p.2 k) ^ 4)
      ((volume.restrict (uIoc 0 s)).prod P) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × Ω => (x + MultiBrownian.W B p.1 p.2 k) ^ 4)
      ((volume.restrict (uIoc 0 s)).prod P) :=
    (measurable_uncurry_addW_pow B k 4 x).aestronglyMeasurable
  rw [uIoc_of_le hs] at hmeas ⊢
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr =>
      integrable_addW_pow B k 4 hr.1.le x
  · have hp : IntegrableOn (fun r : ℝ => x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2)
        (Ioc 0 s) volume :=
      ((by fun_prop : Continuous fun r : ℝ =>
          x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
    have heq : (fun r : ℝ => x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2) =ᵐ[volume.restrict (Ioc 0 s)]
        fun r => ∫ ω, ‖(x + MultiBrownian.W B r ω k) ^ 4‖ ∂P :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => by
        change x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2 =
          ∫ ω, ‖(x + MultiBrownian.W B r ω k) ^ 4‖ ∂P
        have hnn : ∫ ω, ‖(x + MultiBrownian.W B r ω k) ^ 4‖ ∂P =
            ∫ ω, (x + MultiBrownian.W B r ω k) ^ 4 ∂P :=
          integral_congr_ae <| ae_of_all _ fun ω =>
            Real.norm_of_nonneg (by
              have : (x + MultiBrownian.W B r ω k) ^ 4 =
                  ((x + MultiBrownian.W B r ω k) ^ 2) ^ 2 := by ring
              rw [this]; exact sq_nonneg _)
        rw [hnn, integral_addW_pow4 B k hr.1.le x]
    exact (hp.congr_fun_ae heq).integrable

private lemma integral_abs_W_le_sqrt {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {r : ℝ}
    (hr : 0 ≤ r) :
    ∫ ω, |MultiBrownian.W B r ω k| ∂P ≤ Real.sqrt r := by
  have h2 : Integrable (fun ω => MultiBrownian.W B r ω k ^ 2) P :=
    integrable_W_pow B k 2 hr
  have hLpW : MemLp (fun ω => MultiBrownian.W B r ω k) 2 P :=
    memLp_even_of_integrable_pow (q := 1)
      (MultiBrownian.W_meas B r k).aestronglyMeasurable (by simpa using h2)
  have hLp : MemLp (fun ω => |MultiBrownian.W B r ω k|) 2 P := hLpW.abs
  have hvar := variance_eq_sub hLp
  have hnn : 0 ≤ variance (fun ω => |MultiBrownian.W B r ω k|) P := variance_nonneg _ _
  have heq : ∫ ω, ((fun ω => |MultiBrownian.W B r ω k|) ^ 2) ω ∂P =
      ∫ ω, |MultiBrownian.W B r ω k| ^ 2 ∂P := by
    simp [Pi.pow_apply]
  have hsq : (∫ ω, |MultiBrownian.W B r ω k| ∂P) ^ 2 ≤
      ∫ ω, |MultiBrownian.W B r ω k| ^ 2 ∂P := by
    linarith [hvar, hnn, heq]
  have hW2 : ∫ ω, |MultiBrownian.W B r ω k| ^ 2 ∂P = r := by
    simp only [sq_abs]; exact integral_W_sq B k hr
  rw [hW2] at hsq
  have habs_nn : 0 ≤ ∫ ω, |MultiBrownian.W B r ω k| ∂P :=
    integral_nonneg fun _ => abs_nonneg _
  exact (Real.le_sqrt habs_nn hr).mpr hsq

private lemma measurable_uncurry_addW {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (x : ℝ) :
    Measurable fun p : ℝ × Ω => x + MultiBrownian.W B p.1 p.2 k :=
  (measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_W_coord_logb B k ω) (fun r => MultiBrownian.W_meas B r k)).const_add x

private lemma integrable_uncurry_addW {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Integrable (fun p : ℝ × Ω => x + MultiBrownian.W B p.1 p.2 k)
      ((volume.restrict (uIoc 0 s)).prod P) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × Ω => x + MultiBrownian.W B p.1 p.2 k)
      ((volume.restrict (uIoc 0 s)).prod P) :=
    (measurable_uncurry_addW B k x).aestronglyMeasurable
  rw [uIoc_of_le hs] at hmeas ⊢
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr =>
      (integrable_addW_pow B k 1 hr.1.le x).congr (ae_of_all _ fun ω => pow_one _)
  · have hsm : StronglyMeasurable fun r : ℝ =>
        ∫ ω, ‖x + MultiBrownian.W B r ω k‖ ∂P :=
      (measurable_uncurry_addW B k x).norm.stronglyMeasurable.integral_prod_right'
    have hp : IntegrableOn (fun r : ℝ => |x| + Real.sqrt r) (Ioc 0 s) volume := by
      have hc : ContinuousOn (fun r : ℝ => |x| + Real.sqrt r) (Icc 0 s) :=
        continuousOn_const.add (Real.continuous_sqrt.continuousOn)
      exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    refine Integrable.mono' hp.integrable hsm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := hr.1.le
    have hnn : 0 ≤ ∫ ω, ‖x + MultiBrownian.W B r ω k‖ ∂P :=
      integral_nonneg fun _ => norm_nonneg _
    have hW : Integrable (fun ω => MultiBrownian.W B r ω k) P :=
      (integrable_W_pow B k 1 hr0).congr (ae_of_all _ fun ω => pow_one _)
    have h1 : Integrable (fun _ : Ω => |x|) P := integrable_const _
    have h2 : Integrable (fun ω => |MultiBrownian.W B r ω k|) P := hW.abs
    have hxW : Integrable (fun ω => x + MultiBrownian.W B r ω k) P :=
      (integrable_addW_pow B k 1 hr0 x).congr (ae_of_all _ fun ω => pow_one _)
    have Isum : Integrable (fun ω => |x| + |MultiBrownian.W B r ω k|) P := by
      simpa [Pi.add_apply] using h1.add h2
    have htri : ∫ ω, |x + MultiBrownian.W B r ω k| ∂P ≤
        ∫ ω, |x| + |MultiBrownian.W B r ω k| ∂P :=
      integral_mono hxW.abs Isum fun ω => abs_add_le _ _
    have hsum : ∫ ω, |x| + |MultiBrownian.W B r ω k| ∂P =
        ∫ ω, |x| ∂P + ∫ ω, |MultiBrownian.W B r ω k| ∂P :=
      integral_add h1 h2
    have hle : ∫ ω, ‖x + MultiBrownian.W B r ω k‖ ∂P ≤ |x| + Real.sqrt r := by
      simp only [Real.norm_eq_abs]
      refine htri.trans ?_
      rw [hsum, integral_const]
      simp only [smul_eq_mul, probReal_univ]
      linarith [integral_abs_W_le_sqrt B k hr0]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle

private lemma integral_interval_addW {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ∫ ω, (∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω k) ∂P = x * s := by
  have hf := integrable_uncurry_addW B k hs x
  have hswap := intervalIntegral_integral_swap (μ := P) (a := 0) (b := s)
    (f := fun r ω => x + MultiBrownian.W B r ω k) hf
  rw [← hswap]
  have hpt : ∀ r : ℝ, 0 ≤ r →
      ∫ ω, x + MultiBrownian.W B r ω k ∂P = x := by
    intro r hr
    have hW : Integrable (fun ω => MultiBrownian.W B r ω k) P :=
      (integrable_W_pow B k 1 hr).congr (ae_of_all _ fun ω => pow_one _)
    rw [integral_add (integrable_const _) hW, integral_const, integral_W B k hr]
    simp
  have : (fun r : ℝ => ∫ ω, x + MultiBrownian.W B r ω k ∂P) =ᵐ[volume.restrict (uIoc 0 s)]
      fun _ => x := by
    rw [uIoc_of_le hs]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hpt r hr.1.le
  have hI : ∫ r in (0 : ℝ)..s, ∫ ω, x + MultiBrownian.W B r ω k ∂P =
      ∫ r in (0 : ℝ)..s, x := by
    simp_rw [intervalIntegral.integral_of_le hs]
    rw [uIoc_of_le hs] at this
    exact integral_congr_ae this
  rw [hI, intervalIntegral.integral_const, smul_eq_mul]
  ring

private lemma integral_interval_addW_pow4 {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ∫ ω, (∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω k) ^ 4) ∂P =
      s * x ^ 4 + 3 * s ^ 2 * x ^ 2 + s ^ 3 := by
  have hf := integrable_uncurry_addW_pow4 B k hs x
  have hswap := intervalIntegral_integral_swap (μ := P) (a := 0) (b := s)
    (f := fun r ω => (x + MultiBrownian.W B r ω k) ^ 4) hf
  rw [← hswap]
  have hpt : ∀ r : ℝ, 0 ≤ r →
      ∫ ω, (x + MultiBrownian.W B r ω k) ^ 4 ∂P = x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2 :=
    fun r hr => integral_addW_pow4 B k hr x
  have : (fun r : ℝ => ∫ ω, (x + MultiBrownian.W B r ω k) ^ 4 ∂P) =ᵐ[volume.restrict (uIoc 0 s)]
      fun r => x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2 := by
    rw [uIoc_of_le hs]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hpt r hr.1.le
  have hI : ∫ r in (0 : ℝ)..s, ∫ ω, (x + MultiBrownian.W B r ω k) ^ 4 ∂P =
      ∫ r in (0 : ℝ)..s, x ^ 4 + 6 * x ^ 2 * r + 3 * r ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le hs]
    rw [uIoc_of_le hs] at this
    exact integral_congr_ae this
  have hid : IntervalIntegrable (fun r : ℝ => r) volume 0 s :=
    continuous_id.intervalIntegrable _ _
  have hsqI : IntervalIntegrable (fun r : ℝ => r ^ 2) volume 0 s :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hcst : IntervalIntegrable (fun _ : ℝ => x ^ 4) volume 0 s :=
    continuous_const.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun r : ℝ => 6 * x ^ 2 * r) volume 0 s :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hquad : IntervalIntegrable (fun r : ℝ => 3 * r ^ 2) volume 0 s :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have h_id : ∫ r in (0 : ℝ)..s, r = s ^ 2 / 2 := by
    have hderiv : ∀ r ∈ Ioo (0 : ℝ) s, HasDerivAt (fun t : ℝ => t ^ 2 / 2) r r := fun r _ => by
      convert (hasDerivAt_pow 2 r).div_const 2 using 1; ring_nf
    have hcont : ContinuousOn (fun t : ℝ => t ^ 2 / 2) (Icc 0 s) := by fun_prop
    simp [zero_pow]
  have h_sq : ∫ r in (0 : ℝ)..s, r ^ 2 = s ^ 3 / 3 := by
    have hderiv : ∀ r ∈ Ioo (0 : ℝ) s, HasDerivAt (fun t : ℝ => t ^ 3 / 3) (r ^ 2) r := fun r _ => by
      convert (hasDerivAt_pow 3 r).div_const 3 using 1; ring_nf
    have hcont : ContinuousOn (fun t : ℝ => t ^ 3 / 3) (Icc 0 s) := by fun_prop
    simpa [zero_pow, zero_div] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hcont hderiv hsqI
  rw [hI, intervalIntegral.integral_add (hcst.add hlin) hquad,
    intervalIntegral.integral_add hcst hlin, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h_id, h_sq]
  simp [smul_eq_mul]; ring

private lemma integrable_exponent {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    Integrable (fun ω => counterexampleV1Exponent B hd s x ω) P := by
  have hcub := (integrable_addW_pow B ⟨0, hd⟩ 3 hs x).sub (integrable_const (x ^ 3))
  have hcub' := hcub.const_mul (1 / 3 : ℝ)
  have hI : Integrable (fun ω => ∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω ⟨0, hd⟩) P := by
    have hf := integrable_uncurry_addW B ⟨0, hd⟩ hs x
    rw [uIoc_of_le hs] at hf
    simpa [intervalIntegral.integral_of_le hs] using hf.integral_prod_right
  have hQ : Integrable (fun ω => ∫ r in (0 : ℝ)..s,
      (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4) P := by
    have hf := integrable_uncurry_addW_pow4 B ⟨0, hd⟩ hs x
    rw [uIoc_of_le hs] at hf
    simpa [intervalIntegral.integral_of_le hs] using hf.integral_prod_right
  simp only [counterexampleV1Exponent]
  exact (hcub'.sub hI).sub (hQ.const_mul (1 / 2 : ℝ))

private lemma integral_exponent_eq {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ∫ ω, counterexampleV1Exponent B hd s x ω ∂P =
      -(1 / 2 : ℝ) * (s * x ^ 4 + 3 * s ^ 2 * x ^ 2 + s ^ 3) := by
  have hcub := (integrable_addW_pow B ⟨0, hd⟩ 3 hs x).sub (integrable_const (x ^ 3))
  have hcub' := hcub.const_mul (1 / 3 : ℝ)
  have hI : Integrable (fun ω => ∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω ⟨0, hd⟩) P := by
    have hf := integrable_uncurry_addW B ⟨0, hd⟩ hs x
    rw [uIoc_of_le hs] at hf
    simpa [intervalIntegral.integral_of_le hs] using hf.integral_prod_right
  have hQ : Integrable (fun ω => ∫ r in (0 : ℝ)..s,
      (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4) P := by
    have hf := integrable_uncurry_addW_pow4 B ⟨0, hd⟩ hs x
    rw [uIoc_of_le hs] at hf
    simpa [intervalIntegral.integral_of_le hs] using hf.integral_prod_right
  simp only [counterexampleV1Exponent]
  rw [integral_sub, integral_sub, integral_const_mul, integral_const_mul, integral_sub,
    integral_addW_pow3 B ⟨0, hd⟩ hs x, integral_const, integral_interval_addW B ⟨0, hd⟩ hs x,
    integral_interval_addW_pow4 B ⟨0, hd⟩ hs x]
  · simp; ring
  · exact integrable_addW_pow B ⟨0, hd⟩ 3 hs x
  · exact integrable_const _
  · exact hcub'
  · exact hI
  · exact (hcub'.sub hI)
  · exact hQ.const_mul _

/-- The mean of the exponent is the explicit quartic `-½(s x⁴ + 3 s² x² + s³)`,
and Jensen gives the same lower bound on `log v₁`. -/
lemma counterexampleV1_log_bound_explicit (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (x : ℝ) :
    -(1 / 2 : ℝ) * ((M.T / 2) * x ^ 4 + 3 * (M.T / 2) ^ 2 * x ^ 2 + (M.T / 2) ^ 3) ≤
      Real.log (counterexampleV1AtHalf M B x) := by
  set s₀ : ℝ := M.T / 2
  have hs : 0 ≤ s₀ := div_nonneg M.hT.le (by norm_num)
  have hv := counterexampleV1_pos_le M B x
  have hint_exp : Integrable (fun ω =>
      Real.exp (counterexampleV1Exponent B M.hd s₀ x ω)) P := by
    by_contra h
    have : counterexampleV1AtHalf M B x = 0 := by
      simpa [counterexampleV1AtHalf, counterexampleV1, s₀] using integral_undef h
    linarith [hv.1]
  have hint_phi : Integrable (fun ω => counterexampleV1Exponent B M.hd s₀ x ω) P :=
    integrable_exponent B M.hd hs x
  have hjensen : ∫ ω, counterexampleV1Exponent B M.hd s₀ x ω ∂P ≤
      Real.log (∫ ω, Real.exp (counterexampleV1Exponent B M.hd s₀ x ω) ∂P) := by
    have h := ConvexOn.map_integral_le (μ := P) convexOn_exp
      Real.continuous_exp.continuousOn
      isClosed_univ (ae_of_all _ fun _ => mem_univ _) hint_phi hint_exp
    rw [← Real.log_exp (∫ ω, counterexampleV1Exponent B M.hd s₀ x ω ∂P)]
    exact Real.log_le_log (Real.exp_pos _) h
  have hE : ∫ ω, counterexampleV1Exponent B M.hd s₀ x ω ∂P =
      -(1 / 2 : ℝ) * (s₀ * x ^ 4 + 3 * s₀ ^ 2 * x ^ 2 + s₀ ^ 3) :=
    integral_exponent_eq B M.hd hs x
  simpa [counterexampleV1AtHalf, counterexampleV1, s₀, hE] using hjensen

/-- **B2.** Polynomial lower bound on `log v₁`:
`∃ C ≥ 0, ∀ x, -C (1 + |x|^4) ≤ log (v₁ x)`. -/
lemma counterexampleV1_log_bound (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      -C * (1 + |x| ^ 4) ≤ Real.log (counterexampleV1AtHalf M B x) := by
  set s₀ : ℝ := M.T / 2
  have hs : 0 ≤ s₀ := div_nonneg M.hT.le (by norm_num)
  set C : ℝ := (s₀ + 3 * s₀ ^ 2 + s₀ ^ 3) / 2
  refine ⟨C, div_nonneg (by positivity) (by norm_num), fun x => ?_⟩
  have hexp := counterexampleV1_log_bound_explicit M B x
  have hx2 : x ^ 2 ≤ 1 + |x| ^ 4 := by
    rw [show |x| ^ 4 = (x ^ 2) ^ 2 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]]
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hx4 : x ^ 4 = |x| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hpoly : s₀ * x ^ 4 + 3 * s₀ ^ 2 * x ^ 2 + s₀ ^ 3 ≤
      (s₀ + 3 * s₀ ^ 2 + s₀ ^ 3) * (1 + |x| ^ 4) := by
    have h1 : 0 ≤ 1 + |x| ^ 4 := by positivity
    have hs2 : 0 ≤ s₀ ^ 2 := sq_nonneg s₀
    have hs3 : 0 ≤ s₀ ^ 3 := pow_nonneg hs 3
    have hA : s₀ * |x| ^ 4 ≤ s₀ * (1 + |x| ^ 4) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hs
    have hB : s₀ ^ 3 ≤ s₀ ^ 3 * (1 + |x| ^ 4) :=
      le_mul_of_one_le_right hs3 (le_add_of_nonneg_right (by positivity))
    calc s₀ * x ^ 4 + 3 * s₀ ^ 2 * x ^ 2 + s₀ ^ 3
        = s₀ * |x| ^ 4 + 3 * s₀ ^ 2 * x ^ 2 + s₀ ^ 3 := by rw [hx4]
      _ ≤ s₀ * |x| ^ 4 + 3 * s₀ ^ 2 * (1 + |x| ^ 4) + s₀ ^ 3 := by
          nlinarith [hx2, hs2]
      _ ≤ s₀ * (1 + |x| ^ 4) + 3 * s₀ ^ 2 * (1 + |x| ^ 4) + s₀ ^ 3 * (1 + |x| ^ 4) := by
          linarith [hA, hB]
      _ = (s₀ + 3 * s₀ ^ 2 + s₀ ^ 3) * (1 + |x| ^ 4) := by ring
  have : -C * (1 + |x| ^ 4) ≤
      -(1 / 2 : ℝ) * (s₀ * x ^ 4 + 3 * s₀ ^ 2 * x ^ 2 + s₀ ^ 3) := by
    have hC : C = (s₀ + 3 * s₀ ^ 2 + s₀ ^ 3) / 2 := rfl
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hmul : (1 / 2 : ℝ) * (s₀ * x ^ 4 + 3 * s₀ ^ 2 * x ^ 2 + s₀ ^ 3) ≤
        C * (1 + |x| ^ 4) := by
      have hrhs : C * (1 + |x| ^ 4) =
          (1 / 2 : ℝ) * ((s₀ + 3 * s₀ ^ 2 + s₀ ^ 3) * (1 + |x| ^ 4)) := by
        rw [hC]; ring
      rw [hrhs]
      exact mul_le_mul_of_nonneg_left hpoly hhalf
    linarith [hmul]
  simp only [s₀] at hexp this
  exact this.trans hexp

end SignatureVolatility

module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.BrownianScalingShiftedExponent
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# B3a. Deterministic Cameron–Martin shift for a C² path with `h(0) = 0`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped ENNReal NNReal

set_option maxHeartbeats 800000

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Pathwise Doléans exponent along an arbitrary continuous path. -/
noncomputable def pathExponent (w : ℝ → ℝ) (x s : ℝ) : ℝ :=
  (1 / 3 : ℝ) * ((x + w s) ^ 3 - x ^ 3)
    - (∫ r in (0 : ℝ)..s, x + w r)
    - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s, (x + w r) ^ 4)

/-! ### Helper 1: Elementary L² Vitali (no `.min` / `.measurable` on `AEStronglyMeasurable`!) -/

private lemma tendsto_integral_of_ae_tendsto_of_L2_bdd_real
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n, MemLp (f n) 2 P) (hg : MemLp g 2 P)
    (hbd : ∀ n, ∫ ω, (f n ω - g ω) ^ 2 ∂P ≤ M)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, g ω ∂P)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := 2 * (M + 1) / ε
  have hR : 0 < R := by positivity
  have hmin_asm : ∀ n, AEStronglyMeasurable (fun ω => min |f n ω - g ω| R) P := fun n =>
    (continuous_id.min continuous_const).comp_aestronglyMeasurable
      ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm
  have hmin_lim : Tendsto (fun n => ∫ ω, min |f n ω - g ω| R ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => R)
      hmin_asm (integrable_const R)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (le_min (abs_nonneg _) hR.le)]; exact min_le_right _ _)
      (by
        filter_upwards [hae] with ω hω
        have h0 : Tendsto (fun n => |f n ω - g ω|) atTop (𝓝 0) := by
          simpa [sub_self] using (hω.sub (tendsto_const_nhds (x := g ω))).abs
        have hmin0 : Tendsto (fun n => min |f n ω - g ω| R) atTop (𝓝 0) := by
          simpa [min_eq_left hR.le] using h0.min (tendsto_const_nhds (x := R))
        exact hmin0)
    simpa using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmin_lim) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hMR : M / R < ε / 2 := by simp only [R]; field_simp; linarith
  have hmin_lt : ∫ ω, min |f n ω - g ω| R ∂P < ε / 2 := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => le_min (abs_nonneg _) hR.le)] at h
    exact h
  have hpt : ∀ ω, |f n ω - g ω| ≤ min |f n ω - g ω| R + (f n ω - g ω) ^ 2 / R := fun ω => by
    rcases le_total |f n ω - g ω| R with hle | hge
    · rw [min_eq_left hle]; linarith [div_nonneg (sq_nonneg (f n ω - g ω)) hR.le]
    · rw [min_eq_right hge]
      have h1 : |f n ω - g ω| ≤ (f n ω - g ω) ^ 2 / R := by
        rw [le_div_iff₀ hR, ← sq_abs, sq]; exact mul_le_mul_of_nonneg_left hge (abs_nonneg _)
      linarith
  have hi_min : Integrable (fun ω => min |f n ω - g ω| R) P :=
    (integrable_const R).mono' (hmin_asm n) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (le_min (abs_nonneg _) hR.le)]; exact min_le_right _ _)
  have hi_sq : Integrable (fun ω => (f n ω - g ω) ^ 2 / R) P :=
    ((hf n).sub hg).integrable_sq.div_const R
  rw [Real.dist_eq, ← integral_sub ((hf n).integrable one_le_two) (hg.integrable one_le_two)]
  calc |∫ ω, (f n ω - g ω) ∂P|
      ≤ ∫ ω, |f n ω - g ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (min |f n ω - g ω| R + (f n ω - g ω) ^ 2 / R) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hi_min.add hi_sq) (ae_of_all _ hpt)
    _ = (∫ ω, min |f n ω - g ω| R ∂P) + (∫ ω, (f n ω - g ω) ^ 2 ∂P) / R := by
        rw [integral_add hi_min hi_sq, integral_div]
    _ ≤ (∫ ω, min |f n ω - g ω| R ∂P) + M / R := by gcongr; exact hbd n
    _ < ε / 2 + ε / 2 := add_lt_add hmin_lt hMR
    _ = ε := add_halves ε

/-! ### Helper 2: Finite-dimensional `lintegral` Gaussian shift & product MGF (no integrability side-goals!) -/

private lemma gaussian_1D_shift_lintegral {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : ℝ, g x ∂(gaussianReal 0 v) =
      ∫⁻ x : ℝ, g (x + c) * ENNReal.ofReal (Real.exp (-(c / (v : ℝ)) * x -
        (1 / 2 : ℝ) * (c ^ 2 / (v : ℝ)))) ∂(gaussianReal 0 v) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hmR : Measurable (fun x : ℝ => g (x + c) * ENNReal.ofReal (Real.exp
      (-(c / (v : ℝ)) * x - (1 / 2 : ℝ) * (c ^ 2 / (v : ℝ))))) :=
    (hg.comp (measurable_id.add_const c)).mul (by fun_prop)
  rw [gaussianReal_of_var_ne_zero 0 hv]
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 v) hg]
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 v) hmR]
  have htrans := lintegral_add_right_eq_self (μ := volume) (fun x => gaussianPDF 0 v x * g x) c
  simp only [Pi.mul_apply]
  rw [← htrans]
  refine lintegral_congr fun x => ?_
  have hpdf : gaussianPDF 0 v (x + c) =
      gaussianPDF 0 v x * ENNReal.ofReal (Real.exp (-(c / (v : ℝ)) * x -
        (1 / 2 : ℝ) * (c ^ 2 / (v : ℝ)))) := by
    simp only [gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
    congr 1
    simp only [gaussianPDFReal_def, sub_zero]
    have hexp : Real.exp (-(x + c) ^ 2 / (2 * (v : ℝ))) =
        Real.exp (-x ^ 2 / (2 * (v : ℝ))) *
          Real.exp (-(c / (v : ℝ)) * x - (1 / 2 : ℝ) * (c ^ 2 / (v : ℝ))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hexp]; ring
  simp [Pi.mul_apply, hpdf, mul_assoc, mul_left_comm, mul_comm]

private lemma gaussian_vec_shift_lintegral {N : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (δ : Fin N → ℝ)
    {F : (Fin N → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z : Fin N → ℝ, F z ∂(Measure.pi fun _ : Fin N => gaussianReal 0 v) =
      ∫⁻ z : Fin N → ℝ, F (z + δ) *
        ENNReal.ofReal (Real.exp (-∑ k : Fin N, (δ k / (v : ℝ)) * z k -
          (1 / 2 : ℝ) * ∑ k : Fin N, δ k ^ 2 / (v : ℝ)))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 v) := by
  induction N with
  | zero =>
    have h0 : ∀ z : Fin 0 → ℝ, z + δ = z := fun z => Subsingleton.elim _ _
    simp [h0]
  | succ N ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => gaussianReal 0 v) 0
    have hL : ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) =
        ∫⁻ p, F (e.symm p) ∂((gaussianReal 0 v).prod (Measure.pi fun _ : Fin N => gaussianReal 0 v)) := by
      calc ∫⁻ z, F z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v)
          = ∫⁻ z, (F ∘ e.symm) (e z) ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) := by
              refine lintegral_congr fun z => by simp [Function.comp_def]
        _ = ∫⁻ p, (F ∘ e.symm) p ∂((gaussianReal 0 v).prod
              (Measure.pi fun _ : Fin N => gaussianReal 0 v)) :=
              hmp.lintegral_comp (hF.comp e.symm.measurable)
    have hmR : Measurable (fun z : Fin (N + 1) → ℝ =>
        F (z + δ) * ENNReal.ofReal (Real.exp (-∑ k : Fin (N + 1), (δ k / (v : ℝ)) * z k -
          (1 / 2 : ℝ) * ∑ k : Fin (N + 1), δ k ^ 2 / (v : ℝ)))) :=
      (hF.comp (measurable_id.add_const δ)).mul
        (((((Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_pi_apply k)).neg).sub
          measurable_const).exp).ennreal_ofReal)
    have hR : ∫⁻ z, F (z + δ) * ENNReal.ofReal (Real.exp (-∑ k : Fin (N + 1), (δ k / (v : ℝ)) * z k -
          (1 / 2 : ℝ) * ∑ k : Fin (N + 1), δ k ^ 2 / (v : ℝ)))
        ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) =
        ∫⁻ p, F (e.symm p + δ) * ENNReal.ofReal (Real.exp (-∑ k : Fin (N + 1), (δ k / (v : ℝ)) * e.symm p k -
          (1 / 2 : ℝ) * ∑ k : Fin (N + 1), δ k ^ 2 / (v : ℝ)))
        ∂((gaussianReal 0 v).prod (Measure.pi fun _ : Fin N => gaussianReal 0 v)) := by
      set FR : (Fin (N + 1) → ℝ) → ℝ≥0∞ := fun z =>
        F (z + δ) * ENNReal.ofReal (Real.exp (-∑ k : Fin (N + 1), (δ k / (v : ℝ)) * z k -
          (1 / 2 : ℝ) * ∑ k : Fin (N + 1), δ k ^ 2 / (v : ℝ)))
      calc ∫⁻ z, FR z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v)
          = ∫⁻ z, (FR ∘ e.symm) (e z) ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) := by
              refine lintegral_congr fun z => by simp [Function.comp_def]
        _ = ∫⁻ p, (FR ∘ e.symm) p ∂((gaussianReal 0 v).prod
              (Measure.pi fun _ : Fin N => gaussianReal 0 v)) :=
              hmp.lintegral_comp (hmR.comp e.symm.measurable)
    rw [hL, hR]
    rw [lintegral_prod (fun p => F (e.symm p)) (hF.comp e.symm.measurable).aemeasurable]
    rw [lintegral_prod (fun p => F (e.symm p + δ) * ENNReal.ofReal (Real.exp
        (-∑ k : Fin (N + 1), (δ k / (v : ℝ)) * e.symm p k -
          (1 / 2 : ℝ) * ∑ k : Fin (N + 1), δ k ^ 2 / (v : ℝ))))
      (hmR.comp e.symm.measurable).aemeasurable]
    have hGmeas : Measurable (fun x : ℝ => ∫⁻ y, F (e.symm (x, y))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 v)) :=
      Measurable.lintegral_prod_right (f := fun x y => F (e.symm (x, y))) (by
        have hunc : Function.uncurry (fun x y => F (e.symm (x, y))) = F ∘ e.symm := by
          ext ⟨x, y⟩; simp [Function.uncurry, Function.comp_def]
        rw [hunc]; exact hF.comp e.symm.measurable)
    rw [gaussian_1D_shift_lintegral hv (δ 0) hGmeas]
    refine lintegral_congr fun x => ?_
    have hmFy : Measurable (fun y => F (e.symm (x + δ 0, y))) :=
      hF.comp (e.symm.measurable.comp measurable_prodMk_left)
    have hinner := ih (Fin.tail δ) (F := fun y => F (e.symm (x + δ 0, y))) hmFy
    rw [hinner]
    have hmFshift : Measurable (fun y =>
        F (e.symm (x + δ 0, y + Fin.tail δ)) *
          ENNReal.ofReal (Real.exp (-∑ j : Fin N, (Fin.tail δ j / (v : ℝ)) * y j -
            (1 / 2 : ℝ) * ∑ j : Fin N, Fin.tail δ j ^ 2 / (v : ℝ)))) :=
      (hF.comp (e.symm.measurable.comp
        (measurable_prodMk_left.comp (measurable_id.add_const (Fin.tail δ))))).mul (by fun_prop)
    rw [← lintegral_mul_const
      (ENNReal.ofReal (Real.exp (-(δ 0 / (v : ℝ)) * x - (1 / 2 : ℝ) * (δ 0 ^ 2 / (v : ℝ)))))
      hmFshift]
    refine lintegral_congr fun y => ?_
    have heq : e.symm (x + δ 0, y + Fin.tail δ) = e.symm (x, y) + δ := by
      ext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp [e, Fin.tail]
    rw [heq, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp [Fin.sum_univ_succ, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_apply, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      Fin.succAbove_zero, Fin.tail]
    ring

/-- Product MGF on `Measure.pi`: `∫⁻ z, exp(∑ (-2 (δ_k/v) z_k - δ_k²/v)) = ofReal (exp (∑ δ_k²/v))`. -/
private lemma lintegral_pi_exp_CM_sq {N : ℕ} {v : ℝ≥0} (hv : v ≠ 0) (δ : Fin N → ℝ) :
    ∫⁻ z : Fin N → ℝ, ENNReal.ofReal (Real.exp
        (∑ k : Fin N, (-2 * (δ k / (v : ℝ)) * z k - δ k ^ 2 / (v : ℝ))))
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 v) =
    ENNReal.ofReal (Real.exp (∑ k : Fin N, δ k ^ 2 / (v : ℝ))) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  induction N with
  | zero => simp
  | succ N ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) 0
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => gaussianReal 0 v) 0
    have hm : Measurable (fun z : Fin (N + 1) → ℝ => ENNReal.ofReal (Real.exp
        (∑ k : Fin (N + 1), (-2 * (δ k / (v : ℝ)) * z k - δ k ^ 2 / (v : ℝ))))) :=
      ((Finset.measurable_sum _ fun k _ => (measurable_const.mul (measurable_pi_apply k)).sub measurable_const).exp).ennreal_ofReal
    have hprod_eq : ∫⁻ z : Fin (N + 1) → ℝ, ENNReal.ofReal (Real.exp
          (∑ k : Fin (N + 1), (-2 * (δ k / (v : ℝ)) * z k - δ k ^ 2 / (v : ℝ))))
        ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) =
        ∫⁻ p : ℝ × (Fin N → ℝ),
          ENNReal.ofReal (Real.exp (-2 * (δ 0 / (v : ℝ)) * p.1 - δ 0 ^ 2 / (v : ℝ))) *
          ENNReal.ofReal (Real.exp (∑ j : Fin N, (-2 * (Fin.tail δ j / (v : ℝ)) * p.2 j - Fin.tail δ j ^ 2 / (v : ℝ))))
        ∂((gaussianReal 0 v).prod (Measure.pi fun _ : Fin N => gaussianReal 0 v)) := by
      set Fmgf : (Fin (N + 1) → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp
        (∑ k : Fin (N + 1), (-2 * (δ k / (v : ℝ)) * z k - δ k ^ 2 / (v : ℝ))))
      have hmap : ∫⁻ z, Fmgf z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) =
          ∫⁻ p, Fmgf (e.symm p) ∂((gaussianReal 0 v).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 v)) := by
        calc ∫⁻ z, Fmgf z ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v)
            = ∫⁻ z, (Fmgf ∘ e.symm) (e z) ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 v) := by
                refine lintegral_congr fun z => by simp [Function.comp_def]
          _ = ∫⁻ p, (Fmgf ∘ e.symm) p ∂((gaussianReal 0 v).prod
                (Measure.pi fun _ : Fin N => gaussianReal 0 v)) :=
                hmp.lintegral_comp (hm.comp e.symm.measurable)
      rw [hmap]
      refine lintegral_congr fun p => ?_
      simp only [Fmgf]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      rw [Fin.sum_univ_succ]
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
        Fin.cons_zero, Fin.cons_succ, Fin.tail]
    have hmgf1 : Measurable (fun x : ℝ => ENNReal.ofReal
        (Real.exp (-2 * (δ 0 / (v : ℝ)) * x - δ 0 ^ 2 / (v : ℝ)))) := by fun_prop
    have hmgfN : Measurable (fun y : Fin N → ℝ => ENNReal.ofReal (Real.exp
        (∑ j : Fin N, (-2 * (Fin.tail δ j / (v : ℝ)) * y j - Fin.tail δ j ^ 2 / (v : ℝ))))) :=
      ((Finset.measurable_sum _ fun j _ =>
        (measurable_const.mul (measurable_pi_apply j)).sub measurable_const).exp).ennreal_ofReal
    rw [hprod_eq, lintegral_prod_mul hmgf1.aemeasurable hmgfN.aemeasurable]
    rw [ih (Fin.tail δ)]
    have h1D : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-2 * (δ 0 / (v : ℝ)) * x - δ 0 ^ 2 / (v : ℝ)))
        ∂(gaussianReal 0 v) = ENNReal.ofReal (Real.exp (δ 0 ^ 2 / (v : ℝ))) := by
      have hi : Integrable (fun x : ℝ => Real.exp (-2 * (δ 0 / (v : ℝ)) * x - δ 0 ^ 2 / (v : ℝ)))
          (gaussianReal 0 v) := by
        simpa [sub_eq_add_neg, Real.exp_add] using
          (ProbabilityTheory.integrable_exp_mul_gaussianReal (-2 * (δ 0 / (v : ℝ)))).mul_const _
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)]
      congr 1
      simp_rw [sub_eq_add_neg, Real.exp_add]
      rw [integral_mul_const]
      have hmgf : ∫ x : ℝ, Real.exp (-2 * (δ 0 / (v : ℝ)) * x) ∂(gaussianReal 0 v) =
          mgf id (gaussianReal 0 v) (-2 * (δ 0 / (v : ℝ))) := rfl
      rw [hmgf, mgf_id_gaussianReal, ← Real.exp_add]
      congr 1; field_simp; ring
    rw [h1D, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Fin.sum_univ_succ]
    simp [Fin.tail]

/-! ### Helper 3: `ContDiffOn ℝ 2 h U` on open `U` ⇒ `ContinuousOn (deriv h)` and `ContinuousOn (iteratedDeriv 2 h)` -/

private lemma contDiffOn_deriv_open {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ 2 h U) :
    ContDiffOn ℝ 1 (deriv h) U ∧ ContinuousOn (iteratedDeriv 2 h) U := by
  have hdw1 : ContDiffOn ℝ 1 (derivWithin h U) U :=
    hh.derivWithin hU.uniqueDiffOn (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hd1 : ContDiffOn ℝ 1 (deriv h) U :=
    hdw1.congr fun r hr => (derivWithin_of_isOpen hU hr).symm
  have hdw2 : ContDiffOn ℝ 0 (derivWithin (deriv h) U) U :=
    hd1.derivWithin hU.uniqueDiffOn (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)
  have hc2 : ContinuousOn (iteratedDeriv 2 h) U :=
    hdw2.continuousOn.congr fun r hr => by
      rw [iteratedDeriv_succ, iteratedDeriv_one, derivWithin_of_isOpen hU hr]
  exact ⟨hd1, hc2⟩

/-! ### Helper 4: Summation by parts + MVT for `CM_disc n ω → CM ω` -/

private lemma tendsto_CM_disc_summation_by_parts {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (h : ℝ → ℝ) (hh0 : h 0 = 0)
    {U : Set ℝ} (hU_open : IsOpen U) (hU_sub : Set.Icc 0 s₀ ⊆ U) (hh_diff : ContDiffOn ℝ 2 h U)
    (ω : Ω) :
    let Δ : ℕ → ℝ := fun n => s₀ / ((n + 1 : ℕ) : ℝ)
    let incr (n : ℕ) (k : Fin (n + 1)) : ℝ :=
      wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ n) (((k : ℕ) + 1 : ℕ) * Δ n) ω
    let δ (n : ℕ) (k : Fin (n + 1)) : ℝ :=
      h (((k : ℕ) + 1 : ℕ) * Δ n) - h ((k : ℝ) * Δ n)
    Tendsto (fun n : ℕ =>
      -∑ k : Fin (n + 1), (δ n k / Δ n) * incr n k -
        (1 / 2 : ℝ) * ∑ k : Fin (n + 1), δ n k ^ 2 / Δ n) atTop
      (𝓝 (-deriv h s₀ * MultiBrownian.W B s₀ ω ⟨0, hd⟩
        + (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * MultiBrownian.W B r ω ⟨0, hd⟩)
        - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, deriv h r ^ 2))) := by
  intro Δ incr δ
  have hΔ_eq : ∀ n, Δ n = s₀ / ((n : ℝ) + 1) := fun n => by simp only [Δ, Nat.cast_succ]
  set w : ℝ → ℝ := fun r => MultiBrownian.W B r ω ⟨0, hd⟩
  have hw0 : w 0 = 0 := MultiBrownian.W_zero B ω ⟨0, hd⟩
  have hw_cont : ContinuousOn w (Set.Icc 0 s₀) := (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn
  obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn hw_cont
  set Mw' := max Mw 1
  obtain ⟨hd1, hc2_U⟩ := contDiffOn_deriv_open hU_open hh_diff
  have hh'_cont : ContinuousOn (deriv h) (Set.Icc 0 s₀) := hd1.continuousOn.mono hU_sub
  have hh''_cont : ContinuousOn (iteratedDeriv 2 h) (Set.Icc 0 s₀) := hc2_U.mono hU_sub
  have hΔ_pos : ∀ n, 0 < Δ n := fun n => div_pos hs₀ (by positivity)
  have hΔ_zero : Tendsto Δ atTop (𝓝 0) := by simpa [Δ] using tendsto_div_succ s₀
  have hgrid_mem : ∀ n (k : ℕ), k ≤ n + 1 → (k : ℝ) * Δ n ∈ Set.Icc 0 s₀ := fun n k hk => by
    refine ⟨by positivity, ?_⟩
    have hN : ((n + 1 : ℕ) : ℝ) * Δ n = s₀ := by simp only [Δ]; field_simp
    calc (k : ℝ) * Δ n ≤ ((n + 1 : ℕ) : ℝ) * Δ n :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (hΔ_pos n).le
      _ = s₀ := hN
  have hh_diffAt : ∀ r ∈ U, DifferentiableAt ℝ h r := fun r hr =>
    (hh_diff.differentiableOn (by norm_num) r hr).differentiableAt (hU_open.mem_nhds hr)
  have hd1_diffAt : ∀ r ∈ U, DifferentiableAt ℝ (deriv h) r := fun r hr =>
    (hd1.differentiableOn (by norm_num) r hr).differentiableAt (hU_open.mem_nhds hr)
  -- First-order MVT on `[k Δ, (k+1) Δ]`
  have hmvt1 : ∀ n (k : Fin (n + 1)),
      ∃ c ∈ Set.Ioo ((k : ℝ) * Δ n) ((((k : ℕ) + 1 : ℕ) : ℝ) * Δ n),
        δ n k / Δ n = deriv h c := fun n k => by
    have hlt : (k : ℝ) * Δ n < (((k : ℕ) + 1 : ℕ) : ℝ) * Δ n := by push_cast; nlinarith [hΔ_pos n]
    have hsub : Set.Icc ((k : ℝ) * Δ n) ((((k : ℕ) + 1 : ℕ) : ℝ) * Δ n) ⊆ Set.Icc 0 s₀ :=
      Set.Icc_subset_Icc (hgrid_mem n k k.isLt.le).1 (hgrid_mem n (k + 1) k.isLt).2
    obtain ⟨c, hc, hd_eq⟩ := exists_deriv_eq_slope h hlt
      ((hh_diff.continuousOn.mono hU_sub).mono hsub)
      (fun r hr => (hh_diffAt r (hU_sub (hsub (Set.Ioo_subset_Icc_self hr)))).differentiableWithinAt)
    have hdiff : (((k : ℕ) + 1 : ℕ) : ℝ) * Δ n - (k : ℝ) * Δ n = Δ n := by push_cast; ring
    exact ⟨c, hc, by simpa only [δ, hdiff] using hd_eq.symm⟩
  -- Second-order MVT on `[(k-1) Δ, (k+1) Δ]`
  have hmvt2 : ∀ n (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < n + 1),
      ∃ ξ ∈ Set.Ioo (((k - 1 : ℕ) : ℝ) * Δ n) ((((k + 1 : ℕ) : ℝ)) * Δ n),
        (h (((k + 1 : ℕ) : ℝ) * Δ n) - h ((k : ℝ) * Δ n)) / Δ n -
          (h ((k : ℝ) * Δ n) - h (((k - 1 : ℕ) : ℝ) * Δ n)) / Δ n =
        iteratedDeriv 2 h ξ * Δ n := by
    intro n k hk1 hk2
    set a := ((k - 1 : ℕ) : ℝ) * Δ n
    set b := (k : ℝ) * Δ n
    have hab : a < b := mul_lt_mul_of_pos_right (by exact_mod_cast Nat.sub_lt hk1 zero_lt_one) (hΔ_pos n)
    have hba : b - a = Δ n := by
      have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (Nat.sub_add_cancel hk1).symm
      simp only [a, b]; rw [this]; ring
    let g : ℝ → ℝ := fun u => h (u + Δ n) - h u
    have hg_sub : ∀ u ∈ Set.Icc a b, u ∈ Set.Icc 0 s₀ ∧ u + Δ n ∈ Set.Icc 0 s₀ := fun u hu => by
      have hb_plus : b + Δ n = ((k + 1 : ℕ) : ℝ) * Δ n := by simp only [b]; push_cast; ring
      exact ⟨⟨(hgrid_mem n (k - 1) (by omega)).1.trans hu.1, hu.2.trans (hgrid_mem n k hk2.le).2⟩,
        ⟨by linarith [(hgrid_mem n (k - 1) (by omega)).1, hu.1, hΔ_pos n],
         by linarith [hu.2, hb_plus, (hgrid_mem n (k + 1) (by omega)).2]⟩⟩
    obtain ⟨η, hη, hg'⟩ := exists_deriv_eq_slope g hab
      (((hh_diff.continuousOn.mono hU_sub).comp (continuousOn_id.add continuousOn_const)
          fun u hu => (hg_sub u hu).2).sub ((hh_diff.continuousOn.mono hU_sub).mono fun u hu => (hg_sub u hu).1))
      (fun u hu => (((hh_diffAt (u + Δ n) (hU_sub (hg_sub u (Set.Ioo_subset_Icc_self hu)).2)).comp u
        ((hasDerivAt_id u).add_const (Δ n)).differentiableAt).sub
        (hh_diffAt u (hU_sub (hg_sub u (Set.Ioo_subset_Icc_self hu)).1))).differentiableWithinAt)
    have hg'_val : deriv g η = deriv h (η + Δ n) - deriv h η := by
      have h1 := (hh_diffAt (η + Δ n) (hU_sub (hg_sub η (Set.Ioo_subset_Icc_self hη)).2)).hasDerivAt
      have h2 := (hh_diffAt η (hU_sub (hg_sub η (Set.Ioo_subset_Icc_self hη)).1)).hasDerivAt
      have hg_eq : g = (h ∘ fun x => x + Δ n) - h := by
        ext u; simp [g, Pi.sub_apply, Function.comp_def]
      have hgη : HasDerivAt g (deriv h (η + Δ n) - deriv h η) η := by
        rw [hg_eq]
        simpa using (h1.comp η ((hasDerivAt_id η).add_const (Δ n))).sub h2
      exact hgη.deriv
    have hη_sub : Set.Icc η (η + Δ n) ⊆ Set.Icc 0 s₀ :=
      Set.Icc_subset_Icc (hg_sub η (Set.Ioo_subset_Icc_self hη)).1.1 (hg_sub η (Set.Ioo_subset_Icc_self hη)).2.2
    obtain ⟨ξ, hξ, h2nd⟩ := exists_deriv_eq_slope (deriv h) (by linarith [hΔ_pos n])
      (hh'_cont.mono hη_sub)
      (fun u hu => (hd1_diffAt u (hU_sub (hη_sub (Set.Ioo_subset_Icc_self hu)))).differentiableWithinAt)
    refine ⟨ξ, ⟨hη.1.trans hξ.1, ?_⟩, ?_⟩
    · have hb_plus : b + Δ n = ((k + 1 : ℕ) : ℝ) * Δ n := by simp only [b]; push_cast; ring
      linarith [hη.2, hξ.2, hb_plus]
    · have h2eq : deriv (deriv h) ξ = iteratedDeriv 2 h ξ := by rw [iteratedDeriv_succ, iteratedDeriv_one]
      have hnum : g b - g a = (h (((k + 1 : ℕ) : ℝ) * Δ n) - h ((k : ℝ) * Δ n)) -
          (h ((k : ℝ) * Δ n) - h (((k - 1 : ℕ) : ℝ) * Δ n)) := by
        have hb1 : b + Δ n = ((k + 1 : ℕ) : ℝ) * Δ n := by simp only [b]; push_cast; ring
        have ha1 : a + Δ n = (k : ℝ) * Δ n := by linarith [hba]
        simp only [g, hb1, ha1]; rfl
      have hsub_η : η + Δ n - η = Δ n := by ring
      calc (h (((k + 1 : ℕ) : ℝ) * Δ n) - h ((k : ℝ) * Δ n)) / Δ n -
            (h ((k : ℝ) * Δ n) - h (((k - 1 : ℕ) : ℝ) * Δ n)) / Δ n
          = (g b - g a) / Δ n := by rw [← sub_div, hnum]
        _ = (g b - g a) / (b - a) := by rw [hba]
        _ = deriv g η := hg'.symm
        _ = deriv h (η + Δ n) - deriv h η := hg'_val
        _ = (deriv h (η + Δ n) - deriv h η) / Δ n * Δ n :=
              (div_mul_cancel₀ _ (hΔ_pos n).ne').symm
        _ = (deriv h (η + Δ n) - deriv h η) / (η + Δ n - η) * Δ n := by rw [hsub_η]
        _ = deriv (deriv h) ξ * Δ n := by rw [h2nd]
        _ = iteratedDeriv 2 h ξ * Δ n := by rw [h2eq]
  -- Part A: `∑ δ_k² / Δ → ∫ (deriv h)²`
  have hPartA : Tendsto (fun n => ∑ k : Fin (n + 1), δ n k ^ 2 / Δ n) atTop
      (𝓝 (∫ r in (0 : ℝ)..s₀, deriv h r ^ 2)) := by
    have hriem := tendsto_lebRiemann_of_continuousOn hs₀.le (hh'_cont.pow 2)
    have hdiff0 : Tendsto (fun n =>
        (∑ k : Fin (n + 1), δ n k ^ 2 / Δ n) -
        (∑ k ∈ Finset.range (n + 1), deriv h ((k : ℝ) * Δ n) ^ 2 * Δ n)) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]; intro ε hε
      have huc := isCompact_Icc.uniformContinuousOn_of_continuous (hh'_cont.pow 2)
      obtain ⟨η, hη, hη_bd⟩ := Metric.uniformContinuousOn_iff_le.mp huc (ε / (2 * s₀)) (by positivity)
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hΔ_zero) η hη
      refine ⟨N, fun n hn => ?_⟩
      have hΔ_le : Δ n ≤ η := by
        have h := hN n hn; rw [Real.dist_eq, sub_zero, abs_of_pos (hΔ_pos n)] at h; exact h.le
      rw [Real.dist_eq, sub_zero, Finset.sum_fin_eq_sum_range, ← Finset.sum_sub_distrib]
      calc _ ≤ ∑ k ∈ Finset.range (n + 1), |(_ : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range (n + 1), (ε / (2 * s₀)) * Δ n := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' := Finset.mem_range.mp hk
            rw [dif_pos hk']
            obtain ⟨c, hc, hce⟩ := hmvt1 n ⟨k, hk'⟩
            have hrew : δ n ⟨k, hk'⟩ ^ 2 / Δ n = deriv h c ^ 2 * Δ n := by
              rw [← hce, div_pow, div_mul_eq_mul_div, sq (Δ n)]; field_simp [(hΔ_pos n).ne']
            rw [hrew, ← sub_mul, abs_mul, abs_of_pos (hΔ_pos n)]
            have hc_mem : c ∈ Set.Icc 0 s₀ :=
              ⟨(hgrid_mem n k hk'.le).1.trans hc.1.le, hc.2.le.trans (hgrid_mem n (k + 1) hk').2⟩
            have hdist : dist c ((k : ℝ) * Δ n) ≤ η := by
              rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hc.1)]
              have : (((k + 1 : ℕ) : ℝ) * Δ n) - (k : ℝ) * Δ n = Δ n := by push_cast; ring
              linarith [hc.2, hΔ_le]
            exact mul_le_mul_of_nonneg_right (hη_bd c hc_mem _ (hgrid_mem n k hk'.le) hdist) (hΔ_pos n).le
        _ = ε / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; simp only [Δ]; field_simp
        _ < ε := half_lt_self hε
    have hcongrA : ∀ n, ∑ k ∈ Finset.range (n + 1), deriv h ((k : ℝ) * Δ n) ^ 2 * Δ n =
        ∑ j ∈ Finset.range (n + 1),
          (deriv h ^ 2) ((j : ℝ) * (s₀ / ((n : ℝ) + 1))) * (s₀ / ((n : ℝ) + 1)) := fun n => by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hΔ_eq n, Pi.pow_apply]
    simpa using hdiff0.add (hriem.congr fun n => (hcongrA n).symm)
  -- Part B: Summation by parts
  have hPartB : Tendsto (fun n => -∑ k : Fin (n + 1), (δ n k / Δ n) * incr n k) atTop
      (𝓝 (-deriv h s₀ * w s₀ + ∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r)) := by
    let a (n k : ℕ) : ℝ := (h (((k + 1 : ℕ) : ℝ) * Δ n) - h ((k : ℝ) * Δ n)) / Δ n
    have hsbp : ∀ n, -∑ k : Fin (n + 1), (δ n k / Δ n) * incr n k =
        -(a n n) * w s₀ +
        ∑ k ∈ Finset.range n, (a n (k + 1) - a n k) * w (((k + 1 : ℕ) : ℝ) * Δ n) := fun n => by
      have hN : ((n + 1 : ℕ) : ℝ) * Δ n = s₀ := by simp only [Δ]; field_simp
      have hident : ∑ k : Fin (n + 1), (δ n k / Δ n) * incr n k =
          ∑ k : Fin (n + 1), a n k * (w ((((k : ℕ) + 1 : ℕ) : ℝ) * Δ n) - w ((k : ℝ) * Δ n)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have ha : a n k = δ n k / Δ n := by simp only [a, δ]
        have hi : incr n k = w ((((k : ℕ) + 1 : ℕ) : ℝ) * Δ n) - w ((k : ℝ) * Δ n) := by
          simp only [incr, w, wnnIncr_eq_W]
        rw [ha, hi]
      rw [hident, Fin.sum_univ_eq_sum_range
        (fun k => a n k * (w (((k + 1 : ℕ) : ℝ) * Δ n) - w ((k : ℝ) * Δ n))) (n + 1)]
      have h1 : ∑ k ∈ Finset.range (n + 1), a n k * w (((k + 1 : ℕ) : ℝ) * Δ n) =
          a n n * w s₀ + ∑ k ∈ Finset.range n, a n k * w (((k + 1 : ℕ) : ℝ) * Δ n) := by
        rw [Finset.sum_range_succ, hN, add_comm]
      have h2 : ∑ k ∈ Finset.range (n + 1), a n k * w ((k : ℝ) * Δ n) =
          ∑ k ∈ Finset.range n, a n (k + 1) * w (((k + 1 : ℕ) : ℝ) * Δ n) := by
        rw [Finset.sum_range_succ']; simp [hw0]
      simp_rw [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_mul, Finset.sum_sub_distrib]; ring
    have hT1 : Tendsto (fun n => -(a n n) * w s₀) atTop (𝓝 (-deriv h s₀ * w s₀)) := by
      have han : Tendsto (fun n => a n n) atTop (𝓝 (deriv h s₀)) := by
        rw [Metric.tendsto_atTop]; intro ε hε
        obtain ⟨η, hη, hη_bd⟩ := Metric.continuousWithinAt_iff.mp (hh'_cont s₀ ⟨hs₀.le, le_rfl⟩) ε hε
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hΔ_zero) η hη
        refine ⟨N, fun n hn => ?_⟩
        obtain ⟨c, hc, hce⟩ := hmvt1 n ⟨n, Nat.lt_succ_self n⟩
        have hN_eq : ((n + 1 : ℕ) : ℝ) * Δ n = s₀ := by simp only [Δ]; field_simp
        have hc_mem : c ∈ Set.Icc 0 s₀ :=
          ⟨(hgrid_mem n n (Nat.le_succ n)).1.trans hc.1.le, by linarith [hc.2, hN_eq]⟩
        have hdist : dist c s₀ < η := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hc.2, hN_eq])]
          have hsub : s₀ - (n : ℝ) * Δ n = Δ n := by rw [← hN_eq]; push_cast; ring
          have hΔ_lt : Δ n < η := by
            have h := hN n hn; rw [Real.dist_eq, sub_zero, abs_of_pos (hΔ_pos n)] at h; exact h
          linarith [hc.1]
        change dist (δ n ⟨n, Nat.lt_succ_self n⟩ / Δ n) (deriv h s₀) < ε
        rw [hce]; exact hη_bd hc_mem hdist
      exact (han.neg).mul_const (w s₀)
    have hT2 : Tendsto (fun n => ∑ k ∈ Finset.range n, (a n (k + 1) - a n k) * w (((k + 1 : ℕ) : ℝ) * Δ n))
        atTop (𝓝 (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r)) := by
      have hriem := tendsto_lebRiemann_of_continuousOn hs₀.le (hh''_cont.mul hw_cont)
      have hriem' : Tendsto (fun n => ∑ k ∈ Finset.range n,
          iteratedDeriv 2 h (((k + 1 : ℕ) : ℝ) * Δ n) * w (((k + 1 : ℕ) : ℝ) * Δ n) * Δ n) atTop
          (𝓝 (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r)) := by
        refine hriem.congr fun n => ?_
        have hΔn : Δ n = s₀ / ((n : ℝ) + 1) := hΔ_eq n
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul]
        have h0 : (iteratedDeriv 2 h * w) 0 * (s₀ / ((n : ℝ) + 1)) = 0 := by
          simp [Pi.mul_apply, hw0]
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Pi.mul_apply, hΔn]
      have hdiff0 : Tendsto (fun n =>
          (∑ k ∈ Finset.range n, (a n (k + 1) - a n k) * w (((k + 1 : ℕ) : ℝ) * Δ n)) -
          (∑ k ∈ Finset.range n, iteratedDeriv 2 h (((k + 1 : ℕ) : ℝ) * Δ n) *
            w (((k + 1 : ℕ) : ℝ) * Δ n) * Δ n)) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]; intro ε hε
        have huc := isCompact_Icc.uniformContinuousOn_of_continuous hh''_cont
        obtain ⟨η, hη, hη_bd⟩ := Metric.uniformContinuousOn_iff_le.mp huc (ε / (2 * s₀ * Mw')) (by positivity)
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hΔ_zero) (η / 2) (half_pos hη)
        refine ⟨N, fun n hn => ?_⟩
        have hΔ_le : Δ n ≤ η / 2 := by
          have h := hN n hn; rw [Real.dist_eq, sub_zero, abs_of_pos (hΔ_pos n)] at h; exact h.le
        rw [Real.dist_eq, sub_zero, ← Finset.sum_sub_distrib]
        calc _ ≤ ∑ k ∈ Finset.range n, |(a n (k + 1) - a n k) * w (((k + 1 : ℕ) : ℝ) * Δ n) -
                iteratedDeriv 2 h (((k + 1 : ℕ) : ℝ) * Δ n) * w (((k + 1 : ℕ) : ℝ) * Δ n) * Δ n| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k ∈ Finset.range n, (ε / (2 * s₀)) * Δ n := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' := Finset.mem_range.mp hk
              obtain ⟨ξ, hξ, h2eq⟩ := hmvt2 n (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ hk')
              have ha_sub : a n (k + 1) - a n k = iteratedDeriv 2 h ξ * Δ n := by
                simpa only [a, Nat.add_sub_cancel] using h2eq
              rw [ha_sub, show iteratedDeriv 2 h ξ * Δ n * w (((k + 1 : ℕ) : ℝ) * Δ n) -
                  iteratedDeriv 2 h (((k + 1 : ℕ) : ℝ) * Δ n) * w (((k + 1 : ℕ) : ℝ) * Δ n) * Δ n =
                  (iteratedDeriv 2 h ξ - iteratedDeriv 2 h (((k + 1 : ℕ) : ℝ) * Δ n)) *
                    w (((k + 1 : ℕ) : ℝ) * Δ n) * Δ n by ring,
                abs_mul, abs_mul, abs_of_pos (hΔ_pos n)]
              have hξ_mem : ξ ∈ Set.Icc 0 s₀ :=
                ⟨(hgrid_mem n k (by omega)).1.trans (by simpa using hξ.1.le),
                 hξ.2.le.trans (hgrid_mem n (k + 2) (by omega)).2⟩
              have hdist : dist ξ (((k + 1 : ℕ) : ℝ) * Δ n) ≤ η := by
                rw [Real.dist_eq, abs_le]
                have h1 : (k : ℝ) * Δ n < ξ := by simpa using hξ.1
                have h2 : ξ < ((k + 2 : ℕ) : ℝ) * Δ n := hξ.2
                have hs1 : ((k + 1 : ℕ) : ℝ) * Δ n - (k : ℝ) * Δ n = Δ n := by push_cast; ring
                have hs2 : ((k + 2 : ℕ) : ℝ) * Δ n - ((k + 1 : ℕ) : ℝ) * Δ n = Δ n := by push_cast; ring
                constructor <;> linarith
              have hdiff_le := hη_bd ξ hξ_mem _ (hgrid_mem n (k + 1) (by omega)) hdist
              have hw_le : |w (((k + 1 : ℕ) : ℝ) * Δ n)| ≤ Mw' :=
                (hMw _ (hgrid_mem n (k + 1) (by omega))).trans (le_max_left _ _)
              calc _ ≤ (ε / (2 * s₀ * Mw')) * Mw' * Δ n :=
                    mul_le_mul_of_nonneg_right (mul_le_mul hdiff_le hw_le (abs_nonneg _) (by positivity))
                      (hΔ_pos n).le
                _ = (ε / (2 * s₀)) * Δ n := by
                    have : Mw' ≠ 0 := by linarith [le_max_right Mw 1]
                    field_simp
          _ ≤ ((n + 1 : ℕ) : ℝ) * ((ε / (2 * s₀)) * Δ n) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity)
          _ = ε / 2 := by simp only [Δ]; field_simp
          _ < ε := half_lt_self hε
      simpa using hdiff0.add hriem'
    exact (hT1.add hT2).congr fun n => (hsbp n).symm
  exact hPartB.sub (hPartA.const_mul (1 / 2 : ℝ))

/-! ### Main lemma: `cameronMartin_C2_shift` -/

lemma cameronMartin_C2_shift {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (h : ℝ → ℝ) (x : ℝ) (Ψ : Ω → ℝ)
    (hh0 : h 0 = 0)
    (hdiff : ∃ U : Set ℝ, IsOpen U ∧ Set.Icc 0 s₀ ⊆ U ∧ ContDiffOn ℝ 2 h U)
    (hpath : ∀ ω,
      let w := fun r => MultiBrownian.W B r ω ⟨0, hd⟩
      pathExponent (fun r => w r + h r) x s₀
        - deriv h s₀ * w s₀
        + (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r)
        - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, deriv h r ^ 2)
      = Ψ ω) :
    ∫ ω, Real.exp (counterexampleV1Exponent B hd s₀ x ω) ∂P =
      ∫ ω, Real.exp (Ψ ω) ∂P := by
  rcases hs₀.eq_or_lt with rfl | hs₀_pos
  · have h0 : ∀ ω, Ψ ω = 0 := fun ω => by
      have := (hpath ω).symm; simp [pathExponent, MultiBrownian.W_zero, hh0] at this; exact this
    have h1 : ∀ ω, counterexampleV1Exponent B hd 0 x ω = 0 := fun ω => by
      simp [counterexampleV1Exponent, MultiBrownian.W_zero]
    simp [h0, h1]
  obtain ⟨U, hU_open, hU_sub, hh_diff⟩ := hdiff
  obtain ⟨hd1, hc2_U⟩ := contDiffOn_deriv_open hU_open hh_diff
  have hh'_cont : ContinuousOn (deriv h) (Set.Icc 0 s₀) := hd1.continuousOn.mono hU_sub
  obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hh'_cont
  set Mh' := max Mh 0
  let CM : Ω → ℝ := fun ω =>
    -deriv h s₀ * MultiBrownian.W B s₀ ω ⟨0, hd⟩
      + (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * MultiBrownian.W B r ω ⟨0, hd⟩)
      - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, deriv h r ^ 2)
  let Δ : ℕ → ℝ := fun n => s₀ / ((n + 1 : ℕ) : ℝ)
  have hΔ_eq : ∀ n, Δ n = s₀ / ((n : ℝ) + 1) := fun n => by simp only [Δ, Nat.cast_succ]
  let incr (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ :=
    fun k => wnnIncr B ⟨0, hd⟩ ((k : ℝ) * Δ n) (((k : ℕ) + 1 : ℕ) * Δ n) ω
  let δ (n : ℕ) : Fin (n + 1) → ℝ := fun k => h (((k : ℕ) + 1 : ℕ) * Δ n) - h ((k : ℝ) * Δ n)
  let CM_disc (n : ℕ) (ω : Ω) : ℝ :=
    -∑ k : Fin (n + 1), (δ n k / Δ n) * incr n ω k -
      (1 / 2 : ℝ) * ∑ k : Fin (n + 1), δ n k ^ 2 / Δ n
  have hincr_m : ∀ n, Measurable (incr n) := fun n =>
    measurable_pi_iff.mpr fun k => measurable_wnnIncr B ⟨0, hd⟩ _ _
  have hCM_disc_m : ∀ n, Measurable (CM_disc n) := fun n =>
    ((Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_wnnIncr B ⟨0, hd⟩ _ _)).neg).sub
      measurable_const
  have hCM_lim : ∀ ω, Tendsto (fun n => CM_disc n ω) atTop (𝓝 (CM ω)) := fun ω =>
    tendsto_CM_disc_summation_by_parts B hd hs₀_pos h hh0 hU_open hU_sub hh_diff ω
  have hCM_m : Measurable CM := measurable_of_tendsto_metrizable hCM_disc_m (tendsto_pi_nhds.mpr hCM_lim)
  -- `|δ n k| ≤ Mh' * Δ n` via MVT
  have hδ_le : ∀ n (k : Fin (n + 1)), |δ n k| ≤ Mh' * Δ n := fun n k => by
    have hΔpos : 0 < Δ n := div_pos hs₀_pos (by positivity)
    have ha : 0 ≤ (k : ℝ) * Δ n := by positivity
    have hb : (((k : ℕ) + 1 : ℕ) : ℝ) * Δ n ≤ s₀ := by
      have hN : ((n + 1 : ℕ) : ℝ) * Δ n = s₀ := by simp only [Δ]; field_simp
      calc (((k : ℕ) + 1 : ℕ) : ℝ) * Δ n ≤ ((n + 1 : ℕ) : ℝ) * Δ n :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast k.isLt) hΔpos.le
        _ = s₀ := hN
    have hsub : Set.Icc ((k : ℝ) * Δ n) ((((k : ℕ) + 1 : ℕ) : ℝ) * Δ n) ⊆ Set.Icc 0 s₀ :=
      Set.Icc_subset_Icc ha hb
    obtain ⟨c, hcI, hderiv⟩ := exists_deriv_eq_slope h (by push_cast; nlinarith)
      ((hh_diff.continuousOn.mono hU_sub).mono hsub)
      (fun r hr => ((hh_diff.differentiableOn (by norm_num) r
        (hU_sub (hsub (Set.Ioo_subset_Icc_self hr)))).differentiableAt
        (hU_open.mem_nhds (hU_sub (hsub (Set.Ioo_subset_Icc_self hr))))).differentiableWithinAt)
    have hsub_t : (((k : ℕ) + 1 : ℕ) : ℝ) * Δ n - (k : ℝ) * Δ n = Δ n := by push_cast; ring
    have hδ_eq : δ n k = deriv h c * Δ n := by
      simp only [δ]; rw [hsub_t] at hderiv; rw [hderiv, div_mul_cancel₀ _ hΔpos.ne']
    rw [hδ_eq, abs_mul, abs_of_pos hΔpos]
    exact mul_le_mul_of_nonneg_right ((hMh c (hsub (Set.Ioo_subset_Icc_self hcI))).trans (le_max_left _ _)) hΔpos.le
  -- Uniform `L²` bound on `exp(CM_disc n)` via `lintegral_pi_exp_CM_sq` + `hasLaw_incrVec`!
  have hL2_CM : ∀ n : ℕ,
      MemLp (fun ω => Real.exp (CM_disc n ω)) 2 P ∧
      ∫ ω, (Real.exp (CM_disc n ω)) ^ 2 ∂P ≤ Real.exp (s₀ * Mh' ^ 2) := fun n => by
    have hΔpos : 0 < Δ n := div_pos hs₀_pos (by positivity)
    have hv : Real.toNNReal (Δ n) ≠ 0 := by
      intro h0; exact hΔpos.not_ge (Real.toNNReal_eq_zero.mp h0)
    have hlaw := hasLaw_incrVec B hd hs₀_pos (n + 1) n.succ_pos
    have hlint_sq : ∫⁻ ω, ENNReal.ofReal ((Real.exp (CM_disc n ω)) ^ 2) ∂P =
        ENNReal.ofReal (Real.exp (∑ k : Fin (n + 1), δ n k ^ 2 / Δ n)) := by
      have hsq : ∀ ω, (Real.exp (CM_disc n ω)) ^ 2 =
          Real.exp (∑ k : Fin (n + 1), (-2 * (δ n k / Δ n) * incr n ω k - δ n k ^ 2 / Δ n)) := fun ω => by
        rw [← Real.exp_nat_mul]; congr 1; simp only [CM_disc, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        push_cast; refine Finset.sum_congr rfl fun k _ => by ring
      simp_rw [hsq]
      have hm_z : Measurable (fun z : Fin (n + 1) → ℝ => ENNReal.ofReal (Real.exp
          (∑ k : Fin (n + 1), (-2 * (δ n k / Δ n) * z k - δ n k ^ 2 / Δ n)))) :=
        ((Finset.measurable_sum _ fun k _ => (measurable_const.mul (measurable_pi_apply k)).sub measurable_const).exp).ennreal_ofReal
      rw [← lintegral_map hm_z (hincr_m n), hlaw.map_eq]
      have hcast : ((Real.toNNReal (Δ n) : ℝ≥0) : ℝ) = Δ n := Real.coe_toNNReal _ hΔpos.le
      have hμ : (s₀ / ((n + 1 : ℕ) : ℝ)).toNNReal = (Δ n).toNNReal := by simp only [Δ]
      rw [hμ]
      simpa [hcast] using lintegral_pi_exp_CM_sq hv (δ n)
    have hsum_le : ∑ k : Fin (n + 1), δ n k ^ 2 / Δ n ≤ s₀ * Mh' ^ 2 := by
      calc ∑ k : Fin (n + 1), δ n k ^ 2 / Δ n
          ≤ ∑ _k : Fin (n + 1), Mh' ^ 2 * Δ n := Finset.sum_le_sum fun k _ => by
            have h1 : δ n k ^ 2 ≤ (Mh' * Δ n) ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hδ_le n k) 2
            rw [div_le_iff₀ hΔpos]; nlinarith
        _ = s₀ * Mh' ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; simp only [Δ]; field_simp
    have hi2 : Integrable (fun ω => (Real.exp (CM_disc n ω)) ^ 2) P := by
      refine ⟨((hCM_disc_m n).exp.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simp_rw [Real.enorm_eq_ofReal (sq_nonneg _), hlint_sq]
      exact ENNReal.ofReal_lt_top
    refine ⟨memLp_two_of_integrable_sq (hCM_disc_m n).exp.aestronglyMeasurable hi2, ?_⟩
    rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all _ fun _ => sq_nonneg _), hlint_sq]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsum_le)
  have hCM_L2 : MemLp (fun ω => Real.exp (CM ω)) 2 P ∧
      ∫ ω, (Real.exp (CM ω)) ^ 2 ∂P ≤ Real.exp (s₀ * Mh' ^ 2) := by
    have hfat := integral_pow_even_le_of_tendsto (N := 2) ⟨1, rfl⟩ hCM_m.exp.aestronglyMeasurable
      (fun n => (hL2_CM n).1.aestronglyMeasurable.aemeasurable)
      (ae_of_all _ fun ω => (Real.continuous_exp.tendsto _).comp (hCM_lim ω))
      (fun n => (hL2_CM n).1.integrable_sq) (fun n => (hL2_CM n).2) tendsto_const_nhds
    exact ⟨memLp_two_of_integrable_sq hCM_m.exp.aestronglyMeasurable hfat.1, hfat.2⟩
  -- Measurability of `pathExponent (w + h) x s₀` via discrete Riemann sums (`discV1Exp`)
  have hwh_lim : ∀ ω, Tendsto (fun n => discV1Exp (n + 1) s₀ x (incr n ω + δ n)) atTop
      (𝓝 (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) := fun ω => by
    have hpsum_h : ∀ n (k : ℕ), k ≤ n + 1 →
        (∑ j : Fin (n + 1), if (j : ℕ) < k then (incr n ω + δ n) j else 0) =
          MultiBrownian.W B ((k : ℝ) * Δ n) ω ⟨0, hd⟩ + h ((k : ℝ) * Δ n) := fun n k hk => by
      have hsplit : (∑ j : Fin (n + 1), if (j : ℕ) < k then (incr n ω + δ n) j else 0) =
          (∑ j : Fin (n + 1), if (j : ℕ) < k then incr n ω j else 0) +
          (∑ j : Fin (n + 1), if (j : ℕ) < k then δ n j else 0) := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
      rw [hsplit, psum_incrVec B hd s₀ (n + 1) k hk ω]
      congr 1
      -- Telescoping sum for `δ n j`
      have htel : ∀ m ≤ n + 1,
          (∑ j : Fin (n + 1), if (j : ℕ) < m then δ n j else 0) = h ((m : ℝ) * Δ n) := by
        intro m hm
        induction m with
        | zero => simp [hh0]
        | succ m ih =>
          have hsplit : (∑ j : Fin (n + 1), if (j : ℕ) < m + 1 then δ n j else 0) =
              (∑ j : Fin (n + 1), if (j : ℕ) < m then δ n j else 0) +
              (∑ j : Fin (n + 1), if (j : ℕ) = m then δ n j else 0) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hjm : (j : ℕ) < m
            · have hlt : (j : ℕ) < m + 1 := Nat.lt_succ_of_lt hjm
              have hne : (j : ℕ) ≠ m := Nat.ne_of_lt hjm
              simp [hjm, hlt, hne]
            · by_cases heq : (j : ℕ) = m
              · have hlt : (j : ℕ) < m + 1 := by omega
                simp [hjm, heq, hlt]
              · have hge : ¬ (j : ℕ) < m + 1 := by omega
                simp [hjm, heq, hge]
          have hsing : (∑ j : Fin (n + 1), if (j : ℕ) = m then δ n j else 0) = δ n ⟨m, hm⟩ := by
            rw [Finset.sum_eq_single ⟨m, hm⟩]
            · simp
            · intro j _ hne
              have : (j : ℕ) ≠ m := fun h => hne (Fin.ext h)
              simp [this]
            · simp
          rw [hsplit, hsing, ih (Nat.le_of_succ_le hm)]
          simp only [δ]; push_cast; ring
      exact htel k hk
    have hwh_cont : ContinuousOn (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) (Set.Icc 0 s₀) :=
      (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn.add (hh_diff.continuousOn.mono hU_sub)
    have hc1 := tendsto_lebRiemann_of_continuousOn
        (g := fun r => x + (MultiBrownian.W B r ω ⟨0, hd⟩ + h r))
        hs₀_pos.le (continuousOn_const.add hwh_cont)
    have hc4 := tendsto_lebRiemann_of_continuousOn
        (g := fun r => (x + (MultiBrownian.W B r ω ⟨0, hd⟩ + h r)) ^ 4)
        hs₀_pos.le ((continuousOn_const.add hwh_cont).pow 4)
    have hlim := ((tendsto_const_nhds (x := (1 / 3 : ℝ) *
      ((x + (MultiBrownian.W B s₀ ω ⟨0, hd⟩ + h s₀)) ^ 3 - x ^ 3))).sub hc1).sub
      (hc4.const_mul (1 / 2 : ℝ))
    refine hlim.congr fun n => ?_
    have hN : ((n + 1 : ℕ) : ℝ) * Δ n = s₀ := by simp only [Δ]; field_simp
    have hsum1 :
        ∑ k : Fin (n + 1),
          (x + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then (incr n ω + δ n) j else 0) *
            (s₀ / ((n + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range (n + 1),
          (x + (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n : ℝ) + 1))) ω ⟨0, hd⟩ +
            h ((k : ℝ) * (s₀ / ((n : ℝ) + 1))))) *
            (s₀ / ((n : ℝ) + 1)) := by
      rw [Fin.sum_univ_eq_sum_range (fun k =>
        (x + ∑ j : Fin (n + 1), if (j : ℕ) < k then (incr n ω + δ n) j else 0) *
          (s₀ / ((n + 1 : ℕ) : ℝ))) (n + 1)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hpsum_h n k (Finset.mem_range.mp hk).le]
      simp only [hΔ_eq n]
      push_cast
      rfl
    have hsum4 :
        ∑ k : Fin (n + 1),
          (x + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then (incr n ω + δ n) j else 0) ^ 4 *
            (s₀ / ((n + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range (n + 1),
          (x + (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n : ℝ) + 1))) ω ⟨0, hd⟩ +
            h ((k : ℝ) * (s₀ / ((n : ℝ) + 1))))) ^ 4 *
            (s₀ / ((n : ℝ) + 1)) := by
      rw [Fin.sum_univ_eq_sum_range (fun k =>
        (x + ∑ j : Fin (n + 1), if (j : ℕ) < k then (incr n ω + δ n) j else 0) ^ 4 *
          (s₀ / ((n + 1 : ℕ) : ℝ))) (n + 1)]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hpsum_h n k (Finset.mem_range.mp hk).le]
      simp only [hΔ_eq n]
      push_cast
      rfl
    simp only [discV1Exp]
    have hΔdef : s₀ / ((n + 1 : ℕ) : ℝ) = Δ n := by simp only [Δ]
    rw [hpsum_h n (n + 1) le_rfl, hN, hΔdef, hsum1, hsum4]
  have hpathExp_m : Measurable (fun ω => pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀) :=
    measurable_of_tendsto_metrizable
      (fun n => (continuous_discV1Exp (n + 1) s₀ x).measurable.comp ((hincr_m n).add_const (δ n)))
      (tendsto_pi_nhds.mpr hwh_lim)
  -- Step 1: Truncated Cameron–Martin identity for every `R : ℕ`
  have hcut : ∀ R : ℕ,
      ∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s₀ x ω)) ∂P =
        ∫ ω, min (R : ℝ) (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) *
          Real.exp (CM ω) ∂P := by
    intro R
    -- Exact finite-dimensional equality at every `n` from `gaussian_vec_shift_lintegral`!
    have hfin : ∀ n : ℕ,
        ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω))) ∂P =
          ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) *
            Real.exp (CM_disc n ω) ∂P := fun n => by
      have hΔpos : 0 < Δ n := div_pos hs₀_pos (by positivity)
      have hv : Real.toNNReal (Δ n) ≠ 0 := by
        intro h0; exact hΔpos.not_ge (Real.toNNReal_eq_zero.mp h0)
      have hlaw := hasLaw_incrVec B hd hs₀_pos (n + 1) n.succ_pos
      have hm_L : Measurable (fun z : Fin (n + 1) → ℝ =>
          ENNReal.ofReal (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x z)))) :=
        ((measurable_const.min ((continuous_discV1Exp (n + 1) s₀ x).measurable.exp)).ennreal_ofReal)
      have hm_R : Measurable (fun z : Fin (n + 1) → ℝ =>
          ENNReal.ofReal (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (z + δ n))) *
            Real.exp (-∑ k : Fin (n + 1), (δ n k / Δ n) * z k -
              (1 / 2 : ℝ) * ∑ k : Fin (n + 1), δ n k ^ 2 / Δ n))) :=
        (((measurable_const.min ((continuous_discV1Exp (n + 1) s₀ x).measurable.comp (measurable_id.add_const (δ n)) |>.exp)).mul
          ((((Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_pi_apply k)).neg).sub measurable_const).exp)).ennreal_ofReal)
      have hlint_eq : ∫⁻ ω, ENNReal.ofReal (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω)))) ∂P =
          ∫⁻ ω, ENNReal.ofReal (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) *
            Real.exp (CM_disc n ω)) ∂P := by
        rw [← lintegral_map hm_L (hincr_m n), ← lintegral_map hm_R (hincr_m n), hlaw.map_eq]
        have hcast : ((Real.toNNReal (Δ n) : ℝ≥0) : ℝ) = Δ n := Real.coe_toNNReal _ hΔpos.le
        have hsh := gaussian_vec_shift_lintegral hv (δ n) hm_L
        have hμ : (s₀ / ((n + 1 : ℕ) : ℝ)).toNNReal = (Δ n).toNNReal := by simp only [Δ]
        rw [hμ]
        simpa [hcast, ENNReal.ofReal_mul (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)] using hsh
      have hiL : Integrable (fun ω => min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω)))) P :=
        (integrable_const (R : ℝ)).mono'
          (measurable_const.min ((continuous_discV1Exp (n + 1) s₀ x).measurable.comp (hincr_m n) |>.exp)).aestronglyMeasurable
          (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]; exact min_le_left _ _)
      have hiR : Integrable (fun ω => min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) *
          Real.exp (CM_disc n ω)) P :=
        (((hL2_CM n).1.integrable one_le_two).const_mul (R : ℝ)).mono'
          ((measurable_const.min ((continuous_discV1Exp (n + 1) s₀ x).measurable.comp ((hincr_m n).add_const (δ n)) |>.exp)).mul
            (hCM_disc_m n).exp).aestronglyMeasurable
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
              abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le)
      rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
        ← ENNReal.toReal_ofReal (integral_nonneg fun _ => mul_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le) (Real.exp_pos _).le),
        ofReal_integral_eq_lintegral_ofReal hiL (ae_of_all _ fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
        ofReal_integral_eq_lintegral_ofReal hiR (ae_of_all _ fun _ => mul_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le) (Real.exp_pos _).le),
        hlint_eq]
    -- LHS converges by DCT (bounded by `R`)
    have hLHS : Tendsto (fun n => ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω))) ∂P)
        atTop (𝓝 (∫ ω, min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s₀ x ω)) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => (R : ℝ))
        (fun n => (measurable_const.min ((continuous_discV1Exp (n + 1) s₀ x).measurable.comp (hincr_m n) |>.exp)).aestronglyMeasurable)
        (integrable_const _)
        (fun n => ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]; exact min_le_left _ _)
        (ae_of_all _ fun ω => by
          have hc1 := tendsto_lebRiemann_of_continuousOn
              (g := fun r => x + MultiBrownian.W B r ω ⟨0, hd⟩)
              hs₀_pos.le (continuousOn_const.add (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn)
          have hc4 := tendsto_lebRiemann_of_continuousOn
              (g := fun r => (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4)
              hs₀_pos.le ((continuousOn_const.add (continuous_W_coord B ⟨0, hd⟩ ω).continuousOn).pow 4)
          have hlim := ((tendsto_const_nhds (x := (1 / 3 : ℝ) * ((x + MultiBrownian.W B s₀ ω ⟨0, hd⟩) ^ 3 - x ^ 3))).sub
            hc1).sub (hc4.const_mul (1 / 2 : ℝ))
          refine tendsto_const_nhds.min ((Real.continuous_exp.tendsto _).comp (hlim.congr fun n => ?_))
          have hN : ((n + 1 : ℕ) : ℝ) * Δ n = s₀ := by simp only [Δ]; field_simp
          have hsum1 :
              ∑ k : Fin (n + 1),
                (x + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then incr n ω j else 0) *
                  (s₀ / ((n + 1 : ℕ) : ℝ)) =
              ∑ k ∈ Finset.range (n + 1),
                (x + MultiBrownian.W B ((k : ℝ) * (s₀ / ((n : ℝ) + 1))) ω ⟨0, hd⟩) *
                  (s₀ / ((n : ℝ) + 1)) := by
            rw [Fin.sum_univ_eq_sum_range (fun k =>
              (x + ∑ j : Fin (n + 1), if (j : ℕ) < k then incr n ω j else 0) *
                (s₀ / ((n + 1 : ℕ) : ℝ))) (n + 1)]
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [psum_incrVec B hd s₀ (n + 1) k (Finset.mem_range.mp hk).le ω]
            push_cast
            rfl
          have hsum4 :
              ∑ k : Fin (n + 1),
                (x + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then incr n ω j else 0) ^ 4 *
                  (s₀ / ((n + 1 : ℕ) : ℝ)) =
              ∑ k ∈ Finset.range (n + 1),
                (x + MultiBrownian.W B ((k : ℝ) * (s₀ / ((n : ℝ) + 1))) ω ⟨0, hd⟩) ^ 4 *
                  (s₀ / ((n : ℝ) + 1)) := by
            rw [Fin.sum_univ_eq_sum_range (fun k =>
              (x + ∑ j : Fin (n + 1), if (j : ℕ) < k then incr n ω j else 0) ^ 4 *
                (s₀ / ((n + 1 : ℕ) : ℝ))) (n + 1)]
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [psum_incrVec B hd s₀ (n + 1) k (Finset.mem_range.mp hk).le ω]
            push_cast
            rfl
          simp only [discV1Exp]
          have hΔdef : s₀ / ((n + 1 : ℕ) : ℝ) = Δ n := by simp only [Δ]
          rw [psum_incrVec B hd s₀ (n + 1) (n + 1) le_rfl ω, hN, hΔdef, hsum1, hsum4])
    -- RHS converges by `tendsto_integral_of_ae_tendsto_of_L2_bdd_real`
    have hfn_L2 : ∀ n, MemLp (fun ω =>
        min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) * Real.exp (CM_disc n ω)) 2 P := fun n =>
      ((hL2_CM n).1.const_mul (R : ℝ)).mono'
        ((measurable_const.min ((continuous_discV1Exp (n + 1) s₀ x).measurable.comp ((hincr_m n).add_const (δ n)) |>.exp)).mul
          (hCM_disc_m n).exp).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le)
    have hg_L2 : MemLp (fun ω =>
        min (R : ℝ) (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) *
          Real.exp (CM ω)) 2 P :=
      (hCM_L2.1.const_mul (R : ℝ)).mono'
        ((measurable_const.min hpathExp_m.exp).mul hCM_m.exp).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le)
    have hRHS : Tendsto (fun n => ∫ ω, min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) *
          Real.exp (CM_disc n ω) ∂P) atTop
        (𝓝 (∫ ω, min (R : ℝ) (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) *
          Real.exp (CM ω) ∂P)) := by
      refine tendsto_integral_of_ae_tendsto_of_L2_bdd_real (M := 4 * (R : ℝ) ^ 2 * Real.exp (s₀ * Mh' ^ 2))
        (by positivity) hfn_L2 hg_L2 (fun n => ?_)
        (ae_of_all _ fun ω => (tendsto_const_nhds.min ((Real.continuous_exp.tendsto _).comp (hwh_lim ω))).mul
          ((Real.continuous_exp.tendsto _).comp (hCM_lim ω)))
      have hpt : ∀ ω,
          (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) * Real.exp (CM_disc n ω) -
           min (R : ℝ) (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) * Real.exp (CM ω)) ^ 2 ≤
          2 * (R : ℝ) ^ 2 * Real.exp (CM_disc n ω) ^ 2 + 2 * (R : ℝ) ^ 2 * Real.exp (CM ω) ^ 2 := fun ω => by
        have h1 : (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) * Real.exp (CM_disc n ω)) ^ 2 ≤
            (R : ℝ) ^ 2 * Real.exp (CM_disc n ω) ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le) (min_le_left _ _) 2) (sq_nonneg _)
        have h2 : (min (R : ℝ) (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) *
            Real.exp (CM ω)) ^ 2 ≤ (R : ℝ) ^ 2 * Real.exp (CM ω) ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le) (min_le_left _ _) 2) (sq_nonneg _)
        nlinarith [sq_nonneg (min (R : ℝ) (Real.exp (discV1Exp (n + 1) s₀ x (incr n ω + δ n))) * Real.exp (CM_disc n ω) +
          min (R : ℝ) (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) * Real.exp (CM ω))]
      calc ∫ ω, _ ∂P
          ≤ ∫ ω, (2 * (R : ℝ) ^ 2 * Real.exp (CM_disc n ω) ^ 2 + 2 * (R : ℝ) ^ 2 * Real.exp (CM ω) ^ 2) ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
              (((hL2_CM n).1.integrable_sq.const_mul _).add (hCM_L2.1.integrable_sq.const_mul _)) (ae_of_all _ hpt)
        _ = 2 * (R : ℝ) ^ 2 * ∫ ω, Real.exp (CM_disc n ω) ^ 2 ∂P + 2 * (R : ℝ) ^ 2 * ∫ ω, Real.exp (CM ω) ^ 2 ∂P := by
            rw [integral_add ((hL2_CM n).1.integrable_sq.const_mul _) (hCM_L2.1.integrable_sq.const_mul _),
              integral_const_mul, integral_const_mul]
        _ ≤ 4 * (R : ℝ) ^ 2 * Real.exp (s₀ * Mh' ^ 2) := by
            have := (hL2_CM n).2; have := hCM_L2.2; nlinarith [sq_nonneg (R : ℝ)]
    exact tendsto_nhds_unique hLHS (hRHS.congr fun n => (hfin n).symm)
  -- Step 2: Pass `R → ∞` by Monotone Convergence, then convert `lintegral` equality to Bochner `integral` equality!
  have hV1_m := measurable_counterexampleV1Exponent B hd hs₀_pos.le x
  have hΨ_m : Measurable Ψ := by
    have heq : Ψ = fun ω => pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀ + CM ω :=
      funext fun ω => by simp only [CM]; linarith [hpath ω]
    rw [heq]; exact hpathExp_m.add hCM_m
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Ψ ω)) ∂P := by
    have hMCT_L := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
      (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s₀ x ω))))
      (fun R => ((measurable_const.min hV1_m.exp).ennreal_ofReal).aemeasurable)
      (ae_of_all _ fun ω R₁ R₂ h12 => ENNReal.ofReal_le_ofReal (min_le_min_right _ (Nat.cast_le.mpr h12)))
      (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| tendsto_atTop_of_eventually_const
        (i₀ := ⌈Real.exp (counterexampleV1Exponent B hd s₀ x ω)⌉₊) fun R hR =>
          min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR)))
    have hMCT_R := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
      (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (R : ℝ)
        (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) * Real.exp (CM ω)))
      (fun R => (((measurable_const.min hpathExp_m.exp).mul hCM_m.exp).ennreal_ofReal).aemeasurable)
      (ae_of_all _ fun ω R₁ R₂ h12 => ENNReal.ofReal_le_ofReal <|
        mul_le_mul_of_nonneg_right (min_le_min_right _ (Nat.cast_le.mpr h12)) (Real.exp_pos _).le)
      (ae_of_all _ fun ω => by
        have hΨeq : pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀ + CM ω = Ψ ω := by
          simp only [CM]; linarith [hpath ω]
        have hlim : Tendsto
            (fun R : ℕ => min (R : ℝ)
              (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) *
              Real.exp (CM ω))
            atTop (𝓝 (Real.exp (Ψ ω))) := by
          rw [← hΨeq, Real.exp_add]
          exact tendsto_atTop_of_eventually_const
            (i₀ := ⌈Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)⌉₊)
            fun R hR => by
              rw [min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR))]
        exact ENNReal.tendsto_ofReal hlim)
    refine tendsto_nhds_unique hMCT_L (hMCT_R.congr fun R => ?_)
    have hiL : Integrable (fun ω => min (R : ℝ) (Real.exp (counterexampleV1Exponent B hd s₀ x ω))) P :=
      (integrable_const (R : ℝ)).mono' (measurable_const.min hV1_m.exp).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]; exact min_le_left _ _)
    have hiR : Integrable (fun ω => min (R : ℝ)
        (Real.exp (pathExponent (fun r => MultiBrownian.W B r ω ⟨0, hd⟩ + h r) x s₀)) * Real.exp (CM ω)) P :=
      ((hCM_L2.1.integrable one_le_two).const_mul (R : ℝ)).mono'
        ((measurable_const.min hpathExp_m.exp).mul hCM_m.exp).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le),
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le)
    rw [← ofReal_integral_eq_lintegral_ofReal hiR (ae_of_all _ fun _ =>
        mul_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le) (Real.exp_pos _).le),
      ← ofReal_integral_eq_lintegral_ofReal hiL (ae_of_all _ fun _ =>
        le_min (Nat.cast_nonneg R) (Real.exp_pos _).le), hcut R]
  by_cases h1 : Integrable (fun ω => Real.exp (counterexampleV1Exponent B hd s₀ x ω)) P
  · have hfi1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s₀ x ω)) ∂P < ∞ := by
      have h := hasFiniteIntegral_iff_enorm.mp h1.hasFiniteIntegral
      simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le] at h
      exact h
    have hfi2 : ∫⁻ ω, ENNReal.ofReal (Real.exp (Ψ ω)) ∂P < ∞ := by rw [← hlint]; exact hfi1
    have h2 : Integrable (fun ω => Real.exp (Ψ ω)) P :=
      ⟨hΨ_m.exp.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr (by
        simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]; exact hfi2)⟩
    have hnnL : 0 ≤ ∫ ω, Real.exp (counterexampleV1Exponent B hd s₀ x ω) ∂P :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have hnnR : 0 ≤ ∫ ω, Real.exp (Ψ ω) ∂P := integral_nonneg fun _ => (Real.exp_pos _).le
    have hL := ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    have hR := ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun _ => (Real.exp_pos _).le)
    rw [← ENNReal.toReal_ofReal hnnL, ← ENNReal.toReal_ofReal hnnR, hL, hR, hlint]
  · have h2 : ¬ Integrable (fun ω => Real.exp (Ψ ω)) P := fun hi2 => h1
      ⟨hV1_m.exp.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr (by
        have h := hasFiniteIntegral_iff_enorm.mp hi2.hasFiniteIntegral
        simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le] at h
        simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
        rw [hlint]; exact h)⟩
    rw [integral_undef h1, integral_undef h2]

end SignatureVolatility

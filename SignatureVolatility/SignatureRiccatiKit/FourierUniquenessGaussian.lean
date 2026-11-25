module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# C3b. Fourier uniqueness for an L¹ identity against a nondegenerate Gaussian
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The Fourier transform of a real L¹ function against a finite measure vanishes
for every frequency iff the function is a.e. zero, via `Measure.ext_of_charFun`
on the positive and negative parts. -/
private lemma ae_zero_of_fourier_zero_real {μ : Measure ℝ} [IsFiniteMeasure μ]
    {u : ℝ → ℝ} (hu : Integrable u μ)
    (hfourier : ∀ ξ : ℝ, ∫ x : ℝ, (u x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ = 0) :
    ∀ᵐ x : ℝ ∂μ, u x = 0 := by
  let up : ℝ → ℝ := fun x => max (u x) 0
  let um : ℝ → ℝ := fun x => max (-u x) 0
  have hup_nn : ∀ x, 0 ≤ up x := fun x => le_max_right _ _
  have hum_nn : ∀ x, 0 ≤ um x := fun x => le_max_right _ _
  have hup_int : Integrable up μ := hu.pos_part
  have hum_int : Integrable um μ := hu.neg_part
  have hu_eq : ∀ x, u x = up x - um x := fun x => by
    simp only [up, um]
    rcases le_total 0 (u x) with h | h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  have hup_lin : ∫⁻ a, ENNReal.ofReal (up a) ∂μ ≠ ∞ := by
    have : (fun a => ENNReal.ofReal (up a)) = fun a => ‖up a‖ₑ :=
      funext fun a => (Real.enorm_of_nonneg (hup_nn a)).symm
    simpa [this] using hup_int.hasFiniteIntegral.ne
  have hum_lin : ∫⁻ a, ENNReal.ofReal (um a) ∂μ ≠ ∞ := by
    have : (fun a => ENNReal.ofReal (um a)) = fun a => ‖um a‖ₑ :=
      funext fun a => (Real.enorm_of_nonneg (hum_nn a)).symm
    simpa [this] using hum_int.hasFiniteIntegral.ne
  let μp : Measure ℝ := μ.withDensity (fun x => ENNReal.ofReal (up x))
  let μm : Measure ℝ := μ.withDensity (fun x => ENNReal.ofReal (um x))
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity hup_lin
  have : IsFiniteMeasure μm := isFiniteMeasure_withDensity hum_lin
  have hcexp_bd (ξ : ℝ) :
      ∀ᵐ x : ℝ ∂μ, ‖Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun x => by
      simp [Complex.norm_exp]
  have hcexp_meas (ξ : ℝ) :
      AEStronglyMeasurable (fun x : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) μ :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have hupC (ξ : ℝ) : Integrable (fun x : ℝ => (up x : ℂ) *
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) μ :=
    hup_int.ofReal.mul_bdd (hcexp_meas ξ) (hcexp_bd ξ)
  have humC (ξ : ℝ) : Integrable (fun x : ℝ => (um x : ℂ) *
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) μ :=
    hum_int.ofReal.mul_bdd (hcexp_meas ξ) (hcexp_bd ξ)
  have hcf : ∀ ξ : ℝ, charFun μp ξ = charFun μm ξ := fun ξ => by
    have h1 : charFun μp ξ =
        ∫ x : ℝ, (up x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ := by
      rw [charFun_apply_real,
        integral_withDensity_eq_integral_toReal_smul₀
          hup_int.aemeasurable.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change (ENNReal.ofReal (up x)).toReal • Complex.exp (↑ξ * ↑x * I) =
        ↑(up x) * Complex.exp (I * ↑ξ * ↑x)
      rw [ENNReal.toReal_ofReal (hup_nn x), Complex.real_smul]
      simp [mul_comm, mul_left_comm]
    have h2 : charFun μm ξ =
        ∫ x : ℝ, (um x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ := by
      rw [charFun_apply_real,
        integral_withDensity_eq_integral_toReal_smul₀
          hum_int.aemeasurable.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change (ENNReal.ofReal (um x)).toReal • Complex.exp (↑ξ * ↑x * I) =
        ↑(um x) * Complex.exp (I * ↑ξ * ↑x)
      rw [ENNReal.toReal_ofReal (hum_nn x), Complex.real_smul]
      simp [mul_comm, mul_left_comm]
    rw [h1, h2]
    have hsub :
        ∫ x : ℝ, (up x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ -
          ∫ x : ℝ, (um x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ = 0 := by
      rw [← integral_sub (hupC ξ) (humC ξ)]
      convert hfourier ξ using 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp [sub_mul, hu_eq x]
    exact sub_eq_zero.mp hsub
  have hmeas_eq : μp = μm := Measure.ext_of_charFun (funext hcf)
  have hae_dens :
      (fun x => ENNReal.ofReal (up x)) =ᵐ[μ] (fun x => ENNReal.ofReal (um x)) :=
    (withDensity_eq_iff hup_int.aemeasurable.ennreal_ofReal
        hum_int.aemeasurable.ennreal_ofReal hup_lin).mp hmeas_eq
  filter_upwards [hae_dens] with x hx
  have heq : up x = um x := (ENNReal.ofReal_eq_ofReal_iff (hup_nn x) (hum_nn x)).mp hx
  rw [hu_eq x, heq, sub_self]

/-- If the Fourier transform of `(f - G)` against `N(0, t)` vanishes for every
frequency, then `G x = (f x : ℂ)` for `gaussianReal 0 t`-a.e. `x`.
Requires `Integrable (f - G)`: without it, Bochner `integral` of a
non-integrable function is `0`, so the hypothesis would hold vacuously.
The call site in `EntireTransfer` supplies this from the `MemTw` expansion. -/
lemma ae_eq_of_fourier_zero_gaussianReal {t : ℝ} (_ht : 0 < t)
    {f : ℝ → ℝ} {G : ℂ → ℂ}
    (hint : Integrable (fun x : ℝ => (f x : ℂ) - G x)
      (gaussianReal 0 (Real.toNNReal t)))
    (hfourier : ∀ ξ : ℝ,
      ∫ x : ℝ, ((f x : ℂ) - G x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))
        ∂(gaussianReal 0 (Real.toNNReal t)) = 0) :
    ∀ᵐ x : ℝ ∂(gaussianReal 0 (Real.toNNReal t)), G x = (f x : ℂ) := by
  set μ := gaussianReal 0 (Real.toNNReal t)
  set g : ℝ → ℂ := fun x => (f x : ℂ) - G x
  have hcexp_bd (ξ : ℝ) :
      ∀ᵐ x : ℝ ∂μ, ‖Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun x => by simp [Complex.norm_exp]
  have hcexp_meas (ξ : ℝ) :
      AEStronglyMeasurable (fun x : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) μ :=
    (by fun_prop : Continuous _).aestronglyMeasurable
  have hg_exp (ξ : ℝ) : Integrable (fun x : ℝ => g x *
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) μ :=
    hint.mul_bdd (hcexp_meas ξ) (hcexp_bd ξ)
  have hconj : Integrable (fun x : ℝ => conj (g x)) μ :=
    MeasureTheory.Integrable.mono hint (by fun_prop)
      (ae_of_all _ fun x => le_of_eq (Complex.norm_conj (g x)))
  have hconj_exp (ξ : ℝ) : Integrable (fun x : ℝ => conj (g x) *
      Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) μ :=
    hconj.mul_bdd (hcexp_meas ξ) (hcexp_bd ξ)
  have hstar_ft : ∀ ξ : ℝ,
      ∫ x : ℝ, conj (g x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ = 0 := by
    intro ξ
    have h0 : conj (∫ x : ℝ, ((f x : ℂ) - G x) *
        Complex.exp (Complex.I * ↑(-ξ) * (x : ℂ)) ∂μ) = 0 := by
      rw [hfourier (-ξ), map_zero]
    rw [← integral_conj] at h0
    convert h0 using 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change conj (g x) * Complex.exp (I * ↑ξ * ↑x) =
      conj (g x * Complex.exp (I * ↑(-ξ) * ↑x))
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_neg, Complex.conj_ofReal, mul_comm, mul_left_comm]
  have hre_ft : ∀ ξ : ℝ,
      ∫ x : ℝ, ((g x).re : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ = 0 := by
    intro ξ
    have hadd := congrArg (fun z : ℂ => z / 2)
      (show (∫ x, g x * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ) +
          (∫ x, conj (g x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ) = 0 by
        rw [hfourier ξ, hstar_ft ξ, add_zero])
    rw [zero_div, ← integral_add (hg_exp ξ) (hconj_exp ξ), ← integral_div] at hadd
    refine hadd.symm.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) |>.symm
    change (g x * Complex.exp (I * ↑ξ * ↑x) +
        conj (g x) * Complex.exp (I * ↑ξ * ↑x)) / 2 =
      ↑(g x).re * Complex.exp (I * ↑ξ * ↑x)
    rw [← add_mul, Complex.add_conj, mul_div_right_comm]
    simp [Complex.ofReal_mul, mul_comm, mul_left_comm]
  have him_ft : ∀ ξ : ℝ,
      ∫ x : ℝ, ((g x).im : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ = 0 := by
    intro ξ
    have hsub := congrArg (fun z : ℂ => z / (2 * Complex.I))
      (show (∫ x, g x * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ) -
          (∫ x, conj (g x) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) ∂μ) = 0 by
        rw [hfourier ξ, hstar_ft ξ, sub_zero])
    rw [zero_div, ← integral_sub (hg_exp ξ) (hconj_exp ξ), ← integral_div] at hsub
    refine hsub.symm.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) |>.symm
    change (g x * Complex.exp (I * ↑ξ * ↑x) -
        conj (g x) * Complex.exp (I * ↑ξ * ↑x)) / (2 * I) =
      ↑(g x).im * Complex.exp (I * ↑ξ * ↑x)
    rw [← sub_mul, Complex.sub_conj, mul_div_right_comm]
    field_simp [Complex.I_ne_zero]
    simp [Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hre0 := ae_zero_of_fourier_zero_real hint.re hre_ft
  have him0 := ae_zero_of_fourier_zero_real hint.im him_ft
  filter_upwards [hre0, him0] with x hre him
  have hg0 : g x = 0 := Complex.ext hre him
  exact (sub_eq_zero.mp hg0).symm

end SignatureVolatility

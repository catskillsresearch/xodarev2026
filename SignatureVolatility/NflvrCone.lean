module

public import SignatureVolatility.NflvrDefs

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A uniformly bounded-below sequence of integrable mean-zero random variables that converges
almost surely to `V` has integrable limit with nonpositive mean. (Fatou; no H3.) -/
theorem expectation_le_zero_of_bounded_below_local_martingale
    {V : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (M : ℕ → Ω → ℝ)
    (hM_int : ∀ n, Integrable (M n) P)
    (hM_zero : ∀ n, ∫ ω, M n ω ∂P = 0)
    (hM_bdd : ∀ n, ∀ᵐ ω ∂P, -a ≤ M n ω)
    (hM_lim : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (𝓝 (V ω)))
    (hV_meas : AEStronglyMeasurable V P) :
    Integrable V P ∧ ∫ ω, V ω ∂P ≤ 0 := by
  have hnn : ∀ n, 0 ≤ᵐ[P] fun ω => M n ω + a := fun n =>
    (hM_bdd n).mono fun _ h => (neg_le_iff_add_nonneg).mp h
  have hV_bdd : ∀ᵐ ω ∂P, 0 ≤ V ω + a := by
    have hall : ∀ᵐ ω ∂P, ∀ n, 0 ≤ M n ω + a := ae_all_iff.mpr hnn
    filter_upwards [hall, hM_lim] with ω h1 h2
    exact ge_of_tendsto (h2.add_const a) (Eventually.of_forall h1)
  have hfatou : ∫⁻ ω, ENNReal.ofReal (V ω + a) ∂P ≤ ENNReal.ofReal a := by
    calc
      ∫⁻ ω, ENNReal.ofReal (V ω + a) ∂P
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (M n ω + a)) atTop ∂P :=
          lintegral_congr_ae (hM_lim.mono fun ω hω =>
            (ENNReal.tendsto_ofReal (hω.add_const a)).liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (M n ω + a) ∂P) atTop :=
          lintegral_liminf_le' fun n =>
            ENNReal.measurable_ofReal.comp_aemeasurable ((hM_int n).aemeasurable.add_const a)
      _ = liminf (fun _ => ENNReal.ofReal a) atTop := by
          refine congrArg (fun u => liminf u atTop) (funext fun n => ?_)
          have hint : Integrable (fun ω => M n ω + a) P := (hM_int n).add (integrable_const a)
          have hlin : ∫⁻ ω, ENNReal.ofReal (M n ω + a) ∂P = ENNReal.ofReal (∫ ω, (M n ω + a) ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal hint (hnn n)).symm
          rw [hlin, integral_add (hM_int n) (integrable_const a), hM_zero n, zero_add,
            integral_const, probReal_univ, one_smul]
      _ = ENNReal.ofReal a := liminf_const _
  have hVa_int : Integrable (fun ω => V ω + a) P := by
    refine ⟨hV_meas.add aestronglyMeasurable_const, ?_⟩
    rw [HasFiniteIntegral]
    have hcongr : ∫⁻ ω, ‖V ω + a‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (V ω + a) ∂P :=
      lintegral_congr_ae (hV_bdd.mono fun _ h => Real.enorm_eq_ofReal h)
    rw [hcongr]
    exact hfatou.trans_lt ENNReal.ofReal_lt_top
  have hV_int : Integrable V P :=
    (hVa_int.sub (integrable_const a)).congr
      (Eventually.of_forall fun ω => by
        change (V ω + a) - a = V ω
        exact add_sub_cancel_right (V ω) a)
  refine ⟨hV_int, ?_⟩
  have hle : ∫ ω, (V ω + a) ∂P ≤ a := by
    rw [← ENNReal.ofReal_le_ofReal_iff ha, ofReal_integral_eq_lintegral_ofReal hVa_int hV_bdd]
    exact hfatou
  rw [integral_add hV_int (integrable_const a), integral_const, probReal_univ, one_smul] at hle
  linarith

/-- If every element of `K` is integrable with nonpositive mean, then `SatisfiesNFLVR_DS`
holds for `K`. This is the weak-* half of bounded-below NFLVR; it does not use H3. -/
theorem nflvr_ds_of_nonpos_mean {K : Set (Ω → ℝ)}
    (hK : ∀ V ∈ K, Integrable V P ∧ ∫ ω, V ω ∂P ≤ 0) :
    SatisfiesNFLVR_DS P K := by
  intro f hf_nn hf_cl
  have hf_int : Integrable f P := (hf_cl.1.integrable le_top)
  have hf_mean : ∫ ω, f ω ∂P ≤ 0 := by
    have h1 : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨h, hhC, -, hnear⟩ :=
      hf_cl.2 ε hε ({fun _ : Ω => (1 : ℝ)} : Finset (Ω → ℝ)) (by intro g hg; simp at hg; subst hg; exact h1)
    have hmul : ∀ ω, (h ω - f ω) * (1 : ℝ) = h ω - f ω := fun ω => mul_one _
    have : |∫ ω, (h ω - f ω) ∂P| < ε := by
      have := hnear (fun _ => (1 : ℝ)) (by simp)
      simp only [mul_one] at this
      exact this
    obtain ⟨V, hV, u, hu_nn, heq⟩ := hhC.2
    obtain ⟨hV_int, hV_le⟩ := hK V hV
    have hh_int : Integrable h P := (hhC.1.integrable le_top)
    have hf_eq : u =ᵐ[P] fun ω => V ω - h ω :=
      heq.mono fun ω hω => by linarith
    have hu_int : Integrable u P := (hV_int.sub hh_int).congr hf_eq.symm
    have hu_ge : 0 ≤ ∫ ω, u ω ∂P := integral_nonneg_of_ae hu_nn
    have hh_le : ∫ ω, h ω ∂P ≤ 0 := by
      rw [integral_congr_ae heq, integral_sub hV_int hu_int]
      linarith
    have hdiff : |∫ ω, h ω ∂P - ∫ ω, f ω ∂P| < ε := by
      have hint : Integrable (fun ω => h ω - f ω) P := hh_int.sub hf_int
      rwa [← integral_sub hh_int hf_int]
    have : ∫ ω, f ω ∂P ≤ ε := by
      have := abs_lt.mp hdiff
      linarith
    linarith
  have hf_zero : ∫ ω, f ω ∂P = 0 :=
    le_antisymm hf_mean (integral_nonneg_of_ae hf_nn)
  exact (integral_eq_zero_iff_of_nonneg_ae hf_nn hf_int).mp hf_zero

end SignatureVolatility

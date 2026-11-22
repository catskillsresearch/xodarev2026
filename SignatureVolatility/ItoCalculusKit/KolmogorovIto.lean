module

public import BrownianMotion.Continuity.KolmogorovChentsov
public import SignatureVolatility.ItoCalculusKit.DoleansIdentify

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SignatureVolatility

/-!
# A continuous version of the raw Itô integral (Kolmogorov–Chentsov)

For an adapted `L⁸` integrand with eighth-moment Hölder bound, `𝔼 (I_v - I_u)⁸ ≤ C (v - u)⁴`
(`integral_kitItoIntRaw_sub_pow_eight_le`), so the Kolmogorov–Chentsov theorem (vendored
`BrownianMotion`) gives a modification of `s ↦ I_{s ∧ t}` with continuous paths
(`exists_continuous_version_kitItoIntRaw`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma ofReal_abs_rpow_eight (a : ℝ) :
    ENNReal.ofReal |a| ^ (8 : ℝ) = ENNReal.ofReal (a ^ 8) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) (by norm_num)]
  congr 1
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs]
  exact abs_of_nonneg (by positivity)

section Kolmogorov

variable (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- **Kolmogorov–Chentsov for the raw Itô integral**: a modification of `s ↦ I_s` on `[0, t]`
with continuous paths. -/
theorem exists_continuous_version_kitItoIntRaw (hd : 0 < d) (hH : HolderAdapted8 B H t K)
    (ht : 0 ≤ t) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun s => Y s ω) ∧
      ∀ s : ℝ≥0, (s : ℝ) ≤ t → Y s =ᵐ[P] kitItoIntRaw B H s := by
  set C8 : ℝ := 14 ^ 4 * gauss8Const * (128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4) with hC8
  have hC80 : 0 ≤ C8 := by
    have := hH.K_nonneg
    have := gauss8Const_nonneg
    have : 0 ≤ ∫ ω, H 0 ω ^ 8 ∂P := integral_nonneg fun ω => by positivity
    positivity
  set X : ℝ≥0 → Ω → ℝ := fun s => kitItoIntRaw B H (min (s : ℝ) t) with hX
  have hle : ∀ s s' : ℝ≥0, s ≤ s' →
      ∫⁻ ω, edist (X s ω) (X s' ω) ^ (8 : ℝ) ∂P ≤ (C8.toNNReal : ℝ≥0∞) * edist s s' ^ (4 : ℝ) := by
    intro s s' hss'
    have hss : (s : ℝ) ≤ s' := hss'
    set u := min (s : ℝ) t
    set v := min (s' : ℝ) t
    have hu : 0 ≤ u := le_min s.2 ht
    have huv : u ≤ v := min_le_min_right t hss
    have hvt : v ≤ t := min_le_right _ _
    have hvu : v - u ≤ (s' : ℝ) - s := by
      simp only [u, v]
      rcases le_total (s' : ℝ) t with h1 | h1
      · rw [min_eq_left h1, min_eq_left (hss.trans h1)]
      · rw [min_eq_right h1]
        rcases le_total (s : ℝ) t with h2 | h2
        · rw [min_eq_left h2]; linarith
        · rw [min_eq_right h2]; linarith
    obtain ⟨hint, hbd⟩ := integral_kitItoIntRaw_sub_pow_eight_le B hd hH hu huv hvt
    have h1 : ∀ ω, edist (X s ω) (X s' ω) ^ (8 : ℝ) =
        ENNReal.ofReal ((kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ^ 8) := by
      intro ω
      rw [edist_dist, Real.dist_eq, ofReal_abs_rpow_eight]
      congr 1
      simp only [X]
      ring
    simp_rw [h1]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)]
    have h2 : edist s s' ^ (4 : ℝ) = ENNReal.ofReal (((s' : ℝ) - s) ^ 4) := by
      rw [edist_dist, NNReal.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hss), ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hss)
          (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    change _ ≤ ENNReal.ofReal C8 * _
    rw [← ENNReal.ofReal_mul hC80]
    refine ENNReal.ofReal_le_ofReal (hbd.trans ?_)
    gcongr
  have hkol : ∀ s s' : ℝ≥0,
      ∫⁻ ω, edist (X s ω) (X s' ω) ^ (8 : ℝ) ∂P ≤ (C8.toNNReal : ℝ≥0∞) * edist s s' ^ (4 : ℝ) := by
    intro s s'
    rcases le_total s s' with h | h
    · exact hle s s' h
    · simp_rw [edist_comm (X s _), edist_comm s]
      exact hle s' s h
  have hXK : IsKolmogorovProcess X P 8 4 C8.toNNReal :=
    IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun s => measurable_kitItoIntRaw B H _) hkol (by norm_num) (by norm_num)
  obtain ⟨Y, -, hYeq, hYh⟩ := exists_modification_holder_iSup
    isCoverWithBoundedCoveringNumber_Ico_nnreal (p := fun _ => 8) (q := fun _ => 4)
    (M := fun _ => C8.toNNReal) (fun _ => hXK.IsAEKolmogorovProcess) (fun n => by finiteness)
    zero_lt_one (fun _ => by norm_num)
  refine ⟨Y, fun ω => continuous_iff_continuousAt.2 fun s => ?_, fun s hs => ?_⟩
  · obtain ⟨U, hU, C, hC⟩ := hYh ω s (1 / 4) (by norm_num) (by rw [ciSup_const]; norm_num)
    exact (hC.continuousOn (by norm_num)).continuousAt hU
  · filter_upwards [hYeq s] with ω hω
    rw [hω]
    simp only [X, min_eq_left hs]

end Kolmogorov

end SignatureVolatility

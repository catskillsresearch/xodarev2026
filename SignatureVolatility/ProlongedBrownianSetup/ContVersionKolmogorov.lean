module

public import BrownianMotion.Continuity.KolmogorovChentsov
public import SignatureVolatility.ProlongedBrownianSetup.ContVersion


@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SignatureVolatility

/-!
# The dyadic continuous version of a Kolmogorov process

If `𝔼(X_v - X_u)⁸ ≤ C (v - u)⁴` on `[0, T]`, then (Kolmogorov–Chentsov) almost surely the left-dyadic
continuous version `contVersion X` agrees on `[0, T]` with a modification having continuous paths.
Hence `contVersion X` has almost surely continuous paths on `[0, T]` and `contVersion X t = X t`
almost surely for each `t ∈ [0, T]` (`contVersion_kolmogorov`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma ofReal_abs_rpow_eight' (a : ℝ) :
    ENNReal.ofReal |a| ^ (8 : ℝ) = ENNReal.ofReal (a ^ 8) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) (by norm_num)]
  congr 1
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs]
  exact abs_of_nonneg (by positivity)

/-- **Kolmogorov for the dyadic continuous version.** -/
theorem contVersion_kolmogorov {X : ℝ → Ω → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hmeas : ∀ s, 0 ≤ s → s ≤ T → Measurable (X s))
    (hmom : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      Integrable (fun ω => (X v ω - X u ω) ^ 8) P ∧
        ∫ ω, (X v ω - X u ω) ^ 8 ∂P ≤ C * (v - u) ^ 4) :
    (∀ᵐ ω ∂P, ContinuousOn (fun t => contVersion X t ω) (Set.Icc 0 T)) ∧
      ∀ t, 0 ≤ t → t ≤ T → contVersion X t =ᵐ[P] X t := by
  set Z : ℝ≥0 → Ω → ℝ := fun s => X (min (s : ℝ) T) with hZ
  have hle : ∀ s s' : ℝ≥0, s ≤ s' →
      ∫⁻ ω, edist (Z s ω) (Z s' ω) ^ (8 : ℝ) ∂P ≤ (C.toNNReal : ℝ≥0∞) * edist s s' ^ (4 : ℝ) := by
    intro s s' hss'
    have hss : (s : ℝ) ≤ s' := hss'
    set u := min (s : ℝ) T
    set v := min (s' : ℝ) T
    have hu : 0 ≤ u := le_min s.2 hT
    have huv : u ≤ v := min_le_min_right T hss
    have hvt : v ≤ T := min_le_right _ _
    have hvu : v - u ≤ (s' : ℝ) - s := by
      simp only [u, v]
      rcases le_total (s' : ℝ) T with h1 | h1
      · rw [min_eq_left h1, min_eq_left (hss.trans h1)]
      · rw [min_eq_right h1]
        rcases le_total (s : ℝ) T with h2 | h2
        · rw [min_eq_left h2]; linarith
        · rw [min_eq_right h2]; linarith
    obtain ⟨hint, hbd⟩ := hmom u v hu huv hvt
    have h1 : ∀ ω, edist (Z s ω) (Z s' ω) ^ (8 : ℝ) =
        ENNReal.ofReal ((X v ω - X u ω) ^ 8) := by
      intro ω
      rw [edist_dist, Real.dist_eq, ofReal_abs_rpow_eight']
      congr 1
      simp only [Z]
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
    change _ ≤ ENNReal.ofReal C * _
    rw [← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal (hbd.trans ?_)
    gcongr
  have hkol : ∀ s s' : ℝ≥0,
      ∫⁻ ω, edist (Z s ω) (Z s' ω) ^ (8 : ℝ) ∂P ≤ (C.toNNReal : ℝ≥0∞) * edist s s' ^ (4 : ℝ) := by
    intro s s'
    rcases le_total s s' with h | h
    · exact hle s s' h
    · simp_rw [edist_comm (Z s _), edist_comm s]
      exact hle s' s h
  have hZK : IsKolmogorovProcess Z P 8 4 C.toNNReal :=
    IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun s => hmeas _ (le_min s.2 hT) (min_le_right _ _)) hkol (by norm_num) (by norm_num)
  obtain ⟨Y, -, hYeq, hYh⟩ := exists_modification_holder_iSup
    isCoverWithBoundedCoveringNumber_Ico_nnreal (p := fun _ => 8) (q := fun _ => 4)
    (M := fun _ => C.toNNReal) (fun _ => hZK.IsAEKolmogorovProcess) (fun n => by finiteness)
    zero_lt_one (fun _ => by norm_num)
  have hYc : ∀ ω, Continuous fun s => Y s ω := fun ω =>
    continuous_iff_continuousAt.2 fun s => by
      obtain ⟨U, hU, C', hC'⟩ := hYh ω s (1 / 4) (by norm_num) (by rw [ciSup_const]; norm_num)
      exact (hC'.continuousOn (by norm_num)).continuousAt hU
  -- agreement on all dyadic points
  have hdy : ∀ᵐ ω ∂P, ∀ n k : ℕ, Y (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω =
      Z (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    exact hYeq _
  have hgood : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → t ≤ T → contVersion X t ω = Y (Real.toNNReal t) ω := by
    filter_upwards [hdy] with ω hω t ht htT
    refine contVersion_eq_of_tendsto ?_
    have hc : Tendsto (fun n => Y (Real.toNNReal (dyadicFloor n t)) ω) atTop
        (𝓝 (Y (Real.toNNReal t) ω)) :=
      ((hYc ω).tendsto _).comp
        ((continuous_real_toNNReal.tendsto t).comp (tendsto_dyadicFloor ht))
    refine hc.congr fun n => ?_
    have h := hω n ⌊t * 2 ^ n⌋₊
    have hd : dyadicFloor n t = (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n := rfl
    rw [← hd] at h
    rw [h]
    simp only [Z, Real.coe_toNNReal _ (dyadicFloor_nonneg n t),
      min_eq_left ((dyadicFloor_le ht n).trans htT)]
  refine ⟨?_, fun t ht htT => ?_⟩
  · filter_upwards [hgood] with ω hω
    have hcont : ContinuousOn (fun t => Y (Real.toNNReal t) ω) (Set.Icc 0 T) :=
      ((hYc ω).comp continuous_real_toNNReal).continuousOn
    exact hcont.congr fun t ht => hω t ht.1 ht.2
  · filter_upwards [hgood, hYeq (Real.toNNReal t)] with ω h1 h2
    rw [h1 t ht htT, h2]
    simp only [Z, Real.coe_toNNReal _ ht, min_eq_left htT]

end SignatureVolatility

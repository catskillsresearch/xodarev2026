module

public import SignatureVolatility.ItoCalculusKit.KolmogorovIto

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SignatureVolatility

/-!
# Pathwise Hölder regularity from eighth moments

A process with continuous paths on `[0, T]` and `𝔼 (X_v - X_u)⁸ ≤ K (v - u)⁴` has, almost surely,
`7/20`-Hölder paths on `[0, T]` (`ae_holder_of_moment8`, Kolmogorov–Chentsov plus density).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Almost-sure `7/20`-Hölder paths from an eighth-moment bound.** -/
theorem ae_holder_of_moment8 {X : ℝ → Ω → ℝ} {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hmeas : ∀ s, 0 ≤ s → s ≤ T → Measurable (X s))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Set.Icc 0 T))
    (hint : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → Integrable (fun ω => (X v ω - X u ω) ^ 8) P)
    (hmom : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → ∫ ω, (X v ω - X u ω) ^ 8 ∂P ≤ K * (v - u) ^ 4) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T,
      |X s' ω - X s ω| ≤ L * |s' - s| ^ (7 / 20 : ℝ) := by
  set Xn : ℝ≥0 → Ω → ℝ := fun s => X (min (s : ℝ) T) with hXn
  have hle : ∀ s s' : ℝ≥0, s ≤ s' →
      ∫⁻ ω, edist (Xn s ω) (Xn s' ω) ^ (8 : ℝ) ∂P ≤ (K.toNNReal : ℝ≥0∞) * edist s s' ^ (4 : ℝ) := by
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
    have h1 : ∀ ω, edist (Xn s ω) (Xn s' ω) ^ (8 : ℝ) =
        ENNReal.ofReal ((X v ω - X u ω) ^ 8) := by
      intro ω
      rw [edist_dist, Real.dist_eq, ofReal_abs_rpow_eight]
      congr 1
      simp only [Xn]
      ring
    simp_rw [h1]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint u v hu huv hvt)
      (ae_of_all _ fun ω => by positivity)]
    have h2 : edist s s' ^ (4 : ℝ) = ENNReal.ofReal (((s' : ℝ) - s) ^ 4) := by
      rw [edist_dist, NNReal.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hss), ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hss)
          (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    change _ ≤ ENNReal.ofReal K * _
    rw [← ENNReal.ofReal_mul hK]
    refine ENNReal.ofReal_le_ofReal ((hmom u v hu huv hvt).trans ?_)
    have : 0 ≤ v - u := sub_nonneg.mpr huv
    gcongr
  have hkol : ∀ s s' : ℝ≥0,
      ∫⁻ ω, edist (Xn s ω) (Xn s' ω) ^ (8 : ℝ) ∂P ≤ (K.toNNReal : ℝ≥0∞) * edist s s' ^ (4 : ℝ) := by
    intro s s'
    rcases le_total s s' with h | h
    · exact hle s s' h
    · simp_rw [edist_comm (Xn s _), edist_comm s]
      exact hle s' s h
  have hXK : IsKolmogorovProcess Xn P 8 4 K.toNNReal :=
    IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun s => hmeas _ (le_min s.2 hT) (min_le_right _ _)) hkol (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt T
  set U : Set ℝ≥0 := Set.Ico 0 ((n : ℝ≥0) + 1) with hUdef
  have hU : IsOpen U := isCoverWithBoundedCoveringNumber_Ico_nnreal.isOpen n
  obtain ⟨Y, -, hYeq, hYh⟩ := exists_modification_holder
    (isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber n) hU
    hXK.IsAEKolmogorovProcess (by finiteness) zero_lt_one (by norm_num)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hae : ∀ᵐ ω ∂P, ∀ q ∈ U ∩ D, Y q ω = Xn q ω :=
    (ae_ball_iff (hDc.mono Set.inter_subset_right)).2 fun q hq => hYeq q hq.1
  filter_upwards [hae, hcont] with ω hω hcω
  obtain ⟨C, hC⟩ := hYh (7 / 20) (by norm_num) (by norm_num) ω
  have hXc : ContinuousOn (fun s => Xn s ω) U :=
    (hcω.comp_continuous (continuous_subtype_val.min continuous_const)
      (fun s => ⟨le_min s.2 hT, min_le_right _ _⟩)).continuousOn
  have heq : Set.EqOn (fun s => Y s ω) (fun s => Xn s ω) U :=
    Set.EqOn.of_subset_closure (fun q hq => hω q hq) (hC.continuousOn (by norm_num)) hXc
      Set.inter_subset_left (hDd.open_subset_closure_inter hU)
  refine ⟨C, fun s hs s' hs' => ?_⟩
  have hmem : ∀ x : ℝ, (hx : x ∈ Set.Icc 0 T) → (⟨x, hx.1⟩ : ℝ≥0) ∈ U := by
    intro x hx
    refine ⟨zero_le, ?_⟩
    change ((⟨x, hx.1⟩ : ℝ≥0) : ℝ) < ((n : ℝ≥0) + 1 : ℝ≥0)
    push_cast
    linarith [hx.2]
  have hval : ∀ x : ℝ, (hx : x ∈ Set.Icc 0 T) → Y ⟨x, hx.1⟩ ω = X x ω := by
    intro x hx
    rw [show Y ⟨x, hx.1⟩ ω = Xn ⟨x, hx.1⟩ ω from heq (hmem x hx)]
    show X (min x T) ω = X x ω
    rw [min_eq_left hx.2]
  have hd := hC.dist_le (hmem s' hs') (hmem s hs)
  rw [hval s' hs', hval s hs, Real.dist_eq] at hd
  refine hd.trans_eq ?_
  have e2 : (((7 / 20 : ℝ≥0)) : ℝ) = 7 / 20 := by norm_num
  rw [e2]
  congr 2

/-- Brownian paths are almost surely `7/20`-Hölder on `[0, T]`. -/
theorem ae_holder_wnn (B : MultiBrownian Ω P d) (k : Fin d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T,
      |B.Wnn (Real.toNNReal s') ω k - B.Wnn (Real.toNNReal s) ω k| ≤
        L * |s' - s| ^ (7 / 20 : ℝ) :=
  ae_holder_of_moment8 (X := fun s ω => B.Wnn (Real.toNNReal s) ω k) hT gauss8Const_nonneg
    (fun _ _ _ => B.Wnn_meas _ k)
    (ae_of_all _ fun ω => ((B.pathContinuous k ω).comp continuous_real_toNNReal).continuousOn)
    (fun _ _ hu huv _ => integrable_wnnIncr_pow8 B k hu huv)
    (fun _ _ hu huv _ => (integral_wnnIncr_pow8 B k hu huv).le)

/-- Under H1–H2, `σ = ⟨ℓ, Ŵ⟩` has almost surely `7/20`-Hölder paths on `[0, T]`. -/
theorem ae_holder_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    {w : Weight} (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) :
    ∀ᵐ ω ∂P, ∃ L : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ s' ∈ Set.Icc 0 T,
      |signatureSigma B hT ℓ s' ω - signatureSigma B hT ℓ s ω| ≤
        L * |s' - s| ^ (7 / 20 : ℝ) := by
  obtain ⟨K, hK⟩ := holderAdapted8_signatureSigma B hT hw hℓ T
  exact ae_holder_of_moment8 hT.le hK.K_nonneg
    (fun s h0 hs => (hK.meas s h0 hs).mono ((pathFiltration B).le_ambient _) le_rfl)
    (ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ)
    (fun u v hu huv hv => integrable_pow_of_memLp_eight
      ((hK.memLp v (hu.trans huv) hv).sub (hK.memLp u hu (huv.trans hv))) le_rfl)
    (fun u v hu huv hv => hK.holder u v hu huv hv)

end SignatureVolatility

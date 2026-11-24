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

omit [IsProbabilityMeasure P] in
/-- The clamped process `s ↦ X (min s T)` on `ℝ≥0` is a Kolmogorov process. -/
lemma isKolmogorovProcess_clamp {X : ℝ → Ω → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hmeas : ∀ s, 0 ≤ s → s ≤ T → Measurable (X s))
    (hmom : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      Integrable (fun ω => (X v ω - X u ω) ^ 8) P ∧
        ∫ ω, (X v ω - X u ω) ^ 8 ∂P ≤ C * (v - u) ^ 4) :
    IsKolmogorovProcess (fun s : ℝ≥0 => X (min (s : ℝ) T)) P 8 4 C.toNNReal := by
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
  exact
    IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun s => hmeas _ (le_min s.2 hT) (min_le_right _ _)) hkol (by norm_num) (by norm_num)

/-- **Kolmogorov for the dyadic continuous version.** -/
theorem contVersion_kolmogorov {X : ℝ → Ω → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hmeas : ∀ s, 0 ≤ s → s ≤ T → Measurable (X s))
    (hmom : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      Integrable (fun ω => (X v ω - X u ω) ^ 8) P ∧
        ∫ ω, (X v ω - X u ω) ^ 8 ∂P ≤ C * (v - u) ^ 4) :
    (∀ᵐ ω ∂P, ContinuousOn (fun t => contVersion X t ω) (Set.Icc 0 T)) ∧
      ∀ t, 0 ≤ t → t ≤ T → contVersion X t =ᵐ[P] X t := by
  set Z : ℝ≥0 → Ω → ℝ := fun s => X (min (s : ℝ) T) with hZ
  have hZK : IsKolmogorovProcess Z P 8 4 C.toNNReal := isKolmogorovProcess_clamp hT hC hmeas hmom
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

/-! ## Supremum bounds on a countable grid -/

/-- A countable grid of `[0, T]` in `ℝ≥0`, dense in `[0, T]` and containing `0`. -/
def gridNN (T : ℝ) : Set ℝ≥0 := Set.range fun x : ℚ => Real.toNNReal (min (max (x : ℝ) 0) T)

lemma countable_gridNN (T : ℝ) : (gridNN T).Countable := Set.countable_range _

lemma zero_mem_gridNN {T : ℝ} (hT : 0 ≤ T) : (0 : ℝ≥0) ∈ gridNN T :=
  ⟨0, by simp [hT]⟩

lemma coe_le_of_mem_gridNN {T : ℝ} (hT : 0 ≤ T) {s : ℝ≥0} (hs : s ∈ gridNN T) : (s : ℝ) ≤ T := by
  obtain ⟨x, rfl⟩ := hs
  rw [Real.coe_toNNReal _ (le_min (le_max_right _ _) hT)]
  exact min_le_right _ _

/-- The Kolmogorov–Chentsov constant for the grid supremum on `[0, T]`. -/
noncomputable def kolSupConst (T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (T ^ 2) * constL (3 * ((⌈T⌉₊ : ℝ≥0∞) + 1)) 1 8 4 ((1 / 4 : ℝ≥0) : ℝ)

lemma kolSupConst_ne_top (T : ℝ) : kolSupConst T ≠ ⊤ := by
  unfold kolSupConst
  have hc : 3 * ((⌈T⌉₊ : ℝ≥0∞) + 1) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
  have hβ : ((1 / 4 : ℝ≥0) : ℝ) < (4 - 1) / 8 := by norm_num
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (constL_lt_top (c := 3 * ((⌈T⌉₊ : ℝ≥0∞) + 1)) (d := 1) (p := 8) (q := 4) hc
      (by norm_num) (by norm_num) (by norm_num) hβ).ne

omit [IsProbabilityMeasure P] in
/-- **Kolmogorov–Chentsov supremum bound.** If `𝔼(X_v - X_u)⁸ ≤ C (v - u)⁴` on `[0, T]`, the
`8`-th moment of `sup_{s ∈ grid} |X_s - X_0|` is at most `C · kolSupConst T`. -/
theorem lintegral_iSup_gridNN_le {X : ℝ → Ω → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hmeas : ∀ s, 0 ≤ s → s ≤ T → Measurable (X s))
    (hmom : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      Integrable (fun ω => (X v ω - X u ω) ^ 8) P ∧
        ∫ ω, (X v ω - X u ω) ^ 8 ∂P ≤ C * (v - u) ^ 4) :
    ∫⁻ ω, (⨆ s : gridNN T, ENNReal.ofReal |X s ω - X 0 ω|) ^ (8 : ℝ) ∂P ≤
      ENNReal.ofReal C * kolSupConst T := by
  set Z : ℝ≥0 → Ω → ℝ := fun s => X (min (s : ℝ) T) with hZ
  have hZK : IsKolmogorovProcess Z P 8 4 C.toNNReal := isKolmogorovProcess_clamp hT hC hmeas hmom
  set n := ⌈T⌉₊
  have hU : gridNN T ⊆ Set.Ico (0 : ℝ≥0) (n + 1) := by
    intro s hs
    refine ⟨bot_le, ?_⟩
    have h1 := coe_le_of_mem_gridNN hT hs
    have h2 : T ≤ n := Nat.le_ceil T
    have : (s : ℝ) < n + 1 := by linarith
    exact_mod_cast this
  have : Countable (gridNN T) := (countable_gridNN T).to_subtype
  have hKC := countable_kolmogorov_chentsov
    (isCoverWithBoundedCoveringNumber_Ico_nnreal.hasBoundedCoveringNumber n)
    hZK.IsAEKolmogorovProcess (by norm_num) (by norm_num) (β := 1 / 4) (by norm_num)
    (gridNN T) hU
  set R : Ω → ℝ≥0∞ := fun ω => ⨆ (s : gridNN T) (t : gridNN T),
    edist (Z s ω) (Z t ω) ^ (8 : ℝ) / edist s t ^ (((1 / 4 : ℝ≥0) : ℝ) * 8)
  have hpt : ∀ ω, (⨆ s : gridNN T, ENNReal.ofReal |X s ω - X 0 ω|) ^ (8 : ℝ) ≤
      ENNReal.ofReal (T ^ 2) * R ω := by
    intro ω
    set A := ENNReal.ofReal (T ^ 2) * R ω
    have hs : ∀ s : gridNN T, ENNReal.ofReal |X s ω - X 0 ω| ≤ A ^ ((8 : ℝ)⁻¹) := by
      intro s
      have hsT := coe_le_of_mem_gridNN hT s.2
      have hZs : Z s ω = X s ω := by simp [Z, min_eq_left hsT]
      have hZ0 : Z 0 ω = X 0 ω := by simp [Z, min_eq_left hT]
      have h8 : ENNReal.ofReal |X s ω - X 0 ω| ^ (8 : ℝ) ≤ A := by
        have he : edist (Z s ω) (Z 0 ω) = ENNReal.ofReal |X s ω - X 0 ω| := by
          rw [edist_dist, Real.dist_eq, hZs, hZ0]
        have hR : edist (Z s ω) (Z 0 ω) ^ (8 : ℝ) / edist (s : ℝ≥0) 0 ^ (((1 / 4 : ℝ≥0) : ℝ) * 8) ≤
            R ω := by
          refine le_trans ?_ (le_iSup _ s)
          exact le_iSup (fun t : gridNN T => edist (Z s ω) (Z t ω) ^ (8 : ℝ) /
            edist (s : ℝ≥0) t ^ (((1 / 4 : ℝ≥0) : ℝ) * 8)) ⟨0, zero_mem_gridNN hT⟩
        have hq : ((1 / 4 : ℝ≥0) : ℝ) * 8 = 2 := by norm_num
        rw [hq, he] at hR
        set e := edist (s : ℝ≥0) 0 ^ (2 : ℝ)
        have heT : e ≤ ENNReal.ofReal (T ^ 2) := by
          have h1 : edist (s : ℝ≥0) 0 = ENNReal.ofReal (s : ℝ) := by
            rw [edist_dist, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
              abs_of_nonneg (NNReal.coe_nonneg _)]
          simp only [e, h1]
          rw [ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg _) (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact pow_le_pow_left₀ (NNReal.coe_nonneg _) hsT 2
        by_cases he0 : e = 0
        · have hs0 : (s : ℝ≥0) = 0 := by
            simp only [e] at he0
            rw [ENNReal.rpow_eq_zero_iff] at he0
            rcases he0 with ⟨h, -⟩ | ⟨h, h'⟩
            · exact edist_eq_zero.1 h
            · norm_num at h'
          have : X (s : ℝ≥0) ω = X 0 ω := by rw [hs0]; simp
          rw [this, sub_self, abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
          exact bot_le
        have heTop : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heT
        calc ENNReal.ofReal |X s ω - X 0 ω| ^ (8 : ℝ)
            = ENNReal.ofReal |X s ω - X 0 ω| ^ (8 : ℝ) / e * e :=
              (ENNReal.div_mul_cancel he0 heTop).symm
          _ ≤ R ω * ENNReal.ofReal (T ^ 2) := mul_le_mul' hR heT
          _ = A := mul_comm _ _
      calc ENNReal.ofReal |X s ω - X 0 ω|
          = (ENNReal.ofReal |X s ω - X 0 ω| ^ (8 : ℝ)) ^ ((8 : ℝ)⁻¹) := by
            rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num), ENNReal.rpow_one]
        _ ≤ A ^ ((8 : ℝ)⁻¹) := ENNReal.rpow_le_rpow h8 (by norm_num)
    calc (⨆ s : gridNN T, ENNReal.ofReal |X s ω - X 0 ω|) ^ (8 : ℝ)
        ≤ (A ^ ((8 : ℝ)⁻¹)) ^ (8 : ℝ) := ENNReal.rpow_le_rpow (iSup_le hs) (by norm_num)
      _ = A := by rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]
  calc ∫⁻ ω, (⨆ s : gridNN T, ENNReal.ofReal |X s ω - X 0 ω|) ^ (8 : ℝ) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (T ^ 2) * R ω ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (T ^ 2) * ∫⁻ ω, R ω ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (T ^ 2) * ((C.toNNReal : ℝ≥0∞) *
          constL (3 * ((n : ℝ≥0∞) + 1)) 1 8 4 ((1 / 4 : ℝ≥0) : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal C * kolSupConst T := by
        simp only [kolSupConst, n]
        rw [show ((C.toNNReal : ℝ≥0∞)) = ENNReal.ofReal C from rfl]
        ring

/-- For a path continuous on `[0, T]`, the grid supremum controls every point of `[0, T]`. -/
lemma ofReal_abs_sub_le_iSup_gridNN {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Set.Icc 0 T)) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    ENNReal.ofReal |f s - f 0| ≤ ⨆ g : gridNN T, ENNReal.ofReal |f g - f 0| := by
  set φ : ℝ → ℝ := fun x => min (max x 0) T
  have hφc : Continuous φ := (continuous_id.max continuous_const).min continuous_const
  have hφm : ∀ x, φ x ∈ Set.Icc 0 T := fun x => ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩
  have hF : Continuous fun x => ENNReal.ofReal |f (φ x) - f 0| :=
    ENNReal.continuous_ofReal.comp ((hf.comp_continuous hφc hφm).sub continuous_const).abs
  have hφs : φ s = s := by simp only [φ, max_eq_left hs.1, min_eq_left hs.2]
  rw [← hφs]
  refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on (p := fun x =>
    ENNReal.ofReal |f (φ x) - f 0| ≤ ⨆ g : gridNN T, ENNReal.ofReal |f g - f 0|) s
    (isClosed_le hF continuous_const) fun x => ?_
  have hmem : Real.toNNReal (φ x) ∈ gridNN T := ⟨x, rfl⟩
  refine le_trans (le_of_eq ?_) (le_iSup (fun g : gridNN T => ENNReal.ofReal |f g - f 0|)
    ⟨_, hmem⟩)
  simp only [Real.coe_toNNReal _ (hφm x).1]

end SignatureVolatility

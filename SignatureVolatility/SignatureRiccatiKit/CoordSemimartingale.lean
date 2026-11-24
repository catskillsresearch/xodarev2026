module

public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.IsSpecialSemimartingale

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace SignatureVolatility

/-!
# Signature coordinates are special semimartingales (paper Lemma 43)

Every coordinate `⟨e_I, Ŵ_t⟩` is a finite combination `Σ c_p ⟨e_{w_p}, W^{Itô}_t⟩` of Itô word
integrals (`stratWordIntegral_eq_list`). Words whose outermost letter is a space letter are Itô
integrals, hence martingales; words whose outermost letter is the time letter are time integrals
`∫₀ᵗ X_r dr` of a.s. continuous processes, hence Lipschitz on `[0, T]` with an integrable constant
(Kolmogorov grid supremum).

* `condExp_itoIntegral_process`: the raw Itô integral against any coordinate is a martingale;
* `condExp_itoWordIntegral_space`: so is every space-headed Itô word integral;
* `ae_lipschitz_itoWordIntegral_nonSpace`: time-headed word integrals are Lipschitz on `[0, T]`;
* `isSpecialSemimartingale_paperSig2_coeff`: Lemma 43 for the paper setup.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Martingale property of the raw Itô integral against any coordinate -/

section Orthogonal

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- `L⁴` rate of the uniform sums towards the raw Itô integral. -/
theorem integral_unifRiemann_sub_itoIntegral_process_le (ht : 0 ≤ t) (hH : HolderAdapted B H t K)
    {N : ℕ} (hN : 0 < N) :
    Integrable (fun ω => (unifRiemann B k H t N ω - itoIntegral_process B k H 0 t ω) ^ 4) P ∧
      ∫ ω, (unifRiemann B k H t N ω - itoIntegral_process B k H 0 t ω) ^ 4 ∂P ≤
        8 * (16 * gaussFourthConst * K * t ^ 4 / (N : ℝ) ^ 2) := by
  have hI := itoIntegral_process_of_holderAdapted B k hH ht
  have LN := memLp_unifRiemann B k ht hH hN
  have hg : AEStronglyMeasurable
      (fun ω => unifRiemann B k H t N ω - itoIntegral_process B k H 0 t ω) P :=
    (LN.sub hI.2).aestronglyMeasurable
  have hfL : ∀ M : ℕ, MemLp (fun ω => unifRiemann B k H t N ω -
      unifRiemann B k H t (M + 1) ω) 4 P := fun M =>
    LN.sub (memLp_unifRiemann B k ht hH M.succ_pos)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun M : ℕ => unifRiemann B k H t N ω -
      unifRiemann B k H t (M + 1) ω) atTop
      (𝓝 (unifRiemann B k H t N ω - itoIntegral_process B k H 0 t ω)) := by
    filter_upwards [hI.1] with ω hω
    exact tendsto_const_nhds.sub hω
  set C₀ : ℝ := 16 * gaussFourthConst * K * t ^ 4 with hC₀
  have hbc : Tendsto (fun M : ℕ => 8 * (C₀ / (N : ℝ) ^ 2) +
      8 * (C₀ / ((M + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 (8 * (C₀ / (N : ℝ) ^ 2))) := by
    have h1 : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have h2 := (tendsto_const_nhds (x := C₀)).div_atTop h1
    have h3 := (h2.const_mul 8).const_add (8 * (C₀ / (N : ℝ) ^ 2))
    simpa using h3
  exact integral_pow_four_le_of_tendsto hg (fun M => (hfL M).aestronglyMeasurable.aemeasurable)
    hlim (fun M => integrable_pow_of_memLp_four (hfL M) (k := 4) le_rfl)
    (fun M => integral_unifRiemann_sub_le B k ht hH hN M.succ_pos) hbc

/-- `L⁴` rate of the off-grid sums towards the raw Itô increment. -/
theorem integral_itoIntegral_process_sub_offRiemann_le (hH : HolderAdapted B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    MemLp (fun ω => itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω -
      offRiemann B k H u v N ω) 4 P ∧
    ∫ ω, (itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω -
      offRiemann B k H u v N ω) ^ 4 ∂P ≤
        27 * gaussFourthConst * K * (144 * v ^ 4 + 128 * u ^ 4) / (N : ℝ) ^ 2 := by
  have hv : 0 < v := hu.trans_lt huv
  have hHv := hH.mono hvt
  have hHu := hH.mono (huv.le.trans hvt)
  obtain ⟨ha, ha'⟩ := integral_unifRiemann_sub_itoIntegral_process_le B k hv.le hHv hN
  obtain ⟨hb, hb'⟩ := integral_unifRiemann_sub_itoIntegral_process_le B k hu hHu hN
  obtain ⟨hc, hc'⟩ := integral_gridChange_le B k hH hu huv hvt hN
  have hIv := (itoIntegral_process_of_holderAdapted B k hHv hv.le).2
  have hIu := (itoIntegral_process_of_holderAdapted B k hHu hu).2
  have hL : MemLp (fun ω => itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω -
      offRiemann B k H u v N ω) 4 P :=
    (hIv.sub hIu).sub (memLp_offRiemann B k hH hu huv.le hvt hN)
  refine ⟨hL, ?_⟩
  set Iv := itoIntegral_process B k H 0 v
  set Iu := itoIntegral_process B k H 0 u
  have hpt : (fun ω => (Iv ω - Iu ω - offRiemann B k H u v N ω) ^ 4) ≤ fun ω =>
      27 * ((unifRiemann B k H v N ω - Iv ω) ^ 4 +
        (unifRiemann B k H u N ω - Iu ω) ^ 4 +
        (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω) ^ 4) := by
    intro ω
    have h := pow_four_add3_le (-(unifRiemann B k H v N ω - Iv ω))
      (unifRiemann B k H u N ω - Iu ω)
      (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω)
    calc _ = (-(unifRiemann B k H v N ω - Iv ω) +
          (unifRiemann B k H u N ω - Iu ω) +
          (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω)) ^ 4 := by
          ring
      _ ≤ _ := h
      _ = _ := by ring
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc _ ≤ ∫ ω, 27 * ((unifRiemann B k H v N ω - Iv ω) ^ 4 +
        (unifRiemann B k H u N ω - Iu ω) ^ 4 +
        (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω) ^ 4) ∂P :=
        integral_mono (integrable_pow_of_memLp_four hL (k := 4) le_rfl)
          (((ha.add hb).add hc).const_mul 27) hpt
    _ = 27 * ((∫ ω, (unifRiemann B k H v N ω - Iv ω) ^ 4 ∂P) +
        (∫ ω, (unifRiemann B k H u N ω - Iu ω) ^ 4 ∂P) +
        ∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω -
          offRiemann B k H u v N ω) ^ 4 ∂P) := by
        have hab : Integrable (fun ω => (unifRiemann B k H v N ω - Iv ω) ^ 4 +
            (unifRiemann B k H u N ω - Iu ω) ^ 4) P := ha.add hb
        rw [integral_const_mul, integral_add hab hc, integral_add ha hb]
    _ ≤ 27 * (8 * (16 * gaussFourthConst * K * v ^ 4 / (N : ℝ) ^ 2) +
        8 * (16 * gaussFourthConst * K * u ^ 4 / (N : ℝ) ^ 2) +
        16 * gaussFourthConst * (Real.sqrt K * (v / (N : ℝ)) * v) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hH.K_nonneg]
        field_simp
        ring

/-- Raw Itô increments against any coordinate are orthogonal to the past. -/
theorem integral_mul_itoIntegral_process_sub_eq_zero (hH : HolderAdapted B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) {g : Ω → ℝ}
    (hg : Measurable[(pathFiltration B).σAlg u] g) (hg2 : MemLp g 2 P) :
    ∫ ω, g ω * (itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω) ∂P = 0 := by
  rcases huv.eq_or_lt with rfl | huv'
  · simp
  set C : ℝ := 27 * gaussFourthConst * K * (144 * v ^ 4 + 128 * u ^ 4) with hC
  set A : ℝ := Real.sqrt (∫ ω, g ω ^ 2 ∂P) with hA
  set Iv := itoIntegral_process B k H 0 v
  set Iu := itoIntegral_process B k H 0 u
  have hbound : ∀ N : ℕ, 0 < N → |∫ ω, g ω * (Iv ω - Iu ω) ∂P|
      ≤ A * Real.sqrt (Real.sqrt C / (N : ℝ)) := by
    intro N hN
    obtain ⟨hL, hle⟩ := integral_itoIntegral_process_sub_offRiemann_le B k hH hu huv' hvt hN
    have hoff := memLp_offRiemann B k hH hu huv hvt hN
    have hY2 := hL.mono_exponent (p := 2) (by norm_num)
    have hsplit : ∫ ω, g ω * (Iv ω - Iu ω) ∂P =
        (∫ ω, g ω * (Iv ω - Iu ω - offRiemann B k H u v N ω) ∂P) +
        ∫ ω, g ω * offRiemann B k H u v N ω ∂P := by
      rw [← integral_add (integrable_mul_of_memLp_two hg2 hY2)
        (integrable_mul_of_memLp_two hg2 (hoff.mono_exponent (by norm_num)))]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only
      ring
    rw [hsplit, integral_mul_offRiemann_eq_zero B k hH hu huv hvt hN hg hg2, add_zero]
    refine (abs_integral_mul_le_sqrt hg2 hY2).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    have h1 := sq_integral_sq_le_integral_pow_four hL
    have hnn : 0 ≤ ∫ ω, (Iv ω - Iu ω - offRiemann B k H u v N ω) ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    have h2 := Real.abs_le_sqrt (h1.trans hle)
    rw [abs_of_nonneg hnn, Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)] at h2
    exact h2
  have ht : Tendsto (fun M : ℕ => A * Real.sqrt (Real.sqrt C / ((M + 1 : ℕ) : ℝ))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_const_nhds (x := Real.sqrt C)).div_atTop h1
    have h3 := ((Real.continuous_sqrt.tendsto 0).comp h2).const_mul A
    rw [Real.sqrt_zero, mul_zero] at h3
    exact h3
  exact abs_nonpos_iff.mp (ge_of_tendsto' ht fun M => hbound (M + 1) M.succ_pos)

/-- **Martingale property of the raw Itô integral** against any coordinate. -/
theorem condExp_itoIntegral_process (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) :
    P[itoIntegral_process B k H 0 v | (pathFiltration B).σAlg u] =ᵐ[P]
      itoIntegral_process B k H 0 u := by
  have hv := hu.trans huv
  have hIv := ((itoIntegral_process_of_holderAdapted B k (hH.mono hvt) hv).2).integrable
    (by norm_num)
  have hIu := ((itoIntegral_process_of_holderAdapted B k (hH.mono (huv.trans hvt)) hu).2).integrable
    (by norm_num)
  have hIum : Measurable[(pathFiltration B).σAlg u] (itoIntegral_process B k H 0 u) :=
    measurable_itoIntegral_process_pathFiltration B k H (fun r hr0 hr =>
      (hH.meas r hr0 (hr.trans (huv.trans hvt))).mono ((pathFiltration B).mono hr) le_rfl)
      le_rfl hu le_rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration B).le_ambient u) hIv
    (fun s _ _ => hIu.integrableOn) (fun s hs _ => ?_) hIum.aestronglyMeasurable).symm
  have hsa : MeasurableSet s := (pathFiltration B).le_ambient u _ hs
  set ind : Ω → ℝ := s.indicator fun _ => (1 : ℝ) with hinddef
  have hg : Measurable[(pathFiltration B).σAlg u] ind := measurable_const.indicator hs
  have hg2 : MemLp ind 2 P :=
    MemLp.of_bound (hg.mono ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by by_cases h : ω ∈ s <;> simp [hinddef, h])
  have h0 := integral_mul_itoIntegral_process_sub_eq_zero B k hH hu huv hvt hg hg2
  have hpt : ∀ f : Ω → ℝ, (fun ω => ind ω * f ω) = s.indicator f := fun f => by
    funext ω; by_cases h : ω ∈ s <;> simp [hinddef, h]
  have hind : ∀ f : Ω → ℝ, ∫ ω in s, f ω ∂P = ∫ ω, ind ω * f ω ∂P := fun f => by
    rw [hpt f, integral_indicator hsa]
  have hint : ∀ f : Ω → ℝ, Integrable f P → Integrable (fun ω => ind ω * f ω) P :=
    fun f hf => by rw [hpt f]; exact hf.indicator hsa
  rw [hind, hind]
  have h1 : ∫ ω, ind ω * (itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω) ∂P =
      ∫ ω, ind ω * itoIntegral_process B k H 0 v ω ∂P -
        ∫ ω, ind ω * itoIntegral_process B k H 0 u ω ∂P := by
    rw [← integral_sub (hint _ hIv) (hint _ hIu)]
    congr 1; funext ω; ring
  linarith

end Orthogonal

/-! ## Itô word integrals -/

section Words

variable (B : MultiBrownian Ω P d)

/-- Whether the outermost (first, in Itô order) letter of a word is a space letter. -/
def isSpaceHead : Word (d + 1) → Bool
  | [] => false
  | j :: _ => decide ((j : ℕ) ≠ 0)

lemma exists_of_isSpaceHead {w : Word (d + 1)} (h : isSpaceHead w = true) :
    ∃ (k : Fin d) (K : Word (d + 1)), w = k.succ :: K := by
  match w, h with
  | j :: K, h =>
    have hj : (j : ℕ) ≠ 0 := by simpa [isSpaceHead] using h
    have hj' : j ≠ 0 := fun e => hj (by simp [e])
    exact ⟨j.pred hj', K, by rw [Fin.succ_pred]⟩

lemma eq_of_not_isSpaceHead {w : Word (d + 1)} (h : ¬ isSpaceHead w = true) :
    w = [] ∨ ∃ K : Word (d + 1), w = (0 : Fin (d + 1)) :: K := by
  match w, h with
  | [], _ => exact Or.inl rfl
  | j :: K, h =>
    have hj : (j : ℕ) = 0 := by simpa [isSpaceHead] using h
    exact Or.inr ⟨K, by rw [show j = 0 from Fin.ext hj]⟩

lemma integrable_itoWordIntegral {t : ℝ} (ht : 0 ≤ t) (w : Word (d + 1)) :
    Integrable (fun ω => itoWordIntegral B 0 t ω w) P :=
  (memLp_itoWordIntegral B ht w (q := 2) le_rfl).integrable (by norm_num)

lemma memLp_two_itoWordIntegral {t : ℝ} (ht : 0 ≤ t) (w : Word (d + 1)) :
    MemLp (fun ω => itoWordIntegral B 0 t ω w) 2 P :=
  (memLp_itoWordIntegral B ht w (q := 2) le_rfl).mono_exponent (by norm_num)

lemma holderAdapted_itoWordIntegral {t : ℝ} (ht : 0 ≤ t) (K : Word (d + 1)) :
    ∃ C, HolderAdapted B (fun r ω => itoWordIntegral B 0 r ω K) t C := by
  by_cases hK : K = []
  · subst hK
    refine ⟨0, ⟨le_rfl, fun u _ _ => ?_, fun u _ _ => ?_, fun u v _ _ _ => ?_⟩⟩
    · simp only [itoWordIntegral_empty]; exact measurable_const
    · simp only [itoWordIntegral_empty]; exact memLp_const 1
    · simp [itoWordIntegral_empty]
  · obtain ⟨L, hH⟩ := (levelBound_itoWordIntegral B ht K hK).holderAdaptedEven le_rfl
    exact ⟨_, hH.toHolderAdapted le_rfl⟩

lemma ae_itoWordIntegral_eq_itoIntegral_process (k : Fin d) (K : Word (d + 1)) {t : ℝ}
    (ht : 0 ≤ t) :
    (fun ω => itoWordIntegral B 0 t ω (k.succ :: K)) =ᵐ[P]
      itoIntegral_process B k (fun r ω => itoWordIntegral B 0 r ω K) 0 t := by
  filter_upwards [ae_tendsto_itoRiemann_start B le_rfl k K ht] with ω hω
  simp only [itoIntegral_process, ht, ↓reduceDIte]
  exact hω.limUnder_eq.symm

/-- **Space-headed Itô word integrals are martingales** for the Brownian path filtration. -/
theorem condExp_itoWordIntegral_space (k : Fin d) (K : Word (d + 1)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    P[fun ω => itoWordIntegral B 0 t ω (k.succ :: K) | (pathFiltration B).σAlg s] =ᵐ[P]
      fun ω => itoWordIntegral B 0 s ω (k.succ :: K) := by
  obtain ⟨C, hH⟩ := holderAdapted_itoWordIntegral B (hs.trans hst) K
  exact (condExp_congr_ae (ae_itoWordIntegral_eq_itoIntegral_process B k K (hs.trans hst))).trans
    ((condExp_itoIntegral_process B k hH hs hst le_rfl).trans
      (ae_itoWordIntegral_eq_itoIntegral_process B k K hs).symm)

/-- The increment `c (X_t - X_0)` of a space-headed word integral is a martingale. -/
lemma condExp_coordTerm {w : Word (d + 1)} (hw : isSpaceHead w = true) (c : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    P[fun ω => c * (itoWordIntegral B 0 t ω w - itoWordIntegral B 0 0 ω w) |
      (pathFiltration B).σAlg s] =ᵐ[P]
      fun ω => c * (itoWordIntegral B 0 s ω w - itoWordIntegral B 0 0 ω w) := by
  obtain ⟨k, K, rfl⟩ := exists_of_isSpaceHead hw
  set w := k.succ :: K
  have h1 := condExp_itoWordIntegral_space B k K hs hst
  have h0 : P[fun ω => itoWordIntegral B 0 0 ω w | (pathFiltration B).σAlg s] =
      fun ω => itoWordIntegral B 0 0 ω w :=
    condExp_of_stronglyMeasurable ((pathFiltration B).le_ambient s)
      (measurable_itoWordIntegral_pathFiltration B le_rfl le_rfl hs w).stronglyMeasurable
      (integrable_itoWordIntegral B le_rfl w)
  have hsub : P[fun ω => itoWordIntegral B 0 t ω w - itoWordIntegral B 0 0 ω w |
      (pathFiltration B).σAlg s] =ᵐ[P]
      P[fun ω => itoWordIntegral B 0 t ω w | (pathFiltration B).σAlg s] -
        P[fun ω => itoWordIntegral B 0 0 ω w | (pathFiltration B).σAlg s] :=
    condExp_sub (integrable_itoWordIntegral B (hs.trans hst) w)
      (integrable_itoWordIntegral B le_rfl w) _
  have hsm := condExp_smul (μ := P) c
    (fun ω => itoWordIntegral B 0 t ω w - itoWordIntegral B 0 0 ω w) ((pathFiltration B).σAlg s)
  change P[c • (fun ω => itoWordIntegral B 0 t ω w - itoWordIntegral B 0 0 ω w) |
    (pathFiltration B).σAlg s] =ᵐ[P] _
  filter_upwards [hsm, hsub, h1] with ω e1 e2 e3
  rw [e1, Pi.smul_apply, smul_eq_mul, e2, Pi.sub_apply, e3, h0]

/-! ### Time-headed words: Lipschitz paths with an integrable constant -/

variable {T : ℝ}

/-- Kolmogorov grid supremum `sup_{s ∈ grid} |X_s - X_0|` of a word integral on `[0, T]`. -/
def wordSup (T : ℝ) (K : Word (d + 1)) (ω : Ω) : ℝ≥0∞ :=
  ⨆ g : gridNN T, ENNReal.ofReal |itoWordIntegral B 0 ((g : ℝ≥0) : ℝ) ω K -
    itoWordIntegral B 0 0 ω K|

lemma measurable_wordSup (T : ℝ) (K : Word (d + 1)) : Measurable (wordSup B T K) := by
  have : Countable (gridNN T) := (countable_gridNN T).to_subtype
  exact Measurable.iSup fun g => (((measurable_itoWordIntegral B 0 _ K).sub
    (measurable_itoWordIntegral B 0 0 K)).abs).ennreal_ofReal

lemma lintegral_wordSup_ne_top (hT : 0 ≤ T) (K : Word (d + 1)) :
    ∫⁻ ω, wordSup B T K ω ∂P ≠ ⊤ := by
  by_cases hK : K = []
  · subst hK; simp [wordSup, itoWordIntegral_empty]
  have hX := levelBound_itoWordIntegral B hT K hK
  have hL0 := hX.L_nonneg 4 (by norm_num)
  have h8 := lintegral_iSup_gridNN_le (P := P) (X := fun s ω => itoWordIntegral B 0 s ω K)
    (C := wordIncr 4 T K ^ 4) hT (pow_nonneg hL0 4)
    (fun s _ _ => measurable_itoWordIntegral B 0 s K) (fun u v hu huv hvT => by
      have hm : MemLp (fun ω => itoWordIntegral B 0 v ω K - itoWordIntegral B 0 u ω K)
          (2 * 4 : ℕ) P :=
        (hX.memLp 4 (by norm_num) v (hu.trans huv) hvT).sub (hX.memLp 4 (by norm_num) u hu
          (huv.trans hvT))
      refine ⟨integrable_pow_of_memLp_evenDeg (N := 2 * 4) ⟨4, rfl⟩ hm, ?_⟩
      have hb := hX.incr 4 (by norm_num) u v hu huv hvT
      have hnn : 0 ≤ ∫ ω, (itoWordIntegral B 0 v ω K - itoWordIntegral B 0 u ω K) ^ (2 * 4) ∂P :=
        integral_nonneg fun ω => (even_two_mul 4).pow_nonneg _
      have h4 := pow_le_pow_left₀ (nrm_nonneg 4 hnn) hb 4
      rw [nrm_pow (by norm_num) hnn, mul_pow] at h4
      exact h4)
  have hpt : ∀ ω, wordSup B T K ω ≤ 1 + wordSup B T K ω ^ (8 : ℝ) := fun ω => by
    by_cases h : wordSup B T K ω ≤ 1
    · exact le_add_right h
    · refine le_add_left ?_
      calc wordSup B T K ω = wordSup B T K ω ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
        _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le (not_le.1 h).le (by norm_num)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ne_top_of_le_ne_top ?_ h8⟩
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (kolSupConst_ne_top T)

/-- Integrable bound `sup_{[0, T]} |X_r| ≤ wordLip` for a word integral. -/
def wordLip (T : ℝ) (K : Word (d + 1)) (ω : Ω) : ℝ :=
  (wordSup B T K ω).toReal + |itoWordIntegral B 0 0 ω K|

lemma wordLip_nonneg (T : ℝ) (K : Word (d + 1)) (ω : Ω) : 0 ≤ wordLip B T K ω :=
  add_nonneg ENNReal.toReal_nonneg (abs_nonneg _)

lemma integrable_wordLip (hT : 0 ≤ T) (K : Word (d + 1)) : Integrable (wordLip B T K) P :=
  (integrable_toReal_of_lintegral_ne_top (measurable_wordSup B T K).aemeasurable
    (lintegral_wordSup_ne_top B hT K)).add (integrable_itoWordIntegral B le_rfl K).abs

lemma ae_abs_le_wordLip (hT : 0 ≤ T) (K : Word (d + 1)) :
    ∀ᵐ ω ∂P, ∀ r ∈ Icc 0 T, |itoWordIntegral B 0 r ω K| ≤ wordLip B T K ω := by
  filter_upwards [ae_lt_top (measurable_wordSup B T K) (lintegral_wordSup_ne_top B hT K),
    ae_continuousOn_itoWordIntegral B hT] with ω hS hc r hr
  have h := ofReal_abs_sub_le_iSup_gridNN hT (hc K) hr
  have h' := (ENNReal.ofReal_le_iff_le_toReal hS.ne).1 h
  have h3 := abs_sub_abs_le_abs_sub (itoWordIntegral B 0 r ω K) (itoWordIntegral B 0 0 ω K)
  unfold wordLip
  linarith

lemma ae_itoWordIntegral_time_eq_integral (K : Word (d + 1)) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → itoWordIntegral B 0 t ω ((0 : Fin (d + 1)) :: K) =
      ∫ r in (0 : ℝ)..t, itoWordIntegral B 0 r ω K := by
  have hcN : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ J : Word (d + 1),
      ContinuousOn (fun t => itoWordIntegral B 0 t ω J) (Icc 0 N) := by
    rw [ae_all_iff]; exact fun N => ae_continuousOn_itoWordIntegral B (Nat.cast_nonneg N)
  refine ae_forall_of_continuousOn
    (f := fun t ω => itoWordIntegral B 0 t ω ((0 : Fin (d + 1)) :: K))
    (g := fun t ω => ∫ r in (0 : ℝ)..t, itoWordIntegral B 0 r ω K) ?_ ?_ fun t ht => ?_
  · filter_upwards [hcN] with ω h N
    exact h N _
  · filter_upwards [hcN] with ω h N
    have hi : IntegrableOn (fun r => itoWordIntegral B 0 r ω K) (uIcc (0 : ℝ) N) := by
      rw [uIcc_of_le (Nat.cast_nonneg N)]; exact (h N K).integrableOn_Icc
    have := intervalIntegral.continuousOn_primitive_interval hi
    rwa [uIcc_of_le (Nat.cast_nonneg N)] at this
  · filter_upwards [ae_integral_itoWordIntegral_start B le_rfl K ht.le] with ω h
    exact h.symm

/-- Lipschitz constant of a non-space-headed word integral on `[0, T]`. -/
def nonSpaceLip (T : ℝ) : Word (d + 1) → Ω → ℝ
  | [] => fun _ => 0
  | _ :: K => wordLip B T K

lemma nonSpaceLip_nonneg (T : ℝ) (w : Word (d + 1)) (ω : Ω) : 0 ≤ nonSpaceLip B T w ω := by
  cases w with
  | nil => exact le_rfl
  | cons j K => exact wordLip_nonneg B T K ω

lemma integrable_nonSpaceLip (hT : 0 ≤ T) (w : Word (d + 1)) :
    Integrable (nonSpaceLip B T w) P := by
  cases w with
  | nil => exact integrable_zero _ _ _
  | cons j K => exact integrable_wordLip B hT K

/-- **Time-headed word integrals are Lipschitz on `[0, T]`** with an integrable constant. -/
theorem ae_lipschitz_itoWordIntegral_nonSpace (hT : 0 ≤ T) {w : Word (d + 1)}
    (hw : ¬ isSpaceHead w = true) :
    ∀ᵐ ω ∂P, ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T,
      |itoWordIntegral B 0 x ω w - itoWordIntegral B 0 y ω w| ≤ nonSpaceLip B T w ω * |x - y| := by
  rcases eq_of_not_isSpaceHead hw with rfl | ⟨K, rfl⟩
  · exact ae_of_all _ fun ω x _ y _ => by simp [itoWordIntegral_empty, nonSpaceLip]
  filter_upwards [ae_itoWordIntegral_time_eq_integral B K, ae_abs_le_wordLip B hT K,
    ae_continuousOn_itoWordIntegral B hT] with ω h1 h2 h3 x hx y hy
  have hii : ∀ z ∈ Icc 0 T, IntervalIntegrable (fun r => itoWordIntegral B 0 r ω K) volume 0 z :=
    fun z hz => ((h3 K).mono (uIcc_subset_Icc ⟨le_rfl, hT⟩ hz)).intervalIntegrable
  rw [h1 x hx.1, h1 y hy.1, intervalIntegral.integral_interval_sub_left (hii x hx) (hii y hy)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x)
    (f := fun r => itoWordIntegral B 0 r ω K) (C := wordLip B T K ω) fun z hz => by
      rw [Real.norm_eq_abs]
      exact h2 z (uIcc_subset_Icc hy hx (uIoc_subset_uIcc hz))
  rw [Real.norm_eq_abs] at this
  exact this

end Words

/-! ## Lemma 43 for the paper setup -/

section Coord

variable (B : MultiBrownian Ω P d) (I : Word (d + 1))

/-- Martingale part: the space-headed Itô terms of the contraction expansion. -/
def coordMart (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter
      (fun i : Fin (contractions I.reverse).length =>
        isSpaceHead (contractions I.reverse)[i].2 = true),
    (contractions I.reverse)[i].1 * (itoWordIntegral B 0 t ω (contractions I.reverse)[i].2 -
      itoWordIntegral B 0 0 ω (contractions I.reverse)[i].2)

/-- Finite-variation part: the time-headed Itô terms of the contraction expansion. -/
def coordFV (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter
      (fun i : Fin (contractions I.reverse).length =>
        ¬ isSpaceHead (contractions I.reverse)[i].2 = true),
    (contractions I.reverse)[i].1 * (itoWordIntegral B 0 t ω (contractions I.reverse)[i].2 -
      itoWordIntegral B 0 0 ω (contractions I.reverse)[i].2)

lemma paperSig2_coeff_eq_contractionSum (t : ℝ) (ω : Ω) :
    (paperSig2 B 0 t ω).coeff I = ∑ i : Fin (contractions I.reverse).length,
      (contractions I.reverse)[i].1 * itoWordIntegral B 0 t ω (contractions I.reverse)[i].2 := by
  rw [paperSig2_coeff, stratWordIntegral_eq_list, ← Fin.sum_univ_fun_getElem]
  rfl

omit [IsProbabilityMeasure P] in
lemma condExp_sum_eq {m : MeasurableSpace Ω} {ι : Type*} (s : Finset ι) (g h : ι → Ω → ℝ)
    (hg : ∀ i ∈ s, Integrable (g i) P) (hh : ∀ i ∈ s, P[g i | m] =ᵐ[P] h i) :
    P[fun ω => ∑ i ∈ s, g i ω | m] =ᵐ[P] fun ω => ∑ i ∈ s, h i ω := by
  have e1 : (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, g i := by ext ω; simp [Finset.sum_apply]
  rw [e1]
  filter_upwards [condExp_finsetSum hg m, (Filter.eventually_all_finset s).2 hh] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl h2

/-- **Paper Lemma 43.** Every signature coordinate of the paper setup is a special
semimartingale for the signature filtration. -/
def isSpecialSemimartingale_paperSig2_coeff {T : ℝ} (hT : 0 < T) :
    IsSpecialSemimartingale P (paperSetup B hT).signatureFiltration T
      (fun t ω => ((paperSetup B hT).W_hat t ω).coeff I) where
  M_part := coordMart B I
  A_part := coordFV B I
  decomp t _ ω := by
    have hX : ∀ t, ((paperSetup B hT).W_hat t ω).coeff I = (paperSig2 B 0 t ω).coeff I :=
      fun _ => rfl
    rw [hX, hX, paperSig2_coeff_eq_contractionSum, paperSig2_coeff_eq_contractionSum, add_assoc, coordMart, coordFV,
      Finset.sum_filter_add_sum_filter_not]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  M_zero ω := by simp [coordMart]
  A_zero ω := by simp [coordFV]
  M_martingale s t hs hst _ := by
    have hG : (paperSetup B hT).signatureFiltration.σAlg s = (pathFiltration B).σAlg s :=
      signature_filtration_eq_brownian_filtration _ s
    refine ⟨integrable_finsetSum _ fun i _ =>
      ((integrable_itoWordIntegral B (hs.trans hst) _).sub
        (integrable_itoWordIntegral B le_rfl _)).const_mul _, ?_⟩
    rw [hG]
    exact condExp_sum_eq _ _ _
      (fun i _ => ((integrable_itoWordIntegral B (hs.trans hst) _).sub
        (integrable_itoWordIntegral B le_rfl _)).const_mul _)
      (fun i hi => condExp_coordTerm B (Finset.mem_filter.1 hi).2 _ hs hst)
  M_l2_bdd := by
    have hM : MemLp (coordMart B I T) 2 P :=
      memLp_finsetSum _ fun i _ => ((memLp_two_itoWordIntegral B hT.le _).sub
        (memLp_two_itoWordIntegral B le_rfl _)).const_mul _
    exact hM.integrable_sq
  M_cont := by
    filter_upwards [ae_continuousOn_itoWordIntegral B hT.le] with ω h
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((h _).sub continuousOn_const)
  A_cont := by
    filter_upwards [ae_continuousOn_itoWordIntegral B hT.le] with ω h
    exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((h _).sub continuousOn_const)
  A_adapted t ht := by
    have hG : (paperSetup B hT).signatureFiltration.σAlg t = (pathFiltration B).σAlg t :=
      signature_filtration_eq_brownian_filtration _ t
    rw [hG]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      ((measurable_itoWordIntegral_pathFiltration B le_rfl ht.1 le_rfl _).sub
        (measurable_itoWordIntegral_pathFiltration B le_rfl le_rfl ht.1 _))
  A_integrable_var := by
    set L := contractions I.reverse
    set S := Finset.univ.filter (fun i : Fin L.length => ¬ isSpaceHead L[i].2 = true)
    set V' : Ω → ℝ := fun ω => ∑ i ∈ S, |L[i].1| * nonSpaceLip B T L[i].2 ω
    refine ⟨fun ω => V' ω * T, (integrable_finsetSum _ fun i _ =>
      (integrable_nonSpaceLip B hT.le _).const_mul _).mul_const T, ?_⟩
    filter_upwards [(Filter.eventually_all_finset S).2 fun i hi =>
      ae_lipschitz_itoWordIntegral_nonSpace B hT.le (Finset.mem_filter.1 hi).2] with ω hω
    have hV0 : 0 ≤ V' ω := Finset.sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (nonSpaceLip_nonneg B T _ ω)
    have hlip : LipschitzOnWith (V' ω).toNNReal (fun t => coordFV B I t ω) (Icc 0 T) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hV0]
      have he : coordFV B I x ω - coordFV B I y ω = ∑ i ∈ S, L[i].1 *
          (itoWordIntegral B 0 x ω L[i].2 - itoWordIntegral B 0 y ω L[i].2) := by
        simp only [coordFV, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [he]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [show V' ω * |x - y| = ∑ i ∈ S, |L[i].1| * nonSpaceLip B T L[i].2 ω * |x - y| from
        Finset.sum_mul _ _ _]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hω i hi x hx y hy) (abs_nonneg _)
    calc eVariationOn (fun t => coordFV B I t ω) (Icc 0 T)
        ≤ ((V' ω).toNNReal : ℝ≥0∞) * eVariationOn id (Icc 0 T) :=
          hlip.comp_eVariationOn_le (mapsTo_id _)
      _ = ENNReal.ofReal (V' ω * T) := by
          rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_mul hV0]; rfl

end Coord

end SignatureVolatility

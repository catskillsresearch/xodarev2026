module

public import SignatureVolatility.ItoCalculusKit.ItoIncrement
public import SignatureVolatility.ItoCalculusKit.EighthTransform


@[expose] public section

open MeasureTheory Filter Topology

namespace SignatureVolatility

/-!
# Eighth-moment time increments of the raw Itô limit

`HolderAdapted8 B H t K`: an adapted integrand in `L⁸` with `𝔼(H_v - H_u)⁸ ≤ K (v - u)⁴`. It is
in particular `HolderAdapted` with constant `√K` (`HolderAdapted8.toHolderAdapted`), and its raw
Itô limit satisfies `𝔼(I_v - I_u)⁸ ≤ 14⁴ c₈ M₈ (v - u)⁴`
(`integral_kitItoIntRaw_sub_pow_eight_le`), the eighth-order analogue of
`integral_kitItoIntRaw_sub_pow_four_le`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Adapted `L⁸` integrand with eighth-moment Hölder bound on `[0, t]`. -/
structure HolderAdapted8 (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t K : ℝ) : Prop where
  K_nonneg : 0 ≤ K
  meas : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u)
  memLp : ∀ u, 0 ≤ u → u ≤ t → MemLp (H u) 8 P
  holder : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t → ∫ ω, (H v ω - H u ω) ^ 8 ∂P ≤ K * (v - u) ^ 4

lemma HolderAdapted8.mono {B : MultiBrownian Ω P d} {H : ℝ → Ω → ℝ} {t K : ℝ}
    (hH : HolderAdapted8 B H t K) {s : ℝ} (hst : s ≤ t) : HolderAdapted8 B H s K :=
  ⟨hH.K_nonneg, fun u h0 hu => hH.meas u h0 (hu.trans hst),
    fun u h0 hu => hH.memLp u h0 (hu.trans hst),
    fun u v h0 huv hv => hH.holder u v h0 huv (hv.trans hst)⟩

/-- `(𝔼 f⁴)² ≤ 𝔼 f⁸`. -/
lemma sq_integral_pow_four_le_integral_pow_eight {f : Ω → ℝ} (hf : MemLp f 8 P) :
    (∫ ω, f ω ^ 4 ∂P) ^ 2 ≤ ∫ ω, f ω ^ 8 ∂P := by
  have hf2 : MemLp (fun ω => f ω ^ 2) 4 P :=
    memLp_four_of_integrable_pow_four (hf.aestronglyMeasurable.pow 2)
      ((integrable_pow_of_memLp_eight hf (k := 8) le_rfl).congr
        (ae_of_all _ fun ω => by simp only; ring))
  have h := sq_integral_sq_le_integral_pow_four hf2
  have e1 : (fun ω => (f ω ^ 2) ^ 2) = fun ω => f ω ^ 4 := by funext ω; ring
  have e2 : (fun ω => (f ω ^ 2) ^ 4) = fun ω => f ω ^ 8 := by funext ω; ring
  simp only [e1, e2] at h
  exact h

lemma HolderAdapted8.toHolderAdapted {B : MultiBrownian Ω P d} {H : ℝ → Ω → ℝ} {t K : ℝ}
    (hH : HolderAdapted8 B H t K) : HolderAdapted B H t (Real.sqrt K) := by
  refine ⟨Real.sqrt_nonneg _, hH.meas, fun u h0 hu => (hH.memLp u h0 hu).mono_exponent
    (by norm_num), fun u v h0 huv hv => ?_⟩
  have hD := (hH.memLp v (h0.trans huv) hv).sub (hH.memLp u h0 (huv.trans hv))
  have h1 := sq_integral_pow_four_le_integral_pow_eight hD
  have h2 := hH.holder u v h0 huv hv
  have h0' : 0 ≤ ∫ ω, (H v ω - H u ω) ^ 4 ∂P := integral_nonneg fun ω => by positivity
  have h3 : ∫ ω, (H v ω - H u ω) ^ 4 ∂P ≤ Real.sqrt (K * (v - u) ^ 4) :=
    Real.le_sqrt_of_sq_le (by simpa using h1.trans h2)
  rwa [Real.sqrt_mul hH.K_nonneg, show (v - u) ^ 4 = ((v - u) ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)] at h3

lemma add_pow_eight_le_conv (a b : ℝ) : (a + b) ^ 8 ≤ 128 * a ^ 8 + 128 * b ^ 8 := by
  have hx : 0 ≤ a ^ 2 := sq_nonneg a
  have hy : 0 ≤ b ^ 2 := sq_nonneg b
  have h1 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h2 : (a + b) ^ 8 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 4 := by
    rw [show (a + b) ^ 8 = ((a + b) ^ 2) ^ 4 by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) h1 4
  have h3 : (a ^ 2 + b ^ 2) ^ 4 ≤ 8 * (a ^ 2) ^ 4 + 8 * (b ^ 2) ^ 4 := by
    nlinarith [sq_nonneg ((a ^ 2 - b ^ 2) ^ 2), sq_nonneg ((a ^ 2) ^ 2 - (b ^ 2) ^ 2),
      sq_nonneg (a ^ 2 + b ^ 2), sq_nonneg (a ^ 2 - b ^ 2), mul_nonneg hx hy]
  calc (a + b) ^ 8 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 4 := h2
    _ = 16 * (a ^ 2 + b ^ 2) ^ 4 := by ring
    _ ≤ 16 * (8 * (a ^ 2) ^ 4 + 8 * (b ^ 2) ^ 4) := by linarith
    _ = 128 * a ^ 8 + 128 * b ^ 8 := by ring

/-- Uniform eighth moment of an `L⁸`-Hölder integrand on `[0, t]`. -/
lemma integral_pow_eight_le_of_holderAdapted8 (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ}
    {t K : ℝ} (hH : HolderAdapted8 B H t K) {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, H s ω ^ 8 ∂P ≤ 128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4 := by
  have ht : 0 ≤ t := hs.trans hst
  have h0 := hH.memLp 0 le_rfl ht
  have hsL := hH.memLp s hs hst
  have i0 : Integrable (fun ω => H 0 ω ^ 8) P := integrable_pow_of_memLp_eight h0 (k := 8) le_rfl
  have id : Integrable (fun ω => (H s ω - H 0 ω) ^ 8) P :=
    integrable_pow_of_memLp_eight (hsL.sub h0) (k := 8) le_rfl
  have is : Integrable (fun ω => H s ω ^ 8) P :=
    integrable_pow_of_memLp_eight hsL (k := 8) le_rfl
  have hhol := hH.holder 0 s le_rfl hs hst
  calc ∫ ω, H s ω ^ 8 ∂P ≤ ∫ ω, (128 * H 0 ω ^ 8 + 128 * (H s ω - H 0 ω) ^ 8) ∂P := by
        refine integral_mono is ((i0.const_mul 128).add (id.const_mul 128)) fun ω => ?_
        have := add_pow_eight_le_conv (H 0 ω) (H s ω - H 0 ω)
        simp only [add_sub_cancel] at this
        exact this
    _ = 128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * ∫ ω, (H s ω - H 0 ω) ^ 8 ∂P := by
        rw [integral_add (i0.const_mul 128) (id.const_mul 128), integral_const_mul,
          integral_const_mul]
    _ ≤ 128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * (K * (s - 0) ^ 4) := by gcongr
    _ ≤ 128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4 := by
        have hK := hH.K_nonneg
        have : (s - 0) ^ 4 ≤ t ^ 4 := by rw [sub_zero]; exact pow_le_pow_left₀ hs hst 4
        nlinarith

omit [IsProbabilityMeasure P] in
/-- **Fatou for eighth moments.** -/
lemma integral_pow_eight_le_of_tendsto {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g P) (hf : ∀ n, AEMeasurable (f n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hint : ∀ n, Integrable (fun ω => f n ω ^ 8) P) {b : ℕ → ℝ} {c : ℝ}
    (hb : ∀ n, ∫ ω, f n ω ^ 8 ∂P ≤ b n) (hbc : Tendsto b atTop (𝓝 c)) :
    Integrable (fun ω => g ω ^ 8) P ∧ ∫ ω, g ω ^ 8 ∂P ≤ c := by
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal (f n ω ^ 8)) atTop
      (𝓝 (ENNReal.ofReal (g ω ^ 8))) :=
    hlim.mono fun ω hω => ENNReal.tendsto_ofReal (hω.pow 8)
  have hL : ∫⁻ ω, ENNReal.ofReal (g ω ^ 8) ∂P ≤ ENNReal.ofReal c :=
    calc ∫⁻ ω, ENNReal.ofReal (g ω ^ 8) ∂P
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω ^ 8)) atTop ∂P :=
          lintegral_congr_ae (hlim'.mono fun ω hω => hω.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω ^ 8) ∂P) atTop :=
          lintegral_liminf_le' fun n => ENNReal.measurable_ofReal.comp_aemeasurable
            ((hf n).pow_const 8)
      _ = liminf (fun n => ENNReal.ofReal (∫ ω, f n ω ^ 8 ∂P)) atTop := by
          congr 1
          funext n
          exact (ofReal_integral_eq_lintegral_ofReal (hint n)
            (ae_of_all _ fun ω => by positivity)).symm
      _ ≤ liminf (fun n => ENNReal.ofReal (b n)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hb n))
      _ = ENNReal.ofReal c := (ENNReal.tendsto_ofReal hbc).liminf_eq
  have hc : 0 ≤ c := by
    refine ge_of_tendsto hbc (Eventually.of_forall fun n => ?_)
    exact (integral_nonneg fun ω => by positivity).trans (hb n)
  have hgi : Integrable (fun ω => g ω ^ 8) P := by
    refine ⟨hg.pow 8, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) (hL.trans_lt ENNReal.ofReal_lt_top)
    rw [Real.enorm_eq_ofReal (by positivity)]
  refine ⟨hgi, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hc, ofReal_integral_eq_lintegral_ofReal hgi
    (ae_of_all _ fun ω => by positivity)]
  exact hL

lemma memLp_unifRiemann_eight (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ}
    {t K : ℝ} (ht : 0 ≤ t) (hH : HolderAdapted8 B H t K) {N : ℕ} (hN : 0 < N) :
    MemLp (unifRiemann B k H t N) 8 P := by
  have h := memLp_finsetSum' (p := 8) (μ := P) (Finset.range N)
    (f := fun i ω => H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω)
    fun i hi => by
      obtain ⟨h0, h1⟩ := unifGrid_mem ht hN (Finset.mem_range.mp hi).le
      have hstep : (i : ℝ) * (t / (N : ℝ)) ≤ ((i + 1 : ℕ) : ℝ) * (t / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith)
          (div_nonneg ht (Nat.cast_nonneg _))
      exact memLp_mul_wnnIncr_eight B k h0 hstep (hH.meas _ h0 h1) (hH.memLp _ h0 h1)
  have hfun : (∑ i ∈ Finset.range N, fun ω => H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω) =
      unifRiemann B k H t N := by
    funext ω; simp [unifRiemann]
  rwa [hfun] at h

private lemma indicator_step_le' {u x y : ℝ} (hxy : x ≤ y) :
    (if u ≤ x then y - x else 0) ≤ max (y - u) 0 - max (x - u) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · have : max (x - u) 0 = 0 := max_eq_right (by linarith)
    rw [this, sub_zero]
    exact le_max_right _ _

section Horizon8

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

lemma measurable_horizonStep8 (hH : HolderAdapted8 B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (hsv : s < v) :
    Measurable[(pathFiltration B).σAlg s] (horizonStep H u v N s) ∧
      MemLp (horizonStep H u v N s) 8 P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hs.trans_lt hsv
  have hleft : ∀ a, 0 < a → s < a → a ≤ t →
      Measurable[(pathFiltration B).σAlg s] (H ((⌊s / (a / (N : ℝ))⌋₊ : ℝ) * (a / (N : ℝ)))) ∧
        MemLp (H ((⌊s / (a / (N : ℝ))⌋₊ : ℝ) * (a / (N : ℝ)))) 8 P := by
    intro a ha hsa hat
    obtain ⟨h0, h1, -⟩ := floor_mul_mem (div_pos ha hNr) hs
    exact ⟨(hH.meas _ h0 (h1.trans (hsa.le.trans hat))).mono ((pathFiltration B).mono h1) le_rfl,
      hH.memLp _ h0 (h1.trans (hsa.le.trans hat))⟩
  have hfun : horizonStep H u v N s = fun ω =>
      if s < u then H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω -
          H ((⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ))) ω
      else H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω :=
    funext fun ω => horizonStep_eq hu huv hN hs hsv ω
  rw [hfun]
  by_cases hsu : s < u
  · simp only [hsu, ↓reduceIte]
    have hA := hleft v hv hsv hvt
    have hB := hleft u (hs.trans_lt hsu) hsu (huv.trans hvt)
    exact ⟨hA.1.sub hB.1, hA.2.sub hB.2⟩
  · simp only [hsu, ↓reduceIte]
    exact hleft v hv hsv hvt

lemma root4_integral_horizonStep_le (hH : HolderAdapted8 B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (hsv : s < v) :
    root4 (∫ ω, horizonStep H u v N s ω ^ 8 ∂P) ≤
      root4 K * (v / (N : ℝ)) +
        (if u ≤ s then root4 (128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4) else 0) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hs.trans_lt hsv
  have hK := hH.K_nonneg
  have hroot_mono : ∀ {x y : ℝ}, x ≤ y → root4 x ≤ root4 y := fun h =>
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
  simp_rw [horizonStep_eq hu huv hN hs hsv]
  obtain ⟨hv0, hv1, hv2⟩ := floor_mul_mem (div_pos hv hNr) hs
  by_cases hsu : s < u
  · have hu0 : 0 < u := hs.trans_lt hsu
    obtain ⟨hu0', hu1, hu2⟩ := floor_mul_mem (div_pos hu0 hNr) hs
    simp only [hsu, ↓reduceIte, not_le.mpr hsu, add_zero]
    set a := (⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))
    set b := (⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ))
    have hΔ : u / (N : ℝ) ≤ v / (N : ℝ) := div_le_div_of_nonneg_right huv hNr.le
    have hab : (a - b) ^ 4 ≤ (v / (N : ℝ)) ^ 4 := by
      have h2 : (a - b) ^ 2 ≤ (v / (N : ℝ)) ^ 2 := sq_le_sq' (by linarith) (by linarith)
      rw [show (a - b) ^ 4 = ((a - b) ^ 2) ^ 2 by ring,
        show (v / (N : ℝ)) ^ 4 = ((v / (N : ℝ)) ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (sq_nonneg _) h2 2
    have hhol : ∫ ω, (H a ω - H b ω) ^ 8 ∂P ≤ K * (v / (N : ℝ)) ^ 4 := by
      rcases le_total b a with hba | hab'
      · exact (hH.holder b a hu0' hba (hv1.trans (hsv.le.trans hvt))).trans
          (mul_le_mul_of_nonneg_left hab hK)
      · have h := hH.holder a b hv0 hab' (hu1.trans (hsu.le.trans (huv.trans hvt)))
        have heq : ∫ ω, (H a ω - H b ω) ^ 8 ∂P = ∫ ω, (H b ω - H a ω) ^ 8 ∂P := by
          congr 1; funext ω; ring
        rw [heq]
        refine h.trans (mul_le_mul_of_nonneg_left ?_ hK)
        have : (b - a) ^ 4 = (a - b) ^ 4 := by ring
        rw [this]; exact hab
    calc root4 (∫ ω, (H a ω - H b ω) ^ 8 ∂P) ≤ root4 (K * (v / (N : ℝ)) ^ 4) :=
          hroot_mono hhol
      _ = root4 K * (v / (N : ℝ)) := by
          rw [root4_mul hK, root4_pow_four_self (by positivity)]
  · simp only [hsu, ↓reduceIte, not_lt.mp hsu]
    have h8 := integral_pow_eight_le_of_holderAdapted8 B hH hv0 (hv1.trans (hsv.le.trans hvt))
    calc root4 (∫ ω, H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω ^ 8 ∂P)
        ≤ root4 (128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4) := hroot_mono h8
      _ ≤ _ := le_add_of_nonneg_left (by have := root4_nonneg K; positivity)

/-- **Eighth moment of the difference of uniform sums over two horizons** `u < v ≤ t`. -/
theorem integral_unifRiemann_sub_horizon_le8 (hH : HolderAdapted8 B H t K) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    ∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω) ^ 8 ∂P ≤
      (14 * root4 gauss8Const * (root4 K * (v / (N : ℝ)) * v +
        root4 (128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4) * (v - u))) ^ 4 := by
  have hv : 0 < v := hu.trans_lt huv
  set M8 : ℝ := 128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4 with hM8
  set δ : ℕ → ℝ := fun M => v / ((M + 1 : ℕ) : ℝ) with hδdef
  have hδ : ∀ M, 0 < δ M := fun M => div_pos hv (by positivity)
  have hgrid : ∀ M i : ℕ, i < M + 1 → 0 ≤ (i : ℝ) * δ M ∧ (i : ℝ) * δ M < v := by
    intro M i hi
    refine ⟨by have := hδ M; positivity, ?_⟩
    have h1 : (i : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hi
    calc (i : ℝ) * δ M < ((M + 1 : ℕ) : ℝ) * δ M := mul_lt_mul_of_pos_right h1 (hδ M)
      _ = v := by simp only [hδdef]; field_simp
  set F : ℕ → Ω → ℝ := fun M ω => ∑ i ∈ Finset.range (M + 1),
    horizonStep H u v N ((i : ℝ) * δ M) ω *
      wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω with hFdef
  have hlim : ∀ ω, Tendsto (fun M => F M ω) atTop
      (𝓝 (unifRiemann B k H v N ω - unifRiemann B k H u N ω)) := by
    intro ω
    have h1 := tendsto_fineStepSum B k hv.le le_rfl N (fun j => H ((j : ℝ) * (v / (N : ℝ))) ω) ω
    have h2 := tendsto_fineStepSum B k hu huv.le N (fun j => H ((j : ℝ) * (u / (N : ℝ))) ω) ω
    refine (h1.sub h2).congr fun M => ?_
    simp only [hFdef, horizonStep, sub_mul, Finset.sum_sub_distrib, hδdef]
  have hmeasF : ∀ M i : ℕ, i < M + 1 →
      Measurable[(pathFiltration B).σAlg ((i : ℝ) * δ M)] (horizonStep H u v N ((i : ℝ) * δ M)) ∧
        MemLp (horizonStep H u v N ((i : ℝ) * δ M)) 8 P := fun M i hi =>
    measurable_horizonStep8 B hH hu huv.le hvt hN (hgrid M i hi).1 (hgrid M i hi).2
  have hτmono : ∀ M, Monotone fun i : ℕ => (i : ℝ) * δ M := fun M i j hij =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (hδ M).le
  have hFL : ∀ M, MemLp (F M) 8 P := by
    intro M
    have h := memLp_finsetSum' (p := 8) (μ := P) (Finset.range (M + 1))
      (f := fun i ω => horizonStep H u v N ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) fun i hi =>
      memLp_mul_wnnIncr_eight B k (hgrid M i (Finset.mem_range.mp hi)).1
        (hτmono M (Nat.le_succ i)) (hmeasF M i (Finset.mem_range.mp hi)).1
        (hmeasF M i (Finset.mem_range.mp hi)).2
    have hfun : (∑ i ∈ Finset.range (M + 1), fun ω => horizonStep H u v N ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) = F M := by
      funext ω; simp [hFdef]
    rwa [hfun] at h
  have hbound : ∀ M, ∫ ω, F M ω ^ 8 ∂P ≤
      (14 * root4 gauss8Const * (root4 K * (v / (N : ℝ)) * v + root4 M8 * (v - u))) ^ 4 := by
    intro M
    have hT := integral_transform_pow_eight_le B k (τ := fun i : ℕ => (i : ℝ) * δ M)
      (by simp) (hτmono M) (fun i => horizonStep H u v N ((i : ℝ) * δ M)) (M + 1)
      (fun j hj => (hmeasF M j hj).1) (fun j hj => (hmeasF M j hj).2)
    refine hT.trans ?_
    have hg8 := root4_nonneg gauss8Const
    refine pow_le_pow_left₀ (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (root4_nonneg _) (sub_nonneg.mpr (hτmono M (Nat.le_succ i))))) ?_ 4
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hterm : ∀ i ∈ Finset.range (M + 1),
        root4 (∫ ω, horizonStep H u v N ((i : ℝ) * δ M) ω ^ 8 ∂P) *
          (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) ≤
        root4 K * (v / (N : ℝ)) * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) +
          root4 M8 * (max (((i + 1 : ℕ) : ℝ) * δ M - u) 0 - max ((i : ℝ) * δ M - u) 0) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hstep : 0 ≤ ((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M :=
        sub_nonneg.mpr (hτmono M (Nat.le_succ i))
      have hs := root4_integral_horizonStep_le B hH hu huv.le hvt hN (hgrid M i hi').1
        (hgrid M i hi').2
      have hind := indicator_step_le' (u := u) (hτmono M (Nat.le_succ i))
      have hM80 := root4_nonneg M8
      calc _ ≤ (root4 K * (v / (N : ℝ)) +
            (if u ≤ (i : ℝ) * δ M then root4 M8 else 0)) *
            (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) := mul_le_mul_of_nonneg_right hs hstep
        _ = root4 K * (v / (N : ℝ)) * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) +
            root4 M8 * (if u ≤ (i : ℝ) * δ M then
              ((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M else 0) := by
            split_ifs <;> ring
        _ ≤ _ := by gcongr
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_range_sub (fun i : ℕ => (i : ℝ) * δ M),
      Finset.sum_range_sub (fun i : ℕ => max ((i : ℝ) * δ M - u) 0)]
    have hvM : ((M + 1 : ℕ) : ℝ) * δ M = v := by simp only [hδdef]; field_simp
    simp only [hvM, Nat.cast_zero, zero_mul, sub_zero, zero_sub]
    rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
  have hRm : AEStronglyMeasurable (fun ω => unifRiemann B k H v N ω -
      unifRiemann B k H u N ω) P :=
    ((memLp_unifRiemann_eight B k (hv.le) (hH.mono hvt) hN).sub
      (memLp_unifRiemann_eight B k hu (hH.mono (huv.le.trans hvt)) hN)).aestronglyMeasurable
  exact (integral_pow_eight_le_of_tendsto hRm (fun M => (hFL M).aestronglyMeasurable.aemeasurable)
    (ae_of_all _ hlim) (fun M => integrable_pow_of_memLp_eight (hFL M) (k := 8) le_rfl)
    hbound tendsto_const_nhds).2

/-- **`L⁸` time increments of the raw Itô limit**: for an adapted `L⁸`-Hölder integrand on
`[0, t]` and `0 ≤ u ≤ v ≤ t`, `E (I_v - I_u)⁸ ≤ 14⁴ · c₈ · M₈ · (v - u)⁴` with
`M₈ = 128 E H₀⁸ + 128 K t⁴`. -/
theorem integral_kitItoIntRaw_sub_pow_eight_le (hd : 0 < d) (hH : HolderAdapted8 B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    Integrable (fun ω => (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ^ 8) P ∧
      ∫ ω, (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ^ 8 ∂P ≤
        14 ^ 4 * gauss8Const * (128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4) * (v - u) ^ 4 := by
  set M8 : ℝ := 128 * ∫ ω, H 0 ω ^ 8 ∂P + 128 * K * t ^ 4 with hM8
  have hM80 : 0 ≤ M8 := by
    have := hH.K_nonneg
    have : 0 ≤ ∫ ω, H 0 ω ^ 8 ∂P := integral_nonneg fun ω => by positivity
    positivity
  rcases huv.eq_or_lt with rfl | hlt
  · simp
  have hv : 0 < v := hu.trans_lt hlt
  have hH4 := hH.toHolderAdapted
  have hIv := kitItoIntRaw_of_holderAdapted B hd hv.le (hH4.mono hvt)
  have hIu := kitItoIntRaw_of_holderAdapted B hd hu (hH4.mono (huv.trans hvt))
  have hg : AEStronglyMeasurable (fun ω => kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) P :=
    (hIv.2.1.sub hIu.2.1).aestronglyMeasurable
  set k := kitDriver hd
  have hfL : ∀ n : ℕ, MemLp (fun ω => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω) 8 P := fun n =>
    (memLp_unifRiemann_eight B k hv.le (hH.mono hvt) n.succ_pos).sub
      (memLp_unifRiemann_eight B k hu (hH.mono (huv.trans hvt)) n.succ_pos)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω) atTop
      (𝓝 (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω)) := by
    filter_upwards [hIv.1, hIu.1] with ω h1 h2
    exact h1.sub h2
  have hc8 := gauss8Const_nonneg
  have hbc : Tendsto (fun n : ℕ => (14 * root4 gauss8Const * (root4 K *
      (v / ((n + 1 : ℕ) : ℝ)) * v + root4 M8 * (v - u))) ^ 4) atTop
      (𝓝 (14 ^ 4 * gauss8Const * M8 * (v - u) ^ 4)) := by
    have h0 : Tendsto (fun n : ℕ => v / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
      exact h.congr fun n => by simp
    have h1 := ((tendsto_const_nhds (x := root4 K)).mul h0).mul_const v
    have h2 := (((h1.add_const (root4 M8 * (v - u))).const_mul
      (14 * root4 gauss8Const)).pow 4)
    convert h2 using 2
    rw [mul_zero, zero_mul, zero_add, mul_pow, mul_pow, mul_pow, root4_pow_four hc8,
      root4_pow_four hM80]
    ring
  exact integral_pow_eight_le_of_tendsto hg (fun n => (hfL n).aestronglyMeasurable.aemeasurable)
    hlim (fun n => integrable_pow_of_memLp_eight (hfL n) (k := 8) le_rfl)
    (fun n => integral_unifRiemann_sub_horizon_le8 B k hH hu hlt hvt n.succ_pos) hbc

end Horizon8

end SignatureVolatility

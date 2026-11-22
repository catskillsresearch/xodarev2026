module

public import SignatureVolatility.ItoCalculusKit.RiemannConvergence


@[expose] public section

open MeasureTheory Filter Topology

namespace SignatureVolatility

/-!
# Time increments of the raw Itô limit

A uniform-grid Itô–Riemann sum on `[0, a]` is, pathwise, the limit of Riemann sums of the
corresponding step integrand along fine uniform grids of a larger interval `[0, v]`
(`tendsto_fineStepSum`). This puts sums over *different* horizons on a common grid, so the
fourth-moment martingale-transform bound applies to their difference.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The step integrand of a uniform grid on `[0, a]` with `N` cells and cell values `h j`. -/
noncomputable def stepFun (a : ℝ) (N : ℕ) (h : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    if (j : ℝ) * (a / (N : ℝ)) ≤ s ∧ s < ((j + 1 : ℕ) : ℝ) * (a / (N : ℝ)) then h j else 0

private lemma sum_range_ite_wnnIncr (B : MultiBrownian Ω P d) (k : Fin d) {δ c c' : ℝ}
    (hδ : 0 < δ) (hcc' : c ≤ c') {M : ℕ} (hc'M : c' ≤ (M : ℝ) * δ) (ω : Ω) :
    ∑ i ∈ Finset.range M, (if c ≤ (i : ℝ) * δ ∧ (i : ℝ) * δ < c' then
        wnnIncr B k ((i : ℝ) * δ) (((i + 1 : ℕ) : ℝ) * δ) ω else 0) =
      B.Wnn (Real.toNNReal ((⌈c' / δ⌉₊ : ℕ) * δ)) ω k -
        B.Wnn (Real.toNNReal ((⌈c / δ⌉₊ : ℕ) * δ)) ω k := by
  set F : ℕ → ℝ := fun n => B.Wnn (Real.toNNReal ((n : ℝ) * δ)) ω k with hF
  have hA : ⌈c / δ⌉₊ ≤ ⌈c' / δ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hcc' hδ.le)
  have hB : ⌈c' / δ⌉₊ ≤ M := Nat.ceil_le.mpr (by rw [div_le_iff₀ hδ]; exact hc'M)
  have hcond : ∀ i : ℕ, (c ≤ (i : ℝ) * δ ∧ (i : ℝ) * δ < c') ↔
      i ∈ Finset.Ico ⌈c / δ⌉₊ ⌈c' / δ⌉₊ := by
    intro i
    rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hδ, lt_div_iff₀ hδ]
  have hfilt : (Finset.range M).filter (fun i : ℕ => c ≤ (i : ℝ) * δ ∧ (i : ℝ) * δ < c') =
      Finset.Ico ⌈c / δ⌉₊ ⌈c' / δ⌉₊ := by
    ext i
    rw [Finset.mem_filter, hcond, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_of_lt_of_le (Finset.mem_Ico.mp h).2 hB, h⟩
  rw [← Finset.sum_filter, hfilt]
  have hterm : ∀ i ∈ Finset.Ico ⌈c / δ⌉₊ ⌈c' / δ⌉₊,
      wnnIncr B k ((i : ℝ) * δ) (((i + 1 : ℕ) : ℝ) * δ) ω = F (i + 1) - F i := by
    intro i _
    simp only [wnnIncr, hF]
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sub _ hA, Finset.sum_range_sub,
    Finset.sum_range_sub]
  ring

private lemma tendsto_ceil_mul (c : ℝ) (hc : 0 ≤ c) {δ : ℕ → ℝ} (hδ : ∀ M, 0 < δ M)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun M => ((⌈c / δ M⌉₊ : ℕ) : ℝ) * δ M) atTop (𝓝 c) := by
  have hlow : ∀ M, c ≤ ((⌈c / δ M⌉₊ : ℕ) : ℝ) * δ M := fun M => by
    rw [← div_le_iff₀ (hδ M)]; exact Nat.le_ceil _
  have hupp : ∀ M, ((⌈c / δ M⌉₊ : ℕ) : ℝ) * δ M ≤ c + δ M := fun M => by
    have h := Nat.ceil_lt_add_one (div_nonneg hc (hδ M).le)
    have := mul_le_mul_of_nonneg_right h.le (hδ M).le
    rwa [add_mul, div_mul_cancel₀ _ (hδ M).ne', one_mul] at this
  have hlim : Tendsto (fun M => c + δ M) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add hδ0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlow hupp

/-- **Fine-grid representation of a coarse Itô–Riemann sum** (pathwise, every `ω`). -/
theorem tendsto_fineStepSum (B : MultiBrownian Ω P d) (k : Fin d) {a v : ℝ} (ha : 0 ≤ a)
    (hav : a ≤ v) (N : ℕ) (h : ℕ → ℝ) (ω : Ω) :
    Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
        stepFun a N h ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) *
          wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
            (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω) atTop
      (𝓝 (∑ j ∈ Finset.range N,
        h j * wnnIncr B k ((j : ℝ) * (a / (N : ℝ))) (((j + 1 : ℕ) : ℝ) * (a / (N : ℝ))) ω)) := by
  rcases (ha.trans hav).eq_or_lt with hv0 | hvpos
  · -- `v = 0`, hence `a = 0`: every increment vanishes
    have ha0 : a = 0 := le_antisymm (hv0 ▸ hav) ha
    subst ha0
    simp only [← hv0, zero_div, mul_zero, wnnIncr, sub_self, mul_zero, Finset.sum_const_zero]
    exact tendsto_const_nhds
  set δ : ℕ → ℝ := fun M => v / ((M + 1 : ℕ) : ℝ) with hδdef
  have hδ : ∀ M, 0 < δ M := fun M => div_pos hvpos (by positivity)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun M => ?_
    simp [hδdef]
  have hW : Continuous fun x : ℝ => B.Wnn (Real.toNNReal x) ω k :=
    (B.pathContinuous k ω).comp continuous_real_toNNReal
  have hrepr : ∀ M : ℕ, ∑ i ∈ Finset.range (M + 1),
      stepFun a N h ((i : ℝ) * δ M) * wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω =
      ∑ j ∈ Finset.range N, h j *
        (B.Wnn (Real.toNNReal ((⌈((j + 1 : ℕ) : ℝ) * (a / (N : ℝ)) / δ M⌉₊ : ℕ) * δ M)) ω k -
          B.Wnn (Real.toNNReal ((⌈(j : ℝ) * (a / (N : ℝ)) / δ M⌉₊ : ℕ) * δ M)) ω k) := by
    intro M
    unfold stepFun
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.mp hj)
    have hΔ : 0 ≤ a / (N : ℝ) := div_nonneg ha (Nat.cast_nonneg _)
    have hcc' : (j : ℝ) * (a / (N : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) * (a / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hΔ
    have hc'v : ((j + 1 : ℕ) : ℝ) * (a / (N : ℝ)) ≤ ((M + 1 : ℕ) : ℝ) * δ M := by
      have h1 : ((j + 1 : ℕ) : ℝ) * (a / (N : ℝ)) ≤ a :=
        (unifGrid_mem ha hN (Finset.mem_range.mp hj)).2
      have h2 : ((M + 1 : ℕ) : ℝ) * δ M = v := by
        simp only [hδdef]; field_simp
      linarith
    rw [← sum_range_ite_wnnIncr B k (hδ M) hcc' hc'v ω, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hlim : ∀ j ∈ Finset.range N, Tendsto (fun M => h j *
        (B.Wnn (Real.toNNReal ((⌈((j + 1 : ℕ) : ℝ) * (a / (N : ℝ)) / δ M⌉₊ : ℕ) * δ M)) ω k -
          B.Wnn (Real.toNNReal ((⌈(j : ℝ) * (a / (N : ℝ)) / δ M⌉₊ : ℕ) * δ M)) ω k)) atTop
      (𝓝 (h j * wnnIncr B k ((j : ℝ) * (a / (N : ℝ))) (((j + 1 : ℕ) : ℝ) * (a / (N : ℝ))) ω)) := by
    intro j _
    have hΔ : 0 ≤ a / (N : ℝ) := div_nonneg ha (Nat.cast_nonneg _)
    have h1 := tendsto_ceil_mul (((j + 1 : ℕ) : ℝ) * (a / (N : ℝ))) (by positivity) hδ hδ0
    have h0 := tendsto_ceil_mul ((j : ℝ) * (a / (N : ℝ))) (by positivity) hδ hδ0
    exact tendsto_const_nhds.mul (((hW.tendsto _).comp h1).sub ((hW.tendsto _).comp h0))
  exact (tendsto_finsetSum _ hlim).congr fun M => (hrepr M).symm

/-- Closed form of the step integrand: the value of the cell containing `s`. -/
lemma stepFun_eq {a : ℝ} (ha' : 0 ≤ a) {N : ℕ} (hN : 0 < N) (h : ℕ → ℝ) (s : ℝ) :
    stepFun a N h s = if 0 ≤ s ∧ s < a then h ⌊s / (a / (N : ℝ))⌋₊ else 0 := by
  rcases ha'.eq_or_lt with ha0 | ha
  · subst ha0
    unfold stepFun
    simp only [zero_div, mul_zero]
    by_cases hs : 0 ≤ s
    · have : ¬ s < 0 := not_lt.mpr hs
      simp [this]
    · simp [hs]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set Δ : ℝ := a / (N : ℝ) with hΔ
  have hΔ0 : 0 < Δ := div_pos ha hNr
  have hNΔ : (N : ℝ) * Δ = a := by rw [hΔ]; field_simp
  unfold stepFun
  rw [← hΔ]
  split_ifs with hs
  · set j₀ := ⌊s / Δ⌋₊ with hj₀
    have hx : 0 ≤ s / Δ := div_nonneg hs.1 hΔ0.le
    have hj₀N : j₀ < N := by
      rw [hj₀, Nat.floor_lt hx, div_lt_iff₀ hΔ0, hNΔ]
      exact hs.2
    have hcell : ∀ j : ℕ, ((j : ℝ) * Δ ≤ s ∧ s < ((j + 1 : ℕ) : ℝ) * Δ) ↔ j = j₀ := by
      intro j
      rw [hj₀, eq_comm, Nat.floor_eq_iff hx, le_div_iff₀ hΔ0, div_lt_iff₀ hΔ0]
      push_cast
      rfl
    rw [Finset.sum_eq_single j₀]
    · rw [ite_eq_left_iff]
      intro h
      exact absurd ((hcell j₀).mpr rfl) h
    · intro j _ hj
      rw [ite_eq_right_iff]
      intro h
      exact absurd ((hcell j).mp h) hj
    · intro hj
      exact absurd (Finset.mem_range.mpr hj₀N) hj
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [ite_eq_right_iff]
    rintro ⟨h1, h2⟩
    exfalso
    apply hs
    have hj : j < N := Finset.mem_range.mp hj
    refine ⟨le_trans (by positivity) h1, lt_of_lt_of_le h2 ?_⟩
    rw [← hNΔ]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hΔ0.le

/-- The left grid point `⌊s / Δ⌋ Δ` lies in `(s - Δ, s]`. -/
lemma floor_mul_mem {Δ s : ℝ} (hΔ : 0 < Δ) (hs : 0 ≤ s) :
    0 ≤ (⌊s / Δ⌋₊ : ℝ) * Δ ∧ (⌊s / Δ⌋₊ : ℝ) * Δ ≤ s ∧ s - Δ < (⌊s / Δ⌋₊ : ℝ) * Δ := by
  have hx : 0 ≤ s / Δ := div_nonneg hs hΔ.le
  refine ⟨by positivity, ?_, ?_⟩
  · have := Nat.floor_le hx
    rwa [le_div_iff₀ hΔ] at this
  · have := Nat.lt_floor_add_one (s / Δ)
    rw [div_lt_iff₀ hΔ, add_mul, one_mul] at this
    linarith

omit [IsProbabilityMeasure P] in
/-- **Fatou for fourth moments.** -/
lemma lintegral_pow_four_le_of_tendsto {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEMeasurable (f n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hint : ∀ n, Integrable (fun ω => f n ω ^ 4) P) {b : ℕ → ℝ} {c : ℝ}
    (hb : ∀ n, ∫ ω, f n ω ^ 4 ∂P ≤ b n) (hbc : Tendsto b atTop (𝓝 c)) :
    ∫⁻ ω, ENNReal.ofReal (g ω ^ 4) ∂P ≤ ENNReal.ofReal c := by
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal (f n ω ^ 4)) atTop
      (𝓝 (ENNReal.ofReal (g ω ^ 4))) :=
    hlim.mono fun ω hω => ENNReal.tendsto_ofReal (hω.pow 4)
  calc ∫⁻ ω, ENNReal.ofReal (g ω ^ 4) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω ^ 4)) atTop ∂P :=
        lintegral_congr_ae (hlim'.mono fun ω hω => hω.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω ^ 4) ∂P) atTop :=
        lintegral_liminf_le' fun n => ENNReal.measurable_ofReal.comp_aemeasurable
          ((hf n).pow_const 4)
    _ = liminf (fun n => ENNReal.ofReal (∫ ω, f n ω ^ 4 ∂P)) atTop := by
        congr 1
        funext n
        exact (ofReal_integral_eq_lintegral_ofReal (hint n)
          (ae_of_all _ fun ω => by positivity)).symm
    _ ≤ liminf (fun n => ENNReal.ofReal (b n)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hb n))
    _ = ENNReal.ofReal c := (ENNReal.tendsto_ofReal hbc).liminf_eq

omit [IsProbabilityMeasure P] in
/-- Integral form of `lintegral_pow_four_le_of_tendsto`. -/
lemma integral_pow_four_le_of_tendsto {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g P) (hf : ∀ n, AEMeasurable (f n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hint : ∀ n, Integrable (fun ω => f n ω ^ 4) P) {b : ℕ → ℝ} {c : ℝ}
    (hb : ∀ n, ∫ ω, f n ω ^ 4 ∂P ≤ b n) (hbc : Tendsto b atTop (𝓝 c)) :
    Integrable (fun ω => g ω ^ 4) P ∧ ∫ ω, g ω ^ 4 ∂P ≤ c := by
  have hL := lintegral_pow_four_le_of_tendsto hf hlim hint hb hbc
  have hc : 0 ≤ c := by
    refine ge_of_tendsto hbc (Eventually.of_forall fun n => ?_)
    exact (integral_nonneg fun ω => by positivity).trans (hb n)
  have hgi : Integrable (fun ω => g ω ^ 4) P := by
    refine ⟨hg.pow 4, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) (hL.trans_lt ENNReal.ofReal_lt_top)
    rw [Real.enorm_eq_ofReal (by positivity)]
  refine ⟨hgi, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hc, ofReal_integral_eq_lintegral_ofReal hgi
    (ae_of_all _ fun ω => by positivity)]
  exact hL

private lemma add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg ((a - b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b),
    sq_nonneg (a - b)]

/-- Uniform fourth moment of an `L⁴`-Hölder integrand on `[0, t]`. -/
lemma integral_pow_four_le_of_holderAdapted (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ}
    {t K : ℝ} (hH : HolderAdapted B H t K) {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, H s ω ^ 4 ∂P ≤ 8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2 := by
  have ht : 0 ≤ t := hs.trans hst
  have h0 := hH.memLp 0 le_rfl ht
  have hsL := hH.memLp s hs hst
  have i0 : Integrable (fun ω => H 0 ω ^ 4) P := integrable_pow_of_memLp_four h0 (k := 4) le_rfl
  have id : Integrable (fun ω => (H s ω - H 0 ω) ^ 4) P :=
    integrable_pow_of_memLp_four (hsL.sub h0) (k := 4) le_rfl
  have is : Integrable (fun ω => H s ω ^ 4) P := integrable_pow_of_memLp_four hsL (k := 4) le_rfl
  have hhol := hH.holder 0 s le_rfl hs hst
  calc ∫ ω, H s ω ^ 4 ∂P ≤ ∫ ω, (8 * H 0 ω ^ 4 + 8 * (H s ω - H 0 ω) ^ 4) ∂P := by
        refine integral_mono is ((i0.const_mul 8).add (id.const_mul 8)) fun ω => ?_
        have := add_pow_four_le (H 0 ω) (H s ω - H 0 ω)
        simp only [add_sub_cancel] at this
        exact this
    _ = 8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * ∫ ω, (H s ω - H 0 ω) ^ 4 ∂P := by
        rw [integral_add (i0.const_mul 8) (id.const_mul 8), integral_const_mul,
          integral_const_mul]
    _ ≤ 8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * (K * (s - 0) ^ 2) := by gcongr
    _ ≤ 8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2 := by
        have hK := hH.K_nonneg
        have : (s - 0) ^ 2 ≤ t ^ 2 := by rw [sub_zero]; exact pow_le_pow_left₀ hs hst 2
        nlinarith

lemma HolderAdapted.mono {B : MultiBrownian Ω P d} {H : ℝ → Ω → ℝ} {t K : ℝ}
    (hH : HolderAdapted B H t K) {s : ℝ} (hst : s ≤ t) : HolderAdapted B H s K :=
  ⟨hH.K_nonneg, fun u h0 hu => hH.meas u h0 (hu.trans hst),
    fun u h0 hu => hH.memLp u h0 (hu.trans hst),
    fun u v h0 huv hv => hH.holder u v h0 huv (hv.trans hst)⟩

/-- Telescoping majorant for the indicator `1_{u ≤ τ}` times a grid step. -/
private lemma indicator_step_le {u x y : ℝ} (hxy : x ≤ y) :
    (if u ≤ x then y - x else 0) ≤ max (y - u) 0 - max (x - u) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · have : max (x - u) 0 = 0 := max_eq_right (by linarith)
    rw [this, sub_zero]
    exact le_max_right _ _

section Horizon

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- The difference of the step integrands of the uniform grids on `[0, v]` and `[0, u]`
(`N` cells each). -/
noncomputable def horizonStep (H : ℝ → Ω → ℝ) (u v : ℝ) (N : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  stepFun v N (fun j => H ((j : ℝ) * (v / (N : ℝ))) ω) s -
    stepFun u N (fun j => H ((j : ℝ) * (u / (N : ℝ))) ω) s

omit [MeasurableSpace Ω] in
lemma horizonStep_eq {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 ≤ s) (hsv : s < v) (ω : Ω) :
    horizonStep H u v N s ω =
      if s < u then H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω -
          H ((⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ))) ω
      else H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω := by
  unfold horizonStep
  rw [stepFun_eq (hu.trans huv) hN, stepFun_eq hu hN]
  by_cases hsu : s < u
  · simp [hs, hsv, hsu]
  · simp [hs, hsv, hsu]

lemma measurable_horizonStep (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (hsv : s < v) :
    Measurable[(pathFiltration B).σAlg s] (horizonStep H u v N s) ∧
      MemLp (horizonStep H u v N s) 4 P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hs.trans_lt hsv
  have hleft : ∀ a, 0 < a → s < a → a ≤ t →
      Measurable[(pathFiltration B).σAlg s] (H ((⌊s / (a / (N : ℝ))⌋₊ : ℝ) * (a / (N : ℝ)))) ∧
        MemLp (H ((⌊s / (a / (N : ℝ))⌋₊ : ℝ) * (a / (N : ℝ)))) 4 P := by
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

lemma sqrt_integral_horizonStep_le (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (hsv : s < v) :
    Real.sqrt (∫ ω, horizonStep H u v N s ω ^ 4 ∂P) ≤
      Real.sqrt K * (v / (N : ℝ)) +
        (if u ≤ s then Real.sqrt (8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2) else 0) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hs.trans_lt hsv
  have hK := hH.K_nonneg
  simp_rw [horizonStep_eq hu huv hN hs hsv]
  obtain ⟨hv0, hv1, hv2⟩ := floor_mul_mem (div_pos hv hNr) hs
  by_cases hsu : s < u
  · have hu0 : 0 < u := hs.trans_lt hsu
    obtain ⟨hu0', hu1, hu2⟩ := floor_mul_mem (div_pos hu0 hNr) hs
    simp only [hsu, ↓reduceIte, not_le.mpr hsu, add_zero]
    set a := (⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))
    set b := (⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ))
    have hΔ : u / (N : ℝ) ≤ v / (N : ℝ) := div_le_div_of_nonneg_right huv hNr.le
    have hab : (a - b) ^ 2 ≤ (v / (N : ℝ)) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hhol : ∫ ω, (H a ω - H b ω) ^ 4 ∂P ≤ K * (v / (N : ℝ)) ^ 2 := by
      rcases le_total b a with hba | hab'
      · exact (hH.holder b a hu0' hba (hv1.trans (hsv.le.trans hvt))).trans
          (mul_le_mul_of_nonneg_left hab hK)
      · have h := hH.holder a b hv0 hab' (hu1.trans (hsu.le.trans (huv.trans hvt)))
        have heq : ∫ ω, (H a ω - H b ω) ^ 4 ∂P = ∫ ω, (H b ω - H a ω) ^ 4 ∂P := by
          congr 1; funext ω; ring
        rw [heq]
        refine h.trans (mul_le_mul_of_nonneg_left ?_ hK)
        have : (b - a) ^ 2 = (a - b) ^ 2 := by ring
        rw [this]; exact hab
    calc Real.sqrt (∫ ω, (H a ω - H b ω) ^ 4 ∂P) ≤ Real.sqrt (K * (v / (N : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hhol
      _ = Real.sqrt K * (v / (N : ℝ)) := by
          rw [Real.sqrt_mul hK, Real.sqrt_sq (by positivity)]
  · simp only [hsu, ↓reduceIte, not_lt.mp hsu]
    have h4 := integral_pow_four_le_of_holderAdapted B hH hv0 (hv1.trans (hsv.le.trans hvt))
    calc Real.sqrt (∫ ω, H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω ^ 4 ∂P)
        ≤ Real.sqrt (8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2) := Real.sqrt_le_sqrt h4
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- **Fourth moment of the difference of uniform sums over two horizons** `u < v ≤ t`. -/
theorem integral_unifRiemann_sub_horizon_le (hH : HolderAdapted B H t K) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    ∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω) ^ 4 ∂P ≤
      16 * gaussFourthConst * (Real.sqrt K * (v / (N : ℝ)) * v +
        Real.sqrt (8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2) * (v - u)) ^ 2 := by
  have hv : 0 < v := hu.trans_lt huv
  set M4 : ℝ := 8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2 with hM4
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
        MemLp (horizonStep H u v N ((i : ℝ) * δ M)) 4 P := fun M i hi =>
    measurable_horizonStep B hH hu huv.le hvt hN (hgrid M i hi).1 (hgrid M i hi).2
  have hτmono : ∀ M, Monotone fun i : ℕ => (i : ℝ) * δ M := fun M i j hij =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (hδ M).le
  have hFL : ∀ M, MemLp (F M) 4 P := by
    intro M
    have h := memLp_finsetSum' (p := 4) (μ := P) (Finset.range (M + 1))
      (f := fun i ω => horizonStep H u v N ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) fun i hi =>
      memLp_mul_wnnIncr B k (hgrid M i (Finset.mem_range.mp hi)).1
        (hτmono M (Nat.le_succ i)) (hmeasF M i (Finset.mem_range.mp hi)).1
        (hmeasF M i (Finset.mem_range.mp hi)).2
    have hfun : (∑ i ∈ Finset.range (M + 1), fun ω => horizonStep H u v N ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) = F M := by
      funext ω; simp [hFdef]
    rwa [hfun] at h
  have hbound : ∀ M, ∫ ω, F M ω ^ 4 ∂P ≤
      16 * gaussFourthConst * (Real.sqrt K * (v / (N : ℝ)) * v + Real.sqrt M4 * (v - u)) ^ 2 := by
    intro M
    have hT := integral_transform_pow_four_le B k (τ := fun i : ℕ => (i : ℝ) * δ M)
      (by simp) (hτmono M) (fun i => horizonStep H u v N ((i : ℝ) * δ M)) (M + 1)
      (fun j hj => (hmeasF M j hj).1) (fun j hj => (hmeasF M j hj).2)
    refine hT.trans ?_
    have hg4 := gaussFourthConst_nonneg
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (hτmono M (Nat.le_succ i)))) ?_ 2
    have hterm : ∀ i ∈ Finset.range (M + 1),
        Real.sqrt (∫ ω, horizonStep H u v N ((i : ℝ) * δ M) ω ^ 4 ∂P) *
          (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) ≤
        Real.sqrt K * (v / (N : ℝ)) * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) +
          Real.sqrt M4 * (max (((i + 1 : ℕ) : ℝ) * δ M - u) 0 - max ((i : ℝ) * δ M - u) 0) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hstep : 0 ≤ ((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M :=
        sub_nonneg.mpr (hτmono M (Nat.le_succ i))
      have hs := sqrt_integral_horizonStep_le B hH hu huv.le hvt hN (hgrid M i hi').1
        (hgrid M i hi').2
      have hind := indicator_step_le (u := u) (hτmono M (Nat.le_succ i))
      calc _ ≤ (Real.sqrt K * (v / (N : ℝ)) +
            (if u ≤ (i : ℝ) * δ M then Real.sqrt M4 else 0)) *
            (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) := mul_le_mul_of_nonneg_right hs hstep
        _ = Real.sqrt K * (v / (N : ℝ)) * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) +
            Real.sqrt M4 * (if u ≤ (i : ℝ) * δ M then
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
    ((memLp_unifRiemann B k (hv.le) (hH.mono hvt) hN).sub
      (memLp_unifRiemann B k hu (hH.mono (huv.le.trans hvt)) hN)).aestronglyMeasurable
  exact (integral_pow_four_le_of_tendsto hRm (fun M => (hFL M).aestronglyMeasurable.aemeasurable)
    (ae_of_all _ hlim) (fun M => integrable_pow_of_memLp_four (hFL M) (k := 4) le_rfl)
    hbound tendsto_const_nhds).2

/-- **`L⁴` time increments of the raw Itô limit**: for an adapted `L⁴`-Hölder integrand on
`[0, t]` and `0 ≤ u ≤ v ≤ t`,
`E (I_v - I_u)⁴ ≤ 16 · 𝔼[G⁴] · M₄ · (v - u)²` with `M₄ = 8 E H₀⁴ + 8 K t²`. -/
theorem integral_kitItoIntRaw_sub_pow_four_le (hd : 0 < d) (hH : HolderAdapted B H t K)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    Integrable (fun ω => (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ^ 4) P ∧
      ∫ ω, (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) ^ 4 ∂P ≤
        16 * gaussFourthConst * (8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2) * (v - u) ^ 2 := by
  set M4 : ℝ := 8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2 with hM4
  have hM40 : 0 ≤ M4 := by
    have := hH.K_nonneg
    have : 0 ≤ ∫ ω, H 0 ω ^ 4 ∂P := integral_nonneg fun ω => by positivity
    positivity
  rcases huv.eq_or_lt with rfl | hlt
  · simp
  have hv : 0 < v := hu.trans_lt hlt
  have hIv := kitItoIntRaw_of_holderAdapted B hd hv.le (hH.mono hvt)
  have hIu := kitItoIntRaw_of_holderAdapted B hd hu (hH.mono (huv.trans hvt))
  have hg : AEStronglyMeasurable (fun ω => kitItoIntRaw B H v ω - kitItoIntRaw B H u ω) P :=
    (hIv.2.1.sub hIu.2.1).aestronglyMeasurable
  set k := kitDriver hd
  have hfL : ∀ n : ℕ, MemLp (fun ω => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω) 4 P := fun n =>
    (memLp_unifRiemann B k hv.le (hH.mono hvt) n.succ_pos).sub
      (memLp_unifRiemann B k hu (hH.mono (huv.trans hvt)) n.succ_pos)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω) atTop
      (𝓝 (kitItoIntRaw B H v ω - kitItoIntRaw B H u ω)) := by
    filter_upwards [hIv.1, hIu.1] with ω h1 h2
    exact h1.sub h2
  have hbc : Tendsto (fun n : ℕ => 16 * gaussFourthConst * (Real.sqrt K *
      (v / ((n + 1 : ℕ) : ℝ)) * v + Real.sqrt M4 * (v - u)) ^ 2) atTop
      (𝓝 (16 * gaussFourthConst * M4 * (v - u) ^ 2)) := by
    have h0 : Tendsto (fun n : ℕ => v / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
      exact h.congr fun n => by simp
    have h1 := ((tendsto_const_nhds (x := Real.sqrt K)).mul h0).mul_const v
    have h2 := ((h1.add_const (Real.sqrt M4 * (v - u))).pow 2).const_mul
      (16 * gaussFourthConst)
    convert h2 using 2
    rw [mul_zero, zero_mul, zero_add, mul_pow, Real.sq_sqrt hM40]
    ring
  exact integral_pow_four_le_of_tendsto hg (fun n => (hfL n).aestronglyMeasurable.aemeasurable)
    hlim (fun n => integrable_pow_of_memLp_four (hfL n) (k := 4) le_rfl)
    (fun n => integral_unifRiemann_sub_horizon_le B k hH hu hlt hvt n.succ_pos) hbc

end Horizon

end SignatureVolatility

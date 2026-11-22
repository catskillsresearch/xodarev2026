module

public import SignatureVolatility.ItoCalculusKit.ItoIncrement8


@[expose] public section

open MeasureTheory Filter Topology

namespace SignatureVolatility

/-!
# Changing the grid of an Itô–Riemann sum

* `integral_unifRiemann_sub_kitItoIntRaw_le`: `L⁴` rate `E (R_N - I_t)⁴ ≤ C / N²` of the uniform
  Itô–Riemann sums towards the raw Itô limit;
* `tendsto_fineIndicator`, `tendsto_fineStepSumOff`: any uniform-grid sum over a sub-interval
  `[x, y] ⊆ [0, v]` is the pathwise limit of fine-grid sums over `[0, v]` of its step integrand.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **`L⁴` rate of the uniform sums towards the raw Itô limit.** -/
theorem integral_unifRiemann_sub_kitItoIntRaw_le (B : MultiBrownian Ω P d) (hd : 0 < d)
    {H : ℝ → Ω → ℝ} {t K : ℝ} (ht : 0 ≤ t) (hH : HolderAdapted B H t K) {N : ℕ} (hN : 0 < N) :
    Integrable (fun ω => (unifRiemann B (kitDriver hd) H t N ω - kitItoIntRaw B H t ω) ^ 4) P ∧
      ∫ ω, (unifRiemann B (kitDriver hd) H t N ω - kitItoIntRaw B H t ω) ^ 4 ∂P ≤
        8 * (16 * gaussFourthConst * K * t ^ 4 / (N : ℝ) ^ 2) := by
  set k := kitDriver hd
  have hI := kitItoIntRaw_of_holderAdapted B hd ht hH
  have LN := memLp_unifRiemann B k ht hH hN
  have hg : AEStronglyMeasurable (fun ω => unifRiemann B k H t N ω - kitItoIntRaw B H t ω) P :=
    (LN.sub hI.2.1).aestronglyMeasurable
  have hfL : ∀ M : ℕ, MemLp (fun ω => unifRiemann B k H t N ω -
      unifRiemann B k H t (M + 1) ω) 4 P := fun M =>
    LN.sub (memLp_unifRiemann B k ht hH M.succ_pos)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun M : ℕ => unifRiemann B k H t N ω -
      unifRiemann B k H t (M + 1) ω) atTop
      (𝓝 (unifRiemann B k H t N ω - kitItoIntRaw B H t ω)) := by
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

private lemma sum_range_ite_wnnIncr' (B : MultiBrownian Ω P d) (k : Fin d) {δ c c' : ℝ}
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

private lemma tendsto_ceil_mul' (c : ℝ) (hc : 0 ≤ c) {δ : ℕ → ℝ} (hδ : ∀ M, 0 < δ M)
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

/-- **Fine-grid representation of one Brownian increment** `W_b - W_a`, `0 ≤ a ≤ b ≤ v`. -/
theorem tendsto_fineIndicator (B : MultiBrownian Ω P d) (k : Fin d) {v a b : ℝ} (hv : 0 < v)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b ≤ v) (ω : Ω) :
    Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
        (if a ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) ∧ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) < b then
          wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
            (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω else 0)) atTop
      (𝓝 (wnnIncr B k a b ω)) := by
  set δ : ℕ → ℝ := fun M => v / ((M + 1 : ℕ) : ℝ) with hδdef
  have hδ : ∀ M, 0 < δ M := fun M => div_pos hv (by positivity)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun M => ?_
    simp [hδdef]
  have hW : Continuous fun x : ℝ => B.Wnn (Real.toNNReal x) ω k :=
    (B.pathContinuous k ω).comp continuous_real_toNNReal
  have hbM : ∀ M : ℕ, b ≤ ((M + 1 : ℕ) : ℝ) * δ M := fun M => by
    have : ((M + 1 : ℕ) : ℝ) * δ M = v := by simp only [hδdef]; field_simp
    linarith
  have hrepr := fun M : ℕ => sum_range_ite_wnnIncr' B k (hδ M) hab (hbM M) ω
  refine Tendsto.congr (fun M => (hrepr M).symm) ?_
  have h1 := tendsto_ceil_mul' b (ha.trans hab) hδ hδ0
  have h0 := tendsto_ceil_mul' a ha hδ hδ0
  exact ((hW.tendsto _).comp h1).sub ((hW.tendsto _).comp h0)

/-- **Fine-grid representation of a uniform sum over a sub-interval** `[x, y] ⊆ [0, v]`:
`∑_{j<N} h_j (W_{x+(j+1)Δ} - W_{x+jΔ})`, `Δ = (y - x)/N`, is the pathwise limit of the fine sums
of its step integrand `s ↦ stepFun (y - x) N h (s - x)`. -/
theorem tendsto_fineStepSumOff (B : MultiBrownian Ω P d) (k : Fin d) {x y v : ℝ} (hv : 0 < v)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyv : y ≤ v) (N : ℕ) (h : ℕ → ℝ) (ω : Ω) :
    Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
        stepFun (y - x) N h ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) - x) *
          wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
            (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω) atTop
      (𝓝 (∑ j ∈ Finset.range N, h j * wnnIncr B k (x + (j : ℝ) * ((y - x) / (N : ℝ)))
        (x + ((j + 1 : ℕ) : ℝ) * ((y - x) / (N : ℝ))) ω)) := by
  set Δ : ℝ := (y - x) / (N : ℝ) with hΔ
  have hΔ0 : 0 ≤ Δ := div_nonneg (sub_nonneg.mpr hxy) (Nat.cast_nonneg _)
  have hrepr : ∀ M : ℕ, ∑ i ∈ Finset.range (M + 1),
      stepFun (y - x) N h ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) - x) *
        wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
          (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω =
      ∑ j ∈ Finset.range N, h j * ∑ i ∈ Finset.range (M + 1),
        (if x + (j : ℝ) * Δ ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) ∧
            (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) < x + ((j + 1 : ℕ) : ℝ) * Δ then
          wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
            (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω else 0) := by
    intro M
    unfold stepFun
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff : ((j : ℝ) * Δ ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) - x ∧
        (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) - x < ((j + 1 : ℕ) : ℝ) * Δ) ↔
        (x + (j : ℝ) * Δ ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) ∧
          (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) < x + ((j + 1 : ℕ) : ℝ) * Δ) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [← hΔ]
    by_cases hc : x + (j : ℝ) * Δ ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) ∧
        (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) < x + ((j + 1 : ℕ) : ℝ) * Δ
    · simp only [hiff.mpr hc, hc, and_self, ↓reduceIte]
    · have hc' : ¬ ((j : ℝ) * Δ ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) - x ∧
          (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) - x < ((j + 1 : ℕ) : ℝ) * Δ) :=
        fun h' => hc (hiff.mp h')
      simp only [hc', hc, ↓reduceIte, mul_zero]
  refine Tendsto.congr (fun M => (hrepr M).symm) ?_
  refine tendsto_finsetSum _ fun j hj => tendsto_const_nhds.mul ?_
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.mp hj)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjN : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.mp hj
  have hle : ((j + 1 : ℕ) : ℝ) * Δ ≤ y - x := by
    calc ((j + 1 : ℕ) : ℝ) * Δ ≤ (N : ℝ) * Δ := mul_le_mul_of_nonneg_right hjN hΔ0
      _ = y - x := by rw [hΔ]; field_simp
  exact tendsto_fineIndicator B k hv (by positivity)
    (by have : (j : ℝ) * Δ ≤ ((j + 1 : ℕ) : ℝ) * Δ :=
          mul_le_mul_of_nonneg_right (by push_cast; linarith) hΔ0
        linarith) (by linarith) ω

section FineFatou

variable (B : MultiBrownian Ω P d) (k : Fin d)

private lemma fine_grid_mem {v : ℝ} (hv : 0 < v) (M i : ℕ) (hi : i < M + 1) :
    0 ≤ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) ∧ (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) < v := by
  have hδ : 0 < v / ((M + 1 : ℕ) : ℝ) := div_pos hv (by positivity)
  refine ⟨by positivity, ?_⟩
  have h1 : (i : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  calc (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) < ((M + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_right h1 hδ
    _ = v := by field_simp

private lemma fine_grid_mono {v : ℝ} (hv : 0 < v) (M : ℕ) :
    Monotone fun i : ℕ => (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) := fun i j hij =>
  mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (div_pos hv (by positivity)).le

private lemma fine_grid_sum {v c : ℝ} (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), c * (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ)) -
      (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) = c * v := by
  rw [← Finset.mul_sum, Finset.sum_range_sub (fun i : ℕ => (i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))]
  simp only [Nat.cast_zero, zero_mul, sub_zero]
  congr 1
  field_simp

/-- **Fatou along fine grids (fourth moments).** If `X` is the pathwise limit of the fine-grid
sums of an adapted `L⁴` step integrand `D` with `√E D_s⁴ ≤ c` on `[0, v)`, then
`E X⁴ ≤ 16 · 𝔼[G⁴] · (c v)²`. -/
theorem integral_pow_four_le_of_fineSums {v c : ℝ} (hv : 0 < v) (D : ℝ → Ω → ℝ)
    (hD : ∀ s, 0 ≤ s → s < v → Measurable[(pathFiltration B).σAlg s] (D s) ∧ MemLp (D s) 4 P)
    (hc : ∀ s, 0 ≤ s → s < v → Real.sqrt (∫ ω, D s ω ^ 4 ∂P) ≤ c) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
      D ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω *
        wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
          (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω) atTop (𝓝 (X ω))) :
    Integrable (fun ω => X ω ^ 4) P ∧ ∫ ω, X ω ^ 4 ∂P ≤ 16 * gaussFourthConst * (c * v) ^ 2 := by
  set δ : ℕ → ℝ := fun M => v / ((M + 1 : ℕ) : ℝ) with hδdef
  have hδ : ∀ M, 0 < δ M := fun M => div_pos hv (by positivity)
  set F : ℕ → Ω → ℝ := fun M ω => ∑ i ∈ Finset.range (M + 1),
    D ((i : ℝ) * δ M) ω * wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω with hFdef
  have hFL : ∀ M, MemLp (F M) 4 P := by
    intro M
    have h := memLp_finsetSum' (p := 4) (μ := P) (Finset.range (M + 1))
      (f := fun i ω => D ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) fun i hi => by
      have hg := fine_grid_mem hv M i (Finset.mem_range.mp hi)
      exact memLp_mul_wnnIncr B k hg.1 (fine_grid_mono hv M (Nat.le_succ i))
        (hD _ hg.1 hg.2).1 (hD _ hg.1 hg.2).2
    have hfun : (∑ i ∈ Finset.range (M + 1), fun ω => D ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) = F M := by
      funext ω; simp [hFdef]
    rwa [hfun] at h
  have hc0 : 0 ≤ c := (Real.sqrt_nonneg _).trans (hc 0 le_rfl hv)
  have hbound : ∀ M, ∫ ω, F M ω ^ 4 ∂P ≤ 16 * gaussFourthConst * (c * v) ^ 2 := by
    intro M
    have hT := integral_transform_pow_four_le B k (τ := fun i : ℕ => (i : ℝ) * δ M)
      (by simp) (fine_grid_mono hv M) (fun i => D ((i : ℝ) * δ M)) (M + 1)
      (fun j hj => (hD _ (fine_grid_mem hv M j hj).1 (fine_grid_mem hv M j hj).2).1)
      (fun j hj => (hD _ (fine_grid_mem hv M j hj).1 (fine_grid_mem hv M j hj).2).2)
    refine hT.trans ?_
    have hg4 := gaussFourthConst_nonneg
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (fine_grid_mono hv M (Nat.le_succ i)))) ?_ 2
    calc ∑ i ∈ Finset.range (M + 1), Real.sqrt (∫ ω, D ((i : ℝ) * δ M) ω ^ 4 ∂P) *
          (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M)
        ≤ ∑ i ∈ Finset.range (M + 1), c * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
            (hc _ (fine_grid_mem hv M i (Finset.mem_range.mp hi)).1
              (fine_grid_mem hv M i (Finset.mem_range.mp hi)).2)
            (sub_nonneg.mpr (fine_grid_mono hv M (Nat.le_succ i)))
      _ = c * v := fine_grid_sum M
  exact integral_pow_four_le_of_tendsto hX (fun M => (hFL M).aestronglyMeasurable.aemeasurable)
    hlim (fun M => integrable_pow_of_memLp_four (hFL M) (k := 4) le_rfl) hbound
    tendsto_const_nhds

/-- **Fatou along fine grids (eighth moments).** -/
theorem integral_pow_eight_le_of_fineSums {v c : ℝ} (hv : 0 < v) (D : ℝ → Ω → ℝ)
    (hD : ∀ s, 0 ≤ s → s < v → Measurable[(pathFiltration B).σAlg s] (D s) ∧ MemLp (D s) 8 P)
    (hc : ∀ s, 0 ≤ s → s < v → root4 (∫ ω, D s ω ^ 8 ∂P) ≤ c) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
      D ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω *
        wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
          (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω) atTop (𝓝 (X ω))) :
    Integrable (fun ω => X ω ^ 8) P ∧
      ∫ ω, X ω ^ 8 ∂P ≤ (14 * root4 gauss8Const * (c * v)) ^ 4 := by
  set δ : ℕ → ℝ := fun M => v / ((M + 1 : ℕ) : ℝ) with hδdef
  have hδ : ∀ M, 0 < δ M := fun M => div_pos hv (by positivity)
  set F : ℕ → Ω → ℝ := fun M ω => ∑ i ∈ Finset.range (M + 1),
    D ((i : ℝ) * δ M) ω * wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω with hFdef
  have hFL : ∀ M, MemLp (F M) 8 P := by
    intro M
    have h := memLp_finsetSum' (p := 8) (μ := P) (Finset.range (M + 1))
      (f := fun i ω => D ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) fun i hi => by
      have hg := fine_grid_mem hv M i (Finset.mem_range.mp hi)
      exact memLp_mul_wnnIncr_eight B k hg.1 (fine_grid_mono hv M (Nat.le_succ i))
        (hD _ hg.1 hg.2).1 (hD _ hg.1 hg.2).2
    have hfun : (∑ i ∈ Finset.range (M + 1), fun ω => D ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) = F M := by
      funext ω; simp [hFdef]
    rwa [hfun] at h
  have hc0 : 0 ≤ c := (root4_nonneg _).trans (hc 0 le_rfl hv)
  have hbound : ∀ M, ∫ ω, F M ω ^ 8 ∂P ≤ (14 * root4 gauss8Const * (c * v)) ^ 4 := by
    intro M
    have hT := integral_transform_pow_eight_le B k (τ := fun i : ℕ => (i : ℝ) * δ M)
      (by simp) (fine_grid_mono hv M) (fun i => D ((i : ℝ) * δ M)) (M + 1)
      (fun j hj => (hD _ (fine_grid_mem hv M j hj).1 (fine_grid_mem hv M j hj).2).1)
      (fun j hj => (hD _ (fine_grid_mem hv M j hj).1 (fine_grid_mem hv M j hj).2).2)
    refine hT.trans ?_
    have hg8 := root4_nonneg gauss8Const
    refine pow_le_pow_left₀ (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (root4_nonneg _) (sub_nonneg.mpr (fine_grid_mono hv M (Nat.le_succ i))))) ?_ 4
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ i ∈ Finset.range (M + 1), root4 (∫ ω, D ((i : ℝ) * δ M) ω ^ 8 ∂P) *
          (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M)
        ≤ ∑ i ∈ Finset.range (M + 1), c * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
            (hc _ (fine_grid_mem hv M i (Finset.mem_range.mp hi)).1
              (fine_grid_mem hv M i (Finset.mem_range.mp hi)).2)
            (sub_nonneg.mpr (fine_grid_mono hv M (Nat.le_succ i)))
      _ = c * v := fine_grid_sum M
  exact integral_pow_eight_le_of_tendsto hX (fun M => (hFL M).aestronglyMeasurable.aemeasurable)
    hlim (fun M => integrable_pow_of_memLp_eight (hFL M) (k := 8) le_rfl) hbound
    tendsto_const_nhds

end FineFatou

/-- Uniform Itô–Riemann sum over `[u, v]` with `N` cells. -/
noncomputable def offRiemann (B : MultiBrownian Ω P d) (k : Fin d) (H : ℝ → Ω → ℝ) (u v : ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range N, H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω *
    wnnIncr B k (u + (j : ℝ) * ((v - u) / (N : ℝ))) (u + ((j + 1 : ℕ) : ℝ) * ((v - u) / (N : ℝ))) ω

section GridChange

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- Fourth-moment Hölder bound for a pair of times at distance `≤ δ`. -/
lemma sqrt_integral_sub_pow_four_le (hH : HolderAdapted B H t K) {p q δ : ℝ} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hpt : p ≤ t) (hqt : q ≤ t) (hδ : 0 ≤ δ) (hpq : |p - q| ≤ δ) :
    Real.sqrt (∫ ω, (H p ω - H q ω) ^ 4 ∂P) ≤ Real.sqrt K * δ := by
  have hK := hH.K_nonneg
  have hsq : (p - q) ^ 2 ≤ δ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpq 2
  have hhol : ∫ ω, (H p ω - H q ω) ^ 4 ∂P ≤ K * δ ^ 2 := by
    rcases le_total q p with hqp | hpq'
    · exact (hH.holder q p hq hqp hpt).trans (mul_le_mul_of_nonneg_left hsq hK)
    · have h := hH.holder p q hp hpq' hqt
      have heq : ∫ ω, (H p ω - H q ω) ^ 4 ∂P = ∫ ω, (H q ω - H p ω) ^ 4 ∂P := by
        congr 1; funext ω; ring
      rw [heq]
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hK)
      have : (q - p) ^ 2 = (p - q) ^ 2 := by ring
      rw [this]; exact hsq
  calc Real.sqrt (∫ ω, (H p ω - H q ω) ^ 4 ∂P) ≤ Real.sqrt (K * δ ^ 2) := Real.sqrt_le_sqrt hhol
    _ = Real.sqrt K * δ := by rw [Real.sqrt_mul hK, Real.sqrt_sq hδ]

/-- The step-integrand difference `[0, v]`-grid minus `[0, u]`-grid minus `[u, v]`-grid. -/
noncomputable def gridDiff (H : ℝ → Ω → ℝ) (u v : ℝ) (N : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  stepFun v N (fun j => H ((j : ℝ) * (v / (N : ℝ))) ω) s -
    stepFun u N (fun j => H ((j : ℝ) * (u / (N : ℝ))) ω) s -
      stepFun (v - u) N (fun j => H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω) (s - u)

omit [MeasurableSpace Ω] in
lemma gridDiff_eq {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) {N : ℕ} (hN : 0 < N) {s : ℝ}
    (hs : 0 ≤ s) (hsv : s < v) :
    ∃ p q : ℝ, 0 ≤ p ∧ p ≤ s ∧ 0 ≤ q ∧ q ≤ s ∧ |p - q| ≤ v / (N : ℝ) ∧
      ∀ ω, gridDiff H u v N s ω = H p ω - H q ω := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hu.trans_lt huv
  have hΔv : 0 < v / (N : ℝ) := div_pos hv hNr
  have hΔuv : 0 < (v - u) / (N : ℝ) := div_pos (sub_pos.mpr huv) hNr
  have hle1 : (v - u) / (N : ℝ) ≤ v / (N : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hNr.le
  obtain ⟨ha0, ha1, ha2⟩ := floor_mul_mem hΔv hs
  set a := (⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ)) with ha
  by_cases hsu : s < u
  · have hu0 : 0 < u := hs.trans_lt hsu
    have hΔu : 0 < u / (N : ℝ) := div_pos hu0 hNr
    have hle2 : u / (N : ℝ) ≤ v / (N : ℝ) := div_le_div_of_nonneg_right huv.le hNr.le
    obtain ⟨hb0, hb1, hb2⟩ := floor_mul_mem hΔu hs
    refine ⟨a, (⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ)), ha0, ha1, hb0, hb1, ?_, fun ω => ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · unfold gridDiff
      rw [stepFun_eq hv.le hN, stepFun_eq hu hN, stepFun_eq (sub_nonneg.mpr huv.le) hN]
      have h3 : ¬ (0 ≤ s - u ∧ s - u < v - u) := fun h => by linarith [h.1]
      simp only [hs, hsv, hsu, and_self, ↓reduceIte, h3, sub_zero]
      rfl
  · have hus : u ≤ s := not_lt.mp hsu
    obtain ⟨hc0, hc1, hc2⟩ := floor_mul_mem hΔuv (sub_nonneg.mpr hus)
    refine ⟨a, u + (⌊(s - u) / ((v - u) / (N : ℝ))⌋₊ : ℝ) * ((v - u) / (N : ℝ)), ha0, ha1,
      by linarith, by linarith, ?_, fun ω => ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · unfold gridDiff
      rw [stepFun_eq hv.le hN, stepFun_eq hu hN, stepFun_eq (sub_nonneg.mpr huv.le) hN]
      have h3 : 0 ≤ s - u ∧ s - u < v - u := ⟨sub_nonneg.mpr hus, by linarith⟩
      simp only [hs, hsv, and_self, ↓reduceIte, h3, true_and, hsu, sub_zero]
      rfl

/-- **Grid change**: `E (R_v^N - R_u^N - R_{[u,v]}^N)⁴ ≤ 16 · 𝔼[G⁴] · (√K (v/N) v)²`. -/
theorem integral_gridChange_le (hH : HolderAdapted B H t K) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    Integrable (fun ω => (unifRiemann B k H v N ω - unifRiemann B k H u N ω -
      offRiemann B k H u v N ω) ^ 4) P ∧
    ∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω) ^ 4 ∂P ≤
      16 * gaussFourthConst * (Real.sqrt K * (v / (N : ℝ)) * v) ^ 2 := by
  have hv : 0 < v := hu.trans_lt huv
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hΔ : 0 ≤ v / (N : ℝ) := (div_pos hv hNr).le
  have hDprop : ∀ s, 0 ≤ s → s < v →
      (Measurable[(pathFiltration B).σAlg s] (gridDiff H u v N s) ∧
        MemLp (gridDiff H u v N s) 4 P) ∧
      Real.sqrt (∫ ω, gridDiff H u v N s ω ^ 4 ∂P) ≤ Real.sqrt K * (v / (N : ℝ)) := by
    intro s hs hsv
    obtain ⟨p, q, hp0, hps, hq0, hqs, hpq, hD⟩ := gridDiff_eq (H := H) hu huv hN hs hsv
    have hpt : p ≤ t := hps.trans (hsv.le.trans hvt)
    have hqt : q ≤ t := hqs.trans (hsv.le.trans hvt)
    have hfun : gridDiff H u v N s = fun ω => H p ω - H q ω := funext hD
    rw [hfun]
    refine ⟨⟨((hH.meas p hp0 hpt).mono ((pathFiltration B).mono hps) le_rfl).sub
      ((hH.meas q hq0 hqt).mono ((pathFiltration B).mono hqs) le_rfl),
      (hH.memLp p hp0 hpt).sub (hH.memLp q hq0 hqt)⟩, ?_⟩
    exact sqrt_integral_sub_pow_four_le B hH hp0 hq0 hpt hqt hΔ hpq
  have hlim : ∀ ω, Tendsto (fun M : ℕ => ∑ i ∈ Finset.range (M + 1),
      gridDiff H u v N ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω *
        wnnIncr B k ((i : ℝ) * (v / ((M + 1 : ℕ) : ℝ)))
          (((i + 1 : ℕ) : ℝ) * (v / ((M + 1 : ℕ) : ℝ))) ω) atTop
      (𝓝 (unifRiemann B k H v N ω - unifRiemann B k H u N ω - offRiemann B k H u v N ω)) := by
    intro ω
    have h1 := tendsto_fineStepSum B k hv.le le_rfl N (fun j => H ((j : ℝ) * (v / (N : ℝ))) ω) ω
    have h2 := tendsto_fineStepSum B k hu huv.le N (fun j => H ((j : ℝ) * (u / (N : ℝ))) ω) ω
    have h3 := tendsto_fineStepSumOff B k hv hu huv.le le_rfl N
      (fun j => H (u + (j : ℝ) * ((v - u) / (N : ℝ))) ω) ω
    refine ((h1.sub h2).sub h3).congr fun M => ?_
    simp only [gridDiff, sub_mul, Finset.sum_sub_distrib]
  have hm : AEStronglyMeasurable (fun ω => unifRiemann B k H v N ω - unifRiemann B k H u N ω -
      offRiemann B k H u v N ω) P := by
    refine (((measurable_unifRiemann B k hv.le (hH.mono hvt) hN).sub
      (measurable_unifRiemann B k hu (hH.mono (huv.le.trans hvt)) hN)).sub ?_).aestronglyMeasurable
    unfold offRiemann
    refine Finset.measurable_sum _ fun j hj => ?_
    have hj' : (j : ℝ) * ((v - u) / (N : ℝ)) ≤ v - u := by
      have : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hj).le
      calc (j : ℝ) * ((v - u) / (N : ℝ)) ≤ (N : ℝ) * ((v - u) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_right this (div_nonneg (by linarith) hNr.le)
        _ = v - u := by field_simp
    exact ((hH.meas _ (by have := div_nonneg (sub_nonneg.mpr huv.le) hNr.le; positivity)
      (by linarith)).mono ((pathFiltration B).le_ambient _) le_rfl).mul
      (measurable_wnnIncr B k _ _)
  exact integral_pow_four_le_of_fineSums B k hv (gridDiff H u v N)
    (fun s hs hsv => (hDprop s hs hsv).1) (fun s hs hsv => (hDprop s hs hsv).2) hm
    (ae_of_all _ hlim)

end GridChange

end SignatureVolatility

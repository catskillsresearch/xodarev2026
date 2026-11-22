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

end SignatureVolatility

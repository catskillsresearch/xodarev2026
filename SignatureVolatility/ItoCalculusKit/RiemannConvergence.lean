module

public import SignatureVolatility.ItoCalculusKit.KitRaw
public import SignatureVolatility.ItoCalculusKit.MartingaleTransform


@[expose] public section

open MeasureTheory Filter Topology Finset

noncomputable section

namespace SignatureVolatility

/-!
# Almost-sure, full-sequence convergence of uniform Itô–Riemann sums

For an integrand `H` that is adapted to the joint path filtration and `L⁴`-Hölder of order `1/2`
on `[0, t]` (`HolderAdapted`: `𝔼|H_v - H_u|⁴ ≤ K (v - u)²`), the left Itô–Riemann sums on the
**non-nested** uniform grids `i·t/N` converge **almost surely along the full sequence** `N → ∞`
(`exists_ae_tendsto_unifRiemann`), so the kit's raw `limUnder` Itô integral is a genuine a.s.
limit, lies in `L⁴`, and is integrable (`kitItoIntRaw_of_holderAdapted`).

Proof: two uniform grids with `N` and `M` cells are both refined by the uniform grid with `N·M`
cells; a refinement changes the sum by a martingale transform with small integrand, whose fourth
moment is `O(N⁻²)` by `integral_transform_pow_four_le`. A dyadic subsequence converges a.s.
(geometric Borel–Cantelli), Fatou transfers the `O(N⁻²)` bound to the limit, and summability in
`N` gives full-sequence a.s. convergence.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Left Itô–Riemann sum of `H` against `W^k` on the uniform grid of `[0, t]` with `N` cells. -/
def unifRiemann (B : MultiBrownian Ω P d) (k : Fin d) (H : ℝ → Ω → ℝ) (t : ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ range N, H ((i : ℝ) * (t / (N : ℝ))) ω *
    wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω

lemma itoRiemann_process_eq_unifRiemann (B : MultiBrownian Ω P d) (k : Fin d) (H : ℝ → Ω → ℝ)
    (t : ℝ) (n : ℕ) (ω : Ω) :
    itoRiemann_process B k H 0 t n ω = unifRiemann B k H t (n + 1) ω := by
  simp only [itoRiemann_process, unifRiemann, zero_add, sub_zero, Nat.cast_add, Nat.cast_one]

/-- Adapted (joint path filtration) and `L⁴`-Hölder-`1/2` integrands on `[0, t]`. -/
structure HolderAdapted (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t K : ℝ) : Prop where
  K_nonneg : 0 ≤ K
  meas : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u)
  memLp : ∀ u, 0 ≤ u → u ≤ t → MemLp (H u) 4 P
  holder : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t → ∫ ω, (H v ω - H u ω) ^ 4 ∂P ≤ K * (v - u) ^ 2

lemma unifGrid_mem {t : ℝ} (ht : 0 ≤ t) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    0 ≤ (i : ℝ) * (t / (N : ℝ)) ∧ (i : ℝ) * (t / (N : ℝ)) ≤ t := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hΔ : 0 ≤ t / (N : ℝ) := div_nonneg ht hNr.le
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hΔ, ?_⟩
  calc (i : ℝ) * (t / (N : ℝ)) ≤ (N : ℝ) * (t / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hΔ
    _ = t := by field_simp

lemma sum_range_mul_div (N p : ℕ) (hp : 0 < p) (a b : ℕ → ℝ) :
    ∑ i ∈ range (N * p), a (i / p) * b i =
      ∑ j ∈ range N, a j * ∑ r ∈ range p, b (j * p + r) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    have h : (N * p + r) / p = N := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp,
        Nat.div_eq_of_lt (Finset.mem_range.mp hr), zero_add]
    rw [h]

/-- A coarse-cell increment is the sum of the fine-cell increments. -/
lemma wnnIncr_coarse_eq_sum (B : MultiBrownian Ω P d) (k : Fin d) (t : ℝ) {N p : ℕ} (j : ℕ)
    (hN : 0 < N) (hp : 0 < p) (ω : Ω) :
    wnnIncr B k ((j : ℝ) * (t / (N : ℝ))) (((j + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω =
      ∑ r ∈ range p, wnnIncr B k (((j * p + r : ℕ) : ℝ) * (t / ((N * p : ℕ) : ℝ)))
        (((j * p + r + 1 : ℕ) : ℝ) * (t / ((N * p : ℕ) : ℝ))) ω := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpr : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h := Finset.sum_range_sub
    (fun r : ℕ => B.Wnn (Real.toNNReal (((j * p + r : ℕ) : ℝ) * (t / ((N * p : ℕ) : ℝ)))) ω k) p
  simp only [← Nat.add_assoc] at h
  have e1 : ((j * p + p : ℕ) : ℝ) * (t / ((N * p : ℕ) : ℝ)) =
      ((j + 1 : ℕ) : ℝ) * (t / (N : ℝ)) := by
    push_cast; field_simp
  have e0 : ((j * p + 0 : ℕ) : ℝ) * (t / ((N * p : ℕ) : ℝ)) = (j : ℝ) * (t / (N : ℝ)) := by
    rw [Nat.add_zero]; push_cast; field_simp
  simp only [wnnIncr]
  rw [h, e1, e0]

section Holder

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

lemma measurable_unifRiemann (ht : 0 ≤ t) (hH : HolderAdapted B H t K) {N : ℕ} (hN : 0 < N) :
    Measurable (unifRiemann B k H t N) := by
  unfold unifRiemann
  refine Finset.measurable_sum _ fun i hi => ?_
  obtain ⟨h0, h1⟩ := unifGrid_mem ht hN (Finset.mem_range.mp hi).le
  exact ((hH.meas _ h0 h1).mono ((pathFiltration B).le_ambient _) le_rfl).mul
    (measurable_wnnIncr B k _ _)

lemma memLp_unifRiemann (ht : 0 ≤ t) (hH : HolderAdapted B H t K) {N : ℕ} (hN : 0 < N) :
    MemLp (unifRiemann B k H t N) 4 P := by
  have h := memLp_finsetSum' (p := 4) (μ := P) (range N)
    (f := fun i ω => H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω)
    fun i hi => by
      obtain ⟨h0, h1⟩ := unifGrid_mem ht hN (Finset.mem_range.mp hi).le
      have hstep : (i : ℝ) * (t / (N : ℝ)) ≤ ((i + 1 : ℕ) : ℝ) * (t / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith)
          (div_nonneg ht (Nat.cast_nonneg _))
      exact memLp_mul_wnnIncr B k h0 hstep (hH.meas _ h0 h1) (hH.memLp _ h0 h1)
  have hfun : (∑ i ∈ range N, fun ω => H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω) =
      unifRiemann B k H t N := by
    funext ω; simp [unifRiemann]
  rwa [hfun] at h

/-- **Refinement estimate.** Refining the uniform grid with `N` cells by a factor `p` changes the
Itô–Riemann sum by `O(N⁻²)` in fourth moment. -/
lemma integral_unifRiemann_refine_le (ht : 0 ≤ t) (hH : HolderAdapted B H t K) {N p : ℕ}
    (hN : 0 < N) (hp : 0 < p) :
    ∫ ω, (unifRiemann B k H t (N * p) ω - unifRiemann B k H t N ω) ^ 4 ∂P ≤
      16 * gaussFourthConst * K * t ^ 4 / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set δ : ℝ := t / ((N * p : ℕ) : ℝ) with hδdef
  have hδ : δ = t / ((N : ℝ) * (p : ℝ)) := by rw [hδdef]; push_cast; rfl
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hNpδ : (N : ℝ) * (p : ℝ) * δ = t := by rw [hδ]; field_simp
  have hpδ : (p : ℝ) * δ = t / (N : ℝ) := by rw [hδ]; field_simp
  set τ : ℕ → ℝ := fun i => (i : ℝ) * δ with hτdef
  have hτmono : Monotone τ := fun i j hij =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ0
  set h : ℕ → Ω → ℝ := fun i ω =>
    H ((i : ℝ) * δ) ω - H (((i / p : ℕ) : ℝ) * (t / (N : ℝ))) ω with hhdef
  -- geometry of the fine point `i δ` and its coarse left endpoint
  have hgeo : ∀ i < N * p,
      0 ≤ ((i / p : ℕ) : ℝ) * (t / (N : ℝ)) ∧
      ((i / p : ℕ) : ℝ) * (t / (N : ℝ)) ≤ (i : ℝ) * δ ∧ (i : ℝ) * δ ≤ t ∧
      (i : ℝ) * δ - ((i / p : ℕ) : ℝ) * (t / (N : ℝ)) ≤ t / (N : ℝ) := by
    intro i hi
    have hq1 : ((i / p : ℕ) : ℝ) * (p : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self i p
    have hq2 : (i : ℝ) < ((i / p : ℕ) : ℝ) * (p : ℝ) + (p : ℝ) := by
      exact_mod_cast Nat.lt_div_mul_add hp
    have hiN : (i : ℝ) ≤ (N : ℝ) * (p : ℝ) := by exact_mod_cast hi.le
    have hc : ((i / p : ℕ) : ℝ) * (t / (N : ℝ)) = ((i / p : ℕ) : ℝ) * (p : ℝ) * δ := by
      rw [mul_assoc, hpδ]
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (div_nonneg ht hNr.le), ?_, ?_, ?_⟩
    · rw [hc]; exact mul_le_mul_of_nonneg_right hq1 hδ0
    · calc (i : ℝ) * δ ≤ (N : ℝ) * (p : ℝ) * δ := mul_le_mul_of_nonneg_right hiN hδ0
        _ = t := hNpδ
    · rw [hc, ← sub_mul, ← hpδ]
      exact mul_le_mul_of_nonneg_right (by linarith) hδ0
  -- the difference is a martingale transform on the fine grid
  have hdiff : ∀ ω, unifRiemann B k H t (N * p) ω - unifRiemann B k H t N ω =
      ∑ i ∈ range (N * p), h i ω * wnnIncr B k (τ i) (τ (i + 1)) ω := by
    intro ω
    have hcoarse : unifRiemann B k H t N ω =
        ∑ i ∈ range (N * p), H (((i / p : ℕ) : ℝ) * (t / (N : ℝ))) ω *
          wnnIncr B k (τ i) (τ (i + 1)) ω := by
      rw [sum_range_mul_div N p hp (fun j => H ((j : ℝ) * (t / (N : ℝ))) ω)
        (fun i => wnnIncr B k (τ i) (τ (i + 1)) ω)]
      unfold unifRiemann
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [wnnIncr_coarse_eq_sum B k t j hN hp ω]
    have hfine : unifRiemann B k H t (N * p) ω =
        ∑ i ∈ range (N * p), H ((i : ℝ) * δ) ω * wnnIncr B k (τ i) (τ (i + 1)) ω := rfl
    rw [hfine, hcoarse, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hhdef]
    ring
  have hmeas : ∀ i < N * p, Measurable[(pathFiltration B).σAlg (τ i)] (h i) := by
    intro i hi
    obtain ⟨g0, g1, g2, _⟩ := hgeo i hi
    exact (hH.meas _ (g0.trans g1) g2).sub
      ((hH.meas _ g0 (g1.trans g2)).mono ((pathFiltration B).mono g1) le_rfl)
  have hLp : ∀ i < N * p, MemLp (h i) 4 P := by
    intro i hi
    obtain ⟨g0, g1, g2, _⟩ := hgeo i hi
    exact (hH.memLp _ (g0.trans g1) g2).sub (hH.memLp _ g0 (g1.trans g2))
  have hbound := integral_transform_pow_four_le B k (τ := τ) (by simp [hτdef]) hτmono h (N * p)
    hmeas hLp
  have hC := gaussFourthConst_nonneg
  have hK := hH.K_nonneg
  have hterm : ∀ i ∈ range (N * p),
      Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i) ≤ Real.sqrt K * (t / (N : ℝ)) * δ := by
    intro i hi
    obtain ⟨g0, g1, g2, g3⟩ := hgeo i (Finset.mem_range.mp hi)
    have hstep : τ (i + 1) - τ i = δ := by simp only [hτdef]; push_cast; ring
    have h4 : ∫ ω, h i ω ^ 4 ∂P ≤ K * (t / (N : ℝ)) ^ 2 :=
      (hH.holder _ _ g0 g1 g2).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr g1) g3 2) hK)
    have hs : Real.sqrt (∫ ω, h i ω ^ 4 ∂P) ≤ Real.sqrt K * (t / (N : ℝ)) := by
      calc Real.sqrt (∫ ω, h i ω ^ 4 ∂P) ≤ Real.sqrt (K * (t / (N : ℝ)) ^ 2) :=
            Real.sqrt_le_sqrt h4
        _ = Real.sqrt K * (t / (N : ℝ)) := by
            rw [Real.sqrt_mul hK, Real.sqrt_sq (div_nonneg ht hNr.le)]
    rw [hstep]
    exact mul_le_mul_of_nonneg_right hs hδ0
  have hsum : ∑ i ∈ range (N * p), Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i) ≤
      Real.sqrt K * (t / (N : ℝ)) * t := by
    calc ∑ i ∈ range (N * p), Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i)
        ≤ ∑ _i ∈ range (N * p), Real.sqrt K * (t / (N : ℝ)) * δ := Finset.sum_le_sum hterm
      _ = Real.sqrt K * (t / (N : ℝ)) * t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          rw [← hNpδ]
          ring
  have hsum0 : 0 ≤ ∑ i ∈ range (N * p), Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (hτmono (Nat.le_succ i)))
  calc ∫ ω, (unifRiemann B k H t (N * p) ω - unifRiemann B k H t N ω) ^ 4 ∂P
      = ∫ ω, (∑ i ∈ range (N * p), h i ω * wnnIncr B k (τ i) (τ (i + 1)) ω) ^ 4 ∂P := by
        simp only [hdiff]
    _ ≤ 16 * gaussFourthConst *
          (∑ i ∈ range (N * p), Real.sqrt (∫ ω, h i ω ^ 4 ∂P) * (τ (i + 1) - τ i)) ^ 2 := hbound
    _ ≤ 16 * gaussFourthConst * (Real.sqrt K * (t / (N : ℝ)) * t) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) (by positivity)
    _ = 16 * gaussFourthConst * K * t ^ 4 / (N : ℝ) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hK]
        field_simp

private lemma sub_pow_four_le' (a b : ℝ) : (a - b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg ((a + b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2)]

/-- **`L⁴`-Cauchy estimate** for the uniform Itô–Riemann sums (common refinement `N·M`). -/
lemma integral_unifRiemann_sub_le (ht : 0 ≤ t) (hH : HolderAdapted B H t K) {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) :
    ∫ ω, (unifRiemann B k H t N ω - unifRiemann B k H t M ω) ^ 4 ∂P ≤
      8 * (16 * gaussFourthConst * K * t ^ 4 / (N : ℝ) ^ 2) +
        8 * (16 * gaussFourthConst * K * t ^ 4 / (M : ℝ) ^ 2) := by
  have hNM : 0 < N * M := Nat.mul_pos hN hM
  have LN := memLp_unifRiemann B k ht hH hN
  have LM := memLp_unifRiemann B k ht hH hM
  have LNM := memLp_unifRiemann B k ht hH hNM
  have I1 : Integrable (fun ω => (unifRiemann B k H t (N * M) ω - unifRiemann B k H t M ω) ^ 4) P :=
    integrable_pow_of_memLp_four (LNM.sub LM) (k := 4) le_rfl
  have I2 : Integrable (fun ω => (unifRiemann B k H t (N * M) ω - unifRiemann B k H t N ω) ^ 4) P :=
    integrable_pow_of_memLp_four (LNM.sub LN) (k := 4) le_rfl
  have I0 : Integrable (fun ω => (unifRiemann B k H t N ω - unifRiemann B k H t M ω) ^ 4) P :=
    integrable_pow_of_memLp_four (LN.sub LM) (k := 4) le_rfl
  have e1 := integral_unifRiemann_refine_le B k ht hH hN hM
  have e2 := integral_unifRiemann_refine_le B k ht hH hM hN
  rw [Nat.mul_comm M N] at e2
  calc ∫ ω, (unifRiemann B k H t N ω - unifRiemann B k H t M ω) ^ 4 ∂P
      ≤ ∫ ω, (8 * (unifRiemann B k H t (N * M) ω - unifRiemann B k H t M ω) ^ 4 +
          8 * (unifRiemann B k H t (N * M) ω - unifRiemann B k H t N ω) ^ 4) ∂P := by
        refine integral_mono I0 ((I1.const_mul 8).add (I2.const_mul 8)) fun ω => ?_
        have h := sub_pow_four_le' (unifRiemann B k H t (N * M) ω - unifRiemann B k H t M ω)
          (unifRiemann B k H t (N * M) ω - unifRiemann B k H t N ω)
        calc (unifRiemann B k H t N ω - unifRiemann B k H t M ω) ^ 4
            = ((unifRiemann B k H t (N * M) ω - unifRiemann B k H t M ω) -
                (unifRiemann B k H t (N * M) ω - unifRiemann B k H t N ω)) ^ 4 := by ring
          _ ≤ _ := h
    _ = 8 * ∫ ω, (unifRiemann B k H t (N * M) ω - unifRiemann B k H t M ω) ^ 4 ∂P +
          8 * ∫ ω, (unifRiemann B k H t (N * M) ω - unifRiemann B k H t N ω) ^ 4 ∂P := by
        rw [integral_add (I1.const_mul 8) (I2.const_mul 8), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by linarith

/-- **Almost-sure, full-sequence convergence of the uniform Itô–Riemann sums** of an adapted
`L⁴`-Hölder integrand; the limit is measurable and in `L⁴`. -/
theorem exists_ae_tendsto_unifRiemann (ht : 0 ≤ t) (hH : HolderAdapted B H t K) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ MemLp Y 4 P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H t (n + 1) ω) atTop (𝓝 (Y ω)) := by
  set C₀ : ℝ := 16 * gaussFourthConst * K * t ^ 4 with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    have := gaussFourthConst_nonneg; have := hH.K_nonneg; positivity
  set R : ℕ → Ω → ℝ := fun N => unifRiemann B k H t N with hR
  have hRm : ∀ N, 0 < N → Measurable (R N) := fun N hN => measurable_unifRiemann B k ht hH hN
  have hRL : ∀ N, 0 < N → MemLp (R N) 4 P := fun N hN => memLp_unifRiemann B k ht hH hN
  have h2 : ∀ j : ℕ, 0 < 2 ^ j := fun j => Nat.pos_of_ne_zero (by positivity)
  -- dyadic increments
  set D : ℕ → Ω → ℝ := fun j ω => R (2 ^ (j + 1)) ω - R (2 ^ j) ω with hD
  have hDm : ∀ j, Measurable (D j) := fun j => (hRm _ (h2 _)).sub (hRm _ (h2 _))
  have hDL : ∀ j, MemLp (D j) 4 P := fun j => (hRL _ (h2 _)).sub (hRL _ (h2 _))
  have hD4 : ∀ j, ∫ ω, D j ω ^ 4 ∂P ≤ C₀ / 4 ^ j := by
    intro j
    have h := integral_unifRiemann_refine_le B k ht hH (N := 2 ^ j) (p := 2) (h2 j) two_pos
    rw [← pow_succ] at h
    refine h.trans (le_of_eq ?_)
    rw [hC₀]
    push_cast
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  -- geometric Borel–Cantelli: `(5/4)^j D_j → 0` a.s.
  have hgeo : ∀ᵐ ω ∂P, Tendsto (fun j => (5 / 4 : ℝ) ^ j * D j ω) atTop (𝓝 0) := by
    refine ae_tendsto_zero_of_summable_integral_pow_four
      (b := fun j => C₀ * (625 / 1024 : ℝ) ^ j)
      (fun j => (hDm j).const_mul _) (fun j => ?_) ?_ fun j => ?_
    · have hi := (integrable_pow_of_memLp_four (hDL j) (k := 4) le_rfl).const_mul
        (((5 / 4 : ℝ) ^ j) ^ 4)
      refine hi.congr (ae_of_all _ fun ω => ?_)
      simp only
      ring
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    · have he : ∫ ω, ((5 / 4 : ℝ) ^ j * D j ω) ^ 4 ∂P =
          ((5 / 4 : ℝ) ^ j) ^ 4 * ∫ ω, D j ω ^ 4 ∂P := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only
        ring
      rw [he]
      calc ((5 / 4 : ℝ) ^ j) ^ 4 * ∫ ω, D j ω ^ 4 ∂P
          ≤ ((5 / 4 : ℝ) ^ j) ^ 4 * (C₀ / 4 ^ j) :=
            mul_le_mul_of_nonneg_left (hD4 j) (by positivity)
        _ = C₀ * (625 / 1024 : ℝ) ^ j := by
            rw [show (625 / 1024 : ℝ) = (5 / 4) ^ 4 * 4⁻¹ by norm_num, mul_pow, ← pow_mul,
              ← pow_mul, mul_comm j 4, inv_pow]
            ring
  -- the dyadic subsequence converges a.s.
  set Y : Ω → ℝ := fun ω => limUnder atTop fun j => R (2 ^ j) ω with hY
  have hYm : Measurable Y :=
    (StronglyMeasurable.limUnder fun j => (hRm _ (h2 j)).stronglyMeasurable).measurable
  have hYlim : ∀ᵐ ω ∂P, Tendsto (fun j => R (2 ^ j) ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [hgeo] with ω hω
    have hev : ∀ᶠ j in atTop, ‖D j ω‖ ≤ (4 / 5 : ℝ) ^ j := by
      filter_upwards [(Metric.tendsto_nhds.mp hω) 1 one_pos] with j hj
      rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (5 / 4) ^ j)]
        at hj
      rw [Real.norm_eq_abs]
      have h54 : (0 : ℝ) < (5 / 4) ^ j := by positivity
      calc |D j ω| = ((5 / 4 : ℝ) ^ j * |D j ω|) / (5 / 4) ^ j := by field_simp
        _ ≤ 1 / (5 / 4) ^ j := by gcongr
        _ = (4 / 5 : ℝ) ^ j := by rw [one_div, ← inv_pow]; norm_num
    have hsum : Summable fun j => D j ω :=
      Summable.of_norm_bounded_eventually_nat
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)) hev
    have htel : ∀ J, R (2 ^ J) ω = R (2 ^ 0) ω + ∑ j ∈ range J, D j ω := by
      intro J
      have := Finset.sum_range_sub (fun j => R (2 ^ j) ω) J
      simp only [hD]
      linarith
    have hlim : Tendsto (fun J => R (2 ^ J) ω) atTop
        (𝓝 (R (2 ^ 0) ω + ∑' j, D j ω)) := by
      rw [show (fun J => R (2 ^ J) ω) = fun J => R (2 ^ 0) ω + ∑ j ∈ range J, D j ω from
        funext htel]
      exact tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
    have hYeq : Y ω = R (2 ^ 0) ω + ∑' j, D j ω := hlim.limUnder_eq
    rw [hYeq]
    exact hlim
  -- Fatou: `𝔼|R_N - Y|⁴ ≤ 16 C₀ / N²`
  have hpow : ∀ N : ℕ, 0 < N → ∀ J, N ≤ J → ((N : ℝ)) ^ 2 ≤ ((2 ^ J : ℕ) : ℝ) ^ 2 := by
    intro N _ J hJ
    have h1 : N ≤ 2 ^ J := (Nat.lt_two_pow_self (n := N)).le.trans
      (Nat.pow_le_pow_right two_pos hJ)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h1) 2
  have hFatou : ∀ N : ℕ, 0 < N →
      ∫⁻ ω, ENNReal.ofReal ((R N ω - Y ω) ^ 4) ∂P ≤ ENNReal.ofReal (16 * C₀ / (N : ℝ) ^ 2) := by
    intro N hN
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hcongr : ∫⁻ ω, ENNReal.ofReal ((R N ω - Y ω) ^ 4) ∂P =
        ∫⁻ ω, liminf (fun J => ENNReal.ofReal ((R N ω - R (2 ^ J) ω) ^ 4)) atTop ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hYlim] with ω hω
      have hc : Tendsto (fun J => ENNReal.ofReal ((R N ω - R (2 ^ J) ω) ^ 4)) atTop
          (𝓝 (ENNReal.ofReal ((R N ω - Y ω) ^ 4))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_const_nhds.sub hω).pow 4)
      exact hc.liminf_eq.symm
    rw [hcongr]
    refine (lintegral_liminf_le fun J =>
      (((hRm N hN).sub (hRm _ (h2 J))).pow_const 4).ennreal_ofReal).trans ?_
    refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
    obtain ⟨J, hbJ, hJ⟩ := (hb.and (eventually_ge_atTop N)).exists
    refine hbJ.trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_pow_of_memLp_four ((hRL N hN).sub (hRL _ (h2 J))) le_rfl)
      (ae_of_all _ fun ω => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle := integral_unifRiemann_sub_le B k ht hH hN (h2 J)
    have hJ2 := hpow N hN J hJ
    have h3 : C₀ / ((2 ^ J : ℕ) : ℝ) ^ 2 ≤ C₀ / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hC₀0 (by positivity) hJ2
    calc ∫ ω, (R N ω - R (2 ^ J) ω) ^ 4 ∂P
        ≤ 8 * (C₀ / (N : ℝ) ^ 2) + 8 * (C₀ / ((2 ^ J : ℕ) : ℝ) ^ 2) := hle
      _ ≤ 16 * C₀ / (N : ℝ) ^ 2 := by
          have : 16 * C₀ / (N : ℝ) ^ 2 = 8 * (C₀ / (N : ℝ) ^ 2) + 8 * (C₀ / (N : ℝ) ^ 2) := by
            ring
          linarith
  -- full-sequence a.s. convergence
  have hfull : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => R (n + 1) ω - Y ω) atTop (𝓝 0) := by
    refine ae_tendsto_zero_of_summable_lintegral_pow_four
      (b := fun n : ℕ => 16 * C₀ * (1 / ((n + 1 : ℕ) : ℝ) ^ 2))
      (fun n => (hRm _ n.succ_pos).sub hYm) ?_ fun n => ?_
    · exact ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
    · refine (hFatou (n + 1) n.succ_pos).trans (le_of_eq ?_)
      congr 1
      ring
  -- `Y ∈ L⁴`
  have hYL : MemLp Y 4 P := by
    have hdiff : MemLp (fun ω => R 1 ω - Y ω) 4 P := by
      refine memLp_four_of_integrable_pow_four
        ((hRm 1 one_pos).sub hYm).aestronglyMeasurable ⟨?_, ?_⟩
      · exact (((hRm 1 one_pos).sub hYm).pow_const 4).aestronglyMeasurable
      · have h := hFatou 1 one_pos
        have he : ∫⁻ ω, ‖(R 1 ω - Y ω) ^ 4‖ₑ ∂P =
            ∫⁻ ω, ENNReal.ofReal ((R 1 ω - Y ω) ^ 4) ∂P :=
          lintegral_congr fun ω => Real.enorm_eq_ofReal (by positivity)
        rw [HasFiniteIntegral, he]
        exact h.trans_lt ENNReal.ofReal_lt_top
    have h := (hRL 1 one_pos).sub hdiff
    have hfun : (R 1 - fun ω => R 1 ω - Y ω) = Y := by
      funext ω; simp
    rwa [hfun] at h
  refine ⟨Y, hYm, hYL, ?_⟩
  filter_upwards [hfull] with ω hω
  have h := hω.add_const (Y ω)
  simpa using h

end Holder

/-- **The raw kit Itô integral of an adapted `L⁴`-Hölder integrand** is an almost-sure limit of
its Itô–Riemann sums along the full sequence of uniform grids; it is in `L⁴`, hence integrable. -/
theorem kitItoIntRaw_of_holderAdapted (B : MultiBrownian Ω P d) (hd : 0 < d) {H : ℝ → Ω → ℝ}
    {t K : ℝ} (ht : 0 ≤ t) (hH : HolderAdapted B H t K) :
    (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B (kitDriver hd) H t (n + 1) ω) atTop
      (𝓝 (kitItoIntRaw B H t ω))) ∧ MemLp (kitItoIntRaw B H t) 4 P ∧
      Integrable (kitItoIntRaw B H t) P := by
  obtain ⟨Y, hYm, hYL, hYlim⟩ := exists_ae_tendsto_unifRiemann B (kitDriver hd) ht hH
  have hraw : ∀ ω, kitItoIntRaw B H t ω =
      limUnder atTop fun n : ℕ => unifRiemann B (kitDriver hd) H t (n + 1) ω := by
    intro ω
    simp only [kitItoIntRaw, hd, ↓reduceDIte, itoIntegral_process, ht]
    congr 1
    funext n
    rw [itoRiemann_process_eq_unifRiemann]
    unfold unifRiemann
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨h0, h1⟩ := unifGrid_mem ht n.succ_pos (Finset.mem_range.mp hi).le
    rw [forceMeasurableProcess_eq_of_adapted B (hH.meas _ h0 h1)]
  have hae : kitItoIntRaw B H t =ᵐ[P] Y := by
    filter_upwards [hYlim] with ω hω
    rw [hraw ω]
    exact hω.limUnder_eq
  have hL : MemLp (kitItoIntRaw B H t) 4 P := hYL.ae_eq hae.symm
  refine ⟨?_, hL, hL.integrable (by norm_num)⟩
  filter_upwards [hYlim, hae] with ω hω he
  rw [he]
  exact hω

end SignatureVolatility

module

public import SignatureVolatility.ItoCalculusKit.FrozenIncrement8

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Eighth-moment rate of the uniform Itô–Riemann sums

For an `L⁸`-Hölder adapted integrand, `𝔼 (R_N(t) - I_t)⁸ ≤ 14⁴ g₈ K t⁸ / N⁴`
(`integral_unifRiemann_sub_kitItoIntRaw_pow_eight_le`), from the eighth-order refinement bound
and Fatou along the almost-sure limit.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section Rate8

variable (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ} {t K : ℝ}

/-- **Eighth-order refinement bound** `𝔼 (R_{Np} - R_N)⁸ ≤ (14 g₈^{1/4} K^{1/4} (t/N) t)⁴`. -/
lemma integral_unifRiemann_refine_le8 (ht : 0 ≤ t) (hH : HolderAdapted8 B H t K) {N p : ℕ}
    (hN : 0 < N) (hp : 0 < p) :
    ∫ ω, (unifRiemann B k H t (N * p) ω - unifRiemann B k H t N ω) ^ 8 ∂P ≤
      (14 * root4 gauss8Const * (root4 K * (t / (N : ℝ)) * t)) ^ 4 := by
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
  have hLp : ∀ i < N * p, MemLp (h i) 8 P := by
    intro i hi
    obtain ⟨g0, g1, g2, _⟩ := hgeo i hi
    exact (hH.memLp _ (g0.trans g1) g2).sub (hH.memLp _ g0 (g1.trans g2))
  have hbound := integral_transform_pow_eight_le B k (τ := τ) (by simp [hτdef]) hτmono h (N * p)
    hmeas hLp
  have hK := hH.K_nonneg
  have hterm : ∀ i ∈ range (N * p),
      root4 (∫ ω, h i ω ^ 8 ∂P) * (τ (i + 1) - τ i) ≤ root4 K * (t / (N : ℝ)) * δ := by
    intro i hi
    obtain ⟨g0, g1, g2, g3⟩ := hgeo i (Finset.mem_range.mp hi)
    have hstep : τ (i + 1) - τ i = δ := by simp only [hτdef]; push_cast; ring
    have h8 : ∫ ω, h i ω ^ 8 ∂P ≤ (root4 K * (t / (N : ℝ))) ^ 4 := by
      rw [mul_pow, root4_pow_four hK]
      exact (hH.holder _ _ g0 g1 g2).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr g1) g3 4) hK)
    rw [hstep]
    exact mul_le_mul_of_nonneg_right
      (root4_le_of_le_pow (by have := root4_nonneg K; positivity) h8) hδ0
  have hsum : ∑ i ∈ range (N * p), root4 (∫ ω, h i ω ^ 8 ∂P) * (τ (i + 1) - τ i) ≤
      root4 K * (t / (N : ℝ)) * t := by
    calc ∑ i ∈ range (N * p), root4 (∫ ω, h i ω ^ 8 ∂P) * (τ (i + 1) - τ i)
        ≤ ∑ _i ∈ range (N * p), root4 K * (t / (N : ℝ)) * δ := Finset.sum_le_sum hterm
      _ = root4 K * (t / (N : ℝ)) * t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          rw [← hNpδ]
          ring
  have hsum0 : 0 ≤ ∑ i ∈ range (N * p), root4 (∫ ω, h i ω ^ 8 ∂P) * (τ (i + 1) - τ i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (root4_nonneg _) (sub_nonneg.mpr (hτmono (Nat.le_succ i)))
  calc ∫ ω, (unifRiemann B k H t (N * p) ω - unifRiemann B k H t N ω) ^ 8 ∂P
      = ∫ ω, (∑ i ∈ range (N * p), h i ω * wnnIncr B k (τ i) (τ (i + 1)) ω) ^ 8 ∂P := by
        simp only [hdiff]
    _ ≤ _ := hbound
    _ ≤ _ := by
        have hg := root4_nonneg gauss8Const
        exact pow_le_pow_left₀ (mul_nonneg (by positivity) hsum0)
          (mul_le_mul_of_nonneg_left hsum (by positivity)) 4

/-- **Eighth-moment rate** `𝔼 (R_N(t) - I_t)⁸ ≤ (14 g₈^{1/4} K^{1/4} (t/N) t)⁴`. -/
theorem integral_unifRiemann_sub_kitItoIntRaw_pow_eight_le (hd : 0 < d)
    (hH : HolderAdapted8 B H t K) (ht : 0 ≤ t) {N : ℕ} (hN : 0 < N) :
    Integrable (fun ω => (unifRiemann B (kitDriver hd) H t N ω - kitItoIntRaw B H t ω) ^ 8) P ∧
    ∫ ω, (unifRiemann B (kitDriver hd) H t N ω - kitItoIntRaw B H t ω) ^ 8 ∂P ≤
      (14 * root4 gauss8Const * (root4 K * (t / (N : ℝ)) * t)) ^ 4 := by
  obtain ⟨hlim, hL4, -⟩ := kitItoIntRaw_of_holderAdapted B hd ht hH.toHolderAdapted
  set k := kitDriver hd
  have hφ : Tendsto (fun p : ℕ => N * (p + 1) - 1) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b, fun p hp => ?_⟩
    have : p + 1 ≤ N * (p + 1) := Nat.le_mul_of_pos_left _ hN
    omega
  have hsub : ∀ p : ℕ, N * (p + 1) - 1 + 1 = N * (p + 1) := fun p =>
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' (Nat.succ_ne_zero p)))
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun p : ℕ =>
      unifRiemann B k H t N ω - unifRiemann B k H t (N * (p + 1)) ω) atTop
      (𝓝 (unifRiemann B k H t N ω - kitItoIntRaw B H t ω)) := by
    filter_upwards [hlim] with ω hω
    have := (hω.comp hφ).const_sub (unifRiemann B k H t N ω)
    refine this.congr fun p => ?_
    simp only [Function.comp_apply, hsub p]
  have hRN := memLp_unifRiemann_eight B k ht hH hN
  have hRm : ∀ p : ℕ, MemLp (unifRiemann B k H t (N * (p + 1))) 8 P := fun p =>
    memLp_unifRiemann_eight B k ht hH (Nat.mul_pos hN (Nat.succ_pos p))
  refine integral_pow_eight_le_of_tendsto
    (hRN.aestronglyMeasurable.sub hL4.aestronglyMeasurable)
    (fun p => (hRN.sub (hRm p)).aestronglyMeasurable.aemeasurable) hlim'
    (fun p => integrable_pow_of_memLp_eight (hRN.sub (hRm p)) (k := 8) le_rfl)
    (b := fun _ => (14 * root4 gauss8Const * (root4 K * (t / (N : ℝ)) * t)) ^ 4)
    (fun p => ?_) tendsto_const_nhds
  have := integral_unifRiemann_refine_le8 B k ht hH hN (Nat.succ_pos p)
  refine le_of_eq_of_le ?_ this
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show (unifRiemann B k H t N ω - unifRiemann B k H t (N * (p + 1)) ω) ^ 8 =
    (unifRiemann B k H t (N * (p + 1)) ω - unifRiemann B k H t N ω) ^ 8
  ring

end Rate8

end SignatureVolatility

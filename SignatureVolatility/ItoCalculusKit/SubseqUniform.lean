module

public import SignatureVolatility.ItoCalculusKit.HolderPath
public import SignatureVolatility.ItoCalculusKit.RiemannRate8

@[expose] public section

open MeasureTheory Filter Topology Finset Set

namespace SignatureVolatility

/-!
# Uniform-in-time convergence of the Itô–Riemann sums along a subsequence

Along `N_j = 2^{16 j}`, almost surely `R_{N_j}(t) → Ĩ_t` for **every** `t ∈ [0, T]`, where `Ĩ` is
a continuous version of the raw Itô integral.  The proof combines the eighth-moment rate
(`RiemannRate8`), Borel–Cantelli on the grids `m T / N_j³`, and the pathwise `7/20`-Hölder bounds
of `σ` and `W` (`HolderPath`), which control `R_N(t) - R_N(t')` deterministically.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **Deterministic continuity of a Riemann sum in its horizon.** -/
lemma abs_riemannSum_sub_le {f g : ℝ → ℝ} {T L G γ h : ℝ} (hγ : 0 < γ) (hL : 0 ≤ L)
    (hf : ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T, |f s' - f s| ≤ L * |s' - s| ^ γ)
    (hg : ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T, |g s' - g s| ≤ L * |s' - s| ^ γ)
    (hG : ∀ s ∈ Icc 0 T, |f s| ≤ G) {t t' : ℝ} (ht : t ∈ Icc 0 T) (ht' : t' ∈ Icc 0 T)
    (htt : |t - t'| ≤ h) {N : ℕ} (hN : 0 < N) :
    |∑ i ∈ range N, f ((i : ℝ) * (t / (N : ℝ))) *
        (g (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) - g ((i : ℝ) * (t / (N : ℝ)))) -
      ∑ i ∈ range N, f ((i : ℝ) * (t' / (N : ℝ))) *
        (g (((i + 1 : ℕ) : ℝ) * (t' / (N : ℝ))) - g ((i : ℝ) * (t' / (N : ℝ))))| ≤
      (N : ℝ) * (L * h ^ γ * (L * T ^ γ) + G * (2 * (L * h ^ γ))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : 0 ≤ h := (abs_nonneg _).trans htt
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      c * t ∈ Icc 0 T ∧ c * t' ∈ Icc 0 T ∧ |c * t - c * t'| ≤ h := by
    intro c hc0 hc1
    refine ⟨⟨mul_nonneg hc0 ht.1, ?_⟩, ⟨mul_nonneg hc0 ht'.1, ?_⟩, ?_⟩
    · nlinarith [ht.1, ht.2]
    · nlinarith [ht'.1, ht'.2]
    · rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
      nlinarith [abs_nonneg (t - t')]
  have hpow : ∀ x : ℝ, |x| ≤ h → |x| ^ γ ≤ h ^ γ := fun x hx =>
    Real.rpow_le_rpow (abs_nonneg _) hx hγ.le
  have hterm : ∀ i ∈ range N,
      |f ((i : ℝ) * (t / (N : ℝ))) *
          (g (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) - g ((i : ℝ) * (t / (N : ℝ)))) -
        f ((i : ℝ) * (t' / (N : ℝ))) *
          (g (((i + 1 : ℕ) : ℝ) * (t' / (N : ℝ))) - g ((i : ℝ) * (t' / (N : ℝ))))| ≤
        L * h ^ γ * (L * T ^ γ) + G * (2 * (L * h ^ γ)) := by
    intro i hi
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
    set c₁ : ℝ := (i : ℝ) / N
    set c₂ : ℝ := ((i : ℝ) + 1) / N
    have hc₁0 : 0 ≤ c₁ := by positivity
    have hc₂0 : 0 ≤ c₂ := by positivity
    have hc₂1 : c₂ ≤ 1 := by rw [div_le_one hNr]; exact hiN
    have hc₁1 : c₁ ≤ 1 := by rw [div_le_one hNr]; linarith
    have ea : ∀ s, (i : ℝ) * (s / (N : ℝ)) = c₁ * s := fun s => by ring
    have eb : ∀ s, ((i + 1 : ℕ) : ℝ) * (s / (N : ℝ)) = c₂ * s := fun s => by push_cast; ring
    simp only [ea, eb]
    obtain ⟨ha, ha', haa⟩ := key c₁ hc₁0 hc₁1
    obtain ⟨hb, hb', hbb⟩ := key c₂ hc₂0 hc₂1
    have hba : |c₂ * t - c₁ * t| ≤ T := by
      have hc12 : 0 ≤ c₂ - c₁ := by
        have : c₁ ≤ c₂ := div_le_div_of_nonneg_right (by linarith) hNr.le
        linarith
      rw [← sub_mul, abs_of_nonneg (mul_nonneg hc12 ht.1)]
      have : c₂ - c₁ ≤ 1 := by linarith
      nlinarith [ht.1, ht.2]
    have e1 := hf _ ha' _ ha
    have e2 := hg _ ha _ hb
    have e3 := hg _ hb' _ hb
    have e4 := hg _ ha' _ ha
    have e5 := hG _ ha'
    have p1 : |c₁ * t - c₁ * t'| ^ γ ≤ h ^ γ := hpow _ haa
    have p3 : |c₂ * t - c₂ * t'| ^ γ ≤ h ^ γ := hpow _ hbb
    have p2 : |c₂ * t - c₁ * t| ^ γ ≤ T ^ γ := Real.rpow_le_rpow (abs_nonneg _) hba hγ.le
    have hLh : 0 ≤ L * h ^ γ := mul_nonneg hL (Real.rpow_nonneg h0 _)
    have hG0 : 0 ≤ G := (abs_nonneg _).trans e5
    set A := f (c₁ * t)
    set A' := f (c₁ * t')
    set Δ := g (c₂ * t) - g (c₁ * t)
    set Δ' := g (c₂ * t') - g (c₁ * t')
    have hA : |A - A'| ≤ L * h ^ γ := e1.trans (mul_le_mul_of_nonneg_left p1 hL)
    have hΔ : |Δ| ≤ L * T ^ γ := e2.trans (mul_le_mul_of_nonneg_left p2 hL)
    have hΔΔ : |Δ - Δ'| ≤ 2 * (L * h ^ γ) := by
      have : Δ - Δ' = (g (c₂ * t) - g (c₂ * t')) - (g (c₁ * t) - g (c₁ * t')) := by ring
      rw [this]
      have q1 : |g (c₂ * t) - g (c₂ * t')| ≤ L * h ^ γ := by
        rw [abs_sub_comm]; exact (by simpa [abs_sub_comm] using e3 : _ ≤ _).trans
          (mul_le_mul_of_nonneg_left p3 hL)
      have q2 : |g (c₁ * t) - g (c₁ * t')| ≤ L * h ^ γ := by
        rw [abs_sub_comm]; exact (by simpa [abs_sub_comm] using e4 : _ ≤ _).trans
          (mul_le_mul_of_nonneg_left p1 hL)
      linarith [abs_sub (g (c₂ * t) - g (c₂ * t')) (g (c₁ * t) - g (c₁ * t'))]
    have : A * Δ - A' * Δ' = (A - A') * Δ + A' * (Δ - Δ') := by ring
    rw [this]
    calc |(A - A') * Δ + A' * (Δ - Δ')| ≤ |A - A'| * |Δ| + |A'| * |Δ - Δ'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ L * h ^ γ * (L * T ^ γ) + G * (2 * (L * h ^ γ)) := by
          gcongr
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ range N, |f ((i : ℝ) * (t / (N : ℝ))) *
          (g (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) - g ((i : ℝ) * (t / (N : ℝ)))) -
        f ((i : ℝ) * (t' / (N : ℝ))) *
          (g (((i + 1 : ℕ) : ℝ) * (t' / (N : ℝ))) - g ((i : ℝ) * (t' / (N : ℝ))))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range N, (L * h ^ γ * (L * T ^ γ) + G * (2 * (L * h ^ γ))) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The subsequence `N_j = 2^{16 j}`. -/
def subseqN (j : ℕ) : ℕ := 2 ^ (16 * j)

/-- The grid size `M_j = N_j³`. -/
def subseqM (j : ℕ) : ℕ := subseqN j ^ 3

/-- The grid points `m T / M_j`. -/
noncomputable def subseqGrid (T : ℝ) (j m : ℕ) : ℝ := (m : ℝ) * (T / (subseqM j : ℝ))

lemma subseqN_pos (j : ℕ) : 0 < subseqN j := by unfold subseqN; positivity

lemma subseqM_pos (j : ℕ) : 0 < subseqM j := by unfold subseqM; have := subseqN_pos j; positivity

lemma subseqN_cast (j : ℕ) : (subseqN j : ℝ) = ((2 : ℝ) ^ j) ^ 16 := by
  unfold subseqN; push_cast; rw [← pow_mul, mul_comm]

lemma subseqM_cast (j : ℕ) : (subseqM j : ℝ) = ((2 : ℝ) ^ j) ^ 48 := by
  unfold subseqM; push_cast; rw [subseqN_cast, ← pow_mul]

lemma subseqGrid_mem {T : ℝ} (hT : 0 ≤ T) {j m : ℕ} (hm : m ≤ subseqM j) :
    subseqGrid T j m ∈ Icc 0 T := by
  have hM : (0 : ℝ) < subseqM j := by exact_mod_cast subseqM_pos j
  have hmM : (m : ℝ) ≤ subseqM j := by exact_mod_cast hm
  refine ⟨by unfold subseqGrid; positivity, ?_⟩
  unfold subseqGrid
  rw [mul_div_assoc', div_le_iff₀ hM]
  nlinarith

lemma rate8_le {g K t T : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K) (ht : 0 ≤ t) (htT : t ≤ T) {N : ℕ}
    (hN : 0 < N) :
    (14 * root4 g * (root4 K * (t / (N : ℝ)) * t)) ^ 4 ≤
      14 ^ 4 * g * K * (T ^ 2 / (N : ℝ)) ^ 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc (14 * root4 g * (root4 K * (t / (N : ℝ)) * t)) ^ 4
      = 14 ^ 4 * root4 g ^ 4 * root4 K ^ 4 * (t ^ 2 / (N : ℝ)) ^ 4 := by ring
    _ = 14 ^ 4 * g * K * (t ^ 2 / (N : ℝ)) ^ 4 := by rw [root4_pow_four hg, root4_pow_four hK]
    _ ≤ 14 ^ 4 * g * K * (T ^ 2 / (N : ℝ)) ^ 4 := by gcongr

lemma subseq_sum_bound {c : ℝ} (hc : 0 ≤ c) (j : ℕ) :
    ((subseqM j : ℝ) + 1) * (c * (1 / (subseqN j : ℝ)) ^ 4 / ((1 / 2 : ℝ) ^ j) ^ 8) ≤
      2 * c * (1 / 256 : ℝ) ^ j := by
  rw [subseqM_cast, subseqN_cast]
  set x : ℝ := (2 : ℝ) ^ j with hx
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by linarith
  have e1 : (1 / 2 : ℝ) ^ j = 1 / x := by rw [hx, one_div_pow]
  have e2 : (1 / 256 : ℝ) ^ j = 1 / x ^ 8 := by
    rw [hx, ← pow_mul, show (1 / 256 : ℝ) = (1 / 2) ^ 8 by norm_num, ← pow_mul, one_div_pow,
      mul_comm]
  rw [e1, e2]
  have h48 : 1 ≤ x ^ 48 := one_le_pow₀ hx1
  have hlhs : (x ^ 48 + 1) * (c * (1 / x ^ 16) ^ 4 / (1 / x) ^ 8) =
      c * (x ^ 48 + 1) / x ^ 56 := by
    field_simp
  rw [hlhs, div_le_iff₀ (by positivity)]
  have : 2 * c * (1 / x ^ 8) * x ^ 56 = 2 * c * x ^ 48 := by
    field_simp
  rw [this]
  nlinarith

lemma tendsto_subseqN_mul_mesh {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun j => (subseqN j : ℝ) * (T / (subseqM j : ℝ)) ^ (7 / 20 : ℝ)) atTop (𝓝 0) := by
  have heq : ∀ j, (subseqN j : ℝ) * (T / (subseqM j : ℝ)) ^ (7 / 20 : ℝ) =
      T ^ (7 / 20 : ℝ) * ((2 : ℝ) ^ j) ^ (-(4 / 5 : ℝ)) := by
    intro j
    rw [subseqN_cast, subseqM_cast]
    set x : ℝ := (2 : ℝ) ^ j
    have hx0 : 0 < x := by positivity
    rw [Real.div_rpow hT (by positivity), ← Real.rpow_natCast x 48, ← Real.rpow_mul hx0.le,
      ← Real.rpow_natCast x 16]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, ← Real.rpow_sub hx0]
    norm_num
  simp_rw [heq]
  have hx : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp hx).const_mul
    (T ^ (7 / 20 : ℝ))
  simpa using this

section BorelCantelli

variable (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ} {T K : ℝ}

/-- **Borel–Cantelli on the grids**: eventually in `j`, `|R_{N_j} - I| < 2^{-j}` at every grid
point `m T / M_j`. -/
theorem ae_eventually_subseqGrid_close (hd : 0 < d) (hH : HolderAdapted8 B H T K) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ m ≤ subseqM j,
      |unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω -
        kitItoIntRaw B H (subseqGrid T j m) ω| < (1 / 2 : ℝ) ^ j := by
  set c : ℝ := 14 ^ 4 * gauss8Const * K * (T ^ 2) ^ 4 with hc
  have hc0 : 0 ≤ c := by have := gauss8Const_nonneg; have := hH.K_nonneg; positivity
  set E : ℕ → ℕ → Set Ω := fun j m => {ω | ((1 / 2 : ℝ) ^ j) ^ 8 ≤
    (unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω -
      kitItoIntRaw B H (subseqGrid T j m) ω) ^ 8} with hE
  set s : ℕ → Set Ω := fun j => ⋃ m ∈ Finset.range (subseqM j + 1), E j m with hs
  have hEm : ∀ j m, m ≤ subseqM j →
      P (E j m) ≤ ENNReal.ofReal (c * (1 / (subseqN j : ℝ)) ^ 4 / ((1 / 2 : ℝ) ^ j) ^ 8) := by
    intro j m hm
    have hmem := subseqGrid_mem hT hm
    obtain ⟨hint, hbd⟩ := integral_unifRiemann_sub_kitItoIntRaw_pow_eight_le B hd
      (hH.mono hmem.2) hmem.1 (subseqN_pos j)
    have hε : 0 < ((1 / 2 : ℝ) ^ j) ^ 8 := by positivity
    have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => by positivity) hint
      (((1 / 2 : ℝ) ^ j) ^ 8)
    have hrate := rate8_le gauss8Const_nonneg hH.K_nonneg hmem.1 hmem.2 (subseqN_pos j)
    have hreal : P.real (E j m) ≤ c * (1 / (subseqN j : ℝ)) ^ 4 / ((1 / 2 : ℝ) ^ j) ^ 8 := by
      rw [le_div_iff₀ hε, mul_comm]
      refine hM.trans (hbd.trans (hrate.trans_eq ?_))
      rw [hc]
      ring
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E j m))]
    exact ENNReal.ofReal_le_ofReal hreal
  have hsj : ∀ j, P (s j) ≤ ENNReal.ofReal (2 * c * (1 / 256 : ℝ) ^ j) := by
    intro j
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ m ∈ Finset.range (subseqM j + 1), P (E j m)
        ≤ ∑ _m ∈ Finset.range (subseqM j + 1),
            ENNReal.ofReal (c * (1 / (subseqN j : ℝ)) ^ 4 / ((1 / 2 : ℝ) ^ j) ^ 8) :=
          Finset.sum_le_sum fun m hm =>
            hEm j m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
      _ = ENNReal.ofReal (((subseqM j : ℝ) + 1) *
            (c * (1 / (subseqN j : ℝ)) ^ 4 / ((1 / 2 : ℝ) ^ j) ^ 8)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [ENNReal.ofReal_add (by positivity) zero_le_one]
          simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (subseq_sum_bound hc0 j)
  have hsum : (∑' j, P (s j)) ≠ ⊤ := by
    refine (lt_of_le_of_lt (ENNReal.tsum_le_tsum hsj) ?_).ne
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (2 * c))]
    exact ENNReal.ofReal_lt_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with j hj m hm
  have hnot : ω ∉ E j m := fun h => hj (by
    simp only [hs, Set.mem_iUnion]
    exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), h⟩)
  simp only [hE, Set.mem_ofPred_eq, not_le] at hnot
  by_contra hcon
  push Not at hcon
  have := pow_le_pow_left₀ (by positivity) hcon 8
  rw [Even.pow_abs ⟨4, rfl⟩] at this
  linarith

open scoped NNReal
/-- **Subsequence convergence at every time.** Almost surely, for every `t ∈ [0, T]`,
`R_{N_j}(t) → Ĩ_t` for a continuous version `Ĩ` of the raw Itô integral, provided the
integrand has almost surely `7/20`-Hölder paths. -/
theorem ae_tendsto_subseq_of_continuous_version (hd : 0 < d) (hT : 0 < T)
    (hH : HolderAdapted8 B H T K)
    (hHpath : ∀ᵐ ω ∂P, ∃ L : ℝ, ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T,
      |H s' ω - H s ω| ≤ L * |s' - s| ^ (7 / 20 : ℝ))
    {Y : ℝ≥0 → Ω → ℝ} (hYc : ∀ ω, Continuous fun s => Y s ω)
    (hY : ∀ s : ℝ≥0, (s : ℝ) ≤ T → Y s =ᵐ[P] kitItoIntRaw B H s) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T,
      Tendsto (fun j => unifRiemann B (kitDriver hd) H t (subseqN j) ω) atTop
        (𝓝 (Y (Real.toNNReal t) ω)) := by
  have hgrid : ∀ᵐ ω ∂P, ∀ j m, m ≤ subseqM j →
      Y (Real.toNNReal (subseqGrid T j m)) ω = kitItoIntRaw B H (subseqGrid T j m) ω := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro m
    by_cases hm : m ≤ subseqM j
    · have hmem := subseqGrid_mem hT.le hm
      filter_upwards [hY (Real.toNNReal (subseqGrid T j m))
        (by rw [Real.coe_toNNReal _ hmem.1]; exact hmem.2)] with ω hω _
      rw [hω, Real.coe_toNNReal _ hmem.1]
    · exact ae_of_all _ fun ω h => absurd h hm
  filter_upwards [hgrid, ae_eventually_subseqGrid_close B hd hH hT.le, hHpath,
    ae_holder_wnn B (kitDriver hd) hT.le] with ω hgr hclose hp1 hp2
  obtain ⟨L1, hL1⟩ := hp1
  obtain ⟨L2, hL2⟩ := hp2
  intro t ht
  set γ : ℝ := 7 / 20 with hγ
  set L := max (max L1 L2) 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hf : ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T, |H s' ω - H s ω| ≤ L * |s' - s| ^ γ :=
    fun s hs s' hs' => (hL1 s hs s' hs').trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (Real.rpow_nonneg (abs_nonneg _) _))
  have hg : ∀ s ∈ Icc 0 T, ∀ s' ∈ Icc 0 T,
      |B.Wnn (Real.toNNReal s') ω (kitDriver hd) - B.Wnn (Real.toNNReal s) ω (kitDriver hd)| ≤
        L * |s' - s| ^ γ :=
    fun s hs s' hs' => (hL2 s hs s' hs').trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) (Real.rpow_nonneg (abs_nonneg _) _))
  set G := |H 0 ω| + L * T ^ γ with hGdef
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hG : ∀ s ∈ Icc 0 T, |H s ω| ≤ G := by
    intro s hs
    have e := hf 0 h0mem s hs
    have hs' : |s - 0| ^ γ ≤ T ^ γ := Real.rpow_le_rpow (abs_nonneg _)
      (by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2) (by norm_num)
    have : |H s ω| ≤ |H 0 ω| + |H s ω - H 0 ω| := by
      have := abs_add_le (H 0 ω) (H s ω - H 0 ω)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hs' hL0]
  obtain ⟨εY, hε0, hεlim, hεmod⟩ := exists_modulus_of_continuousOn hT.le
    (f := fun s => Y (Real.toNNReal s) ω) ((hYc ω).comp continuous_real_toNNReal).continuousOn
  set A := L * (L * T ^ γ) + G * (2 * L) with hA
  set δ : ℕ → ℝ := fun j => (subseqN j : ℝ) * (T / (subseqM j : ℝ)) ^ γ * A +
    (1 / 2 : ℝ) ^ j + εY (subseqM j - 1) with hδ
  have hMsub : Tendsto (fun j => subseqM j - 1) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun j hj => ?_⟩
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ subseqN j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : subseqN j ≤ subseqM j := Nat.le_self_pow (by norm_num) _
    omega
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have := (((tendsto_subseqN_mul_mesh hT.le).mul_const A).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num))).add (hεlim.comp hMsub)
    rw [show (0 : ℝ) = 0 * A + 0 + 0 by ring]
    exact this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hδlim
  filter_upwards [hclose] with j hj
  set M := subseqM j with hMdef
  have hMpos : 0 < M := subseqM_pos j
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  set h : ℝ := T / (M : ℝ) with hhdef
  have hh : 0 < h := div_pos hT hMr
  set m := ⌊t / h⌋₊ with hmdef
  have hth : t / h ≤ M := by
    rw [div_le_iff₀ hh, hhdef, mul_div_cancel₀ _ hMr.ne']
    exact ht.2
  have hm : m ≤ M := Nat.floor_le_of_le hth
  have hmem := subseqGrid_mem hT.le hm
  have hgm : subseqGrid T j m = (m : ℝ) * h := rfl
  have hfl1 : (m : ℝ) ≤ t / h := Nat.floor_le (div_nonneg ht.1 hh.le)
  have hfl2 : t / h < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : (m : ℝ) * h ≤ t := by rwa [le_div_iff₀ hh] at hfl1
  have hhi : t < ((m : ℝ) + 1) * h := by rwa [div_lt_iff₀ hh] at hfl2
  have htt : |t - subseqGrid T j m| ≤ h := by
    rw [hgm, abs_of_nonneg (by linarith)]
    nlinarith
  have hT1 := abs_riemannSum_sub_le (f := fun s => H s ω)
    (g := fun s => B.Wnn (Real.toNNReal s) ω (kitDriver hd)) (by norm_num : (0 : ℝ) < γ) hL0
    hf hg hG ht hmem htt (subseqN_pos j)
  have hT1' : |unifRiemann B (kitDriver hd) H t (subseqN j) ω -
      unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω| ≤
      (subseqN j : ℝ) * h ^ γ * A := by
    refine le_of_le_of_eq hT1 ?_
    rw [hA]; ring
  have hT2 := hj m hm
  rw [← hgr j m hm] at hT2
  have hT3 : |Y (Real.toNNReal (subseqGrid T j m)) ω - Y (Real.toNNReal t) ω| ≤
      εY (M - 1) := by
    refine hεmod (M - 1) _ _ hmem ht ?_
    rw [Nat.sub_add_cancel hMpos, abs_sub_comm]
    exact htt
  rw [Real.dist_eq]
  calc |unifRiemann B (kitDriver hd) H t (subseqN j) ω - Y (Real.toNNReal t) ω|
      ≤ |unifRiemann B (kitDriver hd) H t (subseqN j) ω -
            unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω| +
          |unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω -
            Y (Real.toNNReal (subseqGrid T j m)) ω| +
          |Y (Real.toNNReal (subseqGrid T j m)) ω - Y (Real.toNNReal t) ω| := by
        have := abs_sub_le (unifRiemann B (kitDriver hd) H t (subseqN j) ω)
          (unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω)
          (Y (Real.toNNReal t) ω)
        have := abs_sub_le (unifRiemann B (kitDriver hd) H (subseqGrid T j m) (subseqN j) ω)
          (Y (Real.toNNReal (subseqGrid T j m)) ω) (Y (Real.toNNReal t) ω)
        linarith
    _ ≤ δ j := by
        simp only [hδ]
        linarith

end BorelCantelli

end SignatureVolatility

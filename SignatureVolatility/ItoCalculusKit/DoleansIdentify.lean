module

public import SignatureVolatility.ItoCalculusKit.DoleansInputs

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace SignatureVolatility

/-!
# Almost-sure identification of the Itô–Riemann sums of `s₀ Z σ`

For the signature volatility under H1–H3 and `t ∈ [0, T]`, the left Itô–Riemann sums of
`H = s₀ Z σ` on the uniform grids converge almost surely to `s₀ Z_t - s₀`
(`ae_tendsto_unifRiemann_doleans`). Proof: `Z(τᵢ₊₁) = Z(τᵢ) e^{xᵢ}` with
`xᵢ = σ(τᵢ) ΔWᵢ + aᵢ - ½ ∫_{τᵢ}^{τᵢ₊₁} σ²`, telescoping, and `tendsto_doleansError`, whose
hypotheses are supplied by `DoleansInputs`, the grid Doob bound, continuity of `σ` and of the
Brownian path, and almost-sure quadratic variation.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- A uniform modulus of continuity on `[0, t]` along the mesh `t / (n + 1)`. -/
lemma exists_modulus_of_continuousOn {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Set.Icc 0 t)) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n x y, x ∈ Set.Icc 0 t → y ∈ Set.Icc 0 t → |x - y| ≤ t / ((n + 1 : ℕ) : ℝ) →
        |f x - f y| ≤ ε n := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  set S : ℕ → Set ℝ := fun n => {r | ∃ x ∈ Set.Icc 0 t, ∃ y ∈ Set.Icc 0 t,
    |x - y| ≤ t / ((n + 1 : ℕ) : ℝ) ∧ r = |f x - f y|} with hS
  have hbdd : ∀ n, BddAbove (S n) := fun n => ⟨2 * C, by
    rintro r ⟨x, hx, y, hy, -, rfl⟩
    have h1 := hC x hx
    have h2 := hC y hy
    rw [Real.norm_eq_abs] at h1 h2
    calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ 2 * C := by linarith⟩
  have h0t : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht⟩
  have hmem0 : ∀ n, (0 : ℝ) ∈ S n := fun n =>
    ⟨0, h0t, 0, h0t, by simp only [sub_self, abs_zero]; positivity, by simp⟩
  refine ⟨fun n => sSup (S n), fun n => le_csSup (hbdd n) (hmem0 n), ?_,
    fun n x y hx hy hxy => le_csSup (hbdd n) ⟨x, hx, y, hy, hxy, rfl⟩⟩
  rw [Metric.tendsto_atTop]
  intro e he
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff_le.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (e / 2) (half_pos he)
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hmesh : t / ((n + 1 : ℕ) : ℝ) ≤ δ := by
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 : t < N * δ := (div_lt_iff₀ hδ).mp hN
    have h2 : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ_of_le hn
    nlinarith
  have hle : sSup (S n) ≤ e / 2 := by
    refine csSup_le ⟨0, hmem0 n⟩ ?_
    rintro r ⟨x, hx, y, hy, hxy, rfl⟩
    have := hU x hx y hy (by rw [Real.dist_eq]; exact hxy.trans hmesh)
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_csSup (hbdd n) (hmem0 n))]
  linarith

section Identify

variable {T : ℝ} (B : MultiBrownian Ω P d)

/-- **Almost-sure quadratic variation on the uniform grids**: `∑ (ΔWᵢ)² → t`. -/
theorem ae_tendsto_sum_wnnIncr_sq (k : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ range (n + 1),
      wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2) atTop (𝓝 t) := by
  filter_upwards [ae_tendsto_qvBlocks B k ht] with ω hω
  have hf : ∀ n : ℕ, (range (n + 1)).filter (fun j => j * 0 < 1 * (n + 1)) = range (n + 1) :=
    fun n => filter_true_of_mem fun j _ => by omega
  have h : Tendsto (fun n => ∑ j ∈ range (n + 1), qvIncr B k t n j ω) atTop (𝓝 0) :=
    (hω 0 1).congr fun n => by rw [hf n]
  have e : ∀ n j, qvIncr B k t n j ω =
      wnnIncr B k (gridPt t n j) (gridPt t n (j + 1)) ω ^ 2 - t / ((n + 1 : ℕ) : ℝ) := by
    intro n j
    unfold qvIncr gridPt
    push_cast
    ring_nf
  have hsum : ∀ n, ∑ j ∈ range (n + 1), qvIncr B k t n j ω =
      ∑ i ∈ range (n + 1), wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 - t := by
    intro n
    rw [sum_congr rfl fun j _ => e n j, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have h2 := h.add_const t
  rw [zero_add] at h2
  exact h2.congr fun n => by rw [hsum n]; ring

/-- **One grid step of the Doléans exponential** (every `ω`):
`Z(τᵢ₊₁) = Z(τᵢ) exp (σ(τᵢ) ΔWᵢ + aᵢ - ½ ∫_{τᵢ}^{τᵢ₊₁} σ²)`. -/
lemma kitDoleansExp_step (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (h3 : HypH3 P T (signatureSigma B hT ℓ))
    {u v : ℝ} (hu : u ∈ Set.Icc 0 T) (hv : v ∈ Set.Icc 0 T) {ω : Ω}
    (hω : ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Set.Icc 0 T)) :
    kitDoleansExp B (signatureSigma B hT ℓ) v ω =
      kitDoleansExp B (signatureSigma B hT ℓ) u ω *
        Real.exp (signatureSigma B hT ℓ u ω * wnnIncr B (kitDriver hd) u v ω +
          frozenIncr B hd (signatureSigma B hT ℓ) u v ω -
          (∫ s in u..v, signatureSigma B hT ℓ s ω ^ 2) / 2) := by
  have hc := hω.pow 2
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hi1 : IntervalIntegrable (fun s => signatureSigma B hT ℓ s ω ^ 2) MeasureTheory.volume 0 u :=
    (hc.mono (Set.uIcc_subset_Icc h0 hu)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => signatureSigma B hT ℓ s ω ^ 2) MeasureTheory.volume u v :=
    (hc.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  rw [kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 hv hω,
    kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 hu hω, ← Real.exp_add,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  congr 1
  unfold frozenIncr
  ring

lemma kitDoleansExp_signatureSigma_zero (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (h3 : HypH3 P T (signatureSigma B hT ℓ))
    {ω : Ω} (hω : ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Set.Icc 0 T)) :
    kitDoleansExp B (signatureSigma B hT ℓ) 0 ω = 1 := by
  rw [kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 ⟨le_rfl, hT.le⟩ hω, kitItoIntRaw_zero]
  simp

/-- **Almost-sure identification**: the left Itô–Riemann sums of `s₀ Z σ` on the uniform grids
converge to `s₀ Z_t - s₀`. -/
theorem ae_tendsto_unifRiemann_doleans (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (h3 : HypH3 P T (signatureSigma B hT ℓ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (s₀ : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => unifRiemann B (kitDriver hd)
      (fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
        signatureSigma B hT ℓ s ω') t (n + 1) ω) atTop
      (𝓝 (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) t ω - s₀)) := by
  obtain ⟨K, hH⟩ := holderAdapted8_signatureSigma B hT hw hℓ t
  filter_upwards [ae_bdd_kitItoIntRaw_grid B hd hH.toHolderAdapted ht.1,
    ae_tendsto_sum_wnnIncr_sq B (kitDriver hd) ht.1,
    ae_tendsto_sum_frozenIncr_sq B hd hT hw hℓ ht.1,
    ae_tendsto_sum_kitDoleansExp_mul_frozenIncr B hd hT hw hℓ h3 ht,
    ae_tendsto_sum_kitDoleansExp_mul_qvIncrR B hd hT hw hℓ h3 ht,
    ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ] with ω hbdd hW hA h1 h2 hω
  obtain ⟨M, hM⟩ := hbdd
  set σ := signatureSigma B hT ℓ with hσ
  set Z := kitDoleansExp B σ with hZ
  have hcσ : ContinuousOn (fun s => σ s ω) (Set.Icc 0 T) :=
    hω
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hcσ
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0 ⟨le_rfl, hT.le⟩)
  obtain ⟨ε, hε0, hε, hεb⟩ := exists_modulus_of_continuousOn ht.1
    ((hcσ.pow 2).mono (Set.Icc_subset_Icc_right ht.2))
  obtain ⟨β, -, hβ, hβb⟩ := exists_modulus_of_continuousOn ht.1
    (f := fun s => B.Wnn (Real.toNNReal s) ω (kitDriver hd))
    ((B.pathContinuous _ ω).comp continuous_real_toNNReal).continuousOn
  have hgt : ∀ n i, i ≤ n + 1 → gridPt t n i ∈ Set.Icc 0 t := fun n i hi =>
    ⟨gridPt_nonneg ht.1 n i, gridPt_le ht.1 hi⟩
  have hgT : ∀ n i, i ≤ n + 1 → gridPt t n i ∈ Set.Icc 0 T := fun n i hi =>
    ⟨(hgt n i hi).1, (hgt n i hi).2.trans ht.2⟩
  have hstep : ∀ n i, gridPt t n i ≤ gridPt t n (i + 1) := fun n i =>
    gridPt_mono ht.1 n (Nat.le_succ i)
  have hδ0 : ∀ n, 0 ≤ t / ((n + 1 : ℕ) : ℝ) := fun n => by have := ht.1; positivity
  -- bounds on the cell integrals of `σ²`
  have hσsq : ∀ x ∈ Set.Icc 0 T, ‖σ x ω ^ 2‖ ≤ G ^ 2 := fun x hx => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hG x hx) 2
  have hdqle : ∀ n i, i < n + 1 →
      (∫ s in gridPt t n i..gridPt t n (i + 1), σ s ω ^ 2) ≤ G ^ 2 * (t / ((n + 1 : ℕ) : ℝ)) := by
    intro n i hi
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := gridPt t n i) (b := gridPt t n (i + 1)) (C := G ^ 2)
      (f := fun s => σ s ω ^ 2) (fun x hx => by
        rw [Set.uIoc_of_le (hstep n i)] at hx
        exact hσsq x ⟨(hgT n i hi.le).1.trans hx.1.le,
          hx.2.trans (hgT n (i + 1) (Nat.succ_le_of_lt hi)).2⟩)
    rw [gridPt_succ_sub, abs_of_nonneg (hδ0 n)] at hb
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hb)
  have hmain := tendsto_doleansError (M := Real.exp M) (Q := G ^ 2 * t) ht.1 hG0
    (fun n i => Z (gridPt t n i) ω)
    (fun n i => frozenIncr B hd σ (gridPt t n i) (gridPt t n (i + 1)) ω)
    (fun n i => wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω)
    (fun n i => σ (gridPt t n i) ω)
    (fun n i => ∫ s in gridPt t n i..gridPt t n (i + 1), σ s ω ^ 2)
    (ε := ε) (β := β)
    (fun n i hi => by
      refine ⟨(Real.exp_pos _).le, ?_⟩
      have hMi : |kitItoIntRaw B σ (gridPt t n i) ω| ≤ M := hM (n + 1) (Nat.succ_pos n) i hi.le
      simp only [hZ]
      rw [kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 (hgT n i hi.le) hω]
      refine Real.exp_le_exp.mpr ?_
      have hq : 0 ≤ ∫ s in (0 : ℝ)..gridPt t n i, σ s ω ^ 2 :=
        intervalIntegral.integral_nonneg (hgt n i hi.le).1 fun s _ => sq_nonneg _
      have := le_abs_self (kitItoIntRaw B σ (gridPt t n i) ω)
      linarith)
    (fun n i hi => by
      have := hG _ (hgT n i hi.le); rwa [Real.norm_eq_abs] at this)
    (fun n i hi => intervalIntegral.integral_nonneg (hstep n i) fun s _ => sq_nonneg _)
    (fun n => by
      calc ∑ i ∈ range (n + 1), (∫ s in gridPt t n i..gridPt t n (i + 1), σ s ω ^ 2)
          ≤ ∑ _i ∈ range (n + 1), G ^ 2 * (t / ((n + 1 : ℕ) : ℝ)) :=
            sum_le_sum fun i hi => hdqle n i (mem_range.mp hi)
        _ = G ^ 2 * t := by
            rw [sum_const, card_range, nsmul_eq_mul]
            have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp)
    (fun n i hi => by
      have hu := hgT n i hi.le
      have hv := hgT n (i + 1) (Nat.succ_le_of_lt hi)
      have hc := hcσ.pow 2
      have hii : IntervalIntegrable (fun s => σ s ω ^ 2) MeasureTheory.volume
          (gridPt t n i) (gridPt t n (i + 1)) :=
        (hc.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
      have hconst : σ (gridPt t n i) ω ^ 2 * (t / ((n + 1 : ℕ) : ℝ)) =
          ∫ _s in gridPt t n i..gridPt t n (i + 1), σ (gridPt t n i) ω ^ 2 := by
        rw [intervalIntegral.integral_const, gridPt_succ_sub, smul_eq_mul, mul_comm]
      rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const hii]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := gridPt t n i) (b := gridPt t n (i + 1)) (C := ε n)
        (f := fun s => σ (gridPt t n i) ω ^ 2 - σ s ω ^ 2) (fun x hx => by
          rw [Set.uIoc_of_le (hstep n i)] at hx
          rw [Real.norm_eq_abs]
          refine hεb n _ _ (hgt n i hi.le)
            ⟨(hgt n i hi.le).1.trans hx.1.le, hx.2.trans (hgt n (i + 1) (Nat.succ_le_of_lt hi)).2⟩ ?_
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
          have := gridPt_succ_sub t n i
          linarith [hx.2])
      rw [gridPt_succ_sub, abs_of_nonneg (hδ0 n), Real.norm_eq_abs] at hb
      rw [mul_comm]; exact hb)
    hε0 hε
    (fun n i hi => by
      have hu := hgt n i hi.le
      have hv := hgt n (i + 1) (Nat.succ_le_of_lt hi)
      have := hβb n _ _ hv hu (by rw [gridPt_succ_sub, abs_of_nonneg (hδ0 n)])
      exact this)
    hβ hW hA h1
    (h2.congr fun n => sum_congr rfl fun i _ => by
      simp only [qvIncrR, gridPt_succ_sub]; ring)
  -- telescoping
  have hid : ∀ n, unifRiemann B (kitDriver hd) (fun s ω' => (s₀ * Z s ω') * σ s ω') t (n + 1) ω =
      s₀ * Z t ω - s₀ - s₀ * ∑ i ∈ range (n + 1), Z (gridPt t n i) ω *
        (Real.exp (σ (gridPt t n i) ω * wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω +
          frozenIncr B hd σ (gridPt t n i) (gridPt t n (i + 1)) ω -
          (∫ s in gridPt t n i..gridPt t n (i + 1), σ s ω ^ 2) / 2) - 1 -
          σ (gridPt t n i) ω * wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω) := by
    intro n
    have htel : ∑ i ∈ range (n + 1), (Z (gridPt t n (i + 1)) ω - Z (gridPt t n i) ω) =
        Z t ω - 1 := by
      rw [sum_range_sub (fun i => Z (gridPt t n i) ω), gridPt_last]
      have h0 : gridPt t n 0 = 0 := by simp [gridPt]
      rw [h0, show Z 0 ω = 1 from kitDoleansExp_signatureSigma_zero B hd hT hw hℓ h3 hω]
    have hE : ∑ i ∈ range (n + 1), Z (gridPt t n i) ω *
        (Real.exp (σ (gridPt t n i) ω * wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω +
          frozenIncr B hd σ (gridPt t n i) (gridPt t n (i + 1)) ω -
          (∫ s in gridPt t n i..gridPt t n (i + 1), σ s ω ^ 2) / 2) - 1 -
          σ (gridPt t n i) ω * wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω) =
        (Z t ω - 1) - ∑ i ∈ range (n + 1), Z (gridPt t n i) ω * σ (gridPt t n i) ω *
          wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω := by
      rw [← htel, ← sum_sub_distrib]
      refine sum_congr rfl fun i hi => ?_
      rw [show Z (gridPt t n (i + 1)) ω = _ from kitDoleansExp_step B hd hT hw hℓ h3
        (hgT n i (mem_range.mp hi).le) (hgT n (i + 1) (Nat.succ_le_of_lt (mem_range.mp hi))) hω]
      ring
    have hU : unifRiemann B (kitDriver hd) (fun s ω' => (s₀ * Z s ω') * σ s ω') t (n + 1) ω =
        s₀ * ∑ i ∈ range (n + 1), Z (gridPt t n i) ω * σ (gridPt t n i) ω *
          wnnIncr B (kitDriver hd) (gridPt t n i) (gridPt t n (i + 1)) ω := by
      simp only [unifRiemann, mul_sum, gridPt]
      refine sum_congr rfl fun i _ => by ring
    rw [hU, hE]
    ring
  have hlim := tendsto_const_nhds (x := s₀ * Z t ω - s₀) |>.sub (hmain.const_mul s₀)
  rw [mul_zero, sub_zero] at hlim
  exact hlim.congr fun n => (hid n).symm

/-- **The raw Itô limit of `s₀ Z σ` is `s₀ Z_t - s₀` almost surely** (H1–H3, `t ∈ [0, T]`). -/
theorem kitItoIntRaw_doleans_ae (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (h3 : HypH3 P T (signatureSigma B hT ℓ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (s₀ : ℝ) :
    kitItoIntRaw B (fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
        signatureSigma B hT ℓ s ω') t =ᵐ[P]
      fun ω => s₀ * kitDoleansExp B (signatureSigma B hT ℓ) t ω - s₀ := by
  set H : ℝ → Ω → ℝ := fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
    signatureSigma B hT ℓ s ω' with hHdef
  have hmeas : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg t] (H u) := fun u h0 h1 =>
    ((kitDoleansExp_adapted_path B _ t ⟨u, h0, h1⟩).const_mul s₀).mul
      (measurable_signatureSigma_path B hT ℓ t ⟨u, h0, h1⟩)
  have hrawEq : ∀ ω, kitItoIntRaw B H t ω =
      limUnder atTop fun n : ℕ => unifRiemann B (kitDriver hd) H t (n + 1) ω := by
    intro ω
    simp only [kitItoIntRaw, hd, ↓reduceDIte, itoIntegral_process, ht.1]
    congr 1
    funext n
    rw [itoRiemann_process_eq_unifRiemann]
    unfold unifRiemann
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨h0, h1⟩ := unifGrid_mem ht.1 n.succ_pos (Finset.mem_range.mp hi).le
    rw [forceMeasurableProcess_eq_of_adapted B (hmeas _ h0 h1)]
  filter_upwards [ae_tendsto_unifRiemann_doleans B hd hT hw hℓ h3 ht s₀] with ω hω
  rw [hrawEq ω]
  exact hω.limUnder_eq

/-- First half of the integrability gate: the raw Itô limit of `s₀ Z σ` is integrable. -/
theorem integrable_kitItoIntRaw_doleans (hd : 0 < d) (hT : 0 < T) {w : Weight} (hw : HypH2 w)
    {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ) (h3 : HypH3 P T (signatureSigma B hT ℓ))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (s₀ : ℝ) :
    Integrable (kitItoIntRaw B (fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
        signatureSigma B hT ℓ s ω') t) P := by
  have hZ : Integrable (kitDoleansExp B (signatureSigma B hT ℓ) t) P := by
    have := memLp_kitDoleansExp_signatureSigma B hd hT w hw ℓ hℓ h3 ht 1 le_rfl
    exact memLp_one_iff_integrable.mp (by exact_mod_cast this)
  exact ((hZ.const_mul s₀).sub (integrable_const s₀)).congr
    (kitItoIntRaw_doleans_ae B hd hT hw hℓ h3 ht s₀).symm

end Identify

end SignatureVolatility

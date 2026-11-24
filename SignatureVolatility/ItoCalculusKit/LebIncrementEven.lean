module

public import SignatureVolatility.ItoCalculusKit.ItoIncrementEven
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto


@[expose] public section

open MeasureTheory Filter Topology Finset Set
open scoped ENNReal

namespace SignatureVolatility

/-!
# Even-moment bounds for the time integral of a process

For `q ≥ 2` and a process `H` with almost surely continuous paths on `[0, T]` and `H_u ∈ L^{2q}`:
* the uniform-grid `lebIntegral_process H 0 t` equals the pathwise integral `∫₀ᵗ H` a.s.;
* `‖∫₀ᵗ H‖_{2q}² ≤ A t^{e+2} (q e + 1)^{-1/q}` when `‖H_u‖_{2q}² ≤ A u^e`;
* `‖∫ᵤᵛ H‖_{2q}² ≤ M (v - u)²` when `‖H_u‖_{2q}² ≤ M`.
Both bounds come from the discrete Jensen inequality on Riemann sums and Fatou.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Discrete Jensen: `(∑_{j<N} a_j Δ)^{2q} ≤ (N Δ)^{2q-1} ∑_{j<N} a_j^{2q} Δ`. -/
lemma pow_sum_mul_le {q : ℕ} (hq : q ≠ 0) (a : ℕ → ℝ) (N : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (∑ j ∈ range N, a j * Δ) ^ (2 * q) ≤
      ((N : ℝ) * Δ) ^ (2 * q - 1) * ∑ j ∈ range N, a j ^ (2 * q) * Δ := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [zero_pow (by omega : 2 * q ≠ 0)]
  have hJ := pow_sum_div_card_le_sum_pow (s := range N) (f := fun j => |a j|)
    (fun j _ => abs_nonneg _) (2 * q - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * q), card_range,
    div_le_iff₀ (by positivity)] at hJ
  have habs : |∑ j ∈ range N, a j| ≤ ∑ j ∈ range N, |a j| := abs_sum_le_sum_abs _ _
  have e1 : ∑ j ∈ range N, a j * Δ = (∑ j ∈ range N, a j) * Δ := by rw [sum_mul]
  have e2 : ∑ j ∈ range N, a j ^ (2 * q) * Δ = (∑ j ∈ range N, |a j| ^ (2 * q)) * Δ := by
    rw [sum_mul]; congr 1; funext j; rw [hev.pow_abs]
  rw [e1, e2, mul_pow]
  have h1 : (∑ j ∈ range N, a j) ^ (2 * q) ≤ (∑ j ∈ range N, |a j|) ^ (2 * q) := by
    rw [← hev.pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs _
  have hΔq : Δ ^ (2 * q) = Δ ^ (2 * q - 1) * Δ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * q)]
  calc (∑ j ∈ range N, a j) ^ (2 * q) * Δ ^ (2 * q)
      ≤ ((∑ j ∈ range N, |a j| ^ (2 * q)) * (N : ℝ) ^ (2 * q - 1)) * Δ ^ (2 * q) := by
        gcongr; exact h1.trans hJ
    _ = ((N : ℝ) * Δ) ^ (2 * q - 1) * ((∑ j ∈ range N, |a j| ^ (2 * q)) * Δ) := by
        rw [hΔq, mul_pow]; ring

/-- Moment of a Riemann sum of `L^{2q}` variables. -/
lemma integral_riemannSum_pow_le {q : ℕ} (hq : q ≠ 0) {H : ℝ → Ω → ℝ} (p : ℕ → ℝ) (N : ℕ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hLp : ∀ j < N, MemLp (H (p j)) (2 * q : ℕ) P) :
    MemLp (fun ω => ∑ j ∈ range N, H (p j) ω * Δ) (2 * q : ℕ) P ∧
    ∫ ω, (∑ j ∈ range N, H (p j) ω * Δ) ^ (2 * q) ∂P ≤
      ((N : ℝ) * Δ) ^ (2 * q - 1) * ∑ j ∈ range N, (∫ ω, H (p j) ω ^ (2 * q) ∂P) * Δ := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hS : MemLp (fun ω => ∑ j ∈ range N, H (p j) ω * Δ) (2 * q : ℕ) P := by
    have h := memLp_finsetSum' (p := ((2 * q : ℕ) : ℝ≥0∞)) (μ := P) (range N)
      (f := fun j ω => H (p j) ω * Δ) fun j hj => (hLp j (mem_range.mp hj)).mul_const Δ
    have hfun : (∑ j ∈ range N, fun ω => H (p j) ω * Δ) =
        fun ω => ∑ j ∈ range N, H (p j) ω * Δ := by funext ω; simp
    rwa [hfun] at h
  refine ⟨hS, ?_⟩
  have hi : ∀ j ∈ range N, Integrable (fun ω => H (p j) ω ^ (2 * q) * Δ) P := fun j hj =>
    (integrable_pow_of_memLp_evenDeg hev (hLp j (mem_range.mp hj))).mul_const Δ
  calc ∫ ω, (∑ j ∈ range N, H (p j) ω * Δ) ^ (2 * q) ∂P
      ≤ ∫ ω, ((N : ℝ) * Δ) ^ (2 * q - 1) * ∑ j ∈ range N, H (p j) ω ^ (2 * q) * Δ ∂P :=
        integral_mono (integrable_pow_of_memLp_evenDeg hev hS)
          ((integrable_finsetSum _ hi).const_mul _)
          fun ω => pow_sum_mul_le hq (fun j => H (p j) ω) N hΔ
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ hi]
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [integral_mul_const]

section Leb

variable {q : ℕ} {H : ℝ → Ω → ℝ} {T : ℝ}

omit [MeasurableSpace Ω] in
/-- Riemann sums of a shifted window converge to the pathwise integral over `[u, v]`. -/
lemma tendsto_shiftRiemann {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) {ω : Ω}
    (hω : ContinuousOn (fun s => H s ω) (Icc 0 T)) :
    Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1),
      H (u + (j : ℝ) * ((v - u) / ((n : ℝ) + 1))) ω * ((v - u) / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ s in u..v, H s ω)) := by
  have hc : ContinuousOn (fun s => H (u + s) ω) (Icc 0 (v - u)) := by
    refine hω.comp (continuousOn_const.add continuousOn_id) fun s hs => ?_
    simp only [Set.mem_Icc] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  have h := tendsto_lebRiemann_of_continuousOn (sub_nonneg.mpr huv) hc
  rw [intervalIntegral.integral_comp_add_left (fun s => H s ω) u] at h
  simpa only [add_zero, add_sub_cancel] using h

omit [MeasurableSpace Ω] in
lemma lebIntegral_process_eq_integral {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {ω : Ω}
    (hω : ContinuousOn (fun s => H s ω) (Icc 0 T)) :
    lebIntegral_process H 0 t ω = ∫ s in (0 : ℝ)..t, H s ω := by
  have h := tendsto_shiftRiemann (H := H) le_rfl ht htT hω
  simp only [lebIntegral_process, ht, ↓reduceDIte]
  have e : (fun n : ℕ => lebRiemann_process H 0 t n ω) = fun n : ℕ => ∑ j ∈ range (n + 1),
      H (0 + (j : ℝ) * ((t - 0) / ((n : ℝ) + 1))) ω * ((t - 0) / ((n : ℝ) + 1)) := by
    funext n; simp [lebRiemann_process]
  rw [e, h.limUnder_eq]

/-- Core Fatou step on a window `[u, v]`. -/
lemma nrm_integral_window_le (hq : q ≠ 0)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => H s ω) (Icc 0 T))
    (hLp : ∀ u, 0 ≤ u → u ≤ T → MemLp (H u) (2 * q : ℕ) P) {u v c : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvT : v ≤ T)
    (hb : ∀ n : ℕ, ((v - u)) ^ (2 * q - 1) * ∑ j ∈ range (n + 1),
      (∫ ω, H (u + (j : ℝ) * ((v - u) / ((n : ℝ) + 1))) ω ^ (2 * q) ∂P) *
        ((v - u) / ((n : ℝ) + 1)) ≤ c ^ q) (hc : 0 ≤ c) :
    MemLp (fun ω => ∫ s in u..v, H s ω) (2 * q : ℕ) P ∧
      nrm q (∫ ω, (∫ s in u..v, H s ω) ^ (2 * q) ∂P) ≤ c := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  set Δ : ℕ → ℝ := fun n => (v - u) / ((n : ℝ) + 1)
  have hΔ : ∀ n, 0 ≤ Δ n := fun n => div_nonneg (sub_nonneg.mpr huv) (by positivity)
  have hpt : ∀ n j : ℕ, j < n + 1 → 0 ≤ u + (j : ℝ) * Δ n ∧ u + (j : ℝ) * Δ n ≤ T := by
    intro n j hj
    refine ⟨by have := hΔ n; positivity, ?_⟩
    have h1 : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj.le
    have h2 : (j : ℝ) * Δ n ≤ ((n : ℝ) + 1) * Δ n := mul_le_mul_of_nonneg_right h1 (hΔ n)
    have h3 : ((n : ℝ) + 1) * Δ n = v - u := by simp only [Δ]; field_simp
    linarith
  set f : ℕ → Ω → ℝ := fun n ω => ∑ j ∈ range (n + 1), H (u + (j : ℝ) * Δ n) ω * Δ n
  have hf : ∀ n, MemLp (f n) (2 * q : ℕ) P ∧ ∫ ω, f n ω ^ (2 * q) ∂P ≤ c ^ q := by
    intro n
    obtain ⟨h1, h2⟩ := integral_riemannSum_pow_le hq (H := H) (fun j => u + (j : ℝ) * Δ n)
      (n + 1) (hΔ n) fun j hj => hLp _ (hpt n j hj).1 (hpt n j hj).2
    refine ⟨h1, h2.trans (le_of_eq_of_le ?_ (hb n))⟩
    have : ((n + 1 : ℕ) : ℝ) * Δ n = v - u := by simp only [Δ]; push_cast; field_simp
    rw [this]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (∫ s in u..v, H s ω)) := by
    filter_upwards [hcont] with ω hω
    exact tendsto_shiftRiemann hu huv hvT hω
  have hg : AEStronglyMeasurable (fun ω => ∫ s in u..v, H s ω) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).1.aestronglyMeasurable) hlim
  refine nrm_le_of_tendsto hq hg (fun n => (hf n).1) hlim (b := fun _ => c) (fun n => ?_)
    tendsto_const_nhds
  have h0 : 0 ≤ ∫ ω, f n ω ^ (2 * q) ∂P := integral_nonneg fun ω => hev.pow_nonneg _
  exact nrm_le_of_le_pow hq h0 hc (hf n).2

/-- **`L^{2q}` moment of the time integral** with a power profile. -/
theorem nrm_integral_time_le (hq : 2 ≤ q)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => H s ω) (Icc 0 T))
    (hLp : ∀ u, 0 ≤ u → u ≤ T → MemLp (H u) (2 * q : ℕ) P) {A : ℝ} {e : ℕ} (hA : 0 ≤ A)
    (hmom : ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ A * u ^ e) {t : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    MemLp (fun ω => ∫ s in (0 : ℝ)..t, H s ω) (2 * q : ℕ) P ∧
      nrm q (∫ ω, (∫ s in (0 : ℝ)..t, H s ω) ^ (2 * q) ∂P) ≤
        A * t ^ (e + 2) * nrm q (1 / ((q * e : ℕ) + 1 : ℝ)) := by
  have hq0 : q ≠ 0 := by omega
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hD : (0 : ℝ) < (q * e : ℕ) + 1 := by positivity
  have hc : 0 ≤ A * t ^ (e + 2) * nrm q (1 / ((q * e : ℕ) + 1 : ℝ)) :=
    mul_nonneg (by positivity) (nrm_nonneg q (by positivity))
  refine nrm_integral_window_le hq0 hcont hLp le_rfl ht htT (fun n => ?_) hc
  set Δ := (t - 0) / ((n : ℝ) + 1) with hΔdef
  have hΔ : 0 ≤ Δ := div_nonneg (by linarith) (by positivity)
  have hterm : ∀ j ∈ range (n + 1), (∫ ω, H (0 + (j : ℝ) * Δ) ω ^ (2 * q) ∂P) * Δ ≤
      A ^ q * (((j : ℝ) * Δ) ^ (q * e) * Δ) := by
    intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (mem_range.mp hj).le
    have hp0 : 0 ≤ (j : ℝ) * Δ := by positivity
    have hpT : (j : ℝ) * Δ ≤ T := by
      have : ((n : ℝ) + 1) * Δ = t := by rw [hΔdef]; field_simp; ring
      nlinarith
    rw [zero_add]
    have h0 : 0 ≤ ∫ ω, H ((j : ℝ) * Δ) ω ^ (2 * q) ∂P := integral_nonneg fun ω => hev.pow_nonneg _
    have h1 : ∫ ω, H ((j : ℝ) * Δ) ω ^ (2 * q) ∂P ≤ (A * ((j : ℝ) * Δ) ^ e) ^ q := by
      rw [← nrm_pow hq0 h0]
      exact pow_le_pow_left₀ (nrm_nonneg q h0) (hmom _ hp0 hpT) q
    calc (∫ ω, H ((j : ℝ) * Δ) ω ^ (2 * q) ∂P) * Δ ≤ (A * ((j : ℝ) * Δ) ^ e) ^ q * Δ :=
          mul_le_mul_of_nonneg_right h1 hΔ
      _ = A ^ q * (((j : ℝ) * Δ) ^ (q * e) * Δ) := by rw [mul_pow, ← pow_mul, mul_comm e q]; ring
  have hsum := (sum_le_sum hterm).trans (le_of_eq (mul_sum _ _ _).symm)
  have hgrid := sum_grid_pow_le (q * e) (n + 1) hΔ
  have hNΔ : ((n + 1 : ℕ) : ℝ) * Δ = t := by rw [hΔdef]; push_cast; field_simp; ring
  rw [hNΔ] at hgrid
  have hAq : 0 ≤ A ^ q := by positivity
  have htq : 0 ≤ (t - 0) ^ (2 * q - 1) := by rw [sub_zero]; positivity
  calc (t - 0) ^ (2 * q - 1) * ∑ j ∈ range (n + 1),
        (∫ ω, H (0 + (j : ℝ) * Δ) ω ^ (2 * q) ∂P) * Δ
      ≤ (t - 0) ^ (2 * q - 1) * (A ^ q * (t ^ (q * e + 1) / ((q * e : ℕ) + 1))) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans ?_) htq
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hgrid) hAq
    _ = (A * t ^ (e + 2) * nrm q (1 / ((q * e : ℕ) + 1 : ℝ))) ^ q := by
        rw [mul_pow, nrm_pow hq0 (by positivity), sub_zero, mul_pow, ← pow_mul]
        have e1 : (e + 2) * q = (2 * q - 1) + (q * e + 1) := by
          zify [show 1 ≤ 2 * q by omega]; ring
        rw [e1]
        field_simp
        rw [pow_add, pow_succ]; ring

/-- **`L^{2q}` increments of the time integral.** -/
theorem nrm_integral_time_sub_le (hq : 2 ≤ q)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => H s ω) (Icc 0 T))
    (hLp : ∀ u, 0 ≤ u → u ≤ T → MemLp (H u) (2 * q : ℕ) P) {M : ℝ}
    (hM : ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ M) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvT : v ≤ T) :
    MemLp (fun ω => ∫ s in u..v, H s ω) (2 * q : ℕ) P ∧
      nrm q (∫ ω, (∫ s in u..v, H s ω) ^ (2 * q) ∂P) ≤ M * (v - u) ^ 2 := by
  have hq0 : q ≠ 0 := by omega
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hM0 : 0 ≤ M := (nrm_nonneg q (integral_nonneg fun ω => hev.pow_nonneg _)).trans
    (hM 0 le_rfl ((hu.trans huv).trans hvT))
  have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
  refine nrm_integral_window_le hq0 hcont hLp hu huv hvT (fun n => ?_) (by positivity)
  set Δ := (v - u) / ((n : ℝ) + 1) with hΔdef
  have hΔ : 0 ≤ Δ := div_nonneg hvu (by positivity)
  have hterm : ∀ j ∈ range (n + 1), (∫ ω, H (u + (j : ℝ) * Δ) ω ^ (2 * q) ∂P) * Δ ≤
      M ^ q * Δ := by
    intro j hj
    have hj' : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (mem_range.mp hj).le
    have hp0 : 0 ≤ u + (j : ℝ) * Δ := by positivity
    have hpT : u + (j : ℝ) * Δ ≤ T := by
      have : ((n : ℝ) + 1) * Δ = v - u := by rw [hΔdef]; field_simp
      nlinarith
    have h0 : 0 ≤ ∫ ω, H (u + (j : ℝ) * Δ) ω ^ (2 * q) ∂P :=
      integral_nonneg fun ω => hev.pow_nonneg _
    have h1 : ∫ ω, H (u + (j : ℝ) * Δ) ω ^ (2 * q) ∂P ≤ M ^ q := by
      rw [← nrm_pow hq0 h0]
      exact pow_le_pow_left₀ (nrm_nonneg q h0) (hM _ hp0 hpT) q
    exact mul_le_mul_of_nonneg_right h1 hΔ
  have hsum := sum_le_sum hterm
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hNΔ : ((n + 1 : ℕ) : ℝ) * Δ = v - u := by rw [hΔdef]; push_cast; field_simp
  calc (v - u) ^ (2 * q - 1) * ∑ j ∈ range (n + 1),
        (∫ ω, H (u + (j : ℝ) * Δ) ω ^ (2 * q) ∂P) * Δ
      ≤ (v - u) ^ (2 * q - 1) * (((n + 1 : ℕ) : ℝ) * (M ^ q * Δ)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (M * (v - u) ^ 2) ^ q := by
        rw [show ((n + 1 : ℕ) : ℝ) * (M ^ q * Δ) = M ^ q * (((n + 1 : ℕ) : ℝ) * Δ) by ring, hNΔ,
          mul_pow, ← pow_mul]
        have h2 : (v - u) ^ (2 * q) = (v - u) ^ (2 * q - 1) * (v - u) := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * q)]
        rw [h2]; ring

end Leb

end SignatureVolatility

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


@[expose] public section

open MeasureTheory Filter Topology Finset Set

namespace SignatureVolatility

/-!
# Pathwise (Föllmer) Itô calculus for the exponential along uniform grids

Deterministic statements about a single continuous path `x` on `[0, t]` and the uniform grids
`s_j = j · t/(n+1)`:

* `tendsto_lebRiemann_of_continuousOn`: left Riemann sums of a continuous function converge to
  its integral;
* `tendsto_weighted_qv`: if the centred squared increments sum to `o(1)` on every rational block
  (the Föllmer quadratic-variation hypothesis), then they do so against any continuous weight;
* `tendsto_expRiemann`: under the same hypothesis the left Itô–Riemann sums of
  `Z_s = exp (c x_s - c² s / 2)` against `c · dx` converge to `Z_t - Z_0` (Itô's formula for the
  Doléans exponential, pathwise).
-/

/-! ## Riemann sums of continuous functions -/

/-- Left Riemann sums on the uniform grid converge to the integral. -/
theorem tendsto_lebRiemann_of_continuousOn {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 t)) :
    Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1),
      g ((j : ℝ) * (t / ((n : ℝ) + 1))) * (t / ((n : ℝ) + 1)))
      atTop (𝓝 (∫ s in (0 : ℝ)..t, g s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hδg⟩ := huc (ε / (2 * (t + 1))) (by positivity)
  have hlim : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (ge_mem_nhds hδ)] with n hn
  set Δ : ℝ := t / ((n : ℝ) + 1) with hΔdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hΔ0 : 0 ≤ Δ := div_nonneg ht hn1.le
  have hNΔ : ((n : ℝ) + 1) * Δ = t := by rw [hΔdef]; field_simp
  have hgrid : ∀ j : ℕ, j ≤ n + 1 → (j : ℝ) * Δ ∈ Icc 0 t := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    calc (j : ℝ) * Δ ≤ ((n : ℝ) + 1) * Δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hΔ0
      _ = t := hNΔ
  have hsub : ∀ j : ℕ, j < n + 1 → Icc ((j : ℝ) * Δ) (((j : ℝ) + 1) * Δ) ⊆ Icc 0 t := by
    intro j hj s hs
    have h1 := (hgrid j hj.le).1
    have h2 := (hgrid (j + 1) hj).2
    push_cast at h2
    exact ⟨h1.trans hs.1, hs.2.trans h2⟩
  have hle : ∀ j : ℕ, (j : ℝ) * Δ ≤ ((j : ℝ) + 1) * Δ := fun j =>
    mul_le_mul_of_nonneg_right (by linarith) hΔ0
  have hint : ∀ j : ℕ, j < n + 1 →
      IntervalIntegrable g volume ((j : ℝ) * Δ) (((j : ℝ) + 1) * Δ) := fun j hj =>
    (hg.mono (hsub j hj)).intervalIntegrable_of_Icc (hle j)
  have hsum : ∫ s in (0 : ℝ)..t, g s =
      ∑ j ∈ range (n + 1), ∫ s in ((j : ℝ) * Δ)..(((j : ℝ) + 1) * Δ), g s := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
      (a := fun j : ℕ => (j : ℝ) * Δ) (n := n + 1)
      (fun j hj => by simpa using hint j hj)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at h
    rw [h, hNΔ]
  rw [Real.dist_eq, hsum, ← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ range (n + 1),
      |g ((j : ℝ) * Δ) * Δ - ∫ s in ((j : ℝ) * Δ)..(((j : ℝ) + 1) * Δ), g s| ≤
        ε / (2 * (t + 1)) * Δ := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hconst : g ((j : ℝ) * Δ) * Δ =
        ∫ _s in ((j : ℝ) * Δ)..(((j : ℝ) + 1) * Δ), g ((j : ℝ) * Δ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint j hj')]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (j : ℝ) * Δ) (b := ((j : ℝ) + 1) * Δ) (C := ε / (2 * (t + 1)))
      (f := fun s => g ((j : ℝ) * Δ) - g s) (fun s hs => by
        rw [uIoc_of_le (hle j)] at hs
        have hsI : s ∈ Icc ((j : ℝ) * Δ) (((j : ℝ) + 1) * Δ) := ⟨hs.1.le, hs.2⟩
        have hd : dist ((j : ℝ) * Δ) s ≤ δ := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
          have : s - (j : ℝ) * Δ ≤ Δ := by linarith [hs.2]
          exact this.trans hn
        exact hδg _ (hgrid j hj'.le) _ (hsub j hj' hsI) hd)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq ?_)
    rw [abs_of_nonneg (by linarith [hle j])]
    ring
  calc |∑ j ∈ range (n + 1), (g ((j : ℝ) * Δ) * Δ -
          ∫ s in ((j : ℝ) * Δ)..(((j : ℝ) + 1) * Δ), g s)|
      ≤ ∑ j ∈ range (n + 1), |g ((j : ℝ) * Δ) * Δ -
          ∫ s in ((j : ℝ) * Δ)..(((j : ℝ) + 1) * Δ), g s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range (n + 1), ε / (2 * (t + 1)) * Δ := Finset.sum_le_sum hterm
    _ = ε / (2 * (t + 1)) * t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        rw [← hNΔ]
        ring
    _ < ε := by
        have h2 : ε / (2 * (t + 1)) * t = ε * (t / (2 * (t + 1))) := by ring
        have h3 : t / (2 * (t + 1)) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        rw [h2]
        exact mul_lt_of_lt_one_right hε h3

/-! ## Weighted quadratic variation -/

/-- **Föllmer's weighted quadratic variation.** `q n j ≥ 0` plays the role of the squared
increment `(x_{s_{j+1}} - x_{s_j})²` on the `n`-th uniform grid. If the centred sums vanish on
every rational block, then they vanish against every continuous weight. -/
theorem tendsto_weighted_qv {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 t))
    (q : ℕ → ℕ → ℝ) (hq : ∀ n j, 0 ≤ q n j)
    (hqv : ∀ K i : ℕ, Tendsto (fun n =>
      ∑ j ∈ (range (n + 1)).filter (fun j => j * K < i * (n + 1)),
        (q n j - t / ((n : ℝ) + 1))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1),
      g ((j : ℝ) * (t / ((n : ℝ) + 1))) * (q n j - t / ((n : ℝ) + 1))) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- total variation of the centred increments is eventually bounded
  have htot : Tendsto (fun n => ∑ j ∈ range (n + 1), (q n j - t / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    refine (hqv 1 1).congr fun n => ?_
    refine Finset.sum_congr (Finset.filter_true_of_mem fun j hj => ?_) fun _ _ => rfl
    simpa using Finset.mem_range.mp hj
  have hT : ∀ᶠ n : ℕ in atTop,
      ∑ j ∈ range (n + 1), |q n j - t / ((n : ℝ) + 1)| ≤ 2 * t + 1 := by
    filter_upwards [(Metric.tendsto_nhds.mp htot) 1 one_pos] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hΔ0 : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht hn1.le
    calc ∑ j ∈ range (n + 1), |q n j - t / ((n : ℝ) + 1)|
        ≤ ∑ j ∈ range (n + 1), ((q n j - t / ((n : ℝ) + 1)) + 2 * (t / ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_le]
          constructor <;> linarith [hq n j]
      _ = ∑ j ∈ range (n + 1), (q n j - t / ((n : ℝ) + 1)) + 2 * t := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          congr 1
          push_cast
          field_simp
      _ ≤ 2 * t + 1 := by linarith [(abs_lt.mp hn).2]
  -- uniform continuity of the weight
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hδg⟩ := huc (ε / (4 * (2 * t + 1))) (by positivity)
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (t / δ)
  set K : ℕ := K₀ + 1 with hKdef
  have hKpos : 0 < K := Nat.succ_pos _
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hKδ : t / (K : ℝ) ≤ δ := by
    rw [div_le_iff₀ hKr]
    have h1 : t < (K₀ : ℝ) * δ := by rwa [div_lt_iff₀ hδ] at hK₀
    have h2 : (K₀ : ℝ) * δ ≤ (K : ℝ) * δ := by
      rw [hKdef]; push_cast; nlinarith
    linarith
  -- the step-function part tends to zero
  have hstep : Tendsto (fun n : ℕ => ∑ i ∈ range K, g ((i : ℝ) * (t / (K : ℝ))) *
      ((∑ j ∈ (range (n + 1)).filter (fun j => j * K < (i + 1) * (n + 1)),
          (q n j - t / ((n : ℝ) + 1))) -
        ∑ j ∈ (range (n + 1)).filter (fun j => j * K < i * (n + 1)),
          (q n j - t / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (range K) fun i _ =>
      (tendsto_const_nhds (x := g ((i : ℝ) * (t / (K : ℝ))))).mul
        ((hqv K (i + 1)).sub (hqv K i))
    simpa using h
  filter_upwards [hT, (Metric.tendsto_nhds.mp hstep) (ε / 2) (by positivity)] with n hTn hSn
  rw [Real.dist_eq, sub_zero] at hSn ⊢
  set Δ : ℝ := t / ((n : ℝ) + 1) with hΔdef
  set N : ℕ := n + 1 with hNdef
  have hNpos : 0 < N := Nat.succ_pos _
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNcast : (N : ℝ) = (n : ℝ) + 1 := by rw [hNdef]; push_cast; ring
  have hΔN : Δ = t / (N : ℝ) := by rw [hΔdef, hNcast]
  -- block index of grid point `j`
  have hdiv : ∀ j i : ℕ, j * K / N = i ↔ i * N ≤ j * K ∧ j * K < (i + 1) * N := by
    intro j i
    rw [Nat.le_antisymm_iff, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hNpos,
      Nat.le_div_iff_mul_le hNpos, and_comm]
  have hblock : ∀ i : ℕ,
      ∑ j ∈ (range N).filter (fun j => j * K / N = i), (q n j - Δ) =
        (∑ j ∈ (range N).filter (fun j => j * K < (i + 1) * N), (q n j - Δ)) -
          ∑ j ∈ (range N).filter (fun j => j * K < i * N), (q n j - Δ) := by
    intro i
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : i * N ≤ (i + 1) * N := Nat.mul_le_mul_right _ (Nat.le_succ _)
    by_cases h1 : j * K < i * N
    · have h2 : j * K < (i + 1) * N := lt_of_lt_of_le h1 hlt
      have h3 : ¬ j * K / N = i := by
        rw [hdiv]; exact fun h => absurd h.1 (not_le.mpr h1)
      simp [h1, h2, h3]
    · by_cases h2 : j * K < (i + 1) * N
      · have h3 : j * K / N = i := (hdiv j i).mpr ⟨not_lt.mp h1, h2⟩
        simp [h1, h2, h3]
      · have h3 : ¬ j * K / N = i := by
          rw [hdiv]; exact fun h => h2 h.2
        simp [h1, h2, h3]
  have hmaps : ∀ j ∈ range N, j * K / N ∈ range K := by
    intro j hj
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hNpos]
    exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hj) hKpos |>.trans_eq (Nat.mul_comm _ _)
  have hsplit : ∑ j ∈ range N, g ((j : ℝ) * Δ) * (q n j - Δ) =
      ∑ j ∈ range N, (g ((j : ℝ) * Δ) - g (((j * K / N : ℕ) : ℝ) * (t / (K : ℝ)))) * (q n j - Δ) +
        ∑ i ∈ range K, g ((i : ℝ) * (t / (K : ℝ))) *
          ((∑ j ∈ (range N).filter (fun j => j * K < (i + 1) * N), (q n j - Δ)) -
            ∑ j ∈ (range N).filter (fun j => j * K < i * N), (q n j - Δ)) := by
    have hfib : ∑ i ∈ range K, g ((i : ℝ) * (t / (K : ℝ))) *
          ((∑ j ∈ (range N).filter (fun j => j * K < (i + 1) * N), (q n j - Δ)) -
            ∑ j ∈ (range N).filter (fun j => j * K < i * N), (q n j - Δ)) =
        ∑ j ∈ range N, g (((j * K / N : ℕ) : ℝ) * (t / (K : ℝ))) * (q n j - Δ) := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hblock i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.mp hj).2]
    rw [hfib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- the oscillation part is small
  have hosc : |∑ j ∈ range N,
      (g ((j : ℝ) * Δ) - g (((j * K / N : ℕ) : ℝ) * (t / (K : ℝ)))) * (q n j - Δ)| ≤
        ε / (4 * (2 * t + 1)) * (2 * t + 1) := by
    calc |∑ j ∈ range N,
          (g ((j : ℝ) * Δ) - g (((j * K / N : ℕ) : ℝ) * (t / (K : ℝ)))) * (q n j - Δ)|
        ≤ ∑ j ∈ range N,
          |(g ((j : ℝ) * Δ) - g (((j * K / N : ℕ) : ℝ) * (t / (K : ℝ)))) * (q n j - Δ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range N, ε / (4 * (2 * t + 1)) * |q n j - Δ| := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have hjN : j < N := Finset.mem_range.mp hj
          set i : ℕ := j * K / N with hi
          obtain ⟨hi1, hi2⟩ := (hdiv j i).mp rfl
          have hiK : i < K := Finset.mem_range.mp (hmaps j hj)
          have hi1r : (i : ℝ) * (N : ℝ) ≤ (j : ℝ) * (K : ℝ) := by exact_mod_cast hi1
          have hi2r : (j : ℝ) * (K : ℝ) < ((i : ℝ) + 1) * (N : ℝ) := by exact_mod_cast hi2
          have hjNr : (j : ℝ) < (N : ℝ) := by exact_mod_cast hjN
          have hiKr : (i : ℝ) < (K : ℝ) := by exact_mod_cast hiK
          -- both points lie in `[0, t]` and are `t / K`-close
          have e1 : (j : ℝ) * Δ = t * ((j : ℝ) / (N : ℝ)) := by rw [hΔN]; ring
          have e2 : (i : ℝ) * (t / (K : ℝ)) = t * ((i : ℝ) / (K : ℝ)) := by ring
          have f1 : (i : ℝ) / (K : ℝ) ≤ (j : ℝ) / (N : ℝ) := by
            rw [div_le_div_iff₀ hKr hNr]; exact hi1r
          have f2 : (j : ℝ) / (N : ℝ) ≤ ((i : ℝ) + 1) / (K : ℝ) := by
            rw [div_le_div_iff₀ hNr hKr]; exact hi2r.le
          have f3 : (j : ℝ) / (N : ℝ) ≤ 1 := by
            rw [div_le_one hNr]; exact hjNr.le
          have f4 : (i : ℝ) / (K : ℝ) ≤ 1 := by
            rw [div_le_one hKr]; exact hiKr.le
          have f0 : 0 ≤ (i : ℝ) / (K : ℝ) := by positivity
          have m1 : (j : ℝ) * Δ ∈ Icc 0 t := by
            rw [e1]
            exact ⟨mul_nonneg ht (f0.trans f1), mul_le_of_le_one_right ht f3⟩
          have m2 : (i : ℝ) * (t / (K : ℝ)) ∈ Icc 0 t := by
            rw [e2]
            exact ⟨mul_nonneg ht f0, mul_le_of_le_one_right ht f4⟩
          have hd : dist ((j : ℝ) * Δ) ((i : ℝ) * (t / (K : ℝ))) ≤ δ := by
            rw [Real.dist_eq, e1, e2, ← mul_sub, abs_of_nonneg (mul_nonneg ht (sub_nonneg.mpr f1))]
            refine le_trans ?_ hKδ
            have : (j : ℝ) / (N : ℝ) - (i : ℝ) / (K : ℝ) ≤ 1 / (K : ℝ) := by
              have : ((i : ℝ) + 1) / (K : ℝ) = (i : ℝ) / (K : ℝ) + 1 / (K : ℝ) := by ring
              linarith
            calc t * ((j : ℝ) / (N : ℝ) - (i : ℝ) / (K : ℝ)) ≤ t * (1 / (K : ℝ)) :=
                  mul_le_mul_of_nonneg_left this ht
              _ = t / (K : ℝ) := by ring
          have := hδg _ m1 _ m2 hd
          rwa [Real.dist_eq] at this
      _ = ε / (4 * (2 * t + 1)) * ∑ j ∈ range N, |q n j - Δ| := by rw [Finset.mul_sum]
      _ ≤ ε / (4 * (2 * t + 1)) * (2 * t + 1) :=
          mul_le_mul_of_nonneg_left hTn (by positivity)
  have hε4 : ε / (4 * (2 * t + 1)) * (2 * t + 1) = ε / 4 := by
    field_simp
  rw [hsplit]
  calc |_ + _| ≤ _ := abs_add_le _ _
    _ < ε := by linarith [hosc, hSn]

/-! ## The exponential -/

/-- Second-order Taylor bound for the Doléans increment: with `u = c·Δx` and `a = c²Δ/2`,
`exp (u - a) = 1 + u + (u²/2 - a) + O(θ (u² + a))`. -/
lemma abs_exp_sub_taylor_le {u a θ : ℝ} (hu : |u| ≤ θ) (ha0 : 0 ≤ a) (ha : a ≤ θ)
    (hθ : θ ≤ 1 / 2) :
    |Real.exp (u - a) - 1 - u - u ^ 2 / 2 + a| ≤ 4 * θ * (u ^ 2 + a) := by
  have hθ0 : 0 ≤ θ := (abs_nonneg u).trans hu
  have hδ : |u - a| ≤ 2 * θ := by
    calc |u - a| ≤ |u| + |a| := abs_sub _ _
      _ ≤ θ + θ := add_le_add hu (by rwa [abs_of_nonneg ha0])
      _ = 2 * θ := by ring
  have hδ1 : |u - a| ≤ 1 := hδ.trans (by linarith)
  have hb := Real.exp_bound hδ1 (n := 3) (by norm_num)
  have hsum : ∑ m ∈ range 3, (u - a) ^ m / (m.factorial : ℝ) =
      1 + (u - a) + (u - a) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have h3 : |u - a| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ))) ≤
      2 * θ * (u - a) ^ 2 := by
    have e : (((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ))) = 2 / 9 := by
      norm_num [Nat.factorial]
    rw [e]
    have hsq : |u - a| ^ 3 = |u - a| * (u - a) ^ 2 := by
      rw [pow_succ, sq_abs]; ring
    rw [hsq]
    have h0 : 0 ≤ (u - a) ^ 2 := sq_nonneg _
    have habs : 0 ≤ |u - a| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hδ h0, mul_nonneg habs h0]
  have hr := hb.trans h3
  have hua : |u * a| ≤ θ * a := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_right hu ha0
  have hsplit : Real.exp (u - a) - 1 - u - u ^ 2 / 2 + a =
      (Real.exp (u - a) - (1 + (u - a) + (u - a) ^ 2 / 2)) + (-(u * a) + a ^ 2 / 2) := by ring
  rw [hsplit]
  have h1 := abs_add_le (Real.exp (u - a) - (1 + (u - a) + (u - a) ^ 2 / 2)) (-(u * a) + a ^ 2 / 2)
  have h2 : |-(u * a) + a ^ 2 / 2| ≤ θ * a + a ^ 2 / 2 := by
    calc |-(u * a) + a ^ 2 / 2| ≤ |-(u * a)| + |a ^ 2 / 2| := abs_add_le _ _
      _ = |u * a| + a ^ 2 / 2 := by rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 2)]
      _ ≤ θ * a + a ^ 2 / 2 := by linarith
  have hsq2 : (u - a) ^ 2 ≤ 2 * u ^ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (u + a)]
  have haa : a ^ 2 ≤ θ * a := by nlinarith
  have hθa : θ * a ^ 2 ≤ θ * a / 2 := by nlinarith [mul_nonneg hθ0 ha0]
  nlinarith [mul_le_mul_of_nonneg_left hsq2 (by positivity : (0 : ℝ) ≤ 2 * θ),
    mul_nonneg hθ0 ha0, mul_nonneg hθ0 (sq_nonneg u)]

/-- **Pathwise Itô formula for the Doléans exponential** along the uniform grids: if the path `x`
has Föllmer quadratic variation `s` on rational blocks of `[0, t]`, then the left Itô–Riemann
sums of `Z_s = exp (c x_s - c² s / 2)` against `c · dx` converge to `Z_t - Z_0`. -/
theorem tendsto_expRiemann {t : ℝ} (ht : 0 ≤ t) (c : ℝ) {x : ℝ → ℝ} (hx : Continuous x)
    (hqv : ∀ K i : ℕ, Tendsto (fun n : ℕ =>
      ∑ j ∈ (range (n + 1)).filter (fun j => j * K < i * (n + 1)),
        ((x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1)))) ^ 2 -
          t / ((n : ℝ) + 1))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1),
      Real.exp (c * x ((j : ℝ) * (t / ((n : ℝ) + 1))) -
          (1 / 2 : ℝ) * (c ^ 2 * ((j : ℝ) * (t / ((n : ℝ) + 1))))) *
        (c * (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1))))))
      atTop (𝓝 (Real.exp (c * x t - (1 / 2 : ℝ) * (c ^ 2 * t)) - Real.exp (c * x 0))) := by
  set Z : ℝ → ℝ := fun s => Real.exp (c * x s - (1 / 2 : ℝ) * (c ^ 2 * s)) with hZ
  have hZc : Continuous Z := by
    rw [hZ]; fun_prop
  set q : ℕ → ℕ → ℝ := fun n j =>
    (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1)))) ^ 2 with hq
  -- (i) the weighted quadratic-variation term vanishes
  have hW := tendsto_weighted_qv ht hZc.continuousOn q (fun n j => sq_nonneg _) hqv
  -- total squared increments are eventually bounded
  have htot : Tendsto (fun n => ∑ j ∈ range (n + 1), (q n j - t / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    refine (hqv 1 1).congr fun n => ?_
    refine Finset.sum_congr (Finset.filter_true_of_mem fun j hj => ?_) fun _ _ => rfl
    simpa using Finset.mem_range.mp hj
  have hV : ∀ᶠ n : ℕ in atTop, ∑ j ∈ range (n + 1), (q n j + t / ((n : ℝ) + 1)) ≤ 2 * t + 1 := by
    filter_upwards [(Metric.tendsto_nhds.mp htot) 1 one_pos] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc ∑ j ∈ range (n + 1), (q n j + t / ((n : ℝ) + 1))
        = ∑ j ∈ range (n + 1), (q n j - t / ((n : ℝ) + 1)) + 2 * t := by
          have e : ∀ j ∈ range (n + 1), q n j + t / ((n : ℝ) + 1) =
              (q n j - t / ((n : ℝ) + 1)) + 2 * (t / ((n : ℝ) + 1)) := fun j _ => by ring
          rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          congr 1
          push_cast
          field_simp
      _ ≤ 2 * t + 1 := by linarith [(abs_lt.mp hn).2]
  -- bound on `Z` over `[0, t]`
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).bddAbove_image
    (continuous_abs.comp hZc).continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ s ∈ Icc 0 t, |Z s| ≤ M := fun s hs =>
    (hM₀ (mem_image_of_mem _ hs)).trans (le_max_left _ _)
  -- uniform smallness of increments
  have hsmall : ∀ θ : ℝ, 0 < θ → ∀ᶠ n : ℕ in atTop, ∀ j < n + 1,
      |c * (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1))))| ≤ θ ∧
        (1 / 2 : ℝ) * (c ^ 2 * (t / ((n : ℝ) + 1))) ≤ θ := by
    intro θ hθ
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous
      (hx.continuousOn (s := Icc 0 t))
    rw [Metric.uniformContinuousOn_iff_le] at huc
    obtain ⟨δ, hδ, hδx⟩ := huc (θ / (|c| + 1)) (by positivity)
    have hlim : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have hlim2 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (c ^ 2 * (t / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      simpa using (hlim.const_mul (c ^ 2)).const_mul (1 / 2 : ℝ)
    filter_upwards [hlim.eventually (ge_mem_nhds hδ), hlim2.eventually (ge_mem_nhds hθ)]
      with n hn hn2 j hj
    refine ⟨?_, hn2⟩
    set Δ : ℝ := t / ((n : ℝ) + 1) with hΔdef
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hΔ0 : 0 ≤ Δ := div_nonneg ht hn1.le
    have hNΔ : ((n : ℝ) + 1) * Δ = t := by rw [hΔdef]; field_simp
    have hjr : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast hj
    have m1 : (j : ℝ) * Δ ∈ Icc 0 t :=
      ⟨by positivity, by nlinarith⟩
    have m2 : ((j : ℝ) + 1) * Δ ∈ Icc 0 t :=
      ⟨by positivity, by nlinarith⟩
    have hd : dist (((j : ℝ) + 1) * Δ) ((j : ℝ) * Δ) ≤ δ := by
      rw [Real.dist_eq, show ((j : ℝ) + 1) * Δ - (j : ℝ) * Δ = Δ by ring, abs_of_nonneg hΔ0]
      exact hn
    have h := hδx _ m2 _ m1 hd
    rw [Real.dist_eq] at h
    rw [abs_mul]
    calc |c| * |x (((j : ℝ) + 1) * Δ) - x ((j : ℝ) * Δ)| ≤ |c| * (θ / (|c| + 1)) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ θ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [abs_nonneg c]
  -- (ii) the Taylor remainder term vanishes
  set ρ : ℕ → ℕ → ℝ := fun n j =>
    Real.exp (c * (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1)))) -
        (1 / 2 : ℝ) * (c ^ 2 * (t / ((n : ℝ) + 1)))) - 1 -
      c * (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1)))) -
      (c * (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1))))) ^ 2 / 2 +
      (1 / 2 : ℝ) * (c ^ 2 * (t / ((n : ℝ) + 1))) with hρ
  have hR : Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1), Z ((j : ℝ) * (t / ((n : ℝ) + 1))) * ρ n j)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set D : ℝ := M * (4 * (c ^ 2 + 1) * (2 * t + 1)) + 1 with hD
    have hDpos : 0 < D := by positivity
    set θ : ℝ := min (1 / 2) (ε / (2 * D)) with hθdef
    have hθpos : 0 < θ := lt_min (by norm_num) (by positivity)
    filter_upwards [hV, hsmall θ hθpos] with n hVn hsn
    rw [Real.dist_eq, sub_zero]
    set Δ : ℝ := t / ((n : ℝ) + 1) with hΔdef
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hΔ0 : 0 ≤ Δ := div_nonneg ht hn1.le
    have hNΔ : ((n : ℝ) + 1) * Δ = t := by rw [hΔdef]; field_simp
    calc |∑ j ∈ range (n + 1), Z ((j : ℝ) * Δ) * ρ n j|
        ≤ ∑ j ∈ range (n + 1), |Z ((j : ℝ) * Δ) * ρ n j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (n + 1), M * (4 * θ * (c ^ 2 + 1)) * (q n j + Δ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          obtain ⟨h1, h2⟩ := hsn j hj'
          have hjr : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast hj'
          have m1 : (j : ℝ) * Δ ∈ Icc 0 t := ⟨by positivity, by nlinarith⟩
          have hb := abs_exp_sub_taylor_le h1 (by positivity) h2 (min_le_left _ _)
          rw [abs_mul]
          have hq0 : 0 ≤ q n j := sq_nonneg _
          have hρle : |ρ n j| ≤ 4 * θ * (c ^ 2 + 1) * (q n j + Δ) := by
            refine hb.trans ?_
            have e : (c * (x (((j : ℝ) + 1) * Δ) - x ((j : ℝ) * Δ))) ^ 2 = c ^ 2 * q n j := by
              simp only [hq]; ring
            rw [e]
            have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
            nlinarith [mul_nonneg hθpos.le (mul_nonneg hc2 hq0), mul_nonneg hθpos.le hq0,
              mul_nonneg hθpos.le (mul_nonneg hc2 hΔ0), mul_nonneg hθpos.le hΔ0]
          calc |Z ((j : ℝ) * Δ)| * |ρ n j| ≤ M * (4 * θ * (c ^ 2 + 1) * (q n j + Δ)) :=
                mul_le_mul (hM _ m1) hρle (abs_nonneg _) hM0
            _ = M * (4 * θ * (c ^ 2 + 1)) * (q n j + Δ) := by ring
      _ = M * (4 * θ * (c ^ 2 + 1)) * ∑ j ∈ range (n + 1), (q n j + Δ) := by
          rw [Finset.mul_sum]
      _ ≤ M * (4 * θ * (c ^ 2 + 1)) * (2 * t + 1) :=
          mul_le_mul_of_nonneg_left hVn (by positivity)
      _ = θ * (M * (4 * (c ^ 2 + 1) * (2 * t + 1))) := by ring
      _ ≤ θ * D := mul_le_mul_of_nonneg_left (by rw [hD]; linarith) hθpos.le
      _ ≤ ε / (2 * D) * D := mul_le_mul_of_nonneg_right (min_le_right _ _) hDpos.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- assemble: telescoping identity
  have hident : ∀ n : ℕ, ∑ j ∈ range (n + 1),
      Z ((j : ℝ) * (t / ((n : ℝ) + 1))) *
        (c * (x (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) - x ((j : ℝ) * (t / ((n : ℝ) + 1))))) =
      (Z t - Z 0) -
        c ^ 2 / 2 * (∑ j ∈ range (n + 1),
          Z ((j : ℝ) * (t / ((n : ℝ) + 1))) * (q n j - t / ((n : ℝ) + 1))) -
        ∑ j ∈ range (n + 1), Z ((j : ℝ) * (t / ((n : ℝ) + 1))) * ρ n j := by
    intro n
    set Δ : ℝ := t / ((n : ℝ) + 1) with hΔdef
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNΔ : ((n : ℝ) + 1) * Δ = t := by rw [hΔdef]; field_simp
    have htel := Finset.sum_range_sub (fun j : ℕ => Z ((j : ℝ) * Δ)) (n + 1)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at htel
    rw [hNΔ] at htel
    rw [← htel, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstep : Z (((j : ℝ) + 1) * Δ) = Z ((j : ℝ) * Δ) *
        Real.exp (c * (x (((j : ℝ) + 1) * Δ) - x ((j : ℝ) * Δ)) - (1 / 2 : ℝ) * (c ^ 2 * Δ)) := by
      simp only [hZ]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hstep]
    simp only [hρ, hq]
    ring
  have hfinal : Tendsto (fun n : ℕ => (Z t - Z 0) -
        c ^ 2 / 2 * (∑ j ∈ range (n + 1),
          Z ((j : ℝ) * (t / ((n : ℝ) + 1))) * (q n j - t / ((n : ℝ) + 1))) -
        ∑ j ∈ range (n + 1), Z ((j : ℝ) * (t / ((n : ℝ) + 1))) * ρ n j)
      atTop (𝓝 ((Z t - Z 0) - c ^ 2 / 2 * 0 - 0)) :=
    (tendsto_const_nhds.sub (hW.const_mul _)).sub hR
  have hval : Z t - Z 0 - c ^ 2 / 2 * 0 - 0 =
      Real.exp (c * x t - (1 / 2 : ℝ) * (c ^ 2 * t)) - Real.exp (c * x 0) := by simp [hZ]
  rw [hval] at hfinal
  exact hfinal.congr fun n => (hident n).symm

end SignatureVolatility

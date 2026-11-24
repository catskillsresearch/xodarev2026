module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.ItoCalculusKit.ExpSupermartingale
public import SignatureVolatility.ItoCalculusKit.DoleansIdentify
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto

/-!
# B1a. `E exp(Φ(x,s)) ≤ 1` by the existing Doléans bound, with `H_r = (x + W_r)²`

This is the exact analogue of the Pillar A bound
`lintegral_exp_counterexampleU0_pairing_le_one`, with the integrand
`W²` replaced by `(x + W)²`. Itô's formula on `(x + W)³/3` gives the
pathwise identity
`Φ(x,s) = ∫₀ˢ (x+W)² dW - ½∫₀ˢ (x+W)⁴ dr`, so
`lintegral_exp_ito_le_one` at `q = 1` yields the claim.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Path-continuity of a Brownian coordinate, used for Riemann/QV limits. -/
private lemma continuous_W_coord' {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) (ω : Ω) :
    Continuous fun s : ℝ => MultiBrownian.W B s ω k :=
  (B.pathContinuous k ω).comp continuous_real_toNNReal

private lemma unifGrid_last_cast (t : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * (t / ((n : ℝ) + 1)) = t := by
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private lemma gridPt_cast (t : ℝ) (n i : ℕ) :
    gridPt t n i = (i : ℝ) * (t / ((n : ℝ) + 1)) := by
  simp [gridPt, Nat.cast_add, Nat.cast_one]

private lemma mul_sq_sub_eq (a b : ℝ) :
    a ^ 2 * (b - a) =
      (1 / 3 : ℝ) * (b ^ 3 - a ^ 3) - a * (b - a) ^ 2 - (1 / 3 : ℝ) * (b - a) ^ 3 := by
  ring

/-- Algebraic rearrangement of the left Riemann sums of `(x + W)²`. -/
private lemma unifRiemann_shifted_sq_eq {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    (x : ℝ) {t : ℝ} (_ht : 0 ≤ t) (n : ℕ) (ω : Ω) :
    unifRiemann B k (fun u ω' => (x + MultiBrownian.W B u ω' k) ^ 2) t (n + 1) ω =
      (1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3)
      - ∑ i ∈ range (n + 1),
          (x + MultiBrownian.W B (gridPt t n i) ω k) *
            wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2
      - (1 / 3 : ℝ) * ∑ i ∈ range (n + 1),
          wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3 := by
  set Δ : ℝ := t / ((n + 1 : ℕ) : ℝ)
  have hNΔ : ((n + 1 : ℕ) : ℝ) * Δ = t := by
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp [Δ]
    field_simp
  have hinc : ∀ i : ℕ,
      wnnIncr B k ((i : ℝ) * Δ) (((i + 1 : ℕ) : ℝ) * Δ) ω =
        MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k -
          MultiBrownian.W B ((i : ℝ) * Δ) ω k := fun _ => rfl
  have hgrid : ∀ i, gridPt t n i = (i : ℝ) * Δ := fun i => by
    simp [gridPt, Δ]
  have hgrid' : ∀ i, gridPt t n (i + 1) = ((i + 1 : ℕ) : ℝ) * Δ := fun i => by
    simp [gridPt, Δ]
  have hterm : ∀ i ∈ range (n + 1),
      (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 2 *
          (MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k -
            MultiBrownian.W B ((i : ℝ) * Δ) ω k) =
        (1 / 3 : ℝ) *
            ((x + MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k) ^ 3 -
              (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 3)
          - (x + MultiBrownian.W B (gridPt t n i) ω k) *
              wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2
          - (1 / 3 : ℝ) *
              wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3 := by
    intro i _
    have hi := mul_sq_sub_eq (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k)
      (x + MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k)
    have hdiff :
        (x + MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k) -
            (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) =
          MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k -
            MultiBrownian.W B ((i : ℝ) * Δ) ω k := by ring
    rw [hgrid i, hgrid' i, hinc i, ← hdiff]
    exact hi
  have htel : ∑ i ∈ range (n + 1),
      ((x + MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k) ^ 3 -
        (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 3) =
      (x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3 := by
    have h := Finset.sum_range_sub
      (fun i : ℕ => (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 3) (n + 1)
    have hNΔ' : ((n : ℝ) + 1) * Δ = t := by
      simpa [Nat.cast_add, Nat.cast_one] using hNΔ
    simpa [hNΔ', MultiBrownian.W_zero, add_zero, sub_zero] using h
  calc unifRiemann B k (fun u ω' => (x + MultiBrownian.W B u ω' k) ^ 2) t (n + 1) ω
      = ∑ i ∈ range (n + 1),
          (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 2 *
            (MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k -
              MultiBrownian.W B ((i : ℝ) * Δ) ω k) := by
        simp only [unifRiemann, Δ]
        exact Finset.sum_congr rfl fun i _ => by rw [hinc i]
    _ = ∑ i ∈ range (n + 1),
          ((1 / 3 : ℝ) *
              ((x + MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k) ^ 3 -
                (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 3)
            - (x + MultiBrownian.W B (gridPt t n i) ω k) *
                wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2
            - (1 / 3 : ℝ) *
                wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3) :=
        Finset.sum_congr rfl hterm
    _ = (1 / 3 : ℝ) * ∑ i ∈ range (n + 1),
            ((x + MultiBrownian.W B (((i + 1 : ℕ) : ℝ) * Δ) ω k) ^ 3 -
              (x + MultiBrownian.W B ((i : ℝ) * Δ) ω k) ^ 3)
        - ∑ i ∈ range (n + 1),
            (x + MultiBrownian.W B (gridPt t n i) ω k) *
              wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2
        - (1 / 3 : ℝ) * ∑ i ∈ range (n + 1),
            wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ = (1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3)
        - ∑ i ∈ range (n + 1),
            (x + MultiBrownian.W B (gridPt t n i) ω k) *
              wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2
        - (1 / 3 : ℝ) * ∑ i ∈ range (n + 1),
            wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3 := by
        rw [htel]

/-- The cubic variation along uniform grids vanishes, given a.s. quadratic variation
and path continuity of `W`. -/
private lemma tendsto_sum_wnnIncr_cube {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d) {t : ℝ}
    (ht : 0 ≤ t) {ω : Ω}
    (hsq : Tendsto (fun n => ∑ i ∈ range (n + 1),
      wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2) atTop (𝓝 t)) :
    Tendsto (fun n => ∑ i ∈ range (n + 1),
      wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3) atTop (𝓝 0) := by
  have hx : Continuous (fun s : ℝ => MultiBrownian.W B s ω k) := continuous_W_coord' B k ω
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (hx.continuousOn (s := Icc 0 t))
  rw [Metric.uniformContinuousOn_iff_le] at huc
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set θ : ℝ := ε / (t + 1)
  have hθ : 0 < θ := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδx⟩ := huc θ hθ
  have hΔ : Tendsto (fun n : ℕ => t / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_const_nhds (x := t)).div_atTop
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  filter_upwards [hΔ.eventually (ge_mem_nhds hδ),
    (Metric.tendsto_nhds.mp hsq) 1 one_pos] with n hnΔ hsqn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hΔ0 : 0 ≤ t / ((n + 1 : ℕ) : ℝ) := div_nonneg ht hn1.le
  have hgrid : ∀ i, i ≤ n + 1 → gridPt t n i ∈ Icc 0 t := by
    intro i hi
    refine ⟨by simp [gridPt]; positivity, ?_⟩
    have hle : (i : ℝ) * (t / ((n : ℝ) + 1)) ≤
        ((n : ℝ) + 1) * (t / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi)
        (by simpa [Nat.cast_add, Nat.cast_one] using hΔ0)
    simpa [gridPt, Nat.cast_add, Nat.cast_one, unifGrid_last_cast t n] using hle
  have hinc_le : ∀ i < n + 1,
      |wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω| ≤ θ := by
    intro i hi
    change |MultiBrownian.W B (gridPt t n (i + 1)) ω k -
      MultiBrownian.W B (gridPt t n i) ω k| ≤ θ
    have m1 := hgrid i hi.le
    have m2 := hgrid (i + 1) (Nat.succ_le_of_lt hi)
    have hd : dist (gridPt t n (i + 1)) (gridPt t n i) ≤ δ := by
      have hdiff : gridPt t n (i + 1) - gridPt t n i = t / ((n + 1 : ℕ) : ℝ) := by
        simp [gridPt]; ring
      rw [Real.dist_eq, hdiff, abs_of_nonneg hΔ0]
      exact hnΔ
    have h := hδx _ m2 _ m1 hd
    rwa [Real.dist_eq] at h
  have habs : |∑ i ∈ range (n + 1),
      wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3| ≤
      θ * ∑ i ∈ range (n + 1),
        wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 := by
    have hz : ∀ z : ℝ, |z ^ 3| = |z| * z ^ 2 := fun z => by
      rw [abs_pow, pow_succ, sq_abs, mul_comm]
    calc |∑ i ∈ range (n + 1),
            wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3|
        ≤ ∑ i ∈ range (n + 1),
            |wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 3| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ range (n + 1),
            |wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω| *
              wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => hz _
      _ ≤ ∑ i ∈ range (n + 1),
            θ * wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 := by
          refine Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_right
              (hinc_le i (Finset.mem_range.mp hi)) (sq_nonneg _)
      _ = θ * ∑ i ∈ range (n + 1),
            wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 := by
          rw [← Finset.mul_sum]
  have hsqlt : ∑ i ∈ range (n + 1),
      wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 < t + 1 := by
    rw [Real.dist_eq] at hsqn
    linarith [(abs_lt.mp hsqn).2]
  rw [Real.dist_eq, sub_zero]
  have hθt : θ * (t + 1) = ε :=
    div_mul_cancel₀ ε (by positivity : (t + 1 : ℝ) ≠ 0)
  refine (lt_of_le_of_lt habs ?_).trans_eq hθt
  exact mul_lt_mul_of_pos_left hsqlt hθ

/-- `∑ (x + W_{t_i}) (ΔW_i)² → ∫ (x + W)` almost surely. -/
private lemma ae_tendsto_sum_shifted_mul_wnnIncr_sq {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ range (n + 1),
      (x + MultiBrownian.W B (gridPt t n i) ω k) *
        wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2) atTop
      (𝓝 (∫ r in (0 : ℝ)..t, x + MultiBrownian.W B r ω k)) := by
  filter_upwards [ae_tendsto_qvBlocks B k ht] with ω hω
  have hg : ContinuousOn (fun r : ℝ => x + MultiBrownian.W B r ω k) (Icc 0 t) :=
    (continuous_const.add (continuous_W_coord' B k ω)).continuousOn
  have hW0 : Tendsto (fun n => ∑ j ∈ range (n + 1),
      (x + MultiBrownian.W B ((j : ℝ) * (t / ((n : ℝ) + 1))) ω k) *
        qvIncr B k t n j ω) atTop (𝓝 0) := by
    refine tendsto_weighted_qv ht hg
      (fun n j => wnnIncr B k ((j : ℝ) * (t / ((n : ℝ) + 1)))
        (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) ω ^ 2)
      (fun _ _ => sq_nonneg _) ?_
    intro K i
    simpa [qvIncr] using hω K i
  have hR := tendsto_lebRiemann_of_continuousOn ht hg
  have hsum : ∀ n,
      ∑ i ∈ range (n + 1),
        (x + MultiBrownian.W B (gridPt t n i) ω k) *
          wnnIncr B k (gridPt t n i) (gridPt t n (i + 1)) ω ^ 2 =
      (∑ j ∈ range (n + 1),
        (x + MultiBrownian.W B ((j : ℝ) * (t / ((n : ℝ) + 1))) ω k) * qvIncr B k t n j ω) +
      ∑ j ∈ range (n + 1),
        (x + MultiBrownian.W B ((j : ℝ) * (t / ((n : ℝ) + 1))) ω k) *
          (t / ((n : ℝ) + 1)) := by
    intro n
    have hinc : ∀ j,
        wnnIncr B k (gridPt t n j) (gridPt t n (j + 1)) ω =
          wnnIncr B k ((j : ℝ) * (t / ((n : ℝ) + 1)))
            (((j : ℝ) + 1) * (t / ((n : ℝ) + 1))) ω := fun j => by
      simp [gridPt_cast]
    simp only [qvIncr, gridPt_cast, mul_sub, Finset.sum_sub_distrib, Nat.cast_add,
      Nat.cast_one]
    abel
  have h := hW0.add hR
  simpa [hsum, zero_add] using h

/-- The left Itô–Riemann sums of `(x + W)²` converge a.s. to
`(1/3)((x + W_t)³ - x³) - ∫ (x + W)`. -/
private theorem ae_tendsto_unifRiemann_shifted_sq {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      unifRiemann B k (fun u ω' => (x + MultiBrownian.W B u ω' k) ^ 2) t (n + 1) ω)
      atTop (𝓝 ((1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3)
        - ∫ r in (0 : ℝ)..t, x + MultiBrownian.W B r ω k)) := by
  filter_upwards [ae_tendsto_sum_wnnIncr_sq B k ht,
    ae_tendsto_sum_shifted_mul_wnnIncr_sq B k x ht] with ω hsq hW
  have hcube := tendsto_sum_wnnIncr_cube B k ht hsq
  have hconst :
      Tendsto (fun _ : ℕ =>
        (1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3))
        atTop (𝓝 ((1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3))) :=
    tendsto_const_nhds
  have h := (hconst.sub hW).sub (hcube.const_mul (1 / 3 : ℝ))
  have hlim :
      ((1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3)
        - ∫ r in (0 : ℝ)..t, x + MultiBrownian.W B r ω k)
        - (1 / 3 : ℝ) * 0 =
      (1 / 3 : ℝ) * ((x + MultiBrownian.W B t ω k) ^ 3 - x ^ 3)
        - ∫ r in (0 : ℝ)..t, x + MultiBrownian.W B r ω k := by ring
  rw [← hlim]
  exact h.congr fun n => (unifRiemann_shifted_sq_eq B k x ht n ω).symm

private lemma tendsto_sum_shifted_pow_four {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1),
      ((x + MultiBrownian.W B ((i : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω k) ^ 2) ^ 2 *
        (t / ((n + 1 : ℕ) : ℝ))) atTop
      (𝓝 (∫ r in (0 : ℝ)..t, (x + MultiBrownian.W B r ω k) ^ 4)) := by
  have hg : ContinuousOn (fun r : ℝ => (x + MultiBrownian.W B r ω k) ^ 4) (Icc 0 t) :=
    ((continuous_const.add (continuous_W_coord' B k ω)).pow 4).continuousOn
  have h := tendsto_lebRiemann_of_continuousOn ht hg
  have hsum : (fun n : ℕ => ∑ i ∈ range (n + 1),
      ((x + MultiBrownian.W B ((i : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω k) ^ 2) ^ 2 *
        (t / ((n + 1 : ℕ) : ℝ))) =
      fun n : ℕ => ∑ i ∈ range (n + 1),
        (x + MultiBrownian.W B ((i : ℝ) * (t / ((n : ℝ) + 1))) ω k) ^ 4 *
          (t / ((n : ℝ) + 1)) := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    have hΔ : (t / ((n + 1 : ℕ) : ℝ)) = t / ((n : ℝ) + 1) := by
      simp [Nat.cast_add, Nat.cast_one]
    rw [hΔ]
    ring
  rw [hsum]
  exact h

private lemma measurable_shifted_sq_path {d : ℕ} (B : MultiBrownian Ω P d) (k : Fin d)
    (x : ℝ) {u : ℝ} (h0 : 0 ≤ u) :
    Measurable[(pathFiltration B).σAlg u]
      (fun ω => (x + MultiBrownian.W B u ω k) ^ 2) :=
  ((measurable_W_pathFiltration B (T := u) ⟨u, h0, le_rfl⟩ k).const_add x).pow_const 2

/-- Exact copy of the Pillar A bound, with the integrand shifted by `x`. -/
lemma lintegral_exp_shiftedExponent_le_one {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s x ω)) ∂P ≤ 1 := by
  set k : Fin d := ⟨0, hd⟩
  set H : ℝ → Ω → ℝ := fun u ω => (x + MultiBrownian.W B u ω k) ^ 2
  set I : Ω → ℝ := fun ω =>
    (1 / 3 : ℝ) * ((x + MultiBrownian.W B s ω k) ^ 3 - x ^ 3)
      - ∫ r in (0 : ℝ)..s, x + MultiBrownian.W B r ω k
  set Q : Ω → ℝ := fun ω =>
    ∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω k) ^ 4
  have hH : ∀ u, 0 ≤ u → u ≤ s → Measurable[(pathFiltration B).σAlg u] (H u) :=
    fun _u h0 _hu => measurable_shifted_sq_path B k x h0
  have hI : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H s (n + 1) ω) atTop
      (𝓝 (I ω)) := ae_tendsto_unifRiemann_shifted_sq B k x hs
  have hQ : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∑ i ∈ range (n + 1),
      H ((i : ℝ) * (s / ((n + 1 : ℕ) : ℝ))) ω ^ 2 * (s / ((n + 1 : ℕ) : ℝ))) atTop
      (𝓝 (Q ω)) :=
    ae_of_all _ fun ω => tendsto_sum_shifted_pow_four B k x hs ω
  have h := lintegral_exp_ito_le_one B k hs hH (1 : ℝ) hI hQ
  have hexp : (fun ω => ENNReal.ofReal (Real.exp (counterexampleV1Exponent B hd s x ω))) =
      fun ω => ENNReal.ofReal (Real.exp ((1 : ℝ) * I ω - (1 : ℝ) ^ 2 / 2 * Q ω)) := by
    funext ω
    simp [I, Q, k, counterexampleV1Exponent]
  rw [hexp]
  exact h

end SignatureVolatility

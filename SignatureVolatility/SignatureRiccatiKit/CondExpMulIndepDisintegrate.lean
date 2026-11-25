module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleTensor
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1PosLe
public import SignatureVolatility.SignatureRiccatiKit.BrownianScalingShiftedExponent
public import SignatureVolatility.SignatureRiccatiKit.LintegralExpShifted
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.ItoCalculusKit.JointPast
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ProlongedBrownianSetup.ShiftedWordIntegral
public import SignatureVolatility.ProlongedBrownianSetup.ItoIntegralAgainstBM
public import SignatureVolatility.DualPairing
public import SignatureVolatility.SignatureFiltrationEqBrownianFiltration

/-!
# B5b. Conditional-expectation disintegration for an independent increment factor
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set Finset
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Helper 1: Continuity in `x` (via local Lipschitz bound — no binomial expansion!) -/

private lemma continuous_int_add_pow {s : ℝ} (hs : 0 ≤ s) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc 0 s)) (m : ℕ) :
    Continuous (fun x : ℝ => ∫ r in (0 : ℝ)..s, (x + w r) ^ m) := by
  obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  set Mw' : ℝ := max Mw 0
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  set B : ℝ := |x₀| + 1 + Mw'
  have hB0 : 0 ≤ B := by positivity
  set L : ℝ := s * ((m : ℝ) * B ^ (m - 1)) + 1
  have hL0 : 0 < L := by positivity
  refine ⟨min 1 (ε / L), lt_min one_pos (div_pos hε hL0), fun {x} hx => ?_⟩
  have hx1 : |x - x₀| < 1 := by simpa [Real.dist_eq] using lt_of_lt_of_le hx (min_le_left _ _)
  have hxε : |x - x₀| < ε / L := by simpa [Real.dist_eq] using lt_of_lt_of_le hx (min_le_right _ _)
  have hi : ∀ y : ℝ, IntervalIntegrable (fun r => (y + w r) ^ m) volume 0 s := fun y =>
    ((continuousOn_const.add hw).pow m).intervalIntegrable_of_Icc hs
  rw [Real.dist_eq, ← intervalIntegral.integral_sub (hi x) (hi x₀)]
  have hpt : ∀ r ∈ uIoc 0 s, ‖(x + w r) ^ m - (x₀ + w r) ^ m‖ ≤ ((m : ℝ) * B ^ (m - 1)) * |x - x₀| := by
    intro r hr
    rw [uIoc_of_le hs] at hr
    have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2⟩
    have hwr : |w r| ≤ Mw' := (hMw r hrI).trans (le_max_left _ _)
    have hax : |x + w r| ≤ B := by
      have hx_le : |x| ≤ |x₀| + 1 := by
        have := abs_sub_abs_le_abs_sub x x₀; linarith
      exact (abs_add_le x (w r)).trans (by linarith)
    have hax0 : |x₀ + w r| ≤ B := (abs_add_le x₀ (w r)).trans (by linarith)
    -- `|a^m - b^m| = |a - b| * |∑_{k<m} a^k b^{m-1-k}| ≤ m * B^{m-1} * |a - b|`
    rw [Real.norm_eq_abs]
    cases m with
    | zero => simp
    | succ m =>
      have hfac : (x + w r) ^ (m + 1) - (x₀ + w r) ^ (m + 1) =
          (x - x₀) * ∑ k ∈ Finset.range (m + 1), (x + w r) ^ k * (x₀ + w r) ^ (m - k) := by
        have h := geom_sum₂_mul (x + w r) (x₀ + w r) (m + 1)
        have hsub : (x + w r) - (x₀ + w r) = x - x₀ := by ring
        rw [hsub, mul_comm] at h
        exact h.symm
      rw [hfac, abs_mul]
      have hsum_le : |∑ k ∈ Finset.range (m + 1), (x + w r) ^ k * (x₀ + w r) ^ (m - k)| ≤
          ((m + 1 : ℕ) : ℝ) * B ^ m := by
        calc _ ≤ ∑ k ∈ Finset.range (m + 1), |(x + w r) ^ k * (x₀ + w r) ^ (m - k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k ∈ Finset.range (m + 1), B ^ m := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
              rw [abs_mul, abs_pow, abs_pow]
              calc |x + w r| ^ k * |x₀ + w r| ^ (m - k)
                  ≤ B ^ k * B ^ (m - k) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hax k)
                    (pow_le_pow_left₀ (abs_nonneg _) hax0 (m - k)) (by positivity) (by positivity)
                _ = B ^ m := by rw [← pow_add, Nat.add_sub_cancel' hk']
          _ = ((m + 1 : ℕ) : ℝ) * B ^ m := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc |x - x₀| * |∑ k ∈ Finset.range (m + 1), (x + w r) ^ k * (x₀ + w r) ^ (m - k)|
          ≤ |x - x₀| * (((m + 1 : ℕ) : ℝ) * B ^ m) := mul_le_mul_of_nonneg_left hsum_le (abs_nonneg _)
        _ = ((m + 1 : ℕ) : ℝ) * B ^ (m + 1 - 1) * |x - x₀| := by simp; ring
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at hbd
  calc |∫ r in (0 : ℝ)..s, ((x + w r) ^ m - (x₀ + w r) ^ m)|
      ≤ ((m : ℝ) * B ^ (m - 1)) * |x - x₀| * s := hbd
    _ ≤ L * |x - x₀| := by nlinarith [abs_nonneg (x - x₀)]
    _ < L * (ε / L) := mul_lt_mul_of_pos_left hxε hL0
    _ = ε := mul_div_cancel₀ ε hL0.ne'

private lemma continuous_counterexampleV1ExponentScaled_in_x {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (lam : ℝ) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    Continuous (fun x : ℝ => counterexampleV1ExponentScaled B hd lam s x ω) := by
  have hw : ContinuousOn (fun r => MultiBrownian.W B r ω ⟨0, hd⟩) (Icc 0 s) :=
    (continuous_W_coord_v1 B ⟨0, hd⟩ ω).continuousOn
  have hc1 : Continuous (fun x : ℝ => ∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω ⟨0, hd⟩)) := by
    simpa [pow_one] using continuous_int_add_pow hs hw 1
  have hc4 : Continuous (fun x : ℝ => ∫ r in (0 : ℝ)..s, (x + MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4) :=
    continuous_int_add_pow hs hw 4
  unfold counterexampleV1ExponentScaled
  exact ((continuous_const.mul (((continuous_id.add continuous_const).pow 3).sub (continuous_pow 3))).sub
    (continuous_const.mul hc1)).sub (continuous_const.mul hc4)

private lemma continuous_counterexampleV1Exponent_in_x {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    Continuous (fun x : ℝ => counterexampleV1Exponent B hd s x ω) := by
  have h := continuous_counterexampleV1ExponentScaled_in_x B hd 1 hs ω
  have heq : (fun x : ℝ => counterexampleV1Exponent B hd s x ω) =
      fun x : ℝ => counterexampleV1ExponentScaled B hd 1 s x ω := by
    funext x; simp [counterexampleV1Exponent, counterexampleV1ExponentScaled]
  rwa [heq]

private lemma continuous_trunc_scaled_integral {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (lam : ℝ) {s : ℝ} (hs : 0 ≤ s) (R : ℕ) :
    Continuous (fun x : ℝ =>
      ∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B hd lam s x ω')) ∂P) :=
  continuous_of_dominated
    (fun x => (measurable_const.min
      ((measurable_counterexampleV1ExponentScaled B hd hs x).exp)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun ω' => by
      rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]
      exact min_le_left _ _)
    (integrable_const (R : ℝ))
    (ae_of_all _ fun ω' =>
      continuous_const.min (Real.continuous_exp.comp
        (continuous_counterexampleV1ExponentScaled_in_x B hd lam hs ω')))

/-! ### Helper 2: Independence of shifted increment vectors & measurability at random `Wt ω` -/

private lemma indepFun_pathFiltration_shiftIncrVec {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (N : ℕ) (hN : 0 < N)
    {β : Type*} [MeasurableSpace β] {g : Ω → β}
    (hg : Measurable[(pathFiltration B).σAlg t] g) :
    IndepFun g (fun ω (k : Fin N) =>
      wnnIncr (B.shift t.toNNReal) ⟨0, hd⟩ ((k : ℝ) * (s / (N : ℝ)))
        (((k : ℕ) + 1 : ℕ) * (s / (N : ℝ))) ω) P := by
  set B' := B.shift t.toNNReal
  set Δ : ℝ := s / (N : ℝ)
  have hΔ : 0 ≤ Δ := div_nonneg hs.le (Nat.cast_nonneg N)
  have hfut_indep : Indep (futAlg B ⟨0, hd⟩ t) ((pathFiltration B).σAlg t) P := by
    have hrest_le : ⨆ i ∈ ({(⟨0, hd⟩ : Fin d)}ᶜ : Set (Fin d)), coordAlg B i ≤ ‹MeasurableSpace Ω› :=
      iSup₂_le fun i _ => coordAlg_le B i
    have h123 : Indep (futAlg B ⟨0, hd⟩ t ⊔ ownAlg B ⟨0, hd⟩ t)
        (⨆ i ∈ ({(⟨0, hd⟩ : Fin d)}ᶜ : Set (Fin d)), coordAlg B i) P :=
      indep_of_indep_of_le_left (indep_coordAlg_iSup_compl B ⟨0, hd⟩)
        (sup_le (futAlg_le_coordAlg B ⟨0, hd⟩ t) (ownAlg_le_coordAlg B ⟨0, hd⟩ t))
    have hmain := indep_sup_of_indep_of_indep_sup
      ((futAlg_le_coordAlg B ⟨0, hd⟩ t).trans (coordAlg_le B ⟨0, hd⟩))
      ((ownAlg_le_coordAlg B ⟨0, hd⟩ t).trans (coordAlg_le B ⟨0, hd⟩))
      hrest_le (indep_futAlg_ownAlg B ⟨0, hd⟩ t) h123
    refine indep_of_indep_of_le_right hmain (iSup_le fun r => iSup_le fun i => ?_)
    by_cases hi : i = ⟨0, hd⟩
    · rw [hi]; exact le_sup_of_le_left (measurable_W_ownAlg B ⟨0, hd⟩ r.2.2).comap_le
    · exact le_sup_of_le_right (le_iSup₂_of_le i hi (measurable_W_coordAlg B i r.1).comap_le)
  have hZ_fut : @Measurable Ω (Fin N → ℝ) (futAlg B ⟨0, hd⟩ t) _
      (fun ω (k : Fin N) => wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω) := by
    refine (@measurable_pi_iff Ω (Fin N) (fun _ => ℝ) (futAlg B ⟨0, hd⟩ t) _ _).mpr fun k => ?_
    have hk0 : 0 ≤ (k : ℝ) * Δ := by positivity
    have hk1 : 0 ≤ (((k : ℕ) + 1 : ℕ) : ℝ) * Δ := by positivity
    have heq : (fun ω => wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * Δ) (((k : ℕ) + 1 : ℕ) * Δ) ω) =
        fun ω => wnnIncr B ⟨0, hd⟩ t (t + (((k : ℕ) + 1 : ℕ) : ℝ) * Δ) ω -
          wnnIncr B ⟨0, hd⟩ t (t + (k : ℝ) * Δ) ω := by
      funext ω; rw [wnnIncr_shift B ht ⟨0, hd⟩ hk0 hk1 ω]; simp [wnnIncr]
    rw [heq]
    exact (measurable_wnnIncr_futAlg B ⟨0, hd⟩ (le_add_of_nonneg_right hk1)).sub
      (measurable_wnnIncr_futAlg B ⟨0, hd⟩ (le_add_of_nonneg_right hk0))
  rw [IndepFun_iff_Indep]
  exact (indep_of_indep_of_le hfut_indep hZ_fut.comap_le hg.comap_le).symm

/-- Pointwise discrete-Riemann convergence of `discV1Exp` at `(c² s, c x)` to
`counterexampleV1ExponentScaled`. No `let` in the statement. -/
private lemma tendsto_discV1Exp_scaled {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) (x : ℝ) (ω' : Ω) :
    Tendsto (fun n : ℕ =>
      discV1Exp (n + 1) ((lam ^ (1 / 3 : ℝ)) ^ 2 * s) (lam ^ (1 / 3 : ℝ) * x) (fun k =>
        lam ^ (1 / 3 : ℝ) * wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
          (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω')) atTop
      (𝓝 (counterexampleV1ExponentScaled B' hd lam s x ω')) := by
  set c : ℝ := lam ^ (1 / 3 : ℝ)
  have hc3 : c ^ 3 = lam := by
    rw [show c = lam ^ (1 / 3 : ℝ) from rfl, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
  have hc1 := tendsto_lebRiemann_of_continuousOn
      (g := fun r => x + MultiBrownian.W B' r ω' ⟨0, hd⟩)
      hs.le (continuousOn_const.add (continuous_W_coord_v1 B' ⟨0, hd⟩ ω').continuousOn)
  have hc4 := tendsto_lebRiemann_of_continuousOn
      (g := fun r => (x + MultiBrownian.W B' r ω' ⟨0, hd⟩) ^ 4)
      hs.le ((continuousOn_const.add (continuous_W_coord_v1 B' ⟨0, hd⟩ ω').continuousOn).pow 4)
  have h := ((tendsto_const_nhds (x := (lam / 3) *
      ((x + MultiBrownian.W B' s ω' ⟨0, hd⟩) ^ 3 - x ^ 3))).sub
      (hc1.const_mul lam)).sub (hc4.const_mul (lam ^ 2 / 2))
  refine h.congr fun n => ?_
  set Z : Fin (n + 1) → ℝ := fun k =>
    c * wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
      (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω'
  have hpsum : ∀ k ≤ n + 1,
      (∑ j : Fin (n + 1), if (j : ℕ) < k then Z j else 0) =
        c * MultiBrownian.W B' ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ))) ω' ⟨0, hd⟩ :=
    fun k hk => by
      have hZsum :
          (∑ j : Fin (n + 1), if (j : ℕ) < k then Z j else 0) =
            c * (∑ j : Fin (n + 1), if (j : ℕ) < k then
              wnnIncr B' ⟨0, hd⟩ ((j : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
                (((j : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω' else 0) := by
        dsimp only [Z]
        simp [mul_ite, mul_zero, Finset.mul_sum]
      rw [hZsum, psum_incrVec B' hd s (n + 1) k hk ω']
  have hNs : ((n + 1 : ℕ) : ℝ) * (s / ((n + 1 : ℕ) : ℝ)) = s := by field_simp
  set s' : ℝ := c ^ 2 * s
  set x' : ℝ := c * x
  have hsum1 :
      ∑ k : Fin (n + 1),
        (x' + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z j else 0) *
          (s' / ((n + 1 : ℕ) : ℝ)) =
      lam * ∑ k ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B' ((k : ℝ) * (s / ((n : ℝ) + 1))) ω' ⟨0, hd⟩) *
          (s / ((n : ℝ) + 1)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (x' + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z j else 0) *
        (s' / ((n + 1 : ℕ) : ℝ))) (n + 1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hpsum k (Finset.mem_range.mp hk).le]
    simp only [x', s', ← hc3]
    push_cast
    ring
  have hsum4 :
      ∑ k : Fin (n + 1),
        (x' + ∑ j : Fin (n + 1), if (j : ℕ) < (k : ℕ) then Z j else 0) ^ 4 *
          (s' / ((n + 1 : ℕ) : ℝ)) =
      lam ^ 2 * ∑ k ∈ Finset.range (n + 1),
        (x + MultiBrownian.W B' ((k : ℝ) * (s / ((n : ℝ) + 1))) ω' ⟨0, hd⟩) ^ 4 *
          (s / ((n : ℝ) + 1)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (x' + ∑ j : Fin (n + 1), if (j : ℕ) < k then Z j else 0) ^ 4 *
        (s' / ((n + 1 : ℕ) : ℝ))) (n + 1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hpsum k (Finset.mem_range.mp hk).le]
    simp only [x', s', ← hc3]
    push_cast
    ring
  simp only [discV1Exp]
  rw [hpsum (n + 1) le_rfl, hNs, hsum1, hsum4]
  simp only [x']
  have hcube :
      (1 / 3 : ℝ) * ((c * x + c * MultiBrownian.W B' s ω' ⟨0, hd⟩) ^ 3 - (c * x) ^ 3) =
        (lam / 3) * ((x + MultiBrownian.W B' s ω' ⟨0, hd⟩) ^ 3 - x ^ 3) := by
    have hfac : c * x + c * MultiBrownian.W B' s ω' ⟨0, hd⟩ =
        c * (x + MultiBrownian.W B' s ω' ⟨0, hd⟩) := by ring
    rw [hfac, mul_pow, mul_pow, ← mul_sub, ← mul_assoc, hc3]
    ring
  rw [hcube]
  ring


/-- Joint continuity of the scaled discrete exponent in `(x, z)`. -/
private lemma continuous_discV1Exp_scaled_pair (N : ℕ) (c s : ℝ) :
    Continuous (fun p : ℝ × (Fin N → ℝ) =>
      discV1Exp N (c ^ 2 * s) (c * p.1) (fun k => c * p.2 k)) := by
  have hp (k : ℕ) : Continuous (fun p : ℝ × (Fin N → ℝ) =>
      ∑ j : Fin N, if (j : ℕ) < k then c * p.2 j else 0) :=
    continuous_finsetSum _ fun j _ => by
      by_cases hj : (j : ℕ) < k
      · simp only [hj]
        exact continuous_const.mul ((continuous_apply j).comp continuous_snd)
      · simp only [hj]
        exact (continuous_const : Continuous fun _ : ℝ × (Fin N → ℝ) => (0 : ℝ))
  have hx : Continuous (fun p : ℝ × (Fin N → ℝ) => c * p.1) :=
    continuous_const.mul continuous_fst
  have hcube : Continuous (fun p : ℝ × (Fin N → ℝ) =>
      (1 / 3 : ℝ) * ((c * p.1 + (∑ j : Fin N, if (j : ℕ) < N then c * p.2 j else 0)) ^ 3
        - (c * p.1) ^ 3)) :=
    continuous_const.mul (((hx.add (hp N)).pow 3).sub (hx.pow 3))
  have hsum1 : Continuous (fun p : ℝ × (Fin N → ℝ) =>
      ∑ k : Fin N, (c * p.1 + (∑ j : Fin N, if (j : ℕ) < (k : ℕ) then c * p.2 j else 0))
        * ((c ^ 2 * s) / (N : ℝ))) :=
    continuous_finsetSum _ fun k _ => (hx.add (hp (k : ℕ))).mul continuous_const
  have hsum4 : Continuous (fun p : ℝ × (Fin N → ℝ) =>
      (1 / 2 : ℝ) * ∑ k : Fin N,
        (c * p.1 + (∑ j : Fin N, if (j : ℕ) < (k : ℕ) then c * p.2 j else 0)) ^ 4
          * ((c ^ 2 * s) / (N : ℝ))) :=
    continuous_const.mul <| continuous_finsetSum _ fun k _ =>
      ((hx.add (hp (k : ℕ))).pow 4).mul continuous_const
  unfold discV1Exp
  convert (hcube.sub hsum1).sub hsum4


private lemma measurable_intervalIntegral_addW_uncurry {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun p : ℝ × Ω => ∫ r in (0 : ℝ)..s, p.1 + MultiBrownian.W B r p.2 k := by
  have hsum : ∀ n : ℕ, Measurable fun p : ℝ × Ω =>
      ∑ i ∈ range (n + 1),
        (p.1 + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) p.2 k) *
          (s / ((n : ℝ) + 1)) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      (measurable_fst.add ((MultiBrownian.W_meas B _ k).comp measurable_snd)).mul_const _
  have hlim : ∀ p : ℝ × Ω, Tendsto (fun n : ℕ =>
      ∑ i ∈ range (n + 1),
        (p.1 + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) p.2 k) *
          (s / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, p.1 + MultiBrownian.W B r p.2 k)) := fun p =>
    tendsto_lebRiemann_of_continuousOn (g := fun r => p.1 + MultiBrownian.W B r p.2 k) hs
      (continuousOn_const.add (continuous_W_coord_v1 B k p.2).continuousOn)
  exact measurable_of_tendsto_metrizable (fun n => hsum n) (tendsto_pi_nhds.mpr hlim)

private lemma measurable_intervalIntegral_addW_pow4_uncurry {d : ℕ} (B : MultiBrownian Ω P d)
    (k : Fin d) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun p : ℝ × Ω => ∫ r in (0 : ℝ)..s, (p.1 + MultiBrownian.W B r p.2 k) ^ 4 := by
  have hsum : ∀ n : ℕ, Measurable fun p : ℝ × Ω =>
      ∑ i ∈ range (n + 1),
        (p.1 + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) p.2 k) ^ 4 *
          (s / ((n : ℝ) + 1)) := fun n =>
    Finset.measurable_sum _ fun i _ =>
      ((measurable_fst.add ((MultiBrownian.W_meas B _ k).comp measurable_snd)).pow_const 4).mul_const _
  have hlim : ∀ p : ℝ × Ω, Tendsto (fun n : ℕ =>
      ∑ i ∈ range (n + 1),
        (p.1 + MultiBrownian.W B ((i : ℝ) * (s / ((n : ℝ) + 1))) p.2 k) ^ 4 *
          (s / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..s, (p.1 + MultiBrownian.W B r p.2 k) ^ 4)) := fun p =>
    tendsto_lebRiemann_of_continuousOn (g := fun r => (p.1 + MultiBrownian.W B r p.2 k) ^ 4) hs
      ((continuousOn_const.add (continuous_W_coord_v1 B k p.2).continuousOn).pow 4)
  exact measurable_of_tendsto_metrizable (fun n => hsum n) (tendsto_pi_nhds.mpr hlim)

/-- Unfolded formula for the scaled exponent, as a function of `(x, ω)`. -/
private lemma counterexampleV1ExponentScaled_uncurry_eq {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (lam s : ℝ) :
    (fun p : ℝ × Ω => counterexampleV1ExponentScaled B hd lam s p.1 p.2) =
      fun p =>
        (lam / 3) * ((p.1 + MultiBrownian.W B s p.2 ⟨0, hd⟩) ^ 3 - p.1 ^ 3)
          - lam * (∫ r in (0 : ℝ)..s, p.1 + MultiBrownian.W B r p.2 ⟨0, hd⟩)
          - (lam ^ 2 / 2) * (∫ r in (0 : ℝ)..s, (p.1 + MultiBrownian.W B r p.2 ⟨0, hd⟩) ^ 4) := by
  funext p; rfl

private lemma measurable_W_coord_snd {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) (s : ℝ) :
    Measurable fun p : ℝ × Ω => MultiBrownian.W B s p.2 ⟨0, hd⟩ :=
  (MultiBrownian.W_meas B s ⟨0, hd⟩).comp measurable_snd

set_option maxHeartbeats 1000000 in
private lemma measurable_counterexampleV1ExponentScaled_explicit {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {lam s : ℝ} (hs : 0 ≤ s) :
    Measurable fun p : ℝ × Ω =>
      (lam / 3) * ((p.1 + MultiBrownian.W B s p.2 ⟨0, hd⟩) ^ 3 - p.1 ^ 3)
        - lam * (∫ r in (0 : ℝ)..s, p.1 + MultiBrownian.W B r p.2 ⟨0, hd⟩)
        - (lam ^ 2 / 2) * (∫ r in (0 : ℝ)..s, (p.1 + MultiBrownian.W B r p.2 ⟨0, hd⟩) ^ 4) := by
  have hW := measurable_W_coord_snd B hd s
  have hI := measurable_intervalIntegral_addW_uncurry B ⟨0, hd⟩ hs
  have hQ := measurable_intervalIntegral_addW_pow4_uncurry B ⟨0, hd⟩ hs
  exact ((((measurable_fst.add hW).pow_const 3).sub (measurable_fst.pow_const 3)).const_mul
      (lam / 3 : ℝ)).sub (hI.const_mul lam) |>.sub (hQ.const_mul (lam ^ 2 / 2))

set_option maxHeartbeats 1000000 in
private lemma measurable_counterexampleV1ExponentScaled_uncurry {d : ℕ} (B : MultiBrownian Ω P d)
    (hd : 0 < d) {lam s : ℝ} (hs : 0 ≤ s) :
    Measurable fun p : ℝ × Ω => counterexampleV1ExponentScaled B hd lam s p.1 p.2 := by
  rw [counterexampleV1ExponentScaled_uncurry_eq]
  exact measurable_counterexampleV1ExponentScaled_explicit B hd hs

/-- Explicit function-composition form used by `measurable_counterexampleV1ExponentScaled_comp`. -/
private lemma counterexampleV1ExponentScaled_comp_eq {d : ℕ} (B' : MultiBrownian Ω P d)
    (hd : 0 < d) (lam s : ℝ) (X : Ω → ℝ) :
    (fun ω => counterexampleV1ExponentScaled B' hd lam s (X ω) ω) =
      (fun p : ℝ × Ω => counterexampleV1ExponentScaled B' hd lam s p.1 p.2) ∘
        (fun ω => (X ω, ω)) := by
  funext ω; rfl

set_option maxHeartbeats 1000000 in
private lemma measurable_counterexampleV1ExponentScaled_comp {d : ℕ} (B' : MultiBrownian Ω P d)
    (hd : 0 < d) {lam s : ℝ} (_hlam : 0 < lam) (hs : 0 < s) {X : Ω → ℝ} (hX : Measurable X) :
    Measurable (fun ω => counterexampleV1ExponentScaled B' hd lam s (X ω) ω) := by
  rw [counterexampleV1ExponentScaled_comp_eq]
  exact (measurable_counterexampleV1ExponentScaled_uncurry B' hd hs.le).comp
    (hX.prodMk measurable_id)

/-! ### Helper 3: Truncated Fubini + DCT step (aggressively split) -/

private noncomputable def shiftIncrVec {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (s : ℝ) (n : ℕ) (ω : Ω) : Fin (n + 1) → ℝ :=
  fun k => wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
    (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω

@[irreducible] private noncomputable def truncDiscV1 (c s : ℝ) (n R : ℕ) (x : ℝ) (z : Fin (n + 1) → ℝ) : ℝ :=
  min (R : ℝ) (Real.exp (discV1Exp (n + 1) (c ^ 2 * s) (c * x) (fun k => c * z k)))

@[irreducible] private noncomputable def truncPhi (c s : ℝ) (n R : ℕ)
    (q : (ℝ × ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  q.1.1 * truncDiscV1 c s n R q.1.2 q.2

private lemma truncDiscV1_nonneg (c s : ℝ) (n R : ℕ) (x : ℝ) (z : Fin (n + 1) → ℝ) :
    0 ≤ truncDiscV1 c s n R x z := by
  unfold truncDiscV1
  exact le_min (Nat.cast_nonneg R) (Real.exp_pos _).le

private lemma truncDiscV1_le_R (c s : ℝ) (n R : ℕ) (x : ℝ) (z : Fin (n + 1) → ℝ) :
    truncDiscV1 c s n R x z ≤ R := by
  unfold truncDiscV1
  exact min_le_left _ _

set_option maxHeartbeats 1000000 in
private lemma continuous_truncDiscV1 (c s : ℝ) (n R : ℕ) :
    Continuous (fun p : ℝ × (Fin (n + 1) → ℝ) => truncDiscV1 c s n R p.1 p.2) := by
  unfold truncDiscV1
  exact continuous_const.min (Real.continuous_exp.comp (continuous_discV1Exp_scaled_pair (n + 1) c s))

private lemma continuous_mul_truncDiscV1 (c s : ℝ) (n R : ℕ) :
    Continuous (fun q : (ℝ × ℝ) × (Fin (n + 1) → ℝ) =>
      q.1.1 * truncDiscV1 c s n R q.1.2 q.2) :=
  (continuous_fst.comp continuous_fst).mul
    ((continuous_truncDiscV1 c s n R).comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

set_option maxHeartbeats 1000000 in
private lemma continuous_truncPhi (c s : ℝ) (n R : ℕ) :
    Continuous (truncPhi c s n R) := by
  unfold truncPhi
  exact continuous_mul_truncDiscV1 c s n R

private lemma measurable_shiftIncrVec {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (s : ℝ) (n : ℕ) : Measurable (shiftIncrVec B' hd s n) :=
  measurable_pi_iff.mpr fun k => measurable_wnnIncr B' ⟨0, hd⟩ _ _

private lemma measurable_MK_Wt_pair {d : ℕ} (B : MultiBrownian Ω P d)
    {t : ℝ} {MK Wt : Ω → ℝ}
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt) :
    Measurable (fun ω => (MK ω, Wt ω)) :=
  (hMK_m.mono ((pathFiltration B).le_ambient t) le_rfl).prodMk
    (hWt_m.mono ((pathFiltration B).le_ambient t) le_rfl)

private lemma measurable_MK_ambient {d : ℕ} (B : MultiBrownian Ω P d)
    {t : ℝ} {MK : Ω → ℝ} (hMK_m : Measurable[(pathFiltration B).σAlg t] MK) :
    Measurable MK :=
  hMK_m.mono ((pathFiltration B).le_ambient t) le_rfl

private lemma measurable_Wt_ambient {d : ℕ} (B : MultiBrownian Ω P d)
    {t : ℝ} {Wt : Ω → ℝ} (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt) :
    Measurable Wt :=
  hWt_m.mono ((pathFiltration B).le_ambient t) le_rfl

private lemma map_MK_Wt_shiftIncrVec_eq_prod {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) {MK Wt : Ω → ℝ} (n : ℕ)
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt) :
    P.map (fun ω => ((MK ω, Wt ω), shiftIncrVec (B.shift t.toNNReal) hd s n ω)) =
      (P.map (fun ω => (MK ω, Wt ω))).prod
        (P.map (shiftIncrVec (B.shift t.toNNReal) hd s n)) :=
  (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_MK_Wt_pair B hMK_m hWt_m).aemeasurable
      (measurable_shiftIncrVec (B.shift t.toNNReal) hd s n).aemeasurable).mp
    (indepFun_pathFiltration_shiftIncrVec B hd ht hs (n + 1) n.succ_pos (hMK_m.prodMk hWt_m))

private lemma norm_MK_truncDiscV1_le {d : ℕ} {B' : MultiBrownian Ω P d} {hd : 0 < d}
    {c s : ℝ} {n K R : ℕ} {MK Wt : Ω → ℝ}
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) (ω : Ω) :
    ‖MK ω * truncDiscV1 c s n R (Wt ω) (shiftIncrVec B' hd s n ω)‖ ≤ (K : ℝ) * (R : ℝ) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hMK_bd ω).1,
    abs_of_nonneg (truncDiscV1_nonneg c s n R _ _)]
  exact mul_le_mul (hMK_bd ω).2 (truncDiscV1_le_R c s n R _ _)
    (truncDiscV1_nonneg c s n R _ _) (Nat.cast_nonneg K)

set_option maxHeartbeats 1000000 in
private lemma integrable_truncPhi {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) {MK Wt : Ω → ℝ} {K : ℕ}
    (n R : ℕ) (c : ℝ)
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt)
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) :
    Integrable (truncPhi c s n R)
      ((P.map (fun ω => (MK ω, Wt ω))).prod
        (P.map (shiftIncrVec (B.shift t.toNNReal) hd s n))) := by
  have hpair := measurable_MK_Wt_pair B hMK_m hWt_m
  have hZ := measurable_shiftIncrVec (B.shift t.toNNReal) hd s n
  have hΦc := continuous_truncPhi c s n R
  have hmap := map_MK_Wt_shiftIncrVec_eq_prod B hd ht hs n hMK_m hWt_m
  rw [← hmap]
  refine (integrable_map_measure hΦc.aestronglyMeasurable
    (hpair.prodMk hZ).aemeasurable).mpr ?_
  refine (integrable_const ((K : ℝ) * (R : ℝ))).mono'
    (hΦc.measurable.comp (hpair.prodMk hZ)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simpa [Function.comp_def, truncPhi] using
    (norm_MK_truncDiscV1_le (B' := B.shift t.toNNReal) (hd := hd)
      (c := c) (s := s) (n := n) (R := R) (Wt := Wt) hMK_bd ω)

private lemma integral_map_truncDiscV1 {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (c s : ℝ) (n R : ℕ) (x : ℝ) :
    ∫ z, truncDiscV1 c s n R x z ∂(P.map (shiftIncrVec B' hd s n)) =
      ∫ ω', truncDiscV1 c s n R x (shiftIncrVec B' hd s n ω') ∂P :=
  (integral_map (μ := P) (measurable_shiftIncrVec B' hd s n).aemeasurable
    (f := fun z => truncDiscV1 c s n R x z)
    ((continuous_truncDiscV1 c s n R).comp
      ((continuous_const : Continuous fun _ => x).prodMk continuous_id)).aestronglyMeasurable)

private lemma integral_truncPhi_fiber {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (c s : ℝ) (n R : ℕ) (a b : ℝ) :
    ∫ z, truncPhi c s n R ((a, b), z) ∂(P.map (shiftIncrVec B' hd s n)) =
      a * ∫ z, truncDiscV1 c s n R b z ∂(P.map (shiftIncrVec B' hd s n)) := by
  have hΦ : (fun z => truncPhi c s n R ((a, b), z)) =
      fun z => a * truncDiscV1 c s n R b z := by
    unfold truncPhi; rfl
  rw [hΦ, integral_const_mul]


private lemma aestronglyMeasurable_truncDiscV1_fiber {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (c s : ℝ) (n R : ℕ) (x : ℝ) :
    AEStronglyMeasurable (fun ω' => truncDiscV1 c s n R x (shiftIncrVec B' hd s n ω')) P :=
  ((continuous_truncDiscV1 c s n R).measurable.comp
    (measurable_const.prodMk (measurable_shiftIncrVec B' hd s n))).aestronglyMeasurable

private lemma norm_truncDiscV1_le_R (c s : ℝ) (n R : ℕ) (x : ℝ) (z : Fin (n + 1) → ℝ) :
    ‖truncDiscV1 c s n R x z‖ ≤ R := by
  rw [Real.norm_of_nonneg (truncDiscV1_nonneg c s n R x z)]
  exact truncDiscV1_le_R c s n R x z

set_option maxHeartbeats 1000000 in
private lemma continuous_truncDiscV1_in_x (c s : ℝ) (n R : ℕ) (z : Fin (n + 1) → ℝ) :
    Continuous (fun x : ℝ => truncDiscV1 c s n R x z) :=
  (continuous_truncDiscV1 c s n R).comp (continuous_id.prodMk continuous_const)

set_option maxHeartbeats 2000000 in
private lemma continuous_integral_truncDiscV1_in_x {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (c s : ℝ) (n R : ℕ) :
    Continuous (fun x : ℝ =>
      ∫ ω', truncDiscV1 c s n R x (shiftIncrVec B' hd s n ω') ∂P) :=
  continuous_of_dominated
    (fun x => aestronglyMeasurable_truncDiscV1_fiber B' hd c s n R x)
    (fun x => ae_of_all _ fun ω' =>
      norm_truncDiscV1_le_R c s n R x (shiftIncrVec B' hd s n ω'))
    (integrable_const _)
    (ae_of_all _ fun ω' =>
      continuous_truncDiscV1_in_x c s n R (shiftIncrVec B' hd s n ω'))

set_option maxHeartbeats 1000000 in
private lemma continuous_integral_truncPhi {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    (c s : ℝ) (n R : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      ∫ z, truncPhi c s n R (p, z) ∂(P.map (shiftIncrVec B' hd s n))) := by
  have hfun :
      (fun p : ℝ × ℝ => ∫ z, truncPhi c s n R (p, z) ∂(P.map (shiftIncrVec B' hd s n))) =
        fun p => p.1 * ∫ ω', truncDiscV1 c s n R p.2
          (shiftIncrVec B' hd s n ω') ∂P := by
    funext p
    rw [integral_truncPhi_fiber B' hd c s n R p.1 p.2,
      integral_map_truncDiscV1 B' hd c s n R p.2]
  rw [hfun]
  exact continuous_fst.mul
    ((continuous_integral_truncDiscV1_in_x B' hd c s n R).comp continuous_snd)

set_option maxHeartbeats 1000000 in
private lemma integral_grid_indep_disintegrate {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {lam t s : ℝ} (_hlam : 0 < lam) (ht : 0 ≤ t) (hs : 0 < s)
    {MK Wt : Ω → ℝ} {K R n : ℕ}
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt)
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) :
    ∫ ω, MK ω * truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R (Wt ω)
        (shiftIncrVec (B.shift t.toNNReal) hd s n ω) ∂P =
      ∫ ω, MK ω * (∫ ω', truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R (Wt ω)
        (shiftIncrVec (B.shift t.toNNReal) hd s n ω') ∂P) ∂P := by
  set B' := B.shift t.toNNReal
  set c : ℝ := lam ^ (1 / 3 : ℝ)
  have hpair := measurable_MK_Wt_pair B hMK_m hWt_m
  have hZ := measurable_shiftIncrVec B' hd s n
  have hΦc := continuous_truncPhi c s n R
  have hmap := map_MK_Wt_shiftIncrVec_eq_prod B hd ht hs n hMK_m hWt_m
  have hΦi := integrable_truncPhi B hd ht hs n R c hMK_m hWt_m hMK_bd
  have hLHS :
      (fun ω => MK ω * truncDiscV1 c s n R (Wt ω) (shiftIncrVec B' hd s n ω)) =
        fun ω => truncPhi c s n R ((MK ω, Wt ω), shiftIncrVec B' hd s n ω) := by
    unfold truncPhi; rfl
  rw [hLHS]
  have hL := integral_map (μ := P) (hpair.prodMk hZ).aemeasurable (f := truncPhi c s n R)
    hΦc.aestronglyMeasurable
  rw [hmap, integral_prod _ hΦi] at hL
  have hinnerc := continuous_integral_truncPhi B' hd c s n R
  rw [← hL, integral_map (μ := P) hpair.aemeasurable hinnerc.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  change ∫ z, truncPhi c s n R ((MK ω, Wt ω), z) ∂(P.map (shiftIncrVec B' hd s n)) = _
  rw [integral_truncPhi_fiber B' hd c s n R (MK ω) (Wt ω),
    integral_map_truncDiscV1 B' hd c s n R (Wt ω)]

set_option maxHeartbeats 1000000 in
private lemma tendsto_truncDiscV1_scaled {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) (R : ℕ) (x : ℝ) (ω' : Ω) :
    Tendsto (fun n : ℕ =>
      truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R x (shiftIncrVec B' hd s n ω')) atTop
      (𝓝 (min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' hd lam s x ω')))) := by
  set c : ℝ := lam ^ (1 / 3 : ℝ)
  unfold truncDiscV1 shiftIncrVec
  change Tendsto (fun n => min (R : ℝ) (Real.exp (discV1Exp (n + 1) (c ^ 2 * s) (c * x)
      (fun k => c * wnnIncr B' ⟨0, hd⟩ ((k : ℝ) * (s / ((n + 1 : ℕ) : ℝ)))
        (((k : ℕ) + 1 : ℕ) * (s / ((n + 1 : ℕ) : ℝ))) ω')))) atTop
    (𝓝 (min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' hd lam s x ω'))))
  exact tendsto_const_nhds.min
    ((Real.continuous_exp.tendsto _).comp (tendsto_discV1Exp_scaled B' hd hlam hs x ω'))

set_option maxHeartbeats 1000000 in
private lemma tendsto_integral_truncDiscV1_inner {d : ℕ} (B' : MultiBrownian Ω P d) (hd : 0 < d)
    {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) (R : ℕ) (x : ℝ) :
    Tendsto (fun n : ℕ =>
      ∫ ω', truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R x (shiftIncrVec B' hd s n ω') ∂P) atTop
      (𝓝 (∫ ω', min (R : ℝ)
        (Real.exp (counterexampleV1ExponentScaled B' hd lam s x ω')) ∂P)) :=
  tendsto_integral_of_dominated_convergence (fun _ => (R : ℝ))
    (fun n => ((continuous_truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R).measurable.comp
      (measurable_const.prodMk (measurable_shiftIncrVec B' hd s n))).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω' => by
      rw [Real.norm_of_nonneg (truncDiscV1_nonneg _ _ _ _ _ _)]; exact truncDiscV1_le_R _ _ _ _ _ _)
    (ae_of_all _ fun ω' => tendsto_truncDiscV1_scaled B' hd hlam hs R x ω')

set_option maxHeartbeats 1000000 in
private lemma tendsto_integral_MK_truncDiscV1 {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {lam t s : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (hs : 0 < s)
    {MK Wt : Ω → ℝ} {K R : ℕ}
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt)
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) :
    Tendsto (fun n : ℕ =>
      ∫ ω, MK ω * truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R (Wt ω)
        (shiftIncrVec (B.shift t.toNNReal) hd s n ω) ∂P) atTop
      (𝓝 (∫ ω, MK ω * min (R : ℝ) (Real.exp
        (counterexampleV1ExponentScaled (B.shift t.toNNReal) hd lam s (Wt ω) ω)) ∂P)) :=
  tendsto_integral_of_dominated_convergence (fun _ => (K : ℝ) * (R : ℝ))
    (fun n => ((measurable_MK_ambient B hMK_m).mul
      ((continuous_truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R).measurable.comp
        ((measurable_Wt_ambient B hWt_m).prodMk
          (measurable_shiftIncrVec (B.shift t.toNNReal) hd s n)))).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω =>
      norm_MK_truncDiscV1_le (B' := B.shift t.toNNReal) (hd := hd) hMK_bd ω)
    (ae_of_all _ fun ω =>
      tendsto_const_nhds.mul
        (tendsto_truncDiscV1_scaled (B.shift t.toNNReal) hd hlam hs R (Wt ω) ω))

private lemma norm_MK_inner_trunc_le {d : ℕ} {B' : MultiBrownian Ω P d} {hd : 0 < d}
    {c s : ℝ} {n K R : ℕ} {MK Wt : Ω → ℝ}
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) (ω : Ω) :
    ‖MK ω * ∫ ω', truncDiscV1 c s n R (Wt ω) (shiftIncrVec B' hd s n ω') ∂P‖ ≤
      (K : ℝ) * (R : ℝ) := by
  have hnn : 0 ≤ ∫ ω', truncDiscV1 c s n R (Wt ω) (shiftIncrVec B' hd s n ω') ∂P :=
    integral_nonneg fun _ => truncDiscV1_nonneg c s n R _ _
  have hleR : ∫ ω', truncDiscV1 c s n R (Wt ω) (shiftIncrVec B' hd s n ω') ∂P ≤ R :=
    (integral_mono_of_nonneg (ae_of_all _ fun _ => truncDiscV1_nonneg c s n R _ _)
      (integrable_const (R : ℝ)) (ae_of_all _ fun _ => truncDiscV1_le_R c s n R _ _)).trans (by simp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hMK_bd ω).1, abs_of_nonneg hnn]
  exact mul_le_mul (hMK_bd ω).2 hleR hnn (Nat.cast_nonneg K)

set_option maxHeartbeats 1000000 in
private lemma tendsto_integral_MK_inner_trunc {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {lam t s : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (hs : 0 < s)
    {MK Wt : Ω → ℝ} {K R : ℕ}
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt)
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) :
    Tendsto (fun n : ℕ =>
      ∫ ω, MK ω * (∫ ω', truncDiscV1 (lam ^ (1 / 3 : ℝ)) s n R (Wt ω)
        (shiftIncrVec (B.shift t.toNNReal) hd s n ω') ∂P) ∂P) atTop
      (𝓝 (∫ ω, MK ω * (∫ ω', min (R : ℝ) (Real.exp
        (counterexampleV1ExponentScaled (B.shift t.toNNReal) hd lam s (Wt ω) ω')) ∂P) ∂P)) :=
  tendsto_integral_of_dominated_convergence (fun _ => (K : ℝ) * (R : ℝ))
    (fun n => ((measurable_MK_ambient B hMK_m).mul
      ((continuous_integral_truncDiscV1_in_x (B.shift t.toNNReal) hd
        (lam ^ (1 / 3 : ℝ)) s n R).measurable.comp
          (measurable_Wt_ambient B hWt_m))).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω =>
      norm_MK_inner_trunc_le (B' := B.shift t.toNNReal) (hd := hd)
        (c := lam ^ (1 / 3 : ℝ)) (s := s) (n := n) (R := R) (Wt := Wt) hMK_bd ω)
    (ae_of_all _ fun ω =>
      tendsto_const_nhds.mul
        (tendsto_integral_truncDiscV1_inner (B.shift t.toNNReal) hd hlam hs R (Wt ω)))

set_option maxHeartbeats 1000000 in
private lemma integral_trunc_indep_disintegrate {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {lam t s : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) (hs : 0 < s)
    {MK Wt : Ω → ℝ} {K R : ℕ}
    (hMK_m : Measurable[(pathFiltration B).σAlg t] MK)
    (hWt_m : Measurable[(pathFiltration B).σAlg t] Wt)
    (hMK_bd : ∀ ω, 0 ≤ MK ω ∧ MK ω ≤ K) :
    ∫ ω, MK ω * min (R : ℝ) (Real.exp
      (counterexampleV1ExponentScaled (B.shift t.toNNReal) hd lam s (Wt ω) ω)) ∂P =
      ∫ ω, MK ω * (∫ ω', min (R : ℝ)
        (Real.exp (counterexampleV1ExponentScaled (B.shift t.toNNReal) hd lam s (Wt ω) ω')) ∂P) ∂P :=
  tendsto_nhds_unique
    (tendsto_integral_MK_truncDiscV1 B hd hlam ht hs hMK_m hWt_m hMK_bd)
    ((tendsto_integral_MK_inner_trunc B hd hlam ht hs hMK_m hWt_m hMK_bd).congr fun n =>
      (integral_grid_indep_disintegrate B hd hlam ht hs hMK_m hWt_m hMK_bd).symm)


/-! ### Main lemma: `condExp_mul_indep_disintegrate` -/

lemma condExp_mul_indep_disintegrate (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {lam t : ℝ} (hlam : 1 ≤ lam)
    (ht : 0 ≤ t) (htT : t < M.T) :
    P[fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
        ((paperSetup B M.hT).W_hat M.T ω)) |
      (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
      fun ω =>
        Real.exp (dualPairing (counterexampleU0 M.hd lam)
          ((paperSetup B M.hT).W_hat t ω)) *
        counterexampleV1 B M.hd (lam ^ (2 / 3 : ℝ) * (M.T - t))
          (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t ω ⟨0, M.hd⟩) := by
  have hlam_pos : 0 < lam := by linarith
  have hlam23_nonneg : 0 ≤ lam ^ (2 / 3 : ℝ) := Real.rpow_nonneg hlam_pos.le _
  set s : ℝ := M.T - t
  have hs : 0 < s := sub_pos.mpr htT
  set B' := B.shift t.toNNReal
  set Mt : Ω → ℝ := fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam) ((paperSetup B M.hT).W_hat t ω))
  set Wt : Ω → ℝ := fun ω => MultiBrownian.W B t ω ⟨0, M.hd⟩
  set v : ℝ → ℝ := fun x => counterexampleV1 B M.hd (lam ^ (2 / 3 : ℝ) * s) (lam ^ (1 / 3 : ℝ) * x)
  -- 1. `signatureFiltration.σAlg t = (pathFiltration B).σAlg t`
  have hfilt : (paperSetup B M.hT).signatureFiltration.σAlg t = (pathFiltration B).σAlg t :=
    signature_filtration_eq_brownian_filtration _ t
  rw [hfilt]
  -- 2. Pathwise split `M_T^(λ) = Mt * exp(counterexampleV1ExponentScaled B' hd lam s Wt)` a.s.
  have hsplit : (fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
        ((paperSetup B M.hT).W_hat M.T ω))) =ᵐ[P]
      fun ω => Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω) := by
    filter_upwards [ae_dualPairing_counterexampleU0_eq B M.hd lam M.hT.le,
      ae_dualPairing_counterexampleU0_eq B M.hd lam ht] with ω hT ht'
    simp only [Mt, Wt]; rw [← Real.exp_add]; congr 1
    change dualPairing (counterexampleU0 M.hd lam) (paperSig2 B 0 M.T ω) =
      dualPairing (counterexampleU0 M.hd lam) (paperSig2 B 0 t ω) +
        counterexampleV1ExponentScaled B' M.hd lam s (MultiBrownian.W B t ω ⟨0, M.hd⟩) ω
    rw [hT, ht']
    simp only [counterexampleV1ExponentScaled]
    have hc1 : ContinuousOn (fun r => MultiBrownian.W B r ω ⟨0, M.hd⟩) (Icc 0 M.T) :=
      (continuous_W_coord_v1 B ⟨0, M.hd⟩ ω).continuousOn
    have hsplit1 : ∫ r in (0 : ℝ)..M.T, MultiBrownian.W B r ω ⟨0, M.hd⟩ =
        (∫ r in (0 : ℝ)..t, MultiBrownian.W B r ω ⟨0, M.hd⟩) +
        (∫ u in (0 : ℝ)..s, (MultiBrownian.W B t ω ⟨0, M.hd⟩ + MultiBrownian.W B' u ω ⟨0, M.hd⟩)) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((hc1.mono (Icc_subset_Icc le_rfl htT.le)).intervalIntegrable_of_Icc ht)
        ((hc1.mono (Icc_subset_Icc ht le_rfl)).intervalIntegrable_of_Icc htT.le)]
      congr 1
      have hTst : t + s = M.T := by simp [s]
      have hIV : (∫ r in t..M.T, MultiBrownian.W B r ω ⟨0, M.hd⟩) =
          ∫ r in (t + 0)..(t + s), MultiBrownian.W B r ω ⟨0, M.hd⟩ := by
        simp [hTst]
      rw [hIV, ← intervalIntegral.integral_comp_add_left
        (fun r => MultiBrownian.W B r ω ⟨0, M.hd⟩) t]
      exact intervalIntegral.integral_congr fun u hu => by
        rw [uIcc_of_le hs.le] at hu
        have hWu : MultiBrownian.W B (t + u) ω ⟨0, M.hd⟩ =
            MultiBrownian.W B t ω ⟨0, M.hd⟩ +
              MultiBrownian.W B' u ω ⟨0, M.hd⟩ := by
          simp [B', W_shift B ht hu.1]
        simpa [hWu]
    have hc4 : ContinuousOn (fun r => MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 4) (Icc 0 M.T) :=
      fun r hr => (hc1 r hr).pow 4
    have hsplit4 : ∫ r in (0 : ℝ)..M.T, (MultiBrownian.W B r ω ⟨0, M.hd⟩) ^ 4 =
        (∫ r in (0 : ℝ)..t, (MultiBrownian.W B r ω ⟨0, M.hd⟩) ^ 4) +
        (∫ u in (0 : ℝ)..s, (MultiBrownian.W B t ω ⟨0, M.hd⟩ + MultiBrownian.W B' u ω ⟨0, M.hd⟩) ^ 4) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((hc4.mono (Icc_subset_Icc le_rfl htT.le)).intervalIntegrable_of_Icc ht)
        ((hc4.mono (Icc_subset_Icc ht le_rfl)).intervalIntegrable_of_Icc htT.le)]
      congr 1
      have hTst : t + s = M.T := by simp [s]
      have hIV : (∫ r in t..M.T, (MultiBrownian.W B r ω ⟨0, M.hd⟩) ^ 4) =
          ∫ r in (t + 0)..(t + s), (MultiBrownian.W B r ω ⟨0, M.hd⟩) ^ 4 := by
        simp [hTst]
      rw [hIV, ← intervalIntegral.integral_comp_add_left
        (fun r => (MultiBrownian.W B r ω ⟨0, M.hd⟩) ^ 4) t]
      exact intervalIntegral.integral_congr fun u hu => by
        rw [uIcc_of_le hs.le] at hu
        have hWu : MultiBrownian.W B (t + u) ω ⟨0, M.hd⟩ =
            MultiBrownian.W B t ω ⟨0, M.hd⟩ +
              MultiBrownian.W B' u ω ⟨0, M.hd⟩ := by
          simp [B', W_shift B ht hu.1]
        simpa [hWu]
    have hWT : MultiBrownian.W B M.T ω ⟨0, M.hd⟩ =
        MultiBrownian.W B t ω ⟨0, M.hd⟩ + MultiBrownian.W B' s ω ⟨0, M.hd⟩ := by
      simp [B', s, W_shift B ht hs.le]
    rw [hsplit1, hsplit4, hWT]; ring
  -- 3. Measurability of `Mt`, `Wt`, `v`, and `ω ↦ counterexampleV1ExponentScaled B' hd lam s (Wt ω) ω`
  have hMt_m : Measurable[(pathFiltration B).σAlg t] Mt := by
    have hM_eq : Mt = fun ω => Real.exp (2 * lam * (paperSig2 B 0 t ω).coeff [firstSpace M.hd, firstSpace M.hd, firstSpace M.hd]
        - lam * (paperSig2 B 0 t ω).coeff [firstSpace M.hd, 0]
        - 12 * lam ^ 2 * (paperSig2 B 0 t ω).coeff
            [firstSpace M.hd, firstSpace M.hd, firstSpace M.hd, firstSpace M.hd, 0]) := funext fun ω => by
      change Real.exp (dualPairing (counterexampleU0 M.hd lam) (paperSig2 B 0 t ω)) = _
      rw [dualPairing_counterexampleU0 M.hd lam]
    rw [hM_eq]
    exact Real.continuous_exp.measurable.comp <|
      ((measurable_const.mul (measurable_paperSig2_coeff_pathFiltration B le_rfl ht le_rfl _)).sub
        (measurable_const.mul (measurable_paperSig2_coeff_pathFiltration B le_rfl ht le_rfl _))).sub
        (measurable_const.mul (measurable_paperSig2_coeff_pathFiltration B le_rfl ht le_rfl _))
  have hMt_amb : Measurable Mt := hMt_m.mono ((pathFiltration B).le_ambient t) le_rfl
  have hWt_m : Measurable[(pathFiltration B).σAlg t] Wt :=
    measurable_W_pathFiltration B ⟨t, ht, le_rfl⟩ ⟨0, M.hd⟩
  have hWt_amb : Measurable Wt := hWt_m.mono ((pathFiltration B).le_ambient t) le_rfl
  have hv_m : Measurable v :=
    (measurable_counterexampleV1 B M.hd (mul_nonneg hlam23_nonneg hs.le)).comp (measurable_const.mul measurable_id)
  have hg_m : Measurable[(pathFiltration B).σAlg t] (fun ω => Mt ω * v (Wt ω)) :=
    hMt_m.mul (hv_m.comp hWt_m)
  have hsc_comp_m : Measurable (fun ω => counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω) :=
    measurable_counterexampleV1ExponentScaled_comp B' M.hd hlam_pos hs hWt_amb
  -- 4. Scaling & integrability of the shifted factor at every `x : ℝ`
  have hscale : ∀ x : ℝ,
      ∫ ω', Real.exp (counterexampleV1ExponentScaled B' M.hd lam s x ω') ∂P = v x := fun x => by
    rw [brownian_scaling_shiftedExponent B' M.hd hlam_pos hs.le x,
      counterexampleV1_eq_shift B M.hd ht (mul_nonneg hlam23_nonneg hs.le)]
  have hsc_int : ∀ x : ℝ, Integrable (fun ω' => Real.exp (counterexampleV1ExponentScaled B' M.hd lam s x ω')) P := by
    intro x
    have hB1 := lintegral_exp_shiftedExponent_le_one B M.hd (mul_nonneg hlam23_nonneg hs.le)
      (lam ^ (1 / 3 : ℝ) * x)
    have hiB : Integrable (fun ω' => Real.exp (counterexampleV1Exponent B M.hd (lam ^ (2 / 3 : ℝ) * s)
        (lam ^ (1 / 3 : ℝ) * x) ω')) P :=
      ⟨(measurable_counterexampleV1Exponent B M.hd (mul_nonneg hlam23_nonneg hs.le) _).exp.aestronglyMeasurable, by
        rw [HasFiniteIntegral]; simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
        exact hB1.trans_lt ENNReal.one_lt_top⟩
    have hpos : 0 < v x := integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hiB |>.mpr <| by
      have : Function.support (fun ω' => Real.exp (counterexampleV1Exponent B M.hd (lam ^ (2 / 3 : ℝ) * s)
          (lam ^ (1 / 3 : ℝ) * x) ω')) = Set.univ := by ext ω'; simp [(Real.exp_pos _).ne']
      rw [this, measure_univ]; exact zero_lt_one
    by_contra hni
    have hx := hscale x
    rw [integral_undef hni] at hx
    linarith [hx]
  -- 5. Set-`lintegral` identity on every `S ∈ (pathFiltration B).σAlg t` (MCT over `R` then `K`)
  have hset_lintegral : ∀ S : Set Ω, MeasurableSet[(pathFiltration B).σAlg t] S →
      ∫⁻ ω in S, ENNReal.ofReal (Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)) ∂P =
        ∫⁻ ω in S, ENNReal.ofReal (Mt ω * v (Wt ω)) ∂P := by
    intro S hS
    have hS_amb : MeasurableSet S := (pathFiltration B).le_ambient t S hS
    have hK_lint : ∀ K : ℕ,
        ∫⁻ ω in S, ENNReal.ofReal (min (K : ℝ) (Mt ω) *
          Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)) ∂P =
        ∫⁻ ω in S, ENNReal.ofReal (min (K : ℝ) (Mt ω) * v (Wt ω)) ∂P := fun K => by
      have hinner_MCT : ∀ x, Tendsto (fun R : ℕ =>
          ∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s x ω')) ∂P)
          atTop (𝓝 (v x)) := fun x => by
        rw [← hscale x]
        exact tendsto_integral_of_dominated_convergence _
          (fun R => (measurable_const.min ((measurable_counterexampleV1ExponentScaled B' M.hd hs.le x).exp)).aestronglyMeasurable)
          (hsc_int x)
          (fun R => ae_of_all _ fun ω' => by
            rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]; exact min_le_right _ _)
          (ae_of_all _ fun ω' => tendsto_atTop_of_eventually_const
            (i₀ := ⌈Real.exp (counterexampleV1ExponentScaled B' M.hd lam s x ω')⌉₊) fun R hR =>
              min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR)))
      have hMCT_L := lintegral_tendsto_of_tendsto_of_monotone (μ := P.restrict S)
        (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (K : ℝ) (Mt ω) *
          min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω))))
        (fun R => (((measurable_const.min hMt_amb).mul (measurable_const.min hsc_comp_m.exp)).ennreal_ofReal).aemeasurable)
        (ae_of_all _ fun ω R₁ R₂ h12 => ENNReal.ofReal_le_ofReal <|
          mul_le_mul_of_nonneg_left (min_le_min_right _ (Nat.cast_le.mpr h12))
            (le_min (Nat.cast_nonneg K) (Real.exp_pos _).le))
        (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| tendsto_const_nhds.mul <|
          tendsto_atTop_of_eventually_const
            (i₀ := ⌈Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)⌉₊) fun R hR =>
              min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hR)))
      have hMCT_R := lintegral_tendsto_of_tendsto_of_monotone (μ := P.restrict S)
        (f := fun R : ℕ => fun ω => ENNReal.ofReal (min (K : ℝ) (Mt ω) *
          ∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω')) ∂P))
        (fun R => (((measurable_const.min hMt_amb).mul
          ((continuous_trunc_scaled_integral B' M.hd lam hs.le R).measurable.comp hWt_amb)).ennreal_ofReal).aemeasurable)
        (ae_of_all _ fun ω R₁ R₂ h12 => ENNReal.ofReal_le_ofReal <|
          mul_le_mul_of_nonneg_left
            (integral_mono_of_nonneg (ae_of_all _ fun _ => le_min (Nat.cast_nonneg R₁) (Real.exp_pos _).le)
              ((integrable_const (R₂ : ℝ)).mono'
                (measurable_const.min ((measurable_counterexampleV1ExponentScaled B' M.hd hs.le _).exp)).aestronglyMeasurable
                (ae_of_all _ fun _ => by rw [Real.norm_of_nonneg (le_min (Nat.cast_nonneg R₂) (Real.exp_pos _).le)]; exact min_le_left _ _))
              (ae_of_all _ fun _ => min_le_min_right _ (Nat.cast_le.mpr h12)))
            (le_min (Nat.cast_nonneg K) (Real.exp_pos _).le))
        (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| tendsto_const_nhds.mul (hinner_MCT (Wt ω)))
      refine tendsto_nhds_unique hMCT_L (hMCT_R.congr fun R => ?_)
      have hMK_bd : ∀ ω, 0 ≤ S.indicator (fun ω => min (K : ℝ) (Mt ω)) ω ∧
          S.indicator (fun ω => min (K : ℝ) (Mt ω)) ω ≤ K := fun ω => by
        by_cases hω : ω ∈ S
        · simp only [Set.indicator, hω, ↓reduceIte]
          exact ⟨le_min (Nat.cast_nonneg K) (Real.exp_pos _).le, min_le_left _ _⟩
        · simp only [Set.indicator, hω, ↓reduceIte]
          exact ⟨le_rfl, Nat.cast_nonneg K⟩
      have hKR := integral_trunc_indep_disintegrate B M.hd hlam_pos ht hs
        ((measurable_const.min hMt_m).indicator hS) hWt_m hMK_bd (R := R)
      have hL_eq : ∫⁻ ω in S, ENNReal.ofReal (min (K : ℝ) (Mt ω) *
            min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω))) ∂P =
          ENNReal.ofReal (∫ ω, S.indicator (fun ω => min (K : ℝ) (Mt ω)) ω *
            min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)) ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal, ← lintegral_indicator hS_amb]
        · congr 1; funext ω; by_cases hω : ω ∈ S <;> simp [hω]
        · exact (integrable_const ((K : ℝ) * (R : ℝ))).mono'
            (((measurable_const.min hMt_amb).indicator hS_amb).mul
              (measurable_const.min hsc_comp_m.exp)).aestronglyMeasurable
            (ae_of_all _ fun ω => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hMK_bd ω).1,
                abs_of_nonneg (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)]
              exact mul_le_mul (hMK_bd ω).2 (min_le_left _ _) (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)
                (Nat.cast_nonneg K))
        · exact ae_of_all _ fun ω => mul_nonneg (hMK_bd ω).1 (le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)
      have hR_eq : ∫⁻ ω in S, ENNReal.ofReal (min (K : ℝ) (Mt ω) *
            ∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω')) ∂P) ∂P =
          ENNReal.ofReal (∫ ω, S.indicator (fun ω => min (K : ℝ) (Mt ω)) ω *
            (∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω')) ∂P) ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal, ← lintegral_indicator hS_amb]
        · congr 1; funext ω; by_cases hω : ω ∈ S <;> simp [hω]
        · exact (integrable_const ((K : ℝ) * (R : ℝ))).mono'
            (((measurable_const.min hMt_amb).indicator hS_amb).mul
              ((continuous_trunc_scaled_integral B' M.hd lam hs.le R).measurable.comp hWt_amb)).aestronglyMeasurable
            (ae_of_all _ fun ω => by
              have hnn : 0 ≤ ∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω')) ∂P :=
                integral_nonneg fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le
              have hleR : ∫ ω', min (R : ℝ) (Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω')) ∂P ≤ R :=
                (integral_mono_of_nonneg (ae_of_all _ fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)
                  (integrable_const (R : ℝ)) (ae_of_all _ fun _ => min_le_left _ _)).trans (by simp)
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hMK_bd ω).1, abs_of_nonneg hnn]
              exact mul_le_mul (hMK_bd ω).2 hleR hnn (Nat.cast_nonneg K))
        · exact ae_of_all _ fun ω => mul_nonneg (hMK_bd ω).1
            (integral_nonneg fun _ => le_min (Nat.cast_nonneg R) (Real.exp_pos _).le)
      rw [hL_eq, hR_eq, hKR]
    have hMCT_KL := lintegral_tendsto_of_tendsto_of_monotone (μ := P.restrict S)
      (f := fun K : ℕ => fun ω => ENNReal.ofReal (min (K : ℝ) (Mt ω) *
        Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)))
      (fun K => (((measurable_const.min hMt_amb).mul hsc_comp_m.exp).ennreal_ofReal).aemeasurable)
      (ae_of_all _ fun ω K₁ K₂ h12 => ENNReal.ofReal_le_ofReal <|
        mul_le_mul_of_nonneg_right (min_le_min_right _ (Nat.cast_le.mpr h12)) (Real.exp_pos _).le)
      (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| (tendsto_atTop_of_eventually_const
        (i₀ := ⌈Mt ω⌉₊) fun K hK => min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))).mul_const _)
    have hMCT_KR := lintegral_tendsto_of_tendsto_of_monotone (μ := P.restrict S)
      (f := fun K : ℕ => fun ω => ENNReal.ofReal (min (K : ℝ) (Mt ω) * v (Wt ω)))
      (fun K => (((measurable_const.min hMt_amb).mul (hv_m.comp hWt_amb)).ennreal_ofReal).aemeasurable)
      (ae_of_all _ fun ω K₁ K₂ h12 => ENNReal.ofReal_le_ofReal <|
        mul_le_mul_of_nonneg_right (min_le_min_right _ (Nat.cast_le.mpr h12))
          (integral_nonneg fun _ => (Real.exp_pos _).le))
      (ae_of_all _ fun ω => ENNReal.tendsto_ofReal <| (tendsto_atTop_of_eventually_const
        (i₀ := ⌈Mt ω⌉₊) fun K hK => min_eq_right ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))).mul_const _)
    exact tendsto_nhds_unique hMCT_KL (hMCT_KR.congr fun K => (hK_lint K).symm)
  -- 6. Integrability of LHS and RHS + `ae_eq_condExp_of_forall_setIntegral_eq`
  have hLHS_int : Integrable (fun ω => Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)) P := by
    have hT_ae : (fun ω => Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)) =ᵐ[P]
        fun ω => Real.exp (counterexampleV1ExponentScaled B M.hd lam M.T 0 ω) := by
      filter_upwards [hsplit.symm, ae_dualPairing_counterexampleU0_eq B M.hd lam M.hT.le] with ω h1 h2
      rw [h1]; change Real.exp (dualPairing (counterexampleU0 M.hd lam) (paperSig2 B 0 M.T ω)) = _
      rw [h2]; simp [counterexampleV1ExponentScaled]
    have hsc := brownian_scaling_shiftedExponent B M.hd hlam_pos M.hT.le 0
    have hB1 := lintegral_exp_shiftedExponent_le_one B M.hd (mul_nonneg hlam23_nonneg M.hT.le) 0
    have hiB : Integrable (fun ω => Real.exp (counterexampleV1Exponent B M.hd (lam ^ (2 / 3 : ℝ) * M.T) 0 ω)) P :=
      ⟨(measurable_counterexampleV1Exponent B M.hd (mul_nonneg hlam23_nonneg M.hT.le) 0).exp.aestronglyMeasurable, by
        rw [HasFiniteIntegral]; simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
        exact hB1.trans_lt ENNReal.one_lt_top⟩
    have hpos : 0 < counterexampleV1 B M.hd (lam ^ (2 / 3 : ℝ) * M.T) (lam ^ (1 / 3 : ℝ) * 0) := by
      simp only [mul_zero]
      exact integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hiB |>.mpr <| by
        have : Function.support (fun ω => Real.exp (counterexampleV1Exponent B M.hd (lam ^ (2 / 3 : ℝ) * M.T) 0 ω)) =
            Set.univ := by ext ω; simp [(Real.exp_pos _).ne']
        rw [this, measure_univ]; exact zero_lt_one
    have hiS : Integrable (fun ω => Real.exp (counterexampleV1ExponentScaled B M.hd lam M.T 0 ω)) P := by
      by_contra hni; rw [integral_undef hni] at hsc; linarith
    exact hiS.congr hT_ae.symm
  have hRHS_int : Integrable (fun ω => Mt ω * v (Wt ω)) P := by
    refine ⟨(hg_m.mono ((pathFiltration B).le_ambient t) le_rfl).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hnn : ∀ ω, 0 ≤ Mt ω * v (Wt ω) := fun ω =>
      mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
    simp_rw [Real.enorm_eq_ofReal (hnn _)]
    have huniv := hset_lintegral Set.univ MeasurableSet.univ
    simp only [Measure.restrict_univ] at huniv
    rw [← huniv]
    have hf : ∫⁻ ω, ‖Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)‖ₑ ∂P < ∞ :=
      hasFiniteIntegral_iff_enorm.mp hLHS_int.hasFiniteIntegral
    have hf_eq : (fun ω => ‖Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)‖ₑ) =
        fun ω => ENNReal.ofReal (Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω)) :=
      funext fun ω => Real.enorm_eq_ofReal (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    rw [hf_eq] at hf
    exact hf
  refine (condExp_congr_ae (m := (pathFiltration B).σAlg t) hsplit).trans ?_
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration B).le_ambient t) hLHS_int
    (fun S _ _ => hRHS_int.integrableOn) (fun S hS _ => ?_) hg_m.aestronglyMeasurable).symm
  have hnnL : ∀ ω, 0 ≤ Mt ω * Real.exp (counterexampleV1ExponentScaled B' M.hd lam s (Wt ω) ω) := fun ω =>
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hnnR : ∀ ω, 0 ≤ Mt ω * v (Wt ω) := fun ω =>
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  rw [← ENNReal.toReal_ofReal (setIntegral_nonneg ((pathFiltration B).le_ambient t S hS) fun ω _ => hnnR ω),
    ← ENNReal.toReal_ofReal (setIntegral_nonneg ((pathFiltration B).le_ambient t S hS) fun ω _ => hnnL ω),
    ofReal_integral_eq_lintegral_ofReal hRHS_int.integrableOn (ae_of_all _ hnnR),
    ofReal_integral_eq_lintegral_ofReal hLHS_int.integrableOn (ae_of_all _ hnnL),
    hset_lintegral S hS]

end SignatureVolatility

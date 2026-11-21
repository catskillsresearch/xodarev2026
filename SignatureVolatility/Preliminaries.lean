import Mathlib
open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

lemma finset_sum_mul_sq_le {α : Type*} (s : Finset α) (f g : α → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

lemma abs_finset_sum_mul_le_sqrt {α : Type*} (s : Finset α) (f g : α → ℝ) :
    |∑ i ∈ s, f i * g i| ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hf : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_mul hf, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (finset_sum_mul_sq_le s f g)

lemma sqrt_sum_add_sq_le {α : Type*} (s : Finset α) (f g : α → ℝ) :
    Real.sqrt (∑ i ∈ s, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hf : 0 ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) := Real.sqrt_nonneg _
  have hg : 0 ≤ Real.sqrt (∑ i ∈ s, g i ^ 2) := Real.sqrt_nonneg _
  have hsum_f : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum_g : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : ∑ i ∈ s, f i * g i ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) :=
    (le_abs_self _).trans (abs_finset_sum_mul_le_sqrt s f g)
  have hsq : ∑ i ∈ s, (f i + g i) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2 := by
    calc
      ∑ i ∈ s, (f i + g i) ^ 2
          = (∑ i ∈ s, f i ^ 2) + 2 * (∑ i ∈ s, f i * g i) + (∑ i ∈ s, g i ^ 2) := by
            have hexp : ∀ i, (f i + g i) ^ 2 = f i ^ 2 + 2 * (f i * g i) + g i ^ 2 :=
              fun _ => by ring
            simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) ^ 2 +
            2 * (Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2)) +
            Real.sqrt (∑ i ∈ s, g i ^ 2) ^ 2 := by
            rw [Real.sq_sqrt hsum_f, Real.sq_sqrt hsum_g]
            linarith
      _ = (Real.sqrt (∑ i ∈ s, f i ^ 2) + Real.sqrt (∑ i ∈ s, g i ^ 2)) ^ 2 := by ring
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (add_nonneg hf hg))

lemma sqrt_sum_finset_sum_sq_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (F : β → α → ℝ) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ t, F k i) ^ 2) ≤
      ∑ k ∈ t, Real.sqrt (∑ i ∈ s, (F k i) ^ 2) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert b t hb ih =>
    have hrew : (∑ i ∈ s, (∑ k ∈ insert b t, F k i) ^ 2) =
        ∑ i ∈ s, (F b i + ∑ k ∈ t, F k i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_insert hb]
    rw [hrew, Finset.sum_insert hb]
    refine (sqrt_sum_add_sq_le s (F b) (fun i => ∑ k ∈ t, F k i)).trans ?_
    simpa [add_comm] using
      add_le_add_left ih (Real.sqrt (∑ i ∈ s, (F b i) ^ 2))

lemma sum_sq_le_sq_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hmul : 0 ≤ 2 * f a * (∑ i ∈ s, f i) := by positivity
    nlinarith

lemma cauchy_range_sum_le (N : ℕ) (u v : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (hv : ∀ j, 0 ≤ v j) :
    (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), u k * v (n - k)) ≤
      (∑ k ∈ Finset.range N, u k) * (∑ j ∈ Finset.range N, v j) := by
  let g : ℕ → ℕ → ℝ := fun k n => if k ≤ n then u k * v (n - k) else 0
  have h1 : (∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (n + 1), u k * v (n - k)) =
      ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range N, g k n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnN : n + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    symm
    rw [← Finset.sum_subset (Finset.range_mono hnN)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [g, hkn]
    · intro k _ hknot
      have hnot : ¬ k ≤ n := fun hle => hknot (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [g, hnot]
  rw [h1, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkN : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
  have hsplit : N = k + (N - k) := (Nat.add_sub_of_le hkN).symm
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hzero : ∑ x ∈ Finset.range k, g k x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hnot : ¬ k ≤ x := Nat.not_le_of_gt (Finset.mem_range.mp hx)
    simp [g, hnot]
  rw [hzero, zero_add]
  have htail : ∑ x ∈ Finset.range (N - k), g k (k + x) =
      u k * ∑ x ∈ Finset.range (N - k), v x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [g]
  rw [htail]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N k))
      fun j _ _ => hv j) (hu k)

lemma abs_tsum_le_of_summable_abs {f : ℕ → ℝ} (habs : Summable (fun n => |f n|)) :
    |∑' n, f n| ≤ ∑' n, |f n| := by
  have hf : Summable f := habs.of_abs
  have htend1 : Tendsto (fun N => |∑ n ∈ Finset.range N, f n|) atTop (𝓝 |∑' n, f n|) :=
    hf.hasSum.tendsto_sum_nat.abs
  have htend2 : Tendsto (fun N => ∑ n ∈ Finset.range N, |f n|) atTop (𝓝 (∑' n, |f n|)) :=
    habs.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto htend1 htend2
    (Eventually.of_forall fun N => Finset.abs_sum_le_sum_abs f (Finset.range N))

lemma gronwall_zero_of_continuousOn {f : ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hcont : ContinuousOn f (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ K * ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  have hcomp : IsCompact (Icc (0 : ℝ) T) := isCompact_Icc
  have hne : (Icc (0 : ℝ) T).Nonempty := nonempty_Icc.mpr hT
  obtain ⟨t_max, ht_max, hmax⟩ := hcomp.exists_isMaxOn hne hcont
  let B : ℝ := max (f t_max) 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hfB : ∀ t ∈ Icc 0 T, f t ≤ B := fun t ht => (hmax ht).trans (le_max_left _ _)
  have hiter : ∀ (n : ℕ), ∀ t ∈ Icc 0 T, f t ≤ B * ((K * t) ^ n / (n.factorial : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simpa using hfB t ht
    | succ n ih =>
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
      have hf_int : IntervalIntegrable f volume 0 t :=
        (hcont.mono hsub).intervalIntegrable_of_Icc ht0
      let g : ℝ → ℝ := fun s => B * K ^ n / (n.factorial : ℝ) * s ^ n
      have hg_cont : ContinuousOn g (Icc 0 t) :=
        (continuous_const.mul (continuous_pow n)).continuousOn
      have hg_int : IntervalIntegrable g volume 0 t := hg_cont.intervalIntegrable_of_Icc ht0
      have hfg : ∀ s ∈ Icc 0 t, f s ≤ g s := by
        intro s hs
        have hstep := ih s (hsub hs)
        calc
          f s ≤ B * ((K * s) ^ n / (n.factorial : ℝ)) := hstep
          _ = g s := by simp [g, mul_pow]; ring
      have hint_le : ∫ s in (0 : ℝ)..t, f s ≤ ∫ s in (0 : ℝ)..t, g s :=
        intervalIntegral.integral_mono_on ht0 hf_int hg_int hfg
      have hint_g : ∫ s in (0 : ℝ)..t, g s =
          (B * K ^ n / (n.factorial : ℝ)) * (t ^ (n + 1) / (n + 1 : ℝ)) := by
        simp only [g, intervalIntegral.integral_const_mul, integral_pow]
        simp
      calc
        f t ≤ K * ∫ s in (0 : ℝ)..t, f s := hbound t ht
        _ ≤ K * ∫ s in (0 : ℝ)..t, g s := mul_le_mul_of_nonneg_left hint_le hK
        _ = K * ((B * K ^ n / (n.factorial : ℝ)) * (t ^ (n + 1) / (n + 1 : ℝ))) := by rw [hint_g]
        _ = B * ((K * t) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ,
            mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  intro t ht
  have htend : Tendsto (fun n : ℕ => B * ((K * t) ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      tendsto_const_nhds.mul (Real.summable_pow_div_factorial (K * t)).tendsto_atTop_zero
  have hle0 : f t ≤ 0 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds : Tendsto (fun _ : ℕ => f t) atTop (𝓝 (f t)))
      htend (Eventually.of_forall fun n => hiter n t ht)
  exact le_antisymm hle0 (hnonneg t ht)

lemma not_top_le_coe (n : ℕ) (h : (⊤ : ℕ∞) ≤ (n : ℕ∞)) : False :=
  not_le_of_gt (WithTop.coe_lt_top n) h

end SignatureVolatility

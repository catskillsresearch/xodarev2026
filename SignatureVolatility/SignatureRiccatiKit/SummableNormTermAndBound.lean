module

public import SignatureVolatility.SignatureRiccatiKit.CondSigPoly
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.ProlongedBrownianSetup.StratItoCoeffBounds
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# C1b. Contraction-preimage bound: `∑_I ‖P_{I,t}(z)‖` is of exponential type `≤ 1`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma list_norm_sum_le {E : Type*} [SeminormedAddCommGroup E] :
    ∀ L : List E, ‖L.sum‖ ≤ (L.map norm).sum
  | [] => by simp
  | x :: L => by
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le x L.sum).trans (add_le_add le_rfl (list_norm_sum_le L))

private lemma list_sum_map_le {α : Type*} {f g : α → ℝ} :
    ∀ L : List α, (∀ x ∈ L, f x ≤ g x) → (L.map f).sum ≤ (L.map g).sum
  | [], _ => le_rfl
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self)
      (list_sum_map_le L fun y hy => h y (List.mem_cons_of_mem x hy))

private lemma countOnes_le_length' {d : ℕ} (hd : 0 < d) :
    ∀ J : Word (d + 1), countOnes hd J ≤ J.length
  | [] => le_rfl
  | j :: J => by
    have := countOnes_le_length' hd J
    simp only [countOnes, List.length_cons]
    split_ifs <;> omega

/-- Level-`n` sum of `∑_{(c,J) ∈ contractions I} c * F J` over all words `I` of length `n`. -/
private def contrSum {d : ℕ} (n : ℕ) (F : Word (d + 1) → ℝ) : ℝ :=
  ∑ I ∈ wordsOfLength (d + 1) n, ((contractions I).map fun p => p.1 * F p.2).sum

private lemma contrSum_zero {d : ℕ} (F : Word (d + 1) → ℝ) : contrSum 0 F = F [] := by
  simp [contrSum, wordsOfLength, contractions]

private lemma contrSum_one {d : ℕ} (F : Word (d + 1) → ℝ) :
    contrSum 1 F = ∑ a : Fin (d + 1), F [a] := by
  unfold contrSum
  rw [wordsOfLength.succ]
  simp [wordsOfLength, contractions]

private lemma contrSum_const_mul {d : ℕ} (n : ℕ) (c : ℝ) (F : Word (d + 1) → ℝ) :
    contrSum n (fun w => c * F w) = c * contrSum n F := by
  unfold contrSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [show List.map (fun p => p.1 * (fun w => c * F w) p.2) (contractions I) =
        List.map (fun p => c * (p.1 * F p.2)) (contractions I) from
      List.map_congr_left fun p _ => by ring,
    List.sum_map_mul_left]

/-- Two-step recurrence for `contrSum`: either keep the first letter `a`, or contract an equal
spatial pair `(k.succ, k.succ)` (`d` choices, weight `1/2`) into `0`. -/
private lemma contrSum_add_two {d : ℕ} (n : ℕ) (F : Word (d + 1) → ℝ) :
    contrSum (n + 2) F =
      (∑ a : Fin (d + 1), contrSum (n + 1) (fun w => F (a :: w))) +
        ((d : ℝ) / 2) * contrSum n (fun w => F ((0 : Letter (d + 1)) :: w)) := by
  unfold contrSum
  rw [wordsOfLength.succ (n + 1)]
  simp_rw [contractions_cons, List.map_append, List.sum_append, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun K _ => ?_
    rw [List.map_map]; rfl
  · simp_rw [wordsOfLength.succ n]
    rw [Fin.sum_univ_succ]
    have h0 : ∑ b : Fin (d + 1), ∑ K' ∈ wordsOfLength (d + 1) n,
        ((if (b :: K').head? = some (0 : Fin (d + 1)) ∧ ((0 : Fin (d + 1)) : ℕ) ≠ 0 then
          (contractions (b :: K').tail).map fun p => (p.1 / 2, (0 : Fin (d + 1)) :: p.2)
         else []).map fun p => p.1 * F p.2).sum = 0 := by
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun K' _ => by simp
    rw [h0, zero_add]
    have hterm : ∀ k : Fin d,
        ∑ b : Fin (d + 1), ∑ K' ∈ wordsOfLength (d + 1) n,
          ((if (b :: K').head? = some k.succ ∧ ((k.succ : Fin (d + 1)) : ℕ) ≠ 0 then
            (contractions (b :: K').tail).map fun p => (p.1 / 2, (0 : Fin (d + 1)) :: p.2)
           else []).map fun p => p.1 * F p.2).sum =
        (1 / 2 : ℝ) * ∑ K' ∈ wordsOfLength (d + 1) n,
          ((contractions K').map fun p => p.1 * F ((0 : Letter (d + 1)) :: p.2)).sum := by
      intro k
      rw [Finset.sum_eq_single k.succ]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun K' _ => ?_
        have hcond : (k.succ :: K').head? = some k.succ ∧ ((k.succ : Fin (d + 1)) : ℕ) ≠ 0 :=
          ⟨rfl, Nat.succ_ne_zero k.1⟩
        rw [ite_eq_left_iff.mpr (fun hc => absurd hcond hc)]
        simp only [List.tail_cons, List.map_map]
        rw [show List.map ((fun p => p.1 * F p.2) ∘ fun p => (p.1 / 2, (0 : Letter (d + 1)) :: p.2))
              (contractions K') =
            List.map (fun p => (1 / 2 : ℝ) * (p.1 * F ((0 : Letter (d + 1)) :: p.2)))
              (contractions K') from
          List.map_congr_left fun p _ => by dsimp [Function.comp]; ring,
          List.sum_map_mul_left]
      · intro b _ hb
        refine Finset.sum_eq_zero fun K' _ => ?_
        have hnc : ¬ ((b :: K').head? = some k.succ ∧ ((k.succ : Fin (d + 1)) : ℕ) ≠ 0) := by
          rintro ⟨h1, _⟩; exact hb (Option.some.inj h1)
        rw [ite_eq_right_iff.mpr (fun hc => absurd hc hnc)]
        simp
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-- Target weight supported on words of length `m` in `{0, l₁}^m`. -/
private def targetWt {d : ℕ} (hd : 0 < d) (m : ℕ) (A B : ℝ) (J : Word (d + 1)) : ℝ :=
  if J.length = m ∧ onlyZeroOrOne hd J = true then
    A ^ (m - countOnes hd J) * B ^ (countOnes hd J)
  else 0

private lemma targetWt_cons {d : ℕ} (hd : 0 < d) (m : ℕ) (A B : ℝ)
    (a : Letter (d + 1)) (w : Word (d + 1)) :
    targetWt hd (m + 1) A B (a :: w) =
      if a = 0 then A * targetWt hd m A B w
      else if a = firstSpace hd then B * targetWt hd m A B w
      else 0 := by
  have h0ne : (0 : Letter (d + 1)) ≠ firstSpace hd := (firstSpace_ne_zero hd).symm
  by_cases ha0 : a = 0
  · subst ha0
    have hL : targetWt hd (m + 1) A B (0 :: w) =
        if w.length = m ∧ onlyZeroOrOne hd w = true then
          A ^ (m + 1 - countOnes hd w) * B ^ (countOnes hd w)
        else 0 := by
      simp only [targetWt, List.length_cons, Nat.add_right_cancel_iff, onlyZeroOrOne,
        decide_true, Bool.true_or, Bool.true_and, countOnes, h0ne, ite_false, zero_add]
    rw [hL, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    unfold targetWt
    by_cases hcond : w.length = m ∧ onlyZeroOrOne hd w = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd hcond h),
        ite_eq_left_iff.mpr (fun h => absurd hcond h)]
      rw [Nat.succ_sub (hcond.1 ▸ countOnes_le_length' hd w), pow_succ]; ring
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hcond),
        ite_eq_right_iff.mpr (fun h => absurd h hcond), mul_zero]
  · by_cases ha1 : a = firstSpace hd
    · subst ha1
      have hL : targetWt hd (m + 1) A B (firstSpace hd :: w) =
          if w.length = m ∧ onlyZeroOrOne hd w = true then
            A ^ (m - countOnes hd w) * B ^ (1 + countOnes hd w)
          else 0 := by
        simp only [targetWt, List.length_cons, Nat.add_right_cancel_iff, onlyZeroOrOne,
          decide_true, Bool.or_true, Bool.true_and, countOnes, ite_true]
        split_ifs
        · rw [show m + 1 - (1 + countOnes hd w) = m - countOnes hd w by
            rw [Nat.add_comm m 1, Nat.add_sub_add_left]]
        · rfl
      rw [hL, ite_eq_right_iff.mpr (fun h => absurd h ha0),
        ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      unfold targetWt
      by_cases hcond : w.length = m ∧ onlyZeroOrOne hd w = true
      · rw [ite_eq_left_iff.mpr (fun h => absurd hcond h),
          ite_eq_left_iff.mpr (fun h => absurd hcond h)]
        rw [pow_add, pow_one]; ring
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hcond),
          ite_eq_right_iff.mpr (fun h => absurd h hcond), mul_zero]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h ha0),
        ite_eq_right_iff.mpr (fun h => absurd h ha1)]
      simp [targetWt, onlyZeroOrOne, ha0, ha1]

private lemma contrSum_targetWt_eq_zero_of_gt {d : ℕ} (hd : 0 < d) {m n : ℕ} (hgt : 2 * m < n)
    (A B : ℝ) : contrSum n (targetWt hd m A B) = 0 := by
  unfold contrSum
  refine Finset.sum_eq_zero fun I hI => ?_
  have hlen := wordsOfLength.mem.mp hI
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have hle := (mem_contractions hp).2.2.2
  have hne : p.2.length ≠ m := by omega
  simp [targetWt, hne]

/-- Exact closed form: `∑_{n=0}^{2m} contrSum n (targetWt hd m A B) = ((1 + d/2) A + B)^m`. -/
private lemma sum_contrSum_targetWt {d : ℕ} (hd : 0 < d) (A B : ℝ) :
    ∀ m : ℕ, ∑ n ∈ Finset.range (2 * m + 1), contrSum n (targetWt hd m A B) =
      ((1 + (d : ℝ) / 2) * A + B) ^ m
  | 0 => by simp [contrSum_zero, targetWt, onlyZeroOrOne, countOnes]
  | m + 1 => by
    have ih := sum_contrSum_targetWt hd A B m
    have h0ne : (0 : Letter (d + 1)) ≠ firstSpace hd := (firstSpace_ne_zero hd).symm
    have hhead : ∀ k : ℕ,
        ∑ a : Fin (d + 1), contrSum k (fun w => targetWt hd (m + 1) A B (a :: w)) =
          (A + B) * contrSum k (targetWt hd m A B) := fun k => by
      have hterm : ∀ a : Fin (d + 1),
          contrSum k (fun w => targetWt hd (m + 1) A B (a :: w)) =
            if a = 0 then A * contrSum k (targetWt hd m A B)
            else if a = firstSpace hd then B * contrSum k (targetWt hd m A B)
            else 0 := fun a => by
        simp_rw [targetWt_cons]
        by_cases ha0 : a = 0
        · simp only [ha0, ite_true]; exact contrSum_const_mul k A _
        · by_cases ha1 : a = firstSpace hd
          · simp only [ha1, ite_true]; exact contrSum_const_mul k B _
          · simp [ha0, ha1, contrSum]
      simp_rw [hterm]
      rw [Finset.sum_eq_add_of_mem (0 : Fin (d + 1)) (firstSpace hd)
        (Finset.mem_univ _) (Finset.mem_univ _) h0ne]
      · simp only [ite_true, ite_false, h0ne.symm]; ring
      · intro a _ ⟨ha0, ha1⟩; simp [ha0, ha1]
    have hS0 : contrSum 0 (targetWt hd (m + 1) A B) = 0 := by simp [contrSum_zero, targetWt]
    have hS1 : contrSum 1 (targetWt hd (m + 1) A B) = (A + B) * contrSum 0 (targetWt hd m A B) := by
      have h0 := hhead 0
      simp only [contrSum_zero] at h0 ⊢
      rw [contrSum_one]
      exact h0
    have hS2 : ∀ k : ℕ, contrSum (k + 2) (targetWt hd (m + 1) A B) =
        (A + B) * contrSum (k + 1) (targetWt hd m A B) +
          ((d : ℝ) / 2) * A * contrSum k (targetWt hd m A B) := fun k => by
      rw [contrSum_add_two, hhead (k + 1)]
      have h0step : contrSum k (fun w => targetWt hd (m + 1) A B ((0 : Letter (d + 1)) :: w)) =
          A * contrSum k (targetWt hd m A B) := by
        have hfun : (fun w => targetWt hd (m + 1) A B ((0 : Letter (d + 1)) :: w)) =
            fun w => A * targetWt hd m A B w := by
          funext w; rw [targetWt_cons]; simp
        rw [hfun]
        exact contrSum_const_mul k A _
      rw [h0step]; ring
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
      Finset.sum_range_succ', Finset.sum_range_succ', hS0, hS1]
    simp_rw [hS2, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hshift : contrSum 0 (targetWt hd m A B) +
        ∑ k ∈ Finset.range (2 * m + 1), contrSum (k + 1) (targetWt hd m A B) =
        ∑ k ∈ Finset.range (2 * m + 1), contrSum k (targetWt hd m A B) := by
      have h := Finset.sum_range_succ' (fun k => contrSum k (targetWt hd m A B)) (2 * m + 1)
      have htop : contrSum (2 * m + 1) (targetWt hd m A B) = 0 :=
        contrSum_targetWt_eq_zero_of_gt hd (by omega) A B
      rw [Finset.sum_range_succ, htop, add_zero] at h
      linarith
    have hcombine :
        ((A + B) * contrSum 0 (targetWt hd m A B) +
          ((A + B) * ∑ k ∈ Finset.range (2 * m + 1), contrSum (k + 1) (targetWt hd m A B) +
            ((d : ℝ) / 2) * A * ∑ k ∈ Finset.range (2 * m + 1), contrSum k (targetWt hd m A B))) + 0 =
        ((1 + (d : ℝ) / 2) * A + B) * ∑ k ∈ Finset.range (2 * m + 1), contrSum k (targetWt hd m A B) := by
      calc _ = (A + B) * (contrSum 0 (targetWt hd m A B) +
              ∑ k ∈ Finset.range (2 * m + 1), contrSum (k + 1) (targetWt hd m A B)) +
              ((d : ℝ) / 2) * A * ∑ k ∈ Finset.range (2 * m + 1), contrSum k (targetWt hd m A B) := by ring
        _ = _ := by rw [hshift]; ring
    calc _ = ((A + B) * contrSum 0 (targetWt hd m A B) +
            ((A + B) * ∑ k ∈ Finset.range (2 * m + 1), contrSum (k + 1) (targetWt hd m A B) +
              ((d : ℝ) / 2) * A *
                ∑ k ∈ Finset.range (2 * m + 1), contrSum k (targetWt hd m A B))) + 0 := by ring
        _ = _ := by rw [hcombine, ih, pow_succ']

/-- `y ↦ exp(c * y)` is integrable against `gaussianReal 0 1` (by completing the square). -/
private lemma integrable_exp_mul_gaussianReal_zero_one (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * y)) (gaussianReal 0 1) := by
  have hpdf_int : Integrable (gaussianPDFReal 0 1) volume := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) := integrable_const 1
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff_integrable_smul₀' (measurable_gaussianPDF 0 1).aemeasurable
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (ae_of_all _ fun y => ?_)
    simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 y)]
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul₀' (measurable_gaussianPDF 0 1).aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have htr : Integrable (fun y : ℝ => Real.exp (c ^ 2 / 2) * gaussianPDFReal 0 1 (y - c)) volume :=
    (hpdf_int.comp_sub_right c).const_mul (Real.exp (c ^ 2 / 2))
  refine htr.congr (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, gaussianPDF]
  rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 y)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hexp : Real.exp (c ^ 2 / 2) * Real.exp (-(y - c) ^ 2 / 2) =
      Real.exp (-y ^ 2 / 2) * Real.exp (c * y) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp (c ^ 2 / 2) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y - c) ^ 2 / 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (c ^ 2 / 2) * Real.exp (-(y - c) ^ 2 / 2)) := by ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-y ^ 2 / 2) * Real.exp (c * y)) := by rw [hexp]
    _ = Real.exp (c * y) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)) := by ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) * Real.exp (c * y) := by ring

/-- Standalone list-integrability & integral-sum helpers (avoids nested-induction IH shadowing). -/
private lemma integrable_list_contr {d : ℕ} {μ : Measure ℝ} {F : Word (d + 1) → ℝ → ℝ}
    (hF : ∀ J, Integrable (F J) μ) :
    ∀ L : List (ℝ × Word (d + 1)), Integrable (fun y => (L.map fun p => p.1 * F p.2 y).sum) μ
  | [] => by simp
  | p :: L => by
    simp only [List.map_cons, List.sum_cons]
    exact ((hF p.2).const_mul p.1).add (integrable_list_contr hF L)

private lemma integral_list_contr {d : ℕ} {μ : Measure ℝ} {F : Word (d + 1) → ℝ → ℝ}
    (hF : ∀ J, Integrable (F J) μ) :
    ∀ L : List (ℝ × Word (d + 1)),
      ∫ y, (L.map fun p => p.1 * F p.2 y).sum ∂μ =
        (L.map fun p => p.1 * ∫ y, F p.2 y ∂μ).sum
  | [] => by simp
  | p :: L => by
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add ((hF p.2).const_mul p.1) (integrable_list_contr hF L),
      integral_const_mul, integral_list_contr hF L]

/-- **C1b.** -/
lemma summable_norm_term_and_bound {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t)
    {phi : ExtTensorAlgebra (d + 1)} {K : ℝ}
    (hcoeff : ∀ I : Word (d + 1), |phi.coeff I| ≤ K)
    (hG_mgf : ∫ y : ℝ, Real.exp (Real.sqrt t * |y|) ∂(gaussianReal 0 1) ≤
      2 * Real.exp (t / 2))
    (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖∑ I ∈ wordsOfLength (d + 1) n, (phi.coeff I : ℂ) * condSigPoly hd t I z‖) ∧
      ∑' n : ℕ,
          ‖∑ I ∈ wordsOfLength (d + 1) n,
            (phi.coeff I : ℂ) * condSigPoly hd t I z‖ ≤
        (K * (2 * Real.exp (((3 + (d : ℝ)) / 2) * t))) * Real.exp ‖z‖ := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hcoeff [])
  set M : ℝ := (K * (2 * Real.exp (((3 + (d : ℝ)) / 2) * t))) * Real.exp ‖z‖
  have hpart : ∀ N : ℕ,
      ∑ n ∈ Finset.range N,
        ‖∑ I ∈ wordsOfLength (d + 1) n, (phi.coeff I : ℂ) * condSigPoly hd t I z‖ ≤ M := by
    intro N
    have hword : ∀ n ∈ Finset.range N, ∀ I ∈ wordsOfLength (d + 1) n,
        ‖condSigPoly hd t I.reverse z‖ ≤
          ∑ m ∈ Finset.range N,
            ((contractions I).map fun p => p.1 *
              (∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) p.2 ∂(gaussianReal 0 1))).sum /
              (m.factorial : ℝ) := fun n hn I hI => by
      have hIn : I.length < N := by rw [wordsOfLength.mem.mp hI]; exact Finset.mem_range.mp hn
      unfold condSigPoly
      rw [List.reverse_reverse]
      refine (list_norm_sum_le _).trans ?_
      rw [List.map_map]
      have hswap :
          ∑ m ∈ Finset.range N,
            ((contractions I).map fun p => p.1 *
              (∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) p.2 ∂(gaussianReal 0 1))).sum /
              (m.factorial : ℝ) =
          ((contractions I).map fun p =>
            ∑ m ∈ Finset.range N, p.1 *
              (∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) p.2 ∂(gaussianReal 0 1)) /
              (m.factorial : ℝ)).sum := by
        induction contractions I with
        | nil => simp
        | cons p L ih =>
          simp only [List.map_cons, List.sum_cons, add_div, Finset.sum_add_distrib, ih]
      rw [hswap]
      refine list_sum_map_le (contractions I) fun p hp => ?_
      have hp_lt : p.2.length < N := (mem_contractions hp).2.2.1.trans_lt hIn
      have hp1 : 0 ≤ p.1 := (mem_contractions hp).1.le
      rw [Finset.sum_eq_single p.2.length]
      · simp only [Function.comp_apply]
        split_ifs with h01
        · have htw : ∀ y : ℝ, targetWt hd p.2.length t (‖z‖ + Real.sqrt t * |y|) p.2 =
              t ^ (p.2.length - countOnes hd p.2) * (‖z‖ + Real.sqrt t * |y|) ^ (countOnes hd p.2) :=
            fun y => by simp [targetWt, h01]
          simp_rw [htw, integral_const_mul]
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hp1,
            Real.norm_of_nonneg (by positivity)]
          have hH := monicHermite_bound (countOnes hd p.2) ht z
          calc p.1 * (t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ)) *
                ‖hermitePoly (countOnes hd p.2) t z‖
              ≤ p.1 * (t ^ (p.2.length - countOnes hd p.2) / (p.2.length.factorial : ℝ)) *
                (∫ y : ℝ, (‖z‖ + Real.sqrt t * |y|) ^ (countOnes hd p.2) ∂(gaussianReal 0 1)) :=
                mul_le_mul_of_nonneg_left hH (by positivity)
            _ = _ := by ring
        · simp [targetWt, h01]
      · intro m _ hm; simp [targetWt, Ne.symm hm]
      · intro h; exact absurd (Finset.mem_range.mpr hp_lt) h
    -- Integrability helpers for `targetWt` and `contrSum`
    have hint_tw : ∀ m (J : Word (d + 1)),
        Integrable (fun y : ℝ => targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J) (gaussianReal 0 1) := by
      intro m J
      unfold targetWt
      split_ifs
      · have hbase : MemLp (fun y : ℝ => ‖z‖ + Real.sqrt t * |y|) (countOnes hd J : ℕ) (gaussianReal 0 1) :=
          (memLp_const ‖z‖).add
            (((memLp_id_gaussianReal' (μ := 0) (v := 1) (countOnes hd J : ℕ)
              (ENNReal.natCast_ne_top _)).norm).const_mul (Real.sqrt t))
        refine (hbase.integrable_norm_pow'.const_mul (t ^ (m - countOnes hd J))).congr
          (ae_of_all _ fun y => ?_)
        simp only [Real.norm_of_nonneg (by positivity : 0 ≤ ‖z‖ + Real.sqrt t * |y|)]
      · exact integrable_zero _ _ _
    have hint_S : ∀ m n,
        Integrable (fun y : ℝ => contrSum n (fun J => targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J))
          (gaussianReal 0 1) := fun m n =>
      integrable_finsetSum _ fun I _ => integrable_list_contr (hint_tw m) (contractions I)
    have hswap_int : ∀ m n,
        contrSum n (fun J => ∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J ∂(gaussianReal 0 1)) =
          ∫ y : ℝ, contrSum n (fun J => targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J) ∂(gaussianReal 0 1) := by
      intro m n
      unfold contrSum
      rw [integral_finsetSum _ fun I _ => integrable_list_contr (hint_tw m) (contractions I)]
      refine Finset.sum_congr rfl fun I _ => (integral_list_contr (hint_tw m) (contractions I)).symm
    have hS_nn : ∀ m n, 0 ≤ contrSum n (fun J =>
        ∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J ∂(gaussianReal 0 1)) := fun m n => by
      rw [hswap_int m n]
      refine integral_nonneg fun y => Finset.sum_nonneg fun I _ =>
        List.sum_nonneg fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      refine mul_nonneg (mem_contractions hp).1.le ?_
      change 0 ≤ targetWt hd m t (‖z‖ + Real.sqrt t * |y|) p.2
      unfold targetWt; split_ifs <;> positivity
    -- Main chain of inequalities
    have hstep1 :
        ∑ n ∈ Finset.range N,
          ‖∑ I ∈ wordsOfLength (d + 1) n, (phi.coeff I : ℂ) * condSigPoly hd t I z‖ ≤
        K * ∫ y : ℝ, ∑ m ∈ Finset.range N,
          (((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|)) ^ m / (m.factorial : ℝ))
          ∂(gaussianReal 0 1) := by
      calc ∑ n ∈ Finset.range N,
            ‖∑ I ∈ wordsOfLength (d + 1) n, (phi.coeff I : ℂ) * condSigPoly hd t I z‖
          ≤ K * ∑ n ∈ Finset.range N, ∑ I ∈ wordsOfLength (d + 1) n, ‖condSigPoly hd t I.reverse z‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun n hn => (norm_sum_le _ _).trans ?_
            rw [Finset.mul_sum]
            have hterm : ∀ I ∈ wordsOfLength (d + 1) n,
                ‖(phi.coeff I : ℂ) * condSigPoly hd t I z‖ ≤
                  K * ‖condSigPoly hd t I z‖ := fun I _ => by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hcoeff I) (norm_nonneg _)
            refine (Finset.sum_le_sum hterm).trans_eq ?_
            have hreidx : ∑ I ∈ wordsOfLength (d + 1) n, ‖condSigPoly hd t I z‖ =
                ∑ I ∈ wordsOfLength (d + 1) n, ‖condSigPoly hd t I.reverse z‖ := by
              refine Finset.sum_bij (fun I _ => I.reverse)
                (fun I hI => wordsOfLength.mem.mpr (by simpa using wordsOfLength.mem.mp hI))
                (fun _ _ _ _ h => List.reverse_injective h)
                (fun I hI => ⟨I.reverse,
                  wordsOfLength.mem.mpr (by simpa using wordsOfLength.mem.mp hI),
                  List.reverse_reverse I⟩)
                (fun I _ => by rw [List.reverse_reverse])
            rw [← Finset.mul_sum, hreidx, Finset.mul_sum]
        _ ≤ K * ∑ m ∈ Finset.range N,
              (∑ n ∈ Finset.range (2 * m + 1),
                contrSum n (fun J => ∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J ∂(gaussianReal 0 1))) /
                (m.factorial : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ hK0
            calc ∑ n ∈ Finset.range N, ∑ I ∈ wordsOfLength (d + 1) n, ‖condSigPoly hd t I.reverse z‖
                ≤ ∑ n ∈ Finset.range N, ∑ I ∈ wordsOfLength (d + 1) n,
                    ∑ m ∈ Finset.range N,
                      ((contractions I).map fun p => p.1 *
                        (∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) p.2 ∂(gaussianReal 0 1))).sum /
                        (m.factorial : ℝ) :=
                  Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun I hI => hword n hn I hI
              _ = ∑ m ∈ Finset.range N,
                    (∑ n ∈ Finset.range N,
                      contrSum n (fun J => ∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J ∂(gaussianReal 0 1))) /
                      (m.factorial : ℝ) := by
                  have hswap1 : ∀ n,
                      ∑ I ∈ wordsOfLength (d + 1) n, ∑ m ∈ Finset.range N,
                        ((contractions I).map fun p => p.1 *
                          (∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) p.2 ∂(gaussianReal 0 1))).sum /
                          (m.factorial : ℝ) =
                      ∑ m ∈ Finset.range N,
                        contrSum n (fun J => ∫ y : ℝ, targetWt hd m t (‖z‖ + Real.sqrt t * |y|) J ∂(gaussianReal 0 1)) /
                          (m.factorial : ℝ) := fun n => by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun m _ => (Finset.sum_div _ _ _).symm
                  simp_rw [hswap1]
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun m _ => (Finset.sum_div _ _ _).symm
              _ ≤ _ := by
                  refine Finset.sum_le_sum fun m _ => div_le_div_of_nonneg_right ?_ (by positivity)
                  rcases le_total N (2 * m + 1) with hle | hge
                  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
                      fun n _ _ => hS_nn m n
                  · refine (Finset.sum_subset (Finset.range_mono hge) fun n _ hn => ?_).symm.le
                    have hgt : 2 * m < n := by simp only [Finset.mem_range, not_lt] at hn; omega
                    rw [hswap_int m n]
                    exact integral_eq_zero_of_ae (ae_of_all _ fun y =>
                      contrSum_targetWt_eq_zero_of_gt hd hgt t (‖z‖ + Real.sqrt t * |y|))
        _ = K * ∫ y : ℝ, ∑ m ∈ Finset.range N,
              (((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|)) ^ m / (m.factorial : ℝ))
              ∂(gaussianReal 0 1) := by
            congr 1
            simp_rw [hswap_int]
            have hint_m : ∀ m, Integrable (fun y : ℝ =>
                (((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|)) ^ m / (m.factorial : ℝ)))
                (gaussianReal 0 1) := fun m => by
              have hbase : MemLp (fun y : ℝ => ((1 + (d : ℝ) / 2) * t + ‖z‖) + Real.sqrt t * |y|)
                  (m : ℕ) (gaussianReal 0 1) :=
                (memLp_const ((1 + (d : ℝ) / 2) * t + ‖z‖)).add
                  (((memLp_id_gaussianReal' (μ := 0) (v := 1) (m : ℕ)
                    (ENNReal.natCast_ne_top _)).norm).const_mul (Real.sqrt t))
              refine (hbase.integrable_norm_pow'.div_const (m.factorial : ℝ)).congr
                (ae_of_all _ fun y => ?_)
              have hnn : 0 ≤ (1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|) := by positivity
              simp only [← add_assoc, Real.norm_of_nonneg (by linarith [hnn] : 0 ≤
                ((1 + (d : ℝ) / 2) * t + ‖z‖) + Real.sqrt t * |y|)]
            rw [integral_finsetSum _ fun m _ => hint_m m]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← integral_finsetSum _ fun n _ => hint_S m n, ← integral_div]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            change (∑ i ∈ Finset.range (2 * m + 1),
                contrSum i (targetWt hd m t (‖z‖ + Real.sqrt t * |y|))) / (m.factorial : ℝ) =
              ((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|)) ^ m / (m.factorial : ℝ)
            rw [sum_contrSum_targetWt hd t (‖z‖ + Real.sqrt t * |y|) m]
    refine hstep1.trans ?_
    have hexp_int : Integrable (fun y : ℝ =>
        Real.exp ((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|))) (gaussianReal 0 1) := by
      have h1 : Integrable (fun y : ℝ => Real.exp (Real.sqrt t * |y|)) (gaussianReal 0 1) := by
        refine ((integrable_exp_mul_gaussianReal_zero_one (Real.sqrt t)).add
          (integrable_exp_mul_gaussianReal_zero_one (-(Real.sqrt t)))).mono'
          (by fun_prop : Continuous _).aestronglyMeasurable (ae_of_all _ fun y => ?_)
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        rcases le_total 0 y with hy | hy
        · rw [abs_of_nonneg hy]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_nonpos hy, show Real.sqrt t * -y = -(Real.sqrt t) * y by ring]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
      refine (h1.const_mul (Real.exp ((1 + (d : ℝ) / 2) * t) * Real.exp ‖z‖)).congr
        (ae_of_all _ fun y => ?_)
      dsimp
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc K * ∫ y : ℝ, ∑ m ∈ Finset.range N,
            (((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|)) ^ m / (m.factorial : ℝ))
            ∂(gaussianReal 0 1)
        ≤ K * ∫ y : ℝ, Real.exp ((1 + (d : ℝ) / 2) * t + (‖z‖ + Real.sqrt t * |y|)) ∂(gaussianReal 0 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          exact integral_mono_of_nonneg
            (ae_of_all _ fun y => Finset.sum_nonneg fun _ _ => by positivity) hexp_int
            (ae_of_all _ fun y => Real.sum_le_exp_of_nonneg (by positivity) N)
      _ = K * (Real.exp ((1 + (d : ℝ) / 2) * t) * Real.exp ‖z‖ *
            ∫ y : ℝ, Real.exp (Real.sqrt t * |y|) ∂(gaussianReal 0 1)) := by
          congr 1
          rw [← integral_const_mul]
          congr 1; funext y; rw [Real.exp_add, Real.exp_add, mul_assoc]
      _ ≤ K * (Real.exp ((1 + (d : ℝ) / 2) * t) * Real.exp ‖z‖ * (2 * Real.exp (t / 2))) := by gcongr
      _ = M := by
          simp only [M]
          have hadd : Real.exp ((1 + (d : ℝ) / 2) * t) * Real.exp (t / 2) =
              Real.exp (((3 + (d : ℝ)) / 2) * t) := by
            rw [← Real.exp_add]; congr 1; ring
          calc K * (Real.exp ((1 + (d : ℝ) / 2) * t) * Real.exp ‖z‖ * (2 * Real.exp (t / 2)))
              = K * (2 * (Real.exp ((1 + (d : ℝ) / 2) * t) * Real.exp (t / 2))) * Real.exp ‖z‖ := by ring
            _ = _ := by rw [hadd]
  have hsumm := summable_of_sum_range_le (fun _ => norm_nonneg _) hpart
  exact ⟨hsumm, hsumm.tsum_le_of_sum_range_le hpart⟩

end SignatureVolatility

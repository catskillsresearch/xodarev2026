module

public import SignatureVolatility.Letter
public import SignatureVolatility.Word
public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported
public import SignatureVolatility.DualPairing
public import SignatureVolatility.ExtTensorAlgebra.LevelInner
public import SignatureVolatility.ExtTensorAlgebra.ShuffleWords
public import SignatureVolatility.ExtTensorAlgebra.ShuffleBasis
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigChen
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.ProlongedBrownianSetup.StratItoCoeffBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-!
# Counterexample tensor family `u₀^(λ)`

Shared algebraic and pathwise data for the affine / Riccati duality
counterexample: the first space letter, the finitely supported family
`u₀^(λ) = 2λ e_{[1,1,1]} − λ e_{[1,0]} − 12λ² e_{[1,1,1,1,0]}`, the three-term
`dualPairing` identity, and the a.s. evaluation of `⟨u₀^(λ), Ŵ_t⟩`.
-/

@[expose] public section

namespace SignatureVolatility

open ExtTensorAlgebra

/-- First spatial letter `1 = (0 : Fin d).succ` when `0 < d`. -/
def firstSpace {d : ℕ} (hd : 0 < d) : Letter (d + 1) :=
  (⟨0, hd⟩ : Fin d).succ

lemma firstSpace_ne_zero {d : ℕ} (hd : 0 < d) : firstSpace hd ≠ 0 :=
  Fin.succ_ne_zero _

/-- Counterexample tensor family `u₀^(λ) = 2λ e_{[1,1,1]} - λ e_{[1,0]} - 12λ² e_{[1,1,1,1,0]}`. -/
def counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I =>
    if I = [firstSpace hd, firstSpace hd, firstSpace hd] then 2 * lam
    else if I = [firstSpace hd, 0] then -lam
    else if I = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] then
      -12 * lam ^ 2
    else 0⟩

lemma counterexampleU0_coeff {d : ℕ} (hd : 0 < d) (lam : ℝ) (I : Word (d + 1)) :
    (counterexampleU0 hd lam).coeff I =
      if I = [firstSpace hd, firstSpace hd, firstSpace hd] then 2 * lam
      else if I = [firstSpace hd, 0] then -lam
      else if I = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] then
        -12 * lam ^ 2
      else 0 :=
  rfl

lemma counterexampleU0_coeff_zero {d : ℕ} (hd : 0 < d) (lam : ℝ) {I : Word (d + 1)}
    (h3 : I ≠ [firstSpace hd, firstSpace hd, firstSpace hd])
    (h2 : I ≠ [firstSpace hd, 0])
    (h5 : I ≠ [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0]) :
    (counterexampleU0 hd lam).coeff I = 0 := by
  simp [counterexampleU0_coeff, h3, h2, h5]

lemma counterexampleU0_isFinitelySupported {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    IsFinitelySupported (counterexampleU0 hd lam) := by
  refine ⟨5, fun I hI => ?_⟩
  simp only [counterexampleU0]
  split_ifs with h1 h2 h3
  · subst h1; simp at hI
  · subst h2; simp at hI
  · subst h3; simp at hI
  · rfl



private lemma shuffleWords_nil_left {d : ℕ} (J : Word d) :
    shuffleWords [] J = [J] := by
  simp [shuffleWords]

private lemma shuffleWords_cons_nil {d : ℕ} (i : Letter d) (I : Word d) :
    shuffleWords (i :: I) [] = [i :: I] := by
  simp [shuffleWords]

private lemma shuffleWords_cons_cons {d : ℕ} (i j : Letter d) (I J : Word d) :
    shuffleWords (i :: I) (j :: J) =
      (shuffleWords I (j :: J)).map (i :: ·) ++ (shuffleWords (i :: I) J).map (j :: ·) := by
  rw [shuffleWords]

private lemma shuffleWords_single_single {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a] = [[a, a], [a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_cons_nil]
  simp

private lemma shuffleWords_single_pair {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a, a] = [[a, a, a], [a, a, a], [a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_single_single]
  simp

private lemma shuffleWords_single_triple {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a, a, a] =
      [[a, a, a, a], [a, a, a, a], [a, a, a, a], [a, a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_single_pair]
  simp

open MeasureTheory Filter Topology Set

/-! ## Part 2: Exact signature evaluation for `u₀^(λ)` (sorry-free) -/

/-- The infinite `tsum` in `dualPairing (counterexampleU0 hd lam) X` reduces to 3 explicit terms. -/
lemma dualPairing_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ)
    (X : ExtTensorAlgebra (d + 1)) :
    dualPairing (counterexampleU0 hd lam) X =
      2 * lam * X.coeff [firstSpace hd, firstSpace hd, firstSpace hd]
      - lam * X.coeff [firstSpace hd, 0]
      - 12 * lam ^ 2 *
          X.coeff [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] := by
  set l1 := firstSpace hd with hl1eq
  set u := counterexampleU0 hd lam
  have hzero_len : ∀ n : ℕ, n ≠ 2 → n ≠ 3 → n ≠ 5 → u.levelInner X n = 0 := by
    intro n h2 h3 h5
    refine Finset.sum_eq_zero fun I hI => ?_
    have hlen : I.length = n := wordsOfLength.mem.mp hI
    have hc : u.coeff I = 0 := by
      refine counterexampleU0_coeff_zero hd lam ?_ ?_ ?_
      · intro h; subst h; exact h3 hlen.symm
      · intro h; subst h; exact h2 hlen.symm
      · intro h; subst h; exact h5 hlen.symm
    simp [hc]
  have htsum : dualPairing u X = ∑ n ∈ Finset.range 6, u.levelInner X n :=
    tsum_eq_sum fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      exact hzero_len n (by omega) (by omega) (by omega)
  have h2 : u.levelInner X 2 = -lam * X.coeff [l1, 0] := by
    unfold levelInner
    rw [Finset.sum_eq_single [l1, 0]]
    · have hne : ([l1, 0] : Word (d + 1)) ≠ [l1, l1, l1] := by simp
      simp [u, counterexampleU0, ← hl1eq, hne]
    · intro I hI hIne
      have hlen : I.length = 2 := wordsOfLength.mem.mp hI
      have hc : u.coeff I = 0 := by
        refine counterexampleU0_coeff_zero hd lam ?_ ?_ ?_
        · intro h; subst h; simp at hlen
        · rw [← hl1eq]; exact hIne
        · intro h; subst h; simp at hlen
      simp [hc]
    · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
  have h3 : u.levelInner X 3 = 2 * lam * X.coeff [l1, l1, l1] := by
    unfold levelInner
    rw [Finset.sum_eq_single [l1, l1, l1]]
    · simp [u, counterexampleU0, ← hl1eq]
    · intro I hI hIne
      have hlen : I.length = 3 := wordsOfLength.mem.mp hI
      have hc : u.coeff I = 0 := by
        refine counterexampleU0_coeff_zero hd lam ?_ ?_ ?_
        · rw [← hl1eq]; exact hIne
        · intro h; subst h; simp at hlen
        · intro h; subst h; simp at hlen
      simp [hc]
    · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
  have h5 : u.levelInner X 5 = -12 * lam ^ 2 * X.coeff [l1, l1, l1, l1, 0] := by
    unfold levelInner
    rw [Finset.sum_eq_single [l1, l1, l1, l1, 0]]
    · have hne1 : ([l1, l1, l1, l1, 0] : Word (d + 1)) ≠ [l1, l1, l1] := by simp
      have hne2 : ([l1, l1, l1, l1, 0] : Word (d + 1)) ≠ [l1, 0] := by simp
      simp [u, counterexampleU0, ← hl1eq, hne1, hne2]
    · intro I hI hIne
      have hlen : I.length = 5 := wordsOfLength.mem.mp hI
      have hc : u.coeff I = 0 := by
        refine counterexampleU0_coeff_zero hd lam ?_ ?_ ?_
        · intro h; subst h; simp at hlen
        · intro h; subst h; simp at hlen
        · rw [← hl1eq]; exact hIne
      simp [hc]
    · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
  rw [htsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [hzero_len 0 (by omega) (by omega) (by omega),
    hzero_len 1 (by omega) (by omega) (by omega),
    h2, h3, hzero_len 4 (by omega) (by omega) (by omega), h5]
  ring

section SignatureEval

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma ae_paperSig2_space_two (B : MultiBrownian Ω P d) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff [i.succ, i.succ] =
      (MultiBrownian.W B t ω i) ^ 2 / 2 := by
  filter_upwards [paperSig2_shuffle B ht [i.succ] [i.succ]] with ω hω
  simp only [paperSig2_space, MultiBrownian.W_zero, sub_zero, evalShuffleBasis,
    shuffleWords_single_single, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hω
  linarith

lemma ae_paperSig2_space_three (B : MultiBrownian Ω P d) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff [i.succ, i.succ, i.succ] =
      (MultiBrownian.W B t ω i) ^ 3 / 6 := by
  filter_upwards [paperSig2_shuffle B ht [i.succ] [i.succ, i.succ],
    ae_paperSig2_space_two B i ht] with ω hω h2
  simp only [paperSig2_space, MultiBrownian.W_zero, sub_zero, h2, evalShuffleBasis,
    shuffleWords_single_pair, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hω
  linarith

lemma ae_paperSig2_space_four (B : MultiBrownian Ω P d) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff [i.succ, i.succ, i.succ, i.succ] =
      (MultiBrownian.W B t ω i) ^ 4 / 24 := by
  filter_upwards [paperSig2_shuffle B ht [i.succ] [i.succ, i.succ, i.succ],
    ae_paperSig2_space_three B i ht] with ω hω h3
  simp only [paperSig2_space, MultiBrownian.W_zero, sub_zero, h3, evalShuffleBasis,
    shuffleWords_single_triple, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hω
  linarith

/-- Appending the time letter `0` integrates a Stratonovich signature coordinate in time. -/
lemma ae_paperSig2_append_zero (B : MultiBrownian Ω P d) (I : Word (d + 1)) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff (I ++ [0]) =
      ∫ s in (0 : ℝ)..t, (paperSig2 B 0 s ω).coeff I := by
  filter_upwards [ae_continuousOn_itoWordIntegral B ht, ae_itoWordIntegral_time_cons B ht]
    with ω hω h0
  set K := I.reverse
  have hH : ∀ s, (paperSig2 B 0 s ω).coeff I =
      ((contractions K).map (fun p => p.1 * itoWordIntegral B 0 s ω p.2)).sum := fun s => by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
  have hT : (paperSig2 B 0 t ω).coeff (I ++ [0]) =
      ((contractions K).map
        (fun p => p.1 * ∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω p.2)).sum := by
    rw [paperSig2_coeff, stratWordIntegral_eq_list]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      contractions_cons_zero, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp [h0]
  have hint := integral_list_sum (f := fun w s => itoWordIntegral B 0 s ω w) ht hω (contractions K)
  rw [hT, ← hint.2]
  simp only [hH]

lemma ae_continuousOn_paperSig2_coeff_onNat (B : MultiBrownian Ω P d) (I : Word (d + 1)) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ContinuousOn (fun s => (paperSig2 B 0 s ω).coeff I) (Icc 0 N) := by
  filter_upwards [ae_all_iff.2 fun N : ℕ =>
    ae_continuousOn_itoWordIntegral B (Nat.cast_nonneg N)] with ω hω N
  have hH : (fun s => (paperSig2 B 0 s ω).coeff I) =
      fun s => ((contractions I.reverse).map
        (fun p => p.1 * itoWordIntegral B 0 s ω p.2)).sum := by
    funext s; rw [paperSig2_coeff, stratWordIntegral_eq_list]
  rw [hH]
  exact (integral_list_sum (f := fun w s => itoWordIntegral B 0 s ω w)
    (Nat.cast_nonneg N) (hω N) (contractions I.reverse)).1

/-- Exact pathwise evaluation of `⟨u₀^(λ), Ŵ_t⟩` for every `t ≥ 0` (almost surely). -/
theorem ae_dualPairing_counterexampleU0_eq (B : MultiBrownian Ω P d) (hd : 0 < d) (lam : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P,
      dualPairing (counterexampleU0 hd lam) (paperSig2 B 0 t ω) =
        (lam / 3) * (MultiBrownian.W B t ω ⟨0, hd⟩) ^ 3
        - lam * (∫ r in (0 : ℝ)..t, MultiBrownian.W B r ω ⟨0, hd⟩)
        - (lam ^ 2 / 2) * (∫ r in (0 : ℝ)..t, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ 4) := by
  set i0 : Fin d := ⟨0, hd⟩
  set l1 : Letter (d + 1) := firstSpace hd
  have h4_all : ∀ᵐ ω ∂P, ∀ s, 0 ≤ s →
      (paperSig2 B 0 s ω).coeff [l1, l1, l1, l1] = (MultiBrownian.W B s ω i0) ^ 4 / 24 := by
    refine ae_forall_of_continuousOn
      (ae_continuousOn_paperSig2_coeff_onNat B [l1, l1, l1, l1])
      (ae_of_all _ fun ω N =>
        (((continuous_W_coord B i0 ω).pow 4).div_const 24).continuousOn)
      fun s hs => ae_paperSig2_space_four B i0 hs.le
  filter_upwards [ae_paperSig2_space_three B i0 ht,
    ae_paperSig2_append_zero B [l1] ht,
    ae_paperSig2_append_zero B [l1, l1, l1, l1] ht,
    h4_all] with ω h3 h10 h40 h4s
  rw [dualPairing_counterexampleU0]
  have h10' : (paperSig2 B 0 t ω).coeff [l1, 0] = ∫ r in (0 : ℝ)..t, MultiBrownian.W B r ω i0 := by
    have h := h10
    simp only [List.singleton_append] at h
    rw [h]
    refine intervalIntegral.integral_congr fun r _ => ?_
    have hlet : l1 = i0.succ := rfl
    rw [hlet, paperSig2_space, MultiBrownian.W_zero, sub_zero]
  have h40' : (paperSig2 B 0 t ω).coeff [l1, l1, l1, l1, 0] =
      (∫ r in (0 : ℝ)..t, (MultiBrownian.W B r ω i0) ^ 4) / 24 := by
    have h := h40
    simp only [List.cons_append, List.nil_append] at h
    rw [h, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht] at hr
    exact h4s r hr.1
  have h3' : (paperSig2 B 0 t ω).coeff [firstSpace hd, firstSpace hd, firstSpace hd] =
      (MultiBrownian.W B t ω i0) ^ 3 / 6 := by
    simpa [show i0.succ = firstSpace hd from rfl] using h3
  have h10'' : (paperSig2 B 0 t ω).coeff [firstSpace hd, 0] =
      ∫ r in (0 : ℝ)..t, MultiBrownian.W B r ω i0 := by
    simpa [show l1 = firstSpace hd from rfl] using h10'
  have h40'' : (paperSig2 B 0 t ω).coeff
      [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd, 0] =
      (∫ r in (0 : ℝ)..t, (MultiBrownian.W B r ω i0) ^ 4) / 24 := by
    simpa [show l1 = firstSpace hd from rfl] using h40'
  rw [h3', h10'', h40'']
  ring

end SignatureEval

end SignatureVolatility

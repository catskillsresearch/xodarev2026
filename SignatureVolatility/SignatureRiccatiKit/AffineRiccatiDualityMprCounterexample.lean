module

public import SignatureVolatility.SignatureRiccatiKit
public import SignatureVolatility.SignatureRiccatiKit.RiccatiOp
public import SignatureVolatility.ItoCalculusKit.OfMathFin
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigChen
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.ProlongedBrownianSetup.StratItoCoeffBounds
public import SignatureVolatility.ExtTensorAlgebra.ShuffleWords
public import SignatureVolatility.ExtTensorAlgebra.ShuffleBasis
public import SignatureVolatility.ExtTensorAlgebra.LevelInner
public import SignatureVolatility.ExtTensorAlgebra.LevelNorm
public import SignatureVolatility.WordsOfLength
public import SignatureVolatility.ClassicalRiccatiSolution
public import SignatureVolatility.DualPairing
public import SignatureVolatility.MemTw
public import SignatureVolatility.NormW
public import SignatureVolatility.RightShift
public import SignatureVolatility.ShuffleFinite
public import SignatureVolatility.StratonovichHalfLaplacian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Proposed counterexample to `affine_riccati_duality_mpr`

Source: Gemini Carbon (outside opinion, 2026-11-24), filled-in Lean (Parts 1–5).
Parts 1–3 are sorry-free. Pillar D is sorry-free. Part 5 assembles
`not_affine_riccati_duality_mpr` from pillars A–D; A, B and C remain
`sorry`. This file has not yet been independently proof-checked.

This module is not a completed refutation until A–C are proved as well.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped BigOperators Classical ENNReal NNReal

namespace SignatureVolatility

open ExtTensorAlgebra

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Part 1: Purely algebraic / combinatorial core (sorry-free) -/

private lemma append_singleton_eq_iff {α : Type*} {K L : List α} {a b : α} :
    K ++ [a] = L ++ [b] ↔ K = L ∧ a = b := by
  constructor
  · intro h
    have hr := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.cons.injEq] at hr
    exact ⟨List.reverse_injective hr.2, hr.1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

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

private lemma shuffleWords_pair_single {d : ℕ} (a : Letter d) :
    shuffleWords [a, a] [a] = [[a, a, a], [a, a, a], [a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_single_single, shuffleWords_cons_nil]
  simp

private lemma shuffleWords_single_triple {d : ℕ} (a : Letter d) :
    shuffleWords [a] [a, a, a] =
      [[a, a, a, a], [a, a, a, a], [a, a, a, a], [a, a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_nil_left, shuffleWords_single_pair]
  simp

private lemma shuffleWords_pair_pair {d : ℕ} (a : Letter d) :
    shuffleWords [a, a] [a, a] =
      [[a, a, a, a], [a, a, a, a], [a, a, a, a],
       [a, a, a, a], [a, a, a, a], [a, a, a, a]] := by
  rw [shuffleWords_cons_cons, shuffleWords_single_pair, shuffleWords_pair_single]
  simp

private lemma shuffleBasis_pair_pair {d : ℕ} (a : Letter d) (K : Word d) :
    (shuffleBasis [a, a] [a, a]).coeff K = if K = [a, a, a, a] then 6 else 0 := by
  simp only [shuffleBasis, shuffleWords_pair_pair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  split_ifs <;> norm_num

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

lemma rightShift_zero_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (K : Word (d + 1)) :
    (rightShift 0 (counterexampleU0 hd lam)).coeff K =
      if K = [firstSpace hd] then -lam
      else if K = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd] then
        -12 * lam ^ 2
      else 0 := by
  set l1 := firstSpace hd with hl1eq
  have hl1 : l1 ≠ 0 := firstSpace_ne_zero hd
  have h1 : K ++ [0] ≠ [l1, l1, l1] := by
    intro h
    have h' : K ++ [0] = [l1, l1] ++ [l1] := h
    exact hl1 ((append_singleton_eq_iff.mp h').2.symm)
  have h2 : K ++ [0] = [l1, 0] ↔ K = [l1] := by
    simpa using (append_singleton_eq_iff (K := K) (L := [l1]) (a := (0 : Letter (d + 1))) (b := 0))
  have h3 : K ++ [0] = [l1, l1, l1, l1, 0] ↔ K = [l1, l1, l1, l1] := by
    simpa using (append_singleton_eq_iff (K := K) (L := [l1, l1, l1, l1])
      (a := (0 : Letter (d + 1))) (b := 0))
  simp only [rightShift, counterexampleU0, ← hl1eq, h1, ↓reduceIte, h2, h3]

lemma rightShift_succ_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (i : Fin d)
    (K : Word (d + 1)) :
    (rightShift i.succ (counterexampleU0 hd lam)).coeff K =
      if i = ⟨0, hd⟩ ∧ K = [firstSpace hd, firstSpace hd] then 2 * lam else 0 := by
  set l1 := firstSpace hd with hl1eq
  have hi0 : i.succ ≠ 0 := Fin.succ_ne_zero i
  have h1 : K ++ [i.succ] = [l1, l1, l1] ↔ i = ⟨0, hd⟩ ∧ K = [l1, l1] := by
    have he : K ++ [i.succ] = [l1, l1] ++ [l1] ↔ K = [l1, l1] ∧ i.succ = l1 :=
      append_singleton_eq_iff
    rw [show ([l1, l1, l1] : Word (d + 1)) = [l1, l1] ++ [l1] from rfl, he]
    simp only [l1, firstSpace, Fin.succ_inj, and_comm]
  have h2 : K ++ [i.succ] ≠ [l1, 0] := by
    intro h
    have h' : K ++ [i.succ] = [l1] ++ [0] := h
    exact hi0 (append_singleton_eq_iff.mp h').2
  have h3 : K ++ [i.succ] ≠ [l1, l1, l1, l1, 0] := by
    intro h
    have h' : K ++ [i.succ] = [l1, l1, l1, l1] ++ [0] := h
    exact hi0 (append_singleton_eq_iff.mp h').2
  simp only [rightShift, counterexampleU0, ← hl1eq, h1, h2, h3, ↓reduceIte]

lemma halfLaplacian_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (K : Word (d + 1)) :
    (stratonovichHalfLaplacian (counterexampleU0 hd lam)).coeff K =
      if K = [firstSpace hd] then lam else 0 := by
  set l1 := firstSpace hd with hl1eq
  have hterm : ∀ i : Fin d,
      (counterexampleU0 hd lam).coeff (K ++ [i.succ, i.succ]) =
        if i = ⟨0, hd⟩ ∧ K = [l1] then 2 * lam else 0 := by
    intro i
    have hi0 : i.succ ≠ 0 := Fin.succ_ne_zero i
    have h1 : K ++ [i.succ, i.succ] = [l1, l1, l1] ↔ i = ⟨0, hd⟩ ∧ K = [l1] := by
      have he : (K ++ [i.succ]) ++ [i.succ] = ([l1] ++ [l1]) ++ [l1] ↔
          K ++ [i.succ] = [l1] ++ [l1] ∧ i.succ = l1 := append_singleton_eq_iff
      rw [show K ++ [i.succ, i.succ] = (K ++ [i.succ]) ++ [i.succ] by simp,
        show ([l1, l1, l1] : Word (d + 1)) = ([l1] ++ [l1]) ++ [l1] from rfl, he,
        append_singleton_eq_iff]
      simp only [l1, firstSpace, Fin.succ_inj]
      tauto
    have h2 : K ++ [i.succ, i.succ] ≠ [l1, 0] := by
      intro h
      have h' : (K ++ [i.succ]) ++ [i.succ] = [l1] ++ [0] := by simpa using h
      exact hi0 (append_singleton_eq_iff.mp h').2
    have h3 : K ++ [i.succ, i.succ] ≠ [l1, l1, l1, l1, 0] := by
      intro h
      have h' : (K ++ [i.succ]) ++ [i.succ] = [l1, l1, l1, l1] ++ [0] := by simpa using h
      exact hi0 (append_singleton_eq_iff.mp h').2
    simp only [counterexampleU0, ← hl1eq, h1, h2, h3, ↓reduceIte]
  simp only [stratonovichHalfLaplacian, hterm]
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp only [true_and]
    split_ifs <;> ring
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma quadTerm_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) (K : Word (d + 1)) :
    (1 / 2 : ℝ) * ∑ i : Fin d,
      (shuffleFinite (rightShift i.succ (counterexampleU0 hd lam))
        (rightShift i.succ (counterexampleU0 hd lam)) K.length).coeff K =
      if K = [firstSpace hd, firstSpace hd, firstSpace hd, firstSpace hd] then
        12 * lam ^ 2
      else 0 := by
  set l1 := firstSpace hd with hl1eq
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp only [shuffleFinite, rightShift_succ_counterexampleU0, true_and]
    by_cases hK : K = [l1, l1, l1, l1]
    · subst hK
      have hlen : ([l1, l1, l1, l1] : Word (d + 1)).length = 4 := rfl
      rw [hlen]
      rw [Finset.sum_eq_single 2]
      · rw [Finset.sum_eq_single 2]
        · rw [Finset.sum_eq_single [l1, l1]]
          · rw [Finset.sum_eq_single [l1, l1]]
            · simp only [↓reduceIte, ← hl1eq, shuffleBasis_pair_pair]
              ring
            · intro J _ hJ; simp [hJ, ← hl1eq]
            · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
          · intro I _ hI; simp [hI, ← hl1eq]
          · intro h; exact absurd (wordsOfLength.mem.mpr rfl) h
        · intro n _ hn
          refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J hJ => ?_
          have hJne : J ≠ [l1, l1] := by
            intro heq; subst heq; exact hn (wordsOfLength.mem.mp hJ).symm
          simp [hJne, ← hl1eq]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro m _ hm
        refine Finset.sum_eq_zero fun n _ =>
          Finset.sum_eq_zero fun I hI => Finset.sum_eq_zero fun J _ => ?_
        have hIne : I ≠ [l1, l1] := by
          intro heq; subst heq; exact hm (wordsOfLength.mem.mp hI).symm
        simp [hIne, ← hl1eq]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · simp only [hK, ↓reduceIte]
      have hzero :
          ∑ m ∈ Finset.range (K.length + 1),
            ∑ n ∈ Finset.range (K.length + 1),
              ∑ I ∈ wordsOfLength (d + 1) m,
                ∑ J ∈ wordsOfLength (d + 1) n,
                  (if I = [l1, l1] then 2 * lam else 0) *
                    (if J = [l1, l1] then 2 * lam else 0) *
                    (shuffleBasis I J).coeff K = 0 := by
        refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun n _ =>
          Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J _ => ?_
        by_cases hI : I = [l1, l1]
        · by_cases hJ : J = [l1, l1]
          · subst hI; subst hJ
            simp [shuffleBasis_pair_pair, hK]
          · simp [hJ]
        · simp [hI]
      rw [hzero, mul_zero]
  · intro i _ hi
    simp only [shuffleFinite, rightShift_succ_counterexampleU0, hi, false_and, ↓reduceIte,
      zero_mul, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Exact algebraic kernel property**: `ℛ(u₀^(λ)) = 0` identically. -/
theorem riccatiOp_counterexampleU0 {d : ℕ} (hd : 0 < d) (lam : ℝ) :
    riccatiOp (counterexampleU0 hd lam) = 0 := by
  ext K
  change ((rightShift 0 (counterexampleU0 hd lam)).coeff K +
      (stratonovichHalfLaplacian (counterexampleU0 hd lam)).coeff K) +
      (1 / 2 : ℝ) * ∑ i : Fin d,
        (shuffleFinite (rightShift i.succ (counterexampleU0 hd lam))
          (rightShift i.succ (counterexampleU0 hd lam)) K.length).coeff K = 0
  rw [rightShift_zero_counterexampleU0, halfLaplacian_counterexampleU0, quadTerm_counterexampleU0]
  set l1 := firstSpace hd with hl1eq
  by_cases h1 : K = [l1]
  · subst h1
    have hne : ([l1] : Word (d + 1)) ≠ [l1, l1, l1, l1] := by simp
    simp only [↓reduceIte, hne]
    ring
  · by_cases h4 : K = [l1, l1, l1, l1]
    · subst h4
      simp only [h1, ↓reduceIte]
      ring
    · simp only [h1, h4, ↓reduceIte]
      ring

/-- Constant classical Riccati solution `ψ(s) ≡ u₀^(λ)` for EVERY `M : SignatureVolatilityModel`. -/
noncomputable def counterexampleRiccatiSol (M : SignatureVolatilityModel) (lam : ℝ) :
    ClassicalRiccatiSolution M.w M.T riccatiOp (counterexampleU0 M.hd lam) where
  ψ := fun _ => counterexampleU0 M.hd lam
  mem_Tw := fun _ _ => by
    refine summable_of_ne_finset_zero (s := Finset.range 6) fun n hn => ?_
    have hn5 : 5 < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have hsq : (counterexampleU0 M.hd lam).levelNormSq n = 0 := by
      unfold levelNormSq
      refine Finset.sum_eq_zero fun I hI => ?_
      have hlen : 5 < I.length := by rwa [wordsOfLength.mem.mp hI]
      have h0 : (counterexampleU0 M.hd lam).coeff I = 0 := by
        simp only [counterexampleU0]
        split_ifs with c1 c2 c3
        · subst c1; simp at hlen
        · subst c2; simp at hlen
        · subst c3; simp at hlen
        · rfl
      simp [h0]
    simp [levelNorm, hsq]
  uniform_bdd := ⟨normW M.w (counterexampleU0 M.hd lam),
    tsum_nonneg fun n => mul_nonneg (M.w.pos n).le (levelNorm.nonneg _ _),
    fun _ _ => le_rfl⟩
  init := rfl
  integral_eq := fun t _ I => by
    have h0 : riccatiOp (counterexampleU0 M.hd lam) = 0 := riccatiOp_counterexampleU0 M.hd lam
    have hcoeff : (riccatiOp (counterexampleU0 M.hd lam)).coeff I = 0 := by
      rw [h0]; rfl
    refine ⟨?_, ?_⟩
    · simpa [hcoeff] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 M.T))
    · simp [hcoeff, intervalIntegral.integral_zero]

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

/-! ## Part 3: Degree-4 polynomial bounded on `(-∞, 0]` is constant (sorry-free) -/

private lemma poly4_const_of_bdd_nonpos {a₀ a₁ a₂ a₃ a₄ L : ℝ}
    (hbdd : ∀ x : ℝ, x ≤ 0 →
      L ≤ a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ∧
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 ≤ 0) :
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 := by
  have habs : ∀ n : ℕ,
      |a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
        a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4| ≤ |L| := by
    intro n
    have h := hbdd (-(n : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le L], by linarith [abs_nonneg L]⟩
  have hpow0 : ∀ (k : ℕ), 0 < k → ∀ c : ℝ,
      Tendsto (fun n : ℕ => c / ((n : ℝ) ^ k)) atTop (𝓝 0) := fun k hk c => by
    have h := tendsto_const_nhds (x := c) |>.div_atTop
      ((tendsto_pow_atTop (Nat.ne_of_gt hk)).comp tendsto_natCast_atTop_atTop)
    simpa [Function.comp_def] using h
  have ha4 : a₄ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3 + a₄ * (-(n : ℝ)) ^ 4) / (n : ℝ) ^ 4|) atTop (𝓝 |a₄|) := by
      have h1 : Tendsto (fun n : ℕ =>
          a₀ / (n : ℝ) ^ 4 - a₁ / (n : ℝ) ^ 3 + a₂ / (n : ℝ) ^ 2 - a₃ / (n : ℝ) ^ 1 + a₄)
          atTop (𝓝 (0 - 0 + 0 - 0 + a₄)) :=
        ((((hpow0 4 (by norm_num) a₀).sub (hpow0 3 (by norm_num) a₁)).add
          (hpow0 2 (by norm_num) a₂)).sub (hpow0 1 (by norm_num) a₃)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; try ring
    have hle : |a₄| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 4 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)]
      exact div_le_div_of_nonneg_right (habs n) (by positivity)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  subst ha4
  have ha3 : a₃ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2 +
          a₃ * (-(n : ℝ)) ^ 3) / (n : ℝ) ^ 3|) atTop (𝓝 |-a₃|) := by
      have h1 : Tendsto (fun n : ℕ =>
          a₀ / (n : ℝ) ^ 3 - a₁ / (n : ℝ) ^ 2 + a₂ / (n : ℝ) ^ 1 + (-a₃))
          atTop (𝓝 (0 - 0 + 0 + (-a₃))) :=
        (((hpow0 3 (by norm_num) a₀).sub (hpow0 2 (by norm_num) a₁)).add
          (hpow0 1 (by norm_num) a₂)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; try ring
    have hle : |-a₃| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 3 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    simpa [abs_neg] using le_antisymm hle (abs_nonneg _)
  subst ha3
  have ha2 : a₂ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ)) + a₂ * (-(n : ℝ)) ^ 2) / (n : ℝ) ^ 2|) atTop (𝓝 |a₂|) := by
      have h1 : Tendsto (fun n : ℕ => a₀ / (n : ℝ) ^ 2 - a₁ / (n : ℝ) ^ 1 + a₂)
          atTop (𝓝 (0 - 0 + a₂)) :=
        ((hpow0 2 (by norm_num) a₀).sub (hpow0 1 (by norm_num) a₁)).add tendsto_const_nhds
      simp only [sub_zero, zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp; try ring
    have hle : |a₂| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 2 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  subst ha2
  have ha1 : a₁ = 0 := by
    have hlim : Tendsto (fun n : ℕ =>
        |(a₀ + a₁ * (-(n : ℝ))) / (n : ℝ) ^ 1|) atTop (𝓝 |-a₁|) := by
      have h1 : Tendsto (fun n : ℕ => a₀ / (n : ℝ) ^ 1 + (-a₁)) atTop (𝓝 (0 + (-a₁))) :=
        (hpow0 1 (by norm_num) a₀).add tendsto_const_nhds
      simp only [zero_add] at h1
      refine (h1.abs).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      congr 1; field_simp
    have hle : |-a₁| ≤ 0 := le_of_tendsto_of_tendsto hlim (hpow0 1 (by norm_num) |L|) <| by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 1)]
      have h := habs n; simp only [zero_mul, add_zero] at h
      exact div_le_div_of_nonneg_right h (by positivity)
    simpa [abs_neg] using le_antisymm hle (abs_nonneg _)
  exact And.intro ha1 ⟨rfl, rfl, rfl⟩

/-! ## Part 4: Four isolated analytic/probabilistic pillars (open sub-goals) -/

/-- **Pillar A (Doléans–Dade supermartingale bound)**:
`exp ⟨u₀^(λ), Ŵ_t⟩ = ℰ(∫ λ W_r² dW_r)_t` is a positive local martingale starting at `1`,
hence `𝔼[exp ⟨u₀^(λ), Ŵ_t⟩] ≤ 1 < ∞` for all `t ∈ [0, T]`. -/
lemma signatureTransformFinite_counterexampleU0 (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (lam : ℝ) :
    SignatureTransformFinite P (paperSetup B M.hT) (counterexampleU0 M.hd lam) := by
  sorry

/-- **Pillar B (Markov + Brownian scaling + stopped Girsanov explosion asymptotics)**:
There exists a function `v₁ : ℝ → ℝ` (namely `x ↦ ℚ_x(τ_∞ > T/2)` for `dY = Y² dr + dB̃`)
such that:
1. `0 < v₁ x ≤ 1` for all `x : ℝ`;
2. polynomial lower bound on `log v₁`: `∃ C ≥ 0, ∀ x, -C * (1 + |x|^4) ≤ Real.log (v₁ x)`;
3. uniform positive lower bound on `(-∞, 0]`: `∀ x ≤ 0, v₁ 0 ≤ v₁ x`;
4. decay to `0` as `x → +∞`: `Tendsto v₁ atTop (𝓝 0)`;
5. for every `lam ≥ 1`, at `t = M.T - lam ^ (-(2/3 : ℝ)) * (M.T / 2) ∈ [M.T/2, M.T)`:
   `𝔼[M_T^(λ) | ℱ_t] = M_t^(λ) * v₁(lam^(1/3) * W_t)` a.s. -/
lemma exists_scaled_survival_function (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∃ v₁ : ℝ → ℝ,
      (∀ x, 0 < v₁ x ∧ v₁ x ≤ 1) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, -C * (1 + |x| ^ 4) ≤ Real.log (v₁ x)) ∧
      (∀ x : ℝ, x ≤ 0 → v₁ 0 ≤ v₁ x) ∧
      Tendsto v₁ atTop (𝓝 0) ∧
      ∀ lam : ℝ, 1 ≤ lam →
        let s_lam := lam ^ (-(2 / 3 : ℝ)) * (M.T / 2)
        let t_lam := M.T - s_lam
        P[fun ω => Real.exp (dualPairing (counterexampleU0 M.hd lam)
            ((paperSetup B M.hT).W_hat M.T ω)) |
          (paperSetup B M.hT).signatureFiltration.σAlg t_lam] =ᵐ[P]
          fun ω =>
            Real.exp (dualPairing (counterexampleU0 M.hd lam)
              ((paperSetup B M.hT).W_hat t_lam ω)) *
            v₁ (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩) := by
  sorry

/-- **Pillar C (Girsanov–Fawcett / Hermite conditional signature expansion)**:
If `ϕ ∈ T_w` and `⟨ϕ, Ŵ_t⟩ = f(W_t^0)` a.s. for a measurable function `f : ℝ → ℝ` at `t ∈ (0, T)`,
then `f` agrees Lebesgue-a.e. with the restriction to `ℝ` of an entire function `G : ℂ → ℂ`
of exponential type `≤ 1` (`∃ C ≥ 0, ∀ z, ‖G z‖ ≤ C * Real.exp ‖z‖`). -/
lemma exists_entire_expTypeOne_of_memTw (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ M.T)
    {ϕ : ExtTensorAlgebra (M.d + 1)} (hϕ : MemTw M.w ϕ) {f : ℝ → ℝ}
    (hfeq : (fun ω => dualPairing ϕ ((paperSetup B M.hT).W_hat t ω)) =ᵐ[P]
      fun ω => f (MultiBrownian.W B t ω ⟨0, M.hd⟩)) :
    ∃ (G : ℂ → ℂ) (C : ℝ), Differentiable ℂ G ∧ 0 ≤ C ∧
      (∀ z : ℂ, ‖G z‖ ≤ C * Real.exp ‖z‖) ∧
      (∀ᵐ x : ℝ ∂volume, G x = (f x : ℂ)) := by
  sorry

section PillarD
open Complex Metric

/-! ### Helpers for Pillar D -/

/-- On `[0, ∞)`, `1 + r ^ 4` is dominated by `C * exp (ε * r)` for every `ε > 0`. -/
private lemma one_add_rpow4_le_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → 1 + r ^ 4 ≤ C * Real.exp (ε * r) := by
  have hpow : Tendsto (fun r : ℝ => r ^ 4 * Real.exp (-(ε * r))) atTop (𝓝 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
    have hscale : Tendsto (fun r : ℝ => ε * r) atTop atTop := tendsto_id.const_mul_atTop hε
    have heq : (fun r : ℝ => r ^ 4 * Real.exp (-(ε * r))) =
        fun r => (ε ^ 4)⁻¹ * ((ε * r) ^ 4 * Real.exp (-(ε * r))) := by
      funext r
      have hr : r ^ 4 = (ε ^ 4)⁻¹ * (ε * r) ^ 4 := by
        rw [← inv_pow, ← mul_pow, inv_mul_cancel_left₀ hε.ne']
      rw [hr, mul_assoc]
    simpa [heq] using (h0.comp hscale).const_mul ((ε ^ 4)⁻¹)
  have hone : Tendsto (fun r : ℝ => Real.exp (-(ε * r))) atTop (𝓝 0) := by
    have hneg : (fun r : ℝ => Real.exp (-(ε * r))) = fun r => Real.exp (-ε * r) :=
      funext fun _ => by ring_nf
    rw [hneg]
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hε))
  have hlim : Tendsto (fun r : ℝ => (1 + r ^ 4) * Real.exp (-(ε * r))) atTop (𝓝 0) := by
    simpa [add_mul] using hone.add hpow
  have hlt : ∀ᶠ r : ℝ in atTop, (1 + r ^ 4) * Real.exp (-(ε * r)) < 1 := by
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      eventually_ge_atTop (0 : ℝ)] with r hr hr0
    have hnn : 0 ≤ (1 + r ^ 4) * Real.exp (-(ε * r)) :=
      mul_nonneg (add_nonneg zero_le_one (pow_nonneg hr0 4)) (Real.exp_nonneg _)
    have habs : |(1 + r ^ 4) * Real.exp (-(ε * r))| < 1 := by
      simpa [Real.dist_eq, sub_zero] using hr
    rwa [abs_of_nonneg hnn] at habs
  rw [Filter.eventually_atTop] at hlt
  obtain ⟨R, hR⟩ := hlt
  set R0 := max R 0
  refine ⟨1 + R0 ^ 4,
    add_nonneg zero_le_one (pow_nonneg (le_max_of_le_right le_rfl) 4), fun r hr => ?_⟩
  rcases le_or_gt r R0 with hle | hgt
  · have hmono : 1 + r ^ 4 ≤ 1 + R0 ^ 4 := by gcongr
    exact hmono.trans
      (le_mul_of_one_le_right
        (add_nonneg zero_le_one (pow_nonneg (le_max_of_le_right le_rfl) 4))
        (Real.one_le_exp (mul_nonneg hε.le hr)))
  · have hRR : R ≤ r := (le_max_left R 0).trans hgt.le
    have hle_exp : 1 + r ^ 4 ≤ Real.exp (ε * r) := by
      calc 1 + r ^ 4
          = ((1 + r ^ 4) * Real.exp (-(ε * r))) * Real.exp (ε * r) := by
              rw [mul_assoc, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one]
        _ ≤ 1 * Real.exp (ε * r) := by gcongr; exact le_of_lt (hR r hRR)
        _ = Real.exp (ε * r) := one_mul _
    exact hle_exp.trans
      (le_mul_of_one_le_left (Real.exp_nonneg _)
        (le_add_of_nonneg_right (pow_nonneg (le_max_of_le_right le_rfl) 4)))

/-- Exponential type zero is preserved by precomposition with multiplication by `I` or `-I`. -/
private lemma expTypeZero_comp_mul_I {H : ℂ → ℂ} {u : ℂ} (hu : u = I ∨ u = -I)
    (htype0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖H z‖ ≤ C * Real.exp (ε * ‖z‖)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖H (u * z)‖ ≤ C * Real.exp (ε * ‖z‖) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := htype0 ε hε
  have hu1 : ‖u‖ = 1 := by rcases hu with rfl | rfl <;> simp
  refine ⟨C, hC0, fun z => ?_⟩
  simpa [norm_mul, hu1, one_mul] using hC (u * z)

/-- After rotating so the real axis becomes the imaginary axis, Phragmén–Lindelöf in the
right half-plane (applied to a damped function) lifts the real bound of `H`. -/
private lemma norm_le_mul_exp_of_damped_PL {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (htype0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖H z‖ ≤ C * Real.exp (ε * ‖z‖))
    {M : ℝ} (_hM0 : 0 ≤ M) (hM : ∀ x : ℝ, ‖H x‖ ≤ M) {u : ℂ} (hu : u = I ∨ u = -I)
    {z : ℂ} (hz : 0 ≤ z.re) {η : ℝ} (hη : 0 < η) :
    ‖H (u * z)‖ ≤ M * Real.exp (η * z.re) := by
  set K : ℂ → ℂ := fun ζ => H (u * ζ)
  have hK : Differentiable ℂ K := hH.comp (differentiable_id.const_mul u)
  have hK_type0 := expTypeZero_comp_mul_I (H := H) hu htype0
  set g : ℂ → ℂ := fun ζ => exp ((-η : ℂ) * ζ) * K ζ
  have hg : Differentiable ℂ g := (differentiable_id.const_mul _).cexp.mul hK
  have hgnorm : ∀ ζ : ℂ, ‖g ζ‖ = Real.exp (-(η * ζ.re)) * ‖K ζ‖ := by
    intro ζ
    rw [norm_mul, norm_exp]
    have : ((-η : ℂ) * ζ).re = -(η * ζ.re) := by
      simp [mul_re, ofReal_re, ofReal_im]
    rw [this]
  obtain ⟨C₁, hC₁0, hC₁⟩ := hK_type0 1 one_pos
  have hexp : ∃ c < (2 : ℝ), ∃ B,
      g =O[Bornology.cobounded ℂ ⊓ 𝓟 {ζ : ℂ | 0 < ζ.re}]
        fun ζ => Real.exp (B * ‖ζ‖ ^ c) := by
    refine ⟨(1 : ℝ), (by norm_num : (1 : ℝ) < 2), (1 : ℝ), ?_⟩
    refine Asymptotics.IsBigO.of_bound C₁ ?_
    rw [Filter.eventually_inf_principal]
    refine Eventually.of_forall fun ζ (hζ : 0 < ζ.re) => ?_
    have hexp1 : ‖Real.exp (1 * ‖ζ‖ ^ (1 : ℝ))‖ = Real.exp ‖ζ‖ := by
      rw [one_mul, Real.rpow_one, Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hle : Real.exp (-(η * ζ.re)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hη.le hζ.le))
    rw [hexp1, hgnorm]
    exact (mul_le_of_le_one_left (norm_nonneg _) hle).trans (by simpa [one_mul] using hC₁ ζ)
  have hre : Tendsto (fun x : ℝ => g x) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨Cη, hCη0, hCη⟩ := hK_type0 (η / 2) (half_pos hη)
    have hbound : ∀ᶠ x : ℝ in atTop, ‖g x‖ ≤ Cη * Real.exp (-(η / 2) * x) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have hKx : ‖K x‖ ≤ Cη * Real.exp ((η / 2) * x) := by
        have := hCη (x : ℂ)
        simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] using this
      rw [hgnorm, ofReal_re]
      calc Real.exp (-(η * x)) * ‖K x‖
          ≤ Real.exp (-(η * x)) * (Cη * Real.exp ((η / 2) * x)) := by gcongr
        _ = Cη * (Real.exp (-(η * x)) * Real.exp ((η / 2) * x)) := by ring
        _ = Cη * Real.exp (-(η / 2) * x) := by
            rw [← Real.exp_add]
            congr 2
            ring
    have hzero : Tendsto (fun x : ℝ => Cη * Real.exp (-(η / 2) * x)) atTop (𝓝 0) := by
      have hscale : Tendsto (fun x : ℝ => -(η / 2) * x) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr (half_pos hη))
      simpa [Function.comp_def] using
        tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hscale)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hzero (Eventually.of_forall fun _ => norm_nonneg _) hbound
  have him : ∀ t : ℝ, ‖g (t * I)‖ ≤ M := by
    intro t
    have hre0 : (t * I).re = 0 := by simp
    rw [hgnorm, hre0, mul_zero, neg_zero, Real.exp_zero, one_mul]
    -- `K (t * I) = H (u * t * I)` and `u * I` is real of modulus 1.
    have hKti : K (t * I) = H ((u * I) * (t : ℂ)) := by
      simp only [K]
      rw [mul_comm (t : ℂ) I, mul_assoc]
    have huI : u * I = -1 ∨ u * I = 1 := by
      rcases hu with rfl | rfl <;> simp [I_mul_I]
    rw [hKti]
    rcases huI with h | h
    · rw [h, neg_one_mul, ← ofReal_neg]
      simpa using hM (-t)
    · rw [h, one_mul]
      simpa using hM t
  have hg_le : ‖g z‖ ≤ M :=
    PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real hg.diffContOnCl hexp hre him hz
  have hKz : ‖K z‖ = Real.exp (η * z.re) * ‖g z‖ := by
    rw [hgnorm]
    have hpos : Real.exp (-(η * z.re)) * Real.exp (η * z.re) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc ‖K z‖
        = (Real.exp (-(η * z.re)) * ‖K z‖) * Real.exp (η * z.re) := by
            rw [mul_assoc, mul_comm (‖K z‖), ← mul_assoc, hpos, one_mul]
      _ = Real.exp (η * z.re) * (Real.exp (-(η * z.re)) * ‖K z‖) := by ring
  rw [hKz, mul_comm M]
  exact mul_le_mul_of_nonneg_left hg_le (Real.exp_nonneg _)

/-- An entire function of exponential type zero that is bounded on the real line
is bounded on the whole plane by the same constant. -/
private lemma entire_expTypeZero_bounded_of_bounded_on_real {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (htype0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖H z‖ ≤ C * Real.exp (ε * ‖z‖))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, ‖H x‖ ≤ M) :
    ∀ z : ℂ, ‖H z‖ ≤ M := by
  have hhalf : ∀ u : ℂ, u = I ∨ u = -I → ∀ z : ℂ, 0 ≤ z.re → ‖H (u * z)‖ ≤ M := by
    intro u hu z hz
    have hdamped : ∀ η : ℝ, 0 < η → ‖H (u * z)‖ ≤ M * Real.exp (η * z.re) :=
      fun η hη => norm_le_mul_exp_of_damped_PL hH htype0 hM0 hM hu hz hη
    have hlim : Tendsto (fun η : ℝ => M * Real.exp (η * z.re)) (𝓝[>] 0) (𝓝 M) := by
      have hcont : Continuous (fun η : ℝ => M * Real.exp (η * z.re)) := by fun_prop
      simpa [Real.exp_zero, mul_one] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (eventually_of_mem self_mem_nhdsWithin fun η hη => hdamped η (mem_Ioi.mp hη))
  intro w
  rcases le_or_gt 0 w.im with him | him
  · -- upper half-plane (including the real axis): `w = I * z` with `z = (-I) * w`.
    have hz : I * ((-I) * w) = w := by
      calc I * ((-I) * w) = (I * (-I)) * w := (mul_assoc _ _ _).symm
        _ = (-(I * I)) * w := by rw [mul_neg]
        _ = (-(-1)) * w := by rw [I_mul_I]
        _ = w := by simp
    have hre : 0 ≤ ((-I) * w).re := by
      have : ((-I) * w).re = w.im := by simp [mul_re, neg_re, I_re, I_im]
      rwa [this]
    have hbound := hhalf I (Or.inl rfl) ((-I) * w) hre
    rwa [hz] at hbound
  · -- lower half-plane: `w = (-I) * z` with `z = I * w`.
    have hz : (-I) * (I * w) = w := by
      calc (-I) * (I * w) = ((-I) * I) * w := (mul_assoc _ _ _).symm
        _ = (-(I * I)) * w := by rw [neg_mul]
        _ = (-(-1)) * w := by rw [I_mul_I]
        _ = w := by simp
    have hre : 0 ≤ (I * w).re := by
      have : (I * w).re = -w.im := by simp [mul_re, I_re, I_im]
      rw [this]
      exact le_of_lt (neg_pos.mpr him)
    have hbound := hhalf (-I) (Or.inr rfl) (I * w) hre
    rwa [hz] at hbound



/-- **Pillar D (Phragmén–Lindelöf + Liouville)**:
An entire function of exponential type zero with quartic growth on `ℝ` is a polynomial
of degree `≤ 4`. -/
lemma entire_expTypeZero_polyBound_is_poly4 {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (htype0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (ε * ‖z‖))
    (hpoly : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖F x‖ ≤ C * (1 + |x| ^ 4)) :
    ∃ a₀ a₁ a₂ a₃ a₄ : ℂ, ∀ z : ℂ,
      F z = a₀ + a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3 + a₄ * z ^ 4 := by
  -- Remainder after the degree-`≤ 4` Taylor polynomial, written via iterated `dslope`.
  set H1 : ℂ → ℂ := dslope F 0
  set H2 : ℂ → ℂ := dslope H1 0
  set H3 : ℂ → ℂ := dslope H2 0
  set H4 : ℂ → ℂ := dslope H3 0
  set H : ℂ → ℂ := dslope H4 0
  have hF_an : AnalyticOnNhd ℂ F univ := fun _ _ => hF.analyticAt _
  have hH1_an : AnalyticOnNhd ℂ H1 univ := hF_an.dslope 0
  have hH2_an : AnalyticOnNhd ℂ H2 univ := hH1_an.dslope 0
  have hH3_an : AnalyticOnNhd ℂ H3 univ := hH2_an.dslope 0
  have hH4_an : AnalyticOnNhd ℂ H4 univ := hH3_an.dslope 0
  have hH_an : AnalyticOnNhd ℂ H univ := hH4_an.dslope 0
  have hH : Differentiable ℂ H := fun z => (hH_an z (mem_univ z)).differentiableAt
  have hexpand : ∀ z : ℂ,
      F z = F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * H3 0 + z ^ 4 * H4 0 + z ^ 5 * H z := by
    intro z
    have e1 : F z = F 0 + z * H1 z := by
      have h := sub_smul_dslope F (0 : ℂ) z
      simp only [smul_eq_mul, sub_zero] at h
      rw [h]; abel
    have e2 : H1 z = H1 0 + z * H2 z := by
      have h := sub_smul_dslope H1 (0 : ℂ) z
      simp only [smul_eq_mul, sub_zero] at h
      rw [h]; abel
    have e3 : H2 z = H2 0 + z * H3 z := by
      have h := sub_smul_dslope H2 (0 : ℂ) z
      simp only [smul_eq_mul, sub_zero] at h
      rw [h]; abel
    have e4 : H3 z = H3 0 + z * H4 z := by
      have h := sub_smul_dslope H3 (0 : ℂ) z
      simp only [smul_eq_mul, sub_zero] at h
      rw [h]; abel
    have e5 : H4 z = H4 0 + z * H z := by
      have h := sub_smul_dslope H4 (0 : ℂ) z
      simp only [smul_eq_mul, sub_zero] at h
      rw [h]; abel
    calc F z = F 0 + z * H1 z := e1
      _ = F 0 + z * (H1 0 + z * H2 z) := by rw [e2]
      _ = F 0 + z * H1 0 + z ^ 2 * H2 z := by ring
      _ = F 0 + z * H1 0 + z ^ 2 * (H2 0 + z * H3 z) := by rw [e3]
      _ = F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * H3 z := by ring
      _ = F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * (H3 0 + z * H4 z) := by rw [e4]
      _ = F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * H3 0 + z ^ 4 * H4 z := by ring
      _ = F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * H3 0 + z ^ 4 * (H4 0 + z * H z) := by
          rw [e5]
      _ = F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * H3 0 + z ^ 4 * H4 0 + z ^ 5 * H z := by
          ring
  set P : ℂ → ℂ :=
    fun z => F 0 + z * H1 0 + z ^ 2 * H2 0 + z ^ 3 * H3 0 + z ^ 4 * H4 0
  have hFP : ∀ z, F z = P z + z ^ 5 * H z := hexpand
  set A : ℝ := ‖F 0‖ + ‖H1 0‖ + ‖H2 0‖ + ‖H3 0‖ + ‖H4 0‖
  have hA0 : 0 ≤ A := by positivity
  have hP_le : ∀ z : ℂ, ‖P z‖ ≤ A * (1 + ‖z‖ ^ 4) := by
    intro z
    have hpow : ∀ k : ℕ, k ≤ 4 → ‖z‖ ^ k ≤ 1 + ‖z‖ ^ 4 := fun k hk => by
      rcases le_or_gt ‖z‖ 1 with h | h
      · exact (pow_le_one₀ (norm_nonneg _) h).trans
          (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) 4))
      · exact (pow_le_pow_right₀ (le_of_lt h) hk).trans (le_add_of_nonneg_left zero_le_one)
    have htri :
        ‖P z‖ ≤ ‖F 0‖ + ‖H1 0‖ * ‖z‖ + ‖H2 0‖ * ‖z‖ ^ 2 +
          ‖H3 0‖ * ‖z‖ ^ 3 + ‖H4 0‖ * ‖z‖ ^ 4 := by
      simp only [P]
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
      refine le_trans (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl) ?_
      simp [norm_pow]
      exact le_of_eq (by ring)
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 4 := le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) 4)
    calc ‖P z‖
        ≤ ‖F 0‖ + ‖H1 0‖ * ‖z‖ + ‖H2 0‖ * ‖z‖ ^ 2 +
            ‖H3 0‖ * ‖z‖ ^ 3 + ‖H4 0‖ * ‖z‖ ^ 4 := htri
      _ ≤ ‖F 0‖ * (1 + ‖z‖ ^ 4) + ‖H1 0‖ * (1 + ‖z‖ ^ 4) +
            ‖H2 0‖ * (1 + ‖z‖ ^ 4) + ‖H3 0‖ * (1 + ‖z‖ ^ 4) +
            ‖H4 0‖ * (1 + ‖z‖ ^ 4) := by
          gcongr
          · exact le_mul_of_one_le_right (norm_nonneg _) h1
          · simpa using hpow 1 (by norm_num)
          · exact hpow 2 (by norm_num)
          · exact hpow 3 (by norm_num)
          · exact hpow 4 (by norm_num)
      _ = A * (1 + ‖z‖ ^ 4) := by ring
  -- `H` still has exponential type zero.
  have hH_type0 : ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖H z‖ ≤ C * Real.exp (ε * ‖z‖) := by
    intro ε hε
    obtain ⟨CF, hCF0, hCF⟩ := htype0 ε hε
    obtain ⟨Cexp, hCexp0, hCexp⟩ := one_add_rpow4_le_exp hε
    have hH_ball : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ‖H z‖ ≤ Mb := by
      have hc : IsCompact (closedBall (0 : ℂ) 1) := isCompact_closedBall _ _
      obtain ⟨z0, hz0, hzmax⟩ :=
        hc.exists_isMaxOn (nonempty_closedBall.mpr zero_le_one)
          (hH.continuous.norm.continuousOn)
      exact ⟨‖H z0‖, norm_nonneg _, fun z hz =>
        hzmax (mem_closedBall.mpr (by simpa using hz))⟩
    obtain ⟨Mb, hMb0, hMb⟩ := hH_ball
    refine ⟨CF + A * Cexp + Mb,
      add_nonneg (add_nonneg hCF0 (mul_nonneg hA0 hCexp0)) hMb0, fun z => ?_⟩
    rcases le_or_gt ‖z‖ 1 with hle | hgt
    · have hexp : 1 ≤ Real.exp (ε * ‖z‖) :=
        Real.one_le_exp (mul_nonneg hε.le (norm_nonneg _))
      have hC : Mb ≤ CF + A * Cexp + Mb :=
        le_add_of_nonneg_left (add_nonneg hCF0 (mul_nonneg hA0 hCexp0))
      exact (hMb z hle).trans
        (hC.trans (le_mul_of_one_le_right
          (add_nonneg (add_nonneg hCF0 (mul_nonneg hA0 hCexp0)) hMb0) hexp))
    · have hz1 : 1 ≤ ‖z‖ := hgt.le
      have hz_ne : z ≠ 0 := by
        intro hz; subst hz; rw [norm_zero] at hgt; linarith
      have hdiv : ‖H z‖ = ‖F z - P z‖ / ‖z‖ ^ 5 := by
        have hsub : F z - P z = z ^ 5 * H z := by rw [hFP z]; ring
        rw [hsub, norm_mul, norm_pow]
        exact (mul_div_cancel_left₀ _ (pow_ne_zero 5 (norm_ne_zero_iff.mpr hz_ne))).symm
      have hnum : ‖F z - P z‖ ≤ (CF + A * Cexp) * Real.exp (ε * ‖z‖) := by
        calc ‖F z - P z‖ ≤ ‖F z‖ + ‖P z‖ := norm_sub_le _ _
          _ ≤ CF * Real.exp (ε * ‖z‖) + A * (1 + ‖z‖ ^ 4) := by
              gcongr
              · exact hCF z
              · exact hP_le z
          _ ≤ CF * Real.exp (ε * ‖z‖) + A * (Cexp * Real.exp (ε * ‖z‖)) := by
              gcongr; exact hCexp ‖z‖ (norm_nonneg _)
          _ = (CF + A * Cexp) * Real.exp (ε * ‖z‖) := by ring
      have hden : 1 ≤ ‖z‖ ^ 5 := one_le_pow₀ hz1
      rw [hdiv]
      have hle' : ‖F z - P z‖ / ‖z‖ ^ 5 ≤ ‖F z - P z‖ :=
        div_le_self (norm_nonneg _) hden
      exact hle'.trans
        (hnum.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hMb0)
          (Real.exp_nonneg _)))
  obtain ⟨Cpoly, hCpoly0, hCpoly⟩ := hpoly
  -- `H` is bounded on the real line.
  have hH_real : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, ‖H x‖ ≤ M := by
    have hH_Icc : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ x : ℝ, |x| ≤ 1 → ‖H x‖ ≤ Mb := by
      have hc : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
      have hcont : ContinuousOn (fun x : ℝ => ‖H x‖) (Icc (-1) 1) :=
        (hH.continuous.comp Complex.continuous_ofReal).norm.continuousOn
      obtain ⟨x0, hx0, hxmax⟩ := hc.exists_isMaxOn (by simp) hcont
      exact ⟨‖H x0‖, norm_nonneg _, fun x hx => hxmax (abs_le.mp hx)⟩
    obtain ⟨Mb, hMb0, hMb⟩ := hH_Icc
    refine ⟨Mb + 2 * (Cpoly + A),
      add_nonneg hMb0 (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) (add_nonneg hCpoly0 hA0)),
      fun x => ?_⟩
    rcases le_or_gt |x| 1 with hle | hgt
    · exact (hMb x hle).trans (le_add_of_nonneg_right (by positivity))
    · have hxpos : 0 < |x| := lt_trans zero_lt_one hgt
      have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mp hxpos)
      have hdiv : ‖H x‖ = ‖F x - P x‖ / |x| ^ 5 := by
        have hsub : F (x : ℂ) - P (x : ℂ) = (x : ℂ) ^ 5 * H x := by rw [hFP x]; ring
        rw [hsub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_div_cancel_left₀ _ (pow_ne_zero 5 hxpos.ne')).symm
      have hnum : ‖F x - P x‖ ≤ (Cpoly + A) * (1 + |x| ^ 4) := by
        calc ‖F (x : ℂ) - P (x : ℂ)‖ ≤ ‖F (x : ℂ)‖ + ‖P (x : ℂ)‖ := norm_sub_le _ _
          _ ≤ Cpoly * (1 + |x| ^ 4) + A * (1 + ‖(x : ℂ)‖ ^ 4) := by
              gcongr
              · exact hCpoly x
              · exact hP_le x
          _ = (Cpoly + A) * (1 + |x| ^ 4) := by
              simp [Complex.norm_real, Real.norm_eq_abs]
              ring
      have h14 : 1 + |x| ^ 4 ≤ 2 * |x| ^ 4 := by
        have : (1 : ℝ) ≤ |x| ^ 4 := one_le_pow₀ hgt.le
        linarith
      rw [hdiv, div_le_iff₀ (pow_pos hxpos 5)]
      have hpow45 : |x| ^ 4 ≤ |x| ^ 5 :=
        pow_le_pow_right₀ hgt.le (by norm_num : 4 ≤ 5)
      calc ‖F x - P x‖
          ≤ (Cpoly + A) * (1 + |x| ^ 4) := hnum
        _ ≤ (Cpoly + A) * (2 * |x| ^ 4) := by gcongr
        _ = 2 * (Cpoly + A) * |x| ^ 4 := by ring
        _ ≤ 2 * (Cpoly + A) * |x| ^ 5 := by gcongr
        _ ≤ (Mb + 2 * (Cpoly + A)) * |x| ^ 5 := by
            gcongr
            exact le_add_of_nonneg_left hMb0
  obtain ⟨M, hM0, hM⟩ := hH_real
  have hH_all : ∀ z : ℂ, ‖H z‖ ≤ M :=
    entire_expTypeZero_bounded_of_bounded_on_real hH hH_type0 hM0 hM
  have hbdd : Bornology.IsBounded (Set.range H) :=
    (isBounded_iff_subset_closedBall (0 : ℂ)).2
      ⟨M, fun z hz => by
        obtain ⟨w, rfl⟩ := hz
        simpa [mem_closedBall, dist_zero_right] using hH_all w⟩
  obtain ⟨c, hc⟩ := hH.exists_const_forall_eq_of_bounded hbdd
  -- The constant vanishes because `H` tends to `0` at real infinity.
  have hH_atTop : Tendsto (fun x : ℝ => H x) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ᶠ x : ℝ in atTop, ‖H x‖ ≤ 2 * (Cpoly + A) / x := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      have hdiv : ‖H x‖ = ‖F x - P x‖ / x ^ 5 := by
        have hsub : F (x : ℂ) - P (x : ℂ) = (x : ℂ) ^ 5 * H x := by rw [hFP x]; ring
        have habs : |x| = x := abs_of_nonneg (le_of_lt hxpos)
        rw [hsub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, habs]
        exact (mul_div_cancel_left₀ _ (pow_ne_zero 5 hxpos.ne')).symm
      have hnum : ‖F x - P x‖ ≤ (Cpoly + A) * (1 + x ^ 4) := by
        calc ‖F (x : ℂ) - P (x : ℂ)‖ ≤ ‖F (x : ℂ)‖ + ‖P (x : ℂ)‖ := norm_sub_le _ _
          _ ≤ Cpoly * (1 + |x| ^ 4) + A * (1 + ‖(x : ℂ)‖ ^ 4) := by
              gcongr
              · exact hCpoly x
              · exact hP_le x
          _ = (Cpoly + A) * (1 + x ^ 4) := by
              simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hxpos)]
              ring
      have h14 : 1 + x ^ 4 ≤ 2 * x ^ 4 := by
        have : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx
        linarith
      rw [hdiv, div_le_iff₀ (pow_pos hxpos 5)]
      calc ‖F x - P x‖
          ≤ (Cpoly + A) * (1 + x ^ 4) := hnum
        _ ≤ (Cpoly + A) * (2 * x ^ 4) := by gcongr
        _ = 2 * (Cpoly + A) * x ^ 4 := by ring
        _ = (2 * (Cpoly + A) / x) * x ^ 5 := by
            have : x ^ 5 = x ^ 4 * x := by ring
            field_simp [hxpos.ne']
    have hzero : Tendsto (fun x : ℝ => 2 * (Cpoly + A) / x) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        tendsto_inv_atTop_zero.const_mul (2 * (Cpoly + A))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hzero
      (Eventually.of_forall fun _ => norm_nonneg _) hbound
  have hc0 : c = 0 := by
    have hconst : Tendsto (fun n : ℕ => H (n : ℝ)) atTop (𝓝 c) :=
      tendsto_const_nhds.congr fun n => (hc (n : ℂ)).symm
    have hzero : Tendsto (fun n : ℕ => H (n : ℝ)) atTop (𝓝 0) :=
      hH_atTop.comp tendsto_natCast_atTop_atTop
    exact tendsto_nhds_unique hconst hzero
  refine ⟨F 0, H1 0, H2 0, H3 0, H4 0, fun z => ?_⟩
  have := hFP z
  simp only [P] at this
  rw [this, hc z, hc0, mul_zero, add_zero]
  ring

end PillarD

/-! ## Part 5: Complete assembly of `not_affine_riccati_duality_mpr` (sorry-free modulo A–D) -/

theorem not_affine_riccati_duality_mpr (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ¬ ∀ u₀ : FreeTensorAlgebra (M.d + 1),
      SignatureTransformFinite P (paperSetup B M.hT) u₀.1 →
      Nonempty (ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1) →
      ∃ sol : ClassicalRiccatiSolution M.w M.T riccatiOp u₀.1,
        ∀ t ∈ Icc 0 M.T,
          Integrable (fun ω => Real.exp (dualPairing u₀.1
            ((paperSetup B M.hT).W_hat M.T ω))) P ∧
          P[fun ω => Real.exp (dualPairing u₀.1 ((paperSetup B M.hT).W_hat M.T ω)) |
            (paperSetup B M.hT).signatureFiltration.σAlg t] =ᵐ[P]
            fun ω => Real.exp (dualPairing (sol.ψ (M.T - t))
              ((paperSetup B M.hT).W_hat t ω)) := by
  intro hthm
  obtain ⟨v₁, hv₁_pos_le, ⟨C_poly, hC_poly0, hv₁_poly⟩, hv₁_nonpos, hv₁_tendsto, hcond⟩ :=
    exists_scaled_survival_function M B
  -- For every `lam ≥ 1`, obtain an entire `F_lam` of exponential type `≤ lam^(-1/3)`
  -- agreeing a.e. on `ℝ` with `log ∘ v₁`.
  have hex_F : ∀ lam : ℝ, 1 ≤ lam →
      ∃ (F : ℂ → ℂ) (C : ℝ), Differentiable ℂ F ∧ 0 ≤ C ∧
        (∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (lam ^ (-(1 / 3 : ℝ)) * ‖z‖)) ∧
        (∀ᵐ x : ℝ ∂volume, F x = (Real.log (v₁ x) : ℂ)) := by
    intro lam hlam
    have hlam_pos : 0 < lam := by linarith
    set u₀ : FreeTensorAlgebra (M.d + 1) :=
      ⟨counterexampleU0 M.hd lam, counterexampleU0_isFinitelySupported M.hd lam⟩
    obtain ⟨sol, hsol⟩ := hthm u₀
      (signatureTransformFinite_counterexampleU0 M B lam)
      ⟨counterexampleRiccatiSol M lam⟩
    set s_lam := lam ^ (-(2 / 3 : ℝ)) * (M.T / 2)
    set t_lam := M.T - s_lam
    have hs_pos : 0 < s_lam := mul_pos (Real.rpow_pos_of_pos hlam_pos _) (half_pos M.hT)
    have hs_le : s_lam ≤ M.T / 2 := by
      have h1 : lam ^ (-(2 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlam (by norm_num)
      have hT0 : 0 ≤ M.T / 2 := le_of_lt (half_pos M.hT)
      simpa [s_lam] using mul_le_of_le_one_left hT0 h1
    have ht_pos : 0 < t_lam := by
      change 0 < M.T - s_lam
      linarith [hs_le, half_pos M.hT]
    have ht_mem : t_lam ∈ Icc 0 M.T :=
      ⟨ht_pos.le, sub_le_self _ (le_of_lt hs_pos)⟩
    have hs_mem : M.T - t_lam ∈ Icc 0 M.T := by
      have hst : M.T - t_lam = s_lam := by simp [t_lam]
      rw [hst]
      exact ⟨hs_pos.le, hs_le.trans (by linarith [M.hT])⟩
    -- Subtract `u₀` from `sol.ψ (M.T - t_lam)` and take logs.
    set ϕ : ExtTensorAlgebra (M.d + 1) := sol.ψ (M.T - t_lam) - u₀.1
    have hϕ_mem : MemTw M.w ϕ := by
      have h1 := sol.mem_Tw (M.T - t_lam) hs_mem
      have h2 := (counterexampleRiccatiSol M lam).mem_Tw 0 ⟨le_rfl, M.hT.le⟩
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (M.w.pos n).le (levelNorm.nonneg _ _))
        (fun n => ?_) (h1.add h2)
      -- Triangle inequality on `levelNorm`: `‖a - b‖_n ≤ ‖a‖_n + ‖b‖_n`.
      have htri : ϕ.levelNorm n ≤ (sol.ψ (M.T - t_lam)).levelNorm n + u₀.1.levelNorm n := by
        have hϕ : ϕ = sol.ψ (M.T - t_lam) + (-(1 : ℝ)) • u₀.1 := by
          ext I
          change (sol.ψ (M.T - t_lam)).coeff I - u₀.1.coeff I =
            (sol.ψ (M.T - t_lam)).coeff I + (-1) * u₀.1.coeff I
          ring
        calc ϕ.levelNorm n
            = (sol.ψ (M.T - t_lam) + (-(1 : ℝ)) • u₀.1).levelNorm n := by rw [hϕ]
          _ ≤ (sol.ψ (M.T - t_lam)).levelNorm n + ((-(1 : ℝ)) • u₀.1).levelNorm n :=
              levelNorm.add_le _ _ _
          _ = (sol.ψ (M.T - t_lam)).levelNorm n + u₀.1.levelNorm n := by
              rw [levelNorm.smul, abs_neg, abs_one, one_mul]
      have hunorm : u₀.1.levelNorm n =
          ((counterexampleRiccatiSol M lam).ψ 0).levelNorm n := rfl
      rw [hunorm] at htri
      exact (mul_le_mul_of_nonneg_left htri (M.w.pos n).le).trans_eq (mul_add _ _ _)
    set f_log : ℝ → ℝ :=
      fun x => Real.log (v₁ (lam ^ (1 / 3 : ℝ) * x))
    have hlog_eq : (fun ω => dualPairing ϕ ((paperSetup B M.hT).W_hat t_lam ω)) =ᵐ[P]
        fun ω => f_log (MultiBrownian.W B t_lam ω ⟨0, M.hd⟩) := by
      have hce := (hsol t_lam ht_mem).2.symm.trans (hcond lam hlam)
      have hsumm := (paperSetup B M.hT).factorial_moment_control 1 le_rfl (fun _ => 1)
        (fun _ => zero_le_one) ⟨1, fun _ => by simp⟩ ht_pos.le ht_mem.2
      filter_upwards [hce, hsumm.1] with ω hω hWsum
      have hdp_sub :
          dualPairing ϕ ((paperSetup B M.hT).W_hat t_lam ω) =
            dualPairing (sol.ψ (M.T - t_lam)) ((paperSetup B M.hT).W_hat t_lam ω) -
              dualPairing u₀.1 ((paperSetup B M.hT).W_hat t_lam ω) := by
        -- Follows from summability of both `levelInner` series via Cauchy-Schwarz + `MemTw` + `hWsum`.
        have hcs_sum : ∀ a : ExtTensorAlgebra (M.d + 1), MemTw M.w a →
            Summable (fun n => a.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n) := by
          intro a ha
          obtain ⟨K, hK⟩ : ∃ K, ∀ n, a.levelNorm n ≤ K := by
            refine ⟨∑' n, M.w n * a.levelNorm n, fun n => ?_⟩
            have hw1 : 1 ≤ M.w n := by simpa [M.w.w_zero] using M.w.mono (Nat.zero_le n)
            calc a.levelNorm n ≤ M.w n * a.levelNorm n :=
                  le_mul_of_one_le_left (levelNorm.nonneg _ _) hw1
              _ ≤ ∑' k, M.w k * a.levelNorm k :=
                  ha.le_tsum n fun k _ => mul_nonneg (M.w.pos k).le (levelNorm.nonneg _ _)
          refine Summable.of_norm_bounded (hWsum.mul_left K) fun n => ?_
          simp only [Real.norm_eq_abs, one_mul]
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq (wordsOfLength (M.d + 1) n)
            (fun I => a.coeff I) (fun I => ((paperSetup B M.hT).W_hat t_lam ω).coeff I)
          have hle : |a.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n| ≤
              a.levelNorm n * ((paperSetup B M.hT).W_hat t_lam ω).levelNorm n := by
            unfold levelInner levelNorm levelNormSq
            rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
            exact Real.abs_le_sqrt hcs
          exact hle.trans (mul_le_mul_of_nonneg_right (hK n) (levelNorm.nonneg _ _))
        have hsub : ∀ n, ϕ.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n =
            (sol.ψ (M.T - t_lam)).levelInner ((paperSetup B M.hT).W_hat t_lam ω) n -
              u₀.1.levelInner ((paperSetup B M.hT).W_hat t_lam ω) n := fun n => by
          unfold levelInner
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun I _ => ?_
          change ((sol.ψ (M.T - t_lam)).coeff I - u₀.1.coeff I) * _ = _
          ring
        simp only [dualPairing, hsub]
        exact (hcs_sum _ (sol.mem_Tw _ hs_mem)).tsum_sub
          (hcs_sum _ ((counterexampleRiccatiSol M lam).mem_Tw 0 ⟨le_rfl, M.hT.le⟩))
      have hv_pos := (hv₁_pos_le (lam ^ (1 / 3 : ℝ) * MultiBrownian.W B t_lam ω ⟨0, M.hd⟩)).1
      have hlog := congrArg Real.log hω
      rw [Real.log_exp, Real.log_mul (Real.exp_pos _).ne' hv_pos.ne', Real.log_exp] at hlog
      linarith [hdp_sub, hlog]
    obtain ⟨G, C, hG_diff, hC0, hG_bd, hG_ae⟩ :=
      exists_entire_expTypeOne_of_memTw M B ht_pos ht_mem.2 hϕ_mem hlog_eq
    -- Rescale `F(z) = G(lam^(-1/3) * z)`.
    set c : ℝ := lam ^ (-(1 / 3 : ℝ))
    have hc_pos : 0 < c := Real.rpow_pos_of_pos hlam_pos _
    refine ⟨fun z => G ((c : ℂ) * z), C,
      hG_diff.comp (differentiable_const _ |>.mul differentiable_id), hC0, fun z => ?_, ?_⟩
    · calc ‖G ((c : ℂ) * z)‖ ≤ C * Real.exp ‖(c : ℂ) * z‖ := hG_bd _
        _ = C * Real.exp (c * ‖z‖) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_pos.le]
    · -- Scaling `x ↦ c * x` preserves Lebesgue null sets.
      have hscale : ∀ᵐ x : ℝ ∂volume,
          G ((c * x : ℝ) : ℂ) = (Real.log (v₁ (lam ^ (1 / 3 : ℝ) * (c * x))) : ℂ) :=
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hc_pos.ne').ae hG_ae
      filter_upwards [hscale] with x hx
      have hcancel : lam ^ (1 / 3 : ℝ) * (c * x) = x := by
        rw [← mul_assoc, show c = lam ^ (-(1 / 3 : ℝ)) from rfl,
          ← Real.rpow_add hlam_pos, add_neg_cancel, Real.rpow_zero, one_mul]
      have hx' : G ((c : ℂ) * (x : ℂ)) =
          (Real.log (v₁ (lam ^ (1 / 3 : ℝ) * (c * x))) : ℂ) := by
        simpa [smul_eq_mul, Complex.ofReal_mul] using hx
      rw [hcancel] at hx'
      exact hx' 
  -- Fix `F := F_1` and show `F_lam = F` for all `lam ≥ 1` by the Identity Theorem.
  obtain ⟨F, C₁, hF_diff, -, -, hF_ae⟩ := hex_F 1 le_rfl
  have hF_type0 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (ε * ‖z‖) := by
    intro ε hε
    set lam : ℝ := max 1 (ε⁻¹ ^ (3 : ℕ))
    have hlam1 : 1 ≤ lam := le_max_left _ _
    have hlam_pos : 0 < lam := by linarith
    obtain ⟨F_lam, C_lam, hFlam_diff, hClam0, hFlam_bd, hFlam_ae⟩ := hex_F lam hlam1
    -- `F = F_lam` a.e. on `ℝ`, hence everywhere on `ℝ` by continuity, hence on `ℂ` by analyticity.
    have heq_real : ∀ x : ℝ, F x = F_lam x := by
      have hae : (fun x : ℝ => F x) =ᵐ[volume] fun x : ℝ => F_lam x := by
        filter_upwards [hF_ae, hFlam_ae] with x h1 h2
        rw [h1, h2]
      have heq_fun :=
        (Continuous.ae_eq_iff_eq volume
          (hF_diff.continuous.comp Complex.continuous_ofReal)
          (hFlam_diff.continuous.comp Complex.continuous_ofReal)).mp hae
      intro x
      exact congrFun heq_fun x
    have heq_all : F = F_lam := by
      have hF_an : AnalyticOnNhd ℂ F univ :=
        fun z _ => hF_diff.analyticAt z
      have hFlam_an : AnalyticOnNhd ℂ F_lam univ :=
        fun z _ => hFlam_diff.analyticAt z
      have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = F_lam z := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin] at hU
        obtain ⟨V, hVopen, h0V, hVU⟩ := hU
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen 0 h0V
        refine ⟨((r / 2 : ℝ) : ℂ), hVU ⟨hball ?_, ?_⟩, heq_real (r / 2)⟩
        · have hdist : dist ((r / 2 : ℝ) : ℂ) (0 : ℂ) = r / 2 := by
            rw [dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (half_pos hr)]
          exact hdist.trans_lt (half_lt_self hr)
        · exact Complex.ofReal_ne_zero.mpr (half_pos hr).ne' 
      funext z
      exact hF_an.eqOn_of_preconnected_of_frequently_eq hFlam_an isPreconnected_univ
        (mem_univ 0) hfreq (mem_univ z)
    refine ⟨C_lam, hClam0, fun z => ?_⟩
    rw [heq_all]
    have hpow_le : lam ^ (-(1 / 3 : ℝ)) ≤ ε := by
      have h1 : ε⁻¹ ^ (3 : ℕ) ≤ lam := le_max_right _ _
      have h2 : lam ^ (-(1 / 3 : ℝ)) ≤ (ε⁻¹ ^ (3 : ℕ)) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      refine h2.trans (le_of_eq ?_)
      have hεpos : 0 < ε⁻¹ := inv_pos.mpr hε
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hεpos)]
      have hmul : ((3 : ℕ) : ℝ) * (-(1 / 3 : ℝ)) = -1 := by norm_num
      rw [hmul, Real.rpow_neg_one, inv_inv]
    exact (hFlam_bd z).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg z))) hClam0)
  -- `F` has quartic polynomial bound on `ℝ` (from `hF_ae` + continuity + `hv₁_poly`).
  have hF_real_bounds : ∀ x : ℝ, (F x).im = 0 ∧
      -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0 := by
    have h_ae : ∀ᵐ x : ℝ ∂volume,
        (F x).im = 0 ∧ -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0 := by
      filter_upwards [hF_ae] with x hx
      rw [hx]
      refine ⟨Complex.ofReal_im _, ?_, ?_⟩
      · simpa [Complex.ofReal_re] using hv₁_poly x
      · simpa [Complex.ofReal_re] using Real.log_nonpos (hv₁_pos_le x).1.le (hv₁_pos_le x).2
    have hclosed : IsClosed {x : ℝ | (F x).im = 0 ∧
        -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0} := by
      have hcont : Continuous (fun x : ℝ => F x) :=
        hF_diff.continuous.comp Complex.continuous_ofReal
      exact (isClosed_eq (Complex.continuous_im.comp hcont) continuous_const).inter <|
        (isClosed_le (continuous_const.mul (continuous_const.add (continuous_abs.pow 4)))
          (Complex.continuous_re.comp hcont)).inter
        (isClosed_le (Complex.continuous_re.comp hcont) continuous_const)
    have hdense : Dense {x : ℝ | (F x).im = 0 ∧
        -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0} := by
      refine dense_iff_inter_open.mpr fun U hU hUne => ?_
      have hpos : 0 < volume U := hU.measure_pos volume hUne
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hsub : U ⊆ {x : ℝ | (F x).im = 0 ∧
          -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0}ᶜ :=
        Set.disjoint_iff_inter_eq_empty.mpr hempty |>.subset_compl_right
      exact hpos.ne' (measure_mono_null hsub h_ae)
    intro x
    have hx : x ∈ {x : ℝ | (F x).im = 0 ∧ -C_poly * (1 + |x| ^ 4) ≤ (F x).re ∧ (F x).re ≤ 0} := by
      rw [← hclosed.closure_eq, hdense.closure_eq]
      exact mem_univ x
    exact hx
  have hF_poly : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖F x‖ ≤ C * (1 + |x| ^ 4) := by
    refine ⟨C_poly, hC_poly0, fun x => ?_⟩
    obtain ⟨him, hlo, hhi⟩ := hF_real_bounds x
    have hnorm : ‖F x‖ = |(F x).re| := by
      have hFx : F x = ((F x).re : ℂ) := Complex.ext (by simp) him
      rw [hFx, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    rw [hnorm, abs_of_nonpos hhi]
    linarith
  -- Apply Pillar D: `F` is a polynomial of degree `≤ 4`.
  obtain ⟨a₀, a₁, a₂, a₃, a₄, hF_eq⟩ := entire_expTypeZero_polyBound_is_poly4 hF_diff hF_type0 hF_poly
  -- On `(-∞, 0]`, `F` is bounded between `log (v₁ 0)` and `0` (by `hv₁_nonpos` + density).
  have hF_nonpos : ∀ x : ℝ, x ≤ 0 → Real.log (v₁ 0) ≤ (F x).re ∧ (F x).re ≤ 0 := by
    have h_ae : ∀ᵐ x : ℝ ∂volume, x ≤ 0 → Real.log (v₁ 0) ≤ (F x).re := by
      filter_upwards [hF_ae] with x hx hx0
      rw [hx, Complex.ofReal_re]
      exact Real.log_le_log (hv₁_pos_le 0).1 (hv₁_nonpos x hx0)
    intro x hx
    refine ⟨?_, (hF_real_bounds x).2.2⟩
    by_contra hlt
    push Not at hlt
    have hopen : IsOpen {y : ℝ | y < 0 ∧ (F y).re < Real.log (v₁ 0)} :=
      isOpen_Iio.inter (isOpen_lt (Complex.continuous_re.comp
        (hF_diff.continuous.comp Complex.continuous_ofReal)) continuous_const)
    have hne : {y : ℝ | y < 0 ∧ (F y).re < Real.log (v₁ 0)}.Nonempty := by
      have hcont : Continuous (fun y : ℝ => (F y).re) :=
        Complex.continuous_re.comp (hF_diff.continuous.comp Complex.continuous_ofReal)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
        ((Real.log (v₁ 0) - (F x).re) / 2) (by linarith)
      refine ⟨x - δ / 2, by linarith, ?_⟩
      have hd : dist (x - δ / 2) x < δ := by
        rw [Real.dist_eq, show x - δ / 2 - x = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
        linarith
      have h := hball hd
      rw [Real.dist_eq, abs_lt] at h
      linarith
    have hpos := hopen.measure_pos volume hne
    have hsub : {y : ℝ | y < 0 ∧ (F y).re < Real.log (v₁ 0)} ⊆
        {y : ℝ | y ≤ 0 → Real.log (v₁ 0) ≤ (F y).re}ᶜ := by
      intro y ⟨hy0, hylt⟩ h
      exact not_le.mpr hylt (h hy0.le)
    exact hpos.ne' (measure_mono_null hsub h_ae)
  -- Real part of `F(x)` is a real degree-4 polynomial bounded on `(-∞, 0]`, hence constant!
  have hre_poly : ∀ x : ℝ, (F x).re =
      a₀.re + a₁.re * x + a₂.re * x ^ 2 + a₃.re * x ^ 3 + a₄.re * x ^ 4 := by
    intro x
    rw [hF_eq x]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_succ]
  obtain ⟨ha1, ha2, ha3, ha4⟩ := poly4_const_of_bdd_nonpos (L := Real.log (v₁ 0)) fun x hx => by
    rw [← hre_poly x]; exact hF_nonpos x hx
  have hF_const : ∀ x : ℝ, (F x).re = a₀.re := fun x => by
    rw [hre_poly x, ha1, ha2, ha3, ha4]; ring
  -- Contradiction: `v₁ x → 0` as `x → +∞`, so `log (v₁ x) < a₀.re - 1` for all sufficiently large `x`.
  have hev : ∀ᶠ x : ℝ in atTop, v₁ x < Real.exp (a₀.re - 1) :=
    hv₁_tendsto.eventually (gt_mem_nhds (Real.exp_pos _))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  -- On `(R, R + 1)` (positive Lebesgue measure), `F x = log (v₁ x)` a.e., giving `a₀.re < a₀.re - 1`.
  have hpos : 0 < volume (Ioo R (R + 1)) := by
    rw [Real.volume_Ioo]; norm_num
  have hsub : Ioo R (R + 1) ⊆ {x : ℝ | F x = (Real.log (v₁ x) : ℂ)}ᶜ := by
    intro x ⟨hxR, _⟩ hxEq
    have hre : a₀.re = Real.log (v₁ x) := by
      rw [← hF_const x, hxEq, Complex.ofReal_re]
    have hlt : v₁ x < Real.exp (a₀.re - 1) := hR x hxR.le
    have hlog : Real.log (v₁ x) < a₀.re - 1 := by
      rw [← Real.log_exp (a₀.re - 1)]
      exact Real.log_lt_log (hv₁_pos_le x).1 hlt
    linarith
  exact hpos.ne' (measure_mono_null hsub hF_ae)

end SignatureVolatility

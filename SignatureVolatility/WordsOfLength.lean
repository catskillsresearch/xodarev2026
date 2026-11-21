import SignatureVolatility.Letter
import SignatureVolatility.Word
import SignatureVolatility.Preliminaries

namespace SignatureVolatility

def wordsOfLength (d : ℕ) : ℕ → Finset (Word d)
  | 0 => {[]}
  | n + 1 =>
    (Finset.univ : Finset (Fin d)).biUnion fun i =>
      (wordsOfLength d n).map ⟨fun I => i :: I, fun _ _ h => (List.cons.inj h).2⟩

namespace wordsOfLength

lemma mem {d : ℕ} : ∀ {n : ℕ} {I : Word d}, I ∈ wordsOfLength d n ↔ I.length = n
  | 0, [] => by simp [wordsOfLength]
  | 0, _ :: _ => by simp [wordsOfLength]
  | n + 1, [] => by simp [wordsOfLength]
  | n + 1, i :: I => by
    simp only [wordsOfLength, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map,
      List.length_cons, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨a, J, hJ, hcons⟩
      cases hcons
      exact wordsOfLength.mem.mp hJ
    · intro hlen
      exact ⟨i, I, wordsOfLength.mem.mpr hlen, rfl⟩

lemma succ {d : ℕ} (n : ℕ) (F : Word d → ℝ) :
    ∑ I ∈ wordsOfLength d (n + 1), F I =
      ∑ i : Fin d, ∑ J ∈ wordsOfLength d n, F (i :: J) := by
  classical
  let emb (i : Fin d) : Word d ↪ Word d :=
    ⟨fun I => i :: I, fun _ _ h => (List.cons.inj h).2⟩
  let t (i : Fin d) : Finset (Word d) := (wordsOfLength d n).map (emb i)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin d))) t := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 ?_
    intro L hLi hLj
    obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hLi
    obtain ⟨_, _, hcons⟩ := Finset.mem_map.mp hLj
    exact hij (List.cons.inj hcons).1.symm
  -- `wordsOfLength d (n+1)` is definitionally the indicated biUnion.
  change ∑ I ∈ Finset.univ.biUnion t, F I = ∑ i : Fin d, ∑ J ∈ wordsOfLength d n, F (i :: J)
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ x ∈ t i, F x = ∑ J ∈ wordsOfLength d n, F (i :: J)
  dsimp [t, emb]
  rw [Finset.sum_map]
  rfl

lemma take_drop_sq (d : ℕ) :
    ∀ (k n : ℕ), k ≤ n → ∀ (f g : Word d → ℝ),
      ∑ I ∈ wordsOfLength d n, (f (I.take k) * g (I.drop k)) ^ 2 =
        (∑ J ∈ wordsOfLength d k, f J ^ 2) * (∑ K ∈ wordsOfLength d (n - k), g K ^ 2)
  | 0, n, _, f, g => by
    simp [wordsOfLength, mul_pow, Finset.mul_sum]
  | k + 1, 0, hk, _, _ => absurd hk (Nat.not_succ_le_zero k)
  | k + 1, n + 1, hk, f, g => by
    have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
    rw [Nat.add_sub_add_right, wordsOfLength.succ, wordsOfLength.succ]
    simp only [List.take, List.drop]
    have hstep : ∀ i : Fin d,
        ∑ J ∈ wordsOfLength d n, (f (i :: J.take k) * g (J.drop k)) ^ 2 =
          (∑ J ∈ wordsOfLength d k, f (i :: J) ^ 2) *
            (∑ K ∈ wordsOfLength d (n - k), g K ^ 2) :=
      fun i => wordsOfLength.take_drop_sq d k n hk' (fun J => f (i :: J)) g
    simp_rw [hstep, ← Finset.sum_mul]

end wordsOfLength

end SignatureVolatility

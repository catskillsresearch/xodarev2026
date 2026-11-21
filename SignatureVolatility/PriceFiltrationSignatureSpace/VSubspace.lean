import SignatureVolatility.PriceFiltrationSignatureSpace
import SignatureVolatility.WordsOfLength
import SignatureVolatility.Word


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace PriceFiltrationSignatureSpace

variable {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
  {d : ℕ}

def V_subspace (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) : Submodule ℝ H_S :=
  Submodule.span ℝ {PFS.Y I | (I : Word (d + 1)) (_ : I.length ≤ N)}

namespace V_subspace

lemma mono (PFS : PriceFiltrationSignatureSpace H_S d) {M N : ℕ} (hMN : M ≤ N) :
    PFS.V_subspace M ≤ PFS.V_subspace N := by
  apply Submodule.span_mono
  rintro x ⟨I, hI, rfl⟩
  exact ⟨I, hI.trans hMN, rfl⟩

lemma finiteDimensional (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) :
    FiniteDimensional ℝ (PFS.V_subspace N) := by
  let S_words : Finset (Word (d + 1)) :=
    (Finset.range (N + 1)).biUnion (wordsOfLength (d + 1))
  have hset : {PFS.Y I | (I : Word (d + 1)) (_ : I.length ≤ N)} =
      (S_words.image PFS.Y : Set H_S) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      S_words, Finset.mem_biUnion, Finset.mem_range, wordsOfLength.mem]
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I, ⟨I.length, Nat.lt_succ_of_le hI, rfl⟩, rfl⟩
    · rintro ⟨I, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨I, Nat.le_of_lt_succ hk, rfl⟩
  rw [V_subspace, hset]
  exact FiniteDimensional.span_of_finite ℝ (Finset.finite_toSet _)

lemma topologicalClosure_eq (PFS : PriceFiltrationSignatureSpace H_S d) (N : ℕ) :
    (PFS.V_subspace N).topologicalClosure = PFS.V_subspace N := by
  haveI : FiniteDimensional ℝ (PFS.V_subspace N) := finiteDimensional PFS N
  exact Submodule.IsClosed.topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)

end V_subspace

end PriceFiltrationSignatureSpace

end SignatureVolatility

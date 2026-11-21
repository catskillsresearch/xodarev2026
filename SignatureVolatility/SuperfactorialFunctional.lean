module

public import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
public import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
public import SignatureVolatility.PureBrownianWord
public import SignatureVolatility.WordsOfLength


@[expose] public section

noncomputable section

namespace SignatureVolatility

def superfactorialFunctional (α : ℝ) : ExtTensorAlgebra 2 :=
  ⟨fun I => if I = pureBrownianWord I.length then (I.length.factorial : ℝ) * α ^ I.length else 0⟩

namespace superfactorialFunctional

lemma levelNormSq (α : ℝ) (n : ℕ) :
    (superfactorialFunctional α).levelNormSq n = ((n.factorial : ℝ) * α ^ n) ^ 2 := by
  unfold ExtTensorAlgebra.levelNormSq superfactorialFunctional
  have hmem : pureBrownianWord n ∈ wordsOfLength 2 n := by
    rw [wordsOfLength.mem]
    dsimp [pureBrownianWord]
    simp [List.length_replicate]
  rw [Finset.sum_eq_single (pureBrownianWord n)]
  · dsimp [pureBrownianWord]
    simp [List.length_replicate, pow_two]
  · intro I hI hne
    have hlen : I.length = n := (wordsOfLength.mem (d := 2)).1 hI
    simp [hlen, hne]
  · intro hnot
    exact absurd hmem hnot

end superfactorialFunctional

end SignatureVolatility

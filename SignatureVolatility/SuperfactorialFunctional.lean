import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq
import SignatureVolatility.PureBrownianWord


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def superfactorialFunctional (α : ℝ) : ExtTensorAlgebra 2 :=
  ⟨fun I => if I = pureBrownianWord I.length then (I.length.factorial : ℝ) * α ^ I.length else 0⟩

namespace superfactorialFunctional

lemma levelNormSq (α : ℝ) (n : ℕ) :
    (superfactorialFunctional α).levelNormSq n = ((n.factorial : ℝ) * α ^ n) ^ 2 := by
  unfold ExtTensorAlgebra.levelNormSq superfactorialFunctional
  have hmem : pureBrownianWord n ∈ wordsOfLength 2 n := by
    rw [wordsOfLength.mem, pureBrownianWord, List.length_replicate]
  rw [Finset.sum_eq_single (pureBrownianWord n)]
  · have hlen : (pureBrownianWord n).length = n := List.length_replicate _ _
    simp [hlen]
  · intro I hI hne
    have hlen : I.length = n := wordsOfLength.mem.mp hI
    rw [hlen, if_neg hne]
    ring
  · intro hnot
    exact absurd hmem hnot

end superfactorialFunctional

end SignatureVolatility

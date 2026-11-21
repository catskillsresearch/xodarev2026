import SignatureVolatility.HypH1
import SignatureVolatility.ExtTensorAlgebra.IsFinitelySupported
import SignatureVolatility.Weight
import SignatureVolatility.MemL2w
import SignatureVolatility.ExtTensorAlgebra.ExtTensorAlgebra
import SignatureVolatility.ExtTensorAlgebra.LevelNormSq


noncomputable section

namespace SignatureVolatility

lemma hypH1_of_isFinitelySupported {d : ℕ} (w : Weight) {ℓ : ExtTensorAlgebra (d + 1)}
    (hfin : ExtTensorAlgebra.IsFinitelySupported ℓ) : HypH1 w ℓ := by
  rcases hfin with ⟨N, hN⟩
  refine ⟨summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_⟩
  have hgt : N < n := Nat.lt_of_not_ge fun hle => hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  have hl0 : ℓ.levelNormSq n = 0 := by
    unfold ExtTensorAlgebra.levelNormSq
    refine Finset.sum_eq_zero fun I hI => ?_
    have hlen : I.length = n := wordsOfLength.mem.mp hI
    rw [hN I (hlen ▸ hgt)]
    ring
  rw [hl0, zero_div]

end SignatureVolatility

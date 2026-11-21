import SignatureVolatility.ClassicalRiccatiSolution
import SignatureVolatility.Weight


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

theorem remark_2_19_black_scholes_riccati (c₁ : ℝ) :
    let idx1 : Letter 2 := (0 : Fin 1).succ
    let u₀ : ExtTensorAlgebra 2 := c₁ • ExtTensorAlgebra.basisWord [idx1]
    (riccatiOpBounded 1 u₀).coeff [] = (1 / 2 : ℝ) * c₁ ^ 2 := by
  intro idx1 u₀
  have hshift0 : (rightShift 0 u₀).coeff [] = 0 := by
    simp [rightShift, u₀, ExtTensorAlgebra.basisWord, idx1]
  have hlap : (stratonovichHalfLaplacian u₀).coeff [] = 0 := by
    simp [stratonovichHalfLaplacian, u₀, ExtTensorAlgebra.basisWord, idx1]
  have hshuf : (shuffleFinite (rightShift idx1 u₀) (rightShift idx1 u₀) 1).coeff [] = c₁ ^ 2 := by
    unfold shuffleFinite
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have hm1 : ∑ n ∈ Finset.range 2,
        ∑ I ∈ wordsOfLength 2 1, ∑ J ∈ wordsOfLength 2 n,
          (rightShift idx1 u₀).coeff I * (rightShift idx1 u₀).coeff J *
            (ExtTensorAlgebra.shuffleBasis I J).coeff [] = 0 := by
      refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun I hI => ?_
      refine Finset.sum_eq_zero fun J _ => ?_
      have hlen : I.length = 1 := wordsOfLength.mem.mp hI
      have hzero : (rightShift idx1 u₀).coeff I = 0 := by
        have hne : I ++ [idx1] ≠ [idx1] := by
          intro heq
          have hl := congrArg List.length heq
          simp [hlen] at hl
        simp [rightShift, u₀, ExtTensorAlgebra.basisWord, hne]
      rw [hzero, zero_mul, zero_mul]
    rw [hm1, add_zero, Finset.sum_range_succ, Finset.sum_range_one]
    have hn1 : ∑ I ∈ wordsOfLength 2 0, ∑ J ∈ wordsOfLength 2 1,
        (rightShift idx1 u₀).coeff I * (rightShift idx1 u₀).coeff J *
          (ExtTensorAlgebra.shuffleBasis I J).coeff [] = 0 := by
      refine Finset.sum_eq_zero fun I _ => Finset.sum_eq_zero fun J hJ => ?_
      have hlen : J.length = 1 := wordsOfLength.mem.mp hJ
      have hzero : (rightShift idx1 u₀).coeff J = 0 := by
        have hne : J ++ [idx1] ≠ [idx1] := by
          intro heq
          have hl := congrArg List.length heq
          simp [hlen] at hl
        simp [rightShift, u₀, ExtTensorAlgebra.basisWord, hne]
      rw [hzero, mul_zero, zero_mul]
    rw [hn1, add_zero]
    simp [wordsOfLength, rightShift, u₀, ExtTensorAlgebra.basisWord,
      ExtTensorAlgebra.shuffleBasis, ExtTensorAlgebra.shuffleWords]
    ring
  change (rightShift 0 u₀).coeff [] + (stratonovichHalfLaplacian u₀).coeff [] +
    (1 / 2 : ℝ) * (∑ i : Fin 1,
      (shuffleFinite (rightShift i.succ u₀) (rightShift i.succ u₀) 1).coeff []) = _
  rw [hshift0, hlap, Fin.sum_univ_one]
  simpa [idx1] using congrArg ((1 / 2 : ℝ) * ·) hshuf

/-! ## Section 3: Existence, Uniqueness, Positivity, and Sharpness of H1 (Theorem A) -/

end SignatureVolatility

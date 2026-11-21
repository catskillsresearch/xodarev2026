import SignatureVolatility.GKWDecompositionSetup


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

theorem proposition_6_5_normal_equations {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (𝒰 : Submodule ℝ H) (ε u_star : H) (hu : u_star ∈ 𝒰)
    (horth : ∀ v ∈ 𝒰, ⟪ε - u_star, v⟫ = 0) :
    (∀ u ∈ 𝒰, ‖ε - u_star‖ ^ 2 ≤ ‖ε - u‖ ^ 2) ∧
      ‖ε - u_star‖ ^ 2 = ‖ε‖ ^ 2 - ‖u_star‖ ^ 2 := by
  refine ⟨fun u hu' => ?_, ?_⟩
  · have hdiff : u_star - u ∈ 𝒰 := 𝒰.sub_mem hu hu'
    have h0 : ⟪ε - u_star, u_star - u⟫ = 0 := horth (u_star - u) hdiff
    have hsplit : ε - u = (ε - u_star) + (u_star - u) := by abel
    rw [hsplit, @norm_add_sq_real H _ _ (ε - u_star) (u_star - u), h0]
    nlinarith [sq_nonneg ‖u_star - u‖]
  · have h0 : ⟪ε - u_star, u_star⟫ = 0 := horth u_star hu
    have hsplit : ε = (ε - u_star) + u_star := by abel
    have hpyth := @norm_add_sq_real H _ _ (ε - u_star) u_star
    rw [← hsplit, h0] at hpyth
    linarith

end SignatureVolatility

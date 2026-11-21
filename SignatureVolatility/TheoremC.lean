module

public import SignatureVolatility.Preliminaries
public import SignatureVolatility.PriceFiltrationSignatureSpace
public import SignatureVolatility.PriceFiltrationSignatureSpace.AugmentedMarketSpan
public import SignatureVolatility.PriceFiltrationSignatureSpace.CompletenessDepth
public import SignatureVolatility.PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration
public import SignatureVolatility.PriceFiltrationSignatureSpace.VInfty
public import SignatureVolatility.PriceFiltrationSignatureSpace.VSubspace


@[expose] public section

noncomputable section

open Set

namespace SignatureVolatility

theorem theorem_C {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d)
    {𝒦₁ 𝒦₂ : Set ℝ} (h𝒦₁ : Ioi (0 : ℝ) ⊆ closure 𝒦₁) (h𝒦₂ : Ioi (0 : ℝ) ⊆ closure 𝒦₂) :
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.completenessDepth ≤ (N : ℕ∞)) ∧
    (∀ M : ℕ, (M : ℕ∞) < PFS.completenessDepth → ¬ PFS.IsCompleteOnPriceFiltration 𝒦₁ M) ∧
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.IsCompleteOnPriceFiltration 𝒦₂ N) := by
  obtain ⟨hVtop₁, hbridge₁⟩ := PFS.davis_obloj_bridge 𝒦₁ h𝒦₁
  obtain ⟨_, hbridge₂⟩ := PFS.davis_obloj_bridge 𝒦₂ h𝒦₂
  have hchar : ∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.completenessDepth ≤ (N : ℕ∞) := by
    intro N
    unfold PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration
      PriceFiltrationSignatureSpace.augmentedMarketSpan
      PriceFiltrationSignatureSpace.completenessDepth
    rw [hbridge₁ N]
    constructor
    · -- Completeness ⇒ depth ≤ N: N itself belongs to the defining set of the infimum.
      intro hN
      exact csInf_le (OrderBot.bddBelow _) ⟨N, rfl, hN⟩
    · -- depth ≤ N ⇒ completeness: take a realizing level n₀ ≤ N and use monotonicity.
      intro hle
      let S_good : Set ℕ∞ :=
        {(K : ℕ∞) | ∃ n : ℕ, K = (n : ℕ∞) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}
      have hne : S_good.Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        change sInf S_good ≤ (N : ℕ∞) at hle
        rw [hempty, sInf_empty] at hle
        exact not_top_le_coe N hle
      rcases csInf_mem hne with ⟨n₀, hn₀_eq, hn₀_cl⟩
      have hn₀_le : n₀ ≤ N :=
        WithTop.coe_le_coe.mp (show (n₀ : ℕ∞) ≤ (N : ℕ∞) from hn₀_eq ▸ hle)
      -- Goal after `hbridge₁`: cl(𝒱_N) = cl(𝒱_∞). Use Davis–Obłój `hVtop₁`: cl(𝒱_∞) = ⊤.
      apply le_antisymm
      · -- cl(𝒱_N) ≤ cl(𝒱_∞) = ⊤
        change (PFS.V_subspace N).topologicalClosure ≤ PFS.V_infty
        rw [show PFS.V_infty = ⊤ from hVtop₁]
        exact le_top
      · -- cl(𝒱_∞) ≤ cl(𝒱_N): n₀ realizes depth and 𝒱_{n₀} ⊆ 𝒱_N
        change PFS.V_infty ≤ (PFS.V_subspace N).topologicalClosure
        rw [← hn₀_cl]
        exact Submodule.topologicalClosure_mono
          (PriceFiltrationSignatureSpace.V_subspace.mono PFS hn₀_le)
  refine ⟨hchar, fun M hlt hcomp => not_le_of_gt hlt ((hchar M).mp hcomp), fun N => ?_⟩
  -- Strike-set independence: both bridges reduce to the same density of 𝒱_N in 𝒱_∞.
  unfold PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration
    PriceFiltrationSignatureSpace.augmentedMarketSpan
  rw [hbridge₁ N, hbridge₂ N]

end SignatureVolatility

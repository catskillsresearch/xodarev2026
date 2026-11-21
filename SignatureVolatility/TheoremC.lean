import SignatureVolatility.PriceFiltrationSignatureSpace
import SignatureVolatility.PriceFiltrationSignatureSpace.VSubspace
import SignatureVolatility.PriceFiltrationSignatureSpace.VInfty
import SignatureVolatility.PriceFiltrationSignatureSpace.CompletenessDepth
import SignatureVolatility.PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

theorem theorem_C {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ}
    (PFS : PriceFiltrationSignatureSpace H_S d)
    {𝒦₁ 𝒦₂ : Set ℝ} (h𝒦₁ : Ioi (0 : ℝ) ⊆ closure 𝒦₁) (h𝒦₂ : Ioi (0 : ℝ) ⊆ closure 𝒦₂) :
    -- (1) Equivalence between augmented completeness at level `N` and `(N : ℕ∞) ≥ N^*_S`:
    (∀ N : ℕ,
      PFS.IsCompleteOnPriceFiltration 𝒦₁ N ↔ PFS.completenessDepth ≤ (N : ℕ∞)) ∧
    -- (2) Minimality: no level `M < N^*_S` completes the price filtration:
    (∀ M : ℕ, (M : ℕ∞) < PFS.completenessDepth → ¬ PFS.IsCompleteOnPriceFiltration 𝒦₁ M) ∧
    -- (3) Strike-set independence (Proposition 5.4):
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
    · intro hN
      exact csInf_le (OrderBot.bddBelow _) ⟨N, rfl, hN⟩
    · intro hle
      let S_good : Set ℕ∞ :=
        {(K : ℕ∞) | ∃ n : ℕ, K = (n : ℕ∞) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}
      have hne : S_good.Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        change sInf S_good ≤ (N : ℕ∞) at hle
        rw [hempty, sInf_empty] at hle
        exact not_top_le_coe N hle
      have hmem : sInf S_good ∈ S_good := Nat.WithTop.sInf_mem hne -- Wait: check `csInf_mem` on `ℕ∞`!
      -- On `ℕ∞ = WithTop ℕ`, `WellFoundedLT ℕ∞` gives `csInf_mem hne` directly!
      rcases csInf_mem hne with ⟨n₀, hn₀_eq, hn₀_cl⟩
      have hn₀_le : n₀ ≤ N := by
        exact WithTop.coe_le_coe.mp (hn₀_eq ▸ hle)
      apply le_antisymm
      · rw [PriceFiltrationSignatureSpace.V_infty, hVtop₁]
        exact le_top
      · rw [← hn₀_cl]
        exact Submodule.topologicalClosure_mono (PriceFiltrationSignatureSpace.V_subspace.mono PFS hn₀_le)
  refine ⟨hchar, fun M hlt hcomp => not_le_of_gt hlt ((hchar M).mp hcomp), fun N => ?_⟩
  unfold PriceFiltrationSignatureSpace.IsCompleteOnPriceFiltration
    PriceFiltrationSignatureSpace.augmentedMarketSpan
  rw [hbridge₁ N, hbridge₂ N]

/-! ## Section 6: Galtchouk–Kunita–Watanabe Hedging-Error Decomposition (Theorem D) -/

end SignatureVolatility

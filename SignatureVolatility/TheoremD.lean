import SignatureVolatility.GKWDecompositionSetup
import SignatureVolatility.MemTw
import SignatureVolatility.NormW
import SignatureVolatility.Preliminaries
import SignatureVolatility.PriceFiltrationSignatureSpace
import SignatureVolatility.PriceFiltrationSignatureSpace.CompletenessDepth
import SignatureVolatility.PriceFiltrationSignatureSpace.VInfty
import SignatureVolatility.PriceFiltrationSignatureSpace.VSubspace
import SignatureVolatility.ProjGt
import SignatureVolatility.ProjLe
import SignatureVolatility.TailNorm2wInvLeRatioMulNormW
import SignatureVolatility.Weight

noncomputable section

open scoped RealInnerProductSpace
open Set

namespace SignatureVolatility

/-- **Theorem D (GKW hedging-error decomposition)**: orthogonal residual of the replicable
subspace, quantitative weight-tail bound for signature payoffs, and vanishing residual once
completeness depth is attained (paper §6 / Thm.~D). -/
theorem theorem_D {H_S : Type*} [NormedAddCommGroup H_S] [InnerProductSpace ℝ H_S]
    [CompleteSpace H_S] {d : ℕ} {w : Weight}
    {PFS : PriceFiltrationSignatureSpace H_S d}
    (gkw : GKWDecompositionSetup H_S d w PFS) :
    -- (1) Unique orthogonal GKW decomposition & Pythagorean variance formula:
    (∀ X : H_S, ∃ ε_T : H_S,
      X = gkw.expectationPart X + gkw.stochasticIntegralPart X + ε_T ∧
      (∀ Z ∈ gkw.replicableSubspace, ⟪ε_T, Z⟫ = 0) ∧
      ‖X‖ ^ 2 = ‖gkw.expectationPart X + gkw.stochasticIntegralPart X‖ ^ 2 + ‖ε_T‖ ^ 2) ∧
    -- (2) Quantitative weight-ratio tail bound on `𝒲_{w'}`:
    (∀ (w' : Weight) (b : ExtTensorAlgebra (d + 1)) (_hb : MemTw w' b)
        (N : ℕ) (ρ_N : ℝ) (_hρ : 0 ≤ ρ_N),
      (∀ n : ℕ, N < n → w n / w' n ≤ ρ_N) →
      ∃ Z ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N,
        ‖gkw.evalSig b - Z‖ ≤ gkw.C_sig * ρ_N * normW w' b) ∧
    -- (3) Zero residual at or above finite completeness depth `N ≥ N^*_S` (when `𝒱^{(∞)}_S = ⊤`):
    (PFS.V_infty = ⊤ → ∀ N : ℕ, PFS.completenessDepth ≤ (N : ℕ∞) →
      ∀ X : H_S, X ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N) := by
  haveI := gkw.replicable_hasOrthProj
  refine ⟨fun X => ?_, fun w' b hb N ρ_N hρ hratio => ?_, fun hVtop N hdepth _X => ?_⟩
  · -- Hilbert projection onto closed replicable subspace (paper: existence/uniqueness via GKW).
    let P_X : H_S := replicableStarProjection gkw.replicableSubspace X
    let ε_T : H_S := X - P_X
    have hsplit : P_X = gkw.expectationPart X + gkw.stochasticIntegralPart X :=
      gkw.orthProj_split X
    have horth : ∀ Z ∈ gkw.replicableSubspace, ⟪ε_T, Z⟫ = 0 := by
      intro Z hZ
      have hmem : X - P_X ∈ gkw.replicableSubspaceᗮ :=
        Submodule.sub_starProjection_mem_orthogonal X
      exact (Submodule.mem_orthogonal' gkw.replicableSubspace (X - P_X)).mp hmem Z hZ
    have hP_mem : P_X ∈ gkw.replicableSubspace :=
      Submodule.starProjection_apply_mem gkw.replicableSubspace X
    have hpyth : ‖X‖ ^ 2 = ‖P_X‖ ^ 2 + ‖ε_T‖ ^ 2 := by
      have hdecomp : X = P_X + ε_T := by simp [ε_T]
      have h0 : ⟪P_X, ε_T⟫ = 0 := by
        rw [real_inner_comm]
        exact horth P_X hP_mem
      have hsq := @norm_add_sq_real H_S _ _ P_X ε_T
      rw [← hdecomp, h0] at hsq
      linarith
    refine ⟨ε_T, ?_, horth, ?_⟩
    · rw [← hsplit]; simp [ε_T]
    · rwa [← hsplit]
  · -- Truncate signature payoff; tail controlled by weight ratio (Def. weighted class / κ(w,N)).
    let Z : H_S := gkw.evalSig (projLe N b)
    have hZ_mem : Z ∈ gkw.replicableSubspace ⊔ PFS.V_subspace N :=
      Submodule.mem_sup_right (gkw.evalSig_le_in_V N b)
    refine ⟨Z, hZ_mem, ?_⟩
    have hdecomp : gkw.evalSig b = Z + gkw.evalSig (projGt N b) := by
      conv_lhs => rw [← projGt.add_projLe N b, gkw.evalSig_add]
    have hsub : gkw.evalSig b - Z = gkw.evalSig (projGt N b) := by
      rw [hdecomp]; abel
    rw [hsub]
    obtain ⟨hL2_tail, hnorm_tail⟩ :=
      tail_norm2wInv_le_ratio_mul_normW w w' hb N hρ hratio
    calc
      ‖gkw.evalSig (projGt N b)‖ ≤ gkw.C_sig * norm2wInv w (projGt N b) :=
        gkw.evalSig_l2_bound (projGt N b) hL2_tail
      _ ≤ gkw.C_sig * (ρ_N * normW w' b) :=
        mul_le_mul_of_nonneg_left hnorm_tail gkw.hC_sig_nonneg
      _ = gkw.C_sig * ρ_N * normW w' b := by ring
  · -- Depth dual: once N ≥ N^*_S and 𝒱_∞ = ⊤, 𝒱_N = ⊤ so every claim is replicable + static span.
    let S_good : Set ℕ∞ :=
      {(K : ℕ∞) | ∃ n : ℕ, K = (n : ℕ∞) ∧ (PFS.V_subspace n).topologicalClosure = PFS.V_infty}
    have hne : S_good.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hdepth' : sInf S_good ≤ (N : ℕ∞) := by
        simpa [PriceFiltrationSignatureSpace.completenessDepth] using hdepth
      rw [hempty, sInf_empty] at hdepth'
      exact not_top_le_coe N hdepth'
    rcases csInf_mem hne with ⟨n₀, hn₀_eq, hn₀_cl⟩
    have hn₀_le : n₀ ≤ N :=
      WithTop.coe_le_coe.mp
        (show (n₀ : ℕ∞) ≤ (N : ℕ∞) from
          hn₀_eq ▸ (by simpa [PriceFiltrationSignatureSpace.completenessDepth] using hdepth))
    have hVN_top : PFS.V_subspace N = ⊤ := by
      rw [← PriceFiltrationSignatureSpace.V_subspace.topologicalClosure_eq PFS N]
      apply top_unique
      rw [← hVtop, ← hn₀_cl]
      exact Submodule.topologicalClosure_mono
        (PriceFiltrationSignatureSpace.V_subspace.mono PFS hn₀_le)
    rw [hVN_top]
    exact Submodule.mem_sup_right Submodule.mem_top

end SignatureVolatility
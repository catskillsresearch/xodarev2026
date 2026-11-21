import SignatureVolatility.PriceFiltrationSignatureSpace
import SignatureVolatility.PriceFiltrationSignatureSpace.CompletenessDepth
import SignatureVolatility.PriceFiltrationSignatureSpace.VInfty
import SignatureVolatility.PriceFiltrationSignatureSpace.VSubspace
import SignatureVolatility.Word

noncomputable section

namespace SignatureVolatility

theorem section_7_1_black_scholes_completeness {H_S : Type*} [NormedAddCommGroup H_S]
    [InnerProductSpace ℝ H_S] [CompleteSpace H_S]
    (PFS : PriceFiltrationSignatureSpace H_S 1)
    (hVtop : PFS.V_infty = ⊤)
    (hBS_span : ∀ I : Word 2, PFS.Y I ∈ PFS.V_subspace 0) :
    PFS.completenessDepth = 0 := by
  apply le_antisymm _ zero_le
  unfold PriceFiltrationSignatureSpace.completenessDepth
  refine csInf_le (OrderBot.bddBelow _) ⟨0, rfl, ?_⟩
  apply le_antisymm
  · rw [hVtop]; exact le_top
  · unfold PriceFiltrationSignatureSpace.V_infty
    refine Submodule.topologicalClosure_mono ?_
    rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact hBS_span I

end SignatureVolatility
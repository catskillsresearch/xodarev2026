import SignatureVolatility.ProlongedBrownianSetup
import SignatureVolatility.ProlongedBrownianSetup.WHat
import SignatureVolatility.ProlongedBrownianSetup.BrownianFiltration
import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
  {d : ℕ} {T : ℝ}

theorem signature_filtration_eq_brownian_filtration
    (setup : ProlongedBrownianSetup Ω ℙ d T) (t : ℝ) :
    setup.signatureFiltration.σAlg t = setup.brownianFiltration.σAlg t := by
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun I => ?_
    exact (setup.sig_adapted_to_W t s I).comap_le
  · refine iSup_le fun s => iSup_le fun i => ?_
    have hrec : (fun ω => setup.W s.1 ω i) = (fun ω => (setup.W_hat s.1 ω).coeff [i.succ]) := by
      ext ω
      have hsp := setup.sig2_space 0 s.1 ω i
      rw [setup.W_zero ω i, sub_zero] at hsp
      exact hsp.symm
    rw [hrec]
    exact le_iSup_of_le s (le_iSup_of_le [i.succ] le_rfl)


/-! ## Section 2.3: The Weighted Tensor Algebra `T_w` and its Dual `T_w^*` -/

end SignatureVolatility

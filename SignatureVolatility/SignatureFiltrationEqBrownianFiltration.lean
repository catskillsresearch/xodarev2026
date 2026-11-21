module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.BrownianFiltration
public import SignatureVolatility.ProlongedBrownianSetup.SignatureFiltration
public import SignatureVolatility.ProlongedBrownianSetup.WHat


@[expose] public section

noncomputable section

open MeasureTheory

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
    have hZ :
        (fun u i ω => setup.W u ω i) s.1 i =
          (fun ω => (setup.W_hat s.1 ω).coeff [i.succ]) := by
      funext ω
      have hsp := setup.sig2_space 0 s.1 ω i
      rw [setup.W_zero ω i, sub_zero] at hsp
      exact hsp.symm
    rw [hZ]
    exact le_iSup_of_le s (le_iSup_of_le [i.succ] le_rfl)

end SignatureVolatility

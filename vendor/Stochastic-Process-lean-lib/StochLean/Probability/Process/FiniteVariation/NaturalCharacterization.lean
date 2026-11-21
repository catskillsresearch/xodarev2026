/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Process.FiniteVariation.NaturalTerminalBalance

/-! # The terminal integral characterization of naturality

Protter III.12 characterizes naturality by the expectation of the actual
integral of the bounded test martingale's left-limit process against the FV
process. Both sides require actual integrable full-time terminal limits;
there is no vacuous implication conditioned on a terminal being supplied.

The independently constructed integration-by-parts terminal balance proves
both directions. In the reverse direction, uniqueness of the actual path
limits identifies the characterization's terminals with those in that
balance. The remaining actual raw-bracket terminal consequently has zero
mean. No alternative integral, bracket, or terminal selector is introduced.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ}

/-- Protter III.12, using actual integrable terminal limits and the existing
stochastic integral with left-limit integrand. The FV process's initial
integrability follows from its explicit zero-initial hypothesis. -/
theorem isNatural_iff_integral_leftLimit_eq_terminal_product
    (ha : Adapted F A) (hc : HasCadlagPaths A P) (hv : HasIntegrableVariation A P)
    (h0 : A 0 =ᵐ[P] 0) (hF : F.IsUsual P) :
    IsNatural A F P hF ↔
      ∀ (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P) (hcM : HasCadlagPaths M P)
        (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, ‖M t ω‖ ≤ C),
        let hSM := hM.isSemimartingale_of_bound hF hcM C hb
        let hSA := hv.hasFiniteVariationPaths.isSemimartingale ha hF hc
        let I := hSA.stochasticIntegral hF
          (hSM.adapted.leftLimitProcess_of_usual hF hcM) hcM.hasCagladPaths_leftLimitProcess
        ∃ L B U : Ω → ℝ, Integrable L P ∧ Integrable B P ∧ Integrable U P ∧
          (∀ᵐ ω ∂P, Tendsto (M · ω) atTop (𝓝 (L ω))) ∧
          (∀ᵐ ω ∂P, Tendsto (A · ω) atTop (𝓝 (B ω))) ∧
          (∀ᵐ ω ∂P, Tendsto (I · ω) atTop (𝓝 (U ω))) ∧
          Integrable (fun ω ↦ L ω * B ω) P ∧
          (∫ ω, U ω ∂P) = ∫ ω, L ω * B ω ∂P := by
  have hiZero : Integrable (0 : Ω → ℝ) P :=
    ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩
  have hi0 : Integrable (A 0) P := hiZero.congr h0.symm
  constructor
  · intro hN M hM hcM C hC hb hSM hSA I
    obtain ⟨L, B, U, V, hiL, hiB, hiU, _hiV, hlL, hlB, hlU, hlV, hiProd, hbalance⟩ :=
      hv.exists_integrable_terminals_integrationByParts ha hc hi0 hF hM hcM C hC hb
    refine ⟨L, B, U, hiL, hiB, hiU, hlL, hlB, hlU, hiProd, ?_⟩
    have heV := (hN.integrable_terminal_and_integral_eq_zero hM hcM C hC hb hlV).2
    rw [heV, add_zero] at hbalance
    exact hbalance.symm
  · intro htests
    refine ⟨ha, hc, hv, h0, ?_⟩
    intro M hM hcM C hC hb
    obtain ⟨L, B, U, V, _hiL, _hiB, _hiU, hiV, hlL, hlB, hlU, hlV, _hiProd, hbalance⟩ :=
      hv.exists_integrable_terminals_integrationByParts ha hc hi0 hF hM hcM C hC hb
    obtain ⟨L', B', U', _hiL', _hiB', _hiU', hlL', hlB', hlU', _hiProd', hmean⟩ :=
      htests M hM hcM C hC hb
    have heL : L =ᵐ[P] L' := by
      filter_upwards [hlL, hlL'] with ω hω hω'
      exact tendsto_nhds_unique hω hω'
    have heB : B =ᵐ[P] B' := by
      filter_upwards [hlB, hlB'] with ω hω hω'
      exact tendsto_nhds_unique hω hω'
    have heU : U =ᵐ[P] U' := by
      filter_upwards [hlU, hlU'] with ω hω hω'
      exact tendsto_nhds_unique hω hω'
    have heProd : (fun ω ↦ L ω * B ω) =ᵐ[P] fun ω ↦ L' ω * B' ω := by
      filter_upwards [heL, heB] with ω hl hb'
      rw [hl, hb']
    have hUP : (∫ ω, U ω ∂P) = ∫ ω, L ω * B ω ∂P :=
      (integral_congr_ae heU).trans (hmean.trans (integral_congr_ae heProd).symm)
    refine ⟨V, hiV, hlV, ?_⟩
    linarith only [hbalance, hUP]

end ProbabilityTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicTerminalConvergence
public import StochLean.Probability.Martingale.Doob.DyadicDifferenceMaximal
public import StochLean.Probability.Process.UCP.TerminalEnergy

/-! # Uniform Cauchy convergence of the actual dyadic Doob steps

Terminal L2 Cauchy convergence is combined with the actual conditional remaining
terms and their maximal bounds. This gives UCP-Cauchy for the original ceiling
extensions, not for a substituted cadlag process. The common-event subsequence
is obtained from the existing UCP Cauchy owner.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

theorem Supermartingale.cauchyUCP_dyadicDoobStep_of_globalConditionalModulus
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    (hG2 : ∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P)
    (hGE : Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0)) :
    CauchyUCP P (dyadicDoobStep X F P) := by
  obtain ⟨Z, U, G, hiZ, _, hlZ, hU, hUE, hlU, hG, hG2, hGE, _⟩ :=
    hX.exists_dyadicDoob_terminal_energy_data_of_globalConditionalModulus hc hN hbound hG hG2 hGE
  have hC := hX.cauchySeq_toLp_dyadicDoob_terminals_of_globalConditionalModulus
    hc hbound hU hUE hlU hG hG2 hGE
  let W : ℕ → Ω → ℝ := fun n ω ↦ (G (1 / ((2 ^ n : ℕ) : ℝ≥0)) ω).toReal
  have hW (n : ℕ) : MemLp (W n) 2 P := hG2 _
  have hsmall : Tendsto (fun n ↦ ∫ ω, W n ω ^ 2 ∂P) atTop (𝓝 0) :=
    hGE.comp tendsto_dyadicDoob_width
  apply cauchyUCP_of_terminal_L2_maximal hU hW hC hsmall
  intro T a ha n m
  exact hX.measureReal_exists_compact_dyadicDoob_difference_gt_le hF n m hN
    (fun t ↦ hbound.mono fun _ hω ↦ hω t) hiZ (hU n) (hU m) hlZ
    (hlU n) (hlU m) (hG _) (hG _) T ha

theorem Supermartingale.cauchyUCP_dyadicDoobStep
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    CauchyUCP P (dyadicDoobStep X F P) := by
  obtain ⟨G, hG, _, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound
  exact hX.cauchyUCP_dyadicDoobStep_of_globalConditionalModulus hF hc hN hbound hG hG2 hGE

theorem Supermartingale.exists_dyadicDoob_uniform_cauchy_subsequence
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      UniformCauchySeqOn (fun n t ↦ dyadicDoobStep X F P (k n) t ω) atTop (Icc 0 T) :=
  (hX.cauchyUCP_dyadicDoobStep hF hc hJ hN hbound).exists_seq_ae_locallyUniform_cauchy

end MeasureTheory

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicTerminalData
public import StochLean.Probability.Convergence.TerminalEnergyCauchy

/-! # L2 convergence of the actual dyadic terminal variables

The terminal-difference energy estimate and the proved global conditional
modulus theorem give a genuine Cauchy sequence in native L2. Completeness
constructs its limit. This is convergence across meshes, not merely the
already known fixed-mesh limit as the time index tends to infinity.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ} {U : ℕ → Ω → ℝ}

theorem Supermartingale.cauchySeq_toLp_dyadicDoob_terminals_of_globalConditionalModulus
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hU : ∀ n, MemLp (U n) 2 P)
    (hUE : ∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ 8 * N ^ 2)
    (hlU : ∀ n, ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω)))
    {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    (hG2 : ∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P)
    (hGE : Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0)) :
    CauchySeq (fun n ↦ (hU n).toLp (U n)) := by
  obtain ⟨Z, hiZ, _, _, hlZ⟩ := hX.exists_bounded_actualLimit hc hbound
  let W : ℕ → Ω → ℝ := fun n ω ↦ (G (1 / ((2 ^ n : ℕ) : ℝ≥0)) ω).toReal
  have hW (n : ℕ) : MemLp (W n) 2 P := hG2 _
  have hsmall : Tendsto (fun n ↦ ∫ ω, W n ω ^ 2 ∂P) atTop (𝓝 0) :=
    hGE.comp tendsto_dyadicDoob_width
  apply cauchySeq_toLp_two_of_terminal_energy hU hW hUE hsmall
  intro n m hnm
  exact hX.integral_sq_dyadicDoob_terminal_sub_le hnm
    (fun t ↦ hbound.mono fun _ hω ↦ hω t) hiZ (hU n) (hU m) hlZ
    (hlU n) (hlU m) (hG _) (hG _) (hG2 _) (hG2 _)

theorem Supermartingale.cauchySeq_toLp_dyadicDoob_terminals
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    (hU : ∀ n, MemLp (U n) 2 P)
    (hUE : ∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ 8 * N ^ 2)
    (hlU : ∀ n, ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω))) :
    CauchySeq (fun n ↦ (hU n).toLp (U n)) := by
  obtain ⟨G, hG, _, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound
  exact hX.cauchySeq_toLp_dyadicDoob_terminals_of_globalConditionalModulus
    hc hbound hU hUE hlU hG hG2 hGE

/-- Actual fixed-mesh terminal variables admit an actual L2 limit across meshes.
The terminal variables, Cauchy property and convergence are all conclusions. -/
theorem Supermartingale.exists_dyadicDoob_terminal_L2_limit_of_globalConditionalModulus
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    (hG2 : ∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P)
    (hGE : Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0)) :
    ∃ (U : ℕ → Ω → ℝ) (A : Ω → ℝ),
      (∀ n, MemLp (U n) 2 P) ∧
      (∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ 8 * N ^ 2) ∧
      (∀ n, ∀ᵐ ω ∂P,
        Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω))) ∧
      MemLp A 2 P ∧ Tendsto (fun n ↦ eLpNorm (U n - A) 2 P) atTop (𝓝 0) := by
  obtain ⟨_, U, _, _, _, _, hU, hUE, hlU, _, _, _, _⟩ :=
    hX.exists_dyadicDoob_terminal_energy_data_of_globalConditionalModulus hc hN hbound hG hG2 hGE
  have hC := hX.cauchySeq_toLp_dyadicDoob_terminals_of_globalConditionalModulus
    hc hbound hU hUE hlU hG hG2 hGE
  obtain ⟨A, hA, hlA⟩ := (exists_memLp_tendsto_eLpNorm_iff_cauchySeq_toLp hU).mpr hC
  exact ⟨U, A, hU, hUE, hlU, hA, hlA⟩

theorem Supermartingale.exists_dyadicDoob_terminal_L2_limit
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ (U : ℕ → Ω → ℝ) (A : Ω → ℝ),
      (∀ n, MemLp (U n) 2 P) ∧
      (∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ 8 * N ^ 2) ∧
      (∀ n, ∀ᵐ ω ∂P,
        Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω))) ∧
      MemLp A 2 P ∧ Tendsto (fun n ↦ eLpNorm (U n - A) 2 P) atTop (𝓝 0) := by
  obtain ⟨G, hG, _, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound
  exact hX.exists_dyadicDoob_terminal_L2_limit_of_globalConditionalModulus
    hc hN hbound hG hG2 hGE

end MeasureTheory

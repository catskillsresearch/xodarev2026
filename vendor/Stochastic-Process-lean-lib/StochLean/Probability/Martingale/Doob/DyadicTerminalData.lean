/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicTerminalEnergy

/-! # Constructed terminal energy data for all dyadic meshes

All terminal variables are constructed from the bounded supermartingale. The
generic interface uses a genuine convergent conditional modulus; the TI source
wrapper constructs that modulus internally. The energy bound is a conclusion
about actual variables, not a certificate replacing the dyadic construction.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

theorem tendsto_dyadicDoob_width :
    Tendsto (fun n : ℕ ↦ 1 / ((2 ^ n : ℕ) : ℝ≥0)) atTop (𝓝 0) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow] using
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {N : ℝ}

/-- Actual terminal data from any genuine global modulus with vanishing second moment. -/
theorem Supermartingale.exists_dyadicDoob_terminal_energy_data_of_globalConditionalModulus
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) {G : ℝ≥0 → Ω → ℝ≥0∞}
    (hG : ∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ))
    (hG2 : ∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P)
    (hGE : Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0)) :
    ∃ (Z : Ω → ℝ) (U : ℕ → Ω → ℝ) (G : ℝ≥0 → Ω → ℝ≥0∞),
      Integrable Z P ∧ MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      (∀ n, MemLp (U n) 2 P) ∧ (∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ 8 * N ^ 2) ∧
      (∀ n, ∀ᵐ ω ∂P,
        Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω))) ∧
      (∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) ∧
      (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
      ∀ n m, n ≤ m → (∫ ω, (U n ω - U m ω) ^ 2 ∂P) ≤
        2 * ∫ ω, ((G (1 / ((2 ^ n : ℕ) : ℝ≥0)) ω).toReal +
          (G (1 / ((2 ^ m : ℕ) : ℝ≥0)) ω).toReal) * (U n ω + U m ω) ∂P := by
  obtain ⟨Z, hiZ, hZ, _, hlZ⟩ := hX.exists_bounded_actualLimit hc hbound
  have hb (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N := hbound.mono fun _ hω ↦ hω t
  have hex (n : ℕ) : ∃ U : Ω → ℝ, MemLp U 2 P ∧
      (∫ ω, U ω ^ 2 ∂P) ≤ 8 * N ^ 2 ∧
      (∀ᵐ ω ∂P, Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω))) := by
    obtain ⟨U, hU, hUE, hlU, _, _⟩ :=
      hX.exists_memLp_two_dyadicDoobIncreasing_terminal_of_bound hN
        (fun t ↦ by simpa only [Real.norm_eq_abs] using hb t) n
    exact ⟨U, hU, hUE, hlU.mono fun _ hω ↦ hω.2⟩
  choose U hU hUE hlU using hex
  refine ⟨Z, U, G, hiZ, hZ, hlZ, hU, hUE, hlU, hG, hG2, hGE, ?_⟩
  intro n m hnm
  exact hX.integral_sq_dyadicDoob_terminal_sub_le hnm hb hiZ (hU n) (hU m) hlZ
    (hlU n) (hlU m) (hG _) (hG _) (hG2 _) (hG2 _)

/-- The TI source theorem constructs the actual modulus internally. -/
theorem Supermartingale.exists_dyadicDoob_terminal_energy_data
    (hX : Supermartingale X F P) (hF : F.IsUsual P) (hc : HasCadlagPaths X P)
    (hJ : HasTotallyInaccessibleJumps F X P) (hN : 0 ≤ N)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) :
    ∃ (Z : Ω → ℝ) (U : ℕ → Ω → ℝ) (G : ℝ≥0 → Ω → ℝ≥0∞),
      Integrable Z P ∧ MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      (∀ n, MemLp (U n) 2 P) ∧ (∀ n, (∫ ω, U n ω ^ 2 ∂P) ≤ 8 * N ^ 2) ∧
      (∀ n, ∀ᵐ ω ∂P,
        Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω))) ∧
      (∀ δ, IsGlobalConditionalIncrementModulus F P X δ (G δ)) ∧
      (∀ δ, MemLp (fun ω ↦ (G δ ω).toReal) 2 P) ∧
      Tendsto (fun δ ↦ ∫ ω, (G δ ω).toReal ^ 2 ∂P) (𝓝 0) (𝓝 0) ∧
      ∀ n m, n ≤ m → (∫ ω, (U n ω - U m ω) ^ 2 ∂P) ≤
        2 * ∫ ω, ((G (1 / ((2 ^ n : ℕ) : ℝ≥0)) ω).toReal +
          (G (1 / ((2 ^ m : ℕ) : ℝ≥0)) ω).toReal) * (U n ω + U m ω) ∂P := by
  obtain ⟨G, hG, _, hG2, hGE, _⟩ :=
    hX.exists_globalConditionalModulus_L2_convergence_of_bound hF hc hJ hN hbound
  exact hX.exists_dyadicDoob_terminal_energy_data_of_globalConditionalModulus
    hc hN hbound hG hG2 hGE

end MeasureTheory

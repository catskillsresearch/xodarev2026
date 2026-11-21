/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicApproximation
public import StochLean.Probability.Martingale.Doob.PredictableDifferenceEnergy
public import StochLean.Probability.Martingale.Doob.TerminalPotential

/-! # Closing the actual dyadic Doob approximants

At a fixed mesh, the terminal variable of the increasing part is an actual
path limit. Together with the actual terminal limit of the bounded
supermartingale, it closes the native discrete martingale part. The tower
property then gives the remaining-increase identity at every real time.
The ceiling extension remains left continuous; its predecessor
measurability is essential in the real-time identity.

No convergence as the mesh tends to zero is asserted or assumed here.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z U : Ω → ℝ} {N : ℝ}

/-- Fixed-mesh L2 convergence follows from the actual terminal limit and
monotonicity of the native predictable part. -/
theorem Supermartingale.dyadicDoobIncreasing_tendsto_eLpNorm_two
    (hX : Supermartingale X F P) (n : ℕ) (hU : MemLp U 2 P)
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω))) :
    Tendsto (fun k ↦ eLpNorm (dyadicDoobIncreasing X F P n k - U) 2 P)
      atTop (𝓝 0) :=
  ((dyadicDoobIncreasing_isStronglyPredictable X F P n).memLp_two_and_tendsto_of_monotone_terminal
      (hX.dyadic_restriction n).neg.monotone_predictablePart
      (Eventually.of_forall fun ω ↦ congrFun (dyadicDoobIncreasing_zero X F P n) ω)
      hU hlU).2

/-- The native discrete martingale closes with the sum of the two actual
terminal limits. Neither its closing identity nor uniform integrability
is an input. -/
theorem Supermartingale.dyadicDoob_terminal_closing
    (hX : Supermartingale X F P) (n : ℕ)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω))) :
    let M := fun k : ℕ ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ)) +
      dyadicDoobIncreasing X F P n k
    Martingale M (dyadicDoobFiltration F n) P ∧ UniformIntegrable M 1 P ∧
      Tendsto (fun k ↦ eLpNorm (M k - (Z + U)) 1 P) atTop (𝓝 0) ∧
      ∀ k, M k =ᵐ[P] P[Z + U | dyadicDoobFiltration F n k] := by
  let S : ℕ → Ω → ℝ := fun k ↦ X ((k : ℝ≥0) / (2 ^ n : ℕ))
  let A := dyadicDoobIncreasing X F P n
  intro M
  obtain ⟨hMn, _, _, _, _, hmA, hnA, hiA, _⟩ := hX.dyadic_doob_decomposition_data n
  have hM : Martingale M (dyadicDoobFiltration F n) P := by
    convert hMn using 1
    funext k ω
    change X ((k : ℝ≥0) / (2 ^ n : ℕ)) ω + A k ω =
      -(-X ((k : ℝ≥0) / (2 ^ n : ℕ)) ω - A k ω)
    ring
  have hiU : Integrable U P := hU.integrable (by norm_num)
  have huiS : UniformIntegrable S 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr
        (integrable_const N : Integrable (fun _ : Ω ↦ N) P))).mono_norm
    · exact fun k ↦ (hX.integrable ((k : ℝ≥0) / (2 ^ n : ℕ))).aestronglyMeasurable
    · intro k
      exact (hbound ((k : ℝ≥0) / (2 ^ n : ℕ))).mono fun _ hω ↦ hω.trans (le_abs_self N)
  have huiA : UniformIntegrable A 1 P := by
    apply (uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hiU)).mono_norm
    · exact fun k ↦ (hiA k).aestronglyMeasurable
    · intro k
      filter_upwards [hmA, hnA, hlU] with ω hmω hnω hlω
      rw [Real.norm_of_nonneg (hnω k)]
      exact (hmω.ge_of_tendsto hlω k).trans (le_abs_self _)
  have huiM : UniformIntegrable M 1 P := huiS.add huiA le_rfl
  have hgrid : Tendsto (fun k : ℕ ↦ (k : ℝ≥0) / (2 ^ n : ℕ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by positivity)
  have hlM : ∀ᵐ ω ∂P, Tendsto (fun k ↦ M k ω) atTop (𝓝 ((Z + U) ω)) := by
    filter_upwards [hlZ, hlU] with ω hz hu
    exact (hz.comp hgrid).add hu
  have hL : Tendsto (fun k ↦ eLpNorm (M k - (Z + U)) 1 P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top huiM.1
      (memLp_one_iff_integrable.mpr (hZ.add hiU)) huiM.2.1 hlM
  exact ⟨hM, huiM, hL, hM.eq_condExp_of_tendsto_eLpNorm (hZ.add hiU) hL⟩

/-- The conditional remaining increase is the conditional terminal decrement
from the existing upper dyadic grid. This holds at every deterministic real
time, not only at the mesh points. -/
theorem Supermartingale.condExp_dyadicDoob_terminal_sub_step
    (hX : Supermartingale X F P) (n : ℕ)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : Integrable Z P) (hU : MemLp U 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω)))
    (t : ℝ≥0) :
    P[U - dyadicDoobStep X F P n t | F t] =ᵐ[P]
      P[X (dyadicRightGrid n t) - Z | F t] := by
  let k := Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t)
  let B := dyadicDoobStep X F P n t
  have hclose := (hX.dyadicDoob_terminal_closing n hbound hZ hU hlZ hlU).2.2.2 k
  change X ((k : ℝ≥0) / (2 ^ n : ℕ)) + dyadicDoobIncreasing X F P n k =ᵐ[P]
    P[Z + U | F ((k : ℝ≥0) / (2 ^ n : ℕ))] at hclose
  have hk : (k : ℝ≥0) / (2 ^ n : ℕ) = dyadicRightGrid n t :=
    dyadicDoobStep_grid_time n t
  rw [hk] at hclose
  change X (dyadicRightGrid n t) + B =ᵐ[P] P[Z + U | F (dyadicRightGrid n t)] at hclose
  have htq := le_dyadicRightGrid n t
  have htower : P[X (dyadicRightGrid n t) + B | F t] =ᵐ[P] P[Z + U | F t] :=
    (condExp_congr_ae hclose).trans (condExp_condExp_of_le (F.mono htq)
      (F.le (dyadicRightGrid n t)))
  have hiU : Integrable U P := hU.integrable (by norm_num)
  have hiB : Integrable B P := dyadicDoobStep_integrable X F P n t
  have heB : P[B | F t] = B := condExp_of_stronglyMeasurable (F.le t)
    (dyadicDoobStep_stronglyAdapted X F P n t) hiB
  have haddL := condExp_add (hX.integrable (dyadicRightGrid n t)) hiB (F t)
  have haddR := condExp_add hZ hiU (F t)
  have hsubL := condExp_sub hiU hiB (F t)
  have hsubR := condExp_sub (hX.integrable (dyadicRightGrid n t)) hZ (F t)
  rw [heB] at haddL hsubL
  filter_upwards [htower, haddL, haddR, hsubL, hsubR] with ω ht hl hr hsl hsr
  change P[U - B | F t] ω = P[X (dyadicRightGrid n t) - Z | F t] ω
  simp only [Pi.add_apply, Pi.sub_apply] at hl hr hsl hsr
  linarith

section ProbabilityMeasure

variable [IsProbabilityMeasure P]

/-- A bounded cadlag supermartingale supplies both actual terminal variables
and the all-real-time conditional identity for each fixed dyadic mesh. -/
theorem Supermartingale.exists_dyadicDoob_terminal_identity
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N) (n : ℕ) :
    ∃ Z U : Ω → ℝ, MemLp Z 2 P ∧ MemLp U 2 P ∧
      (∫ ω, U ω ^ 2 ∂P) ≤ 8 * N ^ 2 ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω))) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U ω))) ∧
      Tendsto (fun k ↦ eLpNorm (dyadicDoobIncreasing X F P n k - U) 2 P)
        atTop (𝓝 0) ∧
      (∀ k : ℕ, X ((k : ℝ≥0) / (2 ^ n : ℕ)) + dyadicDoobIncreasing X F P n k =ᵐ[P]
        P[Z + U | dyadicDoobFiltration F n k]) ∧
      ∀ t, P[U - dyadicDoobStep X F P n t | F t] =ᵐ[P]
        P[X (dyadicRightGrid n t) - Z | F t] := by
  obtain ⟨Z, hiZ, hZ, _, hlZ⟩ := hX.exists_bounded_actualLimit hc hbound
  have hb (t : ℝ≥0) : ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N := hbound.mono fun _ hω ↦ hω t
  obtain ⟨U, hU, hUE, hlU', _, _⟩ :=
    hX.exists_memLp_two_dyadicDoobIncreasing_terminal_of_bound hN
      (fun t ↦ by simpa only [Real.norm_eq_abs] using hb t) n
  have hlU := hlU'.mono fun _ hω ↦ hω.2
  exact ⟨Z, U, hZ, hU, hUE, hlZ, hlU,
    hX.dyadicDoobIncreasing_tendsto_eLpNorm_two n hU hlU,
    (hX.dyadicDoob_terminal_closing n hb hiZ hU hlZ hlU).2.2.2,
    hX.condExp_dyadicDoob_terminal_sub_step n hb hiZ hU hlZ hlU⟩

end ProbabilityMeasure

end MeasureTheory

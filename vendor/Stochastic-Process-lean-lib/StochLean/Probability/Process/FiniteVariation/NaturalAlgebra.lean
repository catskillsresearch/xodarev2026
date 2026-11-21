/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.FiniteVariation.Natural
public import StochLean.Probability.Process.FiniteVariation.IntegrableAlgebra
public import StochLean.Probability.Process.Semimartingale.QuadraticCovariation.Algebra

/-! # Linear algebra of natural processes

The actual raw mixed bracket is linear in its finite-variation argument.
Its existing common-event identities carry actual terminal limits through
constant multiplication and addition; integrability and zero mean then
follow from ordinary integral algebra. No bracket martingale property,
predictable compensator theorem, or new terminal selector is assumed.

The sum-variation measurability needed by IV algebra comes from the adapted
cadlag fields of naturality and the usual filtration. Version invariance
requires indistinguishability of entire paths and adaptedness of the target.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {A B : ℝ≥0 → Ω → ℝ} {hF : F.IsUsual P}

/-- Real constant multiplication transports the actual tested bracket
terminal and its zero mean, including the zero scalar. -/
theorem IsNatural.const_mul (hA : IsNatural A F P hF) (c : ℝ) :
    IsNatural (fun t ω ↦ c * A t ω) F P hF := by
  have ha : Adapted F (fun t ω ↦ c * A t ω) := fun t ↦ (hA.adapted t).const_mul c
  have hc : HasCadlagPaths (fun t ω ↦ c * A t ω) P :=
    hA.hasCadlagPaths.continuous_comp (continuous_const.mul continuous_id)
  have hv := hA.hasIntegrableVariation.const_mul c
  have h0 : (fun ω ↦ c * A 0 ω) =ᵐ[P] 0 := by
    filter_upwards [hA.zero_ae] with ω hω
    change c * A 0 ω = 0
    rw [hω, Pi.zero_apply, mul_zero]
  refine ⟨ha, hc, hv, h0, ?_⟩
  intro M hM hcM C hC hb
  obtain ⟨Z, hiZ, hlZ, heZ⟩ := hA.exists_terminal_mean_zero M hM hcM C hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  have he := hSM.quadraticCovariation_const_mul_right hA.isSemimartingale hF c
  refine ⟨fun ω ↦ c * Z ω, hiZ.const_mul c, ?_, ?_⟩
  · filter_upwards [hlZ, he] with ω hl heω
    exact (hl.const_mul c).congr' (Eventually.of_forall fun t ↦ (heω t).symm)
  · rw [integral_const_mul, heZ, mul_zero]

/-- Negation is the negative-one instance of constant multiplication. -/
theorem IsNatural.neg (hA : IsNatural A F P hF) : IsNatural (-A) F P hF := by
  have he : (fun t ω ↦ (-1 : ℝ) * A t ω) = -A := by
    funext t ω
    simp only [neg_one_mul, Pi.neg_apply]
  simpa only [he] using hA.const_mul (-1)

/-- Addition preserves naturality through the sum of actual integrable
bracket terminals. Actual variation measurability is derived, not assumed. -/
theorem IsNatural.add (hA : IsNatural A F P hF) (hB : IsNatural B F P hF) :
    IsNatural (A + B) F P hF := by
  have ha : Adapted F (A + B) := fun t ↦ (hA.adapted t).add (hB.adapted t)
  have hc := hA.hasCadlagPaths.add hB.hasCadlagPaths
  have hv := hA.hasIntegrableVariation.add hB.hasIntegrableVariation
    hA.adapted hB.adapted hF hA.hasCadlagPaths hB.hasCadlagPaths
  have h0 : (A + B) 0 =ᵐ[P] 0 := by
    filter_upwards [hA.zero_ae, hB.zero_ae] with ω ha0 hb0
    simp only [Pi.add_apply, ha0, hb0, Pi.zero_apply, add_zero]
  refine ⟨ha, hc, hv, h0, ?_⟩
  intro M hM hcM C hC hb
  obtain ⟨Z, hiZ, hlZ, heZ⟩ := hA.exists_terminal_mean_zero M hM hcM C hC hb
  obtain ⟨W, hiW, hlW, heW⟩ := hB.exists_terminal_mean_zero M hM hcM C hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  have he := hSM.quadraticCovariation_add_right hA.isSemimartingale hB.isSemimartingale hF
  refine ⟨Z + W, hiZ.add hiW, ?_, ?_⟩
  · filter_upwards [hlZ, hlW, he] with ω hz hw heω
    exact (hz.add hw).congr' (Eventually.of_forall fun t ↦ (heω t).symm)
  · change (∫ ω, Z ω + W ω ∂P) = 0
    rw [integral_add hiZ hiW, heZ, heW, add_zero]

/-- Subtraction follows from the actual addition and negation closures. -/
theorem IsNatural.sub (hA : IsNatural A F P hF) (hB : IsNatural B F P hF) :
    IsNatural (A - B) F P hF := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

/-- Naturality is invariant under indistinguishable adapted replacement.
Coordinatewise almost-sure equality is not used as a pathwise substitute. -/
theorem IsNatural.congr (hA : IsNatural A F P hF) (hAB : Indistinguishable A B P)
    (haB : Adapted F B) : IsNatural B F P hF := by
  have hcB := HasCadlagPaths.congr hAB hA.hasCadlagPaths
  have hvB := hA.hasIntegrableVariation.congr hAB
  have h0B : B 0 =ᵐ[P] 0 := by
    filter_upwards [hAB, hA.zero_ae] with ω he hz
    exact (he 0).symm.trans hz
  refine ⟨haB, hcB, hvB, h0B, ?_⟩
  intro M hM hcM C hC hb
  obtain ⟨Z, hiZ, hlZ, heZ⟩ := hA.exists_terminal_mean_zero M hM hcM C hC hb
  let hSM := hM.isSemimartingale_of_bound hF hcM C hb
  let hSB := hvB.hasFiniteVariationPaths.isSemimartingale haB hF hcB
  have he := hSM.quadraticCovariation_congr hA.isSemimartingale hSM hSB hF
    (ae_of_all _ fun _ _ ↦ rfl) hAB
  refine ⟨Z, hiZ, ?_, heZ⟩
  filter_upwards [hlZ, he] with ω hl heω
  exact hl.congr' (Eventually.of_forall fun t ↦ heω t)

end ProbabilityTheory

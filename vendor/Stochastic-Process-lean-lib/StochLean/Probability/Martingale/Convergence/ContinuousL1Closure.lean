/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Convergence.ContinuousClosure

/-! # The actual integer-time terminal variable of a UI martingale

Discrete martingale convergence and uniform integrability give an actual
integrable limit with L1 convergence. The tower property closes every real-time
coordinate. No whole-half-line pathwise limit is inferred in this module.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

theorem exists_integrable_integer_limit_closing
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ X (n : ℝ≥0) ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun n : ℕ ↦ eLpNorm (X (n : ℝ≥0) - Z) 1 P) atTop (𝓝 0) ∧
      (∀ t, X t =ᵐ[P] P[Z | F t]) := by
  let e : ℕ → ℝ≥0 := Nat.cast
  have he : Monotone e := fun _ _ h ↦ Nat.cast_le.mpr h
  let G := F.reindex e he
  have hm : Martingale (fun n ↦ X (e n)) G P := hX.reindex e he
  let Z := G.limitProcess (fun n ↦ X (e n)) P
  have hui := hu.reindex e
  obtain ⟨C, hC⟩ := hui.2.2
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X (e n) ω) atTop (𝓝 (Z ω)) :=
    hm.submartingale.ae_tendsto_limitProcess hC
  have hZ : MemLp Z 1 P := hui.memLp_of_ae_tendsto hlim
  refine ⟨Z, hZ.integrable le_rfl, hlim, ?_, ?_⟩
  · exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      (fun n ↦ ((hX.stronglyAdapted (e n)).mono (F.le (e n))).aestronglyMeasurable)
      hZ hui.2.1 hlim
  · intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hmZ : X (e n) =ᵐ[P] P[Z | F (e n)] := hm.ae_eq_condExp_limitProcess hui n
    exact (hX.condExp_ae_eq hn).symm.trans ((condExp_congr_ae hmZ).trans
      (condExp_condExp_of_le (F.mono hn) (F.le (e n))))

end MeasureTheory.Martingale

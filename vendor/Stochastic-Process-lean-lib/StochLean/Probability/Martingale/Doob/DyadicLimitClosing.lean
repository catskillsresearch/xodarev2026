/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Doob.DyadicTerminalIdentity
public import StochLean.Probability.Martingale.Convergence.ContinuousClosure
public import StochLean.Probability.Process.UCP
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Closing the UCP limit of the dyadic predictable parts

The actual terminal identities and L2 convergence of the mesh terminal
variables identify each fixed-time limit. UCP uniqueness then closes the
continuous-time process with the sum of the actual terminal variables.
Integrability of the limiting predictable part is a conclusion, not an
assumption. The original left-continuous ceiling approximants are never
asserted to be continuous-time martingales.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X A : ℝ≥0 → Ω → ℝ} {Z V : Ω → ℝ}
  {U : ℕ → Ω → ℝ} {N : ℝ}

/-- Bounded right-continuous paths make upper dyadic sampling converge in L2.
Only a common almost-sure path event is used. -/
theorem Supermartingale.dyadicRightGrid_tendsto_eLpNorm_two
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N) (t : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm (X (dyadicRightGrid n t) - X t) 2 P)
      atTop (𝓝 0) := by
  have hui : UniformIntegrable (fun n ↦ X (dyadicRightGrid n t)) 2 P := by
    apply (uniformIntegrable_const (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num) (memLp_const N : MemLp (fun _ : Ω ↦ N) 2 P)).mono_norm
    · exact fun n ↦ (hX.integrable (dyadicRightGrid n t)).aestronglyMeasurable
    · intro n
      exact (hbound (dyadicRightGrid n t)).mono fun _ hω ↦ hω.trans (le_abs_self N)
  have hgrid : Tendsto (fun n ↦ dyadicRightGrid n t) atTop (𝓝[≥] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_dyadicRightGrid t,
      Eventually.of_forall fun n ↦ le_dyadicRightGrid n t⟩
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ X (dyadicRightGrid n t) ω) atTop (𝓝 (X t ω)) := by
    filter_upwards [hc] with ω hω
    exact ((hω.1 t).tendsto.comp hgrid)
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hui.1
    (MemLp.of_bound (hX.integrable t).aestronglyMeasurable N (hbound t)) hui.2.1 hlim

/-- The actual terminal identities identify the L2 limit of each coordinate
of the ceiling approximants. No integrability of a prospective UCP limit
is needed in this step. -/
theorem Supermartingale.dyadicDoobStep_tendsto_eLpNorm_two_of_terminal_tendsto
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : MemLp Z 2 P) (hU : ∀ n, MemLp (U n) 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ n, ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω)))
    (hUV : Tendsto (fun n ↦ eLpNorm (U n - V) 2 P) atTop (𝓝 0)) (t : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (dyadicDoobStep X F P n t - (P[Z + V | F t] - X t)) 2 P) atTop (𝓝 0) := by
  have hiZ := hZ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hiV := hV.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hiU (n : ℕ) := (hU n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heXt : P[X t | F t] = X t := condExp_of_stronglyMeasurable (F.le t)
    (hX.stronglyAdapted t) (hX.integrable t)
  have herr (n : ℕ) :
      dyadicDoobStep X F P n t - (P[Z + V | F t] - X t) =ᵐ[P]
        P[(U n - V) - (X (dyadicRightGrid n t) - X t) | F t] := by
    let B := dyadicDoobStep X F P n t
    have hiB : Integrable B P := dyadicDoobStep_integrable X F P n t
    have heB : P[B | F t] = B := condExp_of_stronglyMeasurable (F.le t)
      (dyadicDoobStep_stronglyAdapted X F P n t) hiB
    have hid := hX.condExp_dyadicDoob_terminal_sub_step n hbound hiZ (hU n) hlZ
      (hlU n) t
    have hUB := condExp_sub (hiU n) hiB (F t)
    have hXZ := condExp_sub (hX.integrable (dyadicRightGrid n t)) hiZ (F t)
    have hUV' := condExp_sub (hiU n) hiV (F t)
    have hXX := condExp_sub (hX.integrable (dyadicRightGrid n t))
      (hX.integrable t) (F t)
    have hE := condExp_sub ((hiU n).sub hiV)
      ((hX.integrable (dyadicRightGrid n t)).sub (hX.integrable t)) (F t)
    have hZV := condExp_add hiZ hiV (F t)
    rw [heB] at hUB
    rw [heXt] at hXX
    filter_upwards [hid, hUB, hXZ, hUV', hXX, hE, hZV] with ω hid hUB hXZ hUV hXX hE hZV
    change B ω - (P[Z + V | F t] ω - X t ω) =
      P[(U n - V) - (X (dyadicRightGrid n t) - X t) | F t] ω
    change P[U n - B | F t] ω = P[X (dyadicRightGrid n t) - Z | F t] ω at hid
    simp only [Pi.sub_apply, Pi.add_apply] at hUB hXZ hUV hXX hE hZV
    linarith
  have hlim := hUV.add (hX.dyadicRightGrid_tendsto_eLpNorm_two hc hbound t)
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) fun n ↦ ?_
  rw [eLpNorm_congr_ae (herr n)]
  exact (eLpNorm_condExp_le_eLpNorm _ (by norm_num)).trans
    (eLpNorm_sub_le ((hU n).sub hV).aestronglyMeasurable
      ((hX.integrable (dyadicRightGrid n t)).sub (hX.integrable t)).aestronglyMeasurable
      (by norm_num))

/-- UCP uniqueness identifies each coordinate with the actual conditional
terminal value. Adaptedness or integrability of the limit is not assumed. -/
theorem Supermartingale.dyadic_ucpLimit_closing
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : MemLp Z 2 P) (hU : ∀ n, MemLp (U n) 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ n, ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω)))
    (hUV : Tendsto (fun n ↦ eLpNorm (U n - V) 2 P) atTop (𝓝 0))
    (hucp : TendstoUCP P (dyadicDoobStep X F P) atTop A) :
    ∀ t, X t + A t =ᵐ[P] P[Z + V | F t] := by
  intro t
  have hX2 : MemLp (X t) 2 P :=
    MemLp.of_bound (hX.integrable t).aestronglyMeasurable N (hbound t)
  have hC2 : MemLp (P[Z + V | F t] - X t) 2 P :=
    ((hZ.add hV).condExp (by norm_num)).sub hX2
  have hm : TendstoInMeasure P (fun n ↦ dyadicDoobStep X F P n t) atTop
      (P[Z + V | F t] - X t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun n ↦ (dyadicDoobStep_integrable X F P n t).aestronglyMeasurable)
      hC2.aestronglyMeasurable
      (hX.dyadicDoobStep_tendsto_eLpNorm_two_of_terminal_tendsto hc hbound hZ hU hV
        hlZ hlU hUV t)
  have he := tendstoInMeasure_ae_unique (hucp.fixedTime t) hm
  filter_upwards [he] with ω hω
  simp only [Pi.add_apply, Pi.sub_apply] at hω ⊢
  linarith

/-- An adapted UCP limit gives a genuine closed, uniformly integrable
continuous-time martingale. Both the limiting increasing part and its
martingale sum have L2 coordinates, as consequences of the closing identity. -/
theorem Supermartingale.dyadic_ucpLimit_martingale_closing
    (hX : Supermartingale X F P) (hc : HasCadlagPaths X P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N)
    (hZ : MemLp Z 2 P) (hU : ∀ n, MemLp (U n) 2 P) (hV : MemLp V 2 P)
    (hlZ : ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ X t ω) atTop (𝓝 (Z ω)))
    (hlU : ∀ n, ∀ᵐ ω ∂P,
      Tendsto (fun k ↦ dyadicDoobIncreasing X F P n k ω) atTop (𝓝 (U n ω)))
    (hUV : Tendsto (fun n ↦ eLpNorm (U n - V) 2 P) atTop (𝓝 0))
    (hA : Adapted F A) (hucp : TendstoUCP P (dyadicDoobStep X F P) atTop A) :
    (∀ t, X t + A t =ᵐ[P] P[Z + V | F t]) ∧ Martingale (X + A) F P ∧
      UniformIntegrable (X + A) 1 P ∧
      ∀ t, MemLp (A t) 2 P ∧ MemLp (X t + A t) 2 P := by
  have hclose := hX.dyadic_ucpLimit_closing hc hbound hZ hU hV hlZ hlU hUV hucp
  refine ⟨hclose, (martingale_condExp (Z + V) F P).congr
    (hX.stronglyAdapted.add hA.stronglyAdapted) (fun t ↦ (hclose t).symm),
    Martingale.uniformIntegrable_of_integrable_closing
      ((hZ.add hV).integrable (by norm_num)) hclose, fun t ↦ ?_⟩
  have hM2 : MemLp (X t + A t) 2 P :=
    ((hZ.add hV).condExp (by norm_num)).ae_eq (hclose t).symm
  have hX2 : MemLp (X t) 2 P :=
    MemLp.of_bound (hX.integrable t).aestronglyMeasurable N (hbound t)
  have hA2 := hM2.sub hX2
  have he : X t + A t - X t = A t := by abel
  rw [he] at hA2
  exact ⟨hA2, hM2⟩

end MeasureTheory

/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.ClassicalRiccatiSolution
public import SignatureVolatility.ItoCalculusKit.SigmaContinuity

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# The Riccati exponent process `Y_t = ⟨ψ(T − t), Ŵ_t⟩` (Theorem 44 duality, milestone 1)

Take a classical Riccati solution `ψ` (coefficientwise integral equation, uniformly bounded
`T_w` norm). This file proves that the exponent of the candidate affine transform,
`Y_t = ⟨ψ(T − t), Ŵ_t⟩ = ∑_n ⟨ψ(T − t)^{(n)}, Ŵ_t^{(n)}⟩`, is well defined and continuous:

* every coefficient `t ↦ ψ_I(t)` is continuous on `[0, T]` (`continuousOn_coeff`);
* almost surely the level series converges absolutely, uniformly in `t ∈ [0, T]`, and `Y` is
  continuous on `[0, T]` (`ae_riccatiExponent_summable_continuousOn`).

The uniform majorant is `ae_levelNorm_bound_paperSig2`, the Kolmogorov grid-supremum bound on the
signature levels. Only the bound `‖ψ(s)^{(n)}‖ ≤ ‖ψ(s)‖_w ≤ C` on the coefficients is used, so the
false Lemmas 77–78 play no role.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace ClassicalRiccatiSolution

variable {w : Weight} {T : ℝ} {R : ExtTensorAlgebra (d + 1) → ExtTensorAlgebra (d + 1)}
  {u₀ : ExtTensorAlgebra (d + 1)}

/-- Each Riccati coefficient is continuous on `[0, T]`. -/
lemma continuousOn_coeff (sol : ClassicalRiccatiSolution w T R u₀) (hT : 0 ≤ T)
    (I : Word (d + 1)) : ContinuousOn (fun t => (sol.ψ t).coeff I) (Icc 0 T) := by
  have hc := (sol.integral_eq 0 ⟨le_rfl, hT⟩ I).1
  have hint : IntegrableOn (fun s => (R (sol.ψ s)).coeff I) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact hc.integrableOn_compact isCompact_Icc
  have hprim := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le hT] at hprim
  exact (continuousOn_const.add hprim).congr fun t ht => (sol.integral_eq t ht I).2

/-- The level norms of `ψ(s)` are bounded by its `T_w` norm. -/
lemma levelNorm_le_normW (sol : ClassicalRiccatiSolution w T R u₀) {s : ℝ} (hs : s ∈ Icc 0 T)
    (n : ℕ) : (sol.ψ s).levelNorm n ≤ normW w (sol.ψ s) := by
  have h := (sol.mem_Tw s hs).le_tsum n fun j _ =>
    mul_nonneg (w.pos j).le (ExtTensorAlgebra.levelNorm.nonneg _ j)
  have h1 := w.one_le n
  have h0 := ExtTensorAlgebra.levelNorm.nonneg (sol.ψ s) n
  calc (sol.ψ s).levelNorm n ≤ w n * (sol.ψ s).levelNorm n := by nlinarith
    _ ≤ _ := h

/-- The Riccati exponent process `Y_t = ⟨ψ(T − t), Ŵ_t⟩`. -/
def exponent (sol : ClassicalRiccatiSolution w T R u₀) (B : MultiBrownian Ω P d) (t : ℝ)
    (ω : Ω) : ℝ :=
  dualPairing (sol.ψ (T - t)) (paperSig2 B 0 t ω)

/-- **Milestone 1.** Almost surely the level series of `Y_t = ⟨ψ(T − t), Ŵ_t⟩` converges
absolutely for every `t ∈ [0, T]`, with a summable majorant that does not depend on `t`, and
`t ↦ Y_t` is continuous on `[0, T]`. -/
theorem ae_exponent_summable_continuousOn (sol : ClassicalRiccatiSolution w T R u₀)
    (B : MultiBrownian Ω P d) (hT : 0 < T) :
    ∀ᵐ ω ∂P, (∃ K : ℕ → ℝ, Summable K ∧ ∀ t ∈ Icc 0 T, ∀ n,
        |(sol.ψ (T - t)).levelInner (paperSig2 B 0 t ω) n| ≤ K n) ∧
      ContinuousOn (fun t => sol.exponent B t ω) (Icc 0 T) := by
  obtain ⟨C, hC0, hC⟩ := sol.uniform_bdd
  filter_upwards [ae_levelNorm_bound_paperSig2 B hT Weight.constOne HypH2.constOne_admissible,
    ae_continuousOn_paperSig2_coeff B hT.le] with ω hM hcont
  obtain ⟨M, hX, hsum⟩ := hM
  have hsumM : Summable M := hsum.congr fun n => one_mul (M n)
  have hmaps : MapsTo (fun t => T - t) (Icc 0 T) (Icc 0 T) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hbound : ∀ t ∈ Icc 0 T, ∀ n,
      |(sol.ψ (T - t)).levelInner (paperSig2 B 0 t ω) n| ≤ C * M n := by
    intro t ht n
    calc |(sol.ψ (T - t)).levelInner (paperSig2 B 0 t ω) n|
        ≤ (sol.ψ (T - t)).levelNorm n * (paperSig2 B 0 t ω).levelNorm n :=
          ExtTensorAlgebra.levelInner.abs_le _ _ n
      _ ≤ C * M n :=
          mul_le_mul ((sol.levelNorm_le_normW (hmaps ht) n).trans (hC _ (hmaps ht)))
            (hX t ht n) (ExtTensorAlgebra.levelNorm.nonneg _ n) hC0
  refine ⟨⟨fun n => C * M n, hsumM.mul_left C, hbound⟩, ?_⟩
  have hterm : ∀ n, ContinuousOn
      (fun t => (sol.ψ (T - t)).levelInner (paperSig2 B 0 t ω) n) (Icc 0 T) := fun n =>
    continuousOn_finsetSum _ fun I _ =>
      ((sol.continuousOn_coeff hT.le I).comp (continuousOn_const.sub continuousOn_id) hmaps).mul
        (hcont I)
  exact continuousOn_tsum hterm (hsumM.mul_left C) fun n t ht => by
    rw [Real.norm_eq_abs]; exact hbound t ht n

end ClassicalRiccatiSolution

end SignatureVolatility

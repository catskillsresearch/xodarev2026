/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! # Locality of conditional expectation on measurable events

Integrable inputs that agree on an event in the conditioning sigma-field
have conditional expectations agreeing on that event. Integrability is kept
explicit because the native nonintegrable conditional expectation is totalized.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f g : Ω → E} {A : Set Ω}

theorem condExp_congr_ae_restrict (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)]
    (hA : MeasurableSet[m] A) (hf : Integrable f P) (hg : Integrable g P)
    (he : f =ᵐ[P.restrict A] g) : P[f | m] =ᵐ[P.restrict A] P[g | m] := by
  have hce : (P.restrict A)[f | m] =ᵐ[P.restrict A] (P.restrict A)[g | m] :=
    condExp_congr_ae he
  exact (condExp_restrict_ae_eq_restrict hm hA hf).symm.trans
    (hce.trans (condExp_restrict_ae_eq_restrict hm hA hg))

end MeasureTheory

module

public import Mathlib

@[expose] public section

open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

/-- **NFLVR** for the given admissible terminal gains: if admissible gains `G_n` with uniformly
vanishing negative parts, integrable with `𝔼 G_n ≤ 0`, converge a.s. to an integrable `f ≥ 0`,
then `f = 0` a.s. -/
def SatisfiesNFLVR {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω)
    (AdmissibleTerminalGains : Set (Ω → ℝ)) : Prop :=
  ∀ (G : ℕ → Ω → ℝ) (f : Ω → ℝ),
    (∀ n, G n ∈ AdmissibleTerminalGains) →
    Integrable f ℙ →
    (∀ ω, 0 ≤ f ω) →
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ ω, -ε ≤ G n ω) →
    (∀ n, Integrable (G n) ℙ ∧ ∫ ω, G n ω ∂ℙ ≤ 0) →
    (∀ᵐ ω ∂ℙ, Tendsto (fun n => G n ω) atTop (𝓝 (f ω))) →
    f =ᵐ[ℙ] 0

end SignatureVolatility

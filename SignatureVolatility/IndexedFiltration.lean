module

public import Mathlib


@[expose] public section

namespace SignatureVolatility

/-- A real-indexed filtration: σ-algebras `σAlg t`, increasing in `t`, below the ambient one. -/
structure IndexedFiltration (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  σAlg : ℝ → MeasurableSpace Ω
  mono : ∀ ⦃s t : ℝ⦄, s ≤ t → σAlg s ≤ σAlg t
  le_ambient : ∀ t : ℝ, σAlg t ≤ m₀

end SignatureVolatility

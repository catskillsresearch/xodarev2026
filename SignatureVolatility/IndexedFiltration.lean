import Mathlib

namespace SignatureVolatility

structure IndexedFiltration (Ω : Type*) [m₀ : MeasurableSpace Ω] where
  σAlg : ℝ → MeasurableSpace Ω
  mono : ∀ ⦃s t : ℝ⦄, s ≤ t → σAlg s ≤ σAlg t
  le_ambient : ∀ t : ℝ, σAlg t ≤ m₀

end SignatureVolatility

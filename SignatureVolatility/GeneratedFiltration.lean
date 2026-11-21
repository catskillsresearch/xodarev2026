import SignatureVolatility.IndexedFiltration


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

def generatedFiltration {Ω ι : Type*} [m₀ : MeasurableSpace Ω]
    (Z : ℝ → ι → Ω → ℝ) (hmeas : ∀ t i, Measurable (Z t i)) : IndexedFiltration Ω where
  σAlg t := ⨆ (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (i : ι),
    MeasurableSpace.comap (Z s.1 i) inferInstance
  mono s t hst := iSup_le fun u => le_iSup_of_le ⟨u.1, u.2.1, u.2.2.trans hst⟩ le_rfl
  le_ambient t := iSup_le fun u => iSup_le fun i => (hmeas u.1 i).comap_le

end SignatureVolatility

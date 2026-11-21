import SignatureVolatility.Letter


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

abbrev Word (d : ℕ) := List (Letter d)

end SignatureVolatility

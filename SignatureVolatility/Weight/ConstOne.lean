import SignatureVolatility.Weight


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace Weight

def constOne : Weight where
  toFun _ := 1
  w_zero := rfl
  pos _ := zero_lt_one
  mono _ _ _ := le_rfl

end Weight

end SignatureVolatility

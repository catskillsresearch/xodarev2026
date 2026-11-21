import SignatureVolatility.Weight


open scoped BigOperators Classical ENNReal NNReal RealInnerProductSpace
open MeasureTheory Filter Topology Set

noncomputable section

namespace SignatureVolatility

namespace Weight

def geometric (r : ℝ) (hr : 1 ≤ r) : Weight where
  toFun n := r ^ n
  w_zero := pow_zero r
  pos n := pow_pos (zero_lt_one.trans_le hr) n
  mono m n hmn := pow_le_pow_right₀ hr hmn

end Weight

end SignatureVolatility

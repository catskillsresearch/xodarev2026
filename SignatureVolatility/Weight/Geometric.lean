module

public import SignatureVolatility.Weight


@[expose] public section

namespace SignatureVolatility

namespace Weight

/-- The geometric weight `w_n = rⁿ` for `r ≥ 1`. -/
def geometric (r : ℝ) (hr : 1 ≤ r) : Weight where
  toFun n := r ^ n
  w_zero := pow_zero r
  pos n := pow_pos (zero_lt_one.trans_le hr) n
  mono _ _ hmn := pow_le_pow_right₀ hr hmn

end Weight

end SignatureVolatility

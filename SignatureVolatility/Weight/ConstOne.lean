module

public import SignatureVolatility.Weight


@[expose] public section

namespace SignatureVolatility

namespace Weight

/-- The constant weight `w_n = 1`. -/
def constOne : Weight where
  toFun _ := 1
  w_zero := rfl
  pos _ := zero_lt_one
  mono _ _ _ := le_rfl

end Weight

end SignatureVolatility

import SignatureVolatility.Weight

namespace SignatureVolatility

namespace Weight

def constOne : Weight where
  toFun _ := 1
  w_zero := rfl
  pos _ := zero_lt_one
  mono _ _ _ := le_rfl

end Weight

end SignatureVolatility

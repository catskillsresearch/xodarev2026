module

public import SignatureVolatility.Letter
public import SignatureVolatility.Word


@[expose] public section

noncomputable section

namespace SignatureVolatility

def smoothIteratedIntegral {d : ℕ} (X' : ℝ → Fin d → ℝ) (s : ℝ) : Word d → ℝ → ℝ
  | [], _ => 1
  | i :: I, t => ∫ u in s..t, X' u i * smoothIteratedIntegral X' u I t

end SignatureVolatility

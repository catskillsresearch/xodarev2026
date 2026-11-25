module

public import SignatureVolatility.Letter


@[expose] public section

namespace SignatureVolatility

/-- Words (finite lists of letters) over the alphabet `Fin d`. -/
abbrev Word (d : ℕ) := List (Letter d)

end SignatureVolatility

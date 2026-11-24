module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratAdapted

@[expose] public section

noncomputable section

open MeasureTheory

namespace SignatureVolatility

/-!
# The paper's Stratonovich signature `Ŵ_{s,t}` of `X = (t, W_t)`

`itoWordIntegral (j :: I)` integrates the *first* letter outermost (latest in time), whereas
the tensor-algebra conventions used by the paper (`concat`, `rightShift`, `riccatiOp`,
`dŴ = Ŵ ⊗ ∘dX`) make the *last* letter the latest.  `paperSig2` therefore reads the
Stratonovich word integral of the reversed word:
`⟨e_{i₁⋯iₙ}, Ŵ_{s,t}⟩ = ∫_{s<u₁<⋯<uₙ<t} ∘dX^{i₁}_{u₁} ⋯ ∘dX^{iₙ}_{uₙ}`.

Chen and shuffle (`paperSig2_chen`, `paperSig2_shuffle`) are to be obtained from the
piecewise-linear (Wong–Zakai) approximants `sig2StratDyadic` of `Sig2StratDyadic`, which satisfy
both identities exactly, by passing to the limit in probability.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Paper Stratonovich signature of the time-extended Brownian path (iterated integrals). -/
def paperSig2 (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) : ExtTensorAlgebra (d + 1) :=
  ⟨fun I => stratWordIntegral B s t ω I.reverse⟩

lemma paperSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (I : Word (d + 1)) :
    (paperSig2 B s t ω).coeff I = stratWordIntegral B s t ω I.reverse := rfl

lemma paperSig2_empty (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [] = 1 :=
  stratWordIntegral_empty B s t ω

lemma paperSig2_time (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) :
    (paperSig2 B s t ω).coeff [0] = t - s :=
  stratWordIntegral_time B s t ω

lemma paperSig2_space (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i : Fin d) :
    (paperSig2 B s t ω).coeff [i.succ] = MultiBrownian.W B t ω i - MultiBrownian.W B s ω i :=
  stratWordIntegral_space B s t ω i

lemma measurable_paperSig2_coeff (B : MultiBrownian Ω P d) (s t : ℝ) (I : Word (d + 1)) :
    Measurable (fun ω => (paperSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral B s t I.reverse

lemma measurable_paperSig2_coeff_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => (paperSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral_pathFiltration B hs hst htT I.reverse

/-- Level 2, two different letters: the paper order puts the first letter earliest. -/
lemma paperSig2_pair (B : MultiBrownian Ω P d) (s t : ℝ) (ω : Ω) (i j : Fin (d + 1)) :
    (paperSig2 B s t ω).coeff [i, j] = stratWordIntegral B s t ω [j, i] := rfl

/-! ## Paper properties of `paperSig2` (holes, step 3 of the true-signature refactor) -/

/-- **Chen's identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_chen (B : MultiBrownian Ω P d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, paperSig2 B 0 t ω = paperSig2 B 0 s ω ⊗ₜ paperSig2 B s t ω := by
  sorry

/-- **Shuffle identity** for the Brownian Stratonovich signature (almost surely). -/
theorem paperSig2_shuffle (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (I J : Word (d + 1)) :
    ∀ᵐ ω ∂P, (paperSig2 B 0 t ω).coeff I * (paperSig2 B 0 t ω).coeff J =
      ExtTensorAlgebra.evalShuffleBasis I J (paperSig2 B 0 t ω) := by
  sorry

/-- **Paper Proposition 12 / Appendix A**: factorial level control of the Brownian signature
against weights of at most geometric growth. -/
theorem paperSig2_factorial_moment_control (B : MultiBrownian Ω P d) (p : ℝ) (hp : 1 ≤ p)
    (w_fn : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w_fn n) (hgeom : ∃ r : ℝ, ∀ n, w_fn n ≤ r ^ n)
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ᵐ ω ∂P, Summable (fun n : ℕ => w_fn n * (paperSig2 B 0 t ω).levelNorm n)) ∧
      Integrable (fun ω => (∑' n : ℕ, w_fn n * (paperSig2 B 0 t ω).levelNorm n) ^ p) P := by
  sorry

/-- **Signature dynamics** `dŴ = Ŵ ⊗ ∘dX` for the Brownian Stratonovich signature. -/
theorem paperSig2_dynamics (B : MultiBrownian Ω P d) (I : Word (d + 1)) (j : Fin (d + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    TendstoInMeasure P
      (fun n => trapezoidSum (MultiBrownian.W B) (fun s ω => (paperSig2 B 0 s ω).coeff I) j t n)
      Filter.atTop (fun ω => (paperSig2 B 0 t ω).coeff (I ++ [j])) := by
  sorry

end SignatureVolatility

module

public import SignatureVolatility.ProlongedBrownianSetup
public import SignatureVolatility.ItoCalculusKit.LevelBounds

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
Each Itô level `≥ 2` is its adapted continuous version (`contVersion`), so `Ŵ` is the
continuous signature process of the paper (up to the almost-sure continuity proved later).

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

/-! ## Regularity of the coordinates from the level-wise Itô bounds -/

/-- Almost surely, every Itô word coordinate is continuous on `[0, T]`. -/
lemma ae_continuousOn_itoWordIntegral (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ J : Word (d + 1),
      ContinuousOn (fun t => itoWordIntegral B 0 t ω J) (Set.Icc 0 T) := by
  rw [ae_all_iff]
  intro J
  by_cases hJ : J = []
  · subst hJ
    exact Filter.Eventually.of_forall fun ω => by
      simpa [itoWordIntegral_empty] using continuousOn_const
  · exact (levelBound_itoWordIntegral B hT J hJ).cont

/-- Every Itô word coordinate is in every even `L^{2q}`, `q ≥ 2`. -/
lemma memLp_itoWordIntegral (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t) (J : Word (d + 1))
    {q : ℕ} (hq : 2 ≤ q) : MemLp (fun ω => itoWordIntegral B 0 t ω J) (2 * q : ℕ) P := by
  by_cases hJ : J = []
  · subst hJ; simpa [itoWordIntegral_empty] using memLp_const (1 : ℝ)
  · exact (levelBound_itoWordIntegral B ht J hJ).memLp q hq t ht le_rfl

lemma continuousOn_stratItoCorrection (B : MultiBrownian Ω P d) {T : ℝ} {ω : Ω}
    (hω : ∀ J : Word (d + 1), ContinuousOn (fun t => itoWordIntegral B 0 t ω J) (Set.Icc 0 T))
    (K : Word (d + 1)) :
    ContinuousOn (fun t => stratItoCorrection B 0 t ω K) (Set.Icc 0 T) := by
  match K with
  | [] => exact continuousOn_const
  | [_] => exact continuousOn_const
  | _ :: _ :: _ =>
    exact continuousOn_finsetSum _ fun n _ => continuousOn_finsetSum _ fun J _ =>
      continuousOn_const.mul (hω J)

lemma memLp_stratItoCorrection (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    (K : Word (d + 1)) {q : ℕ} (hq : 2 ≤ q) :
    MemLp (fun ω => stratItoCorrection B 0 t ω K) (2 * q : ℕ) P := by
  match K with
  | [] => exact memLp_const 0
  | [_] => exact memLp_const 0
  | _ :: _ :: _ =>
    simp only [stratItoCorrection]
    exact memLp_finsetSum _ fun n _ => memLp_finsetSum _ fun J _ =>
      (memLp_itoWordIntegral B ht J hq).const_mul _

/-- Almost surely, every coordinate of `Ŵ_{0,·}` is continuous on `[0, T]`. -/
theorem ae_continuousOn_paperSig2_coeff (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ I : Word (d + 1),
      ContinuousOn (fun t => (paperSig2 B 0 t ω).coeff I) (Set.Icc 0 T) := by
  filter_upwards [ae_continuousOn_itoWordIntegral B hT] with ω hω I
  simp only [paperSig2_coeff, stratWordIntegral]
  exact (hω _).add (continuousOn_stratItoCorrection B hω _)

/-- Every coordinate of `Ŵ_{0,t}` has finite moments of every even order `2q ≥ 4`. -/
theorem memLp_paperSig2_coeff (B : MultiBrownian Ω P d) {t : ℝ} (ht : 0 ≤ t)
    (I : Word (d + 1)) {q : ℕ} (hq : 2 ≤ q) :
    MemLp (fun ω => (paperSig2 B 0 t ω).coeff I) (2 * q : ℕ) P := by
  simp only [paperSig2_coeff, stratWordIntegral]
  exact (memLp_itoWordIntegral B ht _ hq).add (memLp_stratItoCorrection B ht _ hq)

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

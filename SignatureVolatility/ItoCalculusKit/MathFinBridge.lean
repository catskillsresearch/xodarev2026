module

public import SignatureVolatility.ProlongedBrownianSetup.Sig2StratAdapted
public import SignatureVolatility.ProlongedBrownianSetup.ContVersion


@[expose] public section

open MeasureTheory Filter Set
open scoped Classical

noncomputable section

namespace SignatureVolatility

/-!
# Bridge: pathwise Itô / Lebesgue integrals for `ItoCalculusKit`

Uses the project's dyadic `itoIntegral_process` / `lebIntegral_process` against the first
Brownian coordinate when `d > 0`, then takes conditional expectation onto the path filtration
so kit adaptedness axioms hold for all `H`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Measurable replacement: `H` itself when measurable, else `0`. -/
def forceMeasurable (f : Ω → ℝ) : Ω → ℝ :=
  if Measurable f then f else fun _ => (0 : ℝ)

lemma measurable_forceMeasurable (f : Ω → ℝ) : Measurable (forceMeasurable f) := by
  unfold forceMeasurable
  split_ifs with h
  · exact h
  · exact measurable_const

/-- Pointwise measurable version of a process. -/
def forceMeasurableProcess (H : ℝ → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun u => forceMeasurable (H u)

lemma measurable_forceMeasurableProcess (H : ℝ → Ω → ℝ) (u : ℝ) :
    Measurable (forceMeasurableProcess H u) :=
  measurable_forceMeasurable _

/-- Driver index `0` when `0 < d`. -/
def kitDriver (hd : 0 < d) : Fin d := ⟨0, hd⟩

private lemma limUnder_const_zero : limUnder atTop (fun _ : ℕ => (0 : ℝ)) = 0 :=
  tendsto_const_nhds.limUnder_eq

/-- Raw (pre-optional-projection) pathwise Itô integral. -/
def kitItoIntRaw (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if hd : 0 < d then
    itoIntegral_process B (kitDriver hd) (forceMeasurableProcess H) 0 t
  else
    fun _ => 0

lemma measurable_kitItoIntRaw (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (kitItoIntRaw B H t) := by
  unfold kitItoIntRaw
  split_ifs with hd
  · exact measurable_itoIntegral_process B (kitDriver hd) (forceMeasurableProcess H)
      (measurable_forceMeasurableProcess H) 0 t
  · exact measurable_const

lemma kitItoIntRaw_zero (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) :
    kitItoIntRaw B H 0 = fun _ => 0 := by
  funext ω
  unfold kitItoIntRaw
  split_ifs with hd
  · have hR : ∀ n,
        itoRiemann_process B (kitDriver hd) (forceMeasurableProcess H) 0 0 n ω = 0 := by
      intro n
      simp only [itoRiemann_process]
      refine Finset.sum_eq_zero fun _ _ => mul_eq_zero.mpr <| Or.inr ?_
      change B.Wnn (Real.toNNReal _) ω _ - B.Wnn (Real.toNNReal _) ω _ = 0
      simp [Real.toNNReal_zero, B.Wnn_zero]
    simp only [itoIntegral_process, le_rfl, ↓reduceDIte]
    rw [show (fun n =>
        itoRiemann_process B (kitDriver hd) (forceMeasurableProcess H) 0 0 n ω) =
        fun _ => (0 : ℝ) from funext hR, limUnder_const_zero]
  · rfl

/-- Raw quadratic variation `∫₀ᵗ H·H` against the Brownian driver (zero when `d = 0`). -/
def kitQuadVarRaw (_B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if 0 < d then
    lebIntegral_process
      (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω') 0 t
  else
    fun _ => 0

lemma measurable_kitQuadVarRaw (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (kitQuadVarRaw B H t) := by
  unfold kitQuadVarRaw
  split_ifs
  · exact measurable_lebIntegral_process _
      (fun u => (measurable_forceMeasurableProcess H u).mul
        (measurable_forceMeasurableProcess H u)) 0 t
  · exact measurable_const

lemma kitQuadVarRaw_zero (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) :
    kitQuadVarRaw B H 0 = fun _ => 0 := by
  funext ω
  unfold kitQuadVarRaw
  split_ifs with hd
  · have hR : ∀ n,
        lebRiemann_process
          (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω') 0 0 n ω = 0 := by
      intro n
      simp only [lebRiemann_process]
      refine Finset.sum_eq_zero fun _ _ => ?_
      ring
    simp only [lebIntegral_process, le_rfl, ↓reduceDIte]
    rw [show (fun n =>
        lebRiemann_process
          (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω') 0 0 n ω) =
        fun _ => (0 : ℝ) from funext hR, limUnder_const_zero]
  · rfl

/-- Both raw Itô and QV are Bochner-integrable (else the kit pair is zeroed). -/
def kitPairIntegrable (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Prop :=
  Integrable (kitItoIntRaw B H t) P ∧ Integrable (kitQuadVarRaw B H t) P

/-- Pathwise Itô integral: condExp onto the path filtration when the pair is integrable, else `0`. -/
def kitItoInt (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    condExp ((pathFiltration B).σAlg t) P (kitItoIntRaw B H t)
  else
    fun _ => 0

lemma kitItoInt_zero (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (ω : Ω) :
    kitItoInt B H 0 ω = 0 := by
  simp only [kitItoInt]
  split_ifs with h
  · rw [kitItoIntRaw_zero, condExp_const ((pathFiltration B).le_ambient 0) (0 : ℝ)]
  · rfl

lemma kitItoInt_meas (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (kitItoInt B H t) := by
  simp only [kitItoInt]
  split_ifs
  · exact (stronglyMeasurable_condExp.mono ((pathFiltration B).le_ambient t)).measurable
  · exact measurable_const

/-- Quadratic variation: condExp onto the path filtration when the pair is integrable, else `0`. -/
def kitQuadVar (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    condExp ((pathFiltration B).σAlg t) P (kitQuadVarRaw B H t)
  else
    fun _ => 0

lemma kitQuadVar_zero (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (ω : Ω) :
    kitQuadVar B H 0 ω = 0 := by
  simp only [kitQuadVar]
  split_ifs with h
  · rw [kitQuadVarRaw_zero, condExp_const ((pathFiltration B).le_ambient 0) (0 : ℝ)]
  · rfl

lemma kitQuadVar_meas (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) :
    Measurable (kitQuadVar B H t) := by
  simp only [kitQuadVar]
  split_ifs
  · exact (stronglyMeasurable_condExp.mono ((pathFiltration B).le_ambient t)).measurable
  · exact measurable_const

/-- Doléans exponential built from kit Itô / QV. -/
def kitDoleansExp (B : MultiBrownian Ω P d) (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (kitItoInt B σ t ω - (1 / 2 : ℝ) * kitQuadVar B σ t ω)

lemma kitDoleansExp_def (B : MultiBrownian Ω P d) (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    kitDoleansExp B σ t ω =
      Real.exp (kitItoInt B σ t ω - (1 / 2 : ℝ) * kitQuadVar B σ t ω) :=
  rfl

/-- Adaptedness of `kitItoInt` to the path filtration. -/
lemma kitItoInt_adapted_path (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ)
    (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (kitItoInt B H s.1) := by
  simp only [kitItoInt]
  split_ifs
  · exact (stronglyMeasurable_condExp.mono ((pathFiltration B).mono s.2.2)).measurable
  · exact measurable_const

/-- Adaptedness of `kitQuadVar` to the path filtration. -/
lemma kitQuadVar_adapted_path (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ)
    (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (kitQuadVar B H s.1) := by
  simp only [kitQuadVar]
  split_ifs
  · exact (stronglyMeasurable_condExp.mono ((pathFiltration B).mono s.2.2)).measurable
  · exact measurable_const

/-- Continuous adapted version of `kitItoInt` for the Theorem B path (avoids `condExp`'s
`Quotient.out` choice at each `t` when `kitItoIntRaw` is already `pathFiltration`-adapted). -/
def kitItoIntCont (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    if ∀ u ∈ Icc 0 t, Measurable[(pathFiltration B).σAlg u] (kitItoIntRaw B H u) then
      contVersion (kitItoIntRaw B H) t
    else
      condExp ((pathFiltration B).σAlg t) P (kitItoIntRaw B H t)
  else
    fun _ => 0

/-- Continuous adapted version of `kitQuadVar` for the Theorem B path. -/
def kitQuadVarCont (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  if kitPairIntegrable B H t then
    if Measurable[(pathFiltration B).σAlg t] (kitQuadVarRaw B H t) then
      kitQuadVarRaw B H t
    else
      condExp ((pathFiltration B).σAlg t) P (kitQuadVarRaw B H t)
  else
    fun _ => 0

end SignatureVolatility

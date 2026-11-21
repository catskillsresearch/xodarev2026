module

public import SignatureVolatility.ItoCalculusKit.MathFinBridge


@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# Raw `limUnder` integrals versus the kit integrals

`kitItoInt` / `kitQuadVar` are the raw `limUnder` Riemann limits, gated by Bochner integrability
and projected by `condExp` onto the path filtration. For **adapted** integrands the raw limits
are already path-filtration measurable, so the projection is the identity (pointwise, not merely
almost surely):

* `measurable_kitItoIntRaw_path`, `measurable_kitQuadVarRaw_path`: adaptedness of the raw limits;
* `kitItoInt_eq_raw`, `kitQuadVar_eq_raw`: `condExp` is the identity under the integrability gate;
* `kitDoleansExp_adapted_path`: the kit Doléans exponential is adapted (for every `σ`);
* `kit_doleans_sde_of_raw`: **reduction of the Doléans SDE to raw statements** — for any `σ`, the
  SDE at time `t` follows from the integrability gate for `H = s₀ Z σ` and the almost-sure
  identification of the raw Itô limit `limUnder ∑ H ΔW = s₀ Z_t - s₀`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma forceMeasurableProcess_eq_of_adapted (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ} {t u : ℝ}
    (hH : Measurable[(pathFiltration B).σAlg t] (H u)) : forceMeasurableProcess H u = H u := by
  have h : Measurable (H u) := hH.mono ((pathFiltration B).le_ambient t) le_rfl
  simp [forceMeasurableProcess, forceMeasurable, h]

/-- The raw Itô limit of an integrand adapted on `[0, t]` is `𝓕_t`-measurable. -/
lemma measurable_kitItoIntRaw_path (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) {t : ℝ}
    (ht : 0 ≤ t)
    (hH : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg t] (H u)) :
    Measurable[(pathFiltration B).σAlg t] (kitItoIntRaw B H t) := by
  unfold kitItoIntRaw
  split_ifs with hd
  · exact measurable_itoIntegral_process_pathFiltration B (kitDriver hd)
      (forceMeasurableProcess H)
      (fun u hu0 hut => by
        rw [forceMeasurableProcess_eq_of_adapted B (hH u hu0 hut)]
        exact hH u hu0 hut) le_rfl ht le_rfl
  · exact measurable_const

/-- The raw quadratic variation of an integrand adapted on `[0, t]` is `𝓕_t`-measurable. -/
lemma measurable_kitQuadVarRaw_path (B : MultiBrownian Ω P d) (H : ℝ → Ω → ℝ) {t : ℝ}
    (ht : 0 ≤ t)
    (hH : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg t] (H u)) :
    Measurable[(pathFiltration B).σAlg t] (kitQuadVarRaw B H t) := by
  unfold kitQuadVarRaw
  split_ifs with hd
  · exact measurable_lebIntegral_process_pathFiltration B
      (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω')
      (fun u hu0 hut => by
        have h : Measurable[(pathFiltration B).σAlg t] (forceMeasurableProcess H u) := by
          rw [forceMeasurableProcess_eq_of_adapted B (hH u hu0 hut)]
          exact hH u hu0 hut
        exact h.mul h) le_rfl ht le_rfl
  · exact measurable_const

/-- For adapted integrands passing the integrability gate, `kitItoInt` **is** the raw limit. -/
lemma kitItoInt_eq_raw (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hH : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg t] (H u))
    (hpair : kitPairIntegrable B H t) : kitItoInt B H t = kitItoIntRaw B H t := by
  simp only [kitItoInt, hpair, ↓reduceIte]
  exact condExp_of_stronglyMeasurable ((pathFiltration B).le_ambient t)
    (measurable_kitItoIntRaw_path B H ht hH).stronglyMeasurable hpair.1

/-- For adapted integrands passing the integrability gate, `kitQuadVar` **is** the raw limit. -/
lemma kitQuadVar_eq_raw (B : MultiBrownian Ω P d) {H : ℝ → Ω → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hH : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg t] (H u))
    (hpair : kitPairIntegrable B H t) : kitQuadVar B H t = kitQuadVarRaw B H t := by
  simp only [kitQuadVar, hpair, ↓reduceIte]
  exact condExp_of_stronglyMeasurable ((pathFiltration B).le_ambient t)
    (measurable_kitQuadVarRaw_path B H ht hH).stronglyMeasurable hpair.2

/-- The kit Doléans exponential is adapted to the path filtration, for every `σ`. -/
lemma kitDoleansExp_adapted_path (B : MultiBrownian Ω P d) (σ : ℝ → Ω → ℝ) (t : ℝ)
    (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (kitDoleansExp B σ s.1) :=
  Real.measurable_exp.comp
    ((kitItoInt_adapted_path B σ t s).sub ((kitQuadVar_adapted_path B σ t s).const_mul (1 / 2 : ℝ)))

/-- **Reduction of the Doléans SDE to raw statements.** For any volatility `σ`, the kit SDE at
time `t` follows from (i) the integrability gate for `H = s₀ Z σ` and (ii) the almost-sure
identification of the raw `limUnder` Itô–Riemann limit of `H` with `s₀ Z_t - s₀`; `condExp` onto
the path filtration then acts as the identity because `Z_t` is adapted. -/
theorem kit_doleans_sde_of_raw (B : MultiBrownian Ω P d) (σ : ℝ → Ω → ℝ) (s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t)
    (hpair : kitPairIntegrable B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t)
    (hraw : kitItoIntRaw B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t =ᵐ[P]
      fun ω => s₀ * kitDoleansExp B σ t ω - s₀) :
    ∀ᵐ ω ∂P, s₀ * kitDoleansExp B σ t ω =
      s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  have hsm : StronglyMeasurable[(pathFiltration B).σAlg t]
      (fun ω => s₀ * kitDoleansExp B σ t ω - s₀) :=
    (((kitDoleansExp_adapted_path B σ t ⟨t, ht, le_rfl⟩).const_mul s₀).sub_const
      s₀).stronglyMeasurable
  have hce : kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t =ᵐ[P]
      fun ω => s₀ * kitDoleansExp B σ t ω - s₀ := by
    simp only [kitItoInt, hpair, ↓reduceIte]
    refine (condExp_congr_ae hraw).trans ?_
    rw [condExp_of_stronglyMeasurable ((pathFiltration B).le_ambient t) hsm (hpair.1.congr hraw)]
  filter_upwards [hce] with ω hω
  rw [hω]
  ring

end SignatureVolatility

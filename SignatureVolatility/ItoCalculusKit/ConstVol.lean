module

public import SignatureVolatility.ItoCalculusKit.MathFinBridge


@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SignatureVolatility

/-!
# Constant volatility and locality for the MathFin-bridge Itô kit

* For `σ ≡ c` and `0 < d`, the kit Itô integral is `c W⁰_t` and the kit quadratic variation is
  `c² t`, pointwise in `ω`, so the kit Doléans exponential is geometric Brownian motion
  (`kitDoleansExp_const`).
* Locality: the kit only reads the integrand on `[0, t]` (`kitItoInt_congr`, `kitQuadVar_congr`).
* Gaussian exponential moments of the driver (`integrable_exp_mul_Wnn`, `integral_exp_mul_Wnn`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Constant volatility: the kit Doléans exponential is geometric Brownian motion -/

lemma forceMeasurableProcess_const (c : ℝ) :
    forceMeasurableProcess (fun (_ : ℝ) (_ : Ω) => c) = fun _ _ => c := by
  funext u
  simp [forceMeasurableProcess, forceMeasurable]

/-- For `σ ≡ c` the Riemann sums telescope: the raw Itô integral is `c · W⁰_t`, for every `ω`. -/
lemma kitItoIntRaw_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    kitItoIntRaw B (fun _ _ => c) t =
      fun ω => c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) := by
  funext ω
  have hR : ∀ n, itoRiemann_process B (kitDriver hd)
      (forceMeasurableProcess (fun _ _ => c)) 0 t n ω =
        c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) := by
    intro n
    simp only [itoRiemann_process, forceMeasurableProcess_const, wnnIncr, ← Finset.mul_sum]
    have hsum := Finset.sum_range_sub
      (fun j : ℕ => B.Wnn (Real.toNNReal (0 + (j : ℝ) * ((t - 0) / ((n + 1 : ℕ) : ℝ)))) ω
        (kitDriver hd)) (n + 1)
    have hcast : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := fun j => by push_cast; ring
    simp only [hcast] at hsum ⊢
    rw [hsum]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h1 : 0 + ((n : ℝ) + 1) * ((t - 0) / ((n : ℝ) + 1)) = t := by field_simp; ring
    have h0 : 0 + ((0 : ℕ) : ℝ) * ((t - 0) / ((n : ℝ) + 1)) = 0 := by simp
    rw [h1, h0, Real.toNNReal_zero, B.Wnn_zero, sub_zero]
  simp only [kitItoIntRaw, hd, itoIntegral_process, ht, ↓reduceDIte]
  rw [show (fun n => itoRiemann_process B (kitDriver hd)
      (forceMeasurableProcess (fun _ _ => c)) 0 t n ω) =
      fun _ => c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) from funext hR]
  exact tendsto_const_nhds.limUnder_eq

/-- For `σ ≡ c` the raw quadratic variation is `c² t`. -/
lemma kitQuadVarRaw_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    kitQuadVarRaw B (fun (_ : ℝ) (_ : Ω) => c) t = fun _ => c ^ 2 * t := by
  funext ω
  have hR : ∀ n, lebRiemann_process
      (fun s ω' => forceMeasurableProcess (fun (_ : ℝ) (_ : Ω) => c) s ω' *
        forceMeasurableProcess (fun (_ : ℝ) (_ : Ω) => c) s ω') 0 t n ω = c ^ 2 * t := by
    intro n
    simp only [lebRiemann_process, forceMeasurableProcess_const, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  simp only [kitQuadVarRaw, hd, ↓reduceIte, lebIntegral_process, ht, ↓reduceDIte]
  rw [show (fun n => lebRiemann_process
      (fun s ω' => forceMeasurableProcess (fun (_ : ℝ) (_ : Ω) => c) s ω' *
        forceMeasurableProcess (fun (_ : ℝ) (_ : Ω) => c) s ω') 0 t n ω) =
      fun _ => c ^ 2 * t from funext hR]
  exact tendsto_const_nhds.limUnder_eq

lemma kitPairIntegrable_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : kitPairIntegrable B (fun _ _ => c) t := by
  refine ⟨?_, ?_⟩
  · rw [kitItoIntRaw_const B hd c ht]
    exact ((B.isBrownian (kitDriver hd)).toIsPreBrownianReal.integrable_eval _).const_mul c
  · rw [kitQuadVarRaw_const B hd c ht]
    exact integrable_const _

/-- **Pointwise** (every `ω`): for `σ ≡ c`, `kitItoInt` is `c · W⁰_t`. -/
lemma kitItoInt_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ω : Ω) :
    kitItoInt B (fun _ _ => c) t ω = c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) := by
  have hpair := kitPairIntegrable_const B hd c ht
  have hsm : StronglyMeasurable[(pathFiltration B).σAlg t]
      (kitItoIntRaw B (fun _ _ => c) t) := by
    rw [kitItoIntRaw_const B hd c ht]
    exact ((measurable_W_pathFiltration B (T := t) ⟨t, ht, le_rfl⟩
      (kitDriver hd)).const_mul c).stronglyMeasurable
  simp only [kitItoInt, hpair, ↓reduceIte]
  rw [condExp_of_stronglyMeasurable ((pathFiltration B).le_ambient t) hsm hpair.1,
    kitItoIntRaw_const B hd c ht]

/-- **Pointwise** (every `ω`): for `σ ≡ c`, `kitQuadVar` is `c² t`. -/
lemma kitQuadVar_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (ω : Ω) : kitQuadVar B (fun _ _ => c) t ω = c ^ 2 * t := by
  have hpair := kitPairIntegrable_const B hd c ht
  simp only [kitQuadVar, hpair, ↓reduceIte]
  rw [kitQuadVarRaw_const B hd c ht, condExp_const ((pathFiltration B).le_ambient t) (c ^ 2 * t)]

/-- **Black–Scholes left-hand side.** For constant volatility `σ ≡ c` the kit Doléans
exponential is geometric Brownian motion, pointwise in `ω`. -/
theorem kitDoleansExp_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ω : Ω) :
    kitDoleansExp B (fun _ _ => c) t ω =
      Real.exp (c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) - (1 / 2 : ℝ) * (c ^ 2 * t)) := by
  rw [kitDoleansExp_def, kitItoInt_const B hd c ht, kitQuadVar_const B hd c ht]

lemma measurable_kitDoleansExp (B : MultiBrownian Ω P d) (σ : ℝ → Ω → ℝ) (s : ℝ) :
    Measurable (kitDoleansExp B σ s) :=
  Real.measurable_exp.comp
    ((kitItoInt_meas B σ s).sub ((kitQuadVar_meas B σ s).const_mul (1 / 2 : ℝ)))

lemma integrable_exp_mul_Wnn (B : MultiBrownian Ω P d) (k : Fin d) (a : ℝ) (s : ℝ≥0) :
    Integrable (fun ω => Real.exp (a * B.Wnn s ω k)) P :=
  ((B.isBrownian k).toIsPreBrownianReal.hasLaw_eval s).integrable_comp
    (integrable_exp_mul_gaussianReal a)

lemma integral_exp_mul_Wnn (B : MultiBrownian Ω P d) (k : Fin d) (a : ℝ) (s : ℝ≥0) :
    ∫ ω, Real.exp (a * B.Wnn s ω k) ∂P = Real.exp ((s : ℝ) * a ^ 2 / 2) := by
  have h := mgf_gaussianReal ((B.isBrownian k).toIsPreBrownianReal.hasLaw_eval s) a
  simpa [mgf] using h

/-! ## Locality: the kit only reads the integrand on the grid points of `[0, t]` -/

lemma grid_mem_Icc {t : ℝ} (ht : 0 ≤ t) {n j : ℕ} (hj : j < n + 1) :
    0 + (j : ℝ) * ((t - 0) / ((n + 1 : ℕ) : ℝ)) ∈ Icc 0 t := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hΔ : 0 ≤ (t - 0) / ((n + 1 : ℕ) : ℝ) := div_nonneg (by simpa using ht) hn.le
  have hjr : (j : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hj.le
  refine ⟨by positivity, ?_⟩
  calc 0 + (j : ℝ) * ((t - 0) / ((n + 1 : ℕ) : ℝ))
      ≤ ((n + 1 : ℕ) : ℝ) * ((t - 0) / ((n + 1 : ℕ) : ℝ)) := by
        rw [zero_add]
        exact mul_le_mul_of_nonneg_right hjr hΔ
    _ = t := by field_simp; ring

lemma kitItoIntRaw_congr (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (h : ∀ u ∈ Icc 0 t, H u = H' u) : kitItoIntRaw B H t = kitItoIntRaw B H' t := by
  funext ω
  unfold kitItoIntRaw
  split_ifs with hd
  · by_cases ht : 0 ≤ t
    · simp only [itoIntegral_process, ht, ↓reduceDIte]
      congr 1
      funext n
      simp only [itoRiemann_process]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [forceMeasurableProcess, h _ (grid_mem_Icc ht (Finset.mem_range.mp hj))]
    · simp [itoIntegral_process, ht]
  · rfl

lemma kitQuadVarRaw_congr (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (h : ∀ u ∈ Icc 0 t, H u = H' u) : kitQuadVarRaw B H t = kitQuadVarRaw B H' t := by
  funext ω
  unfold kitQuadVarRaw
  split_ifs with hd
  · by_cases ht : 0 ≤ t
    · simp only [lebIntegral_process, ht, ↓reduceDIte]
      congr 1
      funext n
      simp only [lebRiemann_process]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [forceMeasurableProcess, h _ (grid_mem_Icc ht (Finset.mem_range.mp hj))]
    · simp [lebIntegral_process, ht]
  · rfl

lemma kitItoInt_congr (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (h : ∀ u ∈ Icc 0 t, H u = H' u) : kitItoInt B H t = kitItoInt B H' t := by
  unfold kitItoInt kitPairIntegrable
  rw [kitItoIntRaw_congr B h, kitQuadVarRaw_congr B h]

lemma kitQuadVar_congr (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (h : ∀ u ∈ Icc 0 t, H u = H' u) : kitQuadVar B H t = kitQuadVar B H' t := by
  unfold kitQuadVar kitPairIntegrable
  rw [kitItoIntRaw_congr B h, kitQuadVarRaw_congr B h]

end SignatureVolatility

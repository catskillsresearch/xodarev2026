module

public import SignatureVolatility.DualPairing
public import SignatureVolatility.HypH1
public import SignatureVolatility.HypH2
public import SignatureVolatility.HypH3
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import SignatureVolatility.ItoCalculusKit.ConstVol
public import SignatureVolatility.ItoCalculusKit.KitRaw
public import SignatureVolatility.ItoCalculusKit.MathFinBridge
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto
public import SignatureVolatility.ItoCalculusKit.SigmaContinuity


@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace SignatureVolatility

/-!
# Doléans SDE for the MathFin-bridge Itô kit

Proved here (no axioms beyond Lean's standard three):

* `d = 0` (`kit_doleans_sde_of_no_driver`): no driver ⇒ Itô = QV = 0 ⇒ Doléans = 1.
* **Constant volatility / Black–Scholes** (`kit_doleans_sde_const`, `kit_doleans_sde_one`,
  `kit_doleans_sde_of_const_on`): for `σ ≡ c` (on `[0, T] × Ω`) and `0 < d`,
  `s₀ Z_t = s₀ + ∫₀ᵗ s₀ Z_s c dW_s` a.s. for the `limUnder` kit. Ingredients:
  - `kitDoleansExp_const`: `Z_t = exp (c W⁰_t - c² t / 2)` pointwise in `ω`;
  - `ae_tendsto_qvBlocks` (`BrownianQuadVarAS`): almost-sure, full-sequence quadratic variation
    of `W⁰` on rational blocks of the uniform grids `t·j/(n+1)` (fourth moments + Borel–Cantelli);
  - `tendsto_expRiemann` (`PathwiseExpIto`): pathwise Föllmer–Itô formula for the exponential,
    giving a.s. convergence of the left Itô–Riemann sums of `s₀ Z c` to `s₀ (Z_t - 1)`;
  - Bochner integrability of the raw Itô limit (Gaussian mgf) and of the raw quadratic variation
    `∫₀ᵗ (s₀ Z c)²` (pathwise Riemann sums + Fatou), so the `kitPairIntegrable` gate is open and
    `condExp` onto the path filtration is the identity.
* Pathwise continuity of the signature volatility (`continuousOn_sigma_of_brownian`), feeding the
  `ContinuousOn` hypothesis of the kit field.

* **Signature volatility, quadratic-variation half** (every `ω`, under H1–H2 / H3):
  `measurable_signatureSigma_path` (adaptedness), `kitQuadVarRaw_signatureSigma`
  (`limUnder` Riemann sums of `σ²` equal `∫₀ᵗ σ²`), `integrable_kitQuadVarRaw_signatureSigma`,
  and `kitDoleansExp_signatureSigma` (`Z_t = exp (limUnder ∑ σ ΔW - ½ ∫₀ᵗ σ²)` once the raw Itô
  limit of `σ` is integrable).

Still an axiom: `kit_doleans_sde_of_driver`, the SDE for `0 < d` and a **non-constant** signature
volatility `σ = ⟨ℓ, Ŵ⟩` under H1–H3. By `kit_doleans_sde_of_raw` (`KitRaw`) it would follow from
the integrability gate for `H = s₀ Z σ` and the a.s. identification of the raw limit
`limUnder ∑ H ΔW = s₀ Z_t - s₀`. For `d ≥ 2` the integrand depends on non-driver coordinates, so
`∫ σ dW⁰` is a Lévy-area-type object with no pathwise (Föllmer) formula; the missing input is
almost-sure, full-sequence convergence of adapted Itô–Riemann sums. Its foundations are proved in
`JointPast` (driver increments are independent of the joint past, from process-level
`coordsIndep`) and `MartingaleTransform` (discrete Burkholder-type `L⁴` bound for adapted
transforms); the `L⁴`-Cauchy construction of the limit, moment/regularity bounds for `σ` and
`Z` (from H3), and the final Taylor assembly are not yet formalized.

The SDE is **false** for arbitrary `σ : ℝ → Ω → ℝ`, because `kitItoInt` / `kitQuadVar` are
`limUnder`s of left Riemann sums on the uniform grids `t·j/(n+1)`, gated by Bochner
integrability, then projected by `condExp`:

* `IntegrableOn σ²` alone: a deterministic `σ` supported on the null set `{1 - 1/k}` is a
  machine-checked counterexample (grids see null-set spikes).
* adding pathwise continuity: a time-constant `σ = 𝟙_A` with `A` independent of the driver
  (anticipating) gives `s₀·Z_t ≠ s₀ + ∫ s₀ Z σ dW` after the `condExp` projection.
* adding adaptedness: `σ = W⁰` violates H3 and `∫₀ᵗ Z²σ²` is not integrable for `t ≥ 0.63`,
  so the integrability gate zeroes the right-hand integral.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- No Brownian driver: raw Itô/QV vanish, so the Doléans SDE is `s₀ = s₀`. -/
theorem kit_doleans_sde_of_no_driver (B : MultiBrownian Ω P d) (hd : ¬ 0 < d)
    (s₀ : ℝ) (σ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    s₀ * kitDoleansExp B σ t ω =
      s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  have hIto0 : ∀ H, kitItoIntRaw B H t = fun _ => 0 := by
    intro H; funext; simp [kitItoIntRaw, hd]
  have hQV0 : ∀ H, kitQuadVarRaw B H t = fun _ => 0 := by
    intro H; funext; simp [kitQuadVarRaw, hd]
  have hPair : ∀ H, kitPairIntegrable B H t := by
    intro H
    exact ⟨by simp [hIto0 H], by simp [hQV0 H]⟩
  have hZ : kitDoleansExp B σ t ω = 1 := by
    simp [kitDoleansExp, kitItoInt, kitQuadVar, hPair σ, hIto0 σ, hQV0 σ,
      condExp_const ((pathFiltration B).le_ambient t) (0 : ℝ), Real.exp_zero]
  simp [hZ, kitItoInt, hPair, hIto0,
    condExp_const ((pathFiltration B).le_ambient t) (0 : ℝ)]

/-! ## Constant volatility: the Doléans SDE (Black–Scholes case) -/

lemma forceMeasurableProcess_of_measurable {H : ℝ → Ω → ℝ} (hH : ∀ u, Measurable (H u)) :
    forceMeasurableProcess H = H := by
  funext u
  simp [forceMeasurableProcess, forceMeasurable, hH u]

/-- The integrand `s₀ · Z · σ` of the Doléans SDE for `σ ≡ c`. -/
noncomputable def doleansConstIntegrand (B : MultiBrownian Ω P d) (c s₀ : ℝ) : ℝ → Ω → ℝ :=
  fun s ω' => (s₀ * kitDoleansExp B (fun _ _ => c) s ω') * c

lemma measurable_doleansConstIntegrand (B : MultiBrownian Ω P d) (c s₀ : ℝ) (s : ℝ) :
    Measurable (doleansConstIntegrand B c s₀ s) :=
  ((measurable_kitDoleansExp B _ s).const_mul s₀).mul_const c

lemma doleansConstIntegrand_apply (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ) {s : ℝ}
    (hs : 0 ≤ s) (ω : Ω) :
    doleansConstIntegrand B c s₀ s ω =
      s₀ * (Real.exp (c * B.Wnn (Real.toNNReal s) ω (kitDriver hd) -
        (1 / 2 : ℝ) * (c ^ 2 * s)) * c) := by
  rw [doleansConstIntegrand, kitDoleansExp_const B hd c hs]
  ring

/-- The left Itô–Riemann sums of `s₀ Z c` are `s₀` times the pathwise exponential sums. -/
lemma itoRiemann_doleansConst (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) (ω : Ω) :
    itoRiemann_process B (kitDriver hd)
        (forceMeasurableProcess (doleansConstIntegrand B c s₀)) 0 t n ω =
      s₀ * ∑ j ∈ Finset.range (n + 1),
        Real.exp (c * B.Wnn (Real.toNNReal ((j : ℝ) * (t / ((n : ℝ) + 1)))) ω (kitDriver hd) -
            (1 / 2 : ℝ) * (c ^ 2 * ((j : ℝ) * (t / ((n : ℝ) + 1))))) *
          (c * (B.Wnn (Real.toNNReal (((j : ℝ) + 1) * (t / ((n : ℝ) + 1)))) ω (kitDriver hd) -
            B.Wnn (Real.toNNReal ((j : ℝ) * (t / ((n : ℝ) + 1)))) ω (kitDriver hd))) := by
  rw [forceMeasurableProcess_of_measurable (measurable_doleansConstIntegrand B c s₀),
    Finset.mul_sum]
  simp only [itoRiemann_process, wnnIncr, zero_add, sub_zero, Nat.cast_add, Nat.cast_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : 0 ≤ (j : ℝ) * (t / ((n : ℝ) + 1)) := by positivity
  rw [doleansConstIntegrand_apply B hd c s₀ hj]
  ring

/-- **Almost-sure, full-sequence convergence of the Itô–Riemann sums** of `s₀ Z c` on the uniform
grids: the raw `limUnder` Itô integral is `s₀ (Z_t - 1)` (pathwise Föllmer–Itô + a.s. quadratic
variation). -/
lemma kitItoIntRaw_doleansConst_ae (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    kitItoIntRaw B (doleansConstIntegrand B c s₀) t =ᵐ[P] fun ω =>
      s₀ * (Real.exp (c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) -
        (1 / 2 : ℝ) * (c ^ 2 * t)) - 1) := by
  filter_upwards [ae_tendsto_qvBlocks B (kitDriver hd) ht] with ω hω
  have hx : Continuous fun s : ℝ => B.Wnn (Real.toNNReal s) ω (kitDriver hd) :=
    (B.pathContinuous _ ω).comp continuous_real_toNNReal
  have h := (tendsto_expRiemann ht c hx (fun K i => hω K i)).const_mul s₀
  simp only [Real.toNNReal_zero, B.Wnn_zero, mul_zero, Real.exp_zero] at h
  simp only [kitItoIntRaw, hd, ↓reduceDIte, itoIntegral_process, ht]
  rw [funext fun n => itoRiemann_doleansConst B hd c s₀ ht n ω]
  exact h.limUnder_eq

lemma integrable_kitItoIntRaw_doleansConst (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (kitItoIntRaw B (doleansConstIntegrand B c s₀) t) P := by
  refine Integrable.congr ?_ (kitItoIntRaw_doleansConst_ae B hd c s₀ ht).symm
  simp only [Real.exp_sub]
  exact (((integrable_exp_mul_Wnn B (kitDriver hd) c (Real.toNNReal t)).div_const _).sub
    (integrable_const 1)).const_mul s₀

omit [IsProbabilityMeasure P] in
/-- Fatou: a pointwise limit of nonnegative integrable functions with bounded integrals is
integrable. -/
lemma integrable_of_tendsto_of_integral_le {R : ℕ → Ω → ℝ} {L : Ω → ℝ}
    (hRm : ∀ n, Measurable (R n)) (hR0 : ∀ n ω, 0 ≤ R n ω) (hRi : ∀ n, Integrable (R n) P)
    (hlim : ∀ ω, Tendsto (fun n => R n ω) atTop (𝓝 (L ω))) {C : ℝ}
    (hC : ∀ n, ∫ ω, R n ω ∂P ≤ C) : Integrable L P := by
  have hLm : Measurable L := measurable_of_tendsto_metrizable hRm (tendsto_pi_nhds.mpr hlim)
  refine ⟨hLm.aestronglyMeasurable, ?_⟩
  have hL0 : ∀ ω, 0 ≤ L ω := fun ω => ge_of_tendsto' (hlim ω) fun n => hR0 n ω
  have h1 : ∫⁻ ω, ‖L ω‖ₑ ∂P = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (R n ω)) atTop ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (hL0 ω)]
    exact ((ENNReal.continuous_ofReal.tendsto _).comp (hlim ω)).liminf_eq.symm
  rw [HasFiniteIntegral, h1]
  refine lt_of_le_of_lt (lintegral_liminf_le fun n => (hRm n).ennreal_ofReal) ?_
  refine lt_of_le_of_lt (liminf_le_of_le (by isBoundedDefault) fun b hb => ?_)
    (ENNReal.ofReal_lt_top (r := C))
  obtain ⟨n, hn⟩ := hb.exists
  refine hn.trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hRi n) (ae_of_all _ (hR0 n))]
  exact ENNReal.ofReal_le_ofReal (hC n)

/-- The raw quadratic variation `∫₀ᵗ (s₀ Z c)²` is Bochner-integrable (Riemann sums converge
pathwise by continuity; Fatou + the Gaussian moment generating function bound the limit). -/
lemma integrable_kitQuadVarRaw_doleansConst (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (kitQuadVarRaw B (doleansConstIntegrand B c s₀) t) P := by
  set k : Fin d := kitDriver hd with hk
  set G : Ω → ℝ → ℝ := fun ω s =>
    (s₀ * (Real.exp (c * B.Wnn (Real.toNNReal s) ω k - (1 / 2 : ℝ) * (c ^ 2 * s)) * c)) ^ 2
    with hG
  have hGc : ∀ ω, Continuous (G ω) := fun ω => by
    have hx : Continuous fun s : ℝ => B.Wnn (Real.toNNReal s) ω k :=
      (B.pathContinuous _ ω).comp continuous_real_toNNReal
    simp only [hG]
    fun_prop
  have hGeq : ∀ ω s, G ω s = (s₀ * c) ^ 2 * Real.exp (-(c ^ 2 * s)) *
      Real.exp ((2 * c) * B.Wnn (Real.toNNReal s) ω k) := fun ω s => by
    have hexp : Real.exp (c * B.Wnn (Real.toNNReal s) ω k - (1 / 2 : ℝ) * (c ^ 2 * s)) ^ 2 =
        Real.exp (-(c ^ 2 * s)) * Real.exp ((2 * c) * B.Wnn (Real.toNNReal s) ω k) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp only [hG]
    rw [mul_assoc, ← hexp]
    ring
  set R : ℕ → Ω → ℝ := fun n ω => ∑ j ∈ Finset.range (n + 1),
    G ω ((j : ℝ) * (t / ((n : ℝ) + 1))) * (t / ((n : ℝ) + 1)) with hR
  have hRlim : ∀ ω, Tendsto (fun n => R n ω) atTop
      (𝓝 (kitQuadVarRaw B (doleansConstIntegrand B c s₀) t ω)) := by
    intro ω
    have hlim := tendsto_lebRiemann_of_continuousOn ht (hGc ω).continuousOn
    have hRn : ∀ n, lebRiemann_process
        (fun s ω' => forceMeasurableProcess (doleansConstIntegrand B c s₀) s ω' *
          forceMeasurableProcess (doleansConstIntegrand B c s₀) s ω') 0 t n ω = R n ω := by
      intro n
      rw [forceMeasurableProcess_of_measurable (measurable_doleansConstIntegrand B c s₀)]
      simp only [lebRiemann_process, zero_add, sub_zero, Nat.cast_add, Nat.cast_one, hR]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : 0 ≤ (j : ℝ) * (t / ((n : ℝ) + 1)) := by positivity
      rw [doleansConstIntegrand_apply B hd c s₀ hj]
      simp only [hG]
      ring
    have heq : kitQuadVarRaw B (doleansConstIntegrand B c s₀) t ω = ∫ s in (0 : ℝ)..t, G ω s := by
      simp only [kitQuadVarRaw, hd, ↓reduceIte, lebIntegral_process, ht, ↓reduceDIte]
      rw [funext hRn]
      exact hlim.limUnder_eq
    rw [heq]
    exact hlim
  have hGm : ∀ s, Measurable fun ω => G ω s := fun s =>
    ((((((B.Wnn_meas (Real.toNNReal s) k).const_mul c).sub_const _).exp).mul_const c).const_mul
      s₀).pow_const 2
  have hGi : ∀ s, Integrable (fun ω => G ω s) P := fun s => by
    simp only [hGeq]
    exact (integrable_exp_mul_Wnn B k (2 * c) (Real.toNNReal s)).const_mul _
  have hGle : ∀ s, 0 ≤ s → s ≤ t →
      ∫ ω, G ω s ∂P ≤ (s₀ * c) ^ 2 * Real.exp (t * (2 * c) ^ 2 / 2) := fun s hs hst => by
    simp only [hGeq]
    rw [integral_const_mul, integral_exp_mul_Wnn, Real.coe_toNNReal _ hs]
    have h1 : Real.exp (-(c ^ 2 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg c]
    have h2 : Real.exp (s * (2 * c) ^ 2 / 2) ≤ Real.exp (t * (2 * c) ^ 2 / 2) := by
      rw [Real.exp_le_exp]
      nlinarith [sq_nonneg (2 * c)]
    have h3 : 0 ≤ (s₀ * c) ^ 2 := sq_nonneg _
    calc (s₀ * c) ^ 2 * Real.exp (-(c ^ 2 * s)) * Real.exp (s * (2 * c) ^ 2 / 2)
        ≤ (s₀ * c) ^ 2 * 1 * Real.exp (t * (2 * c) ^ 2 / 2) := by
          gcongr
      _ = (s₀ * c) ^ 2 * Real.exp (t * (2 * c) ^ 2 / 2) := by ring
  refine integrable_of_tendsto_of_integral_le (R := R)
    (C := (s₀ * c) ^ 2 * Real.exp (t * (2 * c) ^ 2 / 2) * t)
    (fun n => Finset.measurable_sum _ fun j _ => (hGm _).mul_const _)
    (fun n ω => Finset.sum_nonneg fun j _ =>
      mul_nonneg (sq_nonneg _) (div_nonneg ht (by positivity)))
    (fun n => integrable_finsetSum _ fun j _ => (hGi _).mul_const _) hRlim fun n => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hΔ0 : 0 ≤ t / ((n : ℝ) + 1) := div_nonneg ht hn1.le
  simp only [hR]
  rw [integral_finsetSum _ fun j _ => (hGi _).mul_const _]
  calc ∑ j ∈ Finset.range (n + 1),
        ∫ ω, G ω ((j : ℝ) * (t / ((n : ℝ) + 1))) * (t / ((n : ℝ) + 1)) ∂P
      ≤ ∑ _j ∈ Finset.range (n + 1),
        (s₀ * c) ^ 2 * Real.exp (t * (2 * c) ^ 2 / 2) * (t / ((n : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [integral_mul_const]
        refine mul_le_mul_of_nonneg_right (hGle _ (by positivity) ?_) hΔ0
        have hjr : (j : ℝ) ≤ (n : ℝ) + 1 := by
          exact_mod_cast (Finset.mem_range.mp hj).le
        calc (j : ℝ) * (t / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * (t / ((n : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hjr hΔ0
          _ = t := by field_simp
    _ = (s₀ * c) ^ 2 * Real.exp (t * (2 * c) ^ 2 / 2) * t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

lemma kitPairIntegrable_doleansConst (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : kitPairIntegrable B (doleansConstIntegrand B c s₀) t :=
  ⟨integrable_kitItoIntRaw_doleansConst B hd c s₀ ht,
    integrable_kitQuadVarRaw_doleansConst B hd c s₀ ht⟩

/-- **Black–Scholes right-hand side.** For `σ ≡ c`, the kit Itô integral of `s₀ Z c` is
`s₀ (Z_t - 1)` almost surely (`condExp` acts as the identity on the adapted limit). -/
theorem kitItoInt_doleansConst_ae (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    kitItoInt B (doleansConstIntegrand B c s₀) t =ᵐ[P] fun ω =>
      s₀ * (Real.exp (c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) -
        (1 / 2 : ℝ) * (c ^ 2 * t)) - 1) := by
  have hpair := kitPairIntegrable_doleansConst B hd c s₀ ht
  have hraw := kitItoIntRaw_doleansConst_ae B hd c s₀ ht
  have hsm : StronglyMeasurable[(pathFiltration B).σAlg t] (fun ω =>
      s₀ * (Real.exp (c * B.Wnn (Real.toNNReal t) ω (kitDriver hd) -
        (1 / 2 : ℝ) * (c ^ 2 * t)) - 1)) :=
    ((((((measurable_W_pathFiltration B (T := t) ⟨t, ht, le_rfl⟩ (kitDriver hd)).const_mul
      c).sub_const _).exp).sub_const 1).const_mul s₀).stronglyMeasurable
  simp only [kitItoInt, hpair, ↓reduceIte]
  refine (condExp_congr_ae hraw).trans ?_
  rw [condExp_of_stronglyMeasurable ((pathFiltration B).le_ambient t) hsm (hpair.1.congr hraw)]

/-- **Doléans SDE for constant volatility** (Black–Scholes): for the `limUnder` kit with
`σ ≡ c`, `s₀ Z_t = s₀ + ∫₀ᵗ s₀ Z_s c dW_s` almost surely, for every `t ≥ 0`. -/
theorem kit_doleans_sde_const (B : MultiBrownian Ω P d) (hd : 0 < d) (c s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, s₀ * kitDoleansExp B (fun _ _ => c) t ω =
      s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B (fun _ _ => c) s ω') * c) t ω := by
  filter_upwards [kitItoInt_doleansConst_ae B hd c s₀ ht] with ω hω
  change _ = s₀ + kitItoInt B (doleansConstIntegrand B c s₀) t ω
  rw [hω, kitDoleansExp_const B hd c ht]
  ring

/-- **Doléans SDE for unit volatility** `σ ≡ 1`. -/
theorem kit_doleans_sde_one (B : MultiBrownian Ω P d) (hd : 0 < d) (s₀ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, s₀ * kitDoleansExp B (fun _ _ => 1) t ω =
      s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B (fun _ _ => 1) s ω') * 1) t ω :=
  kit_doleans_sde_const B hd 1 s₀ ht

/-- **Doléans SDE whenever `σ` is constant on `[0, T] × Ω`** (in particular for a signature
volatility `⟨ℓ, Ŵ⟩` with `ℓ` supported on the empty word): the Black–Scholes case of the kit. -/
theorem kit_doleans_sde_of_const_on {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d) (s₀ c : ℝ)
    (σ : ℝ → Ω → ℝ) (hσ : ∀ s ∈ Icc 0 T, ∀ ω, σ s ω = c) :
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  intro t ht
  have hZ : ∀ s ∈ Icc 0 T, ∀ ω,
      kitDoleansExp B σ s ω = kitDoleansExp B (fun _ _ => c) s ω := by
    intro s hs ω
    have hc : ∀ u ∈ Icc 0 s, σ u = (fun (_ : ℝ) (_ : Ω) => c) u := fun u hu =>
      funext (hσ u ⟨hu.1, hu.2.trans hs.2⟩)
    rw [kitDoleansExp_def, kitDoleansExp_def, kitItoInt_congr B hc, kitQuadVar_congr B hc]
  have hint : kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t =
      kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B (fun _ _ => c) s ω') * c) t :=
    kitItoInt_congr B fun u hu => by
      have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
      funext ω'
      rw [hZ u huT, hσ u huT]
  filter_upwards [kit_doleans_sde_const B hd c s₀ ht.1] with ω hω
  rw [hZ t ht, hint]
  exact hω

/-! ## Signature volatility: adaptedness and the quadratic-variation half of the kit -/

/-- The signature volatility `σ_t(ω) = ⟨ℓ, Ŵ_t(ω)⟩` of the Stratonovich setup over `B`. -/
noncomputable abbrev signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (ℓ : ExtTensorAlgebra (d + 1)) : ℝ → Ω → ℝ :=
  fun t ω => dualPairing ℓ ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat t ω)

/-- `σ_s = ⟨ℓ, Ŵ_s⟩` is adapted to the path filtration. -/
lemma measurable_signatureSigma_path {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (ℓ : ExtTensorAlgebra (d + 1)) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (signatureSigma B hT ℓ s.1) := by
  have hc : ∀ I : Word (d + 1), Measurable[(pathFiltration B).σAlg t]
      (fun ω => ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s.1 ω).coeff I) :=
    fun I => (prolongedBrownianSetup_stratonovich_of_brownian B hT).sig_adapted_to_W t s I
  unfold signatureSigma
  simp only [dualPairing, ExtTensorAlgebra.levelInner]
  have hn : ∀ n : ℕ, Measurable[(pathFiltration B).σAlg t] (fun ω =>
      ∑ I ∈ wordsOfLength (d + 1) n, ℓ.coeff I *
        ((prolongedBrownianSetup_stratonovich_of_brownian B hT).W_hat s.1 ω).coeff I) :=
    fun n => Finset.measurable_sum _ fun I _ => (hc I).const_mul _
  let : MeasurableSpace Ω := (pathFiltration B).σAlg t
  exact Measurable.tsum hn

/-- **Raw quadratic variation of the signature volatility, pathwise for every `ω`**: the
`limUnder` of left Riemann sums of `σ²` on the uniform grids is `∫₀ᵗ σ_s² ds` (H1–H2 give
pathwise continuity of `σ`). -/
lemma kitQuadVarRaw_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (ω : Ω) :
    kitQuadVarRaw B (signatureSigma B hT ℓ) t ω =
      ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2 := by
  have hcont : ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Icc 0 t) :=
    (continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω).mono (Icc_subset_Icc_right ht.2)
  have hlim := tendsto_lebRiemann_of_continuousOn ht.1 (hcont.pow 2)
  have hRn : ∀ n, lebRiemann_process
      (fun s ω' => forceMeasurableProcess (signatureSigma B hT ℓ) s ω' *
        forceMeasurableProcess (signatureSigma B hT ℓ) s ω') 0 t n ω =
      ∑ j ∈ Finset.range (n + 1),
        (signatureSigma B hT ℓ ((j : ℝ) * (t / ((n : ℝ) + 1))) ω) ^ 2 * (t / ((n : ℝ) + 1)) := by
    intro n
    simp only [lebRiemann_process, zero_add, sub_zero, Nat.cast_add, Nat.cast_one]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : 0 ≤ (j : ℝ) * (t / ((n : ℝ) + 1)) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg ht.1 (by positivity))
    rw [forceMeasurableProcess_eq_of_adapted B
      (measurable_signatureSigma_path B hT ℓ _ ⟨_, hj, le_rfl⟩)]
    ring
  simp only [kitQuadVarRaw, hd, ↓reduceIte, lebIntegral_process, ht.1, ↓reduceDIte]
  rw [funext hRn]
  exact hlim.limUnder_eq

/-- Under H3 the raw quadratic variation of the signature volatility is Bochner-integrable. -/
lemma integrable_kitQuadVarRaw_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (hT : 0 < T) (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (kitQuadVarRaw B (signatureSigma B hT ℓ) t) P := by
  refine Integrable.mono' (h3 1 one_pos)
    (measurable_kitQuadVarRaw B (signatureSigma B hT ℓ) t).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have hcontT := (continuousOn_sigma_of_brownian B hT w hw ℓ hℓ ω).pow 2
  rw [kitQuadVarRaw_signatureSigma B hd hT w hw ℓ hℓ ht ω, Real.norm_eq_abs,
    abs_of_nonneg (intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _), one_mul]
  calc ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2
      ≤ ∫ s in (0 : ℝ)..T, (signatureSigma B hT ℓ s ω) ^ 2 :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ fun s => sq_nonneg _) (hcontT.intervalIntegrable_of_Icc hT.le)
    _ ≤ Real.exp (∫ s in (0 : ℝ)..T, (signatureSigma B hT ℓ s ω) ^ 2) :=
        (lt_add_one _).le.trans (Real.add_one_le_exp _)

/-- **Pathwise form of the kit Doléans exponential for the signature volatility** (every `ω`):
once the raw Itô limit of `σ` is integrable, `condExp` is the identity on both raw limits and
`Z_t = exp (limUnder ∑ σ ΔW - ½ ∫₀ᵗ σ²)`. -/
lemma kitDoleansExp_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hI : Integrable (kitItoIntRaw B (signatureSigma B hT ℓ) t) P) (ω : Ω) :
    kitDoleansExp B (signatureSigma B hT ℓ) t ω =
      Real.exp (kitItoIntRaw B (signatureSigma B hT ℓ) t ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2) := by
  have hpair : kitPairIntegrable B (signatureSigma B hT ℓ) t :=
    ⟨hI, integrable_kitQuadVarRaw_signatureSigma B hd hT w hw ℓ hℓ h3 ht⟩
  have had : ∀ u, 0 ≤ u → u ≤ t →
      Measurable[(pathFiltration B).σAlg t] (signatureSigma B hT ℓ u) :=
    fun u h0 hu => measurable_signatureSigma_path B hT ℓ t ⟨u, h0, hu⟩
  rw [kitDoleansExp_def, kitItoInt_eq_raw B ht.1 had hpair, kitQuadVar_eq_raw B ht.1 had hpair,
    kitQuadVarRaw_signatureSigma B hd hT w hw ℓ hℓ ht ω]

/-! ## The Doléans SDE -/

/-- **Remaining analytic gap (single axiom).** Doléans SDE for a positive-dimensional driver and a
**non-constant** signature volatility `σ = ⟨ℓ, Ŵ⟩` (an analytic function of `(t, W_t)` for the
chordal lift) under H1–H3. The constant case (`σ ≡ c` on `[0, T] × Ω`, Black–Scholes) is
*proved* in `kit_doleans_sde_of_const_on` and excluded here. Analytic content still to be
formalized for non-constant `σ`:

1. almost-sure convergence, along the *full* sequence of uniform partitions `t·j/(n+1)`, of the
   left Itô–Riemann sums of `σ` and of `s₀ Z σ` (for constant `σ` this is
   `kitItoIntRaw_doleansConst_ae`: pathwise Föllmer–Itô + a.s. block quadratic variation; for
   `d ≥ 2` the integrand `σ(t, W_t)` is not a function of the driver coordinate alone, so
   martingale fourth-moment bounds are needed instead of a one-dimensional Föllmer formula);
2. the pathwise Itô formula for `exp` of the resulting semimartingale along those partitions;
3. Bochner integrability of the raw Itô / quadratic-variation limits of `s₀ Z σ` (moments of `Z`
   from H3), so that `kitPairIntegrable` holds and `condExp` acts as the identity. -/
theorem kit_doleans_sde_of_driver {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d) (hT : 0 < T)
    (w : Weight) (_hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (_hℓ : HypH1 w ℓ) (s₀ : ℝ) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    (¬ ∃ c : ℝ, ∀ s ∈ Icc 0 T, ∀ ω, σ s ω = c) →
    HypH3 P T σ →
    (∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    (∀ᵐ ω ∂P, ContinuousOn (fun s => σ s ω) (Icc 0 T)) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  sorry

/-- Doléans SDE for the signature volatility under H1–H3, pathwise square-integrability and
pathwise continuity of `σ`. Proved for `d = 0` and for constant `σ`; the non-constant case with a
driver is `kit_doleans_sde_of_driver`. -/
theorem kit_doleans_sde {T : ℝ} (B : MultiBrownian Ω P d) (hT : 0 < T)
    (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ) (s₀ : ℝ) :
    let setup := prolongedBrownianSetup_stratonovich_of_brownian B hT
    let σ : ℝ → Ω → ℝ := fun t ω => dualPairing ℓ (setup.W_hat t ω)
    HypH3 P T σ →
    (∀ᵐ ω ∂P, IntegrableOn (fun s => (σ s ω) ^ 2) (Icc 0 T) volume) →
    (∀ᵐ ω ∂P, ContinuousOn (fun s => σ s ω) (Icc 0 T)) →
    ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      s₀ * kitDoleansExp B σ t ω =
        s₀ + kitItoInt B (fun s ω' => (s₀ * kitDoleansExp B σ s ω') * σ s ω') t ω := by
  intro setup σ h3 hquad hcont t ht
  classical
  by_cases hd : 0 < d
  · by_cases hconst : ∃ c : ℝ, ∀ s ∈ Icc 0 T, ∀ ω, σ s ω = c
    · obtain ⟨c, hc⟩ := hconst
      exact kit_doleans_sde_of_const_on B hd s₀ c σ hc t ht
    · exact kit_doleans_sde_of_driver B hd hT w hw ℓ hℓ s₀ hconst h3 hquad hcont t ht
  · exact ae_of_all P fun ω => kit_doleans_sde_of_no_driver B hd s₀ σ t ω

end SignatureVolatility

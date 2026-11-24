module

public import SignatureVolatility.ItoCalculusKit
public import SignatureVolatility.ItoCalculusKit.FrozenIncrement4
public import SignatureVolatility.ItoCalculusKit.DoleansEnvelope

@[expose] public section

open MeasureTheory Filter Topology Set


namespace SignatureVolatility

/-!
# Strong solutions: the kit integral is the raw Riemann limit

For an adapted `L⁴`-Hölder integrand the integrability gate of `kitItoInt` is open (the raw
quadratic variation is integrable by Fatou, with the `limUnder` junk value on non-convergent
paths), so `kitItoInt = kitItoIntRaw`. The raw integral is linear a.s. Consequently the
difference `D = S₁ - S₂` of two kit strong solutions is `D_t = ∫₀ᵗ D σ dW` (raw) a.s.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma HolderAdapted.sub {B : MultiBrownian Ω P d} {H₁ H₂ : ℝ → Ω → ℝ} {t K₁ K₂ : ℝ}
    (h₁ : HolderAdapted B H₁ t K₁) (h₂ : HolderAdapted B H₂ t K₂) :
    HolderAdapted B (fun s ω => H₁ s ω - H₂ s ω) t (8 * K₁ + 8 * K₂) := by
  refine ⟨by linarith [h₁.K_nonneg, h₂.K_nonneg],
    fun u h0 hu => (h₁.meas u h0 hu).sub (h₂.meas u h0 hu),
    fun u h0 hu => (h₁.memLp u h0 hu).sub (h₂.memLp u h0 hu), fun u v h0 huv hv => ?_⟩
  have hu' : u ≤ t := huv.trans hv
  have hv0 : 0 ≤ v := h0.trans huv
  have i1 : Integrable (fun ω => (H₁ v ω - H₁ u ω) ^ 4) P :=
    integrable_pow_of_memLp_four ((h₁.memLp v hv0 hv).sub (h₁.memLp u h0 hu'))
    (k := 4) le_rfl
  have i2 : Integrable (fun ω => (H₂ v ω - H₂ u ω) ^ 4) P :=
    integrable_pow_of_memLp_four ((h₂.memLp v hv0 hv).sub (h₂.memLp u h0 hu'))
    (k := 4) le_rfl
  have ia : Integrable (fun ω => ((H₁ v ω - H₂ v ω) - (H₁ u ω - H₂ u ω)) ^ 4) P :=
    integrable_pow_of_memLp_four
    (((h₁.memLp v hv0 hv).sub (h₂.memLp v hv0 hv)).sub ((h₁.memLp u h0 hu').sub
      (h₂.memLp u h0 hu'))) (k := 4) le_rfl
  have hh1 := h₁.holder u v h0 huv hv
  have hh2 := h₂.holder u v h0 huv hv
  calc ∫ ω, ((H₁ v ω - H₂ v ω) - (H₁ u ω - H₂ u ω)) ^ 4 ∂P
      ≤ ∫ ω, (8 * (H₁ v ω - H₁ u ω) ^ 4 + 8 * (H₂ v ω - H₂ u ω) ^ 4) ∂P := by
        refine integral_mono ia ((i1.const_mul 8).add (i2.const_mul 8)) fun ω => ?_
        have h := add_pow_four_le_frozen (H₁ v ω - H₁ u ω) (-(H₂ v ω - H₂ u ω))
        have e : (H₁ v ω - H₂ v ω) - (H₁ u ω - H₂ u ω) =
            (H₁ v ω - H₁ u ω) + -(H₂ v ω - H₂ u ω) := by ring
        have e4 : (-(H₂ v ω - H₂ u ω)) ^ 4 = (H₂ v ω - H₂ u ω) ^ 4 := by ring
        show ((H₁ v ω - H₂ v ω) - (H₁ u ω - H₂ u ω)) ^ 4 ≤ _
        rw [e]
        linarith
    _ = 8 * ∫ ω, (H₁ v ω - H₁ u ω) ^ 4 ∂P + 8 * ∫ ω, (H₂ v ω - H₂ u ω) ^ 4 ∂P := by
        rw [integral_add (i1.const_mul 8) (i2.const_mul 8), integral_const_mul,
          integral_const_mul]
    _ ≤ (8 * K₁ + 8 * K₂) * (v - u) ^ 2 := by linarith

section StoppedRaw

variable (B : MultiBrownian Ω P d)

/-- **Integrability gate, quadratic-variation half**, for adapted `L⁴`-Hölder integrands:
Fatou on the nonnegative Riemann sums of `H²`, plus the junk value where they diverge. -/
theorem integrable_kitQuadVarRaw_of_holderAdapted (hd : 0 < d) {H : ℝ → Ω → ℝ} {t K : ℝ}
    (ht : 0 ≤ t) (hH : HolderAdapted B H t K) : Integrable (kitQuadVarRaw B H t) P := by
  set R : ℕ → Ω → ℝ := fun n ω => lebRiemann_process
      (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω') 0 t n ω
    with hR
  have hL : ∀ ω, kitQuadVarRaw B H t ω = limUnder atTop fun n => R n ω := by
    intro ω
    simp only [kitQuadVarRaw, hd, ↓reduceIte, lebIntegral_process, ht, ↓reduceDIte, hR]
  have hgrid : ∀ n : ℕ, ∀ k ∈ Finset.range (n + 1),
      0 ≤ (k : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) ∧ (k : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) ≤ t :=
    fun n k hk => unifGrid_mem ht n.succ_pos (Finset.mem_range.mp hk).le
  have hRe : ∀ n ω, R n ω = ∑ k ∈ Finset.range (n + 1),
      H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω * H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω *
        (t / ((n + 1 : ℕ) : ℝ)) := by
    intro n ω
    simp only [hR, lebRiemann_process, zero_add, sub_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h0, h1⟩ := hgrid n k hk
    rw [forceMeasurableProcess_eq_of_adapted B (hH.meas _ h0 h1)]
  have hΔ : ∀ n : ℕ, 0 ≤ t / ((n + 1 : ℕ) : ℝ) := fun n => div_nonneg ht (by positivity)
  have hR0 : ∀ n ω, 0 ≤ R n ω := fun n ω => by
    rw [hRe]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (mul_self_nonneg _) (hΔ n)
  have hRm : ∀ n, Measurable (R n) := fun n =>
    measurable_lebRiemann_process _ (fun u => (measurable_forceMeasurableProcess H u).mul
      (measurable_forceMeasurableProcess H u)) 0 t n
  set M : ℝ := 1 + (8 * ∫ ω, H 0 ω ^ 4 ∂P + 8 * K * t ^ 2) with hM
  have hsq : ∀ u, 0 ≤ u → u ≤ t → Integrable (fun ω => H u ω * H u ω) P ∧
      ∫ ω, H u ω * H u ω ∂P ≤ M := by
    intro u h0 h1
    have hL4 := hH.memLp u h0 h1
    have hL2 : MemLp (H u) 2 P := hL4.mono_exponent (by norm_num)
    have hi := integrable_mul_of_memLp_two hL2 hL2
    have h4 := integrable_pow_of_memLp_four hL4 (k := 4) le_rfl
    refine ⟨hi, ?_⟩
    calc ∫ ω, H u ω * H u ω ∂P ≤ ∫ ω, (1 + H u ω ^ 4) ∂P :=
          integral_mono hi ((integrable_const 1).add h4) fun ω => by
            nlinarith [sq_nonneg (H u ω ^ 2 - 1), sq_nonneg (H u ω)]
      _ = 1 + ∫ ω, H u ω ^ 4 ∂P := by
          rw [integral_add (integrable_const 1) h4]; simp
      _ ≤ M := by
          have := integral_pow_four_le_of_holderAdapted B hH h0 h1
          rw [hM]; linarith
  have hRi : ∀ n, Integrable (R n) P := fun n => by
    have : R n = fun ω => ∑ k ∈ Finset.range (n + 1),
      H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω * H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω *
        (t / ((n + 1 : ℕ) : ℝ)) := funext (hRe n)
    rw [this]
    exact integrable_finsetSum _ fun k hk =>
      (hsq _ (hgrid n k hk).1 (hgrid n k hk).2).1.mul_const _
  have hRC : ∀ n, ∫ ω, R n ω ∂P ≤ M * t := fun n => by
    have : R n = fun ω => ∑ k ∈ Finset.range (n + 1),
      H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω * H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω *
        (t / ((n + 1 : ℕ) : ℝ)) := funext (hRe n)
    rw [this, integral_finsetSum _ fun k hk =>
      (hsq _ (hgrid n k hk).1 (hgrid n k hk).2).1.mul_const _]
    calc ∑ k ∈ Finset.range (n + 1), ∫ ω, H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω *
            H ((k : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω * (t / ((n + 1 : ℕ) : ℝ)) ∂P
        ≤ ∑ _k ∈ Finset.range (n + 1), M * (t / ((n + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [integral_mul_const]
          exact mul_le_mul_of_nonneg_right
            (hsq _ (hgrid n k hk).1 (hgrid n k hk).2).2 (hΔ n)
      _ = M * t := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp
  have hpt : ∀ ω, ‖kitQuadVarRaw B H t ω‖ₑ ≤
      ‖junkReal‖ₑ + liminf (fun n => ENNReal.ofReal (R n ω)) atTop := by
    intro ω
    rw [hL ω]
    by_cases hc : ∃ x, Tendsto (fun n => R n ω) atTop (𝓝 x)
    · obtain ⟨x, hx⟩ := hc
      rw [hx.limUnder_eq]
      have hx0 : 0 ≤ x := ge_of_tendsto' hx fun n => hR0 n ω
      have hlim := ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq
      rw [Real.enorm_eq_ofReal hx0, show (fun n => ENNReal.ofReal (R n ω)) =
        ENNReal.ofReal ∘ fun n => R n ω from rfl, hlim]
      exact le_add_self
    · rw [limUnder_eq_junkReal hc]
      exact le_self_add
  refine ⟨(measurable_kitQuadVarRaw B H t).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  refine ENNReal.add_lt_top.2 ⟨enorm_lt_top, ?_⟩
  refine lt_of_le_of_lt (lintegral_liminf_le fun n => (hRm n).ennreal_ofReal) ?_
  refine lt_of_le_of_lt (liminf_le_of_le (by isBoundedDefault) fun b hb => ?_)
    (ENNReal.ofReal_lt_top (r := M * t))
  obtain ⟨n, hn⟩ := hb.exists
  refine hn.trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hRi n) (ae_of_all _ (hR0 n))]
  exact ENNReal.ofReal_le_ofReal (hRC n)

/-- For adapted `L⁴`-Hölder integrands, `kitItoInt` **is** the raw Riemann limit. -/
theorem kitItoInt_eq_raw_of_holderAdapted (hd : 0 < d) {H : ℝ → Ω → ℝ} {t K : ℝ}
    (ht : 0 ≤ t) (hH : HolderAdapted B H t K) : kitItoInt B H t = kitItoIntRaw B H t :=
  kitItoInt_eq_raw B ht
    (fun u h0 hu => (hH.meas u h0 hu).mono ((pathFiltration B).mono hu) le_rfl)
    ⟨(kitItoIntRaw_of_holderAdapted B hd ht hH).2.2,
      integrable_kitQuadVarRaw_of_holderAdapted B hd ht hH⟩

lemma unifRiemann_sub (k : Fin d) (H₁ H₂ : ℝ → Ω → ℝ) (t : ℝ) (N : ℕ) (ω : Ω) :
    unifRiemann B k (fun s ω => H₁ s ω - H₂ s ω) t N ω =
      unifRiemann B k H₁ t N ω - unifRiemann B k H₂ t N ω := by
  simp only [unifRiemann, ← Finset.sum_sub_distrib, sub_mul]

/-- **Linearity of the raw integral** on adapted `L⁴`-Hölder integrands (a.s.). -/
theorem kitItoIntRaw_sub_ae (hd : 0 < d) {H₁ H₂ : ℝ → Ω → ℝ} {t K₁ K₂ : ℝ} (ht : 0 ≤ t)
    (h₁ : HolderAdapted B H₁ t K₁) (h₂ : HolderAdapted B H₂ t K₂) :
    kitItoIntRaw B (fun s ω => H₁ s ω - H₂ s ω) t =ᵐ[P]
      fun ω => kitItoIntRaw B H₁ t ω - kitItoIntRaw B H₂ t ω := by
  filter_upwards [(kitItoIntRaw_of_holderAdapted B hd ht (h₁.sub h₂)).1,
    (kitItoIntRaw_of_holderAdapted B hd ht h₁).1,
    (kitItoIntRaw_of_holderAdapted B hd ht h₂).1] with ω h h1 h2
  refine tendsto_nhds_unique h ?_
  simp only [unifRiemann_sub]
  exact h1.sub h2

/-- A kit strong solution adapted to the signature filtration has an adapted `L⁴`-Hölder
integrand `S σ`. -/
theorem holderAdapted_of_strongClass {T : ℝ} (hT : 0 < T) {ℓ : ExtTensorAlgebra (d + 1)}
    {S : ℝ → Ω → ℝ}
    (hadapt : ∀ t ∈ Icc 0 T, Measurable[(prolongedBrownianSetup_stratonovich_of_brownian
      B hT).signatureFiltration.σAlg t] (S t))
    (hcl : KitStrongSolutionClass P T (signatureSigma B hT ℓ) S) :
    ∃ K, HolderAdapted B (fun s ω => S s ω * signatureSigma B hT ℓ s ω) T K := by
  obtain ⟨-, K, hK, hLp, hhol⟩ := hcl
  refine ⟨K, hK, fun u h0 hu => ?_, fun u h0 hu => hLp u ⟨h0, hu⟩, hhol⟩
  have h1 := hadapt u ⟨h0, hu⟩
  rw [signature_filtration_eq_brownian_filtration
    (prolongedBrownianSetup_stratonovich_of_brownian B hT) u,
    ← pathFiltration_eq_brownianFiltration B hT] at h1
  exact h1.mul (measurable_signatureSigma_path B hT ℓ u ⟨u, h0, le_rfl⟩)

/-- **The difference of two kit strong solutions is the raw integral of `D σ`.** -/
theorem stopped_diff_eq_raw (hd : 0 < d) {T : ℝ} (hT : 0 < T) {ℓ : ExtTensorAlgebra (d + 1)}
    {s₀ : ℝ} {S₁ S₂ : ℝ → Ω → ℝ}
    (hadapt₁ : ∀ t ∈ Icc 0 T, Measurable[(prolongedBrownianSetup_stratonovich_of_brownian
      B hT).signatureFiltration.σAlg t] (S₁ t))
    (hadapt₂ : ∀ t ∈ Icc 0 T, Measurable[(prolongedBrownianSetup_stratonovich_of_brownian
      B hT).signatureFiltration.σAlg t] (S₂ t))
    (hcl₁ : KitStrongSolutionClass P T (signatureSigma B hT ℓ) S₁)
    (hcl₂ : KitStrongSolutionClass P T (signatureSigma B hT ℓ) S₂)
    (heq₁ : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₁ t ω = s₀ + kitItoInt B (fun s ω' => S₁ s ω' * signatureSigma B hT ℓ s ω') t ω)
    (heq₂ : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂P,
      S₂ t ω = s₀ + kitItoInt B (fun s ω' => S₂ s ω' * signatureSigma B hT ℓ s ω') t ω) :
    ∃ K, HolderAdapted B (fun s ω => (S₁ s ω - S₂ s ω) * signatureSigma B hT ℓ s ω) T K ∧
      ∀ t ∈ Icc 0 T, (fun ω => S₁ t ω - S₂ t ω) =ᵐ[P]
        kitItoIntRaw B (fun s ω => (S₁ s ω - S₂ s ω) * signatureSigma B hT ℓ s ω) t := by
  obtain ⟨K₁, h₁⟩ := holderAdapted_of_strongClass B hT hadapt₁ hcl₁
  obtain ⟨K₂, h₂⟩ := holderAdapted_of_strongClass B hT hadapt₂ hcl₂
  have e : (fun s ω => (S₁ s ω - S₂ s ω) * signatureSigma B hT ℓ s ω) =
      fun s ω => S₁ s ω * signatureSigma B hT ℓ s ω - S₂ s ω * signatureSigma B hT ℓ s ω := by
    funext s ω; ring
  refine ⟨8 * K₁ + 8 * K₂, e ▸ h₁.sub h₂, fun t ht => ?_⟩
  filter_upwards [heq₁ t ht, heq₂ t ht,
    kitItoIntRaw_sub_ae B hd ht.1 (h₁.mono ht.2) (h₂.mono ht.2)] with ω e1 e2 e3
  rw [kitItoInt_eq_raw_of_holderAdapted B hd ht.1 (h₁.mono ht.2)] at e1
  rw [kitItoInt_eq_raw_of_holderAdapted B hd ht.1 (h₂.mono ht.2)] at e2
  rw [e, e3]
  linarith

end StoppedRaw

end SignatureVolatility

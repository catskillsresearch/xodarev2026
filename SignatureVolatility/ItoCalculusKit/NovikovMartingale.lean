module

public import SignatureVolatility.ItoCalculusKit.DoleansQV
public import SignatureVolatility.ItoCalculusKit.LogDoleansIncrement

@[expose] public section

open MeasureTheory

namespace SignatureVolatility

/-!
# The Doléans exponential of the signature volatility is a martingale

Under H1–H3, `H = Z σ` is Hölder-adapted on `[0, T]` (`holderAdapted_kitDoleansExp_mul`), so its
raw Itô integral is a martingale (`condExp_kitItoIntRaw`); with `Z_t = 1 + ∫₀ᵗ Z σ dW`
(`kitItoIntRaw_doleans_ae`) this gives the martingale property of `Z`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp b - Real.exp a| ≤ |b - a| * (Real.exp a + Real.exp b) := by
  have key : ∀ x y : ℝ, x ≤ y → Real.exp y - Real.exp x ≤ (y - x) * Real.exp y := by
    intro x y hxy
    have h1 := Real.add_one_le_exp (x - y)
    have h2 : Real.exp (x - y) * Real.exp y = Real.exp x := by rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos y]
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)), abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith [key a b h, Real.exp_pos a, Real.exp_pos b]
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)), abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith [key b a h, Real.exp_pos a, Real.exp_pos b]

lemma HolderAdapted.const_mul {B : MultiBrownian Ω P d} {H : ℝ → Ω → ℝ} {t K : ℝ}
    (hH : HolderAdapted B H t K) (c : ℝ) :
    HolderAdapted B (fun s ω => c * H s ω) t (c ^ 4 * K) := by
  refine ⟨mul_nonneg (by positivity) hH.K_nonneg, fun u h0 hu => (hH.meas u h0 hu).const_mul c,
    fun u h0 hu => (hH.memLp u h0 hu).const_mul c, fun u v h0 huv hv => ?_⟩
  calc ∫ ω, (c * H v ω - c * H u ω) ^ 4 ∂P = c ^ 4 * ∫ ω, (H v ω - H u ω) ^ 4 ∂P := by
        rw [← integral_const_mul]; congr 1; funext ω; ring
    _ ≤ c ^ 4 * (K * (v - u) ^ 2) := by gcongr; exact hH.holder u v h0 huv hv
    _ = _ := by ring

omit [IsProbabilityMeasure P] in
lemma integrable_pow_of_memLp_even {f : Ω → ℝ} {p : ℕ} (hp : p ≠ 0) (he : Even p)
    (hf : MemLp f p P) : Integrable (fun ω => f ω ^ p) P :=
  (hf.integrable_norm_pow hp).congr (ae_of_all _ fun ω => by
    simp only [Real.norm_eq_abs, he.pow_abs])

omit [IsProbabilityMeasure P] in
lemma integral_mul_pow_four_le_sqrt {f g : Ω → ℝ} (hf : MemLp (fun ω => f ω ^ 4) 2 P)
    (hg : MemLp (fun ω => g ω ^ 4) 2 P) :
    ∫ ω, f ω ^ 4 * g ω ^ 4 ∂P ≤
      Real.sqrt (∫ ω, f ω ^ 8 ∂P) * Real.sqrt (∫ ω, g ω ^ 8 ∂P) := by
  have h := abs_integral_mul_le_sqrt hf hg
  have e1 : ∫ ω, (f ω ^ 4) ^ 2 ∂P = ∫ ω, f ω ^ 8 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only; ring)
  have e2 : ∫ ω, (g ω ^ 4) ^ 2 ∂P = ∫ ω, g ω ^ 8 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only; ring)
  rw [e1, e2] at h
  exact (le_abs_self _).trans h

lemma sqrt_mul_pow_four {K h : ℝ} (hK : 0 ≤ K) : Real.sqrt (K * h ^ 4) = Real.sqrt K * h ^ 2 := by
  rw [Real.sqrt_mul hK, show h ^ 4 = (h ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]

section Mart

variable {T : ℝ} (B : MultiBrownian Ω P d)

/-- **Uniform `Lᵖ` moments of the Doléans exponential** on `[0, T]` (H1–H3). -/
theorem exists_integral_kitDoleansExp_pow_le (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 T, MemLp (kitDoleansExp B (signatureSigma B hT ℓ) s) p P ∧
      ∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ p ∂P ≤ C := by
  set R : ℝ := ∫ ω, Real.exp ((2 * (p : ℝ) ^ 2 - p) *
    ∫ s in (0 : ℝ)..T, (signatureSigma B hT ℓ s ω) ^ 2) ∂P with hR
  have hR0 : 0 ≤ R := integral_nonneg fun ω => (Real.exp_pos _).le
  refine ⟨1 + R, by linarith, fun s hs => ?_⟩
  have hL := memLp_kitDoleansExp_signatureSigma B hd hT w hw ℓ hℓ h3 hs p hp
  refine ⟨hL, ?_⟩
  have hint : Integrable (fun ω => kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ p) P := by
    have := hL.integrable_norm_pow (by omega)
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_pos (show (0:ℝ) < kitDoleansExp B (signatureSigma B hT ℓ) s ω from Real.exp_pos _)]
  have hlin := lintegral_exp_mul_signatureSigma_le B hd hT hw hℓ h3 hs (p := p)
    (by exact_mod_cast hp)
  have hpt : ∀ᵐ ω ∂P, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ p =
      Real.exp (p * (kitItoIntRaw B (signatureSigma B hT ℓ) s ω -
        (1 / 2 : ℝ) * ∫ u in (0 : ℝ)..s, (signatureSigma B hT ℓ u ω) ^ 2)) := by
    filter_upwards [ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ] with ω hω
    rw [kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 hs hω, ← Real.exp_nat_mul]
  have h1 : ENNReal.ofReal (∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ p ∂P) =
      ∫⁻ ω, ENNReal.ofReal (kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ p) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by
      simp only [Pi.zero_apply]; exact pow_nonneg (Real.exp_pos _).le _)
  have h2 : ENNReal.ofReal (∫ ω, kitDoleansExp B (signatureSigma B hT ℓ) s ω ^ p ∂P) ≤
      ENNReal.ofReal (1 + R) := by
    rw [h1, ENNReal.ofReal_add zero_le_one hR0, ENNReal.ofReal_one]
    rw [lintegral_congr_ae (hpt.mono fun ω h => by rw [h])]
    exact hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h2

lemma add_pow_four_le' (a b : ℝ) : (a + b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  nlinarith [sq_nonneg ((a - b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b),
    sq_nonneg (a - b)]

/-- **`Z σ` is Hölder-adapted on `[0, T]`** (H1–H3): `𝔼 (Z_v σ_v - Z_u σ_u)⁴ ≤ K (v - u)²`. -/
theorem holderAdapted_kitDoleansExp_mul (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) :
    ∃ K, HolderAdapted B (fun s ω => kitDoleansExp B (signatureSigma B hT ℓ) s ω *
      signatureSigma B hT ℓ s ω) T K := by
  obtain ⟨Cz8, hCz80, hCz8⟩ := exists_integral_kitDoleansExp_pow_le B hd hT hw hℓ h3 8 (by norm_num)
  obtain ⟨Cz16, hCz160, hCz16⟩ :=
    exists_integral_kitDoleansExp_pow_le B hd hT hw hℓ h3 16 (by norm_num)
  obtain ⟨Cσ, hCσ0, hCσ⟩ := exists_integral_signatureSigma_pow_sixteen_le B hT hw hℓ
  obtain ⟨K8, hH8⟩ := holderAdapted8_signatureSigma B hT hw hℓ T
  obtain ⟨KL, hKL0, hKL⟩ := integral_logDoleans_incr_pow_eight_le (B := B) (hT := hT) (ℓ := ℓ)
    hd hw hℓ
  have hZX : ∀ s ∈ Set.Icc 0 T, ∀ ω,
      ContinuousOn (fun s => signatureSigma B hT ℓ s ω) (Set.Icc 0 T) →
      kitDoleansExp B (signatureSigma B hT ℓ) s ω =
      Real.exp (logDoleans B hT ℓ s ω) := fun s hs _ hω =>
    kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 hs hω
  set σ := signatureSigma B hT ℓ with hσ
  set Z := kitDoleansExp B σ with hZ
  set C2 : ℝ := (2 ^ 15 * (Cz16 + Cz16) + Cσ) / 2 with hC2
  have hK80 := hH8.K_nonneg
  refine ⟨8 * Real.sqrt KL * Real.sqrt C2 + 8 * Real.sqrt Cz8 * Real.sqrt K8, ?_⟩
  have hσm : ∀ s ∈ Set.Icc 0 T, Measurable (σ s) := fun s hs =>
    (hH8.meas s hs.1 hs.2).mono ((pathFiltration B).le_ambient _) le_rfl
  have hZm : ∀ s, Measurable (Z s) := fun s => measurable_kitDoleansExp B σ s
  refine ⟨by positivity, fun u h0 hu => ?_, fun u h0 hu => ?_, fun u v h0 huv hv => ?_⟩
  · exact (kitDoleansExp_adapted_path B σ u ⟨u, h0, le_rfl⟩).mul (hH8.meas u h0 hu)
  · exact memLp_mul_four_of_eight (hCz8 u ⟨h0, hu⟩).1 (hH8.memLp u h0 hu)
  have huT : u ∈ Set.Icc 0 T := ⟨h0, huv.trans hv⟩
  have hvT : v ∈ Set.Icc 0 T := ⟨h0.trans huv, hv⟩
  -- the pieces
  set x : Ω → ℝ := fun ω => Real.log (Z v ω) - Real.log (Z u ω) with hx
  have hxeq : ∀ᵐ ω ∂P, x ω = logDoleans B hT ℓ v ω - logDoleans B hT ℓ u ω :=
    (ae_continuousOn_sigma_of_brownian B hT w hw ℓ hℓ).mono fun ω hω => by
      simp only [hx]; rw [hZX v hvT ω hω, hZX u huT ω hω, Real.log_exp, Real.log_exp]
  have hxm : Measurable x :=
    (Real.measurable_log.comp (hZm v)).sub (Real.measurable_log.comp (hZm u))
  obtain ⟨hx8i, hx8b⟩ := hKL u v h0 huv hv
  have hx8i' : Integrable (fun ω => x ω ^ 8) P :=
    hx8i.congr (hxeq.mono fun ω h => by simp only; rw [h])
  have hx8b' : ∫ ω, x ω ^ 8 ∂P ≤ KL * (v - u) ^ 4 := by
    have e : ∫ ω, x ω ^ 8 ∂P =
        ∫ ω, (logDoleans B hT ℓ v ω - logDoleans B hT ℓ u ω) ^ 8 ∂P :=
      integral_congr_ae (hxeq.mono fun ω h => by simp only [h])
    rw [e]; exact hx8b
  have hx4 : MemLp (fun ω => x ω ^ 4) 2 P :=
    memLp_pow_four_two (memLp_eight_of_integrable_pow_eight hxm.aestronglyMeasurable hx8i')
  set W : Ω → ℝ := fun ω => (Z u ω + Z v ω) * σ v ω with hW
  have hWm : Measurable W := ((hZm u).add (hZm v)).mul (hσm v hvT)
  have hZ0 : ∀ s ∈ Set.Icc 0 T, ∀ ω, 0 ≤ Z s ω := fun s hs ω => by
    exact (Real.exp_pos _).le
  have hZ16 : ∀ s ∈ Set.Icc 0 T, Integrable (fun ω => Z s ω ^ 16) P := fun s hs =>
    integrable_pow_of_memLp_even (by norm_num) ⟨8, rfl⟩ (hCz16 s hs).1
  have hσ16 := (hCσ v hvT).1
  set D2 : Ω → ℝ := fun ω => (2 ^ 15 * (Z u ω ^ 16 + Z v ω ^ 16) + σ v ω ^ 16) / 2 with hD2
  have hD2i : Integrable D2 P :=
    ((((hZ16 u huT).add (hZ16 v hvT)).const_mul (2 ^ 15)).add hσ16).div_const 2
  have hW8le : ∀ ω, W ω ^ 8 ≤ D2 ω := by
    intro ω
    have h1 : W ω ^ 8 ≤ (((Z u ω + Z v ω) ^ 8) ^ 2 + (σ v ω ^ 8) ^ 2) / 2 := by
      simp only [hW]
      nlinarith [sq_nonneg ((Z u ω + Z v ω) ^ 8 - σ v ω ^ 8)]
    have h2 := add_pow_le (hZ0 u huT ω) (hZ0 v hvT ω) 16
    simp only [hD2]
    have h3 : ((Z u ω + Z v ω) ^ 8) ^ 2 = (Z u ω + Z v ω) ^ 16 := by ring
    have h4 : (σ v ω ^ 8) ^ 2 = σ v ω ^ 16 := by ring
    rw [h3, h4] at h1
    norm_num at h2
    linarith
  have hW8 : Integrable (fun ω => W ω ^ 8) P :=
    hD2i.mono' (hWm.pow_const 8).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hW8le ω)
  have hW8b : ∫ ω, W ω ^ 8 ∂P ≤ C2 := by
    refine (integral_mono hW8 hD2i hW8le).trans ?_
    simp only [hD2]
    have hA : Integrable (fun ω => Z u ω ^ 16 + Z v ω ^ 16) P := (hZ16 u huT).add (hZ16 v hvT)
    have hA' : Integrable (fun ω => 2 ^ 15 * (Z u ω ^ 16 + Z v ω ^ 16)) P := hA.const_mul _
    have hu16 : Integrable (fun ω => Z u ω ^ 16) P := hZ16 u huT
    have hv16 : Integrable (fun ω => Z v ω ^ 16) P := hZ16 v hvT
    rw [integral_div, integral_add hA' hσ16, integral_const_mul, integral_add hu16 hv16]
    have := (hCz16 u huT).2
    have := (hCz16 v hvT).2
    have := (hCσ v hvT).2
    rw [hC2]
    gcongr
  have hW4 : MemLp (fun ω => W ω ^ 4) 2 P :=
    memLp_pow_four_two (memLp_eight_of_integrable_pow_eight hWm.aestronglyMeasurable hW8)
  have hZu4 : MemLp (fun ω => Z u ω ^ 4) 2 P := memLp_pow_four_two (hCz8 u huT).1
  have hb8 : MemLp (fun ω => σ v ω - σ u ω) 8 P :=
    (hH8.memLp v (h0.trans huv) hv).sub (hH8.memLp u h0 (huv.trans hv))
  have hb4 : MemLp (fun ω => (σ v ω - σ u ω) ^ 4) 2 P := memLp_pow_four_two hb8
  have hI1 := integrable_mul_of_memLp_two hx4 hW4
  have hI2 := integrable_mul_of_memLp_two hZu4 hb4
  have hLHS : Integrable (fun ω => (Z v ω * σ v ω - Z u ω * σ u ω) ^ 4) P :=
    integrable_pow_of_memLp_four ((memLp_mul_four_of_eight (hCz8 v hvT).1
      (hH8.memLp v (h0.trans huv) hv)).sub (memLp_mul_four_of_eight (hCz8 u huT).1
      (hH8.memLp u h0 (huv.trans hv)))) le_rfl
  have hpt : ∀ ω, (Z v ω * σ v ω - Z u ω * σ u ω) ^ 4 ≤
      8 * (x ω ^ 4 * W ω ^ 4) + 8 * (Z u ω ^ 4 * (σ v ω - σ u ω) ^ 4) := by
    intro ω
    have ha : |Z v ω - Z u ω| ≤ |x ω| * (Z u ω + Z v ω) := by
      have hpu : 0 < Z u ω := Real.exp_pos _
      have hpv : 0 < Z v ω := Real.exp_pos _
      have := abs_exp_sub_exp_le (Real.log (Z u ω)) (Real.log (Z v ω))
      rwa [Real.exp_log hpu, Real.exp_log hpv] at this
    have he : Even 4 := ⟨2, rfl⟩
    have ha4 : (Z v ω - Z u ω) ^ 4 ≤ x ω ^ 4 * (Z u ω + Z v ω) ^ 4 := by
      calc (Z v ω - Z u ω) ^ 4 = |Z v ω - Z u ω| ^ 4 := (he.pow_abs _).symm
        _ ≤ (|x ω| * (Z u ω + Z v ω)) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) ha 4
        _ = _ := by rw [mul_pow, he.pow_abs]
    have hsplit : Z v ω * σ v ω - Z u ω * σ u ω =
        (Z v ω - Z u ω) * σ v ω + Z u ω * (σ v ω - σ u ω) := by ring
    rw [hsplit]
    refine (add_pow_four_le' _ _).trans ?_
    have h1 : ((Z v ω - Z u ω) * σ v ω) ^ 4 ≤ x ω ^ 4 * W ω ^ 4 := by
      rw [mul_pow]
      calc (Z v ω - Z u ω) ^ 4 * σ v ω ^ 4 ≤ x ω ^ 4 * (Z u ω + Z v ω) ^ 4 * σ v ω ^ 4 :=
            mul_le_mul_of_nonneg_right ha4 (by positivity)
        _ = _ := by simp only [hW]; ring
    have h2 : (Z u ω * (σ v ω - σ u ω)) ^ 4 = Z u ω ^ 4 * (σ v ω - σ u ω) ^ 4 := by ring
    linarith
  have hD : Integrable (fun ω => 8 * (x ω ^ 4 * W ω ^ 4) + 8 * (Z u ω ^ 4 *
      (σ v ω - σ u ω) ^ 4)) P := (hI1.const_mul 8).add (hI2.const_mul 8)
  calc ∫ ω, (Z v ω * σ v ω - Z u ω * σ u ω) ^ 4 ∂P
      ≤ ∫ ω, 8 * (x ω ^ 4 * W ω ^ 4) + 8 * (Z u ω ^ 4 * (σ v ω - σ u ω) ^ 4) ∂P :=
        integral_mono hLHS hD hpt
    _ = 8 * ∫ ω, x ω ^ 4 * W ω ^ 4 ∂P + 8 * ∫ ω, Z u ω ^ 4 * (σ v ω - σ u ω) ^ 4 ∂P := by
        rw [integral_add (hI1.const_mul 8) (hI2.const_mul 8), integral_const_mul,
          integral_const_mul]
    _ ≤ 8 * (Real.sqrt (∫ ω, x ω ^ 8 ∂P) * Real.sqrt (∫ ω, W ω ^ 8 ∂P)) +
        8 * (Real.sqrt (∫ ω, Z u ω ^ 8 ∂P) * Real.sqrt (∫ ω, (σ v ω - σ u ω) ^ 8 ∂P)) := by
        gcongr
        · exact integral_mul_pow_four_le_sqrt hx4 hW4
        · exact integral_mul_pow_four_le_sqrt hZu4 hb4
    _ ≤ 8 * (Real.sqrt (KL * (v - u) ^ 4) * Real.sqrt C2) +
        8 * (Real.sqrt Cz8 * Real.sqrt (K8 * (v - u) ^ 4)) := by
        gcongr
        · exact (hCz8 u huT).2
        · exact hH8.holder u v h0 huv hv
    _ = _ := by
        rw [sqrt_mul_pow_four hKL0, sqrt_mul_pow_four hK80]
        ring

/-- **Martingale property of the Doléans price** `s₀ Z` on the path filtration (H1–H3). -/
theorem condExp_kitDoleansExp_signatureSigma (hd : 0 < d) (hT : 0 < T) {w : Weight}
    (hw : HypH2 w) {ℓ : ExtTensorAlgebra (d + 1)} (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) (s₀ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) :
    Integrable (fun ω => s₀ * kitDoleansExp B (signatureSigma B hT ℓ) t ω) P ∧
      P[fun ω => s₀ * kitDoleansExp B (signatureSigma B hT ℓ) t ω |
        (pathFiltration B).σAlg s] =ᵐ[P]
        fun ω => s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω := by
  have htI : t ∈ Set.Icc 0 T := ⟨hs.trans hst, htT⟩
  have hsI : s ∈ Set.Icc 0 T := ⟨hs, hst.trans htT⟩
  obtain ⟨K, hH⟩ := holderAdapted_kitDoleansExp_mul B hd hT hw hℓ h3
  have hH' := hH.const_mul s₀
  have hfun : (fun s ω => s₀ * (kitDoleansExp B (signatureSigma B hT ℓ) s ω *
      signatureSigma B hT ℓ s ω)) = (fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
        signatureSigma B hT ℓ s ω') := by
    funext s ω; ring
  rw [hfun] at hH'
  have hJt := kitItoIntRaw_doleans_ae B hd hT hw hℓ h3 htI s₀
  have hJs := kitItoIntRaw_doleans_ae B hd hT hw hℓ h3 hsI s₀
  have hJi := integrable_kitItoIntRaw_doleans B hd hT hw hℓ h3 htI s₀
  have hce := condExp_kitItoIntRaw B hd hH' hs hst htT
  set J := kitItoIntRaw B (fun s ω' => (s₀ * kitDoleansExp B (signatureSigma B hT ℓ) s ω') *
    signatureSigma B hT ℓ s ω') with hJ
  have hZi : Integrable (kitDoleansExp B (signatureSigma B hT ℓ) t) P := by
    have := memLp_kitDoleansExp_signatureSigma B hd hT w hw ℓ hℓ h3 htI 1 le_rfl
    exact memLp_one_iff_integrable.mp (by exact_mod_cast this)
  refine ⟨hZi.const_mul s₀, ?_⟩
  have h1 : (fun ω => s₀ * kitDoleansExp B (signatureSigma B hT ℓ) t ω) =ᵐ[P]
      J t + fun _ => s₀ := by
    filter_upwards [hJt] with ω h
    simp only [Pi.add_apply]
    rw [h]; ring
  have h2 := condExp_add hJi (integrable_const s₀) ((pathFiltration B).σAlg s) (μ := P)
  rw [condExp_const ((pathFiltration B).le_ambient s)] at h2
  filter_upwards [condExp_congr_ae (m := (pathFiltration B).σAlg s) h1, h2, hce, hJs]
    with ω e1 e2 e3 e4
  rw [e1, e2, Pi.add_apply, e3, e4]
  ring

end Mart

end SignatureVolatility

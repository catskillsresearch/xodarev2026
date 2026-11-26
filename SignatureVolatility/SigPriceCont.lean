/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.ItoCalculusKit.DoleansSDE
public import SignatureVolatility.ItoCalculusKit.DoleansSigma
public import SignatureVolatility.ItoCalculusKit.ItoIncrement8
public import SignatureVolatility.ItoCalculusKit.SigmaContinuity
public import SignatureVolatility.ItoCalculusKit.SigmaHolder8
public import SignatureVolatility.NflvrBoundedBelow
public import SignatureVolatility.NflvrDS
public import SignatureVolatility.ProlongedBrownianSetup.ContVersionKolmogorov
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.SignatureVolatilityModel.Sigma
public import SignatureVolatility.ItoCalculusKit.OfMathFin

@[expose] public section

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The signature volatility of `M` driven by `B`. Definitionally equal to `sigVol M B`. -/
def modelVol (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) : ℝ → Ω → ℝ :=
  SignatureVolatilityModel.sigma M (paperSetup B M.hT)

lemma modelVol_eq_signatureSigma (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) :
    modelVol M B = signatureSigma B M.hT M.ℓ :=
  rfl

/-- Left grid point `j · t / (n+1)` of the uniform partition of `[0, t]`. -/
lemma unifGrid_mem_Icc {t : ℝ} (ht : 0 ≤ t) (n j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
    (j : ℝ) * (t / ((n : ℝ) + 1)) ∈ Icc 0 t := by
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (div_nonneg ht hden.le), ?_⟩
  have : (j : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (Finset.mem_range.mp hj).le
  calc (j : ℝ) * (t / ((n : ℝ) + 1))
      ≤ ((n : ℝ) + 1) * (t / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right this (div_nonneg ht hden.le)
    _ = t := by field_simp

/-- Almost-surely continuous Doléans exponential of the signature volatility, built from the
dyadic continuous version of the raw Itô integral and the raw quadratic variation. At each
`t ∈ [0, T]` it agrees a.s. with `s₀ exp(kitItoInt σ t - ½ kitQuadVar σ t)`. -/
def sigPriceCont (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) :
    ℝ → Ω → ℝ :=
  fun t ω =>
    M.s₀ * Real.exp
      (contVersion (kitItoIntRaw B (modelVol M B)) t ω -
        (1 / 2 : ℝ) * kitQuadVarRaw B (modelVol M B) t ω)

lemma sigPriceCont_zero (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d) (ω : Ω) :
    sigPriceCont M B 0 ω = M.s₀ := by
  have hfloor : ∀ n, dyadicFloor n 0 = 0 := by
    intro n; simp [dyadicFloor]
  have hI : contVersion (kitItoIntRaw B (modelVol M B)) 0 ω = 0 := by
    refine contVersion_eq_of_tendsto ?_
    have hseq : (fun n => kitItoIntRaw B (modelVol M B) (dyadicFloor n 0) ω) =
        fun _ => (0 : ℝ) := by
      funext n; simp [hfloor n, kitItoIntRaw_zero]
    simp [hseq]
  simp [sigPriceCont, hI, kitQuadVarRaw_zero]

lemma sigPriceCont_strictly_pos (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (t : ℝ) (ω : Ω) : 0 < sigPriceCont M B t ω :=
  mul_pos M.hs₀ (Real.exp_pos _)

lemma measurable_sigPriceCont (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (t : ℝ) : Measurable (sigPriceCont M B t) :=
  measurable_const.mul
    (((measurable_contVersion (kitItoIntRaw B (modelVol M B)) t
        fun _ => measurable_kitItoIntRaw B _ _).sub
      ((measurable_kitQuadVarRaw B (modelVol M B) t).const_mul (1 / 2 : ℝ))).exp)

lemma modelVol_adapted_path (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (modelVol M B s.1) :=
  measurable_signatureSigma_path B M.hT M.ℓ t s

/-- Raw Itô of an `L⁸` Hölder integrand has Kolmogorov increments, so its dyadic continuous
version is a.s. path-continuous on `[0, T]` and agrees with the raw process at each time. -/
lemma contVersion_kitItoIntRaw_ae (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    (∀ᵐ ω ∂P, ContinuousOn (fun t =>
        contVersion (kitItoIntRaw B (modelVol M B)) t ω) (Icc 0 M.T)) ∧
      ∀ t, 0 ≤ t → t ≤ M.T →
        contVersion (kitItoIntRaw B (modelVol M B)) t =ᵐ[P]
          kitItoIntRaw B (modelVol M B) t := by
  obtain ⟨K, hK⟩ := holderAdapted8_signatureSigma B M.hT M.h2 M.h1 M.T
  have hC :
      0 ≤ 14 ^ 4 * gauss8Const *
        (128 * ∫ ω, modelVol M B 0 ω ^ 8 ∂P + 128 * K * M.T ^ 4) := by
    have := hK.K_nonneg
    have := gauss8Const_nonneg
    have : 0 ≤ ∫ ω, modelVol M B 0 ω ^ 8 ∂P :=
      integral_nonneg fun ω => by positivity
    positivity
  refine contVersion_kolmogorov M.hT.le hC
    (fun s _ _ => measurable_kitItoIntRaw B _ s)
    (fun u v hu huv hvT => by
      simpa [modelVol_eq_signatureSigma] using
        integral_kitItoIntRaw_sub_pow_eight_le B M.hd hK hu huv hvT)

lemma kitPairIntegrable_modelVol (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (h3 : HypH3 P M.T (modelVol M B))
    {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    kitPairIntegrable B (modelVol M B) t :=
  ⟨(kitItoIntRaw_signatureSigma B M.hd M.hT M.h2 M.h1 ht.1).2.2,
    integrable_kitQuadVarRaw_signatureSigma B M.hd M.hT M.w M.h2 M.ℓ M.h1 h3 ht⟩

lemma kitItoInt_modelVol_eq_raw (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (h3 : HypH3 P M.T (modelVol M B))
    {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    kitItoInt B (modelVol M B) t = kitItoIntRaw B (modelVol M B) t :=
  kitItoInt_eq_raw B ht.1 (fun u hu0 hut => modelVol_adapted_path M B t ⟨u, hu0, hut⟩)
    (kitPairIntegrable_modelVol M B h3 ht)

lemma kitQuadVar_modelVol_eq_raw (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (h3 : HypH3 P M.T (modelVol M B))
    {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    kitQuadVar B (modelVol M B) t = kitQuadVarRaw B (modelVol M B) t :=
  kitQuadVar_eq_raw B ht.1 (fun u hu0 hut => modelVol_adapted_path M B t ⟨u, hu0, hut⟩)
    (kitPairIntegrable_modelVol M B h3 ht)

lemma continuousOn_kitQuadVarRaw_of_continuousOn_vol (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {ω : Ω}
    (hω : ContinuousOn (fun s => modelVol M B s ω) (Icc 0 M.T)) :
    ContinuousOn (fun t => kitQuadVarRaw B (modelVol M B) t ω) (Icc 0 M.T) := by
  have hf : ContinuousOn (fun s => (modelVol M B s ω) ^ 2) (Icc 0 M.T) := hω.pow 2
  have hI : IntegrableOn (fun s => (modelVol M B s ω) ^ 2) (uIcc (0 : ℝ) M.T) volume := by
    rw [uIcc_of_le M.hT.le]
    exact hf.integrableOn_Icc
  have hprim : ContinuousOn
      (fun t => ∫ s in (0 : ℝ)..t, (modelVol M B s ω) ^ 2) (Icc 0 M.T) := by
    have := continuousOn_primitive_interval hI
    rwa [uIcc_of_le M.hT.le] at this
  have heq : ∀ t ∈ Icc 0 M.T,
      kitQuadVarRaw B (modelVol M B) t ω =
        ∫ s in (0 : ℝ)..t, (modelVol M B s ω) ^ 2 :=
    fun t ht => kitQuadVarRaw_signatureSigma B M.hd M.hT M.ℓ ht hω
  exact ContinuousOn.congr hprim fun t ht => heq t ht

lemma ae_continuousOn_sigPriceCont (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => sigPriceCont M B t ω) (Icc 0 M.T) := by
  filter_upwards [(contVersion_kitItoIntRaw_ae M B).1,
    ae_continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1] with ω hI hσ
  have hQ := continuousOn_kitQuadVarRaw_of_continuousOn_vol M B hσ
  have hexp : ContinuousOn (fun t =>
      Real.exp (contVersion (kitItoIntRaw B (modelVol M B)) t ω -
        (1 / 2 : ℝ) * kitQuadVarRaw B (modelVol M B) t ω)) (Icc 0 M.T) :=
    Real.continuous_exp.comp_continuousOn (hI.sub (hQ.const_mul (1 / 2 : ℝ)))
  have hmul : ContinuousOn
      ((fun _ : ℝ => M.s₀) * fun t =>
        Real.exp (contVersion (kitItoIntRaw B (modelVol M B)) t ω -
          (1 / 2 : ℝ) * kitQuadVarRaw B (modelVol M B) t ω)) (Icc 0 M.T) :=
    continuousOn_const.mul hexp
  exact ContinuousOn.congr hmul fun t _ => by
    simp [sigPriceCont, Pi.mul_apply]

lemma sigPriceCont_ae_eq_doleans (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (h3 : HypH3 P M.T (modelVol M B))
    {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    sigPriceCont M B t =ᵐ[P] fun ω =>
      M.s₀ * Real.exp (kitItoInt B (modelVol M B) t ω -
        (1 / 2 : ℝ) * kitQuadVar B (modelVol M B) t ω) := by
  rw [kitItoInt_modelVol_eq_raw M B h3 ht, kitQuadVar_modelVol_eq_raw M B h3 ht]
  filter_upwards [(contVersion_kitItoIntRaw_ae M B).2 t ht.1 ht.2] with ω hI
  simp [sigPriceCont, hI]

lemma sigPriceCont_adapted_path (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (t : ℝ) (s : {s : ℝ // 0 ≤ s ∧ s ≤ t}) :
    Measurable[(pathFiltration B).σAlg t] (sigPriceCont M B s.1) := by
  have hs0 : 0 ≤ s.1 := s.2.1
  have hst : s.1 ≤ t := s.2.2
  have hdy : ∀ n, Measurable[(pathFiltration B).σAlg s.1]
      (kitItoIntRaw B (modelVol M B) (dyadicFloor n s.1)) := by
    intro n
    have hdn0 : 0 ≤ dyadicFloor n s.1 := dyadicFloor_nonneg n s.1
    have hdns : dyadicFloor n s.1 ≤ s.1 := dyadicFloor_le hs0 n
    exact (measurable_kitItoIntRaw_path B (modelVol M B) hdn0
      (fun u hu0 hut =>
        modelVol_adapted_path M B (dyadicFloor n s.1) ⟨u, hu0, hut⟩)).mono
      ((pathFiltration B).mono hdns) le_rfl
  have hI : Measurable[(pathFiltration B).σAlg t]
      (contVersion (kitItoIntRaw B (modelVol M B)) s.1) :=
    (measurable_contVersion (kitItoIntRaw B (modelVol M B)) s.1 hdy).mono
      ((pathFiltration B).mono hst) le_rfl
  have hQ : Measurable[(pathFiltration B).σAlg t]
      (kitQuadVarRaw B (modelVol M B) s.1) :=
    (measurable_kitQuadVarRaw_path B (modelVol M B) hs0
      (fun u hu0 hut => modelVol_adapted_path M B s.1 ⟨u, hu0, hut⟩)).mono
      ((pathFiltration B).mono hst) le_rfl
  change Measurable[(pathFiltration B).σAlg t]
      (fun ω => M.s₀ * Real.exp (contVersion (kitItoIntRaw B (modelVol M B)) s.1 ω -
        (1 / 2 : ℝ) * kitQuadVarRaw B (modelVol M B) s.1 ω))
  exact (measurable_const : Measurable[(pathFiltration B).σAlg t] (fun _ => M.s₀)).mul
    ((hI.sub (hQ.const_mul (1 / 2 : ℝ))).exp)

/-- If two integrands agree a.s. at every time of `[0, t]`, so do the raw Itô integrals. -/
lemma kitItoIntRaw_congr_ae {d : ℕ} (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hmeas : ∀ u, Measurable (H u)) (hmeas' : ∀ u, Measurable (H' u))
    (h : ∀ u ∈ Icc 0 t, H u =ᵐ[P] H' u) :
    kitItoIntRaw B H t =ᵐ[P] kitItoIntRaw B H' t := by
  have hf : forceMeasurableProcess H = H := forceMeasurableProcess_of_measurable hmeas
  have hf' : forceMeasurableProcess H' = H' := forceMeasurableProcess_of_measurable hmeas'
  unfold kitItoIntRaw
  split_ifs with hd
  · rw [hf, hf']
    have hR : ∀ n, itoRiemann_process B (kitDriver hd) H 0 t n =ᵐ[P]
        itoRiemann_process B (kitDriver hd) H' 0 t n := by
      intro n
      set Δ := (t - (0 : ℝ)) / (n + 1 : ℕ)
      have htimes : ∀ j ∈ Finset.range (n + 1), (0 : ℝ) + (j : ℝ) * Δ ∈ Icc 0 t := by
        intro j hj
        have : (j : ℝ) * (t / ((n : ℝ) + 1)) ∈ Icc 0 t := unifGrid_mem_Icc ht n j hj
        have hΔ : Δ = t / ((n : ℝ) + 1) := by simp [Δ]
        simpa [hΔ] using this
      have hpts : ∀ j ∈ Finset.range (n + 1),
          (fun ω => H ((0 : ℝ) + (j : ℝ) * Δ) ω *
            wnnIncr B (kitDriver hd) ((0 : ℝ) + (j : ℝ) * Δ)
              ((0 : ℝ) + ((j : ℝ) + 1) * Δ) ω) =ᵐ[P]
          (fun ω => H' ((0 : ℝ) + (j : ℝ) * Δ) ω *
            wnnIncr B (kitDriver hd) ((0 : ℝ) + (j : ℝ) * Δ)
              ((0 : ℝ) + ((j : ℝ) + 1) * Δ) ω) :=
        fun j hj => (h _ (htimes j hj)).mul EventuallyEq.rfl
      filter_upwards [(eventually_all_finset (Finset.range (n + 1))).2 hpts] with ω hω
      dsimp [itoRiemann_process]
      exact Finset.sum_congr rfl fun j hj => hω j hj
    have hseq : ∀ᵐ ω ∂P, ∀ n,
        itoRiemann_process B (kitDriver hd) H 0 t n ω =
          itoRiemann_process B (kitDriver hd) H' 0 t n ω := by
      rw [ae_all_iff]; exact hR
    filter_upwards [hseq] with ω hω
    dsimp [itoIntegral_process]
    split_ifs
    · have : (fun n => itoRiemann_process B (kitDriver hd) H 0 t n ω) =
          (fun n => itoRiemann_process B (kitDriver hd) H' 0 t n ω) := funext hω
      rw [this]
  · rfl

/-- If two integrands agree a.s. at every time of `[0, t]`, so does the raw quadratic variation. -/
lemma kitQuadVarRaw_congr_ae {d : ℕ} (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hmeas : ∀ u, Measurable (H u)) (hmeas' : ∀ u, Measurable (H' u))
    (h : ∀ u ∈ Icc 0 t, H u =ᵐ[P] H' u) :
    kitQuadVarRaw B H t =ᵐ[P] kitQuadVarRaw B H' t := by
  have hf : forceMeasurableProcess H = H := forceMeasurableProcess_of_measurable hmeas
  have hf' : forceMeasurableProcess H' = H' := forceMeasurableProcess_of_measurable hmeas'
  unfold kitQuadVarRaw
  split_ifs
  · rw [show (fun s ω' => forceMeasurableProcess H s ω' * forceMeasurableProcess H s ω') =
        fun s ω' => H s ω' * H s ω' by rw [hf],
      show (fun s ω' => forceMeasurableProcess H' s ω' * forceMeasurableProcess H' s ω') =
        fun s ω' => H' s ω' * H' s ω' by rw [hf']]
    have hR : ∀ n, lebRiemann_process (fun s ω' => H s ω' * H s ω') 0 t n =ᵐ[P]
        lebRiemann_process (fun s ω' => H' s ω' * H' s ω') 0 t n := by
      intro n
      set Δ := (t - (0 : ℝ)) / (n + 1 : ℕ)
      have htimes : ∀ j ∈ Finset.range (n + 1), (0 : ℝ) + (j : ℝ) * Δ ∈ Icc 0 t := by
        intro j hj
        have : (j : ℝ) * (t / ((n : ℝ) + 1)) ∈ Icc 0 t := unifGrid_mem_Icc ht n j hj
        have hΔ : Δ = t / ((n : ℝ) + 1) := by simp [Δ]
        simpa [hΔ] using this
      have hpts : ∀ j ∈ Finset.range (n + 1),
          (fun ω => (H ((0 : ℝ) + (j : ℝ) * Δ) ω * H ((0 : ℝ) + (j : ℝ) * Δ) ω) * Δ) =ᵐ[P]
          (fun ω => (H' ((0 : ℝ) + (j : ℝ) * Δ) ω * H' ((0 : ℝ) + (j : ℝ) * Δ) ω) * Δ) := by
        intro j hj
        filter_upwards [h _ (htimes j hj)] with ω hω
        rw [zero_add] at hω
        simp [hω]
      filter_upwards [(eventually_all_finset (Finset.range (n + 1))).2 hpts] with ω hω
      dsimp [lebRiemann_process]
      exact Finset.sum_congr rfl fun j hj => hω j hj
    have hseq : ∀ᵐ ω ∂P, ∀ n,
        lebRiemann_process (fun s ω' => H s ω' * H s ω') 0 t n ω =
          lebRiemann_process (fun s ω' => H' s ω' * H' s ω') 0 t n ω := by
      rw [ae_all_iff]; exact hR
    filter_upwards [hseq] with ω hω
    dsimp [lebIntegral_process]
    split_ifs
    · have : (fun n => lebRiemann_process (fun s ω' => H s ω' * H s ω') 0 t n ω) =
          (fun n => lebRiemann_process (fun s ω' => H' s ω' * H' s ω') 0 t n ω) := funext hω
      rw [this]
  · rfl

lemma kitItoInt_congr_ae {d : ℕ} (B : MultiBrownian Ω P d) {H H' : ℝ → Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hmeas : ∀ u, Measurable (H u)) (hmeas' : ∀ u, Measurable (H' u))
    (h : ∀ u ∈ Icc 0 t, H u =ᵐ[P] H' u) :
    kitItoInt B H t =ᵐ[P] kitItoInt B H' t := by
  have hraw := kitItoIntRaw_congr_ae B ht hmeas hmeas' h
  have hQ := kitQuadVarRaw_congr_ae B ht hmeas hmeas' h
  have hpair : kitPairIntegrable B H t ↔ kitPairIntegrable B H' t :=
    ⟨fun hp => ⟨hp.1.congr hraw, hp.2.congr hQ⟩,
      fun hp => ⟨hp.1.congr hraw.symm, hp.2.congr hQ.symm⟩⟩
  simp only [kitItoInt]
  by_cases hp : kitPairIntegrable B H t
  · have hp' : kitPairIntegrable B H' t := hpair.mp hp
    simp only [hp, hp', ↓reduceIte]
    exact condExp_congr_ae hraw
  · have hp' : ¬ kitPairIntegrable B H' t := mt hpair.mpr hp
    simp [hp, hp']

lemma W_coord_continuous (M : SignatureVolatilityModel) (B : MultiBrownian Ω P M.d)
    (ω : Ω) : Continuous (fun t => MultiBrownian.W B t ω (kitDriver M.hd)) :=
  continuous_W_coord B (kitDriver M.hd) ω

lemma sigPriceCont_adapted_sig (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    Measurable[(generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
      (measurable_paperSig2_coeff B 0)).σAlg t] (sigPriceCont M B t) := by
  rw [sigFiltration_eq_pathFiltration B t]
  exact sigPriceCont_adapted_path M B t ⟨t, ht.1, le_rfl⟩

lemma modelVol_adapted_sig (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) {t : ℝ} (ht : t ∈ Icc 0 M.T) :
    Measurable[(generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
      (measurable_paperSig2_coeff B 0)).σAlg t] (modelVol M B t) := by
  rw [sigFiltration_eq_pathFiltration B t]
  exact modelVol_adapted_path M B t ⟨t, ht.1, le_rfl⟩

/-- Delbaen–Schachermayer NFLVR for the continuous Doléans price `sigPriceCont`. -/
theorem satisfiesNFLVR_DS_sigPriceCont (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) (_h3 : HypH3 P M.T (modelVol M B)) :
    SatisfiesNFLVR_DS P
      (BoundedBelowGains (paperSetup B M.hT).signatureFiltration.σAlg P
        (fun t ω => MultiBrownian.W B t ω (kitDriver M.hd))
        (sigPriceCont M B) (modelVol M B) M.T) := by
  have hfilt :
      (paperSetup B M.hT).signatureFiltration.σAlg =
        (generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
          (measurable_paperSig2_coeff B 0)).σAlg := rfl
  rw [hfilt]
  exact satisfiesNFLVR_DS_boundedBelowGains M.hd B (W_coord_continuous M B) M.hT
    (fun t ht => sigPriceCont_adapted_sig M B ht)
    (fun t ht => modelVol_adapted_sig M B ht)
    (ae_continuousOn_sigPriceCont M B)
    (ae_continuousOn_sigma_of_brownian B M.hT M.w M.h2 M.ℓ M.h1)

end SignatureVolatility

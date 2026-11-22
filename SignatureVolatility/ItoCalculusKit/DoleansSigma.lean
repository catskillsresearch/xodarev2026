module

public import SignatureVolatility.ItoCalculusKit.ConstVol
public import SignatureVolatility.ItoCalculusKit.DoleansMoments

@[expose] public section

open MeasureTheory Set

namespace SignatureVolatility

/-!
# Signature volatility inputs for the Doléans SDE

Pathwise identification of the raw quadratic variation of `σ = ⟨ℓ, Ŵ⟩`, the pathwise form
`Z_t = exp (limUnder ∑ σ ΔW - ½ ∫₀ᵗ σ²)` of the kit Doléans exponential, and its `Lⁿ` moments
(split out of `DoleansSDE` so that the Doléans identification modules can use them).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-! ## Signature volatility: adaptedness and the quadratic-variation half of the kit -/

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

/-- Under H1–H3 the kit Doléans exponential of the signature volatility is, for every `ω`,
`Z_t = exp (limUnder ∑ σ ΔW - ½ ∫₀ᵗ σ²)` (the integrability gate is discharged by
`kitItoIntRaw_signatureSigma`). -/
lemma kitDoleansExp_signatureSigma_eq {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (hT : 0 < T) (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Icc 0 T) (ω : Ω) :
    kitDoleansExp B (signatureSigma B hT ℓ) t ω =
      Real.exp (kitItoIntRaw B (signatureSigma B hT ℓ) t ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (signatureSigma B hT ℓ s ω) ^ 2) :=
  kitDoleansExp_signatureSigma B hd hT w hw ℓ hℓ h3 ht
    (kitItoIntRaw_signatureSigma B hd hT hw hℓ ht.1).2.2 ω

/-- **All `Lⁿ` moments of the Doléans exponential of the signature volatility** (H1–H3). -/
theorem memLp_kitDoleansExp_signatureSigma {T : ℝ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (hT : 0 < T) (w : Weight) (hw : HypH2 w) (ℓ : ExtTensorAlgebra (d + 1)) (hℓ : HypH1 w ℓ)
    (h3 : HypH3 P T (signatureSigma B hT ℓ)) {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) (hn : 1 ≤ n) :
    MemLp (kitDoleansExp B (signatureSigma B hT ℓ) t) n P := by
  have hmeas := (measurable_kitDoleansExp B (signatureSigma B hT ℓ) t).aestronglyMeasurable
    (μ := P)
  have hfin := lintegral_exp_mul_signatureSigma_le B hd hT hw hℓ h3 ht (p := n)
    (by exact_mod_cast hn)
  have hlt := hfin.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩)
  have h4 : MemLp (kitDoleansExp B (signatureSigma B hT ℓ) t) ((n : ℕ) : ENNReal) P := by
    rw [← integrable_norm_rpow_iff hmeas (by simpa using (by omega : n ≠ 0)) (by simp)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    refine ⟨hmeas.norm.pow n, ?_⟩
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) hlt
    rw [Real.enorm_eq_ofReal (by positivity)]
    simp only [Real.norm_eq_abs]
    rw [kitDoleansExp_signatureSigma_eq B hd hT w hw ℓ hℓ h3 ht ω, Real.abs_exp,
      ← Real.exp_nat_mul]
  exact_mod_cast h4
end SignatureVolatility

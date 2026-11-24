module

public import SignatureVolatility.GeneratedFiltration
public import SignatureVolatility.ProlongedBrownianSetup.StratonovichItoConversion


@[expose] public section

open MeasureTheory

noncomputable section

namespace SignatureVolatility

/-!
# Path-filtration measurability of Itô / Stratonovich word coordinates

Proves `Measurable[(pathFiltration B).σAlg T]` for signature coordinates on `[0,s]` with
`s ≤ T`. The filtration is packaged as an `IndexedFiltration` so the σ-algebra is never a
bare `MeasurableSpace` variable (which would compete with the ambient instance on
`MultiBrownian`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Path filtration of `W` (same generators as `sig_adapted_to_W`). -/
def pathFiltration (B : MultiBrownian Ω P d) : IndexedFiltration Ω :=
  generatedFiltration (fun u i ω => MultiBrownian.W B u ω i) (MultiBrownian.W_meas B)

lemma measurable_W_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (u : {u : ℝ // 0 ≤ u ∧ u ≤ T}) (i : Fin d) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => MultiBrownian.W B u.1 ω i) :=
  (comap_measurable _).mono (le_iSup_of_le u (le_iSup_of_le i le_rfl)) le_rfl

lemma measurable_wnnIncr_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i : Fin d) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => wnnIncr B i s t ω) := by
  -- `W` is `reindexProcessFin Wnn`, so `wnnIncr` is definitionally a `W`-increment.
  change Measurable[(pathFiltration B).σAlg T]
    (fun ω => MultiBrownian.W B t ω i - MultiBrownian.W B s ω i)
  exact (measurable_W_pathFiltration B ⟨t, ht, htT⟩ i).sub
    (measurable_W_pathFiltration B ⟨s, hs, hsT⟩ i)

private lemma dyadic_time_mem_Icc {s t : ℝ} (hst : s ≤ t) (n k : ℕ) (hk : k ≤ n + 1) :
    s ≤ s + (k : ℝ) * ((t - s) / (n + 1 : ℕ)) ∧
      s + (k : ℝ) * ((t - s) / (n + 1 : ℕ)) ≤ t := by
  set Δ := (t - s) / (n + 1 : ℕ)
  have hΔ : 0 ≤ Δ := div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg _)
  constructor
  · nlinarith
  · have hk' : (k : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hk
    have hbound : (k : ℝ) * Δ ≤ (n + 1 : ℕ) * Δ := mul_le_mul_of_nonneg_right hk' hΔ
    have htel : s + (n + 1 : ℕ) * Δ = t := by
      simp only [Δ]
      field_simp
      ring
    linarith [hbound, htel]

lemma measurable_lebRiemann_wnnIncr_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => lebRiemann_wnnIncr B i s t n ω) := by
  simp only [lebRiemann_wnnIncr]
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hmem := dyadic_time_mem_Icc hst n k (Nat.le_succ_of_le hk')
  have hu0 : 0 ≤ s + (k : ℝ) * ((t - s) / (n + 1 : ℕ)) := le_trans hs hmem.1
  have huT : s + (k : ℝ) * ((t - s) / (n + 1 : ℕ)) ≤ T := le_trans hmem.2 htT
  exact (measurable_wnnIncr_pathFiltration B i hs hu0 (le_trans hst htT) huT).mul
    measurable_const

lemma measurable_lebIntegral_wnnIncrement_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => lebIntegral_wnnIncrement B i s t ω) := by
  classical
  simp only [lebIntegral_wnnIncrement, hst, ↓reduceDIte]
  have hf : ∀ n, StronglyMeasurable[(pathFiltration B).σAlg T]
      (fun ω => lebRiemann_wnnIncr B i s t n ω) := fun n =>
    (measurable_lebRiemann_wnnIncr_pathFiltration B i hs hst htT n).stronglyMeasurable
  let : MeasurableSpace Ω := (pathFiltration B).σAlg T
  exact (StronglyMeasurable.limUnder hf).measurable

lemma measurable_itoIntegral_timeIntegrand_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoIntegral_timeIntegrand B i s t ω) := by
  classical
  simp only [itoIntegral_timeIntegrand, hst, ↓reduceDIte]
  exact (measurable_const.mul
    (measurable_wnnIncr_pathFiltration B i hs (le_trans hs hst) (le_trans hst htT) htT)).sub
    (measurable_lebIntegral_wnnIncrement_pathFiltration B i hs hst htT)

lemma measurable_itoIntegral_wnnIncrement_diag_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoIntegral_wnnIncrement_diag B i s t ω) := by
  classical
  simp only [itoIntegral_wnnIncrement_diag, hst, ↓reduceDIte]
  exact measurable_const.mul <|
    ((measurable_wnnIncr_pathFiltration B i hs (le_trans hs hst) (le_trans hst htT) htT).pow_const 2).sub
      measurable_const

lemma measurable_itoRiemann_wnnIncr_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i k : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoRiemann_wnnIncr B i k s t n ω) := by
  simp only [itoRiemann_wnnIncr]
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hL := dyadic_time_mem_Icc hst n j (Nat.le_succ_of_le hj')
  have hR := dyadic_time_mem_Icc hst n (j + 1) (by omega)
  have hL0 : 0 ≤ s + (j : ℝ) * ((t - s) / (n + 1 : ℕ)) := le_trans hs hL.1
  have hR0 : 0 ≤ s + ((j : ℝ) + 1) * ((t - s) / (n + 1 : ℕ)) := by
    convert le_trans hs hR.1 using 1
    push_cast; ring
  have hLT : s + (j : ℝ) * ((t - s) / (n + 1 : ℕ)) ≤ T := le_trans hL.2 htT
  have hRT : s + ((j : ℝ) + 1) * ((t - s) / (n + 1 : ℕ)) ≤ T := by
    convert le_trans hR.2 htT using 1
    push_cast; ring
  exact (measurable_wnnIncr_pathFiltration B i hs hL0 (le_trans hst htT) hLT).mul
    (measurable_wnnIncr_pathFiltration B k hL0 hR0 hLT hRT)

lemma measurable_itoIntegral_wnnIncrement_cross_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i k : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoIntegral_wnnIncrement_cross B i k s t ω) := by
  classical
  simp only [itoIntegral_wnnIncrement_cross, hst, ↓reduceDIte]
  have hf : ∀ n, StronglyMeasurable[(pathFiltration B).σAlg T]
      (fun ω => itoRiemann_wnnIncr B i k s t n ω) := fun n =>
    (measurable_itoRiemann_wnnIncr_pathFiltration B i k hs hst htT n).stronglyMeasurable
  let : MeasurableSpace Ω := (pathFiltration B).σAlg T
  exact (StronglyMeasurable.limUnder hf).measurable

lemma measurable_itoIntegral_wnnIncrement_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    (i k : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoIntegral_wnnIncrement B i k s t ω) := by
  classical
  by_cases hik : i = k
  · simpa [itoIntegral_wnnIncrement, hik] using
      measurable_itoIntegral_wnnIncrement_diag_pathFiltration B i hs hst htT
  · simpa [itoIntegral_wnnIncrement, hik] using
      measurable_itoIntegral_wnnIncrement_cross_pathFiltration B i k hs hst htT

/-- Process Riemann sums; integrand measurable on the sample grid `[s,t] ⊆ [0,T]`. -/
lemma measurable_lebRiemann_process_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (H : ℝ → Ω → ℝ)
    (hH : ∀ u, s ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg T] (H u))
    (_hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => lebRiemann_process H s t n ω) := by
  simp only [lebRiemann_process]
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hmem := dyadic_time_mem_Icc hst n k (Nat.le_succ_of_le hk')
  have huT : s + (k : ℝ) * ((t - s) / (n + 1 : ℕ)) ≤ T := le_trans hmem.2 htT
  exact (hH _ hmem.1 huT).mul measurable_const

lemma measurable_lebIntegral_process_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (H : ℝ → Ω → ℝ)
    (hH : ∀ u, s ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg T] (H u))
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => lebIntegral_process H s t ω) := by
  classical
  simp only [lebIntegral_process, hst, ↓reduceDIte]
  have hf : ∀ n, StronglyMeasurable[(pathFiltration B).σAlg T]
      (fun ω => lebRiemann_process H s t n ω) := fun n =>
    (measurable_lebRiemann_process_pathFiltration B H hH hs hst htT n).stronglyMeasurable
  let : MeasurableSpace Ω := (pathFiltration B).σAlg T
  exact (StronglyMeasurable.limUnder hf).measurable

lemma measurable_itoRiemann_process_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (k : Fin d) (H : ℝ → Ω → ℝ)
    (hH : ∀ u, s ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg T] (H u))
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoRiemann_process B k H s t n ω) := by
  simp only [itoRiemann_process]
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hL := dyadic_time_mem_Icc hst n j (Nat.le_succ_of_le hj')
  have hR := dyadic_time_mem_Icc hst n (j + 1) (by omega)
  have hL0 : 0 ≤ s + (j : ℝ) * ((t - s) / (n + 1 : ℕ)) := le_trans hs hL.1
  have hR0 : 0 ≤ s + ((j : ℝ) + 1) * ((t - s) / (n + 1 : ℕ)) := by
    convert le_trans hs hR.1 using 1
    push_cast; ring
  have hLT : s + (j : ℝ) * ((t - s) / (n + 1 : ℕ)) ≤ T := le_trans hL.2 htT
  have hRT : s + ((j : ℝ) + 1) * ((t - s) / (n + 1 : ℕ)) ≤ T := by
    convert le_trans hR.2 htT using 1
    push_cast; ring
  exact (hH _ hL.1 hLT).mul
    (measurable_wnnIncr_pathFiltration B k hL0 hR0 hLT hRT)

lemma measurable_itoIntegral_process_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (k : Fin d) (H : ℝ → Ω → ℝ)
    (hH : ∀ u, s ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg T] (H u))
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoIntegral_process B k H s t ω) := by
  classical
  simp only [itoIntegral_process, hst, ↓reduceDIte]
  have hf : ∀ n, StronglyMeasurable[(pathFiltration B).σAlg T]
      (fun ω => itoRiemann_process B k H s t n ω) := fun n =>
    (measurable_itoRiemann_process_pathFiltration B k H hH hs hst htT n).stronglyMeasurable
  let : MeasurableSpace Ω := (pathFiltration B).σAlg T
  exact (StronglyMeasurable.limUnder hf).measurable

lemma measurable_itoWordIntegral_le1_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoWordIntegral_le1 B s t ω I) := by
  match I with
  | [] => simp [itoWordIntegral_le1]
  | j :: I' =>
    simp only [itoWordIntegral_le1]
    by_cases hI : I' ≠ []
    · simp [hI]
    · simp only [hI, ↓reduceIte]
      by_cases hj : (j : ℕ) = 0
      · simp [hj]
      · simp only [hj, ↓reduceDIte]
        exact (measurable_W_pathFiltration B ⟨t, le_trans hs hst, htT⟩ (spaceLetterIndex j hj)).sub
          (measurable_W_pathFiltration B ⟨s, hs, le_trans hst htT⟩ (spaceLetterIndex j hj))

lemma measurable_itoWordIntegral_cons_long_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (j : Fin (d + 1)) (H : ℝ → Ω → ℝ)
    (hH : ∀ u, s ≤ u → u ≤ T → Measurable[(pathFiltration B).σAlg T] (H u))
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoWordIntegral_cons_long B j H s t ω) := by
  simp only [itoWordIntegral_cons_long]
  by_cases hj : (j : ℕ) = 0
  · simpa [hj] using measurable_lebIntegral_process_pathFiltration B H hH hs hst htT
  · simpa [hj] using
      measurable_itoIntegral_process_pathFiltration B (spaceLetterIndex j hj) H hH hs hst htT

lemma measurable_itoWordStep_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s u : ℝ} (j : Fin (d + 1)) (H : ℝ → Ω → ℝ)
    (hH : ∀ v, s ≤ v → v ≤ T → Measurable[(pathFiltration B).σAlg T] (H v))
    (hs : 0 ≤ s) (huT : u ≤ T) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoWordStep B j H s u ω) := by
  unfold itoWordStep
  by_cases hsu : s ≤ u
  · simpa [hsu] using measurable_itoWordIntegral_cons_long_pathFiltration B j H hH hs hsu huT
  · simp only [hsu, ↓reduceIte]
    exact measurable_const

/-- Main Itô ladder under the path filtration (lower time `0 ≤ s ≤ t ≤ T`). -/
lemma measurable_itoWordIntegral_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => itoWordIntegral B s t ω I) := by
  match I with
  | [] => simp [itoWordIntegral]
  | j :: I' =>
    by_cases hI : I' = []
    · subst hI
      simpa [itoWordIntegral] using
        measurable_itoWordIntegral_le1_pathFiltration B hs hst htT [j]
    · simp only [itoWordIntegral, hI, ↓reduceIte]
      refine measurable_contVersion _ t fun n => ?_
      refine measurable_itoWordStep_pathFiltration B j _ ?_ hs
        ((dyadicFloor_le (hs.trans hst) n).trans htT)
      intro v hsv hvT
      exact measurable_itoWordIntegral_pathFiltration B hs hsv hvT I'

lemma measurable_stratItoCorrection_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => stratItoCorrection B s t ω I) := by
  match I with
  | [] =>
    change Measurable[(pathFiltration B).σAlg T] (fun _ => (0 : ℝ))
    exact measurable_const
  | [_] =>
    change Measurable[(pathFiltration B).σAlg T] (fun _ => (0 : ℝ))
    exact measurable_const
  | _ :: _ :: _ =>
    simp only [stratItoCorrection]
    exact Finset.measurable_sum _ fun _ _ =>
      Finset.measurable_sum _ fun J _ =>
        (measurable_itoWordIntegral_pathFiltration B hs hst htT J).const_mul _

lemma measurable_stratWordIntegral_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => stratWordIntegral B s t ω I) :=
  (measurable_itoWordIntegral_pathFiltration B hs hst htT I).add
    (measurable_stratItoCorrection_pathFiltration B hs hst htT I)

lemma measurable_stratSig2_coeff_pathFiltration (B : MultiBrownian Ω P d) {T : ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) (I : Word (d + 1)) :
    Measurable[(pathFiltration B).σAlg T] (fun ω => (stratSig2 B s t ω).coeff I) :=
  measurable_stratWordIntegral_pathFiltration B hs hst htT I

end SignatureVolatility

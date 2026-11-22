module

public import SignatureVolatility.ItoCalculusKit.RiemannConvergence


@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SignatureVolatility

/-!
# Exponential supermartingale bound for raw Itô limits

For an integrand `H` adapted to the path filtration, the discrete exponentials
`exp (∑ q Hᵢ ΔWᵢ - q²/2 Hᵢ² Δtᵢ)` along the uniform grid have expectation exactly `1`
(`lintegral_exp_unifStep_eq_one`; Gaussian increments independent of the past). By Fatou, any
almost-sure limits `I` of the Itô–Riemann sums and `Q` of the Lebesgue sums of `H²` satisfy
`E exp (q I - q²/2 Q) ≤ 1` (`lintegral_exp_ito_le_one`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

lemma lintegral_ofReal_exp_mul_gaussianReal (c : ℝ) (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂(gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp ((v : ℝ) * c ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
    (ae_of_all _ fun x => (Real.exp_pos _).le)]
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) c
  simp only [mgf, id_eq, zero_mul, zero_add] at h
  rw [h]

/-- One step of the discrete exponential martingale: for `A, h` measurable for the past at `s`,
`E exp (A + q h ΔW - q²/2 h² (u - s)) = E exp A`. -/
lemma lintegral_exp_add_step (B : MultiBrownian Ω P d) (k : Fin d) {s u : ℝ} (hs : 0 ≤ s)
    (hsu : s ≤ u) {A h : Ω → ℝ} (hA : Measurable[(pathFiltration B).σAlg s] A)
    (hh : Measurable[(pathFiltration B).σAlg s] h) (q : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (A ω + (q * h ω * wnnIncr B k s u ω -
        q ^ 2 / 2 * h ω ^ 2 * (u - s)))) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (A ω)) ∂P := by
  set g : Ω → ℝ × ℝ := fun ω => (A ω, h ω) with hgdef
  have hgm : Measurable[(pathFiltration B).σAlg s] g := hA.prodMk hh
  have hle := (pathFiltration B).le_ambient s
  have hg' : Measurable g := hgm.mono hle le_rfl
  set X : Ω → ℝ := fun ω => wnnIncr B k s u ω with hXdef
  have hX : Measurable X := measurable_wnnIncr B k s u
  have hind : IndepFun g X P := indepFun_pathFiltration_wnnIncr B k hsu hgm
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hg'.aemeasurable hX.aemeasurable).mp hind
  have hlaw : P.map X = gaussianReal 0 (Real.toNNReal (u - s)) :=
    (hasLaw_wnnIncr B k hs hsu).map_eq
  set F : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (p.1.1 +
    (q * p.1.2 * p.2 - q ^ 2 / 2 * p.1.2 ^ 2 * (u - s)))) with hFdef
  have hF : Measurable F := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    fun_prop
  have hinner : ∀ a : ℝ × ℝ, ∫⁻ x, F (a, x) ∂(gaussianReal 0 (Real.toNNReal (u - s))) =
      ENNReal.ofReal (Real.exp a.1) := by
    intro a
    have hpt : ∀ x : ℝ, F (a, x) = ENNReal.ofReal (Real.exp a.1 *
        Real.exp (-(q ^ 2 / 2 * a.2 ^ 2 * (u - s)))) *
        ENNReal.ofReal (Real.exp ((q * a.2) * x)) := by
      intro x
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
      simp only [hFdef]
      congr 2
      ring
    simp_rw [hpt]
    rw [lintegral_const_mul _
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (q * a.2 * x))),
      lintegral_ofReal_exp_mul_gaussianReal, ← ENNReal.ofReal_mul (by positivity),
      Real.coe_toNNReal _ (sub_nonneg.mpr hsu), mul_assoc, ← Real.exp_add]
    congr 2
    rw [show -(q ^ 2 / 2 * a.2 ^ 2 * (u - s)) + (u - s) * (q * a.2) ^ 2 / 2 = 0 by ring,
      Real.exp_zero, mul_one]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (A ω + (q * h ω * wnnIncr B k s u ω -
        q ^ 2 / 2 * h ω ^ 2 * (u - s)))) ∂P
      = ∫⁻ ω, F (g ω, X ω) ∂P := rfl
    _ = ∫⁻ p, F p ∂(P.map (fun ω => (g ω, X ω))) :=
        (lintegral_map hF (hg'.prodMk hX)).symm
    _ = ∫⁻ p, F p ∂((P.map g).prod (gaussianReal 0 (Real.toNNReal (u - s)))) := by
        rw [hmap, hlaw]
    _ = ∫⁻ a, ∫⁻ x, F (a, x) ∂(gaussianReal 0 (Real.toNNReal (u - s))) ∂(P.map g) :=
        lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ a, ENNReal.ofReal (Real.exp a.1) ∂(P.map g) := by simp_rw [hinner]
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (A ω)) ∂P :=
        lintegral_map (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp measurable_fst)) hg'

/-- Log-increment of the discrete exponential martingale on the uniform grid `tᵢ = i t / N`. -/
noncomputable def unifStepLog (B : MultiBrownian Ω P d) (k : Fin d) (H : ℝ → Ω → ℝ) (q t : ℝ)
    (N i : ℕ) (ω : Ω) : ℝ :=
  q * H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω -
    q ^ 2 / 2 * H ((i : ℝ) * (t / (N : ℝ))) ω ^ 2 *
      ((((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) - (i : ℝ) * (t / (N : ℝ)))

lemma sum_unifStepLog (B : MultiBrownian Ω P d) (k : Fin d) (H : ℝ → Ω → ℝ) (q t : ℝ) (N : ℕ)
    (ω : Ω) :
    ∑ i ∈ Finset.range N, unifStepLog B k H q t N i ω =
      q * unifRiemann B k H t N ω - q ^ 2 / 2 *
        ∑ i ∈ Finset.range N, H ((i : ℝ) * (t / (N : ℝ))) ω ^ 2 * (t / (N : ℝ)) := by
  unfold unifStepLog unifRiemann
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring

/-- **Discrete exponential martingale**: for an adapted integrand, the uniform-grid discrete
Doléans exponentials have expectation exactly `1`. -/
lemma lintegral_exp_unifStep_eq_one (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hH : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u)) (q : ℝ) (N : ℕ) :
    ∀ m ≤ N, ∫⁻ ω, ENNReal.ofReal (Real.exp
      (∑ i ∈ Finset.range m, unifStepLog B k H q t N i ω)) ∂P = 1 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hN : 0 < N := by omega
    have hΔ : 0 ≤ t / (N : ℝ) := div_nonneg ht (Nat.cast_nonneg _)
    have hgrid : ∀ i, i ≤ N → 0 ≤ (i : ℝ) * (t / (N : ℝ)) ∧ (i : ℝ) * (t / (N : ℝ)) ≤ t :=
      fun i hi => unifGrid_mem ht hN hi
    have hmono : ∀ i j : ℕ, i ≤ j → (i : ℝ) * (t / (N : ℝ)) ≤ (j : ℝ) * (t / (N : ℝ)) :=
      fun i j hij => mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hΔ
    set s : ℝ := (m : ℝ) * (t / (N : ℝ)) with hsdef
    have hs := hgrid m (by omega)
    have hA : Measurable[(pathFiltration B).σAlg s]
        (fun ω => ∑ i ∈ Finset.range m, unifStepLog B k H q t N i ω) := by
      refine Finset.measurable_sum _ fun i hi => ?_
      have hi' : i < m := Finset.mem_range.mp hi
      have hgi := hgrid i (by omega)
      have hgi1 := hgrid (i + 1) (by omega)
      have hHi : Measurable[(pathFiltration B).σAlg s] (H ((i : ℝ) * (t / (N : ℝ)))) :=
        (hH _ hgi.1 hgi.2).mono ((pathFiltration B).mono (hmono i m hi'.le)) le_rfl
      have hW : Measurable[(pathFiltration B).σAlg s] (fun ω => wnnIncr B k
          ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω) :=
        measurable_wnnIncr_pathFiltration B k hgi.1 hgi1.1 (hmono i m hi'.le)
          (hmono (i + 1) m hi')
      unfold unifStepLog
      exact ((hHi.const_mul q).mul hW).sub (((hHi.pow_const 2).const_mul _).mul_const _)
    have hHs : Measurable[(pathFiltration B).σAlg s] (H s) := hH s hs.1 hs.2
    have hsu : s ≤ ((m + 1 : ℕ) : ℝ) * (t / (N : ℝ)) := hmono m (m + 1) (Nat.le_succ m)
    have hstep := lintegral_exp_add_step B k hs.1 hsu hA hHs q
    simp_rw [Finset.sum_range_succ]
    rw [← ih (by omega)]
    exact hstep

/-- **Exponential supermartingale bound (Fatou).** If the Itô–Riemann sums of an adapted `H`
converge a.s. to `I` and the Lebesgue sums of `H²` converge a.s. to `Q` along the uniform grids,
then `E exp (q I - q²/2 Q) ≤ 1`. -/
theorem lintegral_exp_ito_le_one (B : MultiBrownian Ω P d) (k : Fin d) {H : ℝ → Ω → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hH : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u)) (q : ℝ)
    {I Q : Ω → ℝ}
    (hI : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H t (n + 1) ω) atTop (𝓝 (I ω)))
    (hQ : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
      H ((i : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω ^ 2 * (t / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 (Q ω))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (q * I ω - q ^ 2 / 2 * Q ω)) ∂P ≤ 1 := by
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp
    (∑ i ∈ Finset.range (n + 1), unifStepLog B k H q t (n + 1) i ω)) with hf
  have hint : ∀ n, ∫⁻ ω, f n ω ∂P = 1 := fun n =>
    lintegral_exp_unifStep_eq_one B k ht hH q (n + 1) (n + 1) le_rfl
  have hmeasH : ∀ u, 0 ≤ u → u ≤ t → Measurable (H u) := fun u h0 h1 =>
    (hH u h0 h1).mono ((pathFiltration B).le_ambient u) le_rfl
  have hfm : ∀ n, AEMeasurable (f n) P := by
    intro n
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (Finset.measurable_sum _ fun i hi => ?_))).aemeasurable
    have hgi := unifGrid_mem ht n.succ_pos (Finset.mem_range.mp hi).le
    have hHi := hmeasH _ hgi.1 hgi.2
    unfold unifStepLog
    exact ((hHi.const_mul q).mul (measurable_wnnIncr B k _ _)).sub
      (((hHi.pow_const 2).const_mul _).mul_const _)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (q * I ω - q ^ 2 / 2 * Q ω)))) := by
    filter_upwards [hI, hQ] with ω hIω hQω
    refine ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp ?_)
    simp_rw [sum_unifStepLog]
    exact (hIω.const_mul q).sub (hQω.const_mul _)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (q * I ω - q ^ 2 / 2 * Q ω)) ∂P
      = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P :=
        lintegral_congr_ae (hlim.mono fun ω hω => hω.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hfm
    _ = 1 := by simp_rw [hint]; exact liminf_const 1

end SignatureVolatility

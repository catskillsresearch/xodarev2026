module

public import SignatureVolatility.ItoCalculusKit.ItoIncrement
public import SignatureVolatility.ItoCalculusKit.EvenTransform


@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SignatureVolatility

/-!
# Even-moment bounds for the Itô integral against any Brownian coordinate

For `q ≥ 2`, an adapted integrand `H` on `[0, T]` with `‖H_v - H_u‖_{2q}² ≤ L (v - u)`
(`HolderAdaptedEven`) has a raw Itô integral `X_t = itoIntegral_process B k H 0 t` which is the
almost-sure limit of its uniform Riemann sums, lies in `L^{2q}`, and satisfies
* `‖X_t‖_{2q}² ≤ C_q A t^{e+1}/(e+1)` when `‖H_u‖_{2q}² ≤ A u^e` (`nrm_itoIntegral_process_le`);
* `‖X_v - X_u‖_{2q}² ≤ C_q M (v - u)` when `‖H_u‖_{2q}² ≤ M` (`nrm_itoIntegral_process_sub_le`),

with `C_q = evenConst q · ‖G‖_{2q}²`.
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Adapted `L^{2q}` integrand with `‖H_v - H_u‖_{2q}² ≤ L (v - u)` on `[0, t]`. -/
structure HolderAdaptedEven (B : MultiBrownian Ω P d) (q : ℕ) (H : ℝ → Ω → ℝ) (t L : ℝ) :
    Prop where
  L_nonneg : 0 ≤ L
  meas : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u)
  memLp : ∀ u, 0 ≤ u → u ≤ t → MemLp (H u) (2 * q : ℕ) P
  holder : ∀ u v, 0 ≤ u → u ≤ v → v ≤ t →
    nrm q (∫ ω, (H v ω - H u ω) ^ (2 * q) ∂P) ≤ L * (v - u)

lemma HolderAdaptedEven.mono {B : MultiBrownian Ω P d} {q : ℕ} {H : ℝ → Ω → ℝ} {t L : ℝ}
    (hH : HolderAdaptedEven B q H t L) {s : ℝ} (hst : s ≤ t) : HolderAdaptedEven B q H s L :=
  ⟨hH.L_nonneg, fun u h0 hu => hH.meas u h0 (hu.trans hst),
    fun u h0 hu => hH.memLp u h0 (hu.trans hst),
    fun u v h0 huv hv => hH.holder u v h0 huv (hv.trans hst)⟩

/-- Lyapunov: `𝔼 X⁴ ≤ ‖X‖_{2q}⁴` for `q ≥ 2`. -/
lemma integral_pow_four_le_nrm {q : ℕ} (hq : 2 ≤ q) {X : Ω → ℝ} (hX : MemLp X (2 * q : ℕ) P) :
    ∫ ω, X ω ^ 4 ∂P ≤ nrm q (∫ ω, X ω ^ (2 * q) ∂P) ^ 2 := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hA : 0 ≤ ∫ ω, X ω ^ (2 * q) ∂P := integral_nonneg fun ω => hev.pow_nonneg _
  rcases hq.eq_or_lt with rfl | hq2
  · rw [nrm_pow (by norm_num) hA]
  · have hr : (1 : ℝ) < q / 2 := by
      have : (2 : ℝ) < q := by exact_mod_cast hq2
      linarith
    have hpq : ((q : ℝ) / 2).HolderConjugate ((q / 2) / (q / 2 - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hr).mpr rfl
    have hf : MemLp (fun ω => X ω ^ 4) (ENNReal.ofReal (q / 2)) P := by
      have h := hX.norm_rpow_div 4
      have e1 : ((2 * q : ℕ) : ℝ≥0∞) / 4 = ENNReal.ofReal (q / 2) := by
        rw [show ((2 * q : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 * q : ℕ) : ℝ) by simp,
          show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
        congr 1; push_cast; ring
      rw [e1] at h
      refine h.congr_norm (hX.aestronglyMeasurable.pow 4) (ae_of_all _ fun ω => ?_)
      rw [show ((4 : ℝ≥0∞)).toReal = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, norm_pow,
        norm_norm, norm_pow]
    have hg : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal ((q / 2) / (q / 2 - 1))) P :=
      memLp_const 1
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun ω => by positivity)
      (ae_of_all _ fun _ => zero_le_one) hf hg
    simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul, probReal_univ] at h
    have e1 : ∀ ω, (X ω ^ 4) ^ ((q : ℝ) / 2) = X ω ^ (2 * q) := fun ω => by
      rw [show X ω ^ 4 = (X ω ^ 2) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]; ring,
        ← Real.rpow_mul (sq_nonneg _), show ((2 : ℕ) : ℝ) * (q / 2) = ((q : ℕ) : ℝ) by
          push_cast; ring, Real.rpow_natCast, ← pow_mul]
    simp only [e1] at h
    refine h.trans (le_of_eq ?_)
    unfold nrm
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    congr 1
    have : (q : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num

lemma HolderAdaptedEven.toHolderAdapted {B : MultiBrownian Ω P d} {q : ℕ} (hq : 2 ≤ q)
    {H : ℝ → Ω → ℝ} {t L : ℝ} (hH : HolderAdaptedEven B q H t L) :
    HolderAdapted B H t (L ^ 2) := by
  refine ⟨sq_nonneg L, hH.meas, fun u h0 hu => (hH.memLp u h0 hu).mono_exponent (by
    have : (4 : ℝ≥0∞) = ((4 : ℕ) : ℝ≥0∞) := by norm_num
    rw [this]; exact_mod_cast (by omega : 4 ≤ 2 * q)), fun u v h0 huv hv => ?_⟩
  have h := integral_pow_four_le_nrm hq ((hH.memLp v (h0.trans huv) hv).sub (hH.memLp u h0
    (huv.trans hv)))
  refine h.trans ?_
  have hn := hH.holder u v h0 huv hv
  have hn0 : 0 ≤ nrm q (∫ ω, (H v ω - H u ω) ^ (2 * q) ∂P) :=
    nrm_nonneg q (integral_nonneg fun ω => Even.pow_nonneg ⟨q, by ring⟩ _)
  calc nrm q (∫ ω, (H v ω - H u ω) ^ (2 * q) ∂P) ^ 2 ≤ (L * (v - u)) ^ 2 :=
        pow_le_pow_left₀ hn0 (by simpa using hn) 2
    _ = L ^ 2 * (v - u) ^ 2 := by ring

omit [IsProbabilityMeasure P] in
/-- **Fatou for even moments.** -/
lemma integral_pow_even_le_of_tendsto {N : ℕ} (hN : Even N) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g P) (hf : ∀ n, AEMeasurable (f n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hint : ∀ n, Integrable (fun ω => f n ω ^ N) P) {b : ℕ → ℝ} {c : ℝ}
    (hb : ∀ n, ∫ ω, f n ω ^ N ∂P ≤ b n) (hbc : Tendsto b atTop (𝓝 c)) :
    Integrable (fun ω => g ω ^ N) P ∧ ∫ ω, g ω ^ N ∂P ≤ c := by
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal (f n ω ^ N)) atTop
      (𝓝 (ENNReal.ofReal (g ω ^ N))) :=
    hlim.mono fun ω hω => ENNReal.tendsto_ofReal (hω.pow N)
  have hL : ∫⁻ ω, ENNReal.ofReal (g ω ^ N) ∂P ≤ ENNReal.ofReal c :=
    calc ∫⁻ ω, ENNReal.ofReal (g ω ^ N) ∂P
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω ^ N)) atTop ∂P :=
          lintegral_congr_ae (hlim'.mono fun ω hω => hω.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω ^ N) ∂P) atTop :=
          lintegral_liminf_le' fun n => ENNReal.measurable_ofReal.comp_aemeasurable
            ((hf n).pow_const N)
      _ = liminf (fun n => ENNReal.ofReal (∫ ω, f n ω ^ N ∂P)) atTop := by
          congr 1
          funext n
          exact (ofReal_integral_eq_lintegral_ofReal (hint n)
            (ae_of_all _ fun ω => hN.pow_nonneg _)).symm
      _ ≤ liminf (fun n => ENNReal.ofReal (b n)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hb n))
      _ = ENNReal.ofReal c := (ENNReal.tendsto_ofReal hbc).liminf_eq
  have hc : 0 ≤ c := by
    refine ge_of_tendsto hbc (Eventually.of_forall fun n => ?_)
    exact (integral_nonneg fun ω => hN.pow_nonneg _).trans (hb n)
  have hgi : Integrable (fun ω => g ω ^ N) P := by
    refine ⟨hg.pow N, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) (hL.trans_lt ENNReal.ofReal_lt_top)
    rw [Real.enorm_eq_ofReal (hN.pow_nonneg _)]
  refine ⟨hgi, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hc, ofReal_integral_eq_lintegral_ofReal hgi
    (ae_of_all _ fun ω => hN.pow_nonneg _)]
  exact hL

omit [IsProbabilityMeasure P] in
/-- Fatou in squared-norm form: an a.s. limit of sequences with `‖f_n‖_{2q}² ≤ b_n → c` is in
`L^{2q}` with `‖g‖_{2q}² ≤ c`. -/
lemma nrm_le_of_tendsto {q : ℕ} (hq : q ≠ 0) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g P) (hf : ∀ n, MemLp (f n) (2 * q : ℕ) P) [IsFiniteMeasure P]
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) {b : ℕ → ℝ} {c : ℝ}
    (hb : ∀ n, nrm q (∫ ω, f n ω ^ (2 * q) ∂P) ≤ b n) (hbc : Tendsto b atTop (𝓝 c)) :
    MemLp g (2 * q : ℕ) P ∧ nrm q (∫ ω, g ω ^ (2 * q) ∂P) ≤ c := by
  have hev : Even (2 * q) := ⟨q, by ring⟩
  have hb' : ∀ n, ∫ ω, f n ω ^ (2 * q) ∂P ≤ b n ^ q := fun n => by
    have h0 : 0 ≤ ∫ ω, f n ω ^ (2 * q) ∂P := integral_nonneg fun ω => hev.pow_nonneg _
    rw [← nrm_pow hq h0]
    exact pow_le_pow_left₀ (nrm_nonneg q h0) (hb n) q
  have hc : 0 ≤ c := ge_of_tendsto hbc (Eventually.of_forall fun n =>
    (nrm_nonneg q (integral_nonneg fun ω => hev.pow_nonneg _)).trans (hb n))
  obtain ⟨hi, hle⟩ := integral_pow_even_le_of_tendsto hev hg
    (fun n => (hf n).aestronglyMeasurable.aemeasurable) hlim
    (fun n => integrable_pow_of_memLp_evenDeg hev (hf n)) hb' (hbc.pow q)
  exact ⟨memLp_even_of_integrable_pow hg hi,
    nrm_le_of_le_pow hq (integral_nonneg fun ω => hev.pow_nonneg _) hc hle⟩

lemma memLp_unifRiemann_even (B : MultiBrownian Ω P d) (k : Fin d) (q : ℕ) {H : ℝ → Ω → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hmeas : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u))
    (hLp : ∀ u, 0 ≤ u → u ≤ t → MemLp (H u) (2 * q : ℕ) P) {N : ℕ} (hN : 0 < N) :
    MemLp (unifRiemann B k H t N) (2 * q : ℕ) P := by
  have h := memLp_finsetSum' (p := ((2 * q : ℕ) : ℝ≥0∞)) (μ := P) (Finset.range N)
    (f := fun i ω => H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω)
    fun i hi => by
      obtain ⟨h0, h1⟩ := unifGrid_mem ht hN (Finset.mem_range.mp hi).le
      have hstep : (i : ℝ) * (t / (N : ℝ)) ≤ ((i + 1 : ℕ) : ℝ) * (t / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith)
          (div_nonneg ht (Nat.cast_nonneg _))
      exact memLp_mul_wnnIncr_even B k q h0 hstep (hmeas _ h0 h1) (hLp _ h0 h1)
  have hfun : (∑ i ∈ Finset.range N, fun ω => H ((i : ℝ) * (t / (N : ℝ))) ω *
      wnnIncr B k ((i : ℝ) * (t / (N : ℝ))) (((i + 1 : ℕ) : ℝ) * (t / (N : ℝ))) ω) =
      unifRiemann B k H t N := by
    funext ω; simp [unifRiemann]
  rwa [hfun] at h

/-- `a^{e+1} + (e+1) a^e b ≤ (a+b)^{e+1}` for `a, b ≥ 0`. -/
lemma pow_succ_add_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (e : ℕ) :
    a ^ (e + 1) + (e + 1) * a ^ e * b ≤ (a + b) ^ (e + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hab : 0 ≤ a + b := by positivity
    have h1 := mul_le_mul_of_nonneg_left ih hab
    have e1 : (a + b) * (a ^ (e + 1) + (e + 1) * a ^ e * b) =
        a ^ (e + 1 + 1) + ((↑(e + 1) : ℝ) + 1) * a ^ (e + 1) * b + (e + 1) * a ^ e * b ^ 2 := by
      push_cast; ring
    rw [e1] at h1
    have : 0 ≤ (e + 1) * a ^ e * b ^ 2 := by positivity
    have e2 : (a + b) ^ (e + 1 + 1) = (a + b) * (a + b) ^ (e + 1) := by ring
    rw [e2]
    linarith

/-- Left Riemann sums of `u ↦ u^e` on a uniform grid are at most the integral. -/
lemma sum_grid_pow_le (e N : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    ∑ j ∈ Finset.range N, ((j : ℝ) * h) ^ e * h ≤ ((N : ℝ) * h) ^ (e + 1) / (e + 1) := by
  have he : (0 : ℝ) < e + 1 := by positivity
  have hterm : ∀ j ∈ Finset.range N, ((j : ℝ) * h) ^ e * h ≤
      ((((j + 1 : ℕ) : ℝ) * h) ^ (e + 1) - ((j : ℝ) * h) ^ (e + 1)) / (e + 1) := by
    intro j _
    rw [le_div_iff₀ he]
    have := pow_succ_add_ge (mul_nonneg (Nat.cast_nonneg j) hh) hh e
    have e1 : ((j + 1 : ℕ) : ℝ) * h = (j : ℝ) * h + h := by push_cast; ring
    rw [e1]; linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_div, Finset.sum_range_sub (fun j : ℕ => ((j : ℝ) * h) ^ (e + 1))]
  simp

/-- The constant `C_q = evenConst q · ‖G‖_{2q}²`. -/
noncomputable def itoEvenConst (q : ℕ) : ℝ := evenConst q * nrm q (gaussMoment q)

lemma itoEvenConst_nonneg {q : ℕ} (hq : 2 ≤ q) : 0 ≤ itoEvenConst q :=
  mul_nonneg (by linarith [one_le_evenConst hq]) (nrm_nonneg q (gaussMoment_nonneg q))

/-- **Moment bound for uniform Itô–Riemann sums** with a power profile. -/
theorem nrm_unifRiemann_le (B : MultiBrownian Ω P d) (k : Fin d) {q : ℕ} (hq : 2 ≤ q)
    {H : ℝ → Ω → ℝ} {t A : ℝ} {e : ℕ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hmeas : ∀ u, 0 ≤ u → u ≤ t → Measurable[(pathFiltration B).σAlg u] (H u))
    (hLp : ∀ u, 0 ≤ u → u ≤ t → MemLp (H u) (2 * q : ℕ) P)
    (hmom : ∀ u, 0 ≤ u → u ≤ t → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ A * u ^ e)
    {N : ℕ} (hN : 0 < N) :
    nrm q (∫ ω, unifRiemann B k H t N ω ^ (2 * q) ∂P) ≤
      itoEvenConst q * (A * (t ^ (e + 1) / (e + 1))) := by
  set δ := t / (N : ℝ) with hδ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 ≤ δ := div_nonneg ht hNr.le
  have hτmono : Monotone fun i : ℕ => (i : ℝ) * δ := fun i j hij =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ0
  have hgrid : ∀ j < N, 0 ≤ (j : ℝ) * δ ∧ (j : ℝ) * δ ≤ t := fun j hj =>
    unifGrid_mem ht hN hj.le
  have hT := nrm_transform_le B k hq (τ := fun i : ℕ => (i : ℝ) * δ) (by simp) hτmono
    (fun i => H ((i : ℝ) * δ)) N (fun j hj => hmeas _ (hgrid j hj).1 (hgrid j hj).2)
    (fun j hj => hLp _ (hgrid j hj).1 (hgrid j hj).2)
  have hsum : ∑ j ∈ Finset.range N, nrm q (∫ ω, H ((j : ℝ) * δ) ω ^ (2 * q) ∂P) *
      (((j + 1 : ℕ) : ℝ) * δ - (j : ℝ) * δ) ≤ A * (t ^ (e + 1) / (e + 1)) := by
    have hterm : ∀ j ∈ Finset.range N,
        nrm q (∫ ω, H ((j : ℝ) * δ) ω ^ (2 * q) ∂P) * (((j + 1 : ℕ) : ℝ) * δ - (j : ℝ) * δ) ≤
          A * (((j : ℝ) * δ) ^ e * δ) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have e1 : ((j + 1 : ℕ) : ℝ) * δ - (j : ℝ) * δ = δ := by push_cast; ring
      rw [e1, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hmom _ (hgrid j hj').1 (hgrid j hj').2) hδ0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((sum_grid_pow_le e N hδ0).trans (le_of_eq ?_)) hA
    rw [hδ]; field_simp
  have hC := itoEvenConst_nonneg hq
  unfold itoEvenConst
  have hsimp : unifRiemann B k H t N = fun ω => ∑ j ∈ Finset.range N,
      H ((j : ℝ) * δ) ω * wnnIncr B k ((j : ℝ) * δ) (((j + 1 : ℕ) : ℝ) * δ) ω := rfl
  rw [hsimp]
  refine hT.trans ?_
  unfold itoEvenConst at hC
  exact mul_le_mul_of_nonneg_left hsum hC

private lemma indicator_step_le_even {u x y : ℝ} (hxy : x ≤ y) :
    (if u ≤ x then y - x else 0) ≤ max (y - u) 0 - max (x - u) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith
  · have : max (x - u) 0 = 0 := max_eq_right (by linarith)
    rw [this, sub_zero]
    exact le_max_right _ _

section HorizonEven

variable (B : MultiBrownian Ω P d) (k : Fin d) {q : ℕ} {H : ℝ → Ω → ℝ} {t L Mq : ℝ}

lemma measurable_horizonStep_even (hH : HolderAdaptedEven B q H t L) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (hsv : s < v) :
    Measurable[(pathFiltration B).σAlg s] (horizonStep H u v N s) ∧
      MemLp (horizonStep H u v N s) (2 * q : ℕ) P := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hs.trans_lt hsv
  have hleft : ∀ a, 0 < a → s < a → a ≤ t →
      Measurable[(pathFiltration B).σAlg s] (H ((⌊s / (a / (N : ℝ))⌋₊ : ℝ) * (a / (N : ℝ)))) ∧
        MemLp (H ((⌊s / (a / (N : ℝ))⌋₊ : ℝ) * (a / (N : ℝ)))) (2 * q : ℕ) P := by
    intro a ha hsa hat
    obtain ⟨h0, h1, -⟩ := floor_mul_mem (div_pos ha hNr) hs
    exact ⟨(hH.meas _ h0 (h1.trans (hsa.le.trans hat))).mono ((pathFiltration B).mono h1) le_rfl,
      hH.memLp _ h0 (h1.trans (hsa.le.trans hat))⟩
  have hfun : horizonStep H u v N s = fun ω =>
      if s < u then H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω -
          H ((⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ))) ω
      else H ((⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))) ω :=
    funext fun ω => horizonStep_eq hu huv hN hs hsv ω
  rw [hfun]
  by_cases hsu : s < u
  · simp only [hsu, ↓reduceIte]
    have hA := hleft v hv hsv hvt
    have hB := hleft u (hs.trans_lt hsu) hsu (huv.trans hvt)
    exact ⟨hA.1.sub hB.1, hA.2.sub hB.2⟩
  · simp only [hsu, ↓reduceIte]
    exact hleft v hv hsv hvt

lemma nrm_integral_horizonStep_le (hH : HolderAdaptedEven B q H t L)
    (hM : ∀ u, 0 ≤ u → u ≤ t → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ Mq) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) (hsv : s < v) :
    nrm q (∫ ω, horizonStep H u v N s ω ^ (2 * q) ∂P) ≤
      L * (v / (N : ℝ)) + (if u ≤ s then Mq else 0) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : 0 < v := hs.trans_lt hsv
  have hL := hH.L_nonneg
  simp_rw [horizonStep_eq hu huv hN hs hsv]
  obtain ⟨hv0, hv1, hv2⟩ := floor_mul_mem (div_pos hv hNr) hs
  by_cases hsu : s < u
  · have hu0 : 0 < u := hs.trans_lt hsu
    obtain ⟨hu0', hu1, hu2⟩ := floor_mul_mem (div_pos hu0 hNr) hs
    simp only [hsu, ↓reduceIte, not_le.mpr hsu, add_zero]
    set a := (⌊s / (v / (N : ℝ))⌋₊ : ℝ) * (v / (N : ℝ))
    set b := (⌊s / (u / (N : ℝ))⌋₊ : ℝ) * (u / (N : ℝ))
    have hΔ : u / (N : ℝ) ≤ v / (N : ℝ) := div_le_div_of_nonneg_right huv hNr.le
    rcases le_total b a with hba | hab'
    · refine (hH.holder b a hu0' hba (hv1.trans (hsv.le.trans hvt))).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hL
    · have h := hH.holder a b hv0 hab' (hu1.trans (hsu.le.trans (huv.trans hvt)))
      have heq : ∫ ω, (H a ω - H b ω) ^ (2 * q) ∂P = ∫ ω, (H b ω - H a ω) ^ (2 * q) ∂P := by
        congr 1; funext ω
        rw [show H a ω - H b ω = -(H b ω - H a ω) by ring, Even.neg_pow ⟨q, by ring⟩]
      rw [heq]
      refine h.trans (mul_le_mul_of_nonneg_left (by linarith) hL)
  · simp only [hsu, ↓reduceIte, not_lt.mp hsu]
    have h := hM _ hv0 (hv1.trans (hsv.le.trans hvt))
    have : 0 ≤ L * (v / (N : ℝ)) := by positivity
    linarith

/-- **Moment of the difference of uniform sums over two horizons** `u < v ≤ t`. -/
theorem nrm_unifRiemann_sub_horizon_le (hq : 2 ≤ q) (hH : HolderAdaptedEven B q H t L)
    (hM : ∀ u, 0 ≤ u → u ≤ t → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ Mq) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvt : v ≤ t) {N : ℕ} (hN : 0 < N) :
    nrm q (∫ ω, (unifRiemann B k H v N ω - unifRiemann B k H u N ω) ^ (2 * q) ∂P) ≤
      itoEvenConst q * (L * (v / (N : ℝ)) * v + Mq * (v - u)) := by
  have hq0 : q ≠ 0 := by omega
  have hv : 0 < v := hu.trans_lt huv
  have hMq : 0 ≤ Mq := (nrm_nonneg q (integral_nonneg fun ω =>
    Even.pow_nonneg ⟨q, by ring⟩ _)).trans (hM 0 le_rfl (hu.trans (huv.le.trans hvt)))
  set δ : ℕ → ℝ := fun M => v / ((M + 1 : ℕ) : ℝ) with hδdef
  have hδ : ∀ M, 0 < δ M := fun M => div_pos hv (by positivity)
  have hgrid : ∀ M i : ℕ, i < M + 1 → 0 ≤ (i : ℝ) * δ M ∧ (i : ℝ) * δ M < v := by
    intro M i hi
    refine ⟨by have := hδ M; positivity, ?_⟩
    have h1 : (i : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hi
    calc (i : ℝ) * δ M < ((M + 1 : ℕ) : ℝ) * δ M := mul_lt_mul_of_pos_right h1 (hδ M)
      _ = v := by simp only [hδdef]; field_simp
  set F : ℕ → Ω → ℝ := fun M ω => ∑ i ∈ Finset.range (M + 1),
    horizonStep H u v N ((i : ℝ) * δ M) ω *
      wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω with hFdef
  have hlim : ∀ ω, Tendsto (fun M => F M ω) atTop
      (𝓝 (unifRiemann B k H v N ω - unifRiemann B k H u N ω)) := by
    intro ω
    have h1 := tendsto_fineStepSum B k hv.le le_rfl N (fun j => H ((j : ℝ) * (v / (N : ℝ))) ω) ω
    have h2 := tendsto_fineStepSum B k hu huv.le N (fun j => H ((j : ℝ) * (u / (N : ℝ))) ω) ω
    refine (h1.sub h2).congr fun M => ?_
    simp only [hFdef, horizonStep, sub_mul, Finset.sum_sub_distrib, hδdef]
  have hmeasF : ∀ M i : ℕ, i < M + 1 →
      Measurable[(pathFiltration B).σAlg ((i : ℝ) * δ M)] (horizonStep H u v N ((i : ℝ) * δ M)) ∧
        MemLp (horizonStep H u v N ((i : ℝ) * δ M)) (2 * q : ℕ) P := fun M i hi =>
    measurable_horizonStep_even B hH hu huv.le hvt hN (hgrid M i hi).1 (hgrid M i hi).2
  have hτmono : ∀ M, Monotone fun i : ℕ => (i : ℝ) * δ M := fun M i j hij =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (hδ M).le
  have hFL : ∀ M, MemLp (F M) (2 * q : ℕ) P := by
    intro M
    have h := memLp_finsetSum' (p := ((2 * q : ℕ) : ℝ≥0∞)) (μ := P) (Finset.range (M + 1))
      (f := fun i ω => horizonStep H u v N ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) fun i hi =>
      memLp_mul_wnnIncr_even B k q (hgrid M i (Finset.mem_range.mp hi)).1
        (hτmono M (Nat.le_succ i)) (hmeasF M i (Finset.mem_range.mp hi)).1
        (hmeasF M i (Finset.mem_range.mp hi)).2
    have hfun : (∑ i ∈ Finset.range (M + 1), fun ω => horizonStep H u v N ((i : ℝ) * δ M) ω *
        wnnIncr B k ((i : ℝ) * δ M) (((i + 1 : ℕ) : ℝ) * δ M) ω) = F M := by
      funext ω; simp [hFdef]
    rwa [hfun] at h
  have hC := itoEvenConst_nonneg hq
  have hbound : ∀ M, nrm q (∫ ω, F M ω ^ (2 * q) ∂P) ≤
      itoEvenConst q * (L * (v / (N : ℝ)) * v + Mq * (v - u)) := by
    intro M
    have hT := nrm_transform_le B k hq (τ := fun i : ℕ => (i : ℝ) * δ M)
      (by simp) (hτmono M) (fun i => horizonStep H u v N ((i : ℝ) * δ M)) (M + 1)
      (fun j hj => (hmeasF M j hj).1) (fun j hj => (hmeasF M j hj).2)
    refine hT.trans ?_
    unfold itoEvenConst
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hterm : ∀ i ∈ Finset.range (M + 1),
        nrm q (∫ ω, horizonStep H u v N ((i : ℝ) * δ M) ω ^ (2 * q) ∂P) *
          (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) ≤
        L * (v / (N : ℝ)) * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) +
          Mq * (max (((i + 1 : ℕ) : ℝ) * δ M - u) 0 - max ((i : ℝ) * δ M - u) 0) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hstep : 0 ≤ ((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M :=
        sub_nonneg.mpr (hτmono M (Nat.le_succ i))
      have hs := nrm_integral_horizonStep_le B hH hM hu huv.le hvt hN (hgrid M i hi').1
        (hgrid M i hi').2
      have hind := indicator_step_le_even (u := u) (hτmono M (Nat.le_succ i))
      calc _ ≤ (L * (v / (N : ℝ)) + (if u ≤ (i : ℝ) * δ M then Mq else 0)) *
            (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) := mul_le_mul_of_nonneg_right hs hstep
        _ = L * (v / (N : ℝ)) * (((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M) +
            Mq * (if u ≤ (i : ℝ) * δ M then
              ((i + 1 : ℕ) : ℝ) * δ M - (i : ℝ) * δ M else 0) := by
            split_ifs <;> ring
        _ ≤ _ := by gcongr
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_range_sub (fun i : ℕ => (i : ℝ) * δ M),
      Finset.sum_range_sub (fun i : ℕ => max ((i : ℝ) * δ M - u) 0)]
    have hvM : ((M + 1 : ℕ) : ℝ) * δ M = v := by simp only [hδdef]; field_simp
    simp only [hvM, Nat.cast_zero, zero_mul, sub_zero, zero_sub]
    rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
  have hRm : AEStronglyMeasurable (fun ω => unifRiemann B k H v N ω -
      unifRiemann B k H u N ω) P :=
    ((memLp_unifRiemann_even B k q hv.le (fun w h0 h1 => hH.meas w h0 (h1.trans hvt))
      (fun w h0 h1 => hH.memLp w h0 (h1.trans hvt)) hN).sub
      (memLp_unifRiemann_even B k q hu (fun w h0 h1 => hH.meas w h0 (h1.trans (huv.le.trans hvt)))
      (fun w h0 h1 => hH.memLp w h0 (h1.trans (huv.le.trans hvt))) hN)).aestronglyMeasurable
  exact (nrm_le_of_tendsto hq0 hRm hFL (ae_of_all _ hlim) hbound tendsto_const_nhds).2

end HorizonEven

section Limit

variable (B : MultiBrownian Ω P d) (k : Fin d) {q : ℕ} {H : ℝ → Ω → ℝ} {T L : ℝ}

/-- The raw Itô integral against coordinate `k` is the a.s. limit of its uniform sums. -/
lemma ae_tendsto_itoIntegral_process (hq : 2 ≤ q) (hH : HolderAdaptedEven B q H T L) {t : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H t (n + 1) ω) atTop
      (𝓝 (itoIntegral_process B k H 0 t ω)) := by
  obtain ⟨Y, -, -, hY⟩ := exists_ae_tendsto_unifRiemann B k ht
    ((hH.mono htT).toHolderAdapted hq)
  filter_upwards [hY] with ω hω
  have hraw : itoIntegral_process B k H 0 t ω =
      limUnder atTop fun n : ℕ => unifRiemann B k H t (n + 1) ω := by
    simp only [itoIntegral_process, ht, ↓reduceDIte]
    congr 1
    funext n
    rw [itoRiemann_process_eq_unifRiemann]
  rw [hraw, hω.limUnder_eq]
  exact hω

/-- **`L^{2q}` moment of the raw Itô integral** with a power profile. -/
theorem nrm_itoIntegral_process_le (hq : 2 ≤ q) (hH : HolderAdaptedEven B q H T L) {A : ℝ}
    {e : ℕ} (hA : 0 ≤ A)
    (hmom : ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ A * u ^ e) {t : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) :
    MemLp (fun ω => itoIntegral_process B k H 0 t ω) (2 * q : ℕ) P ∧
      nrm q (∫ ω, itoIntegral_process B k H 0 t ω ^ (2 * q) ∂P) ≤
        itoEvenConst q * (A * (t ^ (e + 1) / (e + 1))) := by
  have hlim := ae_tendsto_itoIntegral_process B k hq hH ht htT
  have hL : ∀ n : ℕ, MemLp (unifRiemann B k H t (n + 1)) (2 * q : ℕ) P := fun n =>
    memLp_unifRiemann_even B k q ht (fun w h0 h1 => hH.meas w h0 (h1.trans htT))
      (fun w h0 h1 => hH.memLp w h0 (h1.trans htT)) n.succ_pos
  have hg : AEStronglyMeasurable (fun ω => itoIntegral_process B k H 0 t ω) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hL n).aestronglyMeasurable) hlim
  exact nrm_le_of_tendsto (by omega) hg hL hlim
    (fun n => nrm_unifRiemann_le B k hq ht hA (fun w h0 h1 => hH.meas w h0 (h1.trans htT))
      (fun w h0 h1 => hH.memLp w h0 (h1.trans htT))
      (fun w h0 h1 => hmom w h0 (h1.trans htT)) n.succ_pos) tendsto_const_nhds

/-- **`L^{2q}` time increments of the raw Itô integral.** -/
theorem nrm_itoIntegral_process_sub_le (hq : 2 ≤ q) (hH : HolderAdaptedEven B q H T L)
    {Mq : ℝ} (hM : ∀ u, 0 ≤ u → u ≤ T → nrm q (∫ ω, H u ω ^ (2 * q) ∂P) ≤ Mq) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    nrm q (∫ ω, (itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω) ^ (2 * q)
      ∂P) ≤ itoEvenConst q * Mq * (v - u) := by
  have hq0 : q ≠ 0 := by omega
  rcases huv.eq_or_lt with rfl | hlt
  · simp only [sub_self, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, hq0,
      not_false_eq_true, zero_pow, integral_zero, mul_zero, nrm_zero q hq0, le_refl]
  have hv : 0 < v := hu.trans_lt hlt
  have hlv := ae_tendsto_itoIntegral_process B k hq hH hv.le hvT
  have hlu := ae_tendsto_itoIntegral_process B k hq hH hu (huv.trans hvT)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω) atTop
      (𝓝 (itoIntegral_process B k H 0 v ω - itoIntegral_process B k H 0 u ω)) := by
    filter_upwards [hlv, hlu] with ω h1 h2
    exact h1.sub h2
  have hfL : ∀ n : ℕ, MemLp (fun ω => unifRiemann B k H v (n + 1) ω -
      unifRiemann B k H u (n + 1) ω) (2 * q : ℕ) P := fun n =>
    (memLp_unifRiemann_even B k q hv.le (fun w h0 h1 => hH.meas w h0 (h1.trans hvT))
      (fun w h0 h1 => hH.memLp w h0 (h1.trans hvT)) n.succ_pos).sub
    (memLp_unifRiemann_even B k q hu (fun w h0 h1 => hH.meas w h0 (h1.trans (huv.trans hvT)))
      (fun w h0 h1 => hH.memLp w h0 (h1.trans (huv.trans hvT))) n.succ_pos)
  have hg : AEStronglyMeasurable (fun ω => itoIntegral_process B k H 0 v ω -
      itoIntegral_process B k H 0 u ω) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfL n).aestronglyMeasurable) hlim
  have hbc : Tendsto (fun n : ℕ => itoEvenConst q * (L * (v / ((n + 1 : ℕ) : ℝ)) * v +
      Mq * (v - u))) atTop (𝓝 (itoEvenConst q * Mq * (v - u))) := by
    have h0 : Tendsto (fun n : ℕ => v / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat v).comp (tendsto_add_atTop_nat 1)
      exact h.congr fun n => by simp
    have h1 := ((tendsto_const_nhds (x := L)).mul h0).mul_const v
    have h2 := ((h1.add_const (Mq * (v - u))).const_mul (itoEvenConst q))
    convert h2 using 2
    ring
  exact (nrm_le_of_tendsto hq0 hg hfL hlim
    (fun n => nrm_unifRiemann_sub_horizon_le B k hq hH (fun w h0 h1 => hM w h0 h1) hu hlt hvT
      n.succ_pos) hbc).2

end Limit

end SignatureVolatility

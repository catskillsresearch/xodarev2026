module

public import SignatureVolatility.SignatureRiccatiKit.ComplexTilt
public import SignatureVolatility.ProlongedBrownianSetup.ItoWordIntegral
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ItoCalculusKit.ItoIncrementEven
public import SignatureVolatility.ItoCalculusKit.RiemannConvergence
public import SignatureVolatility.ItoCalculusKit.LevelBounds
public import SignatureVolatility.SignatureRiccatiKit.LintegralExpShifted
public import SignatureVolatility.ItoCalculusKit.ItoOrthogonal
public import SignatureVolatility.ItoCalculusKit.CrossVariation
public import SignatureVolatility.ItoCalculusKit.ItoIncrement
public import SignatureVolatility.ItoCalculusKit.FourthMoment
public import SignatureVolatility.ItoCalculusKit.MartingaleTransform
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# C2. Closed form for the tilted expectation of every Itô word integral
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal NNReal

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Elementary Vitali: a.s. convergence + uniform `L²` bound ⇒ integral convergence. -/
private lemma tendsto_integral_of_ae_tendsto_of_L2_bdd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℕ → Ω → E} {g : Ω → E} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n, MemLp (f n) 2 P) (hg : MemLp g 2 P)
    (hbd : ∀ n, ∫ ω, ‖f n ω - g ω‖ ^ 2 ∂P ≤ M)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, g ω ∂P)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := 2 * (M + 1) / ε
  have hR : 0 < R := by positivity
  have hsm (n : ℕ) : AEStronglyMeasurable (fun ω => min ‖f n ω - g ω‖ R) P :=
    continuous_min.comp_aestronglyMeasurable
      ((AEStronglyMeasurable.norm
          (AEStronglyMeasurable.sub (hf n).aestronglyMeasurable
            hg.aestronglyMeasurable)).prodMk aestronglyMeasurable_const)
  have hmin_lim : Tendsto (fun n => ∫ ω, min ‖f n ω - g ω‖ R ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => (R : ℝ))
      (fun n => hsm n) (integrable_const R)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (le_min (norm_nonneg _) hR.le)]
        exact min_le_right _ _)
      (by
        filter_upwards [hae] with ω hω
        have h0 : Tendsto (fun n => ‖f n ω - g ω‖) atTop (𝓝 0) := by
          simpa [sub_self] using (hω.sub (tendsto_const_nhds (x := g ω))).norm
        have : Tendsto (fun n => min ‖f n ω - g ω‖ R) atTop (𝓝 (min (0 : ℝ) R)) :=
          h0.min tendsto_const_nhds
        simpa [min_eq_left hR.le] using this)
    simpa using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmin_lim) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hMR : M / R < ε / 2 := by
    simp only [R]; field_simp; linarith
  have hmin_lt : ∫ ω, min ‖f n ω - g ω‖ R ∂P < ε / 2 := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun _ => le_min (norm_nonneg _) hR.le)] at h
    exact h
  have hpt : ∀ ω, ‖f n ω - g ω‖ ≤ min ‖f n ω - g ω‖ R + ‖f n ω - g ω‖ ^ 2 / R := fun ω => by
    rcases le_total ‖f n ω - g ω‖ R with hle | hge
    · rw [min_eq_left hle]; linarith [div_nonneg (sq_nonneg ‖f n ω - g ω‖) hR.le]
    · rw [min_eq_right hge]
      have : ‖f n ω - g ω‖ ≤ ‖f n ω - g ω‖ ^ 2 / R := by
        rw [le_div_iff₀ hR, sq]; exact mul_le_mul_of_nonneg_left hge (norm_nonneg _)
      linarith
  have hi_min : Integrable (fun ω => min ‖f n ω - g ω‖ R) P :=
    (integrable_const R).mono' (hsm n) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (le_min (norm_nonneg _) hR.le)]; exact min_le_right _ _)
  have hi_sq : Integrable (fun ω => ‖f n ω - g ω‖ ^ 2 / R) P :=
    ((hf n).sub hg).norm.integrable_sq.div_const R
  rw [dist_eq_norm, ← integral_sub ((hf n).integrable one_le_two) (hg.integrable one_le_two)]
  calc ‖∫ ω, (f n ω - g ω) ∂P‖
      ≤ ∫ ω, ‖f n ω - g ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (min ‖f n ω - g ω‖ R + ‖f n ω - g ω‖ ^ 2 / R) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi_min.add hi_sq)
          (ae_of_all _ hpt)
    _ = (∫ ω, min ‖f n ω - g ω‖ R ∂P) + (∫ ω, ‖f n ω - g ω‖ ^ 2 ∂P) / R := by
        rw [integral_add hi_min hi_sq, integral_div]
    _ ≤ (∫ ω, min ‖f n ω - g ω‖ R ∂P) + M / R := by gcongr; exact hbd n
    _ < ε / 2 + ε / 2 := add_lt_add hmin_lt hMR
    _ = ε := add_halves ε


/-- `X ∈ L²` lifts to `(X : ℂ) * E_t(ξ) ∈ L²` by the uniform bound `‖E_t(ξ)‖ = exp(ξ² t / 2)`. -/
private lemma memLp_mul_complexTilt {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (ξ : ℝ) {t : ℝ} {X : Ω → ℝ} (hX : MemLp X 2 P) :
    MemLp (fun ω => (X ω : ℂ) * complexTilt B hd ξ t ω) 2 P := by
  have hXℂ : MemLp (fun ω => (X ω : ℂ)) 2 P :=
    MeasureTheory.MemLp.ofReal (K := ℂ) hX
  have hE : MemLp (fun ω => complexTilt B hd ξ t ω) ⊤ P :=
    MemLp.of_bound (p := ⊤)
      (measurable_complexTilt B hd ξ t).aestronglyMeasurable
      (Real.exp (ξ ^ 2 * t / 2))
      (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B hd ξ t ω))
  exact hXℂ.mul (q := ⊤) hE

theorem integral_itoWordIntegral_mul_complexTilt {d : ℕ}
    (B : MultiBrownian Ω P d) (hd : 0 < d) (ξ : ℝ) (J : Word (d + 1))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (itoWordIntegral B 0 t ω J : ℂ) * complexTilt B hd ξ t ω ∂P =
      if onlyZeroOrOne hd J then
        (Complex.I * (ξ : ℂ)) ^ (countOnes hd J) *
          ((t ^ J.length / (J.length.factorial : ℝ) : ℝ) : ℂ)
      else 0 := by
  induction J generalizing t with
  | nil =>
    simp only [itoWordIntegral_empty, Complex.ofReal_one, one_mul, onlyZeroOrOne, ↓reduceIte,
      countOnes, pow_zero, List.length_nil, Nat.factorial_zero, Nat.cast_one, div_one,
      Complex.ofReal_one, mul_one]
    have hlaw := hasLaw_wnnIncr B ⟨0, hd⟩ le_rfl ht
    have hW' (ω : Ω) : MultiBrownian.W B t ω ⟨0, hd⟩ = wnnIncr B ⟨0, hd⟩ 0 t ω := by
      simp [wnnIncr_eq_W, MultiBrownian.W_zero]
    simp only [complexTilt, hW']
    have hcomp := hlaw.integral_comp
      (f := fun x : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * t / 2 : ℝ) : ℂ)))
      (by fun_prop : Continuous _).aestronglyMeasurable
    simp only [Function.comp_def] at hcomp; rw [hcomp]
    have hcast : ((Real.toNNReal (t - 0) : ℝ≥0) : ℝ) = t := by
      rw [sub_zero, Real.coe_toNNReal _ ht]
    simpa [hcast, sub_zero, max_eq_left ht] using
      integral_exp_complexTilt_gaussianReal ξ (Real.toNNReal (t - 0))
  | cons j K ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · -- Case `j = 0`: uniform left Riemann sums + `tendsto_integral_of_ae_tendsto_of_L2_bdd` (no Fubini!)
      set E_bd : ℝ := Real.exp (ξ ^ 2 * t / 2)
      let L : ℕ → Ω → ℝ := fun n ω =>
        ∑ m ∈ Finset.range (n + 1),
          itoWordIntegral B 0 ((m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω K * (t / ((n + 1 : ℕ) : ℝ))
      obtain ⟨C, hC0, hC⟩ := exists_integral_sq_itoWordIntegral_le B ht K
      -- L² bound for `L n` via `integral_riemannSum_pow_le` (`q = 1`)
      have hL_Lp : ∀ n, MemLp (L n) 2 P ∧ ∫ ω, L n ω ^ 2 ∂P ≤ t ^ 2 * C := fun n => by
        have hΔ0 : 0 ≤ t / ((n + 1 : ℕ) : ℝ) := div_nonneg ht (by positivity)
        have hgrid : ∀ m < n + 1, 0 ≤ (m : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) ∧
            (m : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) ≤ t := fun m hm =>
          unifGrid_mem ht n.succ_pos hm.le
        have h := integral_riemannSum_pow_le (q := 1) one_ne_zero
          (H := fun s ω => itoWordIntegral B 0 s ω K)
          (fun m => (m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) (n + 1) hΔ0
          (fun m hm => by
            simpa using (memLp_itoWordIntegral B (hgrid m hm).1 K le_rfl).mono_exponent (by norm_num))
        refine ⟨by simpa [L] using h.1, ?_⟩
        have hNΔ : ((n + 1 : ℕ) : ℝ) * (t / ((n + 1 : ℕ) : ℝ)) = t := by field_simp
        have hle := h.2
        simp only [Nat.mul_one, Nat.reduceSub, pow_one, hNΔ] at hle
        refine hle.trans ?_
        calc t * ∑ m ∈ Finset.range (n + 1),
              (∫ ω, itoWordIntegral B 0 ((m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω K ^ 2 ∂P) *
                (t / ((n + 1 : ℕ) : ℝ))
            ≤ t * ∑ _m ∈ Finset.range (n + 1), C * (t / ((n + 1 : ℕ) : ℝ)) := by
              gcongr with m hm
              exact hC _ (hgrid m (Finset.mem_range.mp hm)).1 (hgrid m (Finset.mem_range.mp hm)).2
          _ = t ^ 2 * C := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              calc t * (((n + 1 : ℕ) : ℝ) * (C * (t / ((n + 1 : ℕ) : ℝ))))
                  = t * (C * (((n + 1 : ℕ) : ℝ) * (t / ((n + 1 : ℕ) : ℝ)))) := by ring
                _ = t * (C * t) := by rw [hNΔ]
                _ = t ^ 2 * C := by ring
      have hg_Lp : MemLp (fun ω => itoWordIntegral B 0 t ω (0 :: K)) 2 P :=
        (memLp_itoWordIntegral B ht (0 :: K) le_rfl).mono_exponent (by norm_num)
      have hae_L : ∀ᵐ ω ∂P, Tendsto (fun n => (L n ω : ℂ) * complexTilt B hd ξ t ω) atTop
          (𝓝 ((itoWordIntegral B 0 t ω (0 :: K) : ℂ) * complexTilt B hd ξ t ω)) := by
        filter_upwards [ae_itoWordIntegral_time_cons B ht, ae_continuousOn_itoWordIntegral B ht]
          with ω h0 hc
        rw [h0 K]
        have hlim := tendsto_lebRiemann_of_continuousOn ht (hc K)
        have hlim' : Tendsto (fun n => L n ω) atTop (𝓝 (∫ s in (0 : ℝ)..t, itoWordIntegral B 0 s ω K)) :=
          hlim.congr fun n => by
            refine Finset.sum_congr rfl fun m _ => ?_; push_cast; rfl
        exact ((Complex.continuous_ofReal.tendsto _).comp hlim').mul_const _
      have hL_tendsto : Tendsto (fun n => ∫ ω, (L n ω : ℂ) * complexTilt B hd ξ t ω ∂P) atTop
          (𝓝 (∫ ω, (itoWordIntegral B 0 t ω (0 :: K) : ℂ) * complexTilt B hd ξ t ω ∂P)) := by
        set M₂ : ℝ := E_bd ^ 2 * (2 * (t ^ 2 * C) + 2 * ∫ ω, itoWordIntegral B 0 t ω (0 :: K) ^ 2 ∂P)
        have hM₂ : 0 ≤ M₂ := by
          have : 0 ≤ ∫ ω, itoWordIntegral B 0 t ω (0 :: K) ^ 2 ∂P :=
            integral_nonneg fun _ => sq_nonneg _
          positivity
        refine tendsto_integral_of_ae_tendsto_of_L2_bdd hM₂
          (fun n => memLp_mul_complexTilt B hd ξ (hL_Lp n).1)
          (memLp_mul_complexTilt B hd ξ hg_Lp)
          (fun n => ?_) hae_L
        have hpt : ∀ ω, ‖(L n ω : ℂ) * complexTilt B hd ξ t ω -
            (itoWordIntegral B 0 t ω (0 :: K) : ℂ) * complexTilt B hd ξ t ω‖ ^ 2 ≤
            E_bd ^ 2 * (2 * L n ω ^ 2 + 2 * itoWordIntegral B 0 t ω (0 :: K) ^ 2) := fun ω => by
          rw [← sub_mul, norm_mul, norm_complexTilt, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, mul_pow, sq_abs]
          have h2 : (L n ω - itoWordIntegral B 0 t ω (0 :: K)) ^ 2 ≤
              2 * L n ω ^ 2 + 2 * itoWordIntegral B 0 t ω (0 :: K) ^ 2 := by
            nlinarith [sq_nonneg (L n ω + itoWordIntegral B 0 t ω (0 :: K))]
          exact mul_le_mul_of_nonneg_right h2 (sq_nonneg E_bd) |>.trans_eq (mul_comm _ _)
        have hintR : Integrable (fun ω => E_bd ^ 2 *
            (2 * L n ω ^ 2 + 2 * itoWordIntegral B 0 t ω (0 :: K) ^ 2)) P :=
          (((hL_Lp n).1.integrable_sq.const_mul 2).add (hg_Lp.integrable_sq.const_mul 2)).const_mul _
        calc ∫ ω, ‖(L n ω : ℂ) * complexTilt B hd ξ t ω -
              (itoWordIntegral B 0 t ω (0 :: K) : ℂ) * complexTilt B hd ξ t ω‖ ^ 2 ∂P
            ≤ ∫ ω, E_bd ^ 2 * (2 * L n ω ^ 2 + 2 * itoWordIntegral B 0 t ω (0 :: K) ^ 2) ∂P :=
              integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hintR (ae_of_all _ hpt)
          _ = E_bd ^ 2 * (2 * ∫ ω, L n ω ^ 2 ∂P + 2 * ∫ ω, itoWordIntegral B 0 t ω (0 :: K) ^ 2 ∂P) := by
              rw [integral_const_mul, integral_add ((hL_Lp n).1.integrable_sq.const_mul 2)
                (hg_Lp.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul]
          _ ≤ M₂ := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              exact add_le_add (mul_le_mul_of_nonneg_left (hL_Lp n).2 (by positivity)) le_rfl
      -- Evaluate `∫ (L n) * E_t` directly via `integral_mul_complexTilt_eq` + `ih`!
      have hL_eval : ∀ n, ∫ ω, (L n ω : ℂ) * complexTilt B hd ξ t ω ∂P =
          if onlyZeroOrOne hd K then
            (Complex.I * (ξ : ℂ)) ^ (countOnes hd K) *
              ((∑ m ∈ Finset.range (n + 1),
                (((m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ^ K.length / (K.length.factorial : ℝ)) *
                  (t / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
          else 0 := fun n => by
        simp only [L, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
        rw [integral_finsetSum]
        · have hterm : ∀ m ∈ Finset.range (n + 1),
              ∫ ω, (itoWordIntegral B 0 ((m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ω K : ℂ) *
                ((t / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * complexTilt B hd ξ t ω ∂P =
              (if onlyZeroOrOne hd K then
                (Complex.I * (ξ : ℂ)) ^ (countOnes hd K) *
                  ((((m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))) ^ K.length / (K.length.factorial : ℝ) *
                    (t / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
              else 0) := by
            intro m hm
            obtain ⟨hs0, hsT⟩ := unifGrid_mem ht n.succ_pos (Finset.mem_range.mp hm).le
            set s := (m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))
            have hpull : (fun ω => (itoWordIntegral B 0 s ω K : ℂ) *
                ((t / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * complexTilt B hd ξ t ω) =
                fun ω => ((t / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                  ((itoWordIntegral B 0 s ω K : ℂ) * complexTilt B hd ξ t ω) := by
              funext ω; ring
            have hXint : Integrable (fun ω => (itoWordIntegral B 0 s ω K : ℂ)) P :=
              Integrable.ofReal
                ((memLp_itoWordIntegral B hs0 K le_rfl).integrable (by norm_num))
            have hshift :
                ∫ ω, (itoWordIntegral B 0 s ω K : ℂ) * complexTilt B hd ξ t ω ∂P =
                ∫ ω, (itoWordIntegral B 0 s ω K : ℂ) * complexTilt B hd ξ s ω ∂P := by
              simpa [Function.comp_def] using
                integral_mul_complexTilt_eq B hd ξ hs0 hsT
                  (Complex.continuous_ofReal.measurable.comp
                    (measurable_itoWordIntegral_pathFiltration B le_rfl hs0 le_rfl K))
                  hXint
            rw [hpull, integral_const_mul, hshift, ih hs0]
            split_ifs <;> push_cast <;> ring
          rw [Finset.sum_congr rfl hterm]
          split_ifs <;> simp [Finset.mul_sum]
        · intro m hm
          obtain ⟨hs0, _⟩ := unifGrid_mem ht n.succ_pos (Finset.mem_range.mp hm).le
          exact (((memLp_itoWordIntegral B hs0 K le_rfl).integrable (by norm_num)).ofReal.mul_const _).mul_bdd
            (measurable_complexTilt B hd ξ t).aestronglyMeasurable
            (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B hd ξ t ω))
      -- Pass `n → ∞` on the closed form via `tendsto_lebRiemann_of_continuousOn`
      have h0ne : (0 : Letter (d + 1)) ≠ firstSpace hd := (firstSpace_ne_zero hd).symm
      simp only [onlyZeroOrOne, decide_true, Bool.true_or, Bool.true_and, countOnes, h0ne,
        ↓reduceIte, zero_add, List.length_cons]
      have hR_lim : Tendsto (fun n => ∫ ω, (L n ω : ℂ) * complexTilt B hd ξ t ω ∂P) atTop
          (𝓝 (if onlyZeroOrOne hd K then
            (Complex.I * (ξ : ℂ)) ^ (countOnes hd K) *
              ((t ^ (K.length + 1) / ((K.length + 1).factorial : ℝ) : ℝ) : ℂ)
          else 0)) := by
        simp_rw [hL_eval]
        split_ifs with hK
        · have hreal := tendsto_lebRiemann_of_continuousOn ht
            (g := fun s : ℝ => s ^ K.length / (K.length.factorial : ℝ))
            (by fun_prop : Continuous _).continuousOn
          have hint : ∫ s in (0 : ℝ)..t, s ^ K.length / (K.length.factorial : ℝ) =
              t ^ (K.length + 1) / ((K.length + 1).factorial : ℝ) := by
            rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero _),
              sub_zero, Nat.factorial_succ, Nat.cast_mul, div_div,
              mul_comm ((K.length + 1 : ℕ) : ℝ)]
            push_cast; ring
          rw [hint] at hreal
          refine (((Complex.continuous_ofReal.tendsto _).comp hreal).const_mul _).congr fun n => ?_
          simp [Complex.ofReal_sum, Complex.ofReal_mul]
        · exact tendsto_const_nhds
      exact tendsto_nhds_unique hL_tendsto hR_lim
    · -- Case `j = k.succ`: uniform Itô–Riemann sums + `tendsto_integral_of_ae_tendsto_of_L2_bdd`
      set E_bd : ℝ := Real.exp (ξ ^ 2 * t / 2)
      have hstep_sum : ∀ (N : ℕ) (hN : 0 < N),
          ∫ ω, (unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t N ω : ℂ) *
              complexTilt B hd ξ t ω ∂P =
            if k = ⟨0, hd⟩ then
              (Complex.I * (ξ : ℂ)) * ∑ m ∈ Finset.range N,
                (∫ ω, (itoWordIntegral B 0 ((m : ℝ) * (t / (N : ℝ))) ω K : ℂ) *
                  complexTilt B hd ξ ((m : ℝ) * (t / (N : ℝ))) ω ∂P) * ((t / (N : ℝ) : ℝ) : ℂ)
            else 0 := by
        intro N hN
        set Δ : ℝ := t / (N : ℝ)
        have hΔ0 : 0 ≤ Δ := div_nonneg ht (Nat.cast_nonneg N)
        unfold unifRiemann
        simp_rw [Complex.ofReal_sum, Finset.sum_mul]
        rw [integral_finsetSum]
        · have hterm : ∀ m ∈ Finset.range N,
              ∫ ω, ((itoWordIntegral B 0 ((m : ℝ) * Δ) ω K *
                  wnnIncr B k ((m : ℝ) * Δ) (((m + 1 : ℕ) : ℝ) * Δ) ω : ℝ) : ℂ) *
                  complexTilt B hd ξ t ω ∂P =
                if k = ⟨0, hd⟩ then
                  (Complex.I * (ξ : ℂ)) *
                    (∫ ω, (itoWordIntegral B 0 ((m : ℝ) * Δ) ω K : ℂ) *
                      complexTilt B hd ξ ((m : ℝ) * Δ) ω ∂P) * (Δ : ℂ)
                else 0 := by
            intro m hm
            have hmN := Finset.mem_range.mp hm
            obtain ⟨hs0, hsT⟩ := unifGrid_mem ht hN hmN.le
            obtain ⟨hu0, huT⟩ := unifGrid_mem ht hN hmN
            set s := (m : ℝ) * Δ
            set u := ((m + 1 : ℕ) : ℝ) * Δ
            have hsu : s ≤ u := by simp only [s, u]; push_cast; nlinarith
            have hsub : u - s = Δ := by simp only [s, u]; push_cast; ring
            have hXu_meas : Measurable[(pathFiltration B).σAlg u]
                (fun ω => ((itoWordIntegral B 0 s ω K * wnnIncr B k s u ω : ℝ) : ℂ)) :=
              Complex.continuous_ofReal.measurable.comp <|
                ((measurable_itoWordIntegral_pathFiltration B le_rfl hs0 le_rfl K).mono
                  ((pathFiltration B).mono hsu) le_rfl).mul
                  (measurable_wnnIncr_pathFiltration B k hs0 hu0 hsu le_rfl)
            have hXu_int : Integrable
                (fun ω => ((itoWordIntegral B 0 s ω K * wnnIncr B k s u ω : ℝ) : ℂ)) P :=
              (integrable_mul_of_memLp_two
                ((memLp_itoWordIntegral B hs0 K le_rfl).mono_exponent (by norm_num))
                ((hasLaw_wnnIncr B k hs0 hsu).memLp (memLp_id_gaussianReal' 2 (by simp)))).ofReal
            rw [integral_mul_complexTilt_eq B hd ξ hu0 huT hXu_meas hXu_int]
            have hfac : (fun ω => ((itoWordIntegral B 0 s ω K * wnnIncr B k s u ω : ℝ) : ℂ) *
                complexTilt B hd ξ u ω) =
                fun ω => ((itoWordIntegral B 0 s ω K : ℂ) * complexTilt B hd ξ s ω) *
                  ((wnnIncr B k s u ω : ℂ) *
                    Complex.exp (Complex.I * (ξ : ℂ) * (wnnIncr B ⟨0, hd⟩ s u ω : ℂ) +
                      ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ))) := by
              funext ω; rw [complexTilt_split B hd ξ s u ω, hsub, Complex.ofReal_mul]; ring
            rw [hfac]
            by_cases hk : k = ⟨0, hd⟩
            · subst hk; simp only [↓reduceIte]
              have hind := (indepFun_pathFiltration_wnnIncr B ⟨0, hd⟩ hsu
                ((Complex.continuous_ofReal.measurable.comp
                  (measurable_itoWordIntegral_pathFiltration B le_rfl hs0 le_rfl K)).mul
                  (measurable_complexTilt_pathFiltration B hd ξ hs0))).comp
                measurable_id (by fun_prop : Measurable fun x : ℝ => (x : ℂ) *
                  Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ)))
              have hfact := hind.integral_fun_mul_eq_mul_integral
                (((Complex.continuous_ofReal.measurable.comp
                    (measurable_itoWordIntegral B 0 s K)).mul
                  (measurable_complexTilt B hd ξ s)).aestronglyMeasurable)
                ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) *
                    Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
                      ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ))).comp_aestronglyMeasurable
                  (measurable_wnnIncr B ⟨0, hd⟩ s u).aestronglyMeasurable)
              simp only [Function.comp_def, id, Pi.mul_apply] at hfact ⊢
              rw [hfact]
              have hcomp := (hasLaw_wnnIncr B ⟨0, hd⟩ hs0 hsu).integral_comp
                (f := fun x : ℝ => (x : ℂ) * Complex.exp
                  (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ)))
                (by fun_prop : Continuous _).aestronglyMeasurable
              simp only [Function.comp_def] at hcomp; rw [hcomp]
              have hcast : ((Real.toNNReal (u - s) : ℝ≥0) : ℝ) = Δ := by
                rw [hsub, Real.coe_toNNReal _ hΔ0]
              rw [show ∫ x : ℝ, (x : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
                  ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ)) ∂(gaussianReal 0 (Real.toNNReal (u - s))) =
                  Complex.I * (ξ : ℂ) * (Δ : ℂ) by
                simpa [hcast] using integral_mul_exp_complexTilt_gaussianReal ξ (Real.toNNReal (u - s))]
              ring
            · simp only [hk, ↓reduceIte]
              have hind_pair := (indepFun_pathFiltration_wnnIncr_pair B hk hsu
                ((Complex.continuous_ofReal.measurable.comp
                  (measurable_itoWordIntegral_pathFiltration B le_rfl hs0 le_rfl K)).mul
                  (measurable_complexTilt_pathFiltration B hd ξ hs0))).comp
                measurable_id (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) *
                  Complex.exp (Complex.I * (ξ : ℂ) * (p.2 : ℂ) + ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ)))
              have hfact := hind_pair.integral_fun_mul_eq_mul_integral
                (((Complex.continuous_ofReal.measurable.comp
                    (measurable_itoWordIntegral B 0 s K)).mul
                  (measurable_complexTilt B hd ξ s)).aestronglyMeasurable)
                ((by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) *
                    Complex.exp (Complex.I * (ξ : ℂ) * (p.2 : ℂ) +
                      ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ))).comp_aestronglyMeasurable
                  ((measurable_wnnIncr B k s u).aestronglyMeasurable.prodMk
                    (measurable_wnnIncr B ⟨0, hd⟩ s u).aestronglyMeasurable))
              simp only [Function.comp_def, id, Pi.mul_apply] at hfact ⊢
              rw [hfact]
              have hind_kk := (indepFun_wnnIncr_wnnIncr B hk s u).comp
                Complex.continuous_ofReal.measurable
                (by fun_prop : Measurable fun x : ℝ =>
                  Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) + ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ)))
              have hfactk := hind_kk.integral_fun_mul_eq_mul_integral
                (Complex.continuous_ofReal.comp_aestronglyMeasurable
                  (measurable_wnnIncr B k s u).aestronglyMeasurable)
                ((by fun_prop : Continuous fun x : ℝ =>
                    Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ) +
                      ((ξ ^ 2 * Δ / 2 : ℝ) : ℂ))).comp_aestronglyMeasurable
                  (measurable_wnnIncr B ⟨0, hd⟩ s u).aestronglyMeasurable)
              simp only [Function.comp_def] at hfactk ⊢
              rw [hfactk]
              have h0 : ∫ ω, (wnnIncr B k s u ω : ℂ) ∂P = 0 := by
                rw [integral_complex_ofReal, integral_wnnIncr B k hs0 hsu, Complex.ofReal_zero]
              rw [h0, zero_mul, mul_zero]
          rw [Finset.sum_congr rfl hterm]
          split_ifs <;> simp [Finset.mul_sum, mul_assoc]
        · intro m hm
          obtain ⟨hs0, _⟩ := unifGrid_mem ht hN (Finset.mem_range.mp hm).le
          have hsu : (m : ℝ) * Δ ≤ ((m + 1 : ℕ) : ℝ) * Δ := by push_cast; nlinarith
          exact (integrable_mul_of_memLp_two
            ((memLp_itoWordIntegral B hs0 K le_rfl).mono_exponent (by norm_num))
            ((hasLaw_wnnIncr B k hs0 hsu).memLp (memLp_id_gaussianReal' 2 (by simp)))).ofReal.mul_bdd
            (measurable_complexTilt B hd ξ t).aestronglyMeasurable
            (ae_of_all _ fun ω => le_of_eq (norm_complexTilt B hd ξ t ω))
      -- Pass `N = n + 1 → ∞` on LHS using `tendsto_integral_of_ae_tendsto_of_L2_bdd`!
      have hL_lim : Tendsto (fun n : ℕ =>
          ∫ ω, (unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t (n + 1) ω : ℂ) *
            complexTilt B hd ξ t ω ∂P) atTop
          (𝓝 (∫ ω, (itoWordIntegral B 0 t ω (k.succ :: K) : ℂ) * complexTilt B hd ξ t ω ∂P)) := by
        by_cases hK : K = []
        · subst hK
          refine tendsto_const_nhds.congr fun n => ?_
          congr 1; funext ω
          simp only [unifRiemann, itoWordIntegral_empty, one_mul, itoWordIntegral_space]
          have := sum_wnnIncr_grid B k (t := t) n ω
          simp only [dynGrid] at this
          convert congrArg (fun r : ℝ => (r : ℂ) * complexTilt B hd ξ t ω) this.symm using 2
          congr 1; refine Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
        · obtain ⟨L, hH⟩ := (levelBound_itoWordIntegral B ht K hK).holderAdaptedEven le_rfl
          have hHA := hH.toHolderAdapted le_rfl
          have hcongr := ae_itoWordIntegral_space_cons B ht k hK ht le_rfl
          have hlim_ae := (itoIntegral_process_of_holderAdapted B k hHA ht).1
          have hae : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
              (unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t (n + 1) ω : ℂ) *
                complexTilt B hd ξ t ω) atTop
              (𝓝 ((itoWordIntegral B 0 t ω (k.succ :: K) : ℂ) * complexTilt B hd ξ t ω)) := by
            filter_upwards [hlim_ae, hcongr] with ω h1 h2
            rw [h2]; exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const _
          have hL4_bd : ∀ n : ℕ, ∫ ω, (unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t
              (n + 1) ω - itoWordIntegral B 0 t ω (k.succ :: K)) ^ 4 ∂P ≤
              16 * (16 * gaussFourthConst * L ^ 2 * t ^ 4) := fun n => by
            set C₀ := 16 * gaussFourthConst * L ^ 2 * t ^ 4
            have hC₀0 : 0 ≤ C₀ := by have := gaussFourthConst_nonneg; positivity
            have hF := integral_pow_four_le_of_tendsto
              (((memLp_unifRiemann B k ht hHA n.succ_pos).sub
                (memLp_itoWordIntegral B ht (k.succ :: K) le_rfl)).aestronglyMeasurable)
              (fun m => ((memLp_unifRiemann B k ht hHA n.succ_pos).sub
                (memLp_unifRiemann B k ht hHA m.succ_pos)).aestronglyMeasurable.aemeasurable)
              (by
                filter_upwards [hlim_ae, hcongr] with ω h1 h2
                simpa [Pi.sub_apply, h2] using
                  (tendsto_const_nhds
                    (x := unifRiemann B k (fun u ω' => itoWordIntegral B 0 u ω' K) t (n + 1) ω)).sub h1)
              (fun m => integrable_pow_of_memLp_four ((memLp_unifRiemann B k ht hHA n.succ_pos).sub
                (memLp_unifRiemann B k ht hHA m.succ_pos)) le_rfl)
              (b := fun m => 8 * (C₀ / ((n + 1 : ℕ) : ℝ) ^ 2) + 8 * (C₀ / ((m + 1 : ℕ) : ℝ) ^ 2))
              (fun m => integral_unifRiemann_sub_le B k ht hHA n.succ_pos m.succ_pos)
              (by
                have h2 : Tendsto (fun m : ℕ => C₀ / ((m + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
                  have := (tendsto_const_nhds (x := C₀)).div_atTop
                    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
                      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
                  simpa [Function.comp_def] using this
                simpa [add_zero] using
                  (tendsto_const_nhds
                    (x := 8 * (C₀ / ((n + 1 : ℕ) : ℝ) ^ 2))).add (h2.const_mul 8))
            refine hF.2.trans ?_
            have hge1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
              have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast n.succ_pos
              nlinarith
            have hpos : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
            have hone : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
              have : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
              nlinarith
            have hle : 8 / ((n : ℝ) + 1) ^ 2 ≤ 16 := by
              calc 8 / ((n : ℝ) + 1) ^ 2
                  ≤ 8 / 1 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hone
                _ = 8 := by ring
                _ ≤ 16 := by norm_num
            calc 8 * (C₀ / ((n : ℝ) + 1) ^ 2)
                = (8 / ((n : ℝ) + 1) ^ 2) * C₀ := by ring
              _ ≤ 16 * C₀ := mul_le_mul_of_nonneg_right hle hC₀0
          set M₂ := E_bd ^ 2 * Real.sqrt (16 * (16 * gaussFourthConst * L ^ 2 * t ^ 4))
          have hM₂0 : 0 ≤ M₂ := by positivity
          refine tendsto_integral_of_ae_tendsto_of_L2_bdd (M := M₂) hM₂0
            (fun n => memLp_mul_complexTilt B hd ξ
              ((memLp_unifRiemann B k ht hHA n.succ_pos).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)))
            (memLp_mul_complexTilt B hd ξ
              ((memLp_itoWordIntegral B ht (k.succ :: K) le_rfl).mono_exponent
                (by norm_num : (2 : ℝ≥0∞) ≤ 4)))
            (fun n => ?_) hae
          have hrew : (fun ω => ‖(unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t
              (n + 1) ω : ℂ) * complexTilt B hd ξ t ω -
              (itoWordIntegral B 0 t ω (k.succ :: K) : ℂ) * complexTilt B hd ξ t ω‖ ^ 2) =
              fun ω => E_bd ^ 2 * (unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t
                (n + 1) ω - itoWordIntegral B 0 t ω (k.succ :: K)) ^ 2 := by
            funext ω
            rw [← sub_mul, norm_mul, norm_complexTilt, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]
          rw [hrew, integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg E_bd)
          exact (integral_sq_le_sqrt_four
            (((memLp_unifRiemann B k ht hHA n.succ_pos).sub
              (memLp_itoWordIntegral B ht (k.succ :: K) le_rfl)).aestronglyMeasurable)
            (integrable_pow_of_memLp_four ((memLp_unifRiemann B k ht hHA n.succ_pos).sub
              (memLp_itoWordIntegral B ht (k.succ :: K) le_rfl)) le_rfl)).trans
            (Real.sqrt_le_sqrt (hL4_bd n))
      -- Pass `N = n + 1 → ∞` on RHS
      have hR_lim : Tendsto (fun n : ℕ =>
          ∫ ω, (unifRiemann B k (fun s ω' => itoWordIntegral B 0 s ω' K) t (n + 1) ω : ℂ) *
            complexTilt B hd ξ t ω ∂P) atTop
          (𝓝 (if onlyZeroOrOne hd (k.succ :: K) then
            (Complex.I * (ξ : ℂ)) ^ (countOnes hd (k.succ :: K)) *
              ((t ^ (k.succ :: K).length / ((k.succ :: K).length.factorial : ℝ) : ℝ) : ℂ)
          else 0)) := by
        simp_rw [hstep_sum _ (Nat.succ_pos _)]
        by_cases hk : k = ⟨0, hd⟩
        · subst hk
          have h1 : (⟨0, hd⟩ : Fin d).succ = firstSpace hd := rfl
          simp only [↓reduceIte, onlyZeroOrOne, h1, decide_true, Bool.or_true, Bool.true_and,
            countOnes, List.length_cons]
          by_cases hK : onlyZeroOrOne hd K = true
          · simp only [hK, ↓reduceIte]
            have hreal := tendsto_lebRiemann_of_continuousOn ht
              (g := fun s : ℝ => s ^ K.length / (K.length.factorial : ℝ))
              (by fun_prop : Continuous _).continuousOn
            have hint : ∫ s in (0 : ℝ)..t, s ^ K.length / (K.length.factorial : ℝ) =
                t ^ (K.length + 1) / ((K.length + 1).factorial : ℝ) := by
              rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero _),
                sub_zero, Nat.factorial_succ, Nat.cast_mul, div_div,
                mul_comm ((K.length + 1 : ℕ) : ℝ)]
              push_cast; ring
            rw [hint] at hreal
            refine (((Complex.continuous_ofReal.tendsto _).comp hreal).const_mul
              ((Complex.I * (ξ : ℂ)) ^ (1 + countOnes hd K))).congr fun n => ?_
            simp only [Function.comp_def, Complex.ofReal_sum, Complex.ofReal_mul]
            rw [pow_add, pow_one, mul_assoc]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m hm => ?_
            have hih := ih (by positivity : 0 ≤ (m : ℝ) * (t / ((n + 1 : ℕ) : ℝ)))
            simp only [hK, ↓reduceIte] at hih
            rw [hih]
            push_cast; ring
          · simp only [Bool.not_eq_true] at hK
            simp only [hK, Bool.false_eq_true, ↓reduceIte]
            refine tendsto_const_nhds.congr fun n => ?_
            symm; rw [mul_eq_zero]; right
            refine Finset.sum_eq_zero fun m _ => ?_
            rw [ih (by positivity : 0 ≤ (m : ℝ) * (t / ((n + 1 : ℕ) : ℝ))), hK]; simp
        · have hne1 : k.succ ≠ firstSpace hd := fun h => hk (Fin.succ_inj.mp h)
          have hne0 : k.succ ≠ (0 : Letter (d + 1)) := Fin.succ_ne_zero k
          simp only [hk, ↓reduceIte, onlyZeroOrOne, hne0, hne1, decide_false, Bool.or_self,
            Bool.false_and, Bool.false_eq_true]
          exact tendsto_const_nhds
      exact tendsto_nhds_unique hL_lim hR_lim

end SignatureVolatility

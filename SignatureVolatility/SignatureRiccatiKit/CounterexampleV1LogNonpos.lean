module

public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1
public import SignatureVolatility.SignatureRiccatiKit.CameronMartinC2Shift
public import SignatureVolatility.SignatureRiccatiKit.CounterexampleV1PosLe
public import SignatureVolatility.ItoCalculusKit.EvenTransform
public import SignatureVolatility.ItoCalculusKit.LebIncrementEven
public import SignatureVolatility.ItoCalculusKit.ItoIncrementEven
public import SignatureVolatility.ItoCalculusKit.CrossVariation
public import SignatureVolatility.ItoCalculusKit.FourthMoment
public import SignatureVolatility.ItoCalculusKit.PathwiseExpIto
public import SignatureVolatility.ItoCalculusKit.RiemannConvergence
public import SignatureVolatility.ItoCalculusKit.BrownianQuadVarAS
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# B3. Logarithmic lower bound on `log v₁` for `x ≤ 0`, via deterministic Cameron–Martin
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped ENNReal NNReal

set_option maxHeartbeats 400000

namespace SignatureVolatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma tendsto_integral_of_ae_tendsto_of_L2_bdd_real
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n, MemLp (f n) 2 P) (hg : MemLp g 2 P)
    (hbd : ∀ n, ∫ ω, (f n ω - g ω) ^ 2 ∂P ≤ M)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, g ω ∂P)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := 2 * (M + 1) / ε
  have hR : 0 < R := by positivity
  have hmin_asm : ∀ n, AEStronglyMeasurable (fun ω => min |f n ω - g ω| R) P := fun n =>
    (continuous_id.min continuous_const).comp_aestronglyMeasurable
      ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm
  have hmin_lim : Tendsto (fun n => ∫ ω, min |f n ω - g ω| R ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => R)
      hmin_asm (integrable_const R)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (le_min (abs_nonneg _) hR.le)]; exact min_le_right _ _)
      (by
        filter_upwards [hae] with ω hω
        have h0 : Tendsto (fun n => |f n ω - g ω|) atTop (𝓝 0) := by
          simpa [sub_self] using (hω.sub (tendsto_const_nhds (x := g ω))).abs
        have hmin0 : Tendsto (fun n => min |f n ω - g ω| R) atTop (𝓝 0) := by
          simpa [min_eq_left hR.le] using h0.min (tendsto_const_nhds (x := R))
        exact hmin0)
    simpa using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmin_lim) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hMR : M / R < ε / 2 := by simp only [R]; field_simp; linarith
  have hmin_lt : ∫ ω, min |f n ω - g ω| R ∂P < ε / 2 := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => le_min (abs_nonneg _) hR.le)] at h
    exact h
  have hpt : ∀ ω, |f n ω - g ω| ≤ min |f n ω - g ω| R + (f n ω - g ω) ^ 2 / R := fun ω => by
    rcases le_total |f n ω - g ω| R with hle | hge
    · rw [min_eq_left hle]; linarith [div_nonneg (sq_nonneg (f n ω - g ω)) hR.le]
    · rw [min_eq_right hge]
      have h1 : |f n ω - g ω| ≤ (f n ω - g ω) ^ 2 / R := by
        rw [le_div_iff₀ hR, ← sq_abs, sq]; exact mul_le_mul_of_nonneg_left hge (abs_nonneg _)
      linarith
  have hi_min : Integrable (fun ω => min |f n ω - g ω| R) P :=
    (integrable_const R).mono' (hmin_asm n) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (le_min (abs_nonneg _) hR.le)]; exact min_le_right _ _)
  have hi_sq : Integrable (fun ω => (f n ω - g ω) ^ 2 / R) P :=
    ((hf n).sub hg).integrable_sq.div_const R
  rw [Real.dist_eq, ← integral_sub ((hf n).integrable one_le_two) (hg.integrable one_le_two)]
  calc |∫ ω, (f n ω - g ω) ∂P|
      ≤ ∫ ω, |f n ω - g ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (min |f n ω - g ω| R + (f n ω - g ω) ^ 2 / R) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hi_min.add hi_sq) (ae_of_all _ hpt)
    _ = (∫ ω, min |f n ω - g ω| R ∂P) + (∫ ω, (f n ω - g ω) ^ 2 ∂P) / R := by
        rw [integral_add hi_min hi_sq, integral_div]
    _ ≤ (∫ ω, min |f n ω - g ω| R ∂P) + M / R := by gcongr; exact hbd n
    _ < ε / 2 + ε / 2 := add_lt_add hmin_lt hMR
    _ = ε := add_halves ε

private lemma iteratedDeriv_four_exp_half_sq :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 3 := by
  have hd1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_exp (by fun_prop)]
    have : deriv (fun t : ℝ => t ^ 2 / 2) t = t := by
      rw [deriv_div_const]
      simp
    rw [this]
    ring
  have hd2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_id'', hd1]
    ring
  have hd3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hd1]
    have : deriv (fun t : ℝ => 1 + t ^ 2) t = 2 * t := by simp
    rw [this]
    ring
  have hd4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hd1]
    have : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
      have h1 : HasDerivAt (fun s : ℝ => 3 * s) 3 t := by
        simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
      have h2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
        simpa [pow_two] using hasDerivAt_pow 3 t
      exact (h1.add h2).deriv
    rw [this]
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero, hd1, hd2, hd3, hd4]
  simp [Real.exp_zero]

private lemma gaussMoment_two : gaussMoment 2 = 3 := by
  have h0 : 0 ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp [integrableExpSet_fun_id_gaussianReal]
  have hmom : gaussMoment 2 =
      iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
    rw [gaussMoment, show (2 * 2 : ℕ) = 4 from rfl]
    have h := iteratedDeriv_mgf_zero h0 4
    simpa [Pi.pow_apply] using h.symm
  have harg (t : ℝ) : (0 : ℝ) * t + (1 : NNReal) * t ^ 2 / 2 = t ^ 2 / 2 := by
    rw [NNReal.coe_one]
    ring
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t => Real.exp (t ^ 2 / 2) := by
    funext t
    rw [mgf_fun_id_gaussianReal]
    change Real.exp (0 * t + (1 : NNReal) * t ^ 2 / 2) = Real.exp (t ^ 2 / 2)
    rw [harg t]
  rw [hmom, hmgf, iteratedDeriv_four_exp_half_sq]

private lemma integral_pow_odd_gaussianReal_zero (v : ℝ≥0) (k : ℕ) :
    ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) = 0 := by
  have hLp : MemLp (id : ℝ → ℝ) (2 * k + 1 : ℕ) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := v) ((2 * k + 1 : ℕ) : ℝ≥0∞)
      (ENNReal.natCast_ne_top _)
  have hnorm : Integrable (fun y : ℝ => |y| ^ (2 * k + 1)) (gaussianReal 0 v) := by
    simpa [Real.norm_eq_abs] using hLp.integrable_norm_pow (by simp)
  have hint : Integrable (fun y : ℝ => y ^ (2 * k + 1)) (gaussianReal 0 v) :=
    hnorm.mono' (by fun_prop) (ae_of_all _ fun y => by simp [abs_pow])
  have hsym : (gaussianReal 0 v).map (fun y => -y) = gaussianReal 0 v := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
  have hμ : AEStronglyMeasurable (fun y : ℝ => y ^ (2 * k + 1))
      ((gaussianReal 0 v).map Neg.neg) := by
    rw [hsym]; exact hint.aestronglyMeasurable
  have hmap : ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) =
      ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) := by
    calc ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v)
        = ∫ y, y ^ (2 * k + 1) ∂((gaussianReal 0 v).map fun y => -y) :=
          congrArg (fun ν => ∫ y, y ^ (2 * k + 1) ∂ν) hsym.symm
      _ = ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) :=
          integral_map (G := ℝ) measurable_neg.aemeasurable hμ
  have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
  have hpow : ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) =
      ∫ y, -(y ^ (2 * k + 1)) ∂(gaussianReal 0 v) :=
    integral_congr_ae (ae_of_all _ fun y => Odd.neg_pow hodd y)
  have hneg : ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) =
      -(∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v)) := by
    calc ∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v)
        = ∫ y, (-y) ^ (2 * k + 1) ∂(gaussianReal 0 v) := hmap
      _ = ∫ y, -(y ^ (2 * k + 1)) ∂(gaussianReal 0 v) := hpow
      _ = -∫ y, y ^ (2 * k + 1) ∂(gaussianReal 0 v) :=
          integral_neg (fun y : ℝ => y ^ (2 * k + 1))
  linarith

/-- Elementary Riemann-sum swap for `∫ ω, (∫ r in 0..s₀, c r * W_r^m) ∂P = ∫ r in 0..s₀, c r * 𝔼[W_r^m]`
(avoids joint-measurability Fubini completely, using only `tendsto_integral_of_ae_tendsto_of_L2_bdd`!). -/
private lemma integrable_and_integral_weighted_W_pow {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Icc 0 s₀)) (m : ℕ) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) P ∧
      ∫ ω, (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ∂P =
        ∫ r in (0 : ℝ)..s₀, c r * (∫ ω, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m ∂P) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  set K' : ℝ := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  -- Uniform `L²` bound on `r ↦ c r * W_r^m` over `[0, s₀]`
  have hW_Lp : ∀ r ∈ Set.Icc 0 s₀,
      MemLp (fun ω => c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) 2 P ∧
      ∫ ω, (c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 ∂P ≤
        K' ^ 2 * (gaussMoment m * s₀ ^ m) := fun r hr => by
    have hmom : ∫ ω, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ (2 * m) ∂P = gaussMoment m * r ^ m := by
      simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
        integral_wnnIncr_pow_even B ⟨0, hd⟩ m le_rfl hr.1
    have hint2m : Integrable (fun ω => (MultiBrownian.W B r ω ⟨0, hd⟩) ^ (2 * m)) P := by
      simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
        integrable_wnnIncr_pow_even B ⟨0, hd⟩ m le_rfl hr.1
    have hpow_sq : ∀ ω, ((MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 =
        (MultiBrownian.W B r ω ⟨0, hd⟩) ^ (2 * m) := fun ω => by rw [← pow_mul, mul_comm]
    have hLp : MemLp (fun ω => c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) 2 P :=
      memLp_two_of_integrable_sq
        (measurable_const.mul ((MultiBrownian.W_meas B r ⟨0, hd⟩).pow_const m)).aestronglyMeasurable
        (by simpa [mul_pow, hpow_sq] using hint2m.const_mul (c r ^ 2))
    refine ⟨hLp, ?_⟩
    simp_rw [mul_pow, hpow_sq]
    rw [integral_const_mul, hmom]
    have hcr : c r ^ 2 ≤ K' ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ((hK r hr).trans (le_max_left _ _)) 2
    exact mul_le_mul hcr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hr.2 m)
      (gaussMoment_nonneg m)) (mul_nonneg (gaussMoment_nonneg m) (pow_nonneg hr.1 _))
      (sq_nonneg K')
  -- Left Riemann sums `R n ω` converge everywhere to `∫₀^{s₀} c r * W_r^m dr`,
  -- and are uniformly bounded in `L²` by `s₀² * K'² * gaussMoment m * s₀^m` (`integral_riemannSum_pow_le`)!
  let R : ℕ → Ω → ℝ := fun n ω =>
    ∑ k ∈ Finset.range (n + 1),
      c ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) *
        (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩) ^ m *
        (s₀ / ((n + 1 : ℕ) : ℝ))
  have hR_lim : ∀ ω, Tendsto (fun n => R n ω) atTop
      (𝓝 (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m)) := fun ω => by
    have h := tendsto_lebRiemann_of_continuousOn hs₀
      (hc.mul ((continuous_W_coord B ⟨0, hd⟩ ω).pow m).continuousOn)
    exact h.congr fun n => Finset.sum_congr rfl fun k _ => by push_cast; rfl
  have hR_L2 : ∀ n, MemLp (R n) 2 P ∧
      ∫ ω, R n ω ^ 2 ∂P ≤ s₀ ^ 2 * (K' ^ 2 * (gaussMoment m * s₀ ^ m)) := fun n => by
    have hNΔ : ((n + 1 : ℕ) : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ)) = s₀ := by
      by_cases h0 : s₀ = 0
      · simp [h0]
      · have : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
        field_simp
    have hΔnonneg : 0 ≤ s₀ / ((n + 1 : ℕ) : ℝ) := div_nonneg hs₀ (Nat.cast_nonneg _)
    have h := integral_riemannSum_pow_le (q := 1) one_ne_zero
      (H := fun r ω => c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m)
      (fun k => (k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) (n + 1)
      (Δ := s₀ / ((n + 1 : ℕ) : ℝ)) hΔnonneg
      (fun k hk => by
        obtain ⟨h0, h1⟩ := unifGrid_mem hs₀ n.succ_pos hk.le
        exact (hW_Lp _ ⟨h0, h1⟩).1)
    refine ⟨h.1, ?_⟩
    have hle := h.2
    -- `(2 * 1 - 1) = 1`, and `(N * Δ)^1 = s₀`
    have hle' : ∫ ω, R n ω ^ 2 ∂P ≤
        s₀ * ∑ k ∈ Finset.range (n + 1),
          (∫ ω, (c ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) *
            (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩) ^ m) ^ 2 ∂P) *
          (s₀ / ((n + 1 : ℕ) : ℝ)) := by
      simpa only [show (2 * 1 - 1 : ℕ) = 1 from rfl, pow_one, hNΔ] using h.2
    refine hle'.trans ?_
    calc s₀ * ∑ k ∈ Finset.range (n + 1),
          (∫ ω, (c ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) *
            (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩) ^ m) ^ 2 ∂P) *
            (s₀ / ((n + 1 : ℕ) : ℝ))
        ≤ s₀ * ∑ _k ∈ Finset.range (n + 1),
            (K' ^ 2 * (gaussMoment m * s₀ ^ m)) * (s₀ / ((n + 1 : ℕ) : ℝ)) := by
          gcongr with k hk
          obtain ⟨h0, h1⟩ := unifGrid_mem hs₀ n.succ_pos (Finset.mem_range.mp hk).le
          exact (hW_Lp _ ⟨h0, h1⟩).2
      _ = s₀ ^ 2 * (K' ^ 2 * (gaussMoment m * s₀ ^ m)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          calc s₀ * (((n + 1 : ℕ) : ℝ) * ((K' ^ 2 * (gaussMoment m * s₀ ^ m)) *
                  (s₀ / ((n + 1 : ℕ) : ℝ))))
              = s₀ * ((((n + 1 : ℕ) : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) *
                  (K' ^ 2 * (gaussMoment m * s₀ ^ m))) := by ring
            _ = s₀ * (s₀ * (K' ^ 2 * (gaussMoment m * s₀ ^ m))) := by rw [hNΔ]
            _ = s₀ ^ 2 * (K' ^ 2 * (gaussMoment m * s₀ ^ m)) := by ring
  -- Fatou gives `g ∈ L²(P)` with the same `L²` bound, hence `Integrable g P`!
  have hg_meas : AEStronglyMeasurable
      (fun ω => ∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hR_L2 n).1.aestronglyMeasurable)
      (ae_of_all _ hR_lim)
  have hg_L2 : MemLp (fun ω => ∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) 2 P ∧
      ∫ ω, (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 ∂P ≤
        s₀ ^ 2 * (K' ^ 2 * (gaussMoment m * s₀ ^ m)) := by
    have hfat := integral_pow_even_le_of_tendsto (N := 2) ⟨1, rfl⟩ hg_meas
      (fun n => (hR_L2 n).1.aestronglyMeasurable.aemeasurable) (ae_of_all _ hR_lim)
      (fun n => (hR_L2 n).1.integrable_sq) (fun n => (hR_L2 n).2) tendsto_const_nhds
    exact ⟨memLp_two_of_integrable_sq hg_meas hfat.1, hfat.2⟩
  refine ⟨hg_L2.1.integrable one_le_two, ?_⟩
  -- Pass `n → ∞` in `∫ R n ∂P = ∑ c(t_k) 𝔼[W_{t_k}^m] Δ` via `tendsto_integral_of_ae_tendsto_of_L2_bdd`!
  have hLHS : Tendsto (fun n => ∫ ω, R n ω ∂P) atTop
      (𝓝 (∫ ω, (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ∂P)) := by
    set B₂ := 4 * (s₀ ^ 2 * (K' ^ 2 * (gaussMoment m * s₀ ^ m)))
    refine tendsto_integral_of_ae_tendsto_of_L2_bdd_real (M := B₂)
      (by have := gaussMoment_nonneg m; positivity)
      (fun n => (hR_L2 n).1) hg_L2.1 (fun n => ?_) (ae_of_all _ hR_lim)
    have hpt : ∀ ω, (R n ω - ∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 ≤
        2 * R n ω ^ 2 + 2 * (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 := fun ω => by
      nlinarith [sq_nonneg (R n ω + ∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m)]
    calc ∫ ω, (R n ω - ∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 ∂P
        ≤ ∫ ω, (2 * R n ω ^ 2 + 2 * (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2) ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
            (((hR_L2 n).1.integrable_sq.const_mul 2).add (hg_L2.1.integrable_sq.const_mul 2))
            (ae_of_all _ hpt)
      _ = 2 * ∫ ω, R n ω ^ 2 ∂P +
            2 * ∫ ω, (∫ r in (0 : ℝ)..s₀, c r * (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m) ^ 2 ∂P := by
          rw [integral_add ((hR_L2 n).1.integrable_sq.const_mul 2) (hg_L2.1.integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ B₂ := by linarith [(hR_L2 n).2, hg_L2.2]
  have hRHS_eq : ∀ n, ∫ ω, R n ω ∂P =
      ∑ k ∈ Finset.range (n + 1),
        (c ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) *
          ∫ ω, (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩) ^ m ∂P) *
        (s₀ / ((n + 1 : ℕ) : ℝ)) := fun n => by
    unfold R
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => by
        rw [integral_mul_const, integral_const_mul]
    · intro k hk
      obtain ⟨h0, h1⟩ := unifGrid_mem hs₀ n.succ_pos (Finset.mem_range.mp hk).le
      exact ((hW_Lp _ ⟨h0, h1⟩).1.integrable one_le_two).mul_const _
  -- `r ↦ 𝔼[W_r^m]` is continuous on `[0, s₀]` (equals `0` for odd `m`, `gaussMoment (m/2) * r^(m/2)` for even `m`)
  have hcont_mom : ContinuousOn (fun r => ∫ ω, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m ∂P) (Set.Icc 0 s₀) := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have heq : Set.EqOn (fun r => ∫ ω, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ (k + k) ∂P)
          (fun r => gaussMoment k * r ^ k) (Set.Icc 0 s₀) := fun r hr => by
        rw [← two_mul]
        simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
          integral_wnnIncr_pow_even B ⟨0, hd⟩ k le_rfl hr.1
      exact ((continuous_const.mul (continuous_pow k)).continuousOn).congr heq
    · have heq : Set.EqOn (fun r => ∫ ω, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ (2 * k + 1) ∂P)
          (fun _ => 0) (Set.Icc 0 s₀) := fun r hr => by
        have hlaw : HasLaw (fun ω => MultiBrownian.W B r ω ⟨0, hd⟩) (gaussianReal 0 (Real.toNNReal r)) P := by
          simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using hasLaw_wnnIncr B ⟨0, hd⟩ le_rfl hr.1
        have hcomp := hlaw.integral_comp (f := fun z : ℝ => z ^ (2 * k + 1))
          (measurable_id.pow_const _).aestronglyMeasurable
        simp only [Function.comp_def] at hcomp
        change (∫ ω, MultiBrownian.W B r ω ⟨0, hd⟩ ^ (2 * k + 1) ∂P) = 0
        rw [hcomp, integral_pow_odd_gaussianReal_zero]
      exact continuousOn_const.congr heq
  have hRHS := (tendsto_lebRiemann_of_continuousOn hs₀ (hc.mul hcont_mom)).congr fun n => by
    have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
    have hsum :
        ∑ j ∈ Finset.range (n + 1),
          (c * fun r => ∫ ω, (MultiBrownian.W B r ω ⟨0, hd⟩) ^ m ∂P)
            ((j : ℝ) * (s₀ / ((n : ℝ) + 1))) * (s₀ / ((n : ℝ) + 1)) =
        ∑ k ∈ Finset.range (n + 1),
          (c ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) *
            ∫ ω, (MultiBrownian.W B ((k : ℝ) * (s₀ / ((n + 1 : ℕ) : ℝ))) ω ⟨0, hd⟩) ^ m ∂P) *
          (s₀ / ((n + 1 : ℕ) : ℝ)) :=
      Finset.sum_congr rfl fun k _ => by simp only [hcast, Pi.mul_apply]
    exact hsum.trans (hRHS_eq n).symm
  exact tendsto_nhds_unique hLHS hRHS

/-- **B3.** For all `x ≤ 0`,
`log (v₁ x) ≥ -(s₀³/2) - 2 log(1 + s₀ |x|)` at `s₀ = T/2`.
Replaces the earlier (false-as-needed) comparison `v₁ 0 ≤ v₁ x`. -/
lemma counterexampleV1_log_nonpos (M : SignatureVolatilityModel)
    (B : MultiBrownian Ω P M.d) :
    ∀ x : ℝ, x ≤ 0 →
      -((M.T / 2) ^ 3 / 2) - 2 * Real.log (1 + (M.T / 2) * |x|) ≤
        Real.log (counterexampleV1AtHalf M B x) := by
  intro x hx
  set s₀ : ℝ := M.T / 2
  have hs₀ : 0 < s₀ := half_pos M.hT
  set y : ℝ → ℝ := fun r => x / (1 - x * r)
  set h : ℝ → ℝ := fun r => y r - x
  set U : Set ℝ := {r : ℝ | 0 < 1 - x * r}
  have hU_open : IsOpen U := isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul continuous_id))
  have hU_sub : Set.Icc 0 s₀ ⊆ U := fun r hr => by show 0 < 1 - x * r; nlinarith [hr.1]
  have hy_deriv : ∀ r ∈ U, HasDerivAt y (y r ^ 2) r := fun r hr => by
    have hd0 : 1 - x * r ≠ 0 := ne_of_gt hr
    have h1 : HasDerivAt (fun u => 1 - x * u) (-x) r := by
      convert (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).const_mul x) using 1
      · ext u; simp [Pi.sub_apply, id]
      · ring
    convert (hasDerivAt_const r x).div h1 hd0 using 1
    simp only [y]; field_simp; ring
  have hh_deriv : ∀ r ∈ U, deriv h r = y r ^ 2 := fun r hr => by
    have heq : h = y - fun _ => x := by
      ext u; simp only [h, Pi.sub_apply]
    have hd : HasDerivAt h (y r ^ 2) r := by
      rw [heq]
      convert (hy_deriv r hr).sub (hasDerivAt_const r x) using 1
      ring
    exact hd.deriv
  have hh_deriv2 : ∀ r ∈ U, iteratedDeriv 2 h r = 2 * y r ^ 3 := fun r hr => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have heq : deriv h =ᶠ[𝓝 r] fun u => y u ^ 2 :=
      Filter.eventually_of_mem (hU_open.mem_nhds hr) hh_deriv
    rw [heq.deriv_eq]
    convert ((hy_deriv r hr).pow 2).deriv using 1; ring
  have hh_diff : ContDiffOn ℝ 2 h U := by
    have h1 : ContDiffOn ℝ 2 (fun r => 1 - x * r) U :=
      contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id)
    exact (contDiffOn_const.div h1 fun r hr => ne_of_gt hr).sub contDiffOn_const
  let Ψ : Ω → ℝ := fun ω =>
    let w := fun r => MultiBrownian.W B r ω ⟨0, M.hd⟩
    y s₀ * w s₀ ^ 2 + (1 / 3 : ℝ) * w s₀ ^ 3
      - (∫ r in (0 : ℝ)..s₀, y r)
      - (∫ r in (0 : ℝ)..s₀, w r)
      - (∫ r in (0 : ℝ)..s₀, 3 * y r ^ 2 * w r ^ 2)
      - (∫ r in (0 : ℝ)..s₀, 2 * y r * w r ^ 3)
      - (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * w r ^ 4)
  have hy_cont : ContinuousOn y (Set.Icc 0 s₀) :=
    continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      fun r hr => ne_of_gt (hU_sub hr)
  -- Exact FTC identity `(1/3)(y(s₀)³ - x³) = ∫₀^{s₀} y(r)⁴ dr`
  have hy_cube : (1 / 3 : ℝ) * (y s₀ ^ 3 - x ^ 3) = ∫ r in (0 : ℝ)..s₀, y r ^ 4 := by
    have hd : ∀ r ∈ uIcc 0 s₀, HasDerivAt (fun u => (1 / 3 : ℝ) * y u ^ 3) (y r ^ 4) r := fun r hr => by
      rw [uIcc_of_le hs₀.le] at hr
      convert ((hy_deriv r (hU_sub hr)).pow 3).const_mul (1 / 3 : ℝ) using 1; ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hy_cont.pow 4).intervalIntegrable_of_Icc hs₀.le)
    have hy0 : y 0 = x := by simp [y]
    rw [hftc, hy0]; ring
  -- Pathwise cancellation `hpath`
  have hpath : ∀ ω,
      let w := fun r => MultiBrownian.W B r ω ⟨0, M.hd⟩
      pathExponent (fun r => w r + h r) x s₀
        - deriv h s₀ * w s₀
        + (∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r)
        - (1 / 2 : ℝ) * (∫ r in (0 : ℝ)..s₀, deriv h r ^ 2) = Ψ ω := by
    intro ω w
    have hw_cont : ContinuousOn w (Set.Icc 0 s₀) := (continuous_W_coord B ⟨0, M.hd⟩ ω).continuousOn
    have hi : ∀ {g : ℝ → ℝ}, ContinuousOn g (Set.Icc 0 s₀) → IntervalIntegrable g volume 0 s₀ :=
      fun hg => hg.intervalIntegrable_of_Icc hs₀.le
    have hsub1 : ∫ r in (0 : ℝ)..s₀, (x + (w r + h r)) =
        (∫ r in (0 : ℝ)..s₀, y r) + (∫ r in (0 : ℝ)..s₀, w r) := by
      have : ∀ r, x + (w r + h r) = y r + w r := fun r => by simp only [h]; ring
      simp_rw [this]
      exact intervalIntegral.integral_add (hi hy_cont) (hi hw_cont)
    have hsub4 : ∫ r in (0 : ℝ)..s₀, (x + (w r + h r)) ^ 4 =
        (∫ r in (0 : ℝ)..s₀, y r ^ 4) +
        (∫ r in (0 : ℝ)..s₀, 4 * y r ^ 3 * w r) +
        (∫ r in (0 : ℝ)..s₀, 6 * y r ^ 2 * w r ^ 2) +
        (∫ r in (0 : ℝ)..s₀, 4 * y r * w r ^ 3) +
        (∫ r in (0 : ℝ)..s₀, w r ^ 4) := by
      let f0 : ℝ → ℝ := fun r => y r ^ 4
      let f1 : ℝ → ℝ := fun r => 4 * y r ^ 3 * w r
      let f2 : ℝ → ℝ := fun r => 6 * y r ^ 2 * w r ^ 2
      let f3 : ℝ → ℝ := fun r => 4 * y r * w r ^ 3
      let f4 : ℝ → ℝ := fun r => w r ^ 4
      have i0 : IntervalIntegrable f0 volume 0 s₀ := hi (hy_cont.pow 4)
      have i1 : IntervalIntegrable f1 volume 0 s₀ :=
        hi ((continuousOn_const.mul (hy_cont.pow 3)).mul hw_cont)
      have i2 : IntervalIntegrable f2 volume 0 s₀ :=
        hi ((continuousOn_const.mul (hy_cont.pow 2)).mul (hw_cont.pow 2))
      have i3 : IntervalIntegrable f3 volume 0 s₀ :=
        hi ((continuousOn_const.mul hy_cont).mul (hw_cont.pow 3))
      have i4 : IntervalIntegrable f4 volume 0 s₀ := hi (hw_cont.pow 4)
      have hpt : ∀ r, (x + (w r + h r)) ^ 4 = ((((f0 + f1) + f2) + f3) + f4) r := fun r => by
        simp only [h, f0, f1, f2, f3, f4, Pi.add_apply]; ring
      trans intervalIntegral ((((f0 + f1) + f2) + f3) + f4) 0 s₀ volume
      · exact intervalIntegral.integral_congr fun r _ => hpt r
      · change (∫ r in (0 : ℝ)..s₀, ((((f0 + f1) + f2) + f3) + f4) r) = _
        simp only [Pi.add_apply]
        rw [intervalIntegral.integral_add (i0.add i1 |>.add i2 |>.add i3) i4,
          intervalIntegral.integral_add (i0.add i1 |>.add i2) i3,
          intervalIntegral.integral_add (i0.add i1) i2,
          intervalIntegral.integral_add i0 i1]
    have hdh2 : ∫ r in (0 : ℝ)..s₀, iteratedDeriv 2 h r * w r =
        ∫ r in (0 : ℝ)..s₀, 2 * y r ^ 3 * w r :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs₀.le] at hr; rw [hh_deriv2 r (hU_sub hr)]
    have hdh1sq : ∫ r in (0 : ℝ)..s₀, deriv h r ^ 2 = ∫ r in (0 : ℝ)..s₀, y r ^ 4 :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs₀.le] at hr; rw [hh_deriv r (hU_sub hr)]; ring
    have h6 : ∫ r in (0 : ℝ)..s₀, 6 * y r ^ 2 * w r ^ 2 = 2 * ∫ r in (0 : ℝ)..s₀, 3 * y r ^ 2 * w r ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]; exact intervalIntegral.integral_congr fun r _ => by ring
    have h4 : ∫ r in (0 : ℝ)..s₀, 4 * y r ^ 3 * w r = 2 * ∫ r in (0 : ℝ)..s₀, 2 * y r ^ 3 * w r := by
      rw [← intervalIntegral.integral_const_mul]; exact intervalIntegral.integral_congr fun r _ => by ring
    have h4' : ∫ r in (0 : ℝ)..s₀, 4 * y r * w r ^ 3 = 2 * ∫ r in (0 : ℝ)..s₀, 2 * y r * w r ^ 3 := by
      rw [← intervalIntegral.integral_const_mul]; exact intervalIntegral.integral_congr fun r _ => by ring
    have h12 : (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..s₀, w r ^ 4 = ∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * w r ^ 4 :=
      (intervalIntegral.integral_const_mul _ _).symm
    have hcube : (1 / 3 : ℝ) * ((x + (w s₀ + h s₀)) ^ 3 - x ^ 3) =
        (1 / 3 : ℝ) * (y s₀ ^ 3 - x ^ 3) + y s₀ ^ 2 * w s₀ + y s₀ * w s₀ ^ 2 + (1 / 3 : ℝ) * w s₀ ^ 3 := by
      simp only [h]; ring
    unfold pathExponent Ψ
    rw [hcube, hy_cube, hsub1, hsub4, hdh2, hdh1sq, hh_deriv s₀ (hU_sub ⟨hs₀.le, le_rfl⟩),
      h6, h4, h4']
    -- distribute the factor `1/2` over the expanded quartic integral, then match `h12`
    simp only [mul_add, h12]
    ring
  -- Apply `cameronMartin_C2_shift`
  have hcm : counterexampleV1AtHalf M B x = ∫ ω, Real.exp (Ψ ω) ∂P :=
    cameronMartin_C2_shift B M.hd hs₀.le h x Ψ (by simp [h, y]) ⟨U, hU_open, hU_sub, hh_diff⟩ hpath
  -- `Integrable (exp ∘ Ψ) P` in 2 lines from positivity + `integral_undef`!
  have hpos : 0 < counterexampleV1AtHalf M B x := (counterexampleV1_pos_le M B x).1
  have hint_exp : Integrable (fun ω => Real.exp (Ψ ω)) P := by
    by_contra hni
    rw [hcm, integral_undef hni] at hpos
    exact lt_irrefl 0 hpos
  -- Integrability & expectation of every term in `Ψ` via `integrable_and_integral_weighted_W_pow`
  have hT1 := integrable_and_integral_weighted_W_pow B M.hd hs₀.le (c := fun _ => (1 : ℝ)) continuousOn_const 1
  have hT2 := integrable_and_integral_weighted_W_pow B M.hd hs₀.le (c := fun r => 3 * y r ^ 2)
    (continuousOn_const.mul (hy_cont.pow 2)) 2
  have hT3 := integrable_and_integral_weighted_W_pow B M.hd hs₀.le (c := fun r => 2 * y r)
    (continuousOn_const.mul hy_cont) 3
  have hT4 := integrable_and_integral_weighted_W_pow B M.hd hs₀.le (c := fun _ => (1 / 2 : ℝ))
    continuousOn_const 4
  have hW2_int : Integrable (fun ω => y s₀ * MultiBrownian.W B s₀ ω ⟨0, M.hd⟩ ^ 2) P := by
    have hw := integrable_wnnIncr_pow_even B ⟨0, M.hd⟩ 1 le_rfl hs₀.le
    simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using hw.const_mul (y s₀)
  have hW3_int : Integrable (fun ω => (1 / 3 : ℝ) * MultiBrownian.W B s₀ ω ⟨0, M.hd⟩ ^ 3) P := by
    have h4 : MemLp (fun ω => MultiBrownian.W B s₀ ω ⟨0, M.hd⟩) 4 P :=
      memLp_even_of_integrable_pow (q := 2) (MultiBrownian.W_meas B s₀ ⟨0, M.hd⟩).aestronglyMeasurable
        (by simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
          integrable_wnnIncr_pow_even B ⟨0, M.hd⟩ 2 le_rfl hs₀.le)
    exact (integrable_pow_of_memLp_four h4 (by norm_num)).const_mul _
  have hint_Ψ : Integrable Ψ P := by
    refine ((((((hW2_int.add hW3_int).sub (integrable_const _)).sub ?_).sub ?_).sub ?_).sub ?_)
    · simpa using hT1.1
    · exact hT2.1
    · exact hT3.1
    · exact hT4.1
  -- Jensen's inequality
  have hjensen : ∫ ω, Ψ ω ∂P ≤ Real.log (counterexampleV1AtHalf M B x) := by
    rw [hcm, ← Real.log_exp (∫ ω, Ψ ω ∂P)]
    exact Real.log_le_log (Real.exp_pos _)
      (ConvexOn.map_integral_le (μ := P) convexOn_exp Real.continuous_exp.continuousOn
        isClosed_univ (ae_of_all _ fun _ => mem_univ _) hint_Ψ hint_exp)
  -- Evaluate `∫ ω, Ψ ω ∂P` and simplify via integration by parts
  have hE1 : ∫ ω, MultiBrownian.W B s₀ ω ⟨0, M.hd⟩ ^ 2 ∂P = s₀ := by
    simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
      integral_wnnIncr_sq B ⟨0, M.hd⟩ le_rfl hs₀.le
  have hE3_all : ∀ (r : ℝ), 0 ≤ r → ∫ ω, MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 3 ∂P = 0 :=
    fun r hr => by
    have hlaw : HasLaw (fun ω => MultiBrownian.W B r ω ⟨0, M.hd⟩)
        (gaussianReal 0 (Real.toNNReal r)) P := by
      simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
        hasLaw_wnnIncr B ⟨0, M.hd⟩ le_rfl hr
    have hcomp := hlaw.integral_comp (f := fun z : ℝ => z ^ 3)
      (measurable_id.pow_const 3).aestronglyMeasurable
    simp only [Function.comp_def] at hcomp
    rw [hcomp, show (3 : ℕ) = 2 * 1 + 1 from rfl]
    exact integral_pow_odd_gaussianReal_zero _ 1
  have hEΨ : ∫ ω, Ψ ω ∂P =
      y s₀ * s₀ - (∫ r in (0 : ℝ)..s₀, y r) -
        3 * (∫ r in (0 : ℝ)..s₀, r * y r ^ 2) - (1 / 2 : ℝ) * (gaussMoment 2 * (s₀ ^ 3 / 3)) := by
    set ψ0 : Ω → ℝ := fun ω => y s₀ * MultiBrownian.W B s₀ ω ⟨0, M.hd⟩ ^ 2
    set ψ1 : Ω → ℝ := fun ω => (1 / 3 : ℝ) * MultiBrownian.W B s₀ ω ⟨0, M.hd⟩ ^ 3
    set ψy : Ω → ℝ := fun _ => ∫ r in (0 : ℝ)..s₀, y r
    set ψw : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..s₀, MultiBrownian.W B r ω ⟨0, M.hd⟩
    set ψ2 : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..s₀, 3 * y r ^ 2 * MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 2
    set ψ3 : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..s₀, 2 * y r * MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 3
    set ψ4 : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 4
    have hΨeq : Ψ = (((((ψ0 + ψ1) - ψy) - ψw) - ψ2) - ψ3) - ψ4 := by
      ext ω; simp only [Ψ, ψ0, ψ1, ψy, ψw, ψ2, ψ3, ψ4, Pi.add_apply, Pi.sub_apply]
    have hT1' : Integrable ψw P := by simpa [ψw, one_mul, pow_one] using hT1.1
    have I01 : Integrable (ψ0 + ψ1) P := hW2_int.add hW3_int
    have Iy : Integrable ((ψ0 + ψ1) - ψy) P := I01.sub (integrable_const _)
    have Iw : Integrable (((ψ0 + ψ1) - ψy) - ψw) P := Iy.sub hT1'
    have I2 : Integrable ((((ψ0 + ψ1) - ψy) - ψw) - ψ2) P := Iw.sub hT2.1
    have I3 : Integrable (((((ψ0 + ψ1) - ψy) - ψw) - ψ2) - ψ3) P := I2.sub hT3.1
    rw [hΨeq]
    have e4 : ∫ ω, (((((ψ0 + ψ1) - ψy) - ψw) - ψ2) - ψ3 - ψ4) ω ∂P =
        (∫ ω, (((((ψ0 + ψ1) - ψy) - ψw) - ψ2) - ψ3) ω ∂P) - ∫ ω, ψ4 ω ∂P := by
      simpa [Pi.sub_apply] using integral_sub I3 hT4.1
    have e3 : ∫ ω, (((((ψ0 + ψ1) - ψy) - ψw) - ψ2) - ψ3) ω ∂P =
        (∫ ω, ((((ψ0 + ψ1) - ψy) - ψw) - ψ2) ω ∂P) - ∫ ω, ψ3 ω ∂P := by
      simpa [Pi.sub_apply] using integral_sub I2 hT3.1
    have e2 : ∫ ω, ((((ψ0 + ψ1) - ψy) - ψw) - ψ2) ω ∂P =
        (∫ ω, (((ψ0 + ψ1) - ψy) - ψw) ω ∂P) - ∫ ω, ψ2 ω ∂P := by
      simpa [Pi.sub_apply] using integral_sub Iw hT2.1
    have e1 : ∫ ω, (((ψ0 + ψ1) - ψy) - ψw) ω ∂P =
        (∫ ω, ((ψ0 + ψ1) - ψy) ω ∂P) - ∫ ω, ψw ω ∂P := by
      simpa [Pi.sub_apply] using integral_sub Iy hT1'
    have e0 : ∫ ω, ((ψ0 + ψ1) - ψy) ω ∂P =
        (∫ ω, (ψ0 + ψ1) ω ∂P) - ∫ ω, ψy ω ∂P := by
      have hc : Integrable ψy P := integrable_const _
      simpa [Pi.sub_apply] using integral_sub I01 hc
    have e01 : ∫ ω, (ψ0 + ψ1) ω ∂P = ∫ ω, ψ0 ω ∂P + ∫ ω, ψ1 ω ∂P := by
      simpa [Pi.add_apply] using integral_add hW2_int hW3_int
    rw [e4, e3, e2, e1, e0, e01, integral_const_mul, integral_const_mul, hE1,
      hE3_all s₀ hs₀.le, integral_const, probReal_univ, smul_eq_mul, one_mul,
      mul_zero, add_zero]
    simp only [ψ0, ψ1, ψy, ψw, ψ2, ψ3, ψ4]
    have h1_zero : ∫ ω, (∫ r in (0 : ℝ)..s₀, MultiBrownian.W B r ω ⟨0, M.hd⟩) ∂P = 0 := by
      have := hT1.2; simp only [one_mul, pow_one] at this; rw [this]
      have hz : ∀ r ∈ uIcc 0 s₀, (∫ ω, MultiBrownian.W B r ω ⟨0, M.hd⟩ ∂P) = (0 : ℝ) :=
        fun r hr => by
          rw [uIcc_of_le hs₀.le] at hr
          simpa [wnnIncr_eq_W, MultiBrownian.W_zero] using
            integral_wnnIncr B ⟨0, M.hd⟩ le_rfl hr.1
      exact (intervalIntegral.integral_congr hz).trans intervalIntegral.integral_zero
    have h2_val : ∫ ω, (∫ r in (0 : ℝ)..s₀, 3 * y r ^ 2 * MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 2) ∂P =
        3 * ∫ r in (0 : ℝ)..s₀, r * y r ^ 2 := by
      rw [hT2.2, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs₀.le] at hr
      have hm2 : ∫ ω, MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 2 ∂P = r := by
        simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using integral_wnnIncr_sq B ⟨0, M.hd⟩ le_rfl hr.1
      rw [hm2]; ring
    have h3_zero : ∫ ω, (∫ r in (0 : ℝ)..s₀, 2 * y r * MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 3) ∂P = 0 := by
      rw [hT3.2]
      have hz : ∀ r ∈ uIcc 0 s₀,
          2 * y r * (∫ ω, MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 3 ∂P) = 0 :=
        fun r hr => by
          rw [uIcc_of_le hs₀.le] at hr
          rw [hE3_all r hr.1, mul_zero]
      exact (intervalIntegral.integral_congr hz).trans intervalIntegral.integral_zero
    have h4_val : ∫ ω, (∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 4) ∂P =
        (1 / 2 : ℝ) * (gaussMoment 2 * (s₀ ^ 3 / 3)) := by
      rw [hT4.2]
      have hcongr : ∫ r in (0 : ℝ)..s₀, (1 / 2 : ℝ) * (∫ ω, MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 4 ∂P) =
          ∫ r in (0 : ℝ)..s₀, ((1 / 2 : ℝ) * gaussMoment 2) * r ^ 2 :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hs₀.le] at hr
          have hm4 : ∫ ω, MultiBrownian.W B r ω ⟨0, M.hd⟩ ^ 4 ∂P = gaussMoment 2 * r ^ 2 := by
            simpa [wnnIncr_eq_W, MultiBrownian.W_zero, sub_zero] using
              integral_wnnIncr_pow_even B ⟨0, M.hd⟩ 2 le_rfl hr.1
          rw [hm4]; ring
      rw [hcongr, intervalIntegral.integral_const_mul, integral_pow, zero_pow (by norm_num), sub_zero]
      ring
    rw [h1_zero, h2_val, h3_zero, h4_val]; ring
  -- Integration by parts `∫ r y² = s₀ y(s₀) - ∫ y`, `∫ y = -log(1 + s₀ |x|)`, and `gaussMoment 2 = 3`
  have hibp : ∫ r in (0 : ℝ)..s₀, r * y r ^ 2 = s₀ * y s₀ - ∫ r in (0 : ℝ)..s₀, y r := by
    have hd : ∀ r ∈ uIcc 0 s₀, HasDerivAt (fun u => u * y u) (y r + r * y r ^ 2) r := fun r hr => by
      rw [uIcc_of_le hs₀.le] at hr
      have heq : (fun u => u * y u) = id * y := by
        ext u; simp [Pi.mul_apply]
      rw [heq]
      convert (hasDerivAt_id r).mul (hy_deriv r (hU_sub hr)) using 1
      simp [id]
    have ig : IntervalIntegrable (fun r => r * y r ^ 2) volume 0 s₀ :=
      (continuousOn_id.mul (hy_cont.pow 2)).intervalIntegrable_of_Icc hs₀.le
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hy_cont.add (continuousOn_id.mul (hy_cont.pow 2))).intervalIntegrable_of_Icc hs₀.le)
    rw [intervalIntegral.integral_add (hy_cont.intervalIntegrable_of_Icc hs₀.le) ig,
      zero_mul, sub_zero] at hftc
    linarith
  have hint_y : ∫ r in (0 : ℝ)..s₀, y r = -Real.log (1 + s₀ * |x|) := by
    have hd : ∀ r ∈ uIcc 0 s₀, HasDerivAt (fun u => -Real.log (1 - x * u)) (y r) r := fun r hr => by
      rw [uIcc_of_le hs₀.le] at hr
      have h1 : HasDerivAt (fun u => 1 - x * u) (-x) r := by
        convert (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).const_mul x) using 1
        · ext u; simp [Pi.sub_apply, id]
        · ring
      convert (h1.log (ne_of_gt (hU_sub hr))).neg using 1
      simp only [y]; field_simp
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hy_cont.intervalIntegrable_of_Icc hs₀.le)
    simp only [mul_zero, sub_zero, Real.log_one, neg_zero] at hftc
    rw [hftc, abs_of_nonpos hx]; congr 1; ring
  have hg2 : gaussMoment 2 = 3 := gaussMoment_two
  have hys0 : y s₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx (le_of_lt (hU_sub ⟨hs₀.le, le_rfl⟩))
  refine le_trans ?_ hjensen
  rw [hEΨ, hibp, hint_y, hg2]
  nlinarith

end SignatureVolatility

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Semimartingale.Quasimartingale.FutureEnvelope

/-! # Balance of the actual positive and negative future envelopes

The finite partition identity retains the terminal-zero tail and telescopes
after applying the conditional-expectation tower property. To pass to the two
essential suprema, each is compared with a translated upper bound for the
other. A genuine family member establishes nonnegativity of both real bounds.
No supremum/subtraction interchange or Rao decomposition is assumed.
-/

@[expose] public section

open MeasureTheory StochLean Finset Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {H : ℝ≥0}

/-- For an actual finite partition, the positive-minus-negative conditional
decrement sums equal the initial conditional value, including the final tail. -/
theorem conditional_positive_sub_negative_decrements_ae_eq
    (hi : ∀ t, Integrable (X t) P) (π : TimePartition H) :
    (fun ω ↦
      P[(fun ω ↦ (∑ i, max (P[X (π.left i) - X (π.right i) | F (π.left i)] ω) 0) +
        max (X H ω) 0) | F 0] ω -
      P[(fun ω ↦ (∑ i, max (P[(-X) (π.left i) - (-X) (π.right i) |
        F (π.left i)] ω) 0) + max ((-X) H ω) 0) | F 0] ω) =ᵐ[P] P[X 0 | F 0] := by
  let D (i : Fin π.size) := P[X (π.left i) - X (π.right i) | F (π.left i)]
  let B (Z : ℝ≥0 → Ω → ℝ) (ω : Ω) :=
    (∑ i, max (P[Z (π.left i) - Z (π.right i) | F (π.left i)] ω) 0) + max (Z H ω) 0
  have hBi (Z : ℝ≥0 → Ω → ℝ) (hZ : ∀ t, Integrable (Z t) P) : Integrable (B Z) P :=
    (integrable_finsetSum Finset.univ (fun i _ ↦
      (integrable_condExp (f := Z (π.left i) - Z (π.right i))
        (m := F (π.left i))).sup (integrable_zero _ _ _))).add
      ((hZ H).sup (integrable_zero _ _ _))
  have hmax (x : ℝ) : max x 0 - max (-x) 0 = x := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      ring
  have hn (i : Fin π.size) :
      P[(-X) (π.left i) - (-X) (π.right i) | F (π.left i)] =ᵐ[P] -D i := by
    have hid : (-X) (π.left i) - (-X) (π.right i) =
        -(X (π.left i) - X (π.right i)) := by
      ext ω
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    rw [hid]
    exact condExp_neg _ _
  let S : Ω → ℝ := fun ω ↦ (∑ i, D i ω) + X H ω
  have hraw : B X - B (-X) =ᵐ[P] S := by
    filter_upwards [ae_all_iff.mpr hn] with ω hω
    simp only [Pi.neg_apply] at hω
    change ((∑ i, max (D i ω) 0) + max (X H ω) 0) -
      ((∑ i, max (P[(-X) (π.left i) - (-X) (π.right i) | F (π.left i)] ω) 0) +
        max ((-X) H ω) 0) = (∑ i, D i ω) + X H ω
    simp only [Pi.neg_apply, hω]
    have hs : (∑ i, max (D i ω) 0) - (∑ i, max (-D i ω) 0) = ∑ i, D i ω := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ hmax (D i ω)
    have ht := hmax (X H ω)
    linarith only [hs, ht]
  have he (i : Fin π.size) : P[D i | F 0] =ᵐ[P]
      P[X (π.left i) | F 0] - P[X (π.right i) | F 0] :=
    (condExp_condExp_of_le (μ := P) (F.mono (show 0 ≤ π.left i from bot_le))
      (F.le (π.left i))).trans (condExp_sub (hi (π.left i)) (hi (π.right i)) (F 0))
  have hS : P[S | F 0] =ᵐ[P] P[X 0 | F 0] := by
    have hsum := condExp_finsetSum (μ := P) (s := Finset.univ) (f := D)
      (fun _ _ ↦ integrable_condExp) (F 0)
    have hadd := condExp_add (f := fun ω ↦ ∑ i, D i ω)
      (integrable_finsetSum Finset.univ (fun i _ ↦
      integrable_condExp (f := X (π.left i) - X (π.right i)) (m := F (π.left i))))
      (hi H) (F 0)
    filter_upwards [hsum, hadd, ae_all_iff.mpr he] with ω hsω haω heω
    simp only [Finset.sum_fn, Pi.add_def] at hsω haω
    change P[(fun ω ↦ (∑ i, D i ω) + X H ω) | F 0] ω = _
    rw [haω, hsω]
    simp only [heω, Pi.sub_apply]
    have ht := π.sum_increment (fun t ↦ P[X t | F 0] ω)
    simp only [TimePartition.increment, sum_sub_distrib] at ht ⊢
    linarith only [ht]
  have hh := (condExp_sub (hBi X hi) (hBi (-X) (fun t ↦ (hi t).neg)) (F 0)).symm.trans
    ((condExp_congr_ae hraw).trans hS)
  simpa only [B, Pi.sub_def] using hh

omit [IsFiniteMeasure P] in
private theorem paired_essentialSupremum_balance {ι : Type*} [Nonempty ι]
    {p n : ι → Ω → ℝ} {x : Ω → ℝ} {Wp Wn : Ω → ℝ≥0∞}
    (hp : IsAEFamilySupremum P (fun i ω ↦ ENNReal.ofReal (p i ω)) Wp)
    (hn : IsAEFamilySupremum P (fun i ω ↦ ENNReal.ofReal (n i ω)) Wn)
    (hpn : ∀ i, 0 ≤ᵐ[P] p i) (hnn : ∀ i, 0 ≤ᵐ[P] n i)
    (hb : ∀ i, p i - n i =ᵐ[P] x)
    (hfp : ∀ᵐ ω ∂P, Wp ω ≠ ∞) (hfn : ∀ᵐ ω ∂P, Wn ω ≠ ∞) :
    (fun ω ↦ (Wp ω).toReal - (Wn ω).toReal) =ᵐ[P] x := by
  classical
  have hple (i : ι) : p i ≤ᵐ[P] fun ω ↦ (Wp ω).toReal := by
    filter_upwards [hp.le_ae i, hfp] with ω hω hfω
    exact (ENNReal.ofReal_le_iff_le_toReal hfω).mp hω
  have hnle (i : ι) : n i ≤ᵐ[P] fun ω ↦ (Wn ω).toReal := by
    filter_upwards [hn.le_ae i, hfn] with ω hω hfω
    exact (ENNReal.ofReal_le_iff_le_toReal hfω).mp hω
  have hpc (i : ι) : p i ≤ᵐ[P] fun ω ↦ x ω + (Wn ω).toReal := by
    filter_upwards [hb i, hnle i] with ω hbω hnω
    simp only [Pi.sub_apply] at hbω
    linarith only [hbω, hnω]
  have hnc (i : ι) : n i ≤ᵐ[P] fun ω ↦ (Wp ω).toReal - x ω := by
    filter_upwards [hb i, hple i] with ω hbω hpω
    simp only [Pi.sub_apply] at hbω
    linarith only [hbω, hpω]
  let i₀ : ι := Classical.choice inferInstance
  have hpos : ∀ᵐ ω ∂P, 0 ≤ x ω + (Wn ω).toReal :=
    (hpn i₀).trans (hpc i₀)
  have hneg : ∀ᵐ ω ∂P, 0 ≤ (Wp ω).toReal - x ω :=
    (hnn i₀).trans (hnc i₀)
  have hup := hp.ae_le (fun ω ↦ ENNReal.ofReal (x ω + (Wn ω).toReal))
    (fun i ↦ (hpc i).mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω)
  have hun := hn.ae_le (fun ω ↦ ENNReal.ofReal ((Wp ω).toReal - x ω))
    (fun i ↦ (hnc i).mono fun _ hω ↦ ENNReal.ofReal_le_ofReal hω)
  filter_upwards [hup, hun, hpos, hneg] with ω hpω hnω hposω hnegω
  have hp' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpω
  have hn' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnω
  rw [ENNReal.toReal_ofReal hposω] at hp'
  rw [ENNReal.toReal_ofReal hnegω] at hn'
  linarith only [hp', hn']

/-- Any versions of the actual finite positive and negative whole-future
envelopes have difference equal to the source process at the fixed time. -/
theorem future_partitionEnvelopes_sub_ae_eq
    (ha : Adapted F X) (hi : ∀ s, Integrable (X s) P)
    (hv : HasFiniteConditionalVariation X F P) (t : ℝ≥0) :
    let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
    let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
    let f (Z : ℝ≥0 → Ω → ℝ) : (Σ H : ℝ≥0, TimePartition H) → Ω → ℝ≥0∞ :=
      fun p ω ↦ ENNReal.ofReal
        (P[(fun ω ↦
          (∑ i, max (P[Z (p.2.left i) - Z (p.2.right i) | G (p.2.left i)] ω) 0) +
            max (Z p.1 ω) 0) | G 0] ω)
    ∀ {Wp Wn : Ω → ℝ≥0∞}, IsAEFamilySupremum P (f Y) Wp →
      IsAEFamilySupremum P (f (-Y)) Wn →
      (fun ω ↦ (Wp ω).toReal - (Wn ω).toReal) =ᵐ[P] X t := by
  dsimp only
  intro Wp Wn hp hn
  let Y : ℝ≥0 → Ω → ℝ := fun s ↦ X (t + s)
  let G := F.reindex (fun s : ℝ≥0 ↦ t + s) (monotone_const.add monotone_id)
  let k (Z : ℝ≥0 → Ω → ℝ) (p : Σ H : ℝ≥0, TimePartition H) : Ω → ℝ :=
    P[(fun ω ↦
      (∑ i, max (P[Z (p.2.left i) - Z (p.2.right i) | G (p.2.left i)] ω) 0) +
        max (Z p.1 ω) 0) | G 0]
  have haY : Adapted G Y := fun s ↦ ha (t + s)
  have hiY (s : ℝ≥0) : Integrable (Y s) P := hi (t + s)
  obtain ⟨Vp, Vn, _, _, hVp, hVn, _, _, hfin⟩ :=
    exists_future_positive_negative_partitionEnvelopes ha hi t
  have hf := (hfin hv).1
  have hfp : ∀ᵐ ω ∂P, Wp ω ≠ ∞ := by
    filter_upwards [hp.ae_eq hVp, hf] with ω heω hfω
    rw [heω]
    exact hfω.1
  have hfn : ∀ᵐ ω ∂P, Wn ω ≠ ∞ := by
    filter_upwards [hn.ae_eq hVn, hf] with ω heω hfω
    rw [heω]
    exact hfω.2
  have hnonneg (Z : ℝ≥0 → Ω → ℝ) (p : Σ H : ℝ≥0, TimePartition H) :
      0 ≤ᵐ[P] k Z p := condExp_nonneg (Eventually.of_forall fun _ ↦
    add_nonneg (sum_nonneg fun _ _ ↦ le_max_right _ _) (le_max_right _ _))
  have hb (p : Σ H : ℝ≥0, TimePartition H) : k Y p - k (-Y) p =ᵐ[P] X t := by
    have hh := conditional_positive_sub_negative_decrements_ae_eq (F := G) hiY p.2
    rw [condExp_of_stronglyMeasurable (G.le 0) (haY.stronglyAdapted 0) (hiY 0)] at hh
    simpa only [k, Pi.sub_def, Y, add_zero] using hh
  let : Nonempty (Σ H : ℝ≥0, TimePartition H) := ⟨⟨0, TimePartition.empty⟩⟩
  exact paired_essentialSupremum_balance (p := k Y) (n := k (-Y)) hp hn
    (hnonneg Y) (hnonneg (-Y)) hb hfp hfn

end ProbabilityTheory

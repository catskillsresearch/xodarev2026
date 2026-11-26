/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.NflvrDefs
public import SignatureVolatility.NflvrCone
public import SignatureVolatility.ProlongedBrownianSetup.PaperSig
public import SignatureVolatility.ItoCalculusKit.JointPast
public import SignatureVolatility.ItoCalculusKit.MathFinBridge
public import SignatureVolatility.ItoCalculusKit.CrossVariation
public import SignatureVolatility.ProlongedBrownianSetup.PaperSigDynamics

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Section 1: Filtration Equality & Predictable Version of A.S.-Continuous Processes -/

/-- `(paperSig2 B 0)` generates the same filtration as `pathFiltration B`. -/
lemma sigFiltration_eq_pathFiltration {d : ℕ} (B : MultiBrownian Ω P d) (t : ℝ) :
    (generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
      (measurable_paperSig2_coeff B 0)).σAlg t = (pathFiltration B).σAlg t := by
  refine le_antisymm
    (iSup_le fun u => iSup_le fun I =>
      (measurable_paperSig2_coeff_pathFiltration B le_rfl u.2.1 u.2.2 I).comap_le)
    (iSup_le fun u => iSup_le fun i => by
      change MeasurableSpace.comap (fun ω => MultiBrownian.W B u.1 ω i) inferInstance ≤
        ⨆ (v : {s : ℝ // 0 ≤ s ∧ s ≤ t}) (I : Word (d + 1)),
          MeasurableSpace.comap (fun ω => (paperSig2 B 0 v.1 ω).coeff I) inferInstance
      have hW : (fun ω => MultiBrownian.W B u.1 ω i) =
          fun ω => (paperSig2 B 0 u.1 ω).coeff [i.succ] := funext fun ω => by
        rw [paperSig2_space, MultiBrownian.W_zero, sub_zero]
      rw [hW]
      refine le_trans
        (le_iSup (f := fun I : Word (d + 1) =>
          MeasurableSpace.comap (fun ω => (paperSig2 B 0 u.1 ω).coeff I) inferInstance) [i.succ])
        (le_iSup (f := fun v : {s : ℝ // 0 ≤ s ∧ s ≤ t} =>
          ⨆ I : Word (d + 1),
            MeasurableSpace.comap (fun ω => (paperSig2 B 0 v.1 ω).coeff I) inferInstance) u))

lemma predSigma_le_prod {σAlg : ℝ → MeasurableSpace Ω} {T : ℝ}
    (hle : ∀ t ∈ Icc 0 T, σAlg t ≤ m₀) :
    predSigma σAlg T ≤ Prod.instMeasurableSpace := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨a, b, A, ha, hab, hb, hA, rfl⟩
  exact measurableSet_Ioc.prod (hle a ⟨ha, hab.trans hb⟩ A hA)

lemma measurable_slice_of_predSigma {σAlg : ℝ → MeasurableSpace Ω} {T : ℝ}
    (hmono : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t → t ≤ T → σAlg s ≤ σAlg t)
    {H : ℝ → Ω → ℝ} (hH : IsPredictableProcess σAlg T H)
    {s : ℝ} (_hs0 : 0 ≤ s) (hsT : s ≤ T) :
    Measurable[σAlg s] (H s) := by
  have hsec : @Measurable Ω (ℝ × Ω) (σAlg s) (predSigma σAlg T) (fun ω => (s, ω)) := by
    let : MeasurableSpace Ω := σAlg s
    refine measurable_generateFrom ?_
    rintro _ ⟨a, b, A, ha, _, _, hA, rfl⟩
    by_cases hsab : s ∈ Ioc a b
    · have heq : (fun ω => (s, ω)) ⁻¹' (Ioc a b ×ˢ A) = A := by ext ω; simp [hsab]
      rw [heq]; exact hmono ha hsab.1.le hsT A hA
    · have heq : (fun ω => (s, ω)) ⁻¹' (Ioc a b ×ˢ A) = ∅ := by ext ω; simp [hsab]
      rw [heq]; exact MeasurableSet.empty
  exact @Measurable.comp Ω (ℝ × Ω) ℝ (σAlg s) (predSigma σAlg T) _ _ _ hH hsec

/-- Product measure `(volume.restrict (Icc 0 T)).prod P`. -/
def dtP (P : Measure Ω) (T : ℝ) : Measure (ℝ × Ω) :=
  (volume.restrict (Icc 0 T)).prod P

omit m₀ in
/-- Membership of a predictable rectangle in the generating family of `predSigma`. -/
lemma mem_predSigma_generators {σAlg : ℝ → MeasurableSpace Ω} {T a b : ℝ} {A : Set Ω}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (hA : MeasurableSet[σAlg a] A) :
    Ioc a b ×ˢ A ∈
      {S | ∃ (a b : ℝ) (A : Set Ω), 0 ≤ a ∧ a ≤ b ∧ b ≤ T ∧
        MeasurableSet[σAlg a] A ∧ S = Ioc a b ×ˢ A} :=
  ⟨a, b, A, ha, hab, hb, hA, rfl⟩

lemma measurableSet_predSigma_rect {σAlg : ℝ → MeasurableSpace Ω} {T a b : ℝ} {A : Set Ω}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (hA : MeasurableSet[σAlg a] A) :
    MeasurableSet[predSigma σAlg T] (Ioc a b ×ˢ A) :=
  MeasurableSpace.measurableSet_generateFrom (mem_predSigma_generators ha hab hb hA)

omit [IsProbabilityMeasure P] in
/-- Any adapted, a.s.-continuous process on `[0, T]` has a `predSigma`-measurable version
indistinguishable from it on `(0, T]`. -/
lemma exists_pred_indistinguishable_of_ae_continuous {σAlg : ℝ → MeasurableSpace Ω}
    {T : ℝ} (hT : 0 < T) {X : ℝ → Ω → ℝ}
    (hadapt : ∀ t ∈ Icc 0 T, Measurable[σAlg t] (X t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc 0 T)) :
    ∃ X' : ℝ → Ω → ℝ, IsPredictableProcess σAlg T X' ∧
      ∀ᵐ ω ∂P, ∀ s ∈ Ioc 0 T, X' s ω = X s ω := by
  let approx (r : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
    ∑ k ∈ Finset.range (2 ^ r),
      if (k : ℝ) * T / (2 ^ r : ℝ) < s ∧ s ≤ ((k + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ)
      then X ((k : ℝ) * T / (2 ^ r : ℝ)) ω else 0
  have happrox_pred : ∀ r, IsPredictableProcess σAlg T (approx r) := fun r => by
    let : MeasurableSpace (ℝ × Ω) := predSigma σAlg T
    unfold IsPredictableProcess Function.uncurry approx
    refine Finset.measurable_sum _ fun k hk => ?_
    set a : ℝ := (k : ℝ) * T / (2 ^ r : ℝ)
    set b : ℝ := ((k + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ)
    have ha0 : 0 ≤ a := by positivity
    have hab : a ≤ b := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by push_cast; linarith) hT.le) (by positivity)
    have hbT : b ≤ T := by
      simp only [b]; rw [div_le_iff₀ (by positivity)]
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (2 ^ r : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      nlinarith
    have hrect : MeasurableSet[predSigma σAlg T] (Ioc a b ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predSigma_rect ha0 hab hbT MeasurableSet.univ
    intro B hB
    by_cases h0 : (0 : ℝ) ∈ B
    · have heq : (fun p : ℝ × Ω => if a < p.1 ∧ p.1 ≤ b then X a p.2 else 0) ⁻¹' B =
          (Ioc a b ×ˢ (X a ⁻¹' B)) ∪ (Ioc a b ×ˢ (Set.univ : Set Ω))ᶜ := by
        ext ⟨s, ω⟩; by_cases hs : a < s ∧ s ≤ b <;> simp [hs, h0]
      rw [heq]
      exact (measurableSet_predSigma_rect ha0 hab hbT
        (hadapt a ⟨ha0, hab.trans hbT⟩ hB)).union hrect.compl
    · have heq : (fun p : ℝ × Ω => if a < p.1 ∧ p.1 ≤ b then X a p.2 else 0) ⁻¹' B =
          Ioc a b ×ˢ (X a ⁻¹' B) := by
        ext ⟨s, ω⟩; by_cases hs : a < s ∧ s ≤ b <;> simp [hs, h0]
      rw [heq]
      exact measurableSet_predSigma_rect ha0 hab hbT (hadapt a ⟨ha0, hab.trans hbT⟩ hB)
  refine ⟨fun s ω => limUnder atTop fun r => approx r s ω, ?_, ?_⟩
  · let : MeasurableSpace (ℝ × Ω) := predSigma σAlg T
    exact (StronglyMeasurable.limUnder fun r => (happrox_pred r).stronglyMeasurable).measurable
  · filter_upwards [hcont] with ω hω s hs
    have hlim : Tendsto (fun r => approx r s ω) atTop (𝓝 (X s ω)) := by
      rw [Metric.tendsto_atTop]; intro ε hε
      obtain ⟨δ, hδ, hδ_bd⟩ := Metric.continuousWithinAt_iff.mp (hω s ⟨hs.1.le, hs.2⟩) ε hε
      obtain ⟨R, hR⟩ := exists_nat_gt (T / δ)
      refine ⟨R, fun r hr => ?_⟩
      set k : ℕ := ⌈s * (2 ^ r : ℝ) / T⌉₊ - 1
      have hpos_mul : 0 < s * (2 ^ r : ℝ) / T := by have := hs.1; positivity
      have hceil_pos : 1 ≤ ⌈s * (2 ^ r : ℝ) / T⌉₊ := Nat.one_le_iff_ne_zero.mpr fun h0 =>
        not_le.mpr hpos_mul (Nat.ceil_eq_zero.mp h0)
      have hceil_le : ⌈s * (2 ^ r : ℝ) / T⌉₊ ≤ 2 ^ r := Nat.ceil_le.mpr <| by
        rw [div_le_iff₀ hT]; push_cast
        nlinarith [hs.2, show (0 : ℝ) < (2 : ℝ) ^ r by positivity]
      have hk_lt : k < 2 ^ r := by omega
      have hk1 : (k : ℝ) * T / (2 ^ r : ℝ) < s := by
        have hlt := Nat.lt_ceil.mp (show k < ⌈s * (2 ^ r : ℝ) / T⌉₊ by omega)
        rw [div_lt_iff₀ (by positivity)]; linarith [(lt_div_iff₀ hT).mp hlt]
      have hk2 : s ≤ ((k + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ) := by
        have hle := Nat.le_ceil (s * (2 ^ r : ℝ) / T)
        rw [show k + 1 = ⌈s * (2 ^ r : ℝ) / T⌉₊ by omega, le_div_iff₀ (by positivity)]
        linarith [(div_le_iff₀ hT).mp hle]
      have happrox_eq : approx r s ω = X ((k : ℝ) * T / (2 ^ r : ℝ)) ω := by
        unfold approx
        rw [Finset.sum_eq_single k]
        · exact ite_eq_left ⟨hk1, hk2⟩
        · intro j _ hjk
          by_cases hcond : (j : ℝ) * T / (2 ^ r : ℝ) < s ∧ s ≤ ((j + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ)
          · exfalso; rcases lt_or_gt_of_ne hjk with hlt | hgt
            · have : ((j + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ) ≤ (k : ℝ) * T / (2 ^ r : ℝ) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hT.le) (by positivity)
              linarith [hcond.2, hk1]
            · have : ((k + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ) ≤ (j : ℝ) * T / (2 ^ r : ℝ) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (by exact_mod_cast hgt) hT.le) (by positivity)
              linarith [hcond.1, hk2]
          · exact ite_eq_right hcond
        · intro h; exact absurd (Finset.mem_range.mpr hk_lt) h
      rw [happrox_eq]
      have hpt_mem : (k : ℝ) * T / (2 ^ r : ℝ) ∈ Icc 0 T := ⟨by positivity, hk1.le.trans hs.2⟩
      have hstep : ((k + 1 : ℕ) : ℝ) * T / (2 ^ r : ℝ) - (k : ℝ) * T / (2 ^ r : ℝ) = T / (2 ^ r : ℝ) := by
        push_cast; ring
      have h2r : T / (2 ^ r : ℝ) < δ := by
        have hlt : T / δ < (2 ^ r : ℝ) := lt_of_lt_of_le hR (by
          exact_mod_cast hr.trans (Nat.lt_two_pow_self (n := r)).le)
        rw [div_lt_iff₀ (by positivity)]; linarith [(div_lt_iff₀ hδ).mp hlt]
      have hdist : dist ((k : ℝ) * T / (2 ^ r : ℝ)) s < δ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hk1)]; linarith
      exact hδ_bd hpt_mem hdist
    exact hlim.limUnder_eq

/-! ## Section 2: Joint-Filtration Elementary Processes, Isometry & π-λ Density -/

/-- Self-contained telescoping sum on `Finset.Ico a b`. -/
private lemma sum_Ico_sub {α : Type*} [AddCommGroup α] (f : ℕ → α) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) = f b - f a := by
  induction hab with
  | refl => simp
  | @step m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ih]; abel

/-- Elementary predictable process on `[0, T]` for `pathFiltration B`. -/
structure JointElem {d : ℕ} (B : MultiBrownian Ω P d) (T : ℝ) where
  n : ℕ
  a : Fin n → ℝ
  b : Fin n → ℝ
  h : Fin n → Ω → ℝ
  hab : ∀ j, 0 ≤ a j ∧ a j ≤ b j ∧ b j ≤ T
  h_meas : ∀ j, Measurable[(pathFiltration B).σAlg (a j)] (h j)
  h_bdd : ∀ j, ∃ C : ℝ, ∀ ω, |h j ω| ≤ C

def JointElem.toFun {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U : JointElem B T)
    (s : ℝ) (ω : Ω) : ℝ :=
  ∑ j : Fin U.n, if U.a j < s ∧ s ≤ U.b j then U.h j ω else 0

def JointElem.ito {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (U : JointElem B T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ j : Fin U.n, U.h j ω *
    (MultiBrownian.W B (min (U.b j) t) ω (kitDriver hd) -
     MultiBrownian.W B (min (U.a j) t) ω (kitDriver hd))

def JointElem.zero {d : ℕ} (B : MultiBrownian Ω P d) (T : ℝ) : JointElem B T :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩

def JointElem.neg {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U : JointElem B T) : JointElem B T :=
  ⟨U.n, U.a, U.b, fun j ω => -U.h j ω, U.hab, fun j => (U.h_meas j).neg,
    fun j => let ⟨C, hC⟩ := U.h_bdd j; ⟨C, fun ω => by rw [abs_neg]; exact hC ω⟩⟩

def JointElem.add {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U V : JointElem B T) : JointElem B T where
  n := U.n + V.n
  a := Fin.append U.a V.a
  b := Fin.append U.b V.b
  h := Fin.append U.h V.h
  hab := Fin.addCases
    (fun i => by
      have h := U.hab i
      rw [← Fin.append_left U.a V.a i, ← Fin.append_left U.b V.b i] at h
      exact h)
    (fun i => by
      have h := V.hab i
      rw [← Fin.append_right U.a V.a i, ← Fin.append_right U.b V.b i] at h
      exact h)
  h_meas := Fin.addCases
    (fun i => by
      have h := U.h_meas i
      rw [← Fin.append_left U.a V.a i, ← Fin.append_left U.h V.h i] at h
      exact h)
    (fun i => by
      have h := V.h_meas i
      rw [← Fin.append_right U.a V.a i, ← Fin.append_right U.h V.h i] at h
      exact h)
  h_bdd := Fin.addCases
    (fun i => by
      have h := U.h_bdd i
      rw [← Fin.append_left U.h V.h i] at h
      exact h)
    (fun i => by
      have h := V.h_bdd i
      rw [← Fin.append_right U.h V.h i] at h
      exact h)

def JointElem.smul {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (c : ℝ) (U : JointElem B T) : JointElem B T :=
  ⟨U.n, U.a, U.b, fun j ω => c * U.h j ω, U.hab, fun j => measurable_const.mul (U.h_meas j),
    fun j => let ⟨C, hC⟩ := U.h_bdd j; ⟨|c| * max C 0, fun ω => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hC ω).trans (le_max_left _ _)) (abs_nonneg c)⟩⟩

lemma JointElem.add_toFun {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U V : JointElem B T) (s : ℝ) (ω : Ω) :
    (U.add V).toFun s ω = U.toFun s ω + V.toFun s ω := by
  simp only [JointElem.toFun, JointElem.add]
  change (∑ j : Fin (U.n + V.n),
      if Fin.append U.a V.a j < s ∧ s ≤ Fin.append U.b V.b j then Fin.append U.h V.h j ω else 0) = _
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

lemma JointElem.add_ito {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ} (U V : JointElem B T) (t : ℝ) (ω : Ω) :
    (U.add V).ito hd t ω = U.ito hd t ω + V.ito hd t ω := by
  simp only [JointElem.ito, JointElem.add]
  change (∑ j : Fin (U.n + V.n),
      Fin.append U.h V.h j ω *
        (MultiBrownian.W B (min (Fin.append U.b V.b j) t) ω (kitDriver hd) -
         MultiBrownian.W B (min (Fin.append U.a V.a j) t) ω (kitDriver hd))) = _
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

lemma JointElem.neg_toFun {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U : JointElem B T) (s : ℝ) (ω : Ω) :
    U.neg.toFun s ω = -U.toFun s ω := by
  simp only [JointElem.toFun, JointElem.neg]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h <;> simp [h]

lemma JointElem.neg_ito {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ} (U : JointElem B T) (t : ℝ) (ω : Ω) :
    U.neg.ito hd t ω = -U.ito hd t ω := by
  simp only [JointElem.ito, JointElem.neg, neg_mul, Finset.sum_neg_distrib]
  rfl

lemma JointElem.measurable_pred {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U : JointElem B T) :
    IsPredictableProcess (pathFiltration B).σAlg T U.toFun := by
  let : MeasurableSpace (ℝ × Ω) := predSigma (pathFiltration B).σAlg T
  unfold IsPredictableProcess Function.uncurry JointElem.toFun
  refine Finset.measurable_sum _ fun j _ => ?_
  have hrect : MeasurableSet[predSigma (pathFiltration B).σAlg T]
      (Ioc (U.a j) (U.b j) ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predSigma_rect (U.hab j).1 (U.hab j).2.1 (U.hab j).2.2 MeasurableSet.univ
  intro S hS
  by_cases h0 : (0 : ℝ) ∈ S
  · have heq : (fun p : ℝ × Ω => if U.a j < p.1 ∧ p.1 ≤ U.b j then U.h j p.2 else 0) ⁻¹' S =
        (Ioc (U.a j) (U.b j) ×ˢ (U.h j ⁻¹' S)) ∪ (Ioc (U.a j) (U.b j) ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext ⟨s, ω⟩; by_cases hs : U.a j < s ∧ s ≤ U.b j <;> simp [hs, h0]
    rw [heq]
    exact (measurableSet_predSigma_rect (U.hab j).1 (U.hab j).2.1 (U.hab j).2.2
      (U.h_meas j hS)).union hrect.compl
  · have heq : (fun p : ℝ × Ω => if U.a j < p.1 ∧ p.1 ≤ U.b j then U.h j p.2 else 0) ⁻¹' S =
        Ioc (U.a j) (U.b j) ×ˢ (U.h j ⁻¹' S) := by
      ext ⟨s, ω⟩; by_cases hs : U.a j < s ∧ s ≤ U.b j <;> simp [hs, h0]
    rw [heq]
    exact measurableSet_predSigma_rect (U.hab j).1 (U.hab j).2.1 (U.hab j).2.2
      (U.h_meas j hS)

lemma isFiniteMeasure_dtP {T : ℝ} : IsFiniteMeasure (dtP P T) := by
  unfold dtP
  have : IsFiniteMeasure (volume.restrict (Icc 0 T)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  infer_instance

lemma JointElem.memLp_dtP {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (U : JointElem B T) :
    MemLp (Function.uncurry U.toFun) 2 (dtP P T) := by
  choose Cj hCj using U.h_bdd
  have : IsFiniteMeasure (dtP P T) := isFiniteMeasure_dtP
  refine MemLp.of_bound
    (U.measurable_pred.mono (predSigma_le_prod (T := T) fun t _ => (pathFiltration B).le_ambient t) le_rfl).aestronglyMeasurable
    (∑ j : Fin U.n, max (Cj j) 0) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs
    (f := fun j : Fin U.n => if U.a j < p.1 ∧ p.1 ≤ U.b j then U.h j p.2 else 0) Finset.univ).trans
    (Finset.sum_le_sum fun j _ => ?_)
  split_ifs
  · exact (hCj j p.2).trans (le_max_left _ _)
  · rw [abs_zero]; exact le_max_right _ _

/-- Sorted-partition elementary process (disjoint ordered intervals `(pts k, pts (k+1)]`). -/
structure SortedElem {d : ℕ} (B : MultiBrownian Ω P d) (T : ℝ) where
  m : ℕ
  pts : Fin (m + 1) → ℝ
  c : Fin m → Ω → ℝ
  h0 : pts 0 = 0
  hT : pts (Fin.last m) = T
  hmono : ∀ k : Fin m, pts k.castSucc ≤ pts k.succ
  hc_meas : ∀ k : Fin m, Measurable[(pathFiltration B).σAlg (pts k.castSucc)] (c k)
  hc_bdd : ∀ k : Fin m, ∃ C : ℝ, ∀ ω, |c k ω| ≤ C

def SortedElem.toFun {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (G : SortedElem B T)
    (s : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin G.m, if G.pts k.castSucc < s ∧ s ≤ G.pts k.succ then G.c k ω else 0

def SortedElem.ito {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (G : SortedElem B T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin G.m, G.c k ω *
    (MultiBrownian.W B (min (G.pts k.succ) t) ω (kitDriver hd) -
     MultiBrownian.W B (min (G.pts k.castSucc) t) ω (kitDriver hd))

lemma sortedElem_pts_mono {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (G : SortedElem B T) :
    Monotone G.pts :=
  Fin.monotone_iff_le_succ.mpr fun k => G.hmono k

lemma sortedElem_pts_mem {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (G : SortedElem B T)
    (k : Fin (G.m + 1)) : G.pts k ∈ Icc 0 T :=
  ⟨(le_of_eq G.h0.symm).trans (sortedElem_pts_mono G (Fin.zero_le k)),
   (sortedElem_pts_mono G (Fin.le_last k)).trans (le_of_eq G.hT)⟩

/-- Refine any `JointElem` onto a sorted partition of `[0, T]` via `Finset.orderEmbOfFin`. -/
lemma jointElem_to_sortedElem {d : ℕ} {B : MultiBrownian Ω P d} {T : ℝ} (hT : 0 < T)
    (U : JointElem B T) :
    ∃ G : SortedElem B T,
      (∀ s ∈ Ioc 0 T, ∀ ω, G.toFun s ω = U.toFun s ω) ∧
      (∀ (hd : 0 < d), ∀ t ∈ Icc 0 T, ∀ ω, G.ito hd t ω = U.ito hd t ω) := by
  let S : Finset ℝ := insert 0 (insert T (Finset.univ.image U.a ∪ Finset.univ.image U.b))
  have hS_sub : ∀ x ∈ S, x ∈ Icc 0 T := fun x hx => by
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨le_rfl, hT.le⟩
    · exact ⟨hT.le, le_rfl⟩
    · exact ⟨(U.hab j).1, (U.hab j).2.1.trans (U.hab j).2.2⟩
    · exact ⟨(U.hab j).1.trans (U.hab j).2.1, (U.hab j).2.2⟩
  have h0_mem : (0 : ℝ) ∈ S := Finset.mem_insert_self 0 _
  have hT_mem : T ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self T _)
  have hS_card : 2 ≤ S.card := by
    have hsub : ({0, T} : Finset ℝ) ⊆ S := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({0, T} : Finset ℝ).card := (Finset.card_pair hT.ne).symm
      _ ≤ S.card := Finset.card_le_card hsub
  set m : ℕ := S.card - 1
  have hm1 : S.card = m + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ S.card)).symm
  let e : Fin (m + 1) ↪o ℝ := S.orderEmbOfFin hm1
  have hstrict : StrictMono e := e.strictMono
  have he_mem : ∀ k, e k ∈ S := fun k => Finset.orderEmbOfFin_mem S hm1 k
  have hmem_range : ∀ x ∈ S, ∃ k : Fin (m + 1), e k = x := fun x hx => by
    have hr : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin S hm1]; exact hx
    exact hr
  have h0_eq : e 0 = 0 := by
    refine le_antisymm ?_ (hS_sub _ (he_mem 0)).1
    obtain ⟨k, hk⟩ := hmem_range 0 h0_mem
    rw [← hk]; exact hstrict.monotone (Fin.zero_le k)
  have hT_eq : e (Fin.last m) = T := by
    refine le_antisymm (hS_sub _ (he_mem (Fin.last m))).2 ?_
    obtain ⟨k, hk⟩ := hmem_range T hT_mem
    rw [← hk]; exact hstrict.monotone (Fin.le_last k)
  let c : Fin m → Ω → ℝ := fun k ω =>
    ∑ j : Fin U.n, if U.a j ≤ e k.castSucc ∧ e k.succ ≤ U.b j then U.h j ω else 0
  let G : SortedElem B T :=
    { m := m, pts := e, c := c, h0 := h0_eq, hT := hT_eq,
      hmono := fun k => (hstrict (Fin.castSucc_lt_succ (i := k))).le,
      hc_meas := fun k => Finset.measurable_sum _ fun j _ => by
        split_ifs with hcond
        · exact (U.h_meas j).mono ((pathFiltration B).mono hcond.1) le_rfl
        · exact measurable_const,
      hc_bdd := fun k => by
        choose Cj hCj using U.h_bdd
        refine ⟨∑ j : Fin U.n, max (Cj j) 0, fun ω =>
          (Finset.abs_sum_le_sum_abs
            (f := fun j : Fin U.n => if U.a j ≤ e k.castSucc ∧ e k.succ ≤ U.b j then U.h j ω else 0)
            Finset.univ).trans (Finset.sum_le_sum fun j _ => ?_)⟩
        split_ifs
        · exact (hCj j ω).trans (le_max_left _ _)
        · rw [abs_zero]; exact le_max_right _ _ }
  have hno_mid : ∀ (k : Fin m) (x : ℝ), x ∈ S → x ≤ e k.castSucc ∨ e k.succ ≤ x := by
    intro k x hx
    obtain ⟨i, rfl⟩ := hmem_range x hx
    rcases le_or_gt i.1 k.1 with hle | hgt
    · left; exact hstrict.monotone (show i ≤ k.castSucc from hle)
    · right; exact hstrict.monotone (show k.succ ≤ i from hgt)
  refine ⟨G, ?_, ?_⟩
  · intro s hs ω
    have hex : ∃ k : Fin m, e k.castSucc < s ∧ s ≤ e k.succ := by
      let F : Finset (Fin (m + 1)) := Finset.univ.filter fun k : Fin (m + 1) => s ≤ e k
      have hne : F.Nonempty :=
        ⟨Fin.last m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT_eq ▸ hs.2⟩⟩
      let r : Fin (m + 1) := F.min' hne
      have hr_ge : s ≤ e r := (Finset.mem_filter.mp (F.min'_mem hne)).2
      have hr_pos : 0 < r.1 := by
        by_contra h0
        have hr0 : r = 0 := Fin.ext (by change r.1 = 0; omega)
        rw [hr0, h0_eq] at hr_ge; linarith [hs.1]
      have hk_lt_m : r.1 - 1 < m := by have := r.isLt; omega
      let k0 : Fin m := ⟨r.1 - 1, hk_lt_m⟩
      have hsucc : k0.succ = r := Fin.ext (by simp only [k0, Fin.val_succ]; omega)
      refine ⟨k0, ?_, by rw [hsucc]; exact hr_ge⟩
      by_contra hle; push Not at hle
      have hmin : r ≤ k0.castSucc := F.min'_le k0.castSucc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
      have : r.1 ≤ r.1 - 1 := hmin
      omega
    obtain ⟨k0, hk0_lt, hk0_le⟩ := hex
    have hG_eq : G.toFun s ω = c k0 ω := by
      unfold SortedElem.toFun; rw [Finset.sum_eq_single k0]
      · simp only [G, hk0_lt, hk0_le, and_self, ↓reduceIte]
      · intro k _ hkk0
        have hnc : ¬ (e k.castSucc < s ∧ s ≤ e k.succ) := fun h => by
          rcases lt_or_gt_of_ne hkk0 with hlt | hgt
          · have : e k.succ ≤ e k0.castSucc := hstrict.monotone (show k.succ ≤ k0.castSucc from hlt)
            linarith [h.2, hk0_lt]
          · have : e k0.succ ≤ e k.castSucc := hstrict.monotone (show k0.succ ≤ k.castSucc from hgt)
            linarith [h.1, hk0_le]
        simp only [G, hnc, ↓reduceIte]
      · intro h; exact absurd (Finset.mem_univ k0) h
    rw [hG_eq]; unfold c JointElem.toFun
    refine Finset.sum_congr rfl fun j _ => ?_
    have haS : U.a j ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
    have hbS : U.b j ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
    have hiff : (U.a j ≤ e k0.castSucc ∧ e k0.succ ≤ U.b j) ↔ (U.a j < s ∧ s ≤ U.b j) := by
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_lt h1 hk0_lt, hk0_le.trans h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨(hno_mid k0 (U.a j) haS).resolve_right (by linarith),
                (hno_mid k0 (U.b j) hbS).resolve_left (by linarith)⟩
    by_cases h : U.a j < s ∧ s ≤ U.b j <;> simp [hiff, h]
  · intro hd t _ ω
    unfold SortedElem.ito JointElem.ito; simp only [G, c, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have haS : U.a j ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
    have hbS : U.b j ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
    obtain ⟨ia, hia⟩ := hmem_range (U.a j) haS
    obtain ⟨ib, hib⟩ := hmem_range (U.b j) hbS
    have hab_idx : ia.1 ≤ ib.1 := by
      by_contra hgt; push Not at hgt
      exact not_lt.mpr (U.hab j).2.1 (hia ▸ hib ▸ hstrict (show ib < ia from hgt))
    let f : ℕ → ℝ := fun k => if hk : k < m + 1 then
      MultiBrownian.W B (min (e ⟨k, hk⟩) t) ω (kitDriver hd) else 0
    let g : ℕ → ℝ := fun k =>
      if hk : k < m then
        (if U.a j ≤ e ⟨k, by omega⟩ ∧ e ⟨k + 1, by omega⟩ ≤ U.b j then U.h j ω else 0) *
          (MultiBrownian.W B (min (e ⟨k + 1, by omega⟩) t) ω (kitDriver hd) -
           MultiBrownian.W B (min (e ⟨k, by omega⟩) t) ω (kitDriver hd))
      else 0
    have hmatch :
        ∑ k : Fin m, (if U.a j ≤ e k.castSucc ∧ e k.succ ≤ U.b j then U.h j ω else 0) *
          (MultiBrownian.W B (min (e k.succ) t) ω (kitDriver hd) -
           MultiBrownian.W B (min (e k.castSucc) t) ω (kitDriver hd)) =
        ∑ k ∈ Finset.range m, g k := by
      rw [← Fin.sum_univ_eq_sum_range g m]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [g, k.isLt, ↓reduceDIte]
      rfl
    have hsum_eq : ∑ k ∈ Finset.range m, g k =
        U.h j ω * ∑ k ∈ Finset.Ico ia.1 ib.1, (f (k + 1) - f k) := by
      rw [Finset.mul_sum]
      have hsub : Finset.Ico ia.1 ib.1 ⊆ Finset.range m := fun k hk => by
        have hk' := Finset.mem_Ico.mp hk; have := ib.isLt
        rw [Finset.mem_range]; omega
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_Ico.mp hk; have hib_lt := ib.isLt
        have hkm : k < m := by omega
        have hk1 : k + 1 < m + 1 := by omega
        have hk0 : k < m + 1 := by omega
        have h1 : U.a j ≤ e ⟨k, hk0⟩ := by rw [← hia]; exact hstrict.monotone (show ia ≤ ⟨k, hk0⟩ from hk'.1)
        have h2 : e ⟨k + 1, hk1⟩ ≤ U.b j := by rw [← hib]; exact hstrict.monotone (show ⟨k + 1, hk1⟩ ≤ ib from hk'.2)
        simp only [g, hkm, ↓reduceDIte, h1, h2, and_self, ↓reduceIte, f, hk1, hk0]
      · intro k hk hnot
        have hkm : k < m := Finset.mem_range.mp hk
        have hnc : ¬ (U.a j ≤ e ⟨k, by omega⟩ ∧ e ⟨k + 1, by omega⟩ ≤ U.b j) := by
          rintro ⟨h1, h2⟩; apply hnot; rw [Finset.mem_Ico]
          have h1' : ia.1 ≤ k := by
            by_contra h; push Not at h
            exact not_lt.mpr h1 (hia ▸ hstrict (show (⟨k, by omega⟩ : Fin (m + 1)) < ia from h))
          have h2' : k + 1 ≤ ib.1 := by
            by_contra h; push Not at h
            exact not_lt.mpr h2 (hib ▸ hstrict (show ib < (⟨k + 1, by omega⟩ : Fin (m + 1)) from h))
          exact ⟨h1', by omega⟩
        simp only [g, hkm, ↓reduceDIte, hnc, ↓reduceIte, zero_mul]
    rw [hmatch, hsum_eq, sum_Ico_sub f hab_idx]
    simp only [f, ib.isLt, ia.isLt, ↓reduceDIte, hia, hib]

/-- Exact Itô isometry on a `SortedElem` at `t ∈ [0, T]` via `indepFun_pathFiltration_wnnIncr`. -/
lemma integral_sortedElem_ito_sq {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (G : SortedElem B T) {t : ℝ} (ht0 : 0 ≤ t) (_htT : t ≤ T) :
    ∫ ω, G.ito hd t ω ^ 2 ∂P =
      ∑ k : Fin G.m, (∫ ω, G.c k ω ^ 2 ∂P) * (min (G.pts k.succ) t - min (G.pts k.castSucc) t) := by
  let Δ (k : Fin G.m) (ω : Ω) : ℝ :=
    G.c k ω * wnnIncr B (kitDriver hd) (min (G.pts k.castSucc) t) (min (G.pts k.succ) t) ω
  have hrew : ∀ ω, G.ito hd t ω = ∑ k : Fin G.m, Δ k ω := fun ω =>
    Finset.sum_congr rfl fun k _ => by simp only [Δ, wnnIncr_eq_W]
  have hΔ_L2 : ∀ k : Fin G.m, MemLp (Δ k) 2 P := fun k => by
    obtain ⟨C, hC⟩ := G.hc_bdd k
    have hstep := min_le_min_right t (G.hmono k)
    have hW := (hasLaw_wnnIncr B (kitDriver hd) (le_min (sortedElem_pts_mem G _).1 ht0) hstep).memLp
      (memLp_id_gaussianReal' 2 (by simp))
    refine (hW.abs.const_mul (max C 0)).mono'
      (((G.hc_meas k).mono ((pathFiltration B).le_ambient _) le_rfl).mul
        (measurable_wnnIncr B (kitDriver hd) _ _)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [Δ, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC ω).trans (le_max_left _ _)) (abs_nonneg _)
  have hcross : ∀ k₁ k₂ : Fin G.m, k₁ < k₂ → ∫ ω, Δ k₁ ω * Δ k₂ ω ∂P = 0 := fun k₁ k₂ h12 => by
    by_cases ht_ge : G.pts k₂.castSucc ≤ t
    · have hmin2 : min (G.pts k₂.castSucc) t = G.pts k₂.castSucc := min_eq_left ht_ge
      have hle1 : G.pts k₁.succ ≤ G.pts k₂.castSucc := sortedElem_pts_mono G (show k₁.succ ≤ k₂.castSucc from h12)
      have hle0 : G.pts k₁.castSucc ≤ G.pts k₂.castSucc := (G.hmono k₁).trans hle1
      have hmin1a : min (G.pts k₁.castSucc) t = G.pts k₁.castSucc := min_eq_left (hle0.trans ht_ge)
      have hmin1b : min (G.pts k₁.succ) t = G.pts k₁.succ := min_eq_left (hle1.trans ht_ge)
      have hstep2 : G.pts k₂.castSucc ≤ min (G.pts k₂.succ) t := le_min (G.hmono k₂) ht_ge
      have hpast_m : Measurable[(pathFiltration B).σAlg (G.pts k₂.castSucc)] (fun ω => Δ k₁ ω * G.c k₂ ω) := by
        have hc1 := (G.hc_meas k₁).mono ((pathFiltration B).mono hle0) le_rfl
        have hW1 : Measurable[(pathFiltration B).σAlg (G.pts k₂.castSucc)]
            (wnnIncr B (kitDriver hd) (min (G.pts k₁.castSucc) t) (min (G.pts k₁.succ) t)) := by
          rw [hmin1a, hmin1b]
          exact measurable_wnnIncr_pathFiltration B (kitDriver hd) (sortedElem_pts_mem G _).1
            (sortedElem_pts_mem G _).1 hle0 hle1
        exact (hc1.mul hW1).mul (G.hc_meas k₂)
      have hind := indepFun_pathFiltration_wnnIncr B (kitDriver hd) hstep2 hpast_m
      have hprod : (fun ω => Δ k₁ ω * Δ k₂ ω) =
          fun ω => (Δ k₁ ω * G.c k₂ ω) * wnnIncr B (kitDriver hd) (G.pts k₂.castSucc) (min (G.pts k₂.succ) t) ω := by
        funext ω; simp only [Δ, hmin2]; ring
      rw [hprod, hind.integral_fun_mul_eq_mul_integral
        (hpast_m.mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
        (measurable_wnnIncr B (kitDriver hd) _ _).aestronglyMeasurable,
        integral_wnnIncr B (kitDriver hd) (sortedElem_pts_mem G _).1 hstep2, mul_zero]
    · have hmin2a : min (G.pts k₂.castSucc) t = t := min_eq_right (le_of_not_ge ht_ge)
      have hmin2b : min (G.pts k₂.succ) t = t := min_eq_right ((le_of_not_ge ht_ge).trans (G.hmono k₂))
      have hzero : (fun ω => Δ k₁ ω * Δ k₂ ω) = fun _ => 0 := funext fun ω => by
        simp [Δ, hmin2a, hmin2b, wnnIncr]
      rw [hzero, integral_zero]
  have hdiag : ∀ k : Fin G.m,
      ∫ ω, Δ k ω ^ 2 ∂P = (∫ ω, G.c k ω ^ 2 ∂P) * (min (G.pts k.succ) t - min (G.pts k.castSucc) t) := fun k => by
    by_cases ht_ge : G.pts k.castSucc ≤ t
    · have hmin1 : min (G.pts k.castSucc) t = G.pts k.castSucc := min_eq_left ht_ge
      have hstep : G.pts k.castSucc ≤ min (G.pts k.succ) t := le_min (G.hmono k) ht_ge
      have hind := (indepFun_pathFiltration_wnnIncr B (kitDriver hd) hstep ((G.hc_meas k).pow_const 2)).comp
        measurable_id (measurable_id.pow_const 2)
      simp only [Function.comp_def, id_eq] at hind
      have hsq : (fun ω => Δ k ω ^ 2) = fun ω => G.c k ω ^ 2 *
          wnnIncr B (kitDriver hd) (G.pts k.castSucc) (min (G.pts k.succ) t) ω ^ 2 := funext fun ω => by
        simp only [Δ, hmin1, mul_pow]
      rw [hsq, hmin1, hind.integral_fun_mul_eq_mul_integral
        (((G.hc_meas k).pow_const 2).mono ((pathFiltration B).le_ambient _) le_rfl).aestronglyMeasurable
        ((measurable_wnnIncr B (kitDriver hd) _ _).pow_const 2).aestronglyMeasurable,
        integral_wnnIncr_sq B (kitDriver hd) (sortedElem_pts_mem G _).1 hstep]
    · have hmin1 : min (G.pts k.castSucc) t = t := min_eq_right (le_of_not_ge ht_ge)
      have hmin2 : min (G.pts k.succ) t = t := min_eq_right ((le_of_not_ge ht_ge).trans (G.hmono k))
      simp [Δ, hmin1, hmin2, wnnIncr]
  simp_rw [hrew, sq, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k₁ _ => integrable_finsetSum _ fun k₂ _ =>
      integrable_mul_of_memLp_two (hΔ_L2 k₁) (hΔ_L2 k₂)]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  rw [integral_finsetSum _ fun k₂ _ => integrable_mul_of_memLp_two (hΔ_L2 k₁) (hΔ_L2 k₂),
    Finset.sum_eq_single k₁]
  · simpa [sq] using hdiag k₁
  · intro k₂ _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [show (fun ω => Δ k₁ ω * Δ k₂ ω) = fun ω => Δ k₂ ω * Δ k₁ ω from funext fun _ => mul_comm _ _]
      exact hcross k₂ k₁ hlt
    · exact hcross k₁ k₂ hgt
  · intro h; exact absurd (Finset.mem_univ k₁) h

/-- Itô isometry on any `JointElem` at `t ∈ [0, T]`. -/
lemma integral_jointElem_ito_sq {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    (U : JointElem B T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ ω, U.ito hd t ω ^ 2 ∂P = ∫ p in Icc 0 t ×ˢ (Set.univ : Set Ω), U.toFun p.1 p.2 ^ 2 ∂(dtP P T) := by
  obtain ⟨G, hG_fun, hG_ito⟩ := jointElem_to_sortedElem hT U
  have h1 : ∫ ω, U.ito hd t ω ^ 2 ∂P =
      ∑ k : Fin G.m, (∫ ω, G.c k ω ^ 2 ∂P) * (min (G.pts k.succ) t - min (G.pts k.castSucc) t) := by
    simp_rw [← hG_ito hd t ⟨ht0, htT⟩]
    exact integral_sortedElem_ito_sq hd G ht0 htT
  rw [h1]
  have hmeas_U := U.memLp_dtP.integrable_sq
  have hcongr : ∫ p in Icc 0 t ×ˢ (Set.univ : Set Ω), U.toFun p.1 p.2 ^ 2 ∂(dtP P T) =
      ∫ p in Ioc 0 t ×ˢ (Set.univ : Set Ω), G.toFun p.1 p.2 ^ 2 ∂(dtP P T) := by
    have hdiff₁ : dtP P T ((Icc 0 t ×ˢ (Set.univ : Set Ω)) \ (Ioc 0 t ×ˢ (Set.univ : Set Ω))) = 0 := by
      have hsub : (Icc 0 t ×ˢ (Set.univ : Set Ω)) \ (Ioc 0 t ×ˢ (Set.univ : Set Ω)) ⊆
          ({0} : Set ℝ) ×ˢ (Set.univ : Set Ω) := by
        rintro ⟨s, ω⟩ ⟨⟨⟨h1, h2⟩, _⟩, h3⟩
        refine ⟨?_, trivial⟩
        have hs0 : s = 0 := le_antisymm (not_lt.mp fun hp => h3 ⟨⟨hp, h2⟩, trivial⟩) h1
        simp [hs0]
      exact measure_mono_null hsub (by simp [dtP, Measure.prod_prod])
    have hdiff₂ : dtP P T ((Ioc 0 t ×ˢ (Set.univ : Set Ω)) \ (Icc 0 t ×ˢ (Set.univ : Set Ω))) = 0 := by
      have hemp : (Ioc 0 t ×ˢ (Set.univ : Set Ω)) \ (Icc 0 t ×ˢ (Set.univ : Set Ω)) = ∅ :=
        Set.sdiff_eq_empty.mpr (Set.prod_mono Ioc_subset_Icc_self Subset.rfl)
      rw [hemp, measure_empty]
    rw [setIntegral_congr_set (ae_eq_set.mpr ⟨hdiff₁, hdiff₂⟩)]
    refine setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) fun p hp => ?_
    rw [hG_fun p.1 ⟨hp.1.1, hp.1.2.trans htT⟩ p.2]
  rw [hcongr]
  have hIoc_eq : Ioc 0 t = ⋃ k : Fin G.m, Ioc (min (G.pts k.castSucc) t) (min (G.pts k.succ) t) := by
    ext s; simp only [Set.mem_Ioc, Set.mem_iUnion]
    constructor
    · rintro ⟨hs0, hst⟩
      let F : Finset (Fin (G.m + 1)) := Finset.univ.filter fun k : Fin (G.m + 1) => s ≤ G.pts k
      have hne : F.Nonempty :=
        ⟨Fin.last G.m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [G.hT]; exact hst.trans htT⟩⟩
      let r : Fin (G.m + 1) := F.min' hne
      have hr_ge : s ≤ G.pts r := (Finset.mem_filter.mp (F.min'_mem hne)).2
      have hr_pos : 0 < r.1 := by
        by_contra h0
        have hr0 : r = 0 := Fin.ext (by change r.1 = 0; omega)
        rw [hr0, G.h0] at hr_ge; linarith
      have hk_lt : r.1 - 1 < G.m := by have := r.isLt; omega
      let k0 : Fin G.m := ⟨r.1 - 1, hk_lt⟩
      have hsucc : k0.succ = r := Fin.ext (by simp only [k0, Fin.val_succ]; omega)
      refine ⟨k0, ?_, le_min (by rw [hsucc]; exact hr_ge) hst⟩
      have hlt : G.pts k0.castSucc < s := by
        by_contra hle; push Not at hle
        have hmin : r ≤ k0.castSucc := F.min'_le k0.castSucc (Finset.mem_filter.mpr ⟨Finset.mem_univ k0.castSucc, hle⟩)
        have : r.1 ≤ r.1 - 1 := hmin
        omega
      exact lt_of_le_of_lt (min_le_left _ _) hlt
    · rintro ⟨k, h1, h2⟩
      exact ⟨lt_of_le_of_lt (le_min (sortedElem_pts_mem G _).1 ht0) h1, h2.trans (min_le_right _ _)⟩
  have hdisj : Pairwise fun k₁ k₂ : Fin G.m =>
      Disjoint (Ioc (min (G.pts k₁.castSucc) t) (min (G.pts k₁.succ) t) ×ˢ (Set.univ : Set Ω))
               (Ioc (min (G.pts k₂.castSucc) t) (min (G.pts k₂.succ) t) ×ˢ (Set.univ : Set Ω)) := by
    intro k₁ k₂ hne
    refine Set.disjoint_left.mpr fun p h1 h2 => ?_
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : min (G.pts k₁.succ) t ≤ min (G.pts k₂.castSucc) t :=
        min_le_min_right t (sortedElem_pts_mono G (show k₁.succ ≤ k₂.castSucc from hlt))
      linarith [h1.1.2, h2.1.1]
    · have : min (G.pts k₂.succ) t ≤ min (G.pts k₁.castSucc) t :=
        min_le_min_right t (sortedElem_pts_mono G (show k₂.succ ≤ k₁.castSucc from hgt))
      linarith [h2.1.2, h1.1.1]
  have hprod_eq : Ioc 0 t ×ˢ (Set.univ : Set Ω) =
      ⋃ k : Fin G.m, (Ioc (min (G.pts k.castSucc) t) (min (G.pts k.succ) t) ×ˢ (Set.univ : Set Ω)) := by
    rw [hIoc_eq, Set.iUnion_prod_const]
  rw [hprod_eq, integral_iUnion_fintype (fun _ => measurableSet_Ioc.prod MeasurableSet.univ) hdisj
    (fun k => hmeas_U.integrableOn.congr_fun (fun p hp => by
      have hpI : p.1 ∈ Ioc 0 T := ⟨lt_of_le_of_lt (le_min (sortedElem_pts_mem G _).1 ht0) hp.1.1,
        hp.1.2.trans ((min_le_right _ _).trans htT)⟩
      rw [hG_fun p.1 hpI p.2]; rfl) (measurableSet_Ioc.prod MeasurableSet.univ))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hon_k : ∀ p ∈ Ioc (min (G.pts k.castSucc) t) (min (G.pts k.succ) t) ×ˢ (Set.univ : Set Ω),
      G.toFun p.1 p.2 ^ 2 = G.c k p.2 ^ 2 := fun p hp => by
    have hcast_le : G.pts k.castSucc ≤ t := by
      have hlt : min (G.pts k.castSucc) t < t :=
        lt_of_lt_of_le hp.1.1 (hp.1.2.trans (min_le_right _ _))
      refine le_of_not_gt fun hgt => ?_
      rw [min_eq_right (le_of_lt hgt)] at hlt
      exact (lt_irrefl t) hlt
    have hp1 : G.pts k.castSucc < p.1 := by
      rw [min_eq_left hcast_le] at hp
      exact hp.1.1
    have hp2 : p.1 ≤ G.pts k.succ := hp.1.2.trans (min_le_left _ _)
    have hval : G.toFun p.1 p.2 = G.c k p.2 := by
      unfold SortedElem.toFun; rw [Finset.sum_eq_single k]
      · simp only [hp1, hp2, and_self, ↓reduceIte]
      · intro k' _ hne
        have hnc : ¬ (G.pts k'.castSucc < p.1 ∧ p.1 ≤ G.pts k'.succ) := fun h => by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := sortedElem_pts_mono G (show k'.succ ≤ k.castSucc from hlt); linarith [h.2, hp1]
          · have := sortedElem_pts_mono G (show k.succ ≤ k'.castSucc from hgt); linarith [h.1, hp2]
        simp only [hnc, ↓reduceIte]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hval]
  rw [setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) hon_k]
  unfold dtP
  have hsubI : Ioc (min (G.pts k.castSucc) t) (min (G.pts k.succ) t) ⊆ Icc 0 T :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc (le_min (sortedElem_pts_mem G _).1 ht0)
      ((min_le_right _ _).trans htT))
  rw [Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ),
    Set.inter_eq_left.mpr (Set.prod_mono hsubI Set.Subset.rfl),
    ← Measure.restrict_prod_eq_prod_univ]
  have hmul := integral_prod_mul
    (μ := volume.restrict (Ioc (min (G.pts k.castSucc) t) (min (G.pts k.succ) t)))
    (ν := P) (f := fun _ : ℝ => (1 : ℝ)) (g := fun ω => G.c k ω ^ 2)
  simp only [one_mul] at hmul
  rw [hmul, integral_const, Measure.real_def, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_min_right t (G.hmono k))),
    smul_eq_mul, mul_one, mul_comm]

/-- Martingale property on `JointElem`: for `0 ≤ s ≤ t ≤ T` and `A ∈ ℱ_s`,
`∫_A U.ito t = ∫_A U.ito s`. -/
lemma setIntegral_jointElem_ito {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ}
    (U : JointElem B T) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[(pathFiltration B).σAlg s] A) :
    ∫ ω in A, U.ito hd t ω ∂P = ∫ ω in A, U.ito hd s ω ∂P := by
  have hi_term : ∀ (j : Fin U.n) (r : ℝ), r ∈ Icc 0 T →
      Integrable (fun ω => U.h j ω *
        (MultiBrownian.W B (min (U.b j) r) ω (kitDriver hd) -
         MultiBrownian.W B (min (U.a j) r) ω (kitDriver hd))) P := fun j r hr => by
    obtain ⟨C, hC⟩ := U.h_bdd j
    have hW := (hasLaw_wnnIncr B (kitDriver hd) (le_min (U.hab j).1 hr.1)
      (min_le_min_right r (U.hab j).2.1)).memLp (memLp_id_gaussianReal' 1 (by simp)) |>.integrable le_rfl
    have hrew : (fun ω => U.h j ω *
        (MultiBrownian.W B (min (U.b j) r) ω (kitDriver hd) -
         MultiBrownian.W B (min (U.a j) r) ω (kitDriver hd))) =
        fun ω => U.h j ω * wnnIncr B (kitDriver hd) (min (U.a j) r) (min (U.b j) r) ω :=
      funext fun ω => by simp only [wnnIncr_eq_W]
    rw [hrew]
    refine (hW.abs.const_mul (max C 0)).mono'
      (((U.h_meas j).mono ((pathFiltration B).le_ambient _) le_rfl).mul
        (measurable_wnnIncr B (kitDriver hd) _ _)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC ω).trans (le_max_left _ _)) (abs_nonneg _)
  have hterm : ∀ j : Fin U.n,
      ∫ ω in A, U.h j ω * (MultiBrownian.W B (min (U.b j) t) ω (kitDriver hd) -
        MultiBrownian.W B (min (U.a j) t) ω (kitDriver hd)) ∂P =
      ∫ ω in A, U.h j ω * (MultiBrownian.W B (min (U.b j) s) ω (kitDriver hd) -
        MultiBrownian.W B (min (U.a j) s) ω (kitDriver hd)) ∂P := fun j => by
    set u := max s (min (U.a j) t)
    set v := max s (min (U.b j) t)
    have hdiff : ∀ ω,
        (MultiBrownian.W B (min (U.b j) t) ω (kitDriver hd) - MultiBrownian.W B (min (U.a j) t) ω (kitDriver hd)) -
        (MultiBrownian.W B (min (U.b j) s) ω (kitDriver hd) - MultiBrownian.W B (min (U.a j) s) ω (kitDriver hd)) =
        wnnIncr B (kitDriver hd) u v ω := fun ω => by
      simp only [wnnIncr_eq_W, u, v]
      rcases le_total (U.a j) s with ha | ha <;> rcases le_total (U.b j) s with hb | hb
      · rw [min_eq_left (ha.trans hst), min_eq_left (hb.trans hst), min_eq_left ha, min_eq_left hb,
          max_eq_left ha, max_eq_left hb]; ring
      · rw [min_eq_left (ha.trans hst), min_eq_left ha, min_eq_right hb,
          max_eq_left ha, max_eq_right (le_min hb hst)]; ring
      · have ha_eq : U.a j = s := le_antisymm ((U.hab j).2.1.trans hb) ha
        have hb_eq : U.b j = s := le_antisymm hb (ha.trans (U.hab j).2.1)
        simp [ha_eq, hb_eq, min_eq_left hst]
      · rw [min_eq_right ha, min_eq_right (ha.trans (U.hab j).2.1),
          max_eq_right (le_min ha hst), max_eq_right (le_min (ha.trans (U.hab j).2.1) hst)]; ring
    rw [← sub_eq_zero, ← integral_sub (hi_term j t ⟨hs0.trans hst, htT⟩).integrableOn
      (hi_term j s ⟨hs0, hst.trans htT⟩).integrableOn]
    have heq : ∫ ω in A, (U.h j ω * (MultiBrownian.W B (min (U.b j) t) ω (kitDriver hd) -
          MultiBrownian.W B (min (U.a j) t) ω (kitDriver hd)) -
        U.h j ω * (MultiBrownian.W B (min (U.b j) s) ω (kitDriver hd) -
          MultiBrownian.W B (min (U.a j) s) ω (kitDriver hd))) ∂P =
        ∫ ω, (A.indicator (U.h j) ω) * wnnIncr B (kitDriver hd) u v ω ∂P := by
      rw [← integral_indicator ((pathFiltration B).le_ambient s A hA)]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases hω : ω ∈ A
      · simp only [Set.indicator_of_mem hω, ← mul_sub, hdiff]
      · simp [hω]
    rw [heq]
    by_cases hta : U.a j ≤ t
    · have huv : u ≤ v := max_le_max_left s (min_le_min_right t (U.hab j).2.1)
      have hu0 : 0 ≤ u := hs0.trans (le_max_left _ _)
      have hsu : s ≤ u := le_max_left _ _
      have hau : U.a j ≤ u := (min_eq_left hta).symm.le.trans (le_max_right _ _)
      have hInd_m : Measurable[(pathFiltration B).σAlg u] (A.indicator (U.h j)) :=
        ((U.h_meas j).mono ((pathFiltration B).mono hau) le_rfl).indicator ((pathFiltration B).mono hsu A hA)
      have hind := indepFun_pathFiltration_wnnIncr B (kitDriver hd) huv hInd_m
      rw [hind.integral_fun_mul_eq_mul_integral
        (hInd_m.mono ((pathFiltration B).le_ambient u) le_rfl).aestronglyMeasurable
        (measurable_wnnIncr B (kitDriver hd) u v).aestronglyMeasurable,
        integral_wnnIncr B (kitDriver hd) hu0 huv, mul_zero]
    · have hlt : t ≤ U.a j := le_of_not_ge hta
      have huv_eq : u = v := by
        simp only [u, v, min_eq_right hlt, min_eq_right (hlt.trans (U.hab j).2.1)]
      simp [huv_eq, wnnIncr]
  unfold JointElem.ito
  rw [integral_finsetSum _ fun j _ => (hi_term j t ⟨hs0.trans hst, htT⟩).integrableOn,
      integral_finsetSum _ fun j _ => (hi_term j s ⟨hs0, hst.trans htT⟩).integrableOn]
  exact Finset.sum_congr rfl fun j _ => hterm j

/-- Private π-λ density helper via `MemLp.induction_dense`: works purely on functions and
`lintegral` (no `Lp`, `indicatorConstLp`, or `Submodule.span`). -/
private lemma exists_jointElem_L2_approx_on_trim {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    (μ : @Measure (ℝ × Ω) (predSigma (pathFiltration B).σAlg T))
    (hμ_fin : @IsFiniteMeasure (ℝ × Ω) (predSigma (pathFiltration B).σAlg T) μ)
    (hμ_compl : μ (Ioc 0 T ×ˢ (Set.univ : Set Ω))ᶜ = 0)
    {Z : ℝ → Ω → ℝ} (hZp : IsPredictableProcess (pathFiltration B).σAlg T Z)
    (hZ_fin : ∫⁻ p, ENNReal.ofReal (Z p.1 p.2 ^ 2) ∂μ < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : JointElem B T, ∫⁻ p, ENNReal.ofReal ((Z p.1 p.2 - U.toFun p.1 p.2) ^ 2) ∂μ < ENNReal.ofReal ε := by
  let : MeasurableSpace (ℝ × Ω) := predSigma (pathFiltration B).σAlg T
  have : IsFiniteMeasure μ := hμ_fin
  have hsq_enorm : ∀ x : ℝ, ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, sq_abs]
  -- 1. Finite sum of `JointElem`s and finite Cauchy–Schwarz
  have hsum_elem : ∀ (N : ℕ) (Us : ℕ → JointElem B T),
      ∃ W : JointElem B T, ∀ s ω, W.toFun s ω = ∑ k ∈ Finset.range N, (Us k).toFun s ω := by
    intro N Us; induction N with
    | zero => exact ⟨JointElem.zero B T, fun s ω => by
        simp only [JointElem.toFun, JointElem.zero]
        exact Finset.sum_eq_zero fun j _ => Fin.elim0 j⟩
    | succ N ih =>
      obtain ⟨W, hW⟩ := ih
      refine ⟨W.add (Us N), fun s ω => ?_⟩
      rw [W.add_toFun, hW, Finset.sum_range_succ]
  have hfin_cs : ∀ (N : ℕ) (a : ℕ → ℝ),
      (∑ k ∈ Finset.range N, a k) ^ 2 ≤ (N : ℝ) * ∑ k ∈ Finset.range N, a k ^ 2 := by
    intro N a; induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_succ]
      have hnn : 0 ≤ ∑ k ∈ Finset.range N, (a k - a N) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hexp : ∑ k ∈ Finset.range N, (a k - a N) ^ 2 =
          (∑ k ∈ Finset.range N, a k ^ 2) - 2 * a N * (∑ k ∈ Finset.range N, a k) + (N : ℝ) * a N ^ 2 := by
        simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hmid : ∑ k ∈ Finset.range N, 2 * a k * a N = 2 * a N * ∑ k ∈ Finset.range N, a k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
        rw [hmid]
      nlinarith
  -- 2. π-λ induction: every `predSigma`-measurable indicator `1_S` is approximated in `L²(μ)` by a `JointElem`
  have hRect_pi : IsPiSystem {S : Set (ℝ × Ω) | ∃ (a b : ℝ) (A : Set Ω),
      0 ≤ a ∧ a ≤ b ∧ b ≤ T ∧ MeasurableSet[(pathFiltration B).σAlg a] A ∧ S = Ioc a b ×ˢ A} := by
    rintro _ ⟨a₁, b₁, A₁, ha₁, hab₁, hb₁, hA₁, rfl⟩ _ ⟨a₂, b₂, A₂, ha₂, hab₂, hb₂, hA₂, rfl⟩ _
    rw [Set.prod_inter_prod, Set.Ioc_inter_Ioc]
    by_cases hle : max a₁ a₂ ≤ min b₁ b₂
    · exact ⟨max a₁ a₂, min b₁ b₂, A₁ ∩ A₂, le_max_of_le_left ha₁, hle, (min_le_left _ _).trans hb₁,
        ((pathFiltration B).mono (le_max_left _ _) A₁ hA₁).inter
        ((pathFiltration B).mono (le_max_right _ _) A₂ hA₂), rfl⟩
    · refine ⟨0, 0, ∅, le_rfl, le_rfl, hT.le,
        @MeasurableSet.empty Ω ((pathFiltration B).σAlg 0), ?_⟩
      rw [Set.Ioc_eq_empty_of_le (le_of_lt (not_le.mp hle)), Set.empty_prod, Set.Ioc_self,
        Set.empty_prod]
  have hind_approx : ∀ (S : Set (ℝ × Ω)), MeasurableSet S → ∀ δ : ℝ, 0 < δ →
      ∃ U : JointElem B T,
        ∫⁻ p, ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ <
          ENNReal.ofReal δ := by
    refine MeasurableSpace.induction_on_inter (m := predSigma (pathFiltration B).σAlg T)
      (C := fun S _ => ∀ δ : ℝ, 0 < δ → ∃ U : JointElem B T,
        ∫⁻ p, ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ <
          ENNReal.ofReal δ)
      rfl hRect_pi ?_ ?_ ?_ ?_
    · -- `∅`
      intro δ hδ
      refine ⟨JointElem.zero B T, ?_⟩
      have h0 : ∀ p : ℝ × Ω,
          ENNReal.ofReal (((JointElem.zero B T).toFun p.1 p.2 - (∅ : Set (ℝ × Ω)).indicator (fun _ => (1 : ℝ)) p) ^ 2) = 0 :=
        fun p => by
          have hz : (JointElem.zero B T).toFun p.1 p.2 = 0 := by
            simp only [JointElem.toFun, JointElem.zero]
            exact Finset.sum_eq_zero fun j _ => Fin.elim0 j
          simp [hz]
      simp_rw [h0, lintegral_zero]
      exact ENNReal.ofReal_pos.mpr hδ
    · -- Rectangle `Ioc a b ×ˢ A`
      rintro _ ⟨a, b, A, ha, hab, hb, hA, rfl⟩ δ hδ
      let U : JointElem B T := ⟨1, fun _ => a, fun _ => b, fun _ => A.indicator 1,
        fun _ => ⟨ha, hab, hb⟩, fun _ => measurable_const.indicator hA,
        fun _ => ⟨1, fun ω => by by_cases h : ω ∈ A <;> simp [h]⟩⟩
      refine ⟨U, ?_⟩
      have h0 : ∀ p : ℝ × Ω,
          ENNReal.ofReal ((U.toFun p.1 p.2 - (Ioc a b ×ˢ A).indicator (fun _ => (1 : ℝ)) p) ^ 2) = 0 := fun p => by
        unfold JointElem.toFun
        by_cases h1 : a < p.1 ∧ p.1 ≤ b <;> by_cases h2 : p.2 ∈ A <;> simp [U, h1, h2]
      simp_rw [h0, lintegral_zero]
      exact ENNReal.ofReal_pos.mpr hδ
    · -- Complement `Sᶜ`
      intro S _ ihS δ hδ
      obtain ⟨U, hU⟩ := ihS δ hδ
      let U1 : JointElem B T := ⟨1, fun _ => 0, fun _ => T, fun _ _ => 1,
        fun _ => ⟨le_rfl, hT.le, le_rfl⟩, fun _ => measurable_const, fun _ => ⟨1, fun _ => by simp⟩⟩
      refine ⟨U1.add U.neg, ?_⟩
      have hae : ∀ᵐ p : ℝ × Ω ∂μ, p ∈ Ioc 0 T ×ˢ (Set.univ : Set Ω) := by
        rw [ae_iff]; exact hμ_compl
      have hcongr : ∫⁻ p, ENNReal.ofReal (((U1.add U.neg).toFun p.1 p.2 - Sᶜ.indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ =
          ∫⁻ p, ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ := by
        refine lintegral_congr_ae (hae.mono fun p hp => ?_)
        change ENNReal.ofReal
            (((U1.add U.neg).toFun p.1 p.2 - Sᶜ.indicator (fun _ => (1 : ℝ)) p) ^ 2) =
          ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2)
        rw [U1.add_toFun, U.neg_toFun]
        have hU1 : U1.toFun p.1 p.2 = 1 := by simp [JointElem.toFun, U1, hp.1.1, hp.1.2]
        rw [hU1]
        by_cases hpS : p ∈ S
        · have hpSc : p ∉ Sᶜ := fun h => h hpS
          rw [Set.indicator_of_mem hpS, Set.indicator_of_notMem hpSc]; congr 1; ring
        · have hpSc : p ∈ Sᶜ := hpS
          rw [Set.indicator_of_notMem hpS, Set.indicator_of_mem hpSc]; congr 1; ring
      rw [hcongr]; exact hU
    · -- Countable disjoint union `⋃ k, f k`
      intro f hdisj hf ihf δ hδ
      have hsum_fin : ∑' k, μ (f k) ≠ ⊤ := by
        rw [← measure_iUnion hdisj hf]; exact measure_ne_top μ _
      have htail_sum : Tendsto (fun N : ℕ => ∑' k, μ (f (k + N))) atTop (𝓝 0) :=
        ENNReal.tendsto_sum_nat_add (fun k => μ (f k)) hsum_fin
      obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp htail_sum) (ENNReal.ofReal (δ / 8))
        (ENNReal.ofReal_pos.mpr (by positivity))
      have htail_le : μ (⋃ k, f (k + N)) ≤ ENNReal.ofReal (δ / 8) := by
        rw [measure_iUnion (f := fun k => f (k + N)) (fun i j hij => hdisj (by omega)) (fun k => hf (k + N))]
        exact hN N le_rfl
      -- Choose `U_k` approximating `f k` with error `< δ / (4 * (N + 1) ^ 2)`
      have hchoose : ∀ k : ℕ, ∃ U : JointElem B T,
          ∫⁻ p, ENNReal.ofReal ((U.toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ <
            ENNReal.ofReal (δ / (4 * ((N : ℝ) + 1) ^ 2)) :=
        fun k => ihf k (δ / (4 * ((N : ℝ) + 1) ^ 2)) (by positivity)
      choose Us hUs using hchoose
      obtain ⟨W, hW⟩ := hsum_elem N Us
      refine ⟨W, ?_⟩
      -- Pointwise indicator decomposition for pairwise disjoint `f`
      have hsplit_ind : ∀ p : ℝ × Ω,
          (⋃ k, f k).indicator (fun _ => (1 : ℝ)) p =
            (∑ k ∈ Finset.range N, (f k).indicator (fun _ => (1 : ℝ)) p) +
            (⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ)) p := fun p => by
        by_cases hhead : ∃ k0 ∈ Finset.range N, p ∈ f k0
        · obtain ⟨k0, hk0, hpk0⟩ := hhead
          have hk0_lt : k0 < N := Finset.mem_range.mp hk0
          have hp_all : p ∈ ⋃ k, f k := Set.mem_iUnion.mpr ⟨k0, hpk0⟩
          have hp_ntail : p ∉ ⋃ k, f (k + N) := by
            intro h; obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp h
            exact Set.disjoint_left.mp (hdisj (show k + N ≠ k0 by omega)) hpk hpk0
          rw [Set.indicator_of_mem hp_all, Set.indicator_of_notMem hp_ntail, add_zero,
            Finset.sum_eq_single k0]
          · rw [Set.indicator_of_mem hpk0]
          · intro k _ hkne
            rw [Set.indicator_of_notMem (Set.disjoint_left.mp (hdisj hkne.symm) hpk0)]
          · intro h; exact absurd hk0 h
        · push Not at hhead
          have hsum0 : ∑ k ∈ Finset.range N, (f k).indicator (fun _ => (1 : ℝ)) p = 0 :=
            Finset.sum_eq_zero fun k hk =>
              Set.indicator_of_notMem (hhead k hk) (fun _ => (1 : ℝ))
          rw [hsum0, zero_add]
          by_cases hall : p ∈ ⋃ k, f k
          · obtain ⟨k1, hpk1⟩ := Set.mem_iUnion.mp hall
            have hge : N ≤ k1 := not_lt.mp fun hlt => hhead k1 (Finset.mem_range.mpr hlt) hpk1
            have hp_tail : p ∈ ⋃ k, f (k + N) := Set.mem_iUnion.mpr ⟨k1 - N, by rwa [Nat.sub_add_cancel hge]⟩
            rw [Set.indicator_of_mem hall, Set.indicator_of_mem hp_tail]
          · have hp_ntail : p ∉ ⋃ k, f (k + N) := fun h => by
              obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp h; exact hall (Set.mem_iUnion.mpr ⟨k + N, hpk⟩)
            rw [Set.indicator_of_notMem hall, Set.indicator_of_notMem hp_ntail]
      have hpt : ∀ p : ℝ × Ω,
          ENNReal.ofReal ((W.toFun p.1 p.2 - (⋃ k, f k).indicator (fun _ => (1 : ℝ)) p) ^ 2) ≤
            ENNReal.ofReal (2 * ((N : ℝ) + 1)) *
              (∑ k ∈ Finset.range N, ENNReal.ofReal (((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2)) +
            ENNReal.ofReal 2 * (⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ≥0∞)) p := fun p => by
        have hdiff : W.toFun p.1 p.2 - (⋃ k, f k).indicator (fun _ => (1 : ℝ)) p =
            (∑ k ∈ Finset.range N, ((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p)) -
            (⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ)) p := by
          rw [hW, hsplit_ind, Finset.sum_sub_distrib]; ring
        have hsq : (W.toFun p.1 p.2 - (⋃ k, f k).indicator (fun _ => (1 : ℝ)) p) ^ 2 ≤
            2 * ((N : ℝ) + 1) * (∑ k ∈ Finset.range N, ((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2) +
            2 * ((⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ)) p) ^ 2 := by
          rw [hdiff]
          have h2ab : ∀ x y : ℝ, (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
            nlinarith [sq_nonneg (x + y)]
          have hcs := hfin_cs N (fun k => (Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p)
          have hsum_nn : 0 ≤ ∑ k ∈ Finset.range N, ((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          have h1 := h2ab (∑ k ∈ Finset.range N, ((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p))
            ((⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ)) p)
          nlinarith
        refine (ENNReal.ofReal_le_ofReal hsq).trans ?_
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hind_sq : ENNReal.ofReal (((⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ)) p) ^ 2) =
            (⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ≥0∞)) p := by
          by_cases hp : p ∈ ⋃ k, f (k + N)
          · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; simp
          · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; simp
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hind_sq]
      have hterm_meas : ∀ k, Measurable (fun p : ℝ × Ω =>
          ENNReal.ofReal (((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2)) := fun k =>
        ENNReal.measurable_ofReal.comp
          (((Us k).measurable_pred.sub (measurable_const.indicator (hf k))).pow_const 2)
      have hhead_meas : Measurable (fun p : ℝ × Ω =>
          ENNReal.ofReal (2 * ((N : ℝ) + 1)) *
            ∑ k ∈ Finset.range N, ENNReal.ofReal (((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2)) :=
        measurable_const.mul (Finset.measurable_sum _ fun k _ => hterm_meas k)
      calc ∫⁻ p, ENNReal.ofReal ((W.toFun p.1 p.2 - (⋃ k, f k).indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ
          ≤ ∫⁻ p, (ENNReal.ofReal (2 * ((N : ℝ) + 1)) *
              (∑ k ∈ Finset.range N, ENNReal.ofReal (((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2)) +
              ENNReal.ofReal 2 * (⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ≥0∞)) p) ∂μ := lintegral_mono hpt
        _ = ENNReal.ofReal (2 * ((N : ℝ) + 1)) *
              (∑ k ∈ Finset.range N, ∫⁻ p, ENNReal.ofReal (((Us k).toFun p.1 p.2 - (f k).indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ) +
            ENNReal.ofReal 2 * μ (⋃ k, f (k + N)) := by
            rw [lintegral_add_left hhead_meas,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_finsetSum (s := Finset.range N) (fun k _ => hterm_meas k),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            have hμ_eq : ∫⁻ a, (⋃ k, f (k + N)).indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ =
                μ (⋃ k, f (k + N)) := by
              simpa [Pi.one_def] using
                lintegral_indicator_one (MeasurableSet.iUnion fun k => hf (k + N))
            rw [hμ_eq]
        _ ≤ ENNReal.ofReal (2 * ((N : ℝ) + 1)) *
              (∑ _k ∈ Finset.range N, ENNReal.ofReal (δ / (4 * ((N : ℝ) + 1) ^ 2))) +
            ENNReal.ofReal 2 * ENNReal.ofReal (δ / 8) :=
            add_le_add (mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => (hUs k).le))
              (mul_le_mul' le_rfl htail_le)
        _ = ENNReal.ofReal (2 * ((N : ℝ) + 1) * ((N : ℝ) * (δ / (4 * ((N : ℝ) + 1) ^ 2))) + 2 * (δ / 8)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ < ENNReal.ofReal δ := by
            refine (ENNReal.ofReal_lt_ofReal_iff hδ).mpr ?_
            have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
            have hfrac : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := (div_le_one hNpos).mpr (by linarith)
            have hsimp : 2 * ((N : ℝ) + 1) * ((N : ℝ) * (δ / (4 * ((N : ℝ) + 1) ^ 2))) =
                (δ / 2) * ((N : ℝ) / ((N : ℝ) + 1)) := by field_simp [hNpos.ne']; ring
            rw [hsimp]; nlinarith
  -- 3. Apply `MemLp.induction_dense` to `Z`!
  have hZ_aesm : AEStronglyMeasurable (Function.uncurry Z) μ :=
    hZp.stronglyMeasurable.aestronglyMeasurable
  have hZ_mem : MemLp (Function.uncurry Z) 2 μ := by
    change eLpNorm (Function.uncurry Z) 2 μ < ∞
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) hZ_aesm]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [hsq_enorm]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hZ_fin.ne
  let P_elem : (ℝ × Ω → ℝ) → Prop := fun g => ∃ U : JointElem B T, g = Function.uncurry U.toFun
  have h0P : ∀ (c : ℝ) ⦃S : Set (ℝ × Ω)⦄, MeasurableSet S → μ S < ⊤ →
      ∀ {δ : ℝ≥0∞}, δ ≠ 0 → ∃ g : ℝ × Ω → ℝ, eLpNorm (g - S.indicator fun _ => c) 2 μ ≤ δ ∧ P_elem g := by
    intro c S hS _ δ hδ
    rcases eq_or_ne δ ⊤ with rfl | hδ_top
    · exact ⟨Function.uncurry (JointElem.zero B T).toFun, le_top, JointElem.zero B T, rfl⟩
    · by_cases hc : c = 0
      · subst hc
        refine ⟨Function.uncurry (JointElem.zero B T).toFun, ?_, JointElem.zero B T, rfl⟩
        have h0 : Function.uncurry (JointElem.zero B T).toFun - S.indicator (fun _ => (0 : ℝ)) = 0 :=
          funext fun p => by simp [Function.uncurry, JointElem.toFun, JointElem.zero]
        rw [h0, eLpNorm_zero]; exact bot_le
      · have hδ_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ hδ_top
        have hc_pos : 0 < |c| := abs_pos.mpr hc
        obtain ⟨U, hU⟩ := hind_approx S hS ((δ.toReal / |c|) ^ 2) (by positivity)
        refine ⟨Function.uncurry (U.smul c).toFun, ?_, U.smul c, rfl⟩
        have haesm : AEStronglyMeasurable (Function.uncurry (U.smul c).toFun - S.indicator fun _ => c) μ :=
          ((U.smul c).measurable_pred.sub (measurable_const.indicator hS)).aestronglyMeasurable
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) haesm]
        simp only [ENNReal.toReal_ofNat]
        simp_rw [hsq_enorm]
        have hscale : ∀ p : ℝ × Ω,
            ENNReal.ofReal (((Function.uncurry (U.smul c).toFun - S.indicator fun _ => c) p) ^ 2) =
              ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2) := fun p => by
          rw [← ENNReal.ofReal_mul (sq_nonneg c)]
          congr 1
          have hUs : (U.smul c).toFun p.1 p.2 = c * U.toFun p.1 p.2 := by
            simp [JointElem.toFun, JointElem.smul, Finset.mul_sum, mul_ite, mul_zero]
            rfl
          simp only [Pi.sub_apply, Function.uncurry, hUs]
          by_cases hpS : p ∈ S <;> simp [hpS] <;> ring
        simp_rw [hscale]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hle : ENNReal.ofReal (c ^ 2) *
              ∫⁻ p, ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ ≤
            ENNReal.ofReal (δ.toReal ^ 2) := by
          refine (mul_le_mul' le_rfl hU.le).trans ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg c)]
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          rw [div_pow, sq_abs, mul_div_cancel₀ _ (pow_ne_zero 2 hc)]
        calc (ENNReal.ofReal (c ^ 2) *
                ∫⁻ p, ENNReal.ofReal ((U.toFun p.1 p.2 - S.indicator (fun _ => (1 : ℝ)) p) ^ 2) ∂μ) ^ (1 / (2 : ℝ))
            ≤ (ENNReal.ofReal (δ.toReal ^ 2)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hle (by positivity)
          _ = ENNReal.ofReal ((δ.toReal ^ 2) ^ (1 / (2 : ℝ))) :=
              ENNReal.ofReal_rpow_of_nonneg (sq_nonneg δ.toReal)
                (by positivity : (0 : ℝ) ≤ 1 / 2)
          _ = ENNReal.ofReal δ.toReal := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hδ_pos.le]
          _ = δ := ENNReal.ofReal_toReal hδ_top
  have h1P : ∀ f g, P_elem f → P_elem g → P_elem (f + g) := by
    rintro _ _ ⟨U₁, rfl⟩ ⟨U₂, rfl⟩
    exact ⟨U₁.add U₂, funext fun ⟨s, ω⟩ => (U₁.add_toFun U₂ s ω).symm⟩
  have hδ0 : ENNReal.ofReal (Real.sqrt (ε / 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (half_pos hε))).ne'
  obtain ⟨g, hg_le, ⟨U, rfl⟩⟩ :=
    MemLp.induction_dense (p := 2) (by norm_num) P_elem h0P h1P hZ_mem hδ0
  refine ⟨U, ?_⟩
  have haesm : AEStronglyMeasurable (Function.uncurry Z - Function.uncurry U.toFun) μ :=
    (hZp.sub U.measurable_pred).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num) haesm] at hg_le
  simp only [ENNReal.toReal_ofNat] at hg_le
  simp_rw [hsq_enorm] at hg_le
  have hpow := ENNReal.rpow_le_rpow hg_le (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at hpow
  have hsqrt : ENNReal.ofReal (Real.sqrt (ε / 2)) ^ (2 : ℝ) =
      ENNReal.ofReal ((Real.sqrt (ε / 2)) ^ (2 : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg (ε / 2)) (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsqrt, Real.rpow_two, Real.sq_sqrt (half_pos hε).le] at hpow
  exact hpow.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))

/-- **π-λ density**: `JointElem` is dense in `L²(predSigma (pathFiltration B).σAlg T, dtP P T)`. -/
lemma exists_jointElem_L2_approx {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → ℝ} (hZp : IsPredictableProcess (pathFiltration B).σAlg T Z)
    (hZL2 : MemLp (Function.uncurry Z) 2 (dtP P T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : JointElem B T, ∫ p, (Z p.1 p.2 - U.toFun p.1 p.2) ^ 2 ∂(dtP P T) < ε := by
  have hle_prod : predSigma (pathFiltration B).σAlg T ≤ Prod.instMeasurableSpace :=
    predSigma_le_prod (T := T) fun t _ => (pathFiltration B).le_ambient t
  have : IsFiniteMeasure (dtP P T) := isFiniteMeasure_dtP
  let μ : @Measure (ℝ × Ω) (predSigma (pathFiltration B).σAlg T) := (dtP P T).trim hle_prod
  have hμ_fin : @IsFiniteMeasure (ℝ × Ω) (predSigma (pathFiltration B).σAlg T) μ :=
    isFiniteMeasure_trim hle_prod
  have hμ_compl : μ (Ioc 0 T ×ˢ (Set.univ : Set Ω))ᶜ = 0 := by
    have hI : MeasurableSet[predSigma (pathFiltration B).σAlg T] (Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
      MeasurableSpace.measurableSet_generateFrom ⟨0, T, Set.univ, le_rfl, hT.le, le_rfl, MeasurableSet.univ, rfl⟩
    rw [trim_measurableSet_eq hle_prod hI.compl]
    have hcompl : (Ioc 0 T ×ˢ (Set.univ : Set Ω))ᶜ = (Ioc 0 T)ᶜ ×ˢ (Set.univ : Set Ω) := by ext ⟨s, ω⟩; simp
    rw [hcompl, dtP, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl]
    have hsing : (Ioc 0 T)ᶜ ∩ Icc 0 T = ({0} : Set ℝ) := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Ioc, Set.mem_Icc, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact le_antisymm (not_lt.mp fun hp => h1 ⟨hp, h3⟩) h2
      · rintro rfl; exact ⟨fun h => lt_irrefl 0 h.1, le_rfl, hT.le⟩
    rw [hsing, Real.volume_singleton, zero_mul]
  have hZ_fin : ∫⁻ p, ENNReal.ofReal (Z p.1 p.2 ^ 2) ∂μ < ⊤ := by
    have hZ_meas : @Measurable (ℝ × Ω) ℝ≥0∞ (predSigma (pathFiltration B).σAlg T) _
        (fun p => ENNReal.ofReal (Z p.1 p.2 ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hZp.pow_const 2)
    rw [lintegral_trim hle_prod hZ_meas]
    change (∫⁻ x, ENNReal.ofReal (Function.uncurry Z x ^ 2) ∂dtP P T) < ⊤
    rw [← ofReal_integral_eq_lintegral_ofReal hZL2.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  obtain ⟨U, hU_lt⟩ := exists_jointElem_L2_approx_on_trim B hT μ hμ_fin hμ_compl hZp hZ_fin hε
  refine ⟨U, ?_⟩
  have hdiff_meas : @Measurable (ℝ × Ω) ℝ≥0∞ (predSigma (pathFiltration B).σAlg T) _
      (fun p => ENNReal.ofReal ((Z p.1 p.2 - U.toFun p.1 p.2) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hZp.sub U.measurable_pred).pow_const 2)
  rw [lintegral_trim hle_prod hdiff_meas] at hU_lt
  change (∫⁻ x, ENNReal.ofReal ((Function.uncurry Z - Function.uncurry U.toFun) x ^ 2) ∂dtP P T) <
      ENNReal.ofReal ε at hU_lt
  rw [← ofReal_integral_eq_lintegral_ofReal (hZL2.sub U.memLp_dtP).integrable_sq
    (ae_of_all _ fun _ => sq_nonneg _)] at hU_lt
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hU_lt

/-- Elementary harmonic-tail bound `∑_{k=m}^n 1/k² ≤ 2 / m` for `1 ≤ m`. -/
private lemma sum_inv_sq_Ico_le {m n : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico m (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / (m : ℝ) := by
  by_cases hle : m ≤ n
  · rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hle), Nat.succ_eq_add_one]
    have hfirst : (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hrest : ∑ k ∈ Finset.Ico (m + 1) (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
      have hterm : ∀ k ∈ Finset.Ico (m + 1) (n + 1),
          (1 : ℝ) / (k : ℝ) ^ 2 ≤ (1 : ℝ) / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := fun k hk => by
        have hk2 : 2 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
        have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ k)
        have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        have hpos1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
        have hpos2 : (0 : ℝ) < (k : ℝ) := by positivity
        rw [hkm1, div_sub_div _ _ hpos1.ne' hpos2.ne', div_le_div_iff₀ (pow_pos hpos2 2) (mul_pos hpos1 hpos2)]
        nlinarith
      refine (Finset.sum_le_sum hterm).trans ?_
      have htel : ∑ k ∈ Finset.Ico (m + 1) (n + 1), ((1 : ℝ) / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
          1 / (m : ℝ) - 1 / (n : ℝ) := by
        have h := sum_Ico_sub (fun k : ℕ => -(1 : ℝ) / (k : ℝ)) hle
        have hshift : ∑ k ∈ Finset.Ico (m + 1) (n + 1), ((1 : ℝ) / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
            ∑ k ∈ Finset.Ico m n, (-(1 : ℝ) / ((k + 1 : ℕ) : ℝ) - -(1 : ℝ) / (k : ℝ)) := by
          refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
          · intro k hk
            have ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
            exact Finset.mem_Ico.mpr ⟨Nat.sub_le_sub_right h1 1, (Nat.sub_lt_sub_right (by omega) h2)⟩
          · intro k hk k' hk' h
            have ⟨h1, _⟩ := Finset.mem_Ico.mp hk
            have ⟨h1', _⟩ := Finset.mem_Ico.mp hk'
            omega
          · intro k hk
            have ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
            refine ⟨k + 1, Finset.mem_Ico.mpr ⟨Nat.add_le_add_right h1 1, Nat.add_lt_add_right h2 1⟩, ?_⟩
            simp
          · intro k hk
            have ⟨h1, _⟩ := Finset.mem_Ico.mp hk
            have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ k)
            have hcast' : ((k : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by linarith
            simp [hcast]
            ring
        rw [hshift, h]; ring
      rw [htel]
      have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
    calc
      (1 : ℝ) / (m : ℝ) ^ 2 + ∑ k ∈ Finset.Ico (m + 1) (n + 1), (1 : ℝ) / (k : ℝ) ^ 2
          ≤ (1 : ℝ) / (m : ℝ) + 1 / (m : ℝ) := add_le_add hfirst hrest
      _ = 2 / (m : ℝ) := by ring
  · rw [Finset.Ico_eq_empty (by omega)]; simp; positivity

/-- **The `u`-cancellation inequality**: for ANY measurable `h : ℝ → ℝ≥0∞` and every `n : ℕ`,
`∫₀ᵀ (∑_{k=1}^n h(k t / (n+1)) · t / (n+1)) dt ≤ 2 T ∫₀ᵀ h(u) du`. -/
lemma lintegral_riemann_sq_le {T : ℝ} (hT : 0 < T) {h : ℝ → ℝ≥0∞} (hh : Measurable h) (n : ℕ) :
    ∫⁻ t in Icc 0 T, (∑ k ∈ Finset.Ico 1 (n + 1),
        h ((k : ℝ) * t / ((n : ℝ) + 1)) * ENNReal.ofReal (t / ((n : ℝ) + 1))) ∂volume ≤
      ENNReal.ofReal (2 * T) * ∫⁻ u in Icc 0 T, h u ∂volume := by
  rw [lintegral_finsetSum (s := Finset.Ico 1 (n + 1))
    (f := fun k t => h ((k : ℝ) * t / ((n : ℝ) + 1)) * ENNReal.ofReal (t / ((n : ℝ) + 1)))
    (fun k _ => (hh.comp ((measurable_const.mul measurable_id).div_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const _)))]
  have hterm : ∀ k ∈ Finset.Ico 1 (n + 1),
      ∫⁻ t in Icc 0 T, h ((k : ℝ) * t / ((n : ℝ) + 1)) * ENNReal.ofReal (t / ((n : ℝ) + 1)) ∂volume =
      ∫⁻ u in Icc 0 T, {u | u ≤ (k : ℝ) * T / ((n : ℝ) + 1)}.indicator
        (fun u => h u * ENNReal.ofReal (((n : ℝ) + 1) * u / (k : ℝ) ^ 2)) u ∂volume := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
    set c : ℝ := (k : ℝ) / ((n : ℝ) + 1)
    have hc : 0 < c := by positivity
    have hc_le : c ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.le_succ_of_le hkn)
    have hsub : ∫⁻ t in Icc 0 T, h (c * t) * ENNReal.ofReal (t / ((n : ℝ) + 1)) ∂volume =
        ENNReal.ofReal c⁻¹ * ∫⁻ u in Icc 0 (c * T), h u * ENNReal.ofReal (u / (k : ℝ)) ∂volume := by
      have hmap : Measure.map (fun t : ℝ => c * t) volume = ENNReal.ofReal c⁻¹ • volume := by
        refine Measure.ext fun s hs => ?_
        rw [Measure.map_apply (measurable_const_mul c) hs, Measure.smul_apply, smul_eq_mul,
          Real.volume_preimage_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc)]
      have h1 := lintegral_map (μ := volume) (f := fun u : ℝ =>
        (Icc 0 (c * T)).indicator (fun u => h u * ENNReal.ofReal (u / (k : ℝ))) u)
        ((hh.mul (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))).indicator measurableSet_Icc)
        (measurable_const_mul c)
      rw [hmap, lintegral_smul_measure, smul_eq_mul, lintegral_indicator measurableSet_Icc] at h1
      rw [← lintegral_indicator measurableSet_Icc, h1]
      refine lintegral_congr fun t => ?_
      have hiff : c * t ∈ Icc 0 (c * T) ↔ t ∈ Icc 0 T := by
        simp only [Set.mem_Icc]; constructor
        · rintro ⟨h1, h2⟩; exact ⟨nonneg_of_mul_nonneg_right h1 hc, le_of_mul_le_mul_left h2 hc⟩
        · rintro ⟨h1, h2⟩; exact ⟨mul_nonneg hc.le h1, mul_le_mul_of_nonneg_left h2 hc.le⟩
      by_cases ht : t ∈ Icc 0 T
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hiff.mpr ht)]
        have heq : c * t / (k : ℝ) = t / ((n : ℝ) + 1) := by
          simp only [c]; have hk0 : (k : ℝ) ≠ 0 := by positivity
          field_simp [hk0]
        rw [heq]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun h => ht (hiff.mp h))]
    have hmul_eq : ∀ t, (k : ℝ) * t / ((n : ℝ) + 1) = c * t := fun t => by simp only [c]; ring
    simp_rw [hmul_eq]; rw [hsub, ← lintegral_const_mul' (ENNReal.ofReal c⁻¹)
      (fun u => h u * ENNReal.ofReal (u / (k : ℝ))) ENNReal.ofReal_ne_top]
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Icc 0 T
    · rw [Set.indicator_of_mem hu]
      by_cases huc : u ≤ c * T
      · have hu_cT : u ∈ Icc 0 (c * T) := ⟨hu.1, huc⟩
        have huc' : u ∈ {u : ℝ | u ≤ (k : ℝ) * T / ((n : ℝ) + 1)} := by
          simpa only [Set.mem_ofPred_eq, c, mul_div_right_comm] using huc
        rw [Set.indicator_of_mem hu_cT,
          Set.indicator_of_mem (show u ∈ {u : ℝ | u ≤ c * T} from huc)]
        rw [mul_left_comm, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
        simp only [c]
        field_simp
      · have hu_ncT : u ∉ Icc 0 (c * T) := fun h => huc h.2
        have huc' : u ∉ {u : ℝ | u ≤ (k : ℝ) * T / ((n : ℝ) + 1)} := by
          simpa only [Set.mem_ofPred_eq, c, mul_div_right_comm] using huc
        rw [Set.indicator_of_notMem hu_ncT,
          Set.indicator_of_notMem (show u ∉ {u : ℝ | u ≤ c * T} from huc)]
    · have hnot : u ∉ Icc 0 (c * T) := fun h => hu ⟨h.1, h.2.trans (mul_le_of_le_one_left hT.le hc_le)⟩
      rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hnot]
  rw [Finset.sum_congr rfl hterm, ← lintegral_finsetSum (s := Finset.Ico 1 (n + 1))
    (f := fun k u => {u | u ≤ (k : ℝ) * T / ((n : ℝ) + 1)}.indicator
      (fun u => h u * ENNReal.ofReal (((n : ℝ) + 1) * u / (k : ℝ) ^ 2)) u)
    (fun k _ => (hh.mul (ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_id).div_const _))).indicator
      (measurableSet_le measurable_id measurable_const))]
  rw [← lintegral_const_mul' (ENNReal.ofReal (2 * T)) h ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc fun u hu => ?_)
  have hu0 : 0 ≤ u := hu.1
  have hsum_le : (∑ k ∈ Finset.Ico 1 (n + 1), {u : ℝ | u ≤ (k : ℝ) * T / ((n : ℝ) + 1)}.indicator
      (fun u => h u * ENNReal.ofReal (((n : ℝ) + 1) * u / (k : ℝ) ^ 2)) u) ≤
      h u * ENNReal.ofReal (2 * T) := by
    have hfac : ∀ k ∈ Finset.Ico 1 (n + 1),
        {u : ℝ | u ≤ (k : ℝ) * T / ((n : ℝ) + 1)}.indicator
          (fun u => h u * ENNReal.ofReal (((n : ℝ) + 1) * u / (k : ℝ) ^ 2)) u =
        h u * ENNReal.ofReal (if u ≤ (k : ℝ) * T / ((n : ℝ) + 1) then ((n : ℝ) + 1) * u / (k : ℝ) ^ 2 else 0) :=
      fun k _ => by by_cases h' : u ≤ (k : ℝ) * T / ((n : ℝ) + 1) <;> simp [Set.indicator, h']
    rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum,
      ← ENNReal.ofReal_sum_of_nonneg (fun k _ => by split_ifs <;> positivity)]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    rcases hu0.eq_or_lt with rfl | hu_pos
    · simp; positivity
    · set m : ℕ := ⌈((n : ℝ) + 1) * u / T⌉₊
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h0 =>
        not_le.mpr (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * u / T) (Nat.ceil_eq_zero.mp h0)
      have hfilt : ∑ k ∈ Finset.Ico 1 (n + 1),
            (if u ≤ (k : ℝ) * T / ((n : ℝ) + 1) then ((n : ℝ) + 1) * u / (k : ℝ) ^ 2 else 0) ≤
          (((n : ℝ) + 1) * u) * ∑ k ∈ Finset.Ico m (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        have hsub : Finset.Ico m (n + 1) ⊆ Finset.Ico 1 (n + 1) := Finset.Ico_subset_Ico_left hm1
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_le_sum fun k _ => ?_
          split_ifs
          · ring_nf; exact le_rfl
          · positivity
        · intro k hk hnot
          have hk_lt : k < m := by simp only [Finset.mem_Ico] at hk hnot; omega
          have hnot_le : ¬ u ≤ (k : ℝ) * T / ((n : ℝ) + 1) := by
            intro hle
            have h1 : ((n : ℝ) + 1) * u / T ≤ (k : ℝ) := by
              rw [div_le_iff₀ hT]; linarith [(le_div_iff₀ (by positivity)).mp hle]
            exact not_le.mpr hk_lt (Nat.ceil_le.mpr h1)
          simp [hnot_le]
      refine hfilt.trans ?_
      have hceil : ((n : ℝ) + 1) * u / T ≤ (m : ℝ) := Nat.le_ceil _
      calc (((n : ℝ) + 1) * u) * ∑ k ∈ Finset.Ico m (n + 1), (1 : ℝ) / (k : ℝ) ^ 2
          ≤ (((n : ℝ) + 1) * u) * (2 / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_Ico_le hm1) (by positivity)
        _ ≤ (((n : ℝ) + 1) * u) * (2 / (((n : ℝ) + 1) * u / T)) := by gcongr
        _ = 2 * T := by field_simp [hu_pos.ne']
  simpa [mul_comm] using hsum_le

/-- Left-point Riemann sum omitting the `k = 0` term (`k = 1, …, n`). -/
def itoRiemannPrime {d : ℕ} (B : MultiBrownian Ω P d) (hd : 0 < d)
    (K : ℝ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Ico 1 (n + 1),
    K ((k : ℝ) * t / ((n : ℝ) + 1)) ω *
      (MultiBrownian.W B (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω (kitDriver hd) -
       MultiBrownian.W B ((k : ℝ) * t / ((n : ℝ) + 1)) ω (kitDriver hd))

/-- Explicit quantitative `L²` bound on `itoRiemannPrime` for a `JointElem`. -/
lemma integral_itoRiemannPrime_jointElem_sub_sq_le {d : ℕ} {B : MultiBrownian Ω P d}
    (hd : 0 < d) {T : ℝ} (hT : 0 < T) (U : JointElem B T)
    (C : ℝ) (hC : ∀ j ω, |U.h j ω| ≤ C) (hC0 : 0 ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (n : ℕ) :
    ∫ ω, (itoRiemannPrime B hd U.toFun t n ω - U.ito hd t ω) ^ 2 ∂P ≤
      (4 * ((U.n : ℝ) * C) ^ 2 * ((2 * U.n + 1 : ℕ) : ℝ) * t) / ((n : ℝ) + 1) := by
  let Un : JointElem B T :=
    { n := n
      a := fun k => ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)
      b := fun k => ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)
      h := fun k ω => U.toFun (((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω
      hab := fun k => ⟨by positivity,
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by push_cast; linarith) ht0) (by positivity),
        by rw [div_le_iff₀ (by positivity)]
           have hk : ((k.1 + 2 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
             exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ k.isLt)
           nlinarith⟩
      h_meas := fun k => measurable_slice_of_predSigma
        (fun s r _ hsr _ => (pathFiltration B).mono hsr) U.measurable_pred
        (s := ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) (by positivity) (by
          rw [div_le_iff₀ (by positivity)]
          have hk : ((k.1 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
            exact_mod_cast (Nat.succ_le_succ k.isLt.le)
          nlinarith)
      h_bdd := fun k => ⟨(U.n : ℝ) * C, fun ω => by
        refine (Finset.abs_sum_le_sum_abs
          (f := fun j : Fin U.n => if U.a j < ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ∧
            ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ≤ U.b j then U.h j ω else 0) Finset.univ).trans ?_
        calc _ ≤ ∑ _j : Fin U.n, C := Finset.sum_le_sum fun j _ => by split_ifs; exact hC j ω; rw [abs_zero]; exact hC0
          _ = (U.n : ℝ) * C := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]⟩ }
  have hUn_ito : ∀ ω, Un.ito hd t ω = itoRiemannPrime B hd U.toFun t n ω := fun ω => by
    unfold JointElem.ito itoRiemannPrime
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    let f : ℕ → ℝ := fun k =>
      U.toFun (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω *
        (MultiBrownian.W B (min (((k + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) t) ω (kitDriver hd) -
         MultiBrownian.W B (min (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) t) ω (kitDriver hd))
    change (∑ k : Fin n, f k.1) = _
    rw [Fin.sum_univ_eq_sum_range f n]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have h1 : ((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      have : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ hk'.le)
      nlinarith
    have h2 : ((k + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      have : ((k + 2 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ hk')
      nlinarith
    simp only [f, min_eq_left h1, min_eq_left h2, add_comm 1 k, show k + 1 + 1 = k + 2 by omega]
  have hdiff_ito : ∀ ω, itoRiemannPrime B hd U.toFun t n ω - U.ito hd t ω = (Un.add U.neg).ito hd t ω := fun ω => by
    rw [JointElem.add_ito, JointElem.neg_ito, hUn_ito]; ring
  simp_rw [hdiff_ito, integral_jointElem_ito_sq hd hT (Un.add U.neg) ht0 htT]
  set M : ℝ := (U.n : ℝ) * C
  have hM0 : 0 ≤ M := by positivity
  set Δ : ℝ := t / ((n : ℝ) + 1)
  let bad : Set ℝ := Icc 0 Δ ∪ (⋃ j : Fin U.n, Icc (U.a j) (U.a j + Δ)) ∪ (⋃ j : Fin U.n, Icc (U.b j) (U.b j + Δ))
  have hbad_meas : MeasurableSet bad :=
    (measurableSet_Icc.union (MeasurableSet.iUnion fun _ => measurableSet_Icc)).union
      (MeasurableSet.iUnion fun _ => measurableSet_Icc)
  have hbad_vol : volume bad ≤ ENNReal.ofReal (((2 * U.n + 1 : ℕ) : ℝ) * Δ) := by
    have h1 : volume (Icc 0 Δ) = ENNReal.ofReal Δ := by rw [Real.volume_Icc, sub_zero]
    have h2 : ∀ x : ℝ, volume (Icc x (x + Δ)) = ENNReal.ofReal Δ := fun x => by
      rw [Real.volume_Icc, add_sub_cancel_left]
    calc volume bad ≤ volume (Icc 0 Δ) + (∑ j : Fin U.n, volume (Icc (U.a j) (U.a j + Δ))) +
          (∑ j : Fin U.n, volume (Icc (U.b j) (U.b j + Δ))) :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add le_rfl (measure_iUnion_fintype_le volume fun j : Fin U.n => Icc (U.a j) (U.a j + Δ))))
            (measure_iUnion_fintype_le volume fun j : Fin U.n => Icc (U.b j) (U.b j + Δ)))
      _ = ENNReal.ofReal (((2 * U.n + 1 : ℕ) : ℝ) * Δ) := by
          simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; push_cast; ring
  have hdiff_zero : ∀ s ∈ Icc 0 t, s ∉ bad → ∀ ω, (Un.add U.neg).toFun s ω = 0 := by
    intro s hs hnb ω
    rw [JointElem.add_toFun, JointElem.neg_toFun, add_neg_eq_zero]
    have hs_gt : Δ < s := by
      by_contra hle; push Not at hle
      exact hnb (Set.mem_union_left _ (Set.mem_union_left _ ⟨hs.1, hle⟩))
    have ht_pos : 0 < t := by
      by_contra h0; have : t = 0 := le_antisymm (not_lt.mp h0) ht0; subst this
      simp [Δ] at hs_gt; linarith [hs.2]
    have hΔ_pos : 0 < Δ := div_pos ht_pos (by positivity)
    set r : ℕ := ⌈s / Δ⌉₊
    have hr2 : 2 ≤ r := by
      have h1 : ((1 : ℕ) : ℝ) < s / Δ := by simpa using (one_lt_div hΔ_pos).mpr hs_gt
      have hlt : 1 < ⌈s / Δ⌉₊ := Nat.lt_ceil.mpr h1
      omega
    have hr_le : r ≤ n + 1 := Nat.ceil_le.mpr <| by
      rw [div_le_iff₀ hΔ_pos]
      have hmul : ((n + 1 : ℕ) : ℝ) * Δ = t := by simp only [Δ]; push_cast; field_simp
      rw [hmul]; exact hs.2
    let k0 : Fin n := ⟨r - 2, by omega⟩
    have hk0_1 : ((k0.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < s := by
      have hidx : k0.1 + 1 = r - 1 := by simp only [k0]; omega
      have hlt : ((r - 1 : ℕ) : ℝ) < s / Δ := Nat.lt_ceil.mp (show r - 1 < ⌈s / Δ⌉₊ by omega)
      have hmul := (lt_div_iff₀ hΔ_pos).mp hlt
      rw [hidx]; simpa only [Δ, mul_div_assoc] using hmul
    have hk0_2 : s ≤ ((k0.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1) := by
      have hidx : k0.1 + 2 = r := by simp only [k0]; omega
      have hle : s ≤ (r : ℝ) * Δ := (div_le_iff₀ hΔ_pos).mp (Nat.le_ceil (s / Δ))
      rw [hidx]; simpa only [Δ, mul_div_assoc] using hle
    have hUn_val : Un.toFun s ω = U.toFun (((k0.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω := by
      change (∑ k : Fin n, if ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < s ∧
          s ≤ ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)
          then U.toFun (((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω else 0) = _
      rw [Finset.sum_eq_single k0]
      · simp only [hk0_1, hk0_2, and_self, ↓reduceIte]
      · intro k _ hne
        have hnc : ¬ (((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < s ∧ s ≤ ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) := by
          rintro ⟨h1, h2⟩; rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
          · have hcast : ((k.1 + 2 : ℕ) : ℝ) ≤ ((k0.1 + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ hlt)
            have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcast ht0) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
            linarith
          · have hcast : ((k0.1 + 2 : ℕ) : ℝ) ≤ ((k.1 + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ hgt)
            have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcast ht0) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
            linarith
        simp only [hnc, ↓reduceIte]
      · intro h; exact absurd (Finset.mem_univ k0) h
    rw [hUn_val]; unfold JointElem.toFun
    refine Finset.sum_congr rfl fun j _ => ?_
    set s' := ((k0.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)
    have hss' : s - s' ≤ Δ := by
      have : ((k0.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1) - s' = Δ := by simp only [s', Δ]; push_cast; ring
      linarith
    have hna : ¬ (U.a j ≤ s ∧ s ≤ U.a j + Δ) := fun h =>
      hnb (Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, h⟩)))
    have hnb' : ¬ (U.b j ≤ s ∧ s ≤ U.b j + Δ) := fun h =>
      hnb (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, h⟩))
    have hiff : (U.a j < s' ∧ s' ≤ U.b j) ↔ (U.a j < s ∧ s ≤ U.b j) := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1.trans hk0_1, ?_⟩
        by_contra hgt; push Not at hgt; exact hnb' ⟨hgt.le, by linarith⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, hk0_1.le.trans h2⟩
        by_contra hle; push Not at hle; exact hna ⟨h1.le, by linarith⟩
    by_cases h : U.a j < s ∧ s ≤ U.b j <;> simp [hiff, h]
  have hpt_bd : ∀ p : ℝ × Ω, p ∈ Icc 0 t ×ˢ (Set.univ : Set Ω) →
      (Un.add U.neg).toFun p.1 p.2 ^ 2 ≤ (bad ×ˢ (Set.univ : Set Ω)).indicator (fun _ => 4 * M ^ 2) p := by
    intro p hp
    by_cases hpb : p.1 ∈ bad
    · have hp_mem : p ∈ bad ×ˢ (Set.univ : Set Ω) := ⟨hpb, trivial⟩
      rw [Set.indicator_of_mem hp_mem]
      have hU_le : ∀ s ω, |U.toFun s ω| ≤ M := fun s ω =>
        (Finset.abs_sum_le_sum_abs
          (f := fun j : Fin U.n => if U.a j < s ∧ s ≤ U.b j then U.h j ω else 0) Finset.univ).trans
          (by calc _ ≤ ∑ _j : Fin U.n, C := Finset.sum_le_sum fun j _ => by split_ifs; exact hC j ω; rw [abs_zero]; exact hC0
            _ = M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
      have hUn_le : |Un.toFun p.1 p.2| ≤ M := by
        by_cases hex : ∃ k : Fin n, ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < p.1 ∧
            p.1 ≤ ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)
        · obtain ⟨k0, h1, h2⟩ := hex
          have hval : Un.toFun p.1 p.2 = U.toFun (((k0.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) p.2 := by
            change (∑ k : Fin n, if ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < p.1 ∧
                p.1 ≤ ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)
                then U.toFun (((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) p.2 else 0) = _
            rw [Finset.sum_eq_single k0]
            · simp only [h1, h2, and_self, ↓reduceIte]
            · intro k _ hne
              have hnc : ¬ (((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < p.1 ∧ p.1 ≤ ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) := by
                rintro ⟨h3, h4⟩; rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
                · have hcast : ((k.1 + 2 : ℕ) : ℝ) ≤ ((k0.1 + 1 : ℕ) : ℝ) := by
                    exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ hlt)
                  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcast ht0) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1); linarith
                · have hcast : ((k0.1 + 2 : ℕ) : ℝ) ≤ ((k.1 + 1 : ℕ) : ℝ) := by
                    exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ hgt)
                  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcast ht0) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1); linarith
              simp only [hnc, ↓reduceIte]
            · intro h; exact absurd (Finset.mem_univ k0) h
          rw [hval]; exact hU_le _ _
        · push Not at hex
          have h0 : Un.toFun p.1 p.2 = 0 := Finset.sum_eq_zero fun k _ => by
            by_cases h1 : ((k.1 + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1) < p.1
            · have h2 : ¬ p.1 ≤ ((k.1 + 2 : ℕ) : ℝ) * t / ((n : ℝ) + 1) := not_le.mpr (hex k h1)
              simp only [Un, h1, h2, and_false, ↓reduceIte]
            · simp only [Un, h1, false_and, ↓reduceIte]
          rw [h0, abs_zero]; exact hM0
      have hsum_abs : |(Un.add U.neg).toFun p.1 p.2| ≤ 2 * M := by
        rw [JointElem.add_toFun, JointElem.neg_toFun]
        calc |Un.toFun p.1 p.2 + -U.toFun p.1 p.2|
              ≤ |Un.toFun p.1 p.2| + |-U.toFun p.1 p.2| :=
                abs_add_le (Un.toFun p.1 p.2) (-U.toFun p.1 p.2)
          _ = |Un.toFun p.1 p.2| + |U.toFun p.1 p.2| := by rw [abs_neg]
          _ ≤ 2 * M := by linarith [hU_le p.1 p.2]
      rw [← sq_abs]
      calc _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hsum_abs 2
        _ = 4 * M ^ 2 := by ring
    · have hp_nmem : p ∉ bad ×ˢ (Set.univ : Set Ω) := fun h => hpb h.1
      rw [hdiff_zero p.1 hp.1 hpb p.2, zero_pow two_ne_zero, Set.indicator_of_notMem hp_nmem]
  have : IsFiniteMeasure (dtP P T) := isFiniteMeasure_dtP
  have hi_ind : Integrable ((bad ×ˢ (Set.univ : Set Ω)).indicator (fun _ => 4 * M ^ 2)) (dtP P T) :=
    (integrable_const _).indicator (hbad_meas.prod MeasurableSet.univ)
  calc ∫ p in Icc 0 t ×ˢ (Set.univ : Set Ω), (Un.add U.neg).toFun p.1 p.2 ^ 2 ∂(dtP P T)
      ≤ ∫ p in Icc 0 t ×ˢ (Set.univ : Set Ω), (bad ×ˢ (Set.univ : Set Ω)).indicator (fun _ => 4 * M ^ 2) p ∂(dtP P T) :=
        setIntegral_mono_on (Un.add U.neg).memLp_dtP.integrable_sq.integrableOn
          hi_ind.integrableOn (measurableSet_Icc.prod MeasurableSet.univ) hpt_bd
    _ ≤ ∫ p, (bad ×ˢ (Set.univ : Set Ω)).indicator (fun _ => 4 * M ^ 2) p ∂(dtP P T) :=
        setIntegral_le_integral hi_ind (ae_of_all _ fun p => by by_cases h : p ∈ bad ×ˢ Set.univ <;> simp [h]; positivity)
    _ = (4 * M ^ 2) * (dtP P T (bad ×ˢ Set.univ)).toReal := by
        rw [integral_indicator_const _ (hbad_meas.prod MeasurableSet.univ), smul_eq_mul, Measure.real_def, mul_comm]
    _ ≤ (4 * M ^ 2) * (((2 * U.n + 1 : ℕ) : ℝ) * Δ) := by
        have hvol_dtP : dtP P T (bad ×ˢ Set.univ) ≤ ENNReal.ofReal (((2 * U.n + 1 : ℕ) : ℝ) * Δ) := by
          rw [dtP, Measure.prod_prod, measure_univ, mul_one, Measure.restrict_apply hbad_meas]
          exact (measure_mono Set.inter_subset_left).trans hbad_vol
        have htoR : (dtP P T (bad ×ˢ Set.univ)).toReal ≤ ((2 * U.n + 1 : ℕ) : ℝ) * Δ := by
          rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2 * U.n + 1 : ℕ) : ℝ) * Δ)]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_dtP
        exact mul_le_mul_of_nonneg_left htoR (by positivity)
    _ = (4 * M ^ 2 * ((2 * U.n + 1 : ℕ) : ℝ) * t) / ((n : ℝ) + 1) := by simp only [Δ]; ring

/-- On any `JointElem`, `itoRiemannPrime` converges to `U.ito` in `L²(P)` for every `t ∈ [0, T]`. -/
lemma tendsto_itoRiemannPrime_jointElem {d : ℕ} {B : MultiBrownian Ω P d} (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    (U : JointElem B T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Tendsto (fun n : ℕ => ∫ ω, (itoRiemannPrime B hd U.toFun t n ω - U.ito hd t ω) ^ 2 ∂P) atTop (𝓝 0) := by
  choose Cj hCj using U.h_bdd
  set C : ℝ := ∑ j : Fin U.n, max (Cj j) 0
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hC : ∀ j ω, |U.h j ω| ≤ C := fun j ω =>
    ((hCj j ω).trans (le_max_left _ _)).trans
      (Finset.single_le_sum (fun i _ => le_max_right (Cj i) 0) (Finset.mem_univ j))
  refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun n => integral_itoRiemannPrime_jointElem_sub_sq_le hd hT U C hC hC0 ht0 htT n) ?_
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

end SignatureVolatility

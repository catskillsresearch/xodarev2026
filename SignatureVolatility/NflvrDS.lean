/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import SignatureVolatility.NflvrL2Ito

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace SignatureVolatility

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## Section 1: Raw-Filtration Left-Continuous Quadratic Variation & Localization -/

/-- Cumulative quadratic variation `Q K s ω = ∫⁻ u in Icc 0 s, ofReal (K u ω ^ 2) du ∈ [0, ∞]`. -/
def localizedQuad (K : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 s, ENNReal.ofReal (K u ω ^ 2) ∂volume

omit m₀ in
lemma localizedQuad_mono (K : ℝ → Ω → ℝ) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    localizedQuad K s ω ≤ localizedQuad K t ω :=
  lintegral_mono_set (Icc_subset_Icc_right hst)

omit m₀ in
lemma localizedQuad_zero (K : ℝ → Ω → ℝ) (ω : Ω) : localizedQuad K 0 ω = 0 := by
  simp [localizedQuad, Set.Icc_self]

/-- For ANY `predSigma`-measurable `K` and any `s ∈ [0, T]`, `localizedQuad K s` is measurable
for the **raw** filtration `(pathFiltration B).σAlg s`. -/
lemma measurable_localizedQuad {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ}
    {K : ℝ → Ω → ℝ} (hKp : IsPredictableProcess (pathFiltration B).σAlg T K)
    {s : ℝ} (_hs0 : 0 ≤ s) (_hsT : s ≤ T) :
    Measurable[(pathFiltration B).σAlg s] (localizedQuad K s) := by
  -- `(u, ω) ↦ (min u s, ω)` is measurable from `ℬ(ℝ) ⊗ ℱ_s` to `predSigma ℱ T`.
  -- Do not `letI` a new `MeasurableSpace Ω`: the named instance `m₀` would clash.
  have hmin : @Measurable (ℝ × Ω) (ℝ × Ω)
      (@Prod.instMeasurableSpace ℝ Ω inferInstance ((pathFiltration B).σAlg s))
      (predSigma (pathFiltration B).σAlg T) (fun p => (min p.1 s, p.2)) := by
    refine @measurable_generateFrom (ℝ × Ω) (ℝ × Ω)
        (@Prod.instMeasurableSpace ℝ Ω inferInstance ((pathFiltration B).σAlg s))
        {S | ∃ (a b : ℝ) (A : Set Ω), 0 ≤ a ∧ a ≤ b ∧ b ≤ T ∧
          MeasurableSet[(pathFiltration B).σAlg a] A ∧ S = Ioc a b ×ˢ A}
        (fun p => (min p.1 s, p.2)) ?_
    rintro _ ⟨a, b, A, _, _, _, hA, rfl⟩
    by_cases has : a < s
    · have heq : (fun p : ℝ × Ω => (min p.1 s, p.2)) ⁻¹' (Ioc a b ×ˢ A) =
          {u : ℝ | a < min u s ∧ min u s ≤ b} ×ˢ A := by ext ⟨u, ω⟩; simp
      rw [heq]
      exact @MeasurableSet.prod ℝ Ω inferInstance ((pathFiltration B).σAlg s) _ _
        ((measurableSet_lt measurable_const (measurable_id.min measurable_const)).inter
          (measurableSet_le (measurable_id.min measurable_const) measurable_const))
        ((pathFiltration B).mono has.le A hA)
    · have heq : (fun p : ℝ × Ω => (min p.1 s, p.2)) ⁻¹' (Ioc a b ×ˢ A) = ∅ := by
        ext ⟨u, ω⟩
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, _⟩, _⟩
        exact not_lt.mpr ((min_le_right u s).trans (le_of_not_gt has)) h1
      rw [heq]
      exact @MeasurableSet.empty (ℝ × Ω)
        (@Prod.instMeasurableSpace ℝ Ω inferInstance ((pathFiltration B).σAlg s))
  have hcomp : @Measurable (ℝ × Ω) ℝ≥0∞
      (@Prod.instMeasurableSpace ℝ Ω inferInstance ((pathFiltration B).σAlg s))
      inferInstance
      (fun p => ENNReal.ofReal (K (min p.1 s) p.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hKp.comp hmin).pow_const 2)
  have hrect : @MeasurableSet (ℝ × Ω)
      (@Prod.instMeasurableSpace ℝ Ω inferInstance ((pathFiltration B).σAlg s))
      (Icc 0 s ×ˢ (Set.univ : Set Ω)) :=
    MeasurableSet.prod measurableSet_Icc MeasurableSet.univ
  have hind : @Measurable (ℝ × Ω) ℝ≥0∞
      (@Prod.instMeasurableSpace ℝ Ω inferInstance ((pathFiltration B).σAlg s))
      inferInstance
      (fun p => (Icc 0 s ×ˢ (Set.univ : Set Ω)).indicator
        (fun q => ENNReal.ofReal (K (min q.1 s) q.2 ^ 2)) p) :=
    hcomp.indicator hrect
  have hinter : @Measurable Ω ℝ≥0∞ ((pathFiltration B).σAlg s) inferInstance
      (fun ω => ∫⁻ u, (Icc 0 s ×ˢ (Set.univ : Set Ω)).indicator
        (fun q => ENNReal.ofReal (K (min q.1 s) q.2 ^ 2)) (u, ω) ∂volume) :=
    @Measurable.lintegral_prod_left' ℝ Ω inferInstance ((pathFiltration B).σAlg s)
      volume _ _ hind
  have hrew : localizedQuad K s = fun ω =>
      ∫⁻ u, (Icc 0 s ×ˢ (Set.univ : Set Ω)).indicator
        (fun q => ENNReal.ofReal (K (min q.1 s) q.2 ^ 2)) (u, ω) ∂volume := by
    funext ω
    unfold localizedQuad
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ Icc 0 s
    · rw [Set.indicator_of_mem hu,
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨hu, Set.mem_univ _⟩), min_eq_left hu.2]
    · rw [Set.indicator_of_notMem hu,
        Set.indicator_of_notMem (fun h => hu (Set.mem_prod.mp h).1)]
  rw [hrew]
  exact hinter

omit m₀ in
/-- Left-continuity of `s ↦ localizedQuad K s ω` for EVERY `ω` and EVERY `s ∈ Ioc 0 T`. -/
lemma localizedQuad_le_iff_rat {K : ℝ → Ω → ℝ} {T : ℝ} {s : ℝ} (hs : s ∈ Ioc 0 T) (ω : Ω) (m : ℝ≥0∞)
    (hK : Measurable (fun u => K u ω)) :
    localizedQuad K s ω ≤ m ↔ ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < s → localizedQuad K (q : ℝ) ω ≤ m := by
  constructor
  · intro h q _ hqs; exact (localizedQuad_mono K hqs.le ω).trans h
  · intro hall
    -- Pick rationals `q_r ∈ [0, s)` with `q_r ↑ s`
    have hex : ∀ r : ℕ, ∃ q : ℚ, max 0 (s - 1 / ((r : ℝ) + 1)) < (q : ℝ) ∧ (q : ℝ) < s := fun r =>
      exists_rat_btwn (max_lt hs.1 (sub_lt_self s (by positivity)))
    choose q hq1 hq2 using hex
    let qr : ℕ → ℚ := fun r => Nat.rec (q 0) (fun k prev => max prev (q (k + 1))) r
    have hqr_mono : Monotone qr := monotone_nat_of_le_succ fun k => le_max_left _ _
    have hqr_nn : ∀ r : ℕ, (0 : ℝ) ≤ Rat.cast (qr r) := by
      intro r
      induction r with
      | zero =>
          have hlt : (0 : ℝ) < Rat.cast (q 0) :=
            (le_max_left (0 : ℝ) (s - 1 / (((0 : ℕ) : ℝ) + 1))).trans_lt (hq1 0)
          simpa [show qr 0 = q 0 from rfl] using hlt.le
      | succ k ih =>
          have hmono : qr k ≤ qr (k + 1) := hqr_mono (Nat.le_succ k)
          exact ih.trans (Rat.cast_le.mpr hmono)
    have hqr_lt : ∀ r : ℕ, Rat.cast (qr r) < s := by
      intro r
      induction r with
      | zero => simpa [show qr 0 = q 0 from rfl] using hq2 0
      | succ k ih =>
          have hcast : Rat.cast (qr (k + 1)) = max (Rat.cast (qr k)) (Rat.cast (q (k + 1))) :=
            (Rat.cast_max (qr k) (q (k + 1)) : ((max (qr k) (q (k + 1)) : ℚ) : ℝ) = _)
          rw [hcast]; exact max_lt ih (hq2 (k + 1))
    have hqr_ge : ∀ r : ℕ, s - 1 / ((r : ℝ) + 1) < Rat.cast (qr r) := by
      intro r
      cases r with
      | zero =>
          have : s - 1 / (((0 : ℕ) : ℝ) + 1) < Rat.cast (q 0) :=
            (le_max_right (0 : ℝ) (s - 1 / (((0 : ℕ) : ℝ) + 1))).trans_lt (hq1 0)
          simpa [show qr 0 = q 0 from rfl] using this
      | succ k =>
          have h1 : (q (k + 1) : ℝ) ≤ (qr (k + 1) : ℝ) :=
            Rat.cast_le.mpr (le_max_right (qr k) (q (k + 1)))
          exact ((le_max_right (0 : ℝ) (s - 1 / (((k + 1 : ℕ) : ℝ) + 1))).trans_lt (hq1 (k + 1))).trans_le h1
    let qR : ℕ → ℝ := fun (r : ℕ) => Rat.cast (K := ℝ) (qr r)
    have hqR : ∀ r, qR r = Rat.cast (K := ℝ) (qr r) := fun r => rfl
    have hIco : localizedQuad K s ω = ∫⁻ u in Ico 0 s, ENNReal.ofReal (K u ω ^ 2) ∂volume := by
      unfold localizedQuad
      refine setLIntegral_congr ?_
      have hdiff : symmDiff (Icc 0 s) (Ico 0 s) = {s} := by
        ext u; simp only [Set.mem_symmDiff, Set.mem_Icc, Set.mem_Ico, Set.mem_singleton_iff]
        constructor
        · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
          · exact le_antisymm h2 (not_lt.mp fun hlt => h3 ⟨h1, hlt⟩)
          · exact absurd ⟨h1, h2.le⟩ h3
        · rintro rfl; exact Or.inl ⟨⟨hs.1.le, le_rfl⟩, fun h => lt_irrefl _ h.2⟩
      refine (ae_eq_set.mpr ⟨?_, ?_⟩)
      · have : Icc 0 s \ Ico 0 s = {s} := by
          ext u
          simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ico, Set.mem_singleton_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact le_antisymm h2 (not_lt.mp fun hlt => h3 ⟨h1, hlt⟩)
          · rintro rfl; exact ⟨⟨hs.1.le, le_rfl⟩, fun h => lt_irrefl _ h.2⟩
        rw [this, Real.volume_singleton]
      · have : Ico 0 s \ Icc 0 s = ∅ := by
          ext u
          simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
          intro h
          exact h.2 ⟨h.1.1, h.1.2.le⟩
        rw [this, measure_empty]
    have hlim : Tendsto (fun r : ℕ => localizedQuad K (qR r) ω) atTop (𝓝 (localizedQuad K s ω)) := by
      rw [hIco]
      simp_rw [localizedQuad, ← lintegral_indicator measurableSet_Icc]
      rw [← lintegral_indicator measurableSet_Ico]
      refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
      · intro r
        -- `u ↦ (Icc 0 (qr r)).indicator (ofReal (K u ω ^ 2)) u` is measurable? Wait: `K · ω` might only be `AEMeasurable`?
        -- Actually we only need `le_of_tendsto` using `lintegral_iSup` on monotone indicator functions!
        -- Wait: we don't even need measurability of `K · ω` if we use `MeasureTheory.setLIntegral_iUnion`!
        exact ((ENNReal.measurable_ofReal.comp (hK.pow_const 2)).aemeasurable).indicator measurableSet_Icc
      · exact ae_of_all _ fun u r₁ r₂ h12 => by
          have hle : qR r₁ ≤ qR r₂ := by
            rw [hqR, hqR]; exact Rat.cast_le.mpr (hqr_mono h12)
          change (Icc 0 (qR r₁)).indicator (fun u => ENNReal.ofReal (K u ω ^ 2)) u ≤
            (Icc 0 (qR r₂)).indicator (fun u => ENNReal.ofReal (K u ω ^ 2)) u
          by_cases hu : u ∈ Icc 0 (qR r₁)
          · have hu2 : u ∈ Icc 0 (qR r₂) := ⟨hu.1, hu.2.trans hle⟩
            rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu2]
          · rw [Set.indicator_of_notMem hu]; exact bot_le
      · exact ae_of_all _ fun u => by
          by_cases hu : u ∈ Ico 0 s
          · obtain ⟨R, hR⟩ := exists_nat_gt (1 / (s - u))
            refine tendsto_atTop_of_eventually_const (i₀ := R) fun r hr => ?_
            have hsu : 0 < s - u := sub_pos.mpr hu.2
            have h1 : 1 / ((r : ℝ) + 1) < s - u := by
              have hlt : 1 / (s - u) < (r : ℝ) + 1 := lt_of_lt_of_le hR (by exact_mod_cast hr.trans (Nat.le_succ r))
              rw [div_lt_iff₀ (by positivity)]
              linarith [(div_lt_iff₀ hsu).mp hlt]
            have hu_mem : u ∈ Icc 0 (qR r) := ⟨hu.1, (by rw [hqR]; linarith [hqr_ge r])⟩
            rw [Set.indicator_of_mem hu_mem, Set.indicator_of_mem hu]
          · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun r _ => ?_
            have hnot : u ∉ Icc 0 (qR r) := fun h => hu ⟨h.1, h.2.trans_lt (hqR r ▸ hqr_lt r)⟩
            rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hu]
    exact le_of_tendsto hlim (Eventually.of_forall fun r => (hqR r).symm ▸ hall (qr r) (hqr_nn r) (hqr_lt r))

/-- Localized integrand `K_loc m s ω := K s ω` on `(0, T]` while `localizedQuad K s ω ≤ m`, else `0`. -/
def localizedK (K : ℝ → Ω → ℝ) (T : ℝ) (m : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  if s ∈ Ioc 0 T ∧ localizedQuad K s ω ≤ (m : ℝ≥0∞) then K s ω else 0

/-- Localized stopping level `τ_m ω = sup({0} ∪ {s ∈ (0, T] : Q(s, ω) ≤ m})`. -/
def localizedTau (K : ℝ → Ω → ℝ) (T : ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  sSup (insert (0 : ℝ) {s ∈ Ioc 0 T | localizedQuad K s ω ≤ (m : ℝ≥0∞)})

omit m₀ in
lemma localizedTau_mem {K : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T) (m : ℕ) (ω : Ω) :
    localizedTau K T m ω ∈ Icc 0 T := by
  have hne : (insert (0 : ℝ) {s ∈ Ioc 0 T | localizedQuad K s ω ≤ (m : ℝ≥0∞)}).Nonempty := ⟨0, Set.mem_insert _ _⟩
  have hbdd : BddAbove (insert (0 : ℝ) {s ∈ Ioc 0 T | localizedQuad K s ω ≤ (m : ℝ≥0∞)}) :=
    ⟨T, fun s hs => by rcases Set.mem_insert_iff.mp hs with rfl | h; exact hT.le; exact h.1.2⟩
  exact ⟨le_csSup hbdd (Set.mem_insert 0 _), csSup_le hne fun s hs => by
    rcases Set.mem_insert_iff.mp hs with rfl | h; exact hT.le; exact h.1.2⟩

omit m₀ in
lemma localizedQuad_at_tau_le {K : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    (hKm : ∀ ω, Measurable (fun u => K u ω)) (m : ℕ) (ω : Ω) :
    localizedQuad K (localizedTau K T m ω) ω ≤ (m : ℝ≥0∞) := by
  have hmem := localizedTau_mem (K := K) hT m ω
  rcases hmem.1.eq_or_lt with h0 | hpos
  · rw [← h0, localizedQuad_zero]; exact bot_le
  · -- By left-continuity at `τ = localizedTau K T m ω ∈ Ioc 0 T`
    have hne : (insert (0 : ℝ) {s ∈ Ioc 0 T | localizedQuad K s ω ≤ (m : ℝ≥0∞)}).Nonempty := ⟨0, Set.mem_insert _ _⟩
    have hbdd : BddAbove (insert (0 : ℝ) {s ∈ Ioc 0 T | localizedQuad K s ω ≤ (m : ℝ≥0∞)}) :=
      ⟨T, fun s hs => by rcases Set.mem_insert_iff.mp hs with rfl | h; exact hT.le; exact h.1.2⟩
    -- Use left-continuity on rationals `q < τ`
    have hall : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < localizedTau K T m ω → localizedQuad K (q : ℝ) ω ≤ (m : ℝ≥0∞) := by
      intro q hq0 hq_lt
      obtain ⟨s, hs_mem, hqs⟩ := (lt_csSup_iff hbdd hne).mp hq_lt
      rcases Set.mem_insert_iff.mp hs_mem with rfl | ⟨_, hQs⟩
      · linarith
      · exact (localizedQuad_mono K hqs.le ω).trans hQs
    -- Apply `localizedQuad_le_iff_rat` directly using `hKm ω`!
    -- Wait: in `localizedQuad_le_iff_rat` above, `AEMeasurable.indicator` needs `AEMeasurable (fun u => ENNReal.ofReal (K u ω ^ 2))`!
    -- Pass `hKm ω` to prove `localizedQuad_le_iff_rat` cleanly (see note right below)!
    exact (localizedQuad_le_iff_rat ⟨hpos, hmem.2⟩ ω m (hKm ω)).mpr hall

/-- **Raw-filtration localization**: `localizedK K T m` is `predSigma`-measurable and lies in
`L²(dtP P T)` with `∫⁻ u in Icc 0 T, ofReal (localizedK K T m u ω ^ 2) ≤ m` for EVERY `ω`! -/
lemma localized_pred_and_L2 {d : ℕ} (B : MultiBrownian Ω P d) {T : ℝ} (hT : 0 < T)
    {K : ℝ → Ω → ℝ} (hKp : IsPredictableProcess (pathFiltration B).σAlg T K) (m : ℕ) :
    IsPredictableProcess (pathFiltration B).σAlg T (localizedK K T m) ∧
    MemLp (Function.uncurry (localizedK K T m)) 2 (dtP P T) := by
  have hKm_slice : ∀ ω, Measurable (fun u => K u ω) := fun ω =>
    (hKp.mono (predSigma_le_prod (T := T) fun t _ => (pathFiltration B).le_ambient t) le_rfl).comp
      (measurable_id.prodMk measurable_const)
  -- 1. Predictability in the RAW filtration via `⋂ q : ℚ`
  have hset_pred : MeasurableSet[predSigma (pathFiltration B).σAlg T]
      {p : ℝ × Ω | p.1 ∈ Ioc 0 T ∧ localizedQuad K p.1 p.2 ≤ (m : ℝ≥0∞)} := by
    have heq : {p : ℝ × Ω | p.1 ∈ Ioc 0 T ∧ localizedQuad K p.1 p.2 ≤ (m : ℝ≥0∞)} =
        (Ioc 0 T ×ˢ (Set.univ : Set Ω)) ∩
        ⋂ q : ℚ, if hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T
          then (Ioc (q : ℝ) T ×ˢ {ω | (m : ℝ≥0∞) < localizedQuad K (q : ℝ) ω})ᶜ else Set.univ := by
      ext ⟨s, ω⟩
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_iInter]
      refine and_congr_right fun hs => ?_
      rw [localizedQuad_le_iff_rat hs ω m (hKm_slice ω)]
      constructor
      · intro hall q; split_ifs with hq
        · simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_ofPred_eq, not_and, not_lt]
          rintro ⟨hqs, _⟩; exact hall q hq.1 hqs
        · trivial
      · intro hall q hq0 hqs
        have hqI : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T := ⟨hq0, hqs.le.trans hs.2⟩
        have h := hall q; rw [dite_eq_left hqI] at h
        simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_ofPred_eq, not_and, not_lt] at h
        exact h ⟨hqs, hs.2⟩
    rw [heq]
    have hrect0 : MeasurableSet[predSigma (pathFiltration B).σAlg T]
        (Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predSigma_rect le_rfl hT.le le_rfl MeasurableSet.univ
    refine hrect0.inter (MeasurableSet.iInter fun q => ?_)
    split_ifs with hq
    · have hQ : MeasurableSet[(pathFiltration B).σAlg (q : ℝ)]
          {ω | (m : ℝ≥0∞) < localizedQuad K (q : ℝ) ω} :=
        measurableSet_lt measurable_const (measurable_localizedQuad B hKp hq.1 hq.2)
      have hrectq : MeasurableSet[predSigma (pathFiltration B).σAlg T]
          (Ioc (q : ℝ) T ×ˢ {ω | (m : ℝ≥0∞) < localizedQuad K (q : ℝ) ω}) :=
        measurableSet_predSigma_rect hq.1 hq.2 le_rfl hQ
      exact hrectq.compl
    · exact MeasurableSet.univ
  have hpred : IsPredictableProcess (pathFiltration B).σAlg T (localizedK K T m) := by
    have heq : Function.uncurry (localizedK K T m) =
        ({p : ℝ × Ω | p.1 ∈ Ioc 0 T ∧ localizedQuad K p.1 p.2 ≤ (m : ℝ≥0∞)}).indicator
          (Function.uncurry K) := by
      ext p
      dsimp only [Function.uncurry, localizedK, Set.indicator]
      by_cases h : p.1 ∈ Ioc 0 T ∧ localizedQuad K p.1 p.2 ≤ (m : ℝ≥0∞)
      · have hp : p ∈ {q : ℝ × Ω | q.1 ∈ Ioc 0 T ∧ localizedQuad K q.1 q.2 ≤ (m : ℝ≥0∞)} := h
        rw [ite_eq_left h, ite_eq_left hp]
      · have hp : p ∉ {q : ℝ × Ω | q.1 ∈ Ioc 0 T ∧ localizedQuad K q.1 q.2 ≤ (m : ℝ≥0∞)} := h
        rw [ite_eq_right h, ite_eq_right hp]
    unfold IsPredictableProcess
    rw [heq]
    exact hKp.indicator hset_pred
  refine ⟨hpred, ?_⟩
  -- 2. `L²(dtP P T)` bound: for EVERY `ω`, `∫⁻ u in Icc 0 T, ofReal (localizedK² u ω) ≤ m`!
  have hmeas_prod : Measurable (Function.uncurry (localizedK K T m)) :=
    hpred.mono (predSigma_le_prod (T := T) fun t _ => (pathFiltration B).le_ambient t) le_rfl
  change eLpNorm (Function.uncurry (localizedK K T m)) 2 (dtP P T) < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
        hmeas_prod.aestronglyMeasurable]
  have hlt_top : ∫⁻ p, ‖localizedK K T m p.1 p.2‖ₑ ^ (2 : ℝ) ∂(dtP P T) < ⊤ := by
    have hrew : ∀ p : ℝ × Ω, ‖localizedK K T m p.1 p.2‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (localizedK K T m p.1 p.2 ^ 2) := fun p => by
      set x := localizedK K T m p.1 p.2
      calc ‖x‖ₑ ^ (2 : ℝ)
          = ‖x‖ₑ ^ (2 : ℕ) := ENNReal.rpow_natCast _ 2
        _ = ENNReal.ofReal |x| ^ (2 : ℕ) := by rw [Real.enorm_eq_ofReal_abs]
        _ = ENNReal.ofReal (|x| ^ 2) := (ENNReal.ofReal_pow (abs_nonneg x) 2).symm
        _ = ENNReal.ofReal (x ^ 2) := by rw [sq_abs]
    simp_rw [hrew]
    unfold dtP
    rw [lintegral_prod_symm (fun p => ENNReal.ofReal (localizedK K T m p.1 p.2 ^ 2))
          (ENNReal.measurable_ofReal.comp (hmeas_prod.pow_const 2)).aemeasurable]
    have hrow : ∀ ω, ∫⁻ u in Icc 0 T, ENNReal.ofReal (localizedK K T m u ω ^ 2) ∂volume ≤ (m : ℝ≥0∞) := fun ω => by
      have hpt : ∀ u ∈ Icc 0 T, ENNReal.ofReal (localizedK K T m u ω ^ 2) ≤
          (Icc 0 (localizedTau K T m ω)).indicator (fun u => ENNReal.ofReal (K u ω ^ 2)) u := fun u hu => by
        by_cases hcond : u ∈ Ioc 0 T ∧ localizedQuad K u ω ≤ (m : ℝ≥0∞)
        · have hu_le : u ≤ localizedTau K T m ω := le_csSup
            ⟨T, fun s hs => by rcases Set.mem_insert_iff.mp hs with rfl | h; exact hT.le; exact h.1.2⟩
            (Set.mem_insert_of_mem 0 hcond)
          have huI : u ∈ Icc 0 (localizedTau K T m ω) := ⟨hu.1, hu_le⟩
          rw [Set.indicator_of_mem huI, localizedK, ite_eq_left hcond]
        · rw [localizedK, ite_eq_right hcond, sq, mul_zero, ENNReal.ofReal_zero]
          exact bot_le
      calc ∫⁻ u in Icc 0 T, ENNReal.ofReal (localizedK K T m u ω ^ 2) ∂volume
          ≤ ∫⁻ u in Icc 0 T, (Icc 0 (localizedTau K T m ω)).indicator (fun u => ENNReal.ofReal (K u ω ^ 2)) u ∂volume :=
            setLIntegral_mono' measurableSet_Icc hpt
        _ ≤ ∫⁻ u, (Icc 0 (localizedTau K T m ω)).indicator (fun u => ENNReal.ofReal (K u ω ^ 2)) u ∂volume :=
            setLIntegral_le_lintegral _ _
        _ = localizedQuad K (localizedTau K T m ω) ω := lintegral_indicator measurableSet_Icc _
        _ ≤ (m : ℝ≥0∞) := localizedQuad_at_tau_le hT hKm_slice m ω
    calc ∫⁻ ω, ∫⁻ u in Icc 0 T, ENNReal.ofReal (localizedK K T m u ω ^ 2) ∂volume ∂P
        ≤ ∫⁻ _ω, (m : ℝ≥0∞) ∂P := lintegral_mono hrow
      _ = (m : ℝ≥0∞) := by simp
      _ < ⊤ := ENNReal.natCast_lt_top m
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt_top.ne

/-! ## Section 2: Uniqueness of Limits in Measure on an Event & Supermartingale Step -/

omit [IsProbabilityMeasure P] in
/-- If `f_j → X` and `g_j → Y` in measure and `f_j = g_j` on `E` for all `j`, then `X = Y` a.s. on `E`. -/
private lemma ae_eq_on_of_tendstoInMeasure {f g : ℕ → Ω → ℝ} {X Y : Ω → ℝ} {E : Set Ω}
    (hf : TendstoInMeasure P f atTop X) (hg : TendstoInMeasure P g atTop Y)
    (heq : ∀ j, ∀ ω ∈ E, f j ω = g j ω) :
    ∀ᵐ ω ∂P, ω ∈ E → X ω = Y ω := by
  have hzero : ∀ k : ℕ, P (E ∩ {ω | 1 / ((k : ℝ) + 1) ≤ dist (X ω) (Y ω)}) = 0 := fun k => by
    set ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 < ε := by positivity
    have hsub : ∀ j, E ∩ {ω | ε ≤ dist (X ω) (Y ω)} ⊆
        {ω | ε / 2 ≤ dist (f j ω) (X ω)} ∪ {ω | ε / 2 ≤ dist (g j ω) (Y ω)} := fun j ω hω => by
      have hωE : ω ∈ E := hω.1
      have hdist : ε ≤ dist (X ω) (Y ω) := hω.2
      have hfeq : f j ω = g j ω := heq j ω hωE
      have htri : dist (X ω) (Y ω) ≤ dist (X ω) (f j ω) + dist (f j ω) (Y ω) := dist_triangle _ _ _
      by_cases h1 : ε / 2 ≤ dist (f j ω) (X ω)
      · exact Or.inl h1
      · right
        change ε / 2 ≤ dist (g j ω) (Y ω)
        rw [← hfeq]
        have hfX : dist (f j ω) (X ω) < ε / 2 := not_le.mp h1
        linarith [htri, hdist, dist_comm (X ω) (f j ω), hfX]
    refine le_antisymm ?_ bot_le
    have hf' := tendstoInMeasure_iff_dist.mp hf
    have hg' := tendstoInMeasure_iff_dist.mp hg
    have hsum : Tendsto (fun j => P {ω | ε / 2 ≤ dist (f j ω) (X ω)} + P {ω | ε / 2 ≤ dist (g j ω) (Y ω)})
        atTop (𝓝 (0 + 0)) := (hf' (ε / 2) (half_pos hε)).add (hg' (ε / 2) (half_pos hε))
    rw [zero_add] at hsum
    exact ge_of_tendsto hsum
      (Eventually.of_forall fun j => (measure_mono (hsub j)).trans (measure_union_le _ _))
  have hall : P (⋃ k : ℕ, E ∩ {ω | 1 / ((k : ℝ) + 1) ≤ dist (X ω) (Y ω)}) = 0 :=
    measure_iUnion_null hzero
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hall
  simp only [Set.mem_ofPred_eq, not_imp] at hω
  obtain ⟨hωE, hne⟩ := hω
  have hpos : 0 < dist (X ω) (Y ω) := dist_pos.mpr hne
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / dist (X ω) (Y ω))
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  have hk1 : 0 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
  have hlt : 1 / dist (X ω) (Y ω) < (k : ℝ) + 1 := lt_of_lt_of_le hk (by linarith)
  have hle : 1 / ((k : ℝ) + 1) ≤ dist (X ω) (Y ω) := by
    rw [div_le_iff₀ hk1, mul_comm]
    exact ((div_lt_iff₀ hpos).mp hlt).le
  exact ⟨hωE, hle⟩

/-- Subtracting the `k = 0` term from `itoRiemannSum` preserves `TendstoInMeasure`. -/
private lemma tendstoInMeasure_itoRiemannPrime_of_isItoIntegral {d : ℕ} (hd : 0 < d)
    (B : MultiBrownian Ω P d) (hB_cont : ∀ ω, Continuous (fun t => MultiBrownian.W B t ω (kitDriver hd)))
    {K V : ℝ → Ω → ℝ} {T : ℝ}
    (hIto : IsItoIntegral P (fun t ω => MultiBrownian.W B t ω (kitDriver hd)) K V T)
    (hK0 : Measurable (K 0))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    TendstoInMeasure P (fun n => itoRiemannPrime B hd K t n) atTop (V t) := by
  have hdiff : ∀ n ω, itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω -
      itoRiemannPrime B hd K t n ω =
      K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd) := fun n ω => by
    unfold itoRiemannSum itoRiemannPrime
    let term : ℕ → ℝ := fun k =>
      K ((k : ℝ) * t / ((n : ℝ) + 1)) ω *
        (MultiBrownian.W B (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω (kitDriver hd) -
          MultiBrownian.W B ((k : ℝ) * t / ((n : ℝ) + 1)) ω (kitDriver hd))
    have hFin : (∑ k : Fin (n + 1),
          K ((k : ℝ) * t / ((n : ℝ) + 1)) ω *
            ((fun s ω => MultiBrownian.W B s ω (kitDriver hd))
              (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω -
             (fun s ω => MultiBrownian.W B s ω (kitDriver hd))
              ((k : ℝ) * t / ((n : ℝ) + 1)) ω)) =
        ∑ k ∈ Finset.range (n + 1), term k := by
      refine Finset.sum_bij (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_
      · intro k hk; exact Finset.mem_range.mpr k.isLt
      · intro a _ b _ h; exact Fin.eq_of_val_eq h
      · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
      · intro k hk; simp [term]
    have hIco : (∑ k ∈ Finset.Ico 1 (n + 1),
          K ((k : ℝ) * t / ((n : ℝ) + 1)) ω *
            (MultiBrownian.W B (((k + 1 : ℕ) : ℝ) * t / ((n : ℝ) + 1)) ω (kitDriver hd) -
              MultiBrownian.W B ((k : ℝ) * t / ((n : ℝ) + 1)) ω (kitDriver hd))) =
        ∑ k ∈ Finset.Ico 1 (n + 1), term k := rfl
    have hsplit : ∑ k ∈ Finset.range (n + 1), term k =
        term 0 + ∑ k ∈ Finset.Ico 1 (n + 1), term k := by
      have h0mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ n)
      have hdiff' : Finset.range (n + 1) \ {0} = Finset.Ico 1 (n + 1) := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
        constructor
        · intro ⟨hk, hk0⟩; exact ⟨Nat.pos_of_ne_zero hk0, hk⟩
        · intro ⟨hk0, hk⟩; exact ⟨hk, Nat.pos_iff_ne_zero.mp hk0⟩
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h0mem, hdiff']
    have hW0 : MultiBrownian.W B 0 ω (kitDriver hd) = 0 := B.W_zero ω (kitDriver hd)
    rw [hFin, hIco, hsplit, add_sub_cancel_right]
    simp [term, hW0]
  have hzero_ae : ∀ ω, Tendsto (fun n : ℕ => K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd))
      atTop (𝓝 0) := fun ω => by
    have ht0 : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hB0 : Tendsto (fun n : ℕ => MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)) atTop (𝓝 0) := by
      have := ((hB_cont ω).tendsto 0).comp ht0
      rwa [B.W_zero ω (kitDriver hd)] at this
    simpa [mul_zero] using tendsto_const_nhds.mul hB0
  -- Combine `hIto.2.2 t ht` and `hzero_ae` directly via triangle inequality on `dist`
  refine tendstoInMeasure_iff_dist.mpr ?_
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]; intro δ hδ
  have hIto' := tendstoInMeasure_iff_dist.mp (hIto.2.2 t ht)
  obtain ⟨N₁, hN₁⟩ := (ENNReal.tendsto_atTop_zero.mp (hIto' (ε / 2) (half_pos hε))) (δ / 2)
    (ENNReal.half_pos hδ.ne')
  -- `P {ω | ε / 2 ≤ |K 0 ω * B₀ (t/(n+1)) ω|} → 0` since `→ 0` everywhere!
  have hzero_meas : Tendsto (fun n : ℕ => P {ω | ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)|})
      atTop (𝓝 0) := by
    -- Pointwise `X_n ω → 0` on a probability space ⇒ the measures of `{ε/2 ≤ |X_n|}` vanish.
    -- Work with the (always defined) measures of the indicated sets; the limsup is empty.
    have hlim : Tendsto
        (fun n : ℕ => P (⋃ k ≥ n, {ω | ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((k : ℝ) + 1)) ω (kitDriver hd)|}))
        atTop (𝓝 (P (⋂ n : ℕ, ⋃ k ≥ n, {ω | ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((k : ℝ) + 1)) ω (kitDriver hd)|}))) :=
      tendsto_measure_iInter_atTop
        (fun n => NullMeasurableSet.iUnion fun k => NullMeasurableSet.iUnion fun _ =>
          (measurableSet_le measurable_const
            ((hK0.mul (MultiBrownian.W_meas B _ _)).abs)).nullMeasurableSet)
        (fun a b hab =>
          Set.iUnion_subset fun k =>
            Set.iUnion_subset fun hk =>
              Set.subset_iUnion_of_subset k <|
                Set.subset_iUnion_of_subset (hab.trans hk) subset_rfl)
        ⟨0, measure_ne_top P _⟩
    have hemp : (⋂ n : ℕ, ⋃ k ≥ n, {ω | ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((k : ℝ) + 1)) ω (kitDriver hd)|}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      push Not
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hzero_ae ω)) (ε / 2) (half_pos hε)
      refine ⟨N, fun k hk => ?_⟩
      have := hN k hk
      simp only [Real.dist_eq, sub_zero] at this
      exact this
    rw [hemp, measure_empty] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
      fun n => measure_mono
        (Set.subset_iUnion_of_subset n (Set.subset_iUnion_of_subset le_rfl subset_rfl))
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp hzero_meas) (δ / 2) (ENNReal.half_pos hδ.ne')
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hsub : {ω | ε ≤ dist (itoRiemannPrime B hd K t n ω) (V t ω)} ⊆
      {ω | ε / 2 ≤ dist (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) (V t ω)} ∪
      {ω | ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)|} := fun ω hω => by
    have htri : dist (itoRiemannPrime B hd K t n ω) (V t ω) ≤
        dist (itoRiemannPrime B hd K t n ω)
          (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) +
        dist (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) (V t ω) :=
      dist_triangle _ _ _
    have hterm : dist (itoRiemannPrime B hd K t n ω)
        (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) =
        |K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)| := by
      rw [dist_comm, Real.dist_eq, hdiff]
    rw [hterm] at htri
    by_cases h1 : ε / 2 ≤ dist (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) (V t ω)
    · exact Or.inl h1
    · right
      change ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)|
      have hεle : ε ≤ dist (itoRiemannPrime B hd K t n ω) (V t ω) := by
        simpa [Set.mem_ofPred_eq] using hω
      have hsumlt : dist (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) (V t ω) < ε / 2 :=
        not_le.mp h1
      have hbound : ε ≤ |K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)| +
          dist (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) (V t ω) :=
        hεle.trans htri
      linarith [hbound, hsumlt]
  calc P {ω | ε ≤ dist (itoRiemannPrime B hd K t n ω) (V t ω)}
      ≤ P {ω | ε / 2 ≤ dist (itoRiemannSum K (fun s ω => MultiBrownian.W B s ω (kitDriver hd)) t n ω) (V t ω)} +
        P {ω | ε / 2 ≤ |K 0 ω * MultiBrownian.W B (t / ((n : ℝ) + 1)) ω (kitDriver hd)|} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ δ / 2 + δ / 2 := add_le_add (hN₁ n ((le_max_left _ _).trans hn)) (hN₂ n ((le_max_right _ _).trans hn))
    _ = δ := ENNReal.add_halves δ

/-! ## Section 3: Main Theorem — Bounded-Below NFLVR (Delbaen–Schachermayer, No H3!) -/

/-- Every gain `G ∈ BoundedBelowGains` for the genuine `L²` Itô cone is integrable with
nonpositive mean (`𝔼[G] = 0 ≤ 0`). Preserves the previous signature; does not use H3. -/
theorem expectation_le_zero_of_boundedBelowGain {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    (_hB_cont : ∀ ω, Continuous (fun t => MultiBrownian.W B t ω (kitDriver hd)))
    {T : ℝ} (hT : 0 < T) {S σ : ℝ → Ω → ℝ}
    (_hS_adapt : ∀ t ∈ Icc 0 T, Measurable[(pathFiltration B).σAlg t] (S t))
    (_hσ_adapt : ∀ t ∈ Icc 0 T, Measurable[(pathFiltration B).σAlg t] (σ t))
    (_hS_cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => S t ω) (Icc 0 T))
    (_hσ_cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => σ t ω) (Icc 0 T))
    {G : Ω → ℝ} (hG : G ∈ BoundedBelowGains (pathFiltration B).σAlg P
      (fun t ω => MultiBrownian.W B t ω (kitDriver hd)) S σ T) :
    Integrable G P ∧ ∫ ω, G ω ∂P ≤ 0 := by
  have hfilt : (generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
      (measurable_paperSig2_coeff B 0)).σAlg = (pathFiltration B).σAlg :=
    funext (sigFiltration_eq_pathFiltration B)
  rw [← hfilt] at hG
  rcases hG with ⟨H, V, a, -, -, hIto, rfl⟩
  obtain ⟨hInt, hEq0⟩ := expectation_eq_zero_of_isL2ItoIntegral hd B hT hIto
  exact ⟨hInt, hEq0.le⟩

/-- **Delbaen–Schachermayer NFLVR for uniformly bounded-below genuine `L²` Itô gains**
(no H3; preserves the existing signature). -/
theorem satisfiesNFLVR_DS_boundedBelowGains {d : ℕ} (hd : 0 < d) (B : MultiBrownian Ω P d)
    (_hB_cont : ∀ ω, Continuous (fun t => MultiBrownian.W B t ω (kitDriver hd)))
    {T : ℝ} (hT : 0 < T) {S σ : ℝ → Ω → ℝ}
    (_hS_adapt : ∀ t ∈ Icc 0 T, Measurable[(generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
      (measurable_paperSig2_coeff B 0)).σAlg t] (S t))
    (_hσ_adapt : ∀ t ∈ Icc 0 T, Measurable[(generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
      (measurable_paperSig2_coeff B 0)).σAlg t] (σ t))
    (_hS_cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => S t ω) (Icc 0 T))
    (_hσ_cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => σ t ω) (Icc 0 T)) :
    SatisfiesNFLVR_DS P
      (BoundedBelowGains
        (generatedFiltration (fun u I ω => (paperSig2 B 0 u ω).coeff I)
          (measurable_paperSig2_coeff B 0)).σAlg P
        (fun t ω => MultiBrownian.W B t ω (kitDriver hd)) S σ T) :=
  satisfiesNFLVR_DS_boundedBelowGains_any hd B hT S σ

end SignatureVolatility

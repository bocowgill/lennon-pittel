module

public import LennonPittel.PivotForwardPivotReadout
public import LennonPittel.PivotRelaxedArcEvents
public import LennonPittel.PivotReversePermutationCompatibility
public import LennonPittel.ReverseSupportWeightUpper

/-!
# The compatibility loss for reverse cycle collections

For a fixed candidate permutation, union-bound the crossed rectangles on
the relaxed column tests. The active male increments vary with the reveal;
their sum is controlled section by section before applying the product law.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The moved women's columns indexed by their old husbands. -/
def reverseMovedColumns {n : ℕ} (μ σ : Matching n) : Finset (Fin n) :=
  σ.support.map μ.symm.toEmbedding

theorem mem_reverseMovedColumns {n : ℕ} (μ σ : Matching n) (i : Fin n) :
    i ∈ reverseMovedColumns μ σ ↔ μ i ∈ σ.support := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := Finset.mem_map.mp h
    change μ.symm w = i at he
    rw [← he, Equiv.apply_symm_apply]
    exact hw
  · intro h
    exact Finset.mem_map.mpr ⟨μ i, h, μ.symm_apply_apply i⟩

/-- The product-column event covering any incompatible realized collection.
All designated arcs pass the relaxed tests, and at least one crossed
rectangle occurs. -/
def reverseCompatibilityCover {n : ℕ} (μ ρ σ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Set (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :=
  {z | (∀ i ∈ reverseMovedColumns μ σ, z.2 i ∈
      forwardInactiveRelaxedReverseArcEvent d flag ρ.support i (μ.symm (σ (μ i)))) ∧
    ∃ m ∈ ρ.support, ∃ i ∈ reverseMovedColumns μ σ,
      z.2 i ∈ forwardInactiveRelaxedCrossEvent d flag ρ.support i (μ.symm (σ (μ i))) m
        (forwardPivotIncrement d flag ρ z.1 m)}

set_option maxHeartbeats 800000 in
theorem measurableSet_reverseCompatibilityCover {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet (reverseCompatibilityCover μ ρ σ d flag) := by
  let S := reverseMovedColumns μ σ
  let B (i : Fin n) :=
    forwardInactiveRelaxedReverseArcEvent d flag ρ.support i (μ.symm (σ (μ i)))
  let V := ForwardRevealedMaleScores flag × ForwardInactiveColumns flag
  let E (m i : Fin n) : Set V := {z | z.2 i ∈
    forwardInactiveRelaxedCrossEvent d flag ρ.support i (μ.symm (σ (μ i))) m
      (forwardPivotIncrement d flag ρ z.1 m)}
  have he : reverseCompatibilityCover μ ρ σ d flag =
      (⋂ i : S, {z : V | z.2 i.val ∈ B i.val}) ∩
        (⋃ m : ρ.support, ⋃ i : S, E m.val i.val) := by
    ext z
    constructor
    · rintro ⟨h, m, hm, i, hi, hc⟩
      exact ⟨mem_iInter.mpr (fun i ↦ h i.val i.property),
        mem_iUnion.mpr ⟨⟨m, hm⟩, mem_iUnion.mpr ⟨⟨i, hi⟩, hc⟩⟩⟩
    · intro h
      obtain ⟨m, hm⟩ := mem_iUnion.mp h.2
      obtain ⟨i, hi⟩ := mem_iUnion.mp hm
      exact ⟨fun j hj ↦ mem_iInter.mp h.1 ⟨j, hj⟩, m.val, m.property, i.val, i.property, hi⟩
  rw [he]
  refine (MeasurableSet.iInter fun i ↦ ?_).inter
    (MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun i ↦ ?_)
  · exact (measurableSet_forwardInactiveRelaxedReverseArcEvent d flag ρ.support i.val _).preimage
      ((measurable_pi_apply i.val).comp measurable_snd)
  · let g (z : V) : ForwardRevealedMaleScores flag ×
        (ForwardInactiveColumnIndex flag i.val → ℝ × ℝ) := (z.1, z.2 i.val)
    have hg : Measurable g :=
      measurable_fst.prodMk ((measurable_pi_apply i.val).comp measurable_snd)
    let dx : ForwardRevealedMaleScores flag → ℝ := fun v ↦ forwardPivotIncrement d flag ρ v m.val
    have hdx : Measurable dx := measurable_forwardPivotIncrement d flag ρ m.val
    let F : Set (ForwardRevealedMaleScores flag ×
        (ForwardInactiveColumnIndex flag i.val → ℝ × ℝ)) := {z | z.2 ∈
      forwardInactiveRelaxedCrossEvent d flag ρ.support i.val (μ.symm (σ (μ i.val))) m.val
        (dx z.1)}
    have hF := @measurableSet_forwardInactiveRelaxedCrossEvent_varying n
      (ForwardRevealedMaleScores flag) inferInstance d flag ρ.support i.val
      (μ.symm (σ (μ i.val))) m.val dx hdx
    change MeasurableSet (g ⁻¹' F)
    exact hF.preimage hg

/-- Bound a normalized column section of the cover. The loss is linear in
the sum of the revealed pivot increments, not in separate uniform bounds
on every increment. -/
theorem measure_reverseCompatibilityCover_section_le {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (v : ForwardRevealedMaleScores flag)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1) {a D : ℝ} (ha : 0 < a)
    (hcomp : ∀ i (t : ForwardKeptColumnIndex flag ρ.support i),
      (∑ j, (diagonalPairAt d j).1) / a ≤ forwardKeptCompetitorMass d t)
    (hΔ0 : ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m)
    (hΔ : (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D) :
    let X := ∑ i, (diagonalPairAt d i).1
    (Measure.pi (normalizedForwardInactiveColumnLaw d flag))
      (Prod.mk v ⁻¹' reverseCompatibilityCover μ ρ σ d flag) ≤
      (ENNReal.ofReal a ^ σ.support.card * ∏ i ∈ σ.support, reverseSpouseWeights μ d i) *
        (σ.support.card : ℝ≥0∞) * ENNReal.ofReal (a * D / X) := by
  intro X
  let L := normalizedForwardInactiveColumnLaw d flag
  let : ∀ i : Fin n, IsProbabilityMeasure (L i) := fun i ↦
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  let S := reverseMovedColumns μ σ
  let j (i : Fin n) := μ.symm (σ (μ i))
  let B (i : Fin n) := forwardInactiveRelaxedReverseArcEvent d flag ρ.support i (j i)
  let dx (m : Fin n) := forwardPivotIncrement d flag ρ v m
  let C (m i : Fin n) := forwardInactiveRelaxedCrossEvent d flag ρ.support i (j i) m (dx m)
  let p (i : Fin n) := ENNReal.ofReal a * reverseSpouseWeights μ d (σ (μ i))
  let b (m : Fin n) := ENNReal.ofReal (a * dx m / X)
  have hp : (∏ i ∈ S, p i) =
      ENNReal.ofReal a ^ σ.support.card * ∏ i ∈ σ.support, reverseSpouseWeights μ d i := by
    change (∏ i ∈ σ.support.map μ.symm.toEmbedding, p i) = _
    rw [Finset.prod_map]
    simp only [p, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
    rw [σ.prod_comp σ.support (fun i ↦ ENNReal.ofReal a * reverseSpouseWeights μ d i)
      (fun _ h ↦ Equiv.Perm.mem_support.mpr h), Finset.prod_mul_distrib, Finset.prod_const]
  have hb : (∑ m ∈ ρ.support, b m) ≤ ENNReal.ofReal (a * D / X) := by
    change (∑ m ∈ ρ.support, ENNReal.ofReal (a * dx m / X)) ≤ _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m hm ↦
      div_nonneg (mul_nonneg ha.le (hΔ0 m hm)) hX.le), ← Finset.sum_div, ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hΔ ha.le) hX.le)
  calc
    _ ≤ (∏ i ∈ S, p i) * (S.card : ℝ≥0∞) * ∑ m ∈ ρ.support, b m :=
      measure_pi_exists_markedColumn_le L S ρ.support B C p b
        (fun i _ ↦ normalizedForwardInactiveColumnLaw_relaxedReverseArc_le d flag ρ.support i
          (j i) (hy0 i) (hy1 i) hx hX ha (fun t _ ↦ hcomp i t))
        (fun m hm i _ ↦ normalizedForwardInactiveColumnLaw_relaxedCross_le d flag ρ.support i
          (j i) m (hy0 i) (hy1 i) hx hX ha (hΔ0 m hm) (fun t _ ↦ hcomp i t))
    _ ≤ _ := by
      rw [hp, show S.card = σ.support.card from Finset.card_map _]
      exact mul_le_mul_right hb _

/-- The bad event for a prescribed collection: its arcs are realized, but
simultaneously undoing its cycles destroys exposure of the forward pivot. -/
def incompatibleReversePermutationEvent {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) : Set (OffDiagonalScorePairs n) :=
  {z | let p := profileOfScores ((splitScorePairs μ).symm (d, z))
       RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
         ¬ IsExposedRotation p (undoReverseRotation μ σ) ρ}

/-- A realized incompatible collection forces one crossed rectangle in
its relaxed columns. The pivot support is indexed by men and the reverse
support is indexed by women. -/
theorem incompatibleReversePermutationEvent_ae_le_cover {n : ℕ}
    (μ ρ σ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag))
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r))
    (hρ : ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      IsExposedRotation (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ)
    (hdisj : ∀ m ∈ ρ.support, μ m ∉ σ.support) :
    incompatibleReversePermutationEvent μ ρ σ d ≤ᵐ[forwardMaskRevealLaw d flag U]
      forwardRevealWithColumns flag ⁻¹' reverseCompatibilityCover μ ρ σ d flag := by
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  unfold forwardMaskRevealLaw at hρ ⊢
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht)), hρ]
    with z hzmask hzstable hzt hze hbad
  let x := (splitScorePairs μ).symm (d, z)
  have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  have hdiag (i : Fin n) : diagonalPairAt d i = (x (.inl i) (μ i), x (.inr (μ i)) i) := by
    simpa only [he] using diagonalPairAt_splitScorePairs μ x i
  have hs : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).2
    (by simpa only [he] using hzstable)
  have hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag :=
    by simpa only [he] using hzmask
  have hkept (w : Fin n) (hw : w ∈ σ.support) : μ.symm (σ w) ∉ ρ.support := by
    intro hm
    apply hdisj _ hm
    rw [Equiv.apply_symm_apply]
    exact Equiv.Perm.mem_support.mpr (σ.injective.ne (Equiv.Perm.mem_support.mp hw))
  let v := (forwardRevealWithColumns flag z).1
  let b := (forwardRevealWithColumns flag z).2
  have harc (i : Fin n) (hi : i ∈ reverseMovedColumns μ σ) :
      b i ∈ forwardInactiveReverseArcEvent d flag i (μ.symm (σ (μ i))) := by
    have hw := (mem_reverseMovedColumns μ σ i).mp hi
    have hne : μ.symm (σ (μ i)) ≠ i := fun e ↦
      Equiv.Perm.mem_support.mp hw (by simpa only [Equiv.apply_symm_apply] using congrArg μ e)
    have h := (isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ x flag hs hzt hmask
      i _ hne).mp (hbad.1 (μ i) hw)
    rw [he] at h
    exact h
  change (∀ i ∈ reverseMovedColumns μ σ, b i ∈ _) ∧ ∃ m ∈ ρ.support, ∃ i ∈
    reverseMovedColumns μ σ, b i ∈ forwardInactiveRelaxedCrossEvent d flag ρ.support i
      (μ.symm (σ (μ i))) m (forwardPivotIncrement d flag ρ v m)
  refine ⟨fun i hi ↦ forwardInactiveReverseArcEvent_subset_relaxed d flag ρ.support i _
    (hkept _ ((mem_reverseMovedColumns μ σ i).mp hi)) (harc i hi), ?_⟩
  obtain ⟨m, hm, w, hw, hmlo, hmhi, hwlo, hwhi⟩ :=
    exists_crossed_scores_of_not_exposed_after_reversePermutation hzt
      ((isStable_profileOfScores_iff hzt μ).mpr hs) hze hbad.1 hdisj hbad.2
  let i := μ.symm w
  have hiw : μ i = w := μ.apply_symm_apply w
  have hi : i ∈ reverseMovedColumns μ σ := (mem_reverseMovedColumns μ σ i).mpr (hiw.symm ▸ hw)
  have hne : m ≠ i := fun e ↦ hdisj m hm (e.symm ▸ (hiw.symm ▸ hw))
  let q : OffDiagonalCellIndex n := ⟨(m, i), hne⟩
  have hflag : flag q ≠ true := by
    intro hf
    have hh := mem_pi.mp hzmask q (mem_univ _)
    change z q ∈ forwardScoreCellFlagEvent (diagonalPairAt d m).1
      (diagonalPairAt d i).2 (flag q) at hh
    rw [hf, forwardScoreCellFlagEvent, ite_eq_left rfl, forwardEligibleScoreCell, hdiag] at hh
    have hq : z q = (x (.inl m) w, x (.inr w) m) := by
      simpa only [he, show μ q.val.2 = w from hiw] using splitScorePairs_offDiagonal_apply μ x q
    have hlt := (mem_prod.mp hh).2
    rw [hq, hdiag i, hiw] at hlt
    exact hwlo.not_gt (show x (.inr w) m < x (.inr w) i from hlt)
  let c : ForwardInactiveColumnIndex flag i := ⟨⟨q, hflag⟩, rfl⟩
  obtain ⟨t, ht'⟩ := mem_iUnion.mp (harc i hi)
  have htLabel : forwardInactiveColumnMan t.val = μ.symm (σ (μ i)) := t.property
  have hcell (u : ForwardInactiveColumnIndex flag i) :
      b i u = (x (.inl (forwardInactiveColumnMan u)) w, x (.inr w) (forwardInactiveColumnMan u)) := by
    change z u.val.val = _
    simpa only [he, u.property, hiw] using splitScorePairs_offDiagonal_apply μ x u.val.val
  have hdx : forwardPivotIncrement d flag ρ v m =
      x (.inl m) (μ (ρ m)) - x (.inl m) (μ m) := by
    simpa only [he] using forwardPivotIncrement_eq_of_exposed μ ρ x flag hzt hmask hze
      (Equiv.Perm.mem_support.mp hm)
  refine ⟨m, hm, i, hi, mem_forwardInactiveRelaxedCrossEvent_of_reverseArc t.val c
    htLabel rfl (hkept _ (hiw.symm ▸ hw)) hm ht' ?_⟩
  rw [reverseCompatibilityRectangle, hcell c, hcell t.val, hdx, hdiag, hdiag, htLabel, hiw]
  simp only [forwardInactiveColumnMan, c, q, mem_prod, mem_Ioo]
  refine ⟨⟨hmlo, ?_⟩, ⟨hwlo, ?_⟩⟩
  · linarith only [show x (.inl m) w < x (.inl m) (μ (ρ m)) from hmhi]
  · linarith only [show x (.inr w) m < x (.inr w) (μ.symm (σ w)) from hwhi]

/-- Hypotheses for the compatibility loss on a fixed score reveal. The
parameter `a` controls the inflation of relaxed arcs and `D` bounds the
total revealed male increment of the pivot. -/
structure ReverseCompatibilityControls {n : ℕ} (μ ρ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (U : Set (ForwardRevealedMaleScores flag))
    (a D : ℝ) : Prop where
  measurable_reveal : MeasurableSet U
  female_nonneg : ∀ i, 0 ≤ (diagonalPairAt d i).2
  female_lt_one : ∀ i, (diagonalPairAt d i).2 < 1
  male_mem : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1
  male_total_pos : 0 < ∑ i, (diagonalPairAt d i).1
  inflation_pos : 0 < a
  kept_mass : ∀ i (t : ForwardKeptColumnIndex flag ρ.support i),
    (∑ j, (diagonalPairAt d j).1) / a ≤ forwardKeptCompetitorMass d t
  increment_nonneg : ∀ v ∈ U, ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m
  increment_sum_le : ∀ v ∈ U, (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D
  tie_free : ∀ᵐ z ∂(offDiagonalScoreLaw n),
    ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)
  pivot_exposed : ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
    IsExposedRotation (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ

/-- The probability mass of an incompatible realization is at most its
relaxed product weight times the crossed-blocker loss factor. -/
theorem measure_incompatibleReversePermutationEvent_le {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) {a D : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hdisj : ∀ m ∈ ρ.support, μ m ∉ σ.support) :
    let X := ∑ i, (diagonalPairAt d i).1
    (forwardMaskRevealLaw d flag U) (incompatibleReversePermutationEvent μ ρ σ d) ≤
      (forwardMaskRevealLaw d flag U) univ *
        ((ENNReal.ofReal a ^ σ.support.card * ∏ i ∈ σ.support, reverseSpouseWeights μ d i) *
          (σ.support.card : ℝ≥0∞) * ENNReal.ofReal (a * D / X)) := by
  intro X
  rw [forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg h.female_lt_one
    h.tie_free]
  exact forwardMaskRevealLaw_measure_le_of_column_sections d flag U h.measurable_reveal
    h.female_nonneg h.female_lt_one (reverseCompatibilityCover μ ρ σ d flag)
    (measurableSet_reverseCompatibilityCover μ ρ σ d flag)
    (incompatibleReversePermutationEvent_ae_le_cover μ ρ σ d flag U h.tie_free h.pivot_exposed hdisj)
    (fun v hv ↦ measure_reverseCompatibilityCover_section_le μ ρ σ d flag v h.female_nonneg
      h.female_lt_one h.male_mem h.male_total_pos h.inflation_pos h.kept_mass
      (h.increment_nonneg v hv) (h.increment_sum_le v hv))

/-- At one support size the bad mass summed over all allowed collections
is bounded using the unit total support weight. -/
theorem sum_measure_incompatibleReversePermutationEvent_le {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (k : ℕ) {a D : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D) :
    let X := ∑ i, (diagonalPairAt d i).1
    let S := goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)
    (∑ σ ∈ S, (forwardMaskRevealLaw d flag U) (incompatibleReversePermutationEvent μ ρ σ d)) ≤
      (forwardMaskRevealLaw d flag U) univ *
        (ENNReal.ofReal a ^ k * (k : ℝ≥0∞) * ENNReal.ofReal (a * D / X)) := by
  intro X S
  let ν := forwardMaskRevealLaw d flag U
  let c := ENNReal.ofReal a ^ k * (k : ℝ≥0∞) * ENNReal.ofReal (a * D / X)
  let r := reverseSpouseWeights μ d
  calc
    _ ≤ ∑ σ ∈ S, (ν univ * c) * ∏ i ∈ σ.support, r i := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
      have hs := mem_goodReverseSupportPermutations.mp hσ
      have hd (m : Fin n) (hm : m ∈ ρ.support) : μ m ∉ σ.support :=
        fun ht ↦ (hs.2 (μ m) ht).1 (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
      have hbad := measure_incompatibleReversePermutationEvent_le μ ρ σ d flag U h hd
      dsimp only at hbad
      rw [hs.1] at hbad
      refine hbad.trans_eq ?_
      dsimp only [c, ν, r, X]
      ac_rfl
    _ = (ν univ * c) * ∑ σ ∈ S, ∏ i ∈ σ.support, r i := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_right
        (goodReverseSupportPermutations_weight_le_one k r
          (sum_reverseSpouseWeights μ d (fun i ↦ (h.male_mem i).1) h.male_total_pos) _ _) (ν univ * c)

end LennonPittelFormalization

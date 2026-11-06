module

public import LennonPittel.PivotLocalEligibility

/-!
# Filtered decorations at a marked matching

A single finite family records all permitted support sizes, including zero.
Its cardinality is a measurable real-valued count on the original score space.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {n : ℕ}

/-- All filtered compatible reverse permutations within the support cap. -/
noncomputable def markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.support.card ≤ K ∧
    σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x

theorem mem_markedFilteredChoices {μ ρ σ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    σ ∈ markedFilteredChoices μ ρ flag K L t x ↔ σ.support.card ≤ K ∧
      σ ∈ filteredReverseSupportFamily μ ρ flag σ.support.card L t x := by
  classical
  simp [markedFilteredChoices]

theorem support_card_eq_of_mem_filteredReverseSupportFamily {μ ρ σ : Matching n}
    {flag : OffDiagonalCellIndex n → Bool} {k L : ℕ} {t : ℝ} {x : ScoreProfile n}
    (h : σ ∈ filteredReverseSupportFamily μ ρ flag k L t x) : σ.support.card = k := by
  classical
  have hcomp := mem_compatibleReversePermutations.mp (Finset.mem_filter.mp h).1
  exact (mem_goodReverseSupportPermutations.mp hcomp.1).1

/-- The moment bound sums support sizes from two on; the marked family can
also retain the empty choice. -/
theorem sum_card_filteredReverseSupportFamily_le_card_markedFilteredChoices
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    (∑ k ∈ Finset.Icc 2 K, (filteredReverseSupportFamily μ ρ flag k L t x).card) ≤
      (markedFilteredChoices μ ρ flag K L t x).card := by
  classical
  let S (k : ℕ) := filteredReverseSupportFamily μ ρ flag k L t x
  have hdisj : (↑(Finset.Icc 2 K) : Set ℕ).PairwiseDisjoint S := by
    intro k _ l _ hne
    exact Finset.disjoint_left.mpr fun σ hk hl ↦
      hne ((support_card_eq_of_mem_filteredReverseSupportFamily hk).symm.trans
        (support_card_eq_of_mem_filteredReverseSupportFamily hl))
  change (∑ k ∈ Finset.Icc 2 K, (S k).card) ≤ _
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro σ hσ
  obtain ⟨k, hk, hσ⟩ := Finset.mem_biUnion.mp hσ
  have hcard := support_card_eq_of_mem_filteredReverseSupportFamily hσ
  exact mem_markedFilteredChoices.mpr
    ⟨hcard.trans_le (Finset.mem_Icc.mp hk).2, hcard.symm ▸ hσ⟩

/-- Each membership test is measurable even if the score cutoff varies with
the profile. -/
theorem measurableSet_mem_markedFilteredChoices (μ ρ σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    MeasurableSet {x : ScoreProfile n | σ ∈ markedFilteredChoices μ ρ flag K L (t x) x} := by
  classical
  have hinc :
      MeasurableSet {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} := by
    have he : {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ (t x)} =
        ⋂ w : σ.support, {x : ScoreProfile n |
          reverseScoreIncrement x μ w.val (μ.symm (σ w.val)) ≤ t x} := by
      ext x
      exact ⟨fun h ↦ mem_iInter.mpr fun w ↦ h w.val w.property,
        fun h w hw ↦ mem_iInter.mp h ⟨w, hw⟩⟩
    rw [he]
    exact MeasurableSet.iInter fun w ↦
      measurableSet_le (measurable_reverseScoreIncrement μ w.val (μ.symm (σ w.val))) ht
  have hcomp : MeasurableSet {x : ScoreProfile n |
      σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card (profileOfScores x)} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete : MeasurableSet
      {p : Profile n | σ ∈ compatibleReverseSupportFamily μ ρ flag σ.support.card p})
  simp only [mem_markedFilteredChoices, filteredReverseSupportFamily, Finset.mem_filter,
    ofPred_and]
  exact (MeasurableSet.const _).inter (hcomp.inter ((MeasurableSet.const _).inter hinc))

theorem measurable_card_markedFilteredChoices (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    {t : ScoreProfile n → ℝ} (ht : Measurable t) :
    Measurable (fun x ↦ ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)) := by
  have h := measurable_finsetCard_of_mem (fun x ↦ markedFilteredChoices μ ρ flag K L (t x) x)
    (fun σ ↦ measurableSet_mem_markedFilteredChoices μ ρ σ flag K L ht)
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using
    ENNReal.measurable_toReal.comp h

/-- The number of filtered choices at the marked pivot, zero off its local
eligibility event. Stability of the mark is imposed by the ambient law. -/
noncomputable def localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x μ ρ then
    ((markedFilteredChoices μ ρ (forwardMaskOfScores (splitScorePairs μ x).1
      (splitScorePairs μ x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x).card : ℝ)
    else 0

private theorem measurable_mask_switch {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β] {M : α → β}
    (hM : Measurable M) {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x ↦ f (M x) x) := by
  intro s hs
  let E (j : β) := {x : α | M x = j ∧ f j x ∈ s}
  have he : (fun x ↦ f (M x) x) ⁻¹' s = ⋃ j, E j := by
    ext x
    change f (M x) x ∈ s ↔ x ∈ ⋃ j, E j
    simp only [mem_iUnion, E, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨M x, rfl, hx⟩, fun ⟨j, hj, hx⟩ ↦ hj.symm ▸ hx⟩
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ (hM (measurableSet_singleton j)).inter (hf j hs)

theorem measurable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Measurable (localFilteredDecorationCount b A B K L μ ρ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x μ)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedFilteredChoices μ ρ flag K L (t x) x).card : ℝ)
  have hM : Measurable M :=
    (measurable_jointForwardMaskOfScores n).comp (splitScorePairs μ).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal μ)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) :=
    measurable_card_markedFilteredChoices μ ρ flag K L ht
  exact (measurable_mask_switch hM hf).ite (measurableSet_isLocallyEligiblePivot b A B μ ρ)
    measurable_const

theorem localFilteredDecorationCount_nonneg (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    0 ≤ localFilteredDecorationCount b A B K L μ ρ x := by
  classical
  unfold localFilteredDecorationCount
  split <;> positivity

/-- A uniform bound, independent of the score profile and all cutoffs. -/
theorem localFilteredDecorationCount_le_factorial (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (x : ScoreProfile n) :
    localFilteredDecorationCount b A B K L μ ρ x ≤ (n.factorial : ℝ) := by
  classical
  unfold localFilteredDecorationCount
  split
  · apply Nat.cast_le.mpr
    simpa only [Fintype.card_perm, Fintype.card_fin] using
      Finset.card_le_univ (markedFilteredChoices μ ρ
        (forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2)
        K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x)
  · positivity

/-- Boundedness makes the marked count integrable for every finite law. -/
theorem integrable_localFilteredDecorationCount (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (ν : Measure (ScoreProfile n)) [IsFiniteMeasure ν] :
    Integrable (localFilteredDecorationCount b A B K L μ ρ) ν := by
  refine (integrable_const (n.factorial : ℝ)).mono'
    (measurable_localFilteredDecorationCount b A B K L μ ρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x)]
  exact localFilteredDecorationCount_le_factorial b A B K L μ ρ x

theorem localFilteredDecorationCount_of_eligible_of_fixedMask {b A B : ℝ}
    (K L : ℕ) {μ ρ : Matching n} {x : ScoreProfile n} {flag : OffDiagonalCellIndex n → Bool}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    localFilteredDecorationCount b A B K L μ ρ x = ((
      markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal (splitScorePairs μ x).1)) x).card :
      ℝ) := by
  classical
  rw [localFilteredDecorationCount, ite_eq_left h, (forwardMaskOfScores_eq_iff _ _ _).mpr hmask,
    reverseDiagonalMaleTotal_splitScorePairs]

theorem localFilteredDecorationCount_of_not_eligible {b A B : ℝ} (K L : ℕ)
    {μ ρ : Matching n} {x : ScoreProfile n} (h : ¬ IsLocallyEligiblePivot b A B x μ ρ) :
    localFilteredDecorationCount b A B K L μ ρ x = 0 := by
  classical
  rw [localFilteredDecorationCount, ite_eq_right h]

section MatchingEndpoints

variable {x : ScoreProfile n} {μ₀ μ ρ σ : Matching n}
  {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}

/-- A member of the marked count is a compatible reverse permutation at
the corresponding singleton anchor. -/
theorem isCompatibleReversePermutation_of_mem_markedFilteredChoices
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    IsCompatibleReversePermutation hopt K r σ := by
  classical
  obtain ⟨hcap, hm⟩ := mem_markedFilteredChoices.mp hσ
  have hc := mem_compatibleReversePermutations.mp (Finset.mem_filter.mp hm).1
  have hg := (mem_goodReverseSupportPermutations.mp hc.1).2
  change RealizesSuccessorPermutation (swapProfile (profileOfScores x))
    (singletonRotationAnchor hopt r).val.symm σ ∧ σ.support.card ≤ K ∧
    (∀ m ∈ r.val.cycle.support, (singletonRotationAnchor hopt r).val m ∉ σ.support) ∧
    IsExposedRotation (profileOfScores x)
      (undoReverseRotation (singletonRotationAnchor hopt r).val σ) r.val.cycle
  rw [hμ, hρ]
  exact ⟨hc.2.1, hcap, fun m hm hmem ↦ (hg _ hmem).1
    (Finset.mem_map.mpr ⟨m, hm, rfl⟩), hc.2.2⟩

/-- Distinct counted permutations give distinct actual filtered decorations,
including the empty choice when it passes the tests. -/
noncomputable def markedFilteredChoicesEmbedding
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (ht : 0 ≤ t) :
    (↥(markedFilteredChoices μ ρ flag K L t x)) ↪ FilteredPivotDecoration hopt K r L t := by
  classical
  let f (σ : ↥(markedFilteredChoices μ ρ flag K L t x)) :
      CompatibleReversePermutation hopt K r :=
    ⟨σ.val, isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hμ hρ
      σ.property⟩
  let e := compatibleReversePermutationEmbedding hopt K r
  refine ⟨fun σ ↦ ⟨e (f σ), ?_⟩, ?_⟩
  · have hf := (Finset.mem_filter.mp (mem_markedFilteredChoices.mp σ.property).2).2
    exact compatibleReversePermutationToDecoration_passesReverseFilters (f σ) ht hf.1
      (by rw [hμ]; exact hf.2)
  · intro σ τ he
    exact Subtype.ext (congrArg (fun a : CompatibleReversePermutation hopt K r ↦ a.val)
      (e.injective (congrArg Subtype.val he)))

theorem card_markedFilteredChoices_le_card_filteredPivotDecoration
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (hμ : (singletonRotationAnchor hopt r).val = μ) (hρ : r.val.cycle = ρ)
    (ht : 0 ≤ t) :
    (markedFilteredChoices μ ρ flag K L t x).card ≤
      Nat.card (FilteredPivotDecoration hopt K r L t) := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective _
    (markedFilteredChoicesEmbedding hopt r hμ hρ ht).injective

end MatchingEndpoints

/-- A stable matching exposing exactly one cycle is that cycle's singleton
anchor, with respect to the specified man-optimal start. -/
theorem exists_singletonRotationAnchor_of_soleForwardExposed {p : Profile n}
    {μ₀ μ ρ : Matching n} (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hsole : IsSoleForwardExposedRotation p μ ρ) :
    ∃ r : Rotation p μ₀, (singletonRotationAnchor hopt r).val = μ ∧ r.val.cycle = ρ := by
  let r := rotationOfExposed hopt hμ hsole.1
  refine ⟨r, ?_, rfl⟩
  have hanchor := (eq_singletonRotationAnchor_iff hopt r ⟨μ, hμ⟩).mpr fun s ↦ by
    constructor
    · intro hs
      exact Subtype.ext (hs.2.symm.trans (congrArg (rotationLabel μ) (hsole.2 _ hs.1)))
    · rintro rfl
      exact ⟨hsole.1, rfl⟩
  exact (congrArg Subtype.val hanchor).symm

/-- An endpoint from a marked choice at a stable singleton pivot is stable. -/
theorem isStable_undoReverseRotation_of_mem_markedFilteredChoices {x : ScoreProfile n}
    {μ ρ σ : Matching n} {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
    (hμ : IsStable (profileOfScores x) μ)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    IsStable (profileOfScores x) (undoReverseRotation μ σ) := by
  classical
  have h := mem_compatibleReversePermutations.mp
    (Finset.mem_filter.mp (mem_markedFilteredChoices.mp hσ).2).1
  exact h.2.1.undo_stable hμ

/-- Removing cycle factors from a counted choice retains compatibility,
the mask exclusions, and both filters. -/
theorem mem_markedFilteredChoices_of_cycleFactors_subset {x : ScoreProfile n}
    {μ ρ σ τ : Matching n} {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ}
    (hμ : IsStable (profileOfScores x) μ)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x)
    (hsub : τ.cycleFactorsFinset ⊆ σ.cycleFactorsFinset) :
    τ ∈ markedFilteredChoices μ ρ flag K L t x := by
  classical
  obtain ⟨hsize, hs⟩ := mem_markedFilteredChoices.mp hσ
  obtain ⟨hc, hshort, hinc⟩ := Finset.mem_filter.mp hs
  obtain ⟨hgood, hreal, hcompat⟩ := mem_compatibleReversePermutations.mp hc
  have hallowed := (mem_goodReverseSupportPermutations.mp hgood).2
  have hsupp : τ.support ⊆ σ.support := by
    intro w hw
    obtain ⟨c, hc, hwc⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hw
    exact Equiv.Perm.mem_cycleFactorsFinset_support_le (hsub hc) hwc
  have heq (w : Fin n) (hw : w ∈ τ.support) : τ w = σ w := by
    obtain ⟨c, hc, hwc⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hw
    exact ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 w hwc).symm.trans
      ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hsub hc)).2 w hwc)
  have hreal' : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm τ :=
    realizesSuccessorPermutation_iff_factors.mpr fun c hc ↦
      realizesSuccessorPermutation_iff_factors.mp hreal c (hsub hc)
  have hfix (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation μ σ m = μ m :=
    undoReverseRotation_apply_of_not_mem_support fun hw ↦
      (hallowed (μ m) hw).1 (Finset.mem_map.mpr ⟨m, Equiv.Perm.mem_support.mpr hm, rfl⟩)
  have hfix' (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation μ τ m = μ m :=
    undoReverseRotation_apply_of_not_mem_support fun hw ↦
      (hallowed (μ m) (hsupp hw)).1
        (Finset.mem_map.mpr ⟨m, Equiv.Perm.mem_support.mpr hm, rfl⟩)
  have hcompat' : IsExposedRotation (profileOfScores x) (undoReverseRotation μ τ) ρ := by
    apply (isExposedRotation_iff_no_pivotCrossBlocker hρ (hreal'.undo_stable hμ) hfix').mpr
    intro m w h
    have hw : w ∈ τ.support := Equiv.Perm.mem_support.mpr fun hw ↦
      h.2.1 (by rw [undoReverseRotation_symm_apply, hw])
    have hpartner : (undoReverseRotation μ τ).symm w = (undoReverseRotation μ σ).symm w := by
      simp only [undoReverseRotation_symm_apply, heq w hw]
    apply (isExposedRotation_iff_no_pivotCrossBlocker hρ (hreal.undo_stable hμ) hfix).mp hcompat
      m w
    exact ⟨h.1, by rw [← hpartner]; exact h.2.1, h.2.2.1, by rw [← hpartner]; exact h.2.2.2⟩
  apply mem_markedFilteredChoices.mpr
  refine ⟨(Finset.card_le_card hsupp).trans hsize, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · refine mem_compatibleReversePermutations.mpr ⟨?_, hreal', hcompat'⟩
    apply mem_goodReverseSupportPermutations.mpr
    refine ⟨rfl, fun i hi ↦ ⟨(hallowed i (hsupp hi)).1, ?_⟩⟩
    rw [heq i hi]
    exact (hallowed i (hsupp hi)).2
  · exact reverseCollectionFilters_mono x μ σ τ L t hsub hshort hinc

/-- The decorated stable endpoint identifies its long pivot, then the anchor,
then the reverse permutation. The two masks and cutoffs need not agree. -/
theorem markedFilteredChoices_endpoint_injective {x : ScoreProfile n}
    {μ₀ μ μ' ρ ρ' σ σ' : Matching n}
    {flag flag' : OffDiagonalCellIndex n → Bool} {K L L' : ℕ} {t t' : ℝ}
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hμ : IsStable (profileOfScores x) μ) (hμ' : IsStable (profileOfScores x) μ')
    (hs : IsSoleForwardExposedRotation (profileOfScores x) μ ρ)
    (hs' : IsSoleForwardExposedRotation (profileOfScores x) μ' ρ')
    (hl : K < ρ.support.card) (hl' : K < ρ'.support.card)
    (hσ : σ ∈ markedFilteredChoices μ ρ flag K L t x)
    (hσ' : σ' ∈ markedFilteredChoices μ' ρ' flag' K L' t' x)
    (he : undoReverseRotation μ σ = undoReverseRotation μ' σ') :
    μ = μ' ∧ ρ = ρ' ∧ σ = σ' := by
  obtain ⟨r, hrμ, hrρ⟩ := exists_singletonRotationAnchor_of_soleForwardExposed hopt hμ hs
  obtain ⟨r', hrμ', hrρ'⟩ :=
    exists_singletonRotationAnchor_of_soleForwardExposed hopt hμ' hs'
  let a : CompatibleReversePermutation hopt K r :=
    ⟨σ, isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hrμ hrρ hσ⟩
  let a' : CompatibleReversePermutation hopt K r' :=
    ⟨σ', isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r' hrμ' hrρ' hσ'⟩
  let q : LongPivot (profileOfScores x) μ₀ K :=
    ⟨r, by simpa only [rotationLength, hrρ] using hl⟩
  let q' : LongPivot (profileOfScores x) μ₀ K :=
    ⟨r', by simpa only [rotationLength, hrρ'] using hl'⟩
  let f := pivotDecorationEmbedding hopt K
  have hf : f ⟨q, compatibleReversePermutationToDecoration hopt K r a⟩ =
      f ⟨q', compatibleReversePermutationToDecoration hopt K r' a'⟩ := by
    apply Subtype.ext
    change (compatibleReversePermutationToDecoration hopt K r a).matching.val =
      (compatibleReversePermutationToDecoration hopt K r' a').matching.val
    rw [compatibleReversePermutationToDecoration_matching,
      compatibleReversePermutationToDecoration_matching, hrμ, hrμ']
    exact he
  have hr : r = r' :=
    congrArg (fun z : Σ s : LongPivot (profileOfScores x) μ₀ K, PivotDecoration hopt K s.val ↦
      z.1.val) (f.injective hf)
  have hm : μ = μ' :=
    hrμ.symm.trans ((congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) hr).trans hrμ')
  refine ⟨hm, hrρ.symm.trans ((congrArg (fun s : Rotation (profileOfScores x) μ₀ ↦
    s.val.cycle) hr).trans hrρ'), ?_⟩
  rw [← hm] at he
  apply Equiv.ext
  intro w
  exact μ.symm.injective (by
    simpa only [undoReverseRotation_symm_apply] using
      congrArg (fun ν : Matching n ↦ ν.symm w) he)

/-- The total filtered count over the score-stable marked matching and
the possible pivot permutations. At an eligible mark only its sole
forward-exposed permutation can contribute. -/
noncomputable def totalLocalFilteredDecorationCount (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact ∑ μ : Matching n, ∑ ρ : Matching n,
    if IsScoreStable x μ then localFilteredDecorationCount b A B K L μ ρ x else 0

theorem measurable_totalLocalFilteredDecorationCount (b A B : ℝ) (K L : ℕ) :
    Measurable (totalLocalFilteredDecorationCount (n := n) b A B K L) := by
  classical
  unfold totalLocalFilteredDecorationCount
  exact Finset.measurable_sum _ fun μ _ ↦ Finset.measurable_sum _ fun ρ _ ↦
    (measurable_localFilteredDecorationCount b A B K L μ ρ).ite
      (measurableSet_isScoreStable μ) measurable_const

private noncomputable def stableMarkedChoices (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) (μ ρ : Matching n) : Finset (Matching n) := by
  classical
  exact if IsScoreStable x μ ∧ IsLocallyEligiblePivot b A B x μ ρ then
    markedFilteredChoices μ ρ
      (forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2)
      K L (reverseIncrementCutoff n (maleSpouseTotal x μ)) x
    else ∅

/-- The total real-valued filtered count is bounded by the number of stable
matchings whenever every contributing pivot is longer than the support cap. -/
theorem totalLocalFilteredDecorationCount_le_numStableMatchings {b A B : ℝ} {K L : ℕ}
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row))
    (hl : ∀ μ ρ : Matching n, IsScoreStable x μ → IsLocallyEligiblePivot b A B x μ ρ →
      K < ρ.support.card) :
    totalLocalFilteredDecorationCount b A B K L x ≤
      (numStableMatchings (profileOfScores x) : ℝ) := by
  classical
  let F (i : Matching n × Matching n) := stableMarkedChoices b A B K L x i.1 i.2
  let P := (Finset.univ : Finset (Matching n × Matching n)).sigma F
  let g (a : Σ _ : Matching n × Matching n, Matching n) := undoReverseRotation a.1.1 a.2
  have hdata (a : ↥P) :
      IsStable (profileOfScores x) a.val.1.1 ∧
      IsSoleForwardExposedRotation (profileOfScores x) a.val.1.1 a.val.1.2 ∧
      K < a.val.1.2.support.card ∧
      a.val.2 ∈ markedFilteredChoices a.val.1.1 a.val.1.2
        (forwardMaskOfScores (splitScorePairs a.val.1.1 x).1 (splitScorePairs a.val.1.1 x).2)
        K L (reverseIncrementCutoff n (maleSpouseTotal x a.val.1.1)) x := by
    have ha := (Finset.mem_sigma.mp a.property).2
    change a.val.2 ∈ stableMarkedChoices b A B K L x a.val.1.1 a.val.1.2 at ha
    unfold stableMarkedChoices at ha
    split at ha
    · rename_i h
      exact ⟨(isStable_profileOfScores_iff ht _).mpr h.1, h.2.isSoleForwardExposed ht,
        hl _ _ h.1 h.2, ha⟩
    · exact (Finset.notMem_empty _ ha).elim
  let e (a : ↥P) : {μ : Matching n // IsStable (profileOfScores x) μ} :=
    ⟨g a.val, isStable_undoReverseRotation_of_mem_markedFilteredChoices (hdata a).1
      (hdata a).2.2.2⟩
  have hinj : Function.Injective e := by
    intro a a' he
    obtain ⟨ha, has, hal, ham⟩ := hdata a
    obtain ⟨ha', has', hal', ham'⟩ := hdata a'
    have hg : g a.val = g a'.val := congrArg Subtype.val he
    obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨a.val.1.1, ha⟩
    obtain ⟨hm, hr, hc⟩ :=
      markedFilteredChoices_endpoint_injective hopt ha ha' has has' hal hal' ham ham' hg
    apply Subtype.ext
    exact Sigma.ext (Prod.ext hm hr) (heq_of_eq hc)
  have hcard : P.card ≤ numStableMatchings (profileOfScores x) := by
    have h := Nat.card_le_card_of_injective e hinj
    rwa [Nat.card_eq_finsetCard, Nat.card_eq_fintype_card] at h
  have hsum : (P.card : ℝ) = totalLocalFilteredDecorationCount b A B K L x := by
    rw [show P = (Finset.univ : Finset (Matching n × Matching n)).sigma F from rfl,
      Finset.card_sigma, Nat.cast_sum, Fintype.sum_prod_type]
    unfold totalLocalFilteredDecorationCount
    refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ρ _ ↦ ?_
    change ((stableMarkedChoices b A B K L x μ ρ).card : ℝ) = _
    by_cases hμ : IsScoreStable x μ <;> by_cases hρ : IsLocallyEligiblePivot b A B x μ ρ <;>
      simp [stableMarkedChoices, localFilteredDecorationCount, hμ, hρ]
  rw [← hsum]
  exact_mod_cast hcard

/-- The square-root coefficient gap ensures every locally eligible pivot
is longer than the support cutoff. -/
theorem IsLocallyEligiblePivot.supportCap_lt {b A B κ : ℝ} {K : ℕ} {x : ScoreProfile n}
    {μ ρ : Matching n} (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hn : 0 < n) (hκ : κ < b) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    K < ρ.support.card := by
  have hr : (K : ℝ) < (ρ.support.card : ℝ) :=
    hK.trans_lt ((mul_lt_mul_of_pos_right hκ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).trans_le
      h.1.length_lower)
  exact_mod_cast hr

end LennonPittelFormalization

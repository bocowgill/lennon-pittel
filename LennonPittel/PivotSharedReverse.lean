module

public import LennonPittel.PivotMarkedDecorationCount

/-!
# The shared reverse cycles of comparable anchors

A woman on a reverse cycle at the later anchor has the same husband at the
earlier anchor exactly when that cycle's label is already in the earlier ideal.
This identifies the residual marked pairs to which the shared-switch toggle applies.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}

/-- At comparable stable matchings, a woman on a later reverse cycle has an
unchanged husband exactly when that rotation was already eliminated earlier. -/
theorem reverseExposedRotationLabel_mem_earlier_iff_unchanged
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : MenWeaklyPrefer p μ ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ})
    {w : Fin n} (hw : w ∈ σ.val.support) :
    reverseExposedRotationLabel hopt hν σ ∈ eliminatedRotations p μ₀ μ ↔
      μ.symm w = ν.symm w := by
  let r := reverseExposedRotationLabel hopt hν σ
  let m := ν.symm w
  have hm : r.val.cycle m ≠ m := by
    intro h
    change ν.symm (σ.val (ν m)) = m at h
    exact (Equiv.Perm.mem_support.mp hw) (by simpa [m] using congrArg ν h)
  have hnew : rotationLabelNewPartner r.val m = some (ν m) := by
    change rotationLabelNewPartner
      (rotationLabel (undoReverseRotation ν σ.val) (reverseRotationCycle ν.symm σ.val)) m = _
    have hm' : reverseRotationCycle ν.symm σ.val m ≠ m := hm
    rw [rotationLabelNewPartner_eq hm', eliminateRotation_undoReverseRotation]
  constructor
  · intro hr
    have hle' := (mem_eliminatedRotations_iff_newRank_le hopt hμ hm hnew).mp hr
    have he := (p.manRank m).injective (le_antisymm (hle m) hle')
    apply μ.injective
    simpa only [m, Equiv.apply_symm_apply] using he.symm
  · intro hsame
    by_contra hnot
    have hsub : eliminatedRotations p μ₀ μ ⊆
        eliminatedRotations p μ₀ (undoReverseRotation ν σ.val) := by
      rw [eliminatedRotations_undoReverseRotation hopt hν σ]
      intro s hs
      refine ⟨(eliminatedRotations_subset_iff hopt hμ hν).mpr hle hs, ?_⟩
      intro he
      exact hnot ((Set.mem_singleton_iff.mp he) ▸ hs)
    have hundo := σ.property.undo_stable hν
    obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hμ hundo
      ((eliminatedRotations_subset_iff hopt hμ hundo).mp hsub)
    have hstrict : p.womanRank w (ν.symm w) <
        p.womanRank w ((undoReverseRotation ν σ.val).symm w) :=
      (σ.property.successor w (Equiv.Perm.mem_support.mp hw)).eligible.1
    exact hstrict.not_ge (by simpa only [hsame] using hpath.womanRank_end_le w)

/-- A compatible collection of later reverse cycles removes an earlier label
exactly when at least one participating woman has the same husband at both anchors. -/
theorem exists_realizedReverseRemovedLabel_mem_earlier_iff
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : MenWeaklyPrefer p μ ν) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) ν.symm σ) :
    (∃ γ ∈ Subtype.val '' (↑(realizedReverseRemovedLabels hopt hν hσ) :
      Set (MaximalEliminatedRotation p μ₀ ν)),
      γ ∈ eliminatedRotations p μ₀ μ) ↔
    ∃ w ∈ σ.support, μ.symm w = ν.symm w := by
  classical
  constructor
  · rintro ⟨γ, ⟨a, ha, rfl⟩, hγ⟩
    change a ∈ realizedReverseRemovedLabels hopt hν hσ at ha
    rw [realizedReverseRemovedLabels] at ha
    obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp ha
    let τ : {τ : Matching n // IsReverseExposedRotation p ν τ} :=
      ⟨c.val, realizesSuccessorPermutation_iff_factors.mp hσ c.val c.property⟩
    obtain ⟨w, hw⟩ := Finset.card_pos.mp
      ((by decide : 0 < 2).trans_le τ.property.isCycle.two_le_card_support)
    exact ⟨w, Equiv.Perm.mem_cycleFactorsFinset_support_le c.property hw,
      (reverseExposedRotationLabel_mem_earlier_iff_unchanged hopt hμ hν hle τ hw).mp hγ⟩
  · rintro ⟨w, hw, hsame⟩
    obtain ⟨c, hc, hwc⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hw
    let τ : {τ : Matching n // IsReverseExposedRotation p ν τ} :=
      ⟨c, realizesSuccessorPermutation_iff_factors.mp hσ c hc⟩
    refine ⟨reverseExposedRotationLabel hopt hν τ,
      ⟨reverseExposedRotationEquivMaximal hopt hν τ, ?_, rfl⟩,
      (reverseExposedRotationLabel_mem_earlier_iff_unchanged hopt hμ hν hle τ hwc).mpr hsame⟩
    change reverseExposedRotationEquivMaximal hopt hν τ ∈
      realizedReverseRemovedLabels hopt hν hσ
    rw [realizedReverseRemovedLabels]
    exact Finset.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_attach _ _, rfl⟩

/-- The order of singleton anchors is exactly the order of their exposed labels. -/
theorem menWeaklyPrefer_singletonRotationAnchor_iff
    (hopt : IsManOptimal p μ₀) (r s : Rotation p μ₀) :
    MenWeaklyPrefer p (singletonRotationAnchor hopt r).val (singletonRotationAnchor hopt s).val
      ↔ r ≤ s := by
  rw [← eliminatedRotations_subset_iff hopt (singletonRotationAnchor hopt r).property
      (singletonRotationAnchor hopt s).property,
    eliminatedRotations_singletonRotationAnchor, eliminatedRotations_singletonRotationAnchor]
  constructor
  · intro h
    by_contra hrs
    exact (h (show s ∈ (Set.Ici r)ᶜ from hrs)) (Set.mem_Ici.mpr le_rfl)
  · exact fun h _ ha hb ↦ ha (h.trans hb)

section MarkedChoices

variable {x : ScoreProfile n} {hopt : IsManOptimal (profileOfScores x) μ₀}
  {K L : ℕ} {t₁ t₂ : ℝ} {ρ η : Matching n}
  {flag₁ flag₂ : OffDiagonalCellIndex n → Bool}

/-- Shared labels in the decoration of a marked choice are detected on the
original matching by an unchanged husband in the support. -/
theorem markedFilteredChoicesEmbedding_shared_iff
    (r s : Rotation (profileOfScores x) μ₀) (hμ : (singletonRotationAnchor hopt r).val = μ)
    (hν : (singletonRotationAnchor hopt s).val = ν) (hη : s.val.cycle = η)
    (hrs : r ≤ s) (ht₂ : 0 ≤ t₂)
    (τ : ↥(markedFilteredChoices ν η flag₂ K L t₂ x)) :
    (∃ γ ∈ (markedFilteredChoicesEmbedding hopt s hν hη ht₂ τ).val.removedLabels,
      γ ∈ eliminatedRotations (profileOfScores x) μ₀ μ) ↔
    ∃ w ∈ τ.val.support, μ.symm w = ν.symm w := by
  let A := singletonRotationAnchor hopt r
  let B := singletonRotationAnchor hopt s
  let hτ :=
    (isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt s hν hη τ.property).1
  have hle := (menWeaklyPrefer_singletonRotationAnchor_iff hopt r s).mpr hrs
  have h := exists_realizedReverseRemovedLabel_mem_earlier_iff hopt A.property B.property hle hτ
  rw [← hμ]
  calc
    _ ↔ ∃ w ∈ τ.val.support, A.val.symm w = B.val.symm w := h
    _ ↔ _ := by
      dsimp only [A, B]
      rw [hν]

/-- The decoration attached to a marked choice has exactly its explicit endpoint. -/
theorem markedFilteredChoicesEmbedding_matching
    (r : Rotation (profileOfScores x) μ₀) (hμ : (singletonRotationAnchor hopt r).val = μ)
    (hρ : r.val.cycle = ρ) (ht₁ : 0 ≤ t₁)
    (σ : ↥(markedFilteredChoices μ ρ flag₁ K L t₁ x)) :
    (markedFilteredChoicesEmbedding hopt r hμ hρ ht₁ σ).val.matching.val =
      undoReverseRotation μ σ.val := by
  let a : CompatibleReversePermutation hopt K r :=
    ⟨σ.val,
      isCompatibleReversePermutation_of_mem_markedFilteredChoices hopt r hμ hρ σ.property⟩
  change (compatibleReversePermutationToDecoration hopt K r a).matching.val = _
  rw [compatibleReversePermutationToDecoration_matching, hμ]

/-- A strictly comparable pair of marked choices with an unchanged woman in the
later reverse support is a residual pair for the shared-switch toggle. -/
noncomputable def residualPivotPairOfMarkedChoices
    (r s : LongPivot (profileOfScores x) μ₀ K) (hrs : r.val < s.val)
    (hμ : (singletonRotationAnchor hopt r.val).val = μ)
    (hν : (singletonRotationAnchor hopt s.val).val = ν)
    (hρ : r.val.val.cycle = ρ) (hη : s.val.val.cycle = η)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (σ : ↥(markedFilteredChoices μ ρ flag₁ K L t₁ x))
    (τ : ↥(markedFilteredChoices ν η flag₂ K L t₂ x))
    (hw : ∃ w ∈ τ.val.support, μ.symm w = ν.symm w) :
    ResidualPivotPair hopt K :=
  ⟨⟨r, (markedFilteredChoicesEmbedding hopt r.val hμ hρ ht₁ σ).val⟩,
    ⟨s, (markedFilteredChoicesEmbedding hopt s.val hν hη ht₂ τ).val⟩, hrs, by
      rw [hμ]
      exact
        (markedFilteredChoicesEmbedding_shared_iff r.val s.val hμ hν hη hrs.le ht₂ τ).mpr hw⟩

end MarkedChoices

section GlobalMarkedPairs

variable {x : ScoreProfile n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}

/-- A marked reverse choice at a stable singleton anchor with a long pivot. -/
structure LongMarkedChoice (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  anchor : Matching n
  cycle : Matching n
  reverse : Matching n
  stable : IsStable (profileOfScores x) anchor
  sole : IsSoleForwardExposedRotation (profileOfScores x) anchor cycle
  long : K < cycle.support.card
  cutoff_nonneg : 0 ≤ t anchor cycle
  mem_choices : reverse ∈
    markedFilteredChoices anchor cycle (flag anchor cycle) K L (t anchor cycle) x

namespace LongMarkedChoice

variable (a : LongMarkedChoice x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)

/-- The realized label of the unique forward cycle, with its length certificate. -/
noncomputable def pivot : LongPivot (profileOfScores x) μ₀ K := by
  let h := exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole
  exact ⟨Classical.choose h,
    by simpa only [rotationLength, (Classical.choose_spec h).2] using a.long⟩

theorem pivot_anchor : (singletonRotationAnchor hopt (a.pivot hopt).val).val = a.anchor :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).1

theorem pivot_cycle : (a.pivot hopt).val.val.cycle = a.cycle :=
  (Classical.choose_spec
    (exists_singletonRotationAnchor_of_soleForwardExposed hopt a.stable a.sole)).2

theorem eq_of_endpoint_eq (hopt : IsManOptimal (profileOfScores x) μ₀)
    {a' : LongMarkedChoice x K L flag t}
    (h : undoReverseRotation a.anchor a.reverse = undoReverseRotation a'.anchor a'.reverse) :
    a = a' := by
  obtain ⟨ha, hc, hr⟩ := markedFilteredChoices_endpoint_injective hopt a.stable a'.stable
    a.sole a'.sole a.long a'.long a.mem_choices a'.mem_choices h
  cases a
  cases a'
  cases ha
  cases hc
  cases hr
  rfl

end LongMarkedChoice

/-- An ordered pair counted by the marked residual term: the later reverse
choice moves at least one woman whose anchor husbands agree. -/
structure ResidualMarkedPair (x : ScoreProfile n) (K L : ℕ)
    (flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool)
    (t : Matching n → Matching n → ℝ) where
  early : LongMarkedChoice x K L flag t
  late : LongMarkedChoice x K L flag t
  prefer : MenWeaklyPrefer (profileOfScores x) early.anchor late.anchor
  ne : early.anchor ≠ late.anchor
  shared : ∃ w ∈ late.reverse.support, early.anchor.symm w = late.anchor.symm w

namespace ResidualMarkedPair

variable (a : ResidualMarkedPair x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)

private theorem pivot_lt : (a.early.pivot hopt).val < (a.late.pivot hopt).val := by
  apply lt_of_le_of_ne
  · apply (menWeaklyPrefer_singletonRotationAnchor_iff hopt _ _).mp
    rw [a.early.pivot_anchor hopt, a.late.pivot_anchor hopt]
    exact a.prefer
  · intro h
    have heq := congrArg (fun s ↦ (singletonRotationAnchor hopt s).val) h
    exact a.ne ((a.early.pivot_anchor hopt).symm.trans (heq.trans (a.late.pivot_anchor hopt)))

/-- A marked residual pair, retaining its two pivots and reverse choices. -/
noncomputable def toResidualPivotPair : ResidualPivotPair hopt K :=
  residualPivotPairOfMarkedChoices (a.early.pivot hopt) (a.late.pivot hopt)
    (by exact a.pivot_lt hopt) (a.early.pivot_anchor hopt) (a.late.pivot_anchor hopt)
    (a.early.pivot_cycle hopt) (a.late.pivot_cycle hopt)
    a.early.cutoff_nonneg a.late.cutoff_nonneg
    ⟨a.early.reverse, a.early.mem_choices⟩ ⟨a.late.reverse, a.late.mem_choices⟩ a.shared

theorem toResidualPivotPair_early_endpoint :
    (a.toResidualPivotPair hopt).early.2.matching.val =
      undoReverseRotation a.early.anchor a.early.reverse :=
  markedFilteredChoicesEmbedding_matching (a.early.pivot hopt).val (a.early.pivot_anchor hopt)
    (a.early.pivot_cycle hopt) a.early.cutoff_nonneg ⟨a.early.reverse, a.early.mem_choices⟩

theorem toResidualPivotPair_late_endpoint :
    (a.toResidualPivotPair hopt).late.2.matching.val =
      undoReverseRotation a.late.anchor a.late.reverse :=
  markedFilteredChoicesEmbedding_matching (a.late.pivot hopt).val (a.late.pivot_anchor hopt)
    (a.late.pivot_cycle hopt) a.late.cutoff_nonneg ⟨a.late.reverse, a.late.mem_choices⟩

/-- The early decoration meets its original cutoff after restoring the shared label. -/
theorem toResidualPivotPair_toggledEarly_passesReverseFilters
    (hties : ∀ row, Function.Injective (x row)) :
    (a.toResidualPivotPair hopt).toggledEarly.2.PassesReverseFilters L
      (t a.early.anchor a.early.cycle) :=
  (a.toResidualPivotPair hopt).toggledEarly_passesReverseFilters L
    (fun _ ↦ t a.early.anchor a.early.cycle) hties
    (markedFilteredChoicesEmbedding hopt (a.early.pivot hopt).val (a.early.pivot_anchor hopt)
      (a.early.pivot_cycle hopt) a.early.cutoff_nonneg
      ⟨a.early.reverse, a.early.mem_choices⟩).property

/-- The later decoration still meets its original cutoff; it is unchanged by the toggle. -/
theorem toResidualPivotPair_late_passesReverseFilters :
    (a.toResidualPivotPair hopt).late.2.PassesReverseFilters L
      (t a.late.anchor a.late.cycle) :=
  (markedFilteredChoicesEmbedding hopt (a.late.pivot hopt).val (a.late.pivot_anchor hopt)
    (a.late.pivot_cycle hopt) a.late.cutoff_nonneg
    ⟨a.late.reverse, a.late.mem_choices⟩).property

/-- No information about either marked choice is lost, even across different anchors. -/
theorem toResidualPivotPair_injective (hopt : IsManOptimal (profileOfScores x) μ₀) :
    Function.Injective
      (fun a : ResidualMarkedPair x K L flag t ↦ a.toResidualPivotPair hopt) := by
  intro a a' h
  have he := congrArg (fun R : ResidualPivotPair hopt K ↦ R.early.2.matching.val) h
  have hl := congrArg (fun R : ResidualPivotPair hopt K ↦ R.late.2.matching.val) h
  dsimp only at he hl
  rw [a.toResidualPivotPair_early_endpoint hopt, a'.toResidualPivotPair_early_endpoint hopt] at he
  rw [a.toResidualPivotPair_late_endpoint hopt, a'.toResidualPivotPair_late_endpoint hopt] at hl
  have hae := a.early.eq_of_endpoint_eq hopt he
  have hal := a.late.eq_of_endpoint_eq hopt hl
  cases a
  cases a'
  cases hae
  cases hal
  rfl

/-- The existing shared-switch toggle bounds the global marked residual count. -/
theorem card_le_twice_incomparable (hopt : IsManOptimal (profileOfScores x) μ₀) :
    Nat.card (ResidualMarkedPair x K L flag t) ≤
      2 * Nat.card (IncomparableStableMatchingPair (profileOfScores x) μ₀) :=
  (Nat.card_le_card_of_injective _ (toResidualPivotPair_injective hopt)).trans
    (ResidualPivotPair.card_le_twice_incomparable hopt K)

/-- Any extra property proved on all toggle images can restrict the target count. -/
theorem card_le_twice_incomparable_restrict (hopt : IsManOptimal (profileOfScores x) μ₀)
    {Q : IncomparableStableMatchingPair (profileOfScores x) μ₀ → Prop}
    (hQ : ∀ a : ResidualMarkedPair x K L flag t, Q (a.toResidualPivotPair hopt).toggleImage) :
    Nat.card (ResidualMarkedPair x K L flag t) ≤ 2 * Nat.card {MN // Q MN} := by
  let P (R : ResidualPivotPair hopt K) :=
    ∃ a : ResidualMarkedPair x K L flag t, a.toResidualPivotPair hopt = R
  let e (a : ResidualMarkedPair x K L flag t) : {R // P R} :=
    ⟨a.toResidualPivotPair hopt, ⟨a, rfl⟩⟩
  have he : Function.Injective e := fun _ _ h ↦
    toResidualPivotPair_injective hopt (congrArg Subtype.val h)
  refine (Nat.card_le_card_of_injective e he).trans
    (ResidualPivotPair.card_le_twice_incomparable_restrict ?_)
  rintro _ ⟨a, rfl⟩
  exact hQ a

end ResidualMarkedPair

end GlobalMarkedPairs

end LennonPittelFormalization

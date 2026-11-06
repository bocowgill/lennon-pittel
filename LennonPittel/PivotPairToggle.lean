module

public import LennonPittel.PivotIncidenceCounting
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# The deterministic shared-switch toggle

The centered comparable-pair term counts pairs with an earlier pivot and a shared
switch removed by the later decoration. Restore one such switch in the earlier
matching. The resulting matchings are incomparable, and the two endpoints and
one bit determine the original pair.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r : Rotation p μ₀}

namespace PivotDecoration

/-- The realized labels removed by this decoration. -/
def removedLabels (D : PivotDecoration hopt K r) : Set (Rotation p μ₀) :=
  Subtype.val '' (↑D.removed :
    Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))

/-- The endpoint ideal is the anchor ideal minus the removed labels. -/
theorem matching_eliminated (D : PivotDecoration hopt K r) :
    eliminatedRotations p μ₀ D.matching.val =
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val \ D.removedLabels :=
  eliminatedRotations_undoMaximalSubsetEmbedding hopt
    (singletonRotationAnchor hopt r).property D.removed

/-- Restore the specified label, if it was removed, in a decoration. -/
noncomputable def eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀) :
    PivotDecoration hopt K r := by
  classical
  let E := D.removed.filter (fun s ↦ s.val ≠ γ)
  have hE : E ⊆ D.removed := Finset.filter_subset _ _
  refine ⟨E, ?_, ?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun _ _ _ ↦ Nat.zero_le _)).trans D.totalLength_le
  · apply (pivot_isExposedAt_undo_iff hopt r E).mpr
    rintro _ ⟨s, hs, rfl⟩
    exact (pivot_isExposedAt_undo_iff hopt r D.removed).mp D.pivot_exposed _
      ⟨s, hE hs, rfl⟩

@[simp]
theorem mem_eraseRemovedLabel (D : PivotDecoration hopt K r) (γ : Rotation p μ₀)
    (s : MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val) :
    s ∈ (D.eraseRemovedLabel γ).removed ↔ s ∈ D.removed ∧ s.val ≠ γ := by
  classical
  exact Finset.mem_filter

theorem eraseRemovedLabel_subset (D : PivotDecoration hopt K r) (γ : Rotation p μ₀) :
    (D.eraseRemovedLabel γ).removed ⊆ D.removed :=
  fun s hs ↦ ((mem_eraseRemovedLabel D γ s).mp hs).1

theorem notMem_removedLabels_eraseRemovedLabel (D : PivotDecoration hopt K r)
    (γ : Rotation p μ₀) : γ ∉ (D.eraseRemovedLabel γ).removedLabels := by
  rintro ⟨s, hs, hsg⟩
  exact ((mem_eraseRemovedLabel D γ s).mp hs).2 hsg

private theorem mem_removedLabels_iff (D : PivotDecoration hopt K r)
    (s : MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val) :
    s.val ∈ D.removedLabels ↔ s ∈ D.removed := by
  constructor
  · rintro ⟨t, ht, hts⟩
    exact Subtype.ext hts ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

/-- The truncated subset and the one restored-label membership determine the original. -/
theorem eq_of_eraseRemovedLabel_eq {D E : PivotDecoration hopt K r} (γ : Rotation p μ₀)
    (h : D.eraseRemovedLabel γ = E.eraseRemovedLabel γ)
    (hbit : γ ∈ D.removedLabels ↔ γ ∈ E.removedLabels) : D = E := by
  have hsets : D.removed = E.removed := by
    ext s
    by_cases hs : s.val = γ
    · rw [← mem_removedLabels_iff, ← mem_removedLabels_iff, hs]
      exact hbit
    · have he : s ∈ (D.eraseRemovedLabel γ).removed ↔
          s ∈ (E.eraseRemovedLabel γ).removed := by rw [h]
      simpa only [mem_eraseRemovedLabel, and_iff_left hs] using he
  cases D
  cases E
  cases hsets
  rfl

end PivotDecoration

/-- A long pivot together with a truncated compatible decoration. -/
abbrev PivotCode (hopt : IsManOptimal p μ₀) (K : ℕ) :=
  Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val

/-- A residual comparable pair: the later decoration removes a label in the earlier anchor. -/
structure ResidualPivotPair (hopt : IsManOptimal p μ₀) (K : ℕ) where
  early : PivotCode hopt K
  late : PivotCode hopt K
  pivot_lt : early.1.val < late.1.val
  shared : ∃ γ ∈ late.2.removedLabels,
    γ ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt early.1.val).val

/-- Ordered pairs of stable matchings with incomparable eliminated ideals. -/
abbrev IncomparableStableMatchingPair (p : Profile n) (μ₀ : Matching n) :=
  {MN : {M : Matching n // IsStable p M} × {N : Matching n // IsStable p N} //
    (¬ eliminatedRotations p μ₀ MN.1.val ⊆ eliminatedRotations p μ₀ MN.2.val) ∧
    (¬ eliminatedRotations p μ₀ MN.2.val ⊆ eliminatedRotations p μ₀ MN.1.val)}

namespace ResidualPivotPair

/-- A choice determined solely by the earlier pivot and the later decorated code. -/
noncomputable def sharedLabel (R : ResidualPivotPair hopt K) : Rotation p μ₀ :=
  Classical.choose R.shared

theorem sharedLabel_mem_late (R : ResidualPivotPair hopt K) :
    R.sharedLabel ∈ R.late.2.removedLabels :=
  (Classical.choose_spec R.shared).1

theorem sharedLabel_mem_early_anchor (R : ResidualPivotPair hopt K) :
    R.sharedLabel ∈
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val :=
  (Classical.choose_spec R.shared).2

/-- Restore the shared label in the earlier code. The later code is left unchanged. -/
noncomputable def toggledEarly (R : ResidualPivotPair hopt K) : PivotCode hopt K :=
  ⟨R.early.1, R.early.2.eraseRemovedLabel R.sharedLabel⟩

/-- The two resulting stable matchings are incomparable. -/
noncomputable def toggleImage (R : ResidualPivotPair hopt K) :
    IncomparableStableMatchingPair p μ₀ := by
  refine ⟨(R.toggledEarly.2.matching, R.late.2.matching), ?_, ?_⟩
  · intro h
    have he : R.sharedLabel ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val := by
      rw [PivotDecoration.matching_eliminated]
      exact ⟨R.sharedLabel_mem_early_anchor,
        R.early.2.notMem_removedLabels_eraseRemovedLabel R.sharedLabel⟩
    have hl := h he
    rw [PivotDecoration.matching_eliminated] at hl
    exact hl.2 R.sharedLabel_mem_late
  · intro h
    have hl : R.early.1.val ∈ eliminatedRotations p μ₀ R.late.2.matching.val :=
      (Rotation.lt_iff_before_exposure hopt R.pivot_lt.ne).mp R.pivot_lt
        _ R.late.2.matching.property R.late.2.pivot_exposed.1 R.late.2.pivot_exposed.2
    have he := h hl
    rw [PivotDecoration.matching_eliminated, eliminatedRotations_singletonRotationAnchor] at he
    apply he.1
    change R.toggledEarly.1.val ≤ R.early.1.val
    exact le_rfl

/-- The earlier singleton ideal is contained in the later singleton ideal. -/
theorem early_anchor_ideal_subset_late_anchor (R : ResidualPivotPair hopt K) :
    eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val ⊆
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.late.1.val).val := by
  rw [eliminatedRotations_singletonRotationAnchor,
    eliminatedRotations_singletonRotationAnchor]
  exact fun _ hs hls ↦ hs (R.pivot_lt.le.trans hls)

/-- The short orientation consists of the later removed labels in the earlier
anchor that are not removed by the toggled earlier decoration. -/
theorem toggle_early_ideal_diff_late (R : ResidualPivotPair hopt K) :
    eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val =
      (R.late.2.removedLabels ∩
        eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val) \
          R.toggledEarly.2.removedLabels := by
  rw [PivotDecoration.matching_eliminated, PivotDecoration.matching_eliminated]
  ext s
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨ha, he⟩, hn⟩
    refine ⟨⟨?_, ha⟩, he⟩
    by_contra h
    exact hn ⟨R.early_anchor_ideal_subset_late_anchor ha, h⟩
  · rintro ⟨⟨hl, ha⟩, he⟩
    exact ⟨⟨ha, he⟩, fun h ↦ h.2 hl⟩

/-- Every label in the short orientation is exposed at the later matching. -/
theorem isExposedAt_late_of_mem_toggle_early_ideal_diff_late (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
      eliminatedRotations p μ₀ R.late.2.matching.val) :
    s.IsExposedAt R.late.2.matching.val := by
  rw [R.toggle_early_ideal_diff_late] at hs
  exact (R.late.2.isExposedAt_matching_iff s).mpr (Or.inr hs.1.1)

/-- The finite collection of labels in the short orientation. -/
noncomputable def shortOrientationLabels (R : ResidualPivotPair hopt K) :
    Finset (Rotation p μ₀) := by
  classical
  exact (R.late.2.removed.filter fun s ↦
    s.val ∈ eliminatedRotations p μ₀ (singletonRotationAnchor hopt R.early.1.val).val ∧
    s.val ∉ R.toggledEarly.2.removedLabels).map ⟨Subtype.val, Subtype.val_injective⟩

/-- The finite short orientation records the exact ideal difference. -/
theorem coe_shortOrientationLabels (R : ResidualPivotPair hopt K) :
    (↑R.shortOrientationLabels : Set (Rotation p μ₀)) =
      eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val := by
  classical
  rw [R.toggle_early_ideal_diff_late]
  ext s
  simp only [shortOrientationLabels, Finset.mem_coe, Finset.mem_map, Finset.mem_filter,
    Function.Embedding.coeFn_mk, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨t, ⟨ht, ha, he⟩, rfl⟩
    exact ⟨⟨⟨t, ht, rfl⟩, ha⟩, he⟩
  · rintro ⟨⟨⟨t, ht, rfl⟩, ha⟩, he⟩
    exact ⟨t, ⟨ht, ha, he⟩, rfl⟩

/-- The combined length of all labels in the short orientation is at most the cap. -/
theorem sum_rotationLength_shortOrientationLabels_le (R : ResidualPivotPair hopt K) :
    (∑ s ∈ R.shortOrientationLabels, rotationLength s) ≤ K := by
  classical
  rw [shortOrientationLabels, Finset.sum_map]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ ↦ Nat.zero_le _)).trans R.late.2.totalLength_le

/-- Men who have a worse partner in the toggled earlier matching. -/
noncomputable def shortOrientationMen (R : ResidualPivotPair hopt K) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦
    p.manRank m (R.late.2.matching.val m) < p.manRank m (R.toggledEarly.2.matching.val m)

/-- Men who have a worse partner in the later matching. -/
noncomputable def longOrientationMen (R : ResidualPivotPair hopt K) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦
    p.manRank m (R.toggledEarly.2.matching.val m) < p.manRank m (R.late.2.matching.val m)

private theorem exists_diff_label_moving_of_rank_lt {A B : Matching n}
    (hopt : IsManOptimal p μ₀) (hA : IsStable p A) (hB : IsStable p B)
    (hAB : MenWeaklyPrefer p A B) {m : Fin n}
    (hm : p.manRank m (A m) < p.manRank m (B m)) :
    ∃ s : Rotation p μ₀,
      s ∈ eliminatedRotations p μ₀ B \ eliminatedRotations p μ₀ A ∧
        s.val.cycle m ≠ m ∧ rotationLabelNewPartner s.val m = some (B m) := by
  obtain ⟨us, hfirst⟩ := exists_rotationSequence_of_manOptimal hopt hA
  obtain ⟨vs, hnext⟩ := exists_rotationSequence_of_menWeaklyPrefer hA hB hAB
  rcases hnext.partner_eq_or_label_newPartner m with he | ⟨l, hl, hmove, hnew⟩
  · exact (hm.ne (congrArg (p.manRank m) he)).elim
  · have hall := hfirst.append hnext
    have hlall : l ∈ rotationLabels μ₀ (us ++ vs) := by
      rw [hfirst.rotationLabels_append]
      exact List.mem_append_right _ hl
    let s : Rotation p μ₀ := ⟨l, B, us ++ vs, hall, hlall⟩
    refine ⟨s, ⟨hall.mem_eliminatedRotations_iff.mpr hlall, ?_⟩, hmove, hnew⟩
    intro hmem
    exact hm.not_ge ((mem_eliminatedRotations_iff_newRank_le hopt hA hmove hnew).mp hmem)

/-- The short orientation's moved men all belong to the supports of its short labels. -/
theorem shortOrientationMen_subset (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen ⊆ R.shortOrientationLabels.biUnion (fun s ↦ s.val.cycle.support) := by
  classical
  intro m hm
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  obtain ⟨J, hJ, hIJ⟩ := exists_eliminatedRotations_union hopt A.property B.property
  have hAJ : MenWeaklyPrefer p A.val J := (eliminatedRotations_subset_iff hopt A.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_left)
  have hBJ : MenWeaklyPrefer p B.val J := (eliminatedRotations_subset_iff hopt B.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  have hm' : p.manRank m (B.val m) < p.manRank m (A.val m) := (Finset.mem_filter.mp hm).2
  obtain ⟨s, hs, hmove, _⟩ := exists_diff_label_moving_of_rank_lt hopt B.property hJ hBJ
    (hm'.trans_le (hAJ m))
  rw [hIJ] at hs
  have hmem : s ∈ eliminatedRotations p μ₀ A.val \ eliminatedRotations p μ₀ B.val :=
    ⟨hs.1.resolve_right hs.2, hs.2⟩
  exact Finset.mem_biUnion.mpr
    ⟨s, by simpa only [← Finset.mem_coe, R.coe_shortOrientationLabels] using hmem,
      Equiv.Perm.mem_support.mpr hmove⟩

/-- The actual number of moved men in the short orientation is at most `K`. -/
theorem card_shortOrientationMen_le (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen.card ≤ K := by
  classical
  exact (Finset.card_le_card R.shortOrientationMen_subset).trans
    (Finset.card_biUnion_le.trans R.sum_rotationLength_shortOrientationLabels_le)

/-- Each man moved by the earlier pivot has a worse partner in the later matching. -/
theorem earlierPivot_support_subset_longOrientationMen (R : ResidualPivotPair hopt K) :
    R.early.1.val.val.cycle.support ⊆ R.longOrientationMen := by
  intro m hm
  have hmove := Equiv.Perm.mem_support.mp hm
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  have hE : R.early.1.val.IsExposedAt A.val := R.toggledEarly.2.pivot_exposed
  have hB : R.early.1.val ∈ eliminatedRotations p μ₀ B.val :=
    (Rotation.lt_iff_before_exposure hopt R.pivot_lt.ne).mp R.pivot_lt
      _ B.property R.late.2.pivot_exposed.1 R.late.2.pivot_exposed.2
  have hnew := rotationLabelNewPartner_eq (μ := A.val) hmove
  rw [hE.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt B.property hmove hnew).mp hB
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (hE.1.manRank_lt_eliminate_of_moved hmove).trans_le hle⟩

/-- The actual long orientation contains at least as many men as the earlier pivot. -/
theorem rotationLength_early_le_card_longOrientationMen (R : ResidualPivotPair hopt K) :
    rotationLength R.early.1.val ≤ R.longOrientationMen.card :=
  Finset.card_le_card R.earlierPivot_support_subset_longOrientationMen

private theorem exists_rank_max_and_eliminated_union {A B : Matching n}
    (hopt : IsManOptimal p μ₀) (hA : IsStable p A) (hB : IsStable p B) :
    ∃ J, IsStable p J ∧ (∀ m, p.manRank m (J m) =
      max (p.manRank m (A m)) (p.manRank m (B m))) ∧
      eliminatedRotations p μ₀ J =
        eliminatedRotations p μ₀ A ∪ eliminatedRotations p μ₀ B := by
  obtain ⟨J, hJ, hIJ⟩ := exists_eliminatedRotations_union hopt hA hB
  obtain ⟨L, hL, hLrank⟩ := exists_stable_manRank_max hA hB
  have hAL : MenWeaklyPrefer p A L := fun m ↦ by rw [hLrank]; exact le_max_left _ _
  have hBL : MenWeaklyPrefer p B L := fun m ↦ by rw [hLrank]; exact le_max_right _ _
  have hJL : MenWeaklyPrefer p J L := (eliminatedRotations_subset_iff hopt hJ hL).mp
    (by
      rw [hIJ]
      exact Set.union_subset ((eliminatedRotations_subset_iff hopt hA hL).mpr hAL)
        ((eliminatedRotations_subset_iff hopt hB hL).mpr hBL))
  have hAJ : MenWeaklyPrefer p A J := (eliminatedRotations_subset_iff hopt hA hJ).mp
    (by rw [hIJ]; exact Set.subset_union_left)
  have hBJ : MenWeaklyPrefer p B J := (eliminatedRotations_subset_iff hopt hB hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  refine ⟨J, hJ, fun m ↦ le_antisymm ?_ (max_le (hAJ m) (hBJ m)), hIJ⟩
  simpa only [hLrank] using hJL m

/-- Read each earlier partner's man in the later matching. -/
noncomputable def relativePermutation (R : ResidualPivotPair hopt K) : Equiv.Perm (Fin n) :=
  R.toggledEarly.2.matching.val.trans R.late.2.matching.val.symm

/-- The relative permutation follows each short label's cycle on its support. -/
theorem relativePermutation_apply_of_mem_shortLabel (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ R.shortOrientationLabels)
    {m : Fin n} (hm : s.val.cycle m ≠ m) :
    R.relativePermutation m = s.val.cycle m := by
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  have hsD : s ∈ eliminatedRotations p μ₀ A.val \ eliminatedRotations p μ₀ B.val :=
    R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
  have hE : s.IsExposedAt B.val := R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hsD
  obtain ⟨J, hJ, hJrank, hIJ⟩ := exists_rank_max_and_eliminated_union hopt A.property B.property
  have hBJ : MenWeaklyPrefer p B.val J := (eliminatedRotations_subset_iff hopt B.property hJ).mp
    (by rw [hIJ]; exact Set.subset_union_right)
  have hJmem : s ∈ eliminatedRotations p μ₀ J := hIJ ▸ Or.inl hsD.1
  have hnew := rotationLabelNewPartner_eq (μ := B.val) hm
  rw [hE.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt hJ hm hnew).mp hJmem
  have hlt := (hE.1.manRank_lt_eliminate_of_moved hm).trans_le hle
  obtain ⟨t, ht, htm, htn⟩ := exists_diff_label_moving_of_rank_lt hopt B.property hJ hBJ hlt
  rw [hIJ] at ht
  have hEt : t.IsExposedAt B.val :=
    R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late ⟨ht.1.resolve_right ht.2, ht.2⟩
  have heq : t = s := by
    by_contra hts
    have hcycles : s.val.cycle ≠ t.val.cycle := fun he ↦ hts (Subtype.ext
      (hEt.2.symm.trans ((congrArg (rotationLabel B.val) he).symm.trans hE.2)))
    exact htm (hE.1.disjoint_moved hEt.1 hcycles m hm)
  rw [heq] at htn
  have hJpartner : eliminateRotation B.val s.val.cycle m = J m :=
    Option.some.inj (hnew.symm.trans htn)
  rw [hJrank] at hlt
  have hAgt : p.manRank m (B.val m) < p.manRank m (A.val m) :=
    (lt_max_iff.mp hlt).resolve_right (lt_irrefl _)
  have hApartner : A.val m = J m := (p.manRank m).injective (by
    rw [hJrank, max_eq_left hAgt.le])
  change B.val.symm (A.val m) = _
  rw [hApartner, ← hJpartner, eliminateRotation_apply, Equiv.symm_apply_apply]

/-- Each short label is an actual cycle factor of the relative permutation. -/
theorem cycle_mem_relativePermutation_cycleFactors (R : ResidualPivotPair hopt K)
    {s : Rotation p μ₀} (hs : s ∈ R.shortOrientationLabels) :
    s.val.cycle ∈ R.relativePermutation.cycleFactorsFinset := by
  have hsD : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
      eliminatedRotations p μ₀ R.late.2.matching.val :=
    R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
  have hE := R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hsD
  exact Equiv.Perm.mem_cycleFactorsFinset_iff.mpr ⟨hE.1.isCycle, fun _ hm ↦
    (R.relativePermutation_apply_of_mem_shortLabel hs (Equiv.Perm.mem_support.mp hm)).symm⟩

/-- A cycle factor moving a man in the short orientation is one of the short exposed labels. -/
theorem exists_shortLabel_of_cycleFactor (R : ResidualPivotPair hopt K)
    {c : Equiv.Perm (Fin n)} (hc : c ∈ R.relativePermutation.cycleFactorsFinset)
    {m : Fin n} (hm : m ∈ c.support) (hmshort : m ∈ R.shortOrientationMen) :
    ∃ s ∈ R.shortOrientationLabels, s.val.cycle = c := by
  classical
  obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.mp (R.shortOrientationMen_subset hmshort)
  exact ⟨s, hs, (Equiv.Perm.cycle_is_cycleOf hms
    (R.cycle_mem_relativePermutation_cycleFactors hs)).trans
      (Equiv.Perm.cycle_is_cycleOf hm hc).symm⟩

/-- The one bit records whether the shared label was present before filtering. -/
noncomputable def toggleBit (R : ResidualPivotPair hopt K) : Bool := by
  classical
  exact decide (R.sharedLabel ∈ R.early.2.removedLabels)

private theorem eq_of_toggled_codes_and_bit {R S : ResidualPivotPair hopt K}
    (hA : R.toggledEarly = S.toggledEarly) (hB : R.late = S.late)
    (hbit : R.toggleBit = S.toggleBit) : R = S := by
  classical
  rcases R with ⟨⟨a, D⟩, L, hlt, hshared⟩
  rcases S with ⟨⟨b, E⟩, L', hlt', hshared'⟩
  have hab : a = b := congrArg Sigma.fst hA
  subst b
  change L = L' at hB
  subst L'
  let γ := Classical.choose hshared
  change (⟨a, D.eraseRemovedLabel γ⟩ : PivotCode hopt K) =
    ⟨a, E.eraseRemovedLabel γ⟩ at hA
  change decide (γ ∈ D.removedLabels) = decide (γ ∈ E.removedLabels) at hbit
  have hdec : γ ∈ D.removedLabels ↔ γ ∈ E.removedLabels := by
    simpa using hbit
  have hDE : D = E := PivotDecoration.eq_of_eraseRemovedLabel_eq γ
    (eq_of_heq (Sigma.mk.inj_iff.mp hA).2) hdec
  subst E
  rfl

/-- An extra subset-closed decoration filter is preserved by the toggle. -/
theorem toggledEarly_preserves (R : ResidualPivotPair hopt K)
    (F : ∀ a : LongPivot p μ₀ K, PivotDecoration hopt K a.val → Prop)
    (hF : ∀ (a : LongPivot p μ₀ K) (D E : PivotDecoration hopt K a.val),
      E.removed ⊆ D.removed → F a D → F a E)
    (h : F R.early.1 R.early.2) : F R.toggledEarly.1 R.toggledEarly.2 :=
  hF _ _ _ (R.early.2.eraseRemovedLabel_subset R.sharedLabel) h

/-- The original residual pair is determined by the incomparable image and one bit. -/
noncomputable def toggleEmbedding (hopt : IsManOptimal p μ₀) (K : ℕ) :
    ResidualPivotPair hopt K ↪ IncomparableStableMatchingPair p μ₀ × Bool :=
  ⟨fun R ↦ (R.toggleImage, R.toggleBit), by
    intro R S h
    have hpair := congrArg (fun z : IncomparableStableMatchingPair p μ₀ × Bool ↦ z.1.val) h
    have hA : R.toggledEarly = S.toggledEarly :=
      (pivotDecorationEmbedding hopt K).injective (congrArg Prod.fst hpair)
    have hB : R.late = S.late :=
      (pivotDecorationEmbedding hopt K).injective (congrArg Prod.snd hpair)
    exact eq_of_toggled_codes_and_bit hA hB (congrArg Prod.snd h)⟩

instance (hopt : IsManOptimal p μ₀) (K : ℕ) : Finite (ResidualPivotPair hopt K) :=
  Finite.of_injective (toggleEmbedding hopt K) (toggleEmbedding hopt K).injective

/-- Restrict the encoding to any filtered source and a predicate on the image pairs. -/
noncomputable def toggleEmbedding_restrict
    {P : ResidualPivotPair hopt K → Prop} {Q : IncomparableStableMatchingPair p μ₀ → Prop}
    (hQ : ∀ R, P R → Q R.toggleImage) :
    {R // P R} ↪ {MN // Q MN} × Bool :=
  ⟨fun R ↦ (⟨R.val.toggleImage, hQ R.val R.property⟩, R.val.toggleBit),
    fun _ _ h ↦ Subtype.ext ((toggleEmbedding hopt K).injective
      (congrArg (fun z : {MN // Q MN} × Bool ↦ (z.1.val, z.2)) h))⟩

/-- The two-to-one bound is retained for restrictions that hold on all toggle images. -/
theorem card_le_twice_incomparable_restrict
    {P : ResidualPivotPair hopt K → Prop} {Q : IncomparableStableMatchingPair p μ₀ → Prop}
    (hQ : ∀ R, P R → Q R.toggleImage) :
    Nat.card {R // P R} ≤ 2 * Nat.card {MN // Q MN} := by
  have h := Nat.card_le_card_of_injective (toggleEmbedding_restrict hQ)
    (toggleEmbedding_restrict hQ).injective
  simpa [Nat.card_prod, mul_comm] using h

/-- The total number of residual pairs is at most twice the incomparable-pair count. -/
theorem card_le_twice_incomparable (hopt : IsManOptimal p μ₀) (K : ℕ) :
    Nat.card (ResidualPivotPair hopt K) ≤
      2 * Nat.card (IncomparableStableMatchingPair p μ₀) := by
  have h := Nat.card_le_card_of_injective (toggleEmbedding hopt K)
    (toggleEmbedding hopt K).injective
  simpa [Nat.card_prod, mul_comm] using h

end ResidualPivotPair

end LennonPittelFormalization

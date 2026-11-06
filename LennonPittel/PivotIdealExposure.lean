module

public import LennonPittel.UndoMaximalSubset

/-!
# Exposed rotations after undoing a subset at a singleton anchor

Deleting maximal elements of an ideal makes all deleted elements minimal outside
the smaller ideal. An old outside minimum survives exactly when none of its
strict predecessors was deleted.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

/-- Deleting maximal elements exposes exactly those elements and the surviving old minima. -/
theorem minimal_compl_diff_maximal_iff {α : Type*} [PartialOrder α]
    (I : LowerSet α) (D : Set α) (hD : ∀ t ∈ D, Maximal (· ∈ I) t) (s : α) :
    Minimal (· ∉ (I : Set α) \ D) s ↔
      s ∈ D ∨ (Minimal (· ∉ I) s ∧ ∀ t ∈ D, ¬ t < s) := by
  simp only [minimal_iff_forall_lt, not_not]
  constructor
  · rintro ⟨hs, hpred⟩
    by_cases hsD : s ∈ D
    · exact Or.inl hsD
    · exact Or.inr ⟨⟨fun hsI ↦ hs ⟨hsI, hsD⟩, fun _ hts ↦ (hpred hts).1⟩,
        fun _ htD hts ↦ (hpred hts).2 htD⟩
  · rintro (hsD | ⟨⟨hsI, hpred⟩, hcompat⟩)
    · have hsI := (hD s hsD).prop
      refine ⟨fun h ↦ h.2 hsD, fun t hts ↦ ⟨I.lower hts.le hsI, ?_⟩⟩
      exact fun htD ↦ hts.not_ge ((hD t htD).2 hsI hts.le)
    · exact ⟨fun h ↦ hsI h.1, fun t hts ↦ ⟨hpred hts, fun htD ↦ hcompat t htD hts⟩⟩

variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}

/-- At the endpoint of an undo subset, the exposed labels are the removed labels and
the originally exposed labels with no removed strict prerequisite. -/
theorem isExposedAt_undoMaximalSubsetEmbedding_iff
    (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (D : Set (MaximalEliminatedRotation p μ₀ μ)) (s : Rotation p μ₀) :
    s.IsExposedAt (undoMaximalSubsetEmbedding hopt hμ D).val ↔
      s ∈ Subtype.val '' D ∨ (s.IsExposedAt μ ∧ ∀ t ∈ Subtype.val '' D, ¬ t < s) := by
  rw [Rotation.isExposedAt_iff_minimal hopt (undoMaximalSubsetEmbedding hopt hμ D).property,
    Rotation.isExposedAt_iff_minimal hopt hμ,
    eliminatedRotations_undoMaximalSubsetEmbedding]
  let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨μ, hμ⟩
  apply minimal_compl_diff_maximal_iff I
  rintro _ ⟨t, _, rfl⟩
  exact t.property

/-- A singleton pivot survives undoing a subset exactly when no strict prerequisite
of the pivot is in that subset. -/
theorem pivot_isExposedAt_undo_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :
    r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      ∀ s ∈ Subtype.val '' D, ¬ s < r := by
  let A := singletonRotationAnchor hopt r
  have hA : r.IsExposedAt A.val := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  have hrI : r ∉ eliminatedRotations p μ₀ A.val :=
    ((Rotation.isExposedAt_iff_minimal hopt A.property r).mp hA).prop
  have hrD : r ∉ Subtype.val '' D := by
    rintro ⟨s, _, hs⟩
    exact hrI (hs ▸ s.property.prop)
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D r]
  exact ⟨fun h ↦ (h.resolve_left hrD).2, fun h ↦ Or.inr ⟨hA, h⟩⟩

/-- When the pivot survives, it and the removed labels form the exact exposed set. -/
theorem isExposedAt_undo_pivot_iff (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
    (hr : r.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val)
    (s : Rotation p μ₀) :
    s.IsExposedAt
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val ↔
      s = r ∨ s ∈ Subtype.val '' D := by
  let A := singletonRotationAnchor hopt r
  have hcompat := (pivot_isExposedAt_undo_iff hopt r D).mp hr
  rw [isExposedAt_undoMaximalSubsetEmbedding_iff hopt A.property D s,
    (eq_singletonRotationAnchor_iff hopt r A).mp rfl s]
  constructor
  · rintro (hsD | ⟨hsr, _⟩)
    · exact Or.inr hsD
    · exact Or.inl hsr
  · rintro (rfl | hsD)
    · exact Or.inr ⟨rfl, hcompat⟩
    · exact Or.inl hsD

end LennonPittelFormalization

module

public import LennonPittel.SingletonRotationAnchor

/-!
# Undoing a rotation in the rotation poset

A one-step stable predecessor removes exactly one realized rotation from the
eliminated set. Such a removal is possible exactly at a maximal element.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}

/-- A realized rotation is undoable at `ν` if a stable predecessor exposes
that label and eliminating it gives `ν`. -/
def Rotation.IsUndoableAt (r : Rotation p μ₀) (ν : Matching n) : Prop :=
  ∃ μ, IsStable p μ ∧ r.IsExposedAt μ ∧ eliminateRotation μ r.val.cycle = ν

/-- A forward elimination inserts just the exposed label into the eliminated ideal. -/
theorem Rotation.IsExposedAt.eliminatedRotations_eliminate
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) :
    eliminatedRotations p μ₀ (eliminateRotation μ r.val.cycle) =
      insert r (eliminatedRotations p μ₀ μ) := by
  obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
  have hstep : RotationSequence p μ [r.val.cycle] (eliminateRotation μ r.val.cycle) :=
    .cons hμ he.1 (.nil (he.1.isStable_eliminate hμ))
  ext s
  rw [(hrs.append hstep).mem_eliminatedRotations_iff, hrs.rotationLabels_append,
    List.mem_append, ← hrs.mem_eliminatedRotations_iff]
  simp only [rotationLabels, List.mem_singleton, he.2, Set.mem_insert_iff]
  constructor
  · rintro (hs | hs)
    · exact Or.inr hs
    · exact Or.inl (Subtype.ext hs)
  · rintro (hs | hs)
    · exact Or.inr (congrArg (fun x : Rotation p μ₀ ↦ x.val) hs)
    · exact Or.inl hs

/-- The stable predecessor has removed exactly the undone label. -/
theorem Rotation.IsExposedAt.eliminatedRotations_eq_diff
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (hstep : eliminateRotation μ r.val.cycle = ν) :
    eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ ν \ {r} := by
  have hnot := ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop
  rw [← hstep, he.eliminatedRotations_eliminate hopt hμ]
  ext s
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact ⟨fun hs ↦ ⟨Or.inr hs, fun h ↦ hnot (h ▸ hs)⟩,
    fun ⟨hs, hne⟩ ↦ hs.resolve_left hne⟩

/-- An undoable rotation is exactly a maximal element of the eliminated ideal. -/
theorem Rotation.isUndoableAt_iff_maximal (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (r : Rotation p μ₀) :
    r.IsUndoableAt ν ↔ Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r := by
  constructor
  · rintro ⟨μ, hμ, he, rfl⟩
    rw [he.eliminatedRotations_eliminate hopt hμ, maximal_iff_forall_gt]
    refine ⟨Set.mem_insert _ _, fun s hrs hs ↦ ?_⟩
    have hold := (Set.mem_insert_iff.mp hs).resolve_left hrs.ne.symm
    exact ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop (hrs.le _ hold)
  · intro hmax
    let I := stableMatchingToRotationIdeal (μ₀ := μ₀) ⟨ν, hν⟩
    let J : LowerSet (Rotation p μ₀) :=
      ⟨(I : Set (Rotation p μ₀)) \ {r}, by
        intro b a hab hb
        refine ⟨I.lower hab hb.1, ?_⟩
        intro ha
        have har : a = r := Set.mem_singleton_iff.mp ha
        subst a
        exact hb.2 (Set.mem_singleton_iff.mpr ((hmax.2 hb.1 hab).antisymm hab))⟩
    let e := stableMatchingEquivRotationIdeals hopt
    let μ := e.symm J
    have hμI : eliminatedRotations p μ₀ μ.val = (J : Set (Rotation p μ₀)) :=
      congrArg (fun K : LowerSet (Rotation p μ₀) ↦ (K : Set (Rotation p μ₀)))
        (e.apply_symm_apply J)
    have he : r.IsExposedAt μ.val := by
      rw [Rotation.isExposedAt_iff_minimal hopt μ.property, minimal_iff_forall_lt, hμI]
      refine ⟨fun h ↦ h.2 (Set.mem_singleton r), fun s hsr hn ↦ hn ?_⟩
      exact ⟨I.lower hsr.le hmax.prop, fun h ↦ hsr.ne (Set.mem_singleton_iff.mp h)⟩
    have hsets : eliminatedRotations p μ₀ (eliminateRotation μ.val r.val.cycle) =
        eliminatedRotations p μ₀ ν := by
      rw [he.eliminatedRotations_eliminate hopt μ.property, hμI]
      change insert r ((I : Set (Rotation p μ₀)) \ {r}) = (I : Set (Rotation p μ₀))
      rw [Set.insert_sdiff_singleton]
      exact Set.insert_eq_of_mem (show r ∈ I from hmax.prop)
    have hstable := he.1.isStable_eliminate μ.property
    have hmatching : (⟨eliminateRotation μ.val r.val.cycle, hstable⟩ :
        {τ : Matching n // IsStable p τ}) = ⟨ν, hν⟩ :=
      (stableMatchingToRotationIdeal_bijective hopt).1 (LowerSet.ext hsets)
    exact ⟨μ.val, μ.property, he, congrArg Subtype.val hmatching⟩

end LennonPittelFormalization

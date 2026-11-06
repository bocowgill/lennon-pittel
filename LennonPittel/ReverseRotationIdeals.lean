module

public import LennonPittel.ReverseSuccessorRotation
public import LennonPittel.UndoableRotations

/-!
# Reverse successor cycles and maximal eliminated rotations

The reverse successor graph uses the women as the proposing side. Its exposed
cycles correspond bijectively to the maximal elements of the eliminated ideal.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ : Equiv.Perm (Fin n)}

/-- A reverse cycle uses each woman's first worse man who prefers her to his current partner. -/
def IsReverseExposedRotation (p : Profile n) (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Prop :=
  IsExposedRotation (swapProfile p) ν.symm σ

/-- Apply the reverse cycle on the women's side, then return to a men-to-women matching. -/
def undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) : Matching n :=
  (eliminateRotation ν.symm σ).symm

/-- Undoing a reverse successor cycle preserves stability. -/
theorem IsReverseExposedRotation.undo_stable
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsStable p (undoReverseRotation ν σ) := by
  apply isStable_swapProfile_iff.mp
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isStable_eliminate
      (isStable_swapProfile_iff.mpr hν)

/-- The corresponding forward cycle is exposed at the predecessor. -/
theorem IsReverseExposedRotation.forward_exposed
    (hσ : IsReverseExposedRotation p ν σ) (hν : IsStable p ν) :
    IsExposedRotation p (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) := by
  simpa only [undoReverseRotation, swapProfile_swapProfile] using
    (show IsExposedRotation (swapProfile p) ν.symm σ from hσ).isExposedRotation_swap_eliminate
      (isStable_swapProfile_iff.mpr hν)

/-- Forward elimination after undoing returns to the original matching. -/
theorem eliminateRotation_undoReverseRotation (ν : Matching n) (σ : Equiv.Perm (Fin n)) :
    eliminateRotation (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) = ν := by
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    eliminateRotation_swap_reverseCycle ν.symm σ

/-- Read the realized rotation label at the predecessor of a reverse cycle. -/
def reverseExposedRotationLabel (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) : Rotation p μ₀ :=
  rotationOfExposed hopt (σ.property.undo_stable hν) (σ.property.forward_exposed hν)

/-- Undoing a concrete reverse cycle deletes exactly its realized rotation label. -/
theorem eliminatedRotations_undoReverseRotation (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
    eliminatedRotations p μ₀ (undoReverseRotation ν σ.val) =
      eliminatedRotations p μ₀ ν \ {reverseExposedRotationLabel hopt hν σ} :=
  (show (reverseExposedRotationLabel hopt hν σ).IsExposedAt (undoReverseRotation ν σ.val)
    from ⟨σ.property.forward_exposed hν, rfl⟩).eliminatedRotations_eq_diff
      hopt (σ.property.undo_stable hν) (eliminateRotation_undoReverseRotation ν σ.val)

/-- The label read from a reverse successor cycle is maximal in the eliminated ideal. -/
theorem reverseExposedRotationLabel_maximal (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
    Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν)
      (reverseExposedRotationLabel hopt hν σ) :=
  (Rotation.isUndoableAt_iff_maximal hopt hν _).mp
    ⟨undoReverseRotation ν σ.val, σ.property.undo_stable hν,
      ⟨σ.property.forward_exposed hν, rfl⟩, eliminateRotation_undoReverseRotation ν σ.val⟩

/-- Reverse successor cycles are in bijection with the maximal eliminated labels. -/
noncomputable def reverseExposedRotationEquivMaximal (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) :
    {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ} ≃
      {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} := by
  let f (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) :
      {r : Rotation p μ₀ // Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} :=
    ⟨reverseExposedRotationLabel hopt hν σ, reverseExposedRotationLabel_maximal hopt hν σ⟩
  apply Equiv.ofBijective f
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro w
    have he := congrArg
      (fun r : {r : Rotation p μ₀ //
          Maximal (fun s ↦ s ∈ eliminatedRotations p μ₀ ν) r} ↦
        r.val.val.cycle (ν.symm w)) h
    change reverseRotationCycle ν.symm σ.val (ν.symm w) =
      reverseRotationCycle ν.symm τ.val (ν.symm w) at he
    exact ν.symm.injective (by simpa [reverseRotationCycle] using he)
  · rintro ⟨r, hr⟩
    obtain ⟨μ, hμ, he, hstep⟩ := (r.isUndoableAt_iff_maximal hopt hν).mpr hr
    let σ := reverseRotationCycle μ r.val.cycle
    have hσ : IsReverseExposedRotation p ν σ := by
      rw [← hstep]
      exact he.1.isExposedRotation_swap_eliminate hμ
    have hund : undoReverseRotation ν σ = μ := by
      rw [← hstep, undoReverseRotation, eliminateRotation_swap_reverseCycle, Equiv.symm_symm]
    have hcycle : reverseRotationCycle ν.symm σ = r.val.cycle := by
      rw [← hstep]
      exact reverseRotationCycle_swap_reverseCycle μ r.val.cycle
    refine ⟨⟨σ, hσ⟩, Subtype.ext (Subtype.ext ?_)⟩
    change rotationLabel (undoReverseRotation ν σ) (reverseRotationCycle ν.symm σ) = r.val
    rw [hund, hcycle]
    exact he.2

end LennonPittelFormalization

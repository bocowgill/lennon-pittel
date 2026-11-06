module

public import LennonPittel.ReverseRotationIdeals

/-!
# Persistence of exposed reverse rotations

Undoing one reverse cycle leaves every other initially exposed reverse cycle
exposed with its original realized label.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ ν : Matching n} {σ τ : Equiv.Perm (Fin n)}

/-- Undoing a distinct reverse cycle preserves exposure of this same cycle. -/
theorem IsReverseExposedRotation.persist_undo (hτ : IsReverseExposedRotation p ν τ)
    (hσ : IsReverseExposedRotation p ν σ) (hne : τ ≠ σ) :
    IsReverseExposedRotation p (undoReverseRotation ν σ) τ := by
  simpa only [IsReverseExposedRotation, undoReverseRotation, Equiv.symm_symm] using
    (show IsExposedRotation (swapProfile p) ν.symm τ from hτ).persist_eliminate hσ hne

/-- Undoing two distinct exposed reverse cycles in either order gives the same matching. -/
theorem IsReverseExposedRotation.undo_comm (hσ : IsReverseExposedRotation p ν σ)
    (hτ : IsReverseExposedRotation p ν τ) (hne : σ ≠ τ) :
    undoReverseRotation (undoReverseRotation ν σ) τ =
      undoReverseRotation (undoReverseRotation ν τ) σ := by
  simpa only [undoReverseRotation, Equiv.symm_symm] using
    congrArg (fun μ : Matching n ↦ μ.symm)
      ((show IsExposedRotation (swapProfile p) ν.symm σ from hσ).eliminate_comm hτ hne)

/-- A reverse cycle that persists after undoing another still undoes the same label. -/
theorem reverseExposedRotationLabel_persist_undo (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (hτ : IsReverseExposedRotation p ν τ)
    (hσ : IsReverseExposedRotation p ν σ) (hne : τ ≠ σ) :
    reverseExposedRotationLabel hopt (hσ.undo_stable hν) ⟨τ, hτ.persist_undo hσ hne⟩ =
      reverseExposedRotationLabel hopt hν ⟨τ, hτ⟩ := by
  let a := reverseExposedRotationLabel hopt hν ⟨σ, hσ⟩
  let b := reverseExposedRotationLabel hopt hν ⟨τ, hτ⟩
  let b' := reverseExposedRotationLabel hopt (hσ.undo_stable hν)
    ⟨τ, hτ.persist_undo hσ hne⟩
  have hba : b ≠ a := fun he ↦ hne
    (congrArg Subtype.val ((reverseExposedRotationEquivMaximal hopt hν).injective
      (Subtype.ext he)))
  have hb := (reverseExposedRotationLabel_maximal hopt hν ⟨τ, hτ⟩).prop
  change b' = b
  by_contra hne'
  -- If the second deletion had a different label, the first order would retain b.
  have hbmem :
      b ∈ eliminatedRotations p μ₀ (undoReverseRotation (undoReverseRotation ν σ) τ) := by
    rw [eliminatedRotations_undoReverseRotation hopt (hσ.undo_stable hν)
      ⟨τ, hτ.persist_undo hσ hne⟩,
      eliminatedRotations_undoReverseRotation hopt hν ⟨σ, hσ⟩]
    exact ⟨⟨hb, fun he ↦ hba (Set.mem_singleton_iff.mp he)⟩,
      fun he ↦ hne' (Set.mem_singleton_iff.mp he).symm⟩
  rw [hσ.undo_comm hτ hne.symm,
    eliminatedRotations_undoReverseRotation hopt (hτ.undo_stable hν)
      ⟨σ, hσ.persist_undo hτ hne.symm⟩,
    eliminatedRotations_undoReverseRotation hopt hν ⟨τ, hτ⟩] at hbmem
  exact hbmem.1.2 (Set.mem_singleton _)

end LennonPittelFormalization

module

public import LennonPittel.RotationDiamond
public import LennonPittel.RotationLabels
public import Mathlib.Data.List.Perm.Basic

/-!
# Path independence of rotation elimination

Two paths of exposed rotations with common endpoints eliminate the same labeled rotations.
-/

@[expose] public section

open StableMarriage
namespace LennonPittelFormalization
variable {n : ℕ} {p : Profile n}

/-- If a participant's partner must change, the exposed rotation can be moved to the
front of the path without changing its rotation labels. -/
theorem RotationSequence.pull_rotation_to_front {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (hpath : RotationSequence p μ rs ν)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) (hend : μ m ≠ ν m) :
    ∃ ts, RotationSequence p (eliminateRotation μ ρ) ts ν ∧
      (rotationLabels μ rs).Perm
        (rotationLabel μ ρ :: rotationLabels (eliminateRotation μ ρ) ts) := by
  classical
  induction hpath generalizing ρ with
  | nil _ => exact (hend rfl).elim
  | @cons μ ν σ rs hμ hσ htail ih =>
    by_cases h : ρ = σ
    · subst σ
      exact ⟨rs, htail, List.Perm.refl _⟩
    · have hend' : eliminateRotation μ σ m ≠ ν m := by
        simpa only [eliminateRotation_apply, hρ.disjoint_moved hσ h m hm] using hend
      obtain ⟨ts, hts, hp⟩ := ih (hρ.persist_eliminate hσ h) hm hend'
      have hc := hρ.eliminate_comm hσ h
      have hts' : RotationSequence p (eliminateRotation (eliminateRotation μ ρ) σ) ts ν :=
        hc.symm ▸ hts
      have hlρ := rotationLabel_eliminate_of_fixes (μ := μ) (hρ.disjoint_moved hσ h)
      have hrev : σ ≠ ρ := Ne.symm h
      have hlσ := rotationLabel_eliminate_of_fixes (μ := μ) (hσ.disjoint_moved hρ hrev)
      refine ⟨σ :: ts, .cons (hρ.isStable_eliminate hμ) (hσ.persist_eliminate hρ hrev) hts', ?_⟩
      simp only [rotationLabels, hlσ, hc]
      rw [hlρ] at hp
      exact (List.Perm.cons _ hp).trans (List.Perm.swap _ _ _)

/-- Two rotation sequences with common endpoints have the same labels up to permutation. -/
theorem RotationSequence.rotationLabels_perm {μ ν : Matching n}
    {rs ss : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) (h' : RotationSequence p μ ss ν) :
    (rotationLabels μ rs).Perm (rotationLabels μ ss) := by
  induction h generalizing ss with
  | nil _ =>
    cases h' with
    | nil _ => exact List.Perm.refl _
    | cons _ hσ htail =>
      obtain ⟨m, hm, _⟩ := hσ.isCycle
      exact ((hσ.partner_ne_of_moved_of_rotationSequence htail hm) rfl).elim
  | cons _ hρ htail ih =>
    obtain ⟨m, hm, _⟩ := hρ.isCycle
    have hend := hρ.partner_ne_of_moved_of_rotationSequence htail hm
    obtain ⟨ts, hts, hp⟩ := h'.pull_rotation_to_front hρ hm hend
    exact (List.Perm.cons _ (ih hts)).trans hp.symm

/-- The set of labeled rotations eliminated by a path from a given matching. -/
def rotationSet (μ : Matching n) (rs : List (Equiv.Perm (Fin n))) : Set (RotationLabel n) :=
  {r | r ∈ rotationLabels μ rs}

/-- The eliminated rotation set depends only on the start and endpoint. -/
theorem RotationSequence.rotationSet_eq {μ ν : Matching n}
    {rs ss : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) (h' : RotationSequence p μ ss ν) :
    rotationSet μ rs = rotationSet μ ss :=
  Set.ext fun _ ↦ (h.rotationLabels_perm h').mem_iff

/-- Two paths from a man-optimal matching to the same stable target eliminate the same rotations. -/
theorem rotationSet_eq_of_manOptimal {μ₀ μ₁ ν : Matching n}
    {rs ss : List (Equiv.Perm (Fin n))} (h₀ : IsManOptimal p μ₀) (h₁ : IsManOptimal p μ₁)
    (h : RotationSequence p μ₀ rs ν) (h' : RotationSequence p μ₁ ss ν) :
    rotationSet μ₀ rs = rotationSet μ₁ ss := by
  have hsame := h₀.eq h₁
  subst μ₁
  exact h.rotationSet_eq h'

end LennonPittelFormalization

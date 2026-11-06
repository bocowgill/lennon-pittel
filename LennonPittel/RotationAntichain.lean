module

public import LennonPittel.RotationIdeals
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Data.Fintype.Powerset

/-!
# Antichains of rotations give exponentially many stable matchings

The lower closure of a subset of an antichain recovers that subset when
restricted to the antichain. The rotation-ideal equivalence then turns
these distinct lower sets into distinct stable matchings.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

section Preorder

variable {α : Type*} [Preorder α] {A : Set α}

/-- The lower closure of a subset of an antichain adds no other members of that antichain. -/
theorem mem_lowerClosure_antichain_iff (hA : IsAntichain (· ≤ ·) A)
    (S : Set A) (a : A) :
    a.val ∈ lowerClosure (Subtype.val '' S) ↔ a ∈ S :=
  ⟨fun h ↦
    let ⟨_, ⟨b, hb, rfl⟩, hab⟩ := mem_lowerClosure.mp h
    (Subtype.ext (hA.eq a.property b.property hab)).symm ▸ hb,
    fun ha ↦ subset_lowerClosure ⟨a, ha, rfl⟩⟩

/-- Distinct subsets of an antichain generate distinct lower sets. -/
def antichainLowerSetEmbedding (hA : IsAntichain (· ≤ ·) A) : Set A ↪ LowerSet α :=
  let f (S : Set A) : LowerSet α := lowerClosure (Subtype.val '' S)
  ⟨f, fun {S T} h ↦ Set.ext fun a ↦
    calc
      a ∈ S ↔ a.val ∈ f S := (mem_lowerClosure_antichain_iff hA S a).symm
      _ ↔ a.val ∈ f T := by rw [h]
      _ ↔ a ∈ T := mem_lowerClosure_antichain_iff hA T a⟩

end Preorder

variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}

/-- Each subset of an antichain of rotations gives a distinct stable matching. -/
noncomputable def rotationAntichainStableMatchingEmbedding (hopt : IsManOptimal p μ₀)
    {A : Set (Rotation p μ₀)} (hA : IsAntichain (· ≤ ·) A) :
    Set A ↪ {ν : Matching n // IsStable p ν} :=
  (antichainLowerSetEmbedding hA).trans
    (stableMatchingEquivRotationIdeals hopt).symm.toEmbedding

/-- The resulting stable matching eliminates exactly the chosen rotations within the antichain. -/
theorem mem_eliminatedRotations_antichainStableMatching_iff (hopt : IsManOptimal p μ₀)
    {A : Set (Rotation p μ₀)} (hA : IsAntichain (· ≤ ·) A) (S : Set A) (a : A) :
    a.val ∈ eliminatedRotations p μ₀ (rotationAntichainStableMatchingEmbedding hopt hA S).val ↔
      a ∈ S := by
  change a.val ∈ stableMatchingEquivRotationIdeals hopt
    ((stableMatchingEquivRotationIdeals hopt).symm (antichainLowerSetEmbedding hA S)) ↔ a ∈ S
  rw [Equiv.apply_symm_apply]
  exact mem_lowerClosure_antichain_iff hA S a

/-- An antichain of `A.card` rotations gives at least `2 ^ A.card` stable matchings. -/
theorem pow_card_rotationAntichain_le_numStableMatchings (hopt : IsManOptimal p μ₀)
    (A : Finset (Rotation p μ₀)) (hA : IsAntichain (· ≤ ·) (A : Set (Rotation p μ₀))) :
    2 ^ A.card ≤ numStableMatchings p := by
  classical
  let e := rotationAntichainStableMatchingEmbedding hopt hA
  calc
    2 ^ A.card = Nat.card (Set ↥A) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_coe]
    _ ≤ Nat.card {ν : Matching n // IsStable p ν} :=
      Nat.card_le_card_of_injective e e.injective
    _ = numStableMatchings p := Nat.card_eq_fintype_card

end LennonPittelFormalization

module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.SupClosed

/-!
# Lower sets of a finite set family

The prerequisite relation is determined by which elements occur together in the family.
Finite unions and nonempty finite intersections suffice to recover every lower set.
-/

@[expose] public section

namespace LennonPittelFormalization

/-- Every lower set for the prerequisite relation belongs to the family, if the family
contains the empty set, covers a finite ground set, and is closed under intersections and unions. -/
theorem mem_family_of_downward_closed {α : Type*} [Finite α] {F : Set (Set α)}
    (hempty : ∅ ∈ F)
    (hinter : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∩ B ∈ F)
    (hunion : ∀ ⦃A B⦄, A ∈ F → B ∈ F → A ∪ B ∈ F)
    (hcover : ∀ a : α, ∃ A ∈ F, a ∈ A) {I : Set α}
    (hdown : ∀ ⦃a b : α⦄, (∀ A ∈ F, b ∈ A → a ∈ A) → b ∈ I → a ∈ I) :
    I ∈ F := by
  -- The prerequisites of b are the intersection of all family members containing b.
  let P (b : α) : Set α := ⋂₀ {A : Set α | A ∈ F ∧ b ∈ A}
  have hInf : InfClosed F := fun _ hA _ hB ↦ hinter hA hB
  have hP (b : α) : P b ∈ F := by
    obtain ⟨A, hA, hbA⟩ := hcover b
    change sInf {A : Set α | A ∈ F ∧ b ∈ A} ∈ F
    exact hInf.sInf_mem_of_nonempty (Set.toFinite _) ⟨A, hA, hbA⟩ fun _ h ↦ h.1
  -- A lower set is the union of the prerequisite sets of its elements.
  have hEq : I = ⋃ b : I, P b := by
    ext a
    constructor
    · intro ha
      exact Set.mem_iUnion_of_mem ⟨a, ha⟩ (Set.mem_sInter.mpr fun _ h ↦ h.2)
    · intro ha
      obtain ⟨b, hab⟩ := Set.mem_iUnion.mp ha
      exact hdown (fun A hA hb ↦ Set.mem_sInter.mp hab A ⟨hA, hb⟩) b.property
  have hSup : SupClosed F := fun _ hA _ hB ↦ hunion hA hB
  rw [hEq]
  exact hSup.iSup_mem hempty fun b : I ↦ hP b

end LennonPittelFormalization

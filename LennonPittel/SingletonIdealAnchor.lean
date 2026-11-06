module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Singleton anchors in finite lower-set lattices

The complement of the principal upper set of an element is the unique lower set whose
complement has that element as its only minimal element.
-/

@[expose] public section

namespace LennonPittelFormalization

variable {α : Type*} [PartialOrder α]

/-- The lower set omitting an element and every element above it. -/
def singletonAnchorIdeal (r : α) : LowerSet α :=
  ⟨(Set.Ici r)ᶜ, fun _ _ hst ht hrs ↦ ht (hrs.trans hst)⟩

/-- A rotation belongs to the anchor precisely when it is not above the pivot. -/
@[simp]
theorem mem_singletonAnchorIdeal {r s : α} :
    s ∈ singletonAnchorIdeal r ↔ ¬ r ≤ s :=
  Iff.rfl

/-- The singleton anchor is exactly the ideal with the specified unique minimal omitted element. -/
theorem lowerSet_eq_singletonAnchorIdeal_iff [Finite α] (I : LowerSet α) (r : α) :
    I = singletonAnchorIdeal r ↔ ∀ s : α, Minimal (fun t : α ↦ t ∉ I) s ↔ s = r :=
  ⟨fun h s ↦ h.symm ▸
    minimal_iff_eq (fun hr ↦ (mem_singletonAnchorIdeal.mp hr) le_rfl)
      (fun _ ht ↦ not_not.mp fun hrt ↦ ht (mem_singletonAnchorIdeal.mpr hrt)),
    fun h ↦ LowerSet.ext (Set.ext fun s ↦
      show s ∈ I ↔ ¬ r ≤ s from
      ⟨fun hs hrs ↦ ((h r).mpr rfl).prop (I.lower hrs hs),
        fun hrs ↦ Classical.byContradiction fun hs ↦
          -- Each omitted element lies above a minimal omitted element.
          let ⟨t, hts, ht⟩ := Finite.exists_le_minimal (p := fun t : α ↦ t ∉ I) hs
          hrs (by simpa only [(h t).mp ht] using hts)⟩)⟩

end LennonPittelFormalization

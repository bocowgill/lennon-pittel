module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Cycles in finite successor graphs

A finite nonempty set with a fixed-point-free successor map contains a directed cycle.
We view the cycle as a permutation of the ambient type, fixing everything off the cycle.
-/

@[expose] public section

namespace LennonPittelFormalization

open Function

private theorem periodicPt_of_repeat {α : Type*} {f : α → α} {x : α} {i j : ℕ}
    (hij : i < j) (heq : f^[i] x = f^[j] x) :
    f^[i] x ∈ periodicPts f :=
  mk_mem_periodicPts (Nat.sub_pos_of_lt hij)
    (show f^[j - i] (f^[i] x) = f^[i] x by
      rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, ← heq])

private theorem nonempty_periodicPts {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    (periodicPts f).Nonempty :=
  let x := Classical.choice (inferInstance : Nonempty α)
  have hrepeat : ∃ i j, f^[i] x = f^[j] x ∧ i ≠ j := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  let ⟨i, j, heq, hne⟩ := hrepeat
  (lt_or_gt_of_ne hne).elim
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq⟩)
    (fun h ↦ ⟨_, periodicPt_of_repeat h heq.symm⟩)

/-- A fixed-point-free map of a finite nonempty subset contains a cycle.
The returned permutation follows the map on its moved points, all of which lie in the subset. -/
theorem exists_cycle_permutation {α : Type*} [Finite α] {s : Set α} [Nonempty s]
    (f : s → s) (hnf : ∀ x, f x ≠ x) :
    ∃ ρ : Equiv.Perm α, ρ.IsCycle ∧
      ∀ a, ρ a ≠ a → ∃ ha : a ∈ s, ρ a = (f ⟨a, ha⟩).1 := by
  classical
  let ⟨a, ha⟩ := nonempty_periodicPts f
  let hbij := bijOn_periodicPts f
  let e : Equiv.Perm (periodicPts f) := Equiv.ofBijective _ hbij.bijective
  let τ : Equiv.Perm s := Equiv.Perm.ofSubtype e
  let σ : Equiv.Perm α := Equiv.Perm.ofSubtype τ
  have hτ (x : s) (hx : x ∈ periodicPts f) : τ x = f x :=
    Equiv.Perm.ofSubtype_apply_of_mem e hx
  have hσ (x : s) (hx : x ∈ periodicPts f) : σ x.1 = (f x).1 :=
    (Equiv.Perm.ofSubtype_apply_coe τ x).trans (congrArg Subtype.val (hτ x hx))
  have hmove : σ a.1 ≠ a.1 := fun h ↦ hnf a (Subtype.ext ((hσ a ha).symm.trans h))
  exact ⟨σ.cycleOf a.1, σ.isCycle_cycleOf hmove, fun x hne ↦
    have hsame : σ.SameCycle a.1 x := Classical.byContradiction fun h ↦
      hne (Equiv.Perm.cycleOf_apply_of_not_sameCycle h)
    have heq := hsame.cycleOf_apply
    have hσne : σ x ≠ x := fun h ↦ hne (heq.trans h)
    have hx : x ∈ s := Classical.byContradiction fun h ↦
      hσne (Equiv.Perm.ofSubtype_apply_of_not_mem τ h)
    have hper : (⟨x, hx⟩ : s) ∈ periodicPts f := Classical.byContradiction fun h ↦
      hσne <| (Equiv.Perm.ofSubtype_apply_of_mem τ hx).trans <|
        congrArg Subtype.val (Equiv.Perm.ofSubtype_apply_of_not_mem e h)
    ⟨hx, heq.trans (hσ ⟨x, hx⟩ hper)⟩⟩

end LennonPittelFormalization

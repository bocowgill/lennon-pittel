module

public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Counting cycles with prescribed support

Extending a permutation on a finite support by the identity preserves its cycle type.
Grouping by support then reduces sums over cycles of a fixed length to sums over subsets.
-/

@[expose] public section

open Equiv.Perm Finset
open scoped BigOperators Classical

namespace LennonPittelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem cycleType_ofSubtype_eq_iff {S : Finset ι} (τ : Equiv.Perm S) :
    τ.cycleType = {S.card} ↔ (ofSubtype τ).IsCycle ∧ (ofSubtype τ).support = S := by
  have htype : (ofSubtype τ).cycleType = τ.cycleType :=
    cycleType_extendDomain (α := ↥S) (p := fun i ↦ i ∈ S) (Equiv.refl _) (g := τ)
  rw [← htype]
  constructor
  · intro h
    have hc : (ofSubtype τ).IsCycle := card_cycleType_eq_one.mp (by rw [h]; rfl)
    have hs : (ofSubtype τ).support.card = S.card := by
      rw [← sum_cycleType, h, Multiset.sum_singleton]
    refine ⟨hc, eq_of_subset_of_card_le ?_ hs.ge⟩
    intro i hi
    by_contra hn
    exact (mem_support.mp hi) (ofSubtype_apply_of_not_mem τ hn)
  · rintro ⟨hc, hs⟩
    rw [hc.cycleType, hs]

/-- A prescribed support of size at least two admits exactly the cyclic orders of that support. -/
theorem card_cyclesWithSupport (S : Finset ι) (hS : 2 ≤ S.card) :
    (Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = S)).card =
      (S.card - 1).factorial := by
  let A := Finset.univ.filter (fun τ : Equiv.Perm S ↦ τ.cycleType = {S.card})
  have hcount : A.card = (S.card - 1).factorial := by
    have hcard : Fintype.card S = S.card := Fintype.card_coe S
    simpa only [A, hcard, Nat.choose_self, mul_one] using
      (card_of_cycleType_singleton (α := S) hS hcard.ge)
  rw [← hcount]
  symm
  refine Finset.card_bij (fun τ _ ↦ ofSubtype τ) ?_ ?_ ?_
  · intro τ hτ
    exact mem_filter.mpr ⟨mem_univ _, (cycleType_ofSubtype_eq_iff τ).mp (mem_filter.mp hτ).2⟩
  · intro τ₁ _ τ₂ _ h
    exact ofSubtype_injective h
  · intro σ hσ
    obtain ⟨hc, hs⟩ := (mem_filter.mp hσ).2
    have hInv := isInvariant_of_support_le (show σ.support ⊆ S from hs.le)
    let τ := σ.subtypePerm hInv
    have heq : ofSubtype τ = σ :=
      (ofSubtype_eq_iff hInv).mpr ⟨hs.le, fun _ ↦ rfl⟩
    refine ⟨τ, mem_filter.mpr ⟨mem_univ _, (cycleType_ofSubtype_eq_iff τ).mpr ?_⟩, heq⟩
    rw [heq]
    exact ⟨hc, hs⟩

/-- Sum a weight depending only on the support over all cycles of a given length. -/
theorem sum_cyclesWithLength_by_support (k : ℕ) (hk : 2 ≤ k) (F : Finset ι → ℝ) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support.card = k),
      F σ.support) =
      ((k - 1).factorial : ℝ) * ∑ S ∈ (Finset.univ : Finset ι).powersetCard k, F S := by
  let C := Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support.card = k)
  let P := (Finset.univ : Finset ι).powersetCard k
  have hm : ∀ σ ∈ C, σ.support ∈ P := fun σ hσ ↦
    mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hσ).2.2⟩
  change (∑ σ ∈ C, F σ.support) = ((k - 1).factorial : ℝ) * ∑ S ∈ P, F S
  rw [← sum_fiberwise_of_maps_to' hm F, mul_sum]
  refine sum_congr rfl fun S hS ↦ ?_
  have hcard : S.card = k := (mem_powersetCard.mp hS).2
  have hfiber :
      C.filter (fun σ ↦ σ.support = S) =
        Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = S) := by
    ext σ
    simp only [C, mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ hcard⟩, h.2⟩⟩
  rw [hfiber, sum_const, nsmul_eq_mul, card_cyclesWithSupport S (hcard.symm ▸ hk), hcard]

end LennonPittelFormalization

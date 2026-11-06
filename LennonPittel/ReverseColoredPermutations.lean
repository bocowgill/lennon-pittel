module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases

/-!
# Three-color cycle count on a fixed support

Coloring every nontrivial cycle of a permutation colors the points in its
support compatibly with that permutation. Color-preserving permutations on a
finite type inject into pairs consisting of their color-class sizes and one
unrestricted permutation.
-/

@[expose] public section

open scoped BigOperators

namespace LennonPittelFormalization

private def colorSize {α : Type*} [Fintype α] (c : α → Fin 3) (i : Fin 3) : ℕ :=
  Fintype.card {x // c x = i}

private theorem colorSize_sum {α : Type*} [Fintype α] (c : α → Fin 3) :
    ∑ i, colorSize c i = Fintype.card α := by
  simpa only [colorSize, Fintype.card_sigma] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv c)

private abbrev ColorShape (α : Type*) [Fintype α] :=
  Fin (Fintype.card α + 1) × Fin (Fintype.card α + 1)

private def colorShape {α : Type*} [Fintype α] (c : α → Fin 3) : ColorShape α :=
  (⟨colorSize c 0, Nat.lt_succ_of_le (Fintype.card_subtype_le (fun x ↦ c x = 0))⟩,
    ⟨colorSize c 1, Nat.lt_succ_of_le (Fintype.card_subtype_le (fun x ↦ c x = 1))⟩)

private theorem colorSize_eq_of_colorShape_eq {α : Type*} [Fintype α] {c d : α → Fin 3}
    (h : colorShape c = colorShape d) (i : Fin 3) : colorSize c i = colorSize d i := by
  have h₀ : colorSize c 0 = colorSize d 0 := congrArg (fun q : ColorShape α ↦ q.1.val) h
  have h₁ : colorSize c 1 = colorSize d 1 := congrArg (fun q : ColorShape α ↦ q.2.val) h
  have h₂ : colorSize c 2 = colorSize d 2 := by
    have hc := colorSize_sum c
    have hd := colorSize_sum d
    rw [Fin.sum_univ_three] at hc hd
    omega
  fin_cases i <;> assumption

private noncomputable def colorRelabel {α : Type*} [Fintype α] {c d : α → Fin 3}
    (h : colorShape c = colorShape d) : Equiv.Perm α :=
  Equiv.ofFiberEquiv fun i ↦ Fintype.equivOfCardEq (colorSize_eq_of_colorShape_eq h i)

private theorem colorRelabel_map {α : Type*} [Fintype α] {c d : α → Fin 3}
    (h : colorShape c = colorShape d) (a : α) : d (colorRelabel h a) = c a :=
  Equiv.ofFiberEquiv_map _ _

private abbrev ColorPreservingPerm (α : Type*) :=
  Σ c : α → Fin 3, {σ : Equiv.Perm α // ∀ a, c (σ a) = c a}

open scoped Classical in
/-- The class sizes and an unrestricted permutation encode a point coloring and a permutation
that preserves it. -/
private theorem card_colorPreservingPerm_le {α : Type*} [Fintype α] :
    Nat.card (ColorPreservingPerm α) ≤
      (Fintype.card α).factorial * (Fintype.card α + 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  let S := Set.range (colorShape (α := α))
  let shape (c : α → Fin 3) : S := ⟨colorShape c, ⟨c, rfl⟩⟩
  let rep (v : S) : α → Fin 3 := Classical.choose v.property
  have hrep (v : S) : colorShape (rep v) = v.val := Classical.choose_spec v.property
  let base (c : α → Fin 3) : Equiv.Perm α := colorRelabel (hrep (shape c))
  let encode (p : ColorPreservingPerm α) : S × Equiv.Perm α :=
    (shape p.1, (base p.1).trans p.2.val)
  have hencode (p : ColorPreservingPerm α) (a : α) :
      p.1 ((encode p).2 a) = rep (shape p.1) a :=
    (p.2.property _).trans (colorRelabel_map (hrep (shape p.1)) a)
  have hinj : Function.Injective encode := by
    rintro ⟨c, σ⟩ ⟨d, τ⟩ heq
    have hshape : shape c = shape d := congrArg Prod.fst heq
    have hperm := congrArg Prod.snd heq
    have hcd : c = d := by
      funext a
      obtain ⟨x, rfl⟩ := ((encode ⟨c, σ⟩).2).surjective a
      have hc := hencode ⟨c, σ⟩ x
      have hd := hencode ⟨d, τ⟩ x
      rw [hshape] at hc
      exact hc.trans (hd.symm.trans (congrArg (fun e : Equiv.Perm α ↦ d (e x)) hperm).symm)
    subst d
    have hστ : σ = τ := by
      apply Subtype.ext
      ext a
      obtain ⟨x, rfl⟩ := (base c).surjective a
      exact congrArg (fun e : Equiv.Perm α ↦ e x) hperm
    rw [hστ]
  calc
    _ ≤ Fintype.card (S × Equiv.Perm α) := Fintype.card_le_of_injective encode hinj
    _ ≤ _ := by
      rw [Fintype.card_prod, Fintype.card_perm, mul_comm, pow_two]
      apply Nat.mul_le_mul_left
      calc
        _ ≤ Fintype.card (ColorShape α) := Fintype.card_subtype_le _
        _ = _ := by simp only [ColorShape, Fintype.card_prod, Fintype.card_fin]

open scoped Classical in
/-- For a fixed support, the sum over permutations of the number of ways to
color their nontrivial cycles with three colors has a quadratic-factor bound. -/
theorem sum_three_pow_cycleFactorsFinset_support_le {n : ℕ} (s : Finset (Fin n)) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ ↦ σ.support = s),
      3 ^ σ.cycleFactorsFinset.card) ≤ s.card.factorial * (s.card + 1) ^ 2 := by
  let F := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ ↦ σ.support = s)
  have hsupport (σ : F) : σ.val.support = s := (Finset.mem_filter.mp σ.property).2
  let restrict (σ : F) : Equiv.Perm s :=
    σ.val.subtypePerm (Equiv.Perm.isInvariant_of_support_le (hsupport σ).le)
  have hrestrict : Function.Injective restrict := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ s
    · exact congrArg (fun e : Equiv.Perm s ↦ (e ⟨x, hx⟩ : Fin n)) h
    · have hσ : x ∉ σ.val.support := by rwa [hsupport σ]
      have hτ : x ∉ τ.val.support := by rwa [hsupport τ]
      exact (Equiv.Perm.notMem_support.mp hσ).trans (Equiv.Perm.notMem_support.mp hτ).symm
  let cycle (σ : F) (a : s) : σ.val.cycleFactorsFinset :=
    ⟨σ.val.cycleOf a, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (by
      rw [hsupport σ]
      exact a.property)⟩
  let A := Σ σ : F, σ.val.cycleFactorsFinset → Fin 3
  let f (p : A) : ColorPreservingPerm s :=
    ⟨p.2 ∘ cycle p.1, ⟨restrict p.1, fun a ↦
      congrArg p.2 (Subtype.ext (Equiv.Perm.cycleOf_self_apply p.1.val a))⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨σ, c⟩ ⟨τ, d⟩ heq
    have hστ : σ = τ := hrestrict (congrArg (fun p : ColorPreservingPerm s ↦ p.2.val) heq)
    subst τ
    suffices c = d by rw [this]
    funext ρ
    obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp ρ.property).1.nonempty_support
    have has : a ∈ s := (hsupport σ) ▸ Equiv.Perm.mem_cycleFactorsFinset_support_le ρ.property ha
    let x : s := ⟨a, has⟩
    have hρ : cycle σ x = ρ := Subtype.ext (Equiv.Perm.cycle_is_cycleOf ha ρ.property).symm
    have h := congrArg (fun p : ColorPreservingPerm s ↦ p.1 x) heq
    change c (cycle σ x) = d (cycle σ x) at h
    rwa [hρ] at h
  have hA : Nat.card A = ∑ σ ∈ F, 3 ^ σ.cycleFactorsFinset.card := by
    simp only [Nat.card_eq_fintype_card, A, Fintype.card_sigma, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_coe]
    exact Finset.sum_attach F (fun σ ↦ 3 ^ σ.cycleFactorsFinset.card)
  change (∑ σ ∈ F, 3 ^ σ.cycleFactorsFinset.card) ≤ _
  rw [← hA]
  calc
    _ ≤ Nat.card (ColorPreservingPerm s) := Nat.card_le_card_of_injective f hf
    _ ≤ (Fintype.card s).factorial * (Fintype.card s + 1) ^ 2 :=
      card_colorPreservingPerm_le (α := s)
    _ = _ := by rw [Fintype.card_coe]

end LennonPittelFormalization

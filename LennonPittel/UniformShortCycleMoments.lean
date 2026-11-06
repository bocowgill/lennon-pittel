module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic

/-!
# Short-cycle moments of a uniform permutation

Mark a nontrivial cycle and delete it. The remainder is an arbitrary
permutation on the complement of that cycle. The same decomposition counts
ordered pairs of distinct short cycles by marking one cycle and counting
short cycles in the remainder.
-/

@[expose] public section

open Equiv Equiv.Perm
open scoped BigOperators

namespace LennonPittelFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of nontrivial cycles whose length is at most `L`. -/
def shortCycleCount (L : ℕ) (σ : Perm α) : ℕ :=
  (σ.cycleType.filter (· ≤ L)).card

private abbrev CycleComplement (c : Perm α) := {x : α // x ∉ c.support}

private theorem disjoint_ofSubtype_cycleComplement (c : Perm α)
    (τ : Perm (CycleComplement c)) : Disjoint τ.ofSubtype c := by
  intro x
  by_cases hx : x ∈ c.support
  · exact Or.inl (ofSubtype_apply_of_not_mem τ (not_not_intro hx))
  · exact Or.inr (notMem_support.mp hx)

private theorem mem_cycleFactorsFinset_of_complement_mul (c : Perm α) (hc : c.IsCycle)
    (τ : Perm (CycleComplement c)) : c ∈ (τ.ofSubtype * c).cycleFactorsFinset := by
  rw [(disjoint_ofSubtype_cycleComplement c τ).cycleFactorsFinset_mul_eq_union,
    hc.cycleFactorsFinset_eq_singleton]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self c)

private theorem remainder_support_subset {c g : Perm α} (h : c ∈ g.cycleFactorsFinset) :
    (g * c⁻¹).support ≤ c.supportᶜ := by
  intro x hx
  exact Finset.mem_compl.mpr fun hxc ↦
    Finset.disjoint_left.mp (disjoint_mul_inv_of_mem_cycleFactorsFinset h).disjoint_support hx hxc

/-- A permutation containing a marked cycle is specified by the permutation
on the complement of that cycle. -/
private noncomputable def markedCycleEquivComplement (c : Perm α) (hc : c.IsCycle) :
    {g : Perm α // c ∈ g.cycleFactorsFinset} ≃ Perm (CycleComplement c) :=
  (Equiv.ofBijective
    (fun τ : Perm (CycleComplement c) ↦ ⟨τ.ofSubtype * c,
      mem_cycleFactorsFinset_of_complement_mul c hc τ⟩)
    ⟨fun _ _ h ↦ ofSubtype_injective (mul_right_cancel (congrArg Subtype.val h)),
      fun g ↦ by
        have hs := remainder_support_subset g.property
        let τ : Perm (CycleComplement c) :=
          (g.val * c⁻¹).subtypePerm (fun x ↦ by
            simpa only [Finset.mem_compl] using isInvariant_of_support_le hs x)
        have hτ : τ.ofSubtype = g.val * c⁻¹ :=
          ofSubtype_subtypePerm _ (fun x hx ↦
            Finset.mem_compl.mp (hs (mem_support.mpr hx)))
        refine ⟨τ, Subtype.ext ?_⟩
        change τ.ofSubtype * c = g.val
        rw [hτ, inv_mul_cancel_right]⟩).symm

private theorem sum_markedCycle_remainders {A : Type*} [AddCommMonoid A]
    (c : Perm α) (hc : c.IsCycle) (F : Multiset ℕ → A) :
    (∑ g ∈ Finset.univ.filter (fun g : Perm α ↦ c ∈ g.cycleFactorsFinset),
      F (g * c⁻¹).cycleType) =
      ∑ τ : Perm (CycleComplement c), F τ.cycleType := by
  classical
  rw [Finset.sum_subtype (p := fun g : Perm α ↦ c ∈ g.cycleFactorsFinset) _ (by simp)]
  let e := (markedCycleEquivComplement c hc).symm
  symm
  refine Fintype.sum_equiv e _ _ fun τ ↦ ?_
  change F τ.cycleType = F ((τ.ofSubtype * c) * c⁻¹).cycleType
  rw [mul_inv_cancel_right, cycleType_ofSubtype]

open scoped Classical in
private theorem sum_cycleFactors_remainders {A : Type*} [AddCommMonoid A]
    (Q : ℕ → Prop) [DecidablePred Q] (F : Multiset ℕ → A) :
    (∑ g : Perm α, ∑ c ∈ g.cycleFactorsFinset.filter (fun c ↦ Q c.support.card),
      F (g * c⁻¹).cycleType) =
    ∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ Q c.support.card),
      ∑ τ : Perm (CycleComplement c), F τ.cycleType := by
  classical
  calc
    _ = ∑ g : Perm α, ∑ c : Perm α,
        if c ∈ g.cycleFactorsFinset ∧ Q c.support.card then F (g * c⁻¹).cycleType else 0 := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [← Finset.sum_filter]
      congr 1
      ext c
      simp
    _ = ∑ c : Perm α, ∑ g : Perm α,
        if c ∈ g.cycleFactorsFinset ∧ Q c.support.card then F (g * c⁻¹).cycleType else 0 :=
      Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      by_cases hc : c.IsCycle ∧ Q c.support.card
      · rw [ite_eq_left hc]
        simp only [hc.2, and_true]
        rw [← Finset.sum_filter]
        exact sum_markedCycle_remainders c hc.1 F
      · rw [ite_eq_right hc]
        refine Finset.sum_eq_zero fun g _ ↦ ite_eq_right fun hg ↦ ?_
        exact hc ⟨(mem_cycleFactorsFinset_iff.mp hg.1).1, hg.2⟩

private theorem shortCycleCount_eq_card (L : ℕ) (g : Perm α) :
    shortCycleCount L g = (g.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L)).card := by
  simp only [shortCycleCount, Equiv.Perm.cycleType, Multiset.filter_map, Multiset.card_map]
  rfl

private theorem card_cycleComplement (c : Perm α) :
    Fintype.card (CycleComplement c) = Fintype.card α - c.support.card := by
  rw [← Finset.card_compl, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ Finset.mem_compl.symm)

open scoped Classical in
private theorem sum_shortCycleCount_eq_sum_cycleComplement (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ)) =
      ∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L),
        (Nat.factorial (Fintype.card α - c.support.card) : ℝ) := by
  convert sum_cycleFactors_remainders (α := α) (· ≤ L) (fun _ ↦ (1 : ℝ)) using 1
  · refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp [shortCycleCount_eq_card]
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_perm,
      card_cycleComplement]

open scoped Classical in
private theorem sum_cycleComplement_support_card (j : ℕ) (hj₂ : 2 ≤ j) (hjk : j ≤ Fintype.card α) :
    (∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card = j),
      (Nat.factorial (Fintype.card α - c.support.card) : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) * (1 / (j : ℝ)) := by
  let s := Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card = j)
  change ∑ c ∈ s, _ = _
  have hs (c : Perm α) (hc : c ∈ s) : c.support.card = j := (Finset.mem_filter.mp hc).2.2
  have he : s = Finset.univ.filter (fun c : Perm α ↦ c.cycleType = {j}) := by
    ext c
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hc, hj⟩
      rw [hc.cycleType, hj]
    · intro h
      have hc : c.IsCycle := card_cycleType_eq_one.mp (by rw [h]; simp)
      rw [hc.cycleType, Multiset.singleton_inj] at h
      exact ⟨hc, h⟩
  have hm : s.card * (Nat.factorial (Fintype.card α - j) * j) =
      Nat.factorial (Fintype.card α) := by
    rw [he]
    simpa [hjk, hj₂] using card_of_cycleType_mul_eq α ({j} : Multiset ℕ)
  have hmR : (s.card : ℝ) * ((Nat.factorial (Fintype.card α - j) : ℝ) * (j : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) := by exact_mod_cast hm
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  calc
    _ = ∑ _ ∈ s, (Nat.factorial (Fintype.card α - j) : ℝ) :=
      Finset.sum_congr rfl fun c hc ↦ by rw [hs c hc]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, eq_div_iff hjR, mul_assoc]
      exact hmR

private theorem sum_shortCycleCount_general (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ)) =
      (Nat.factorial (Fintype.card α) : ℝ) *
        ∑ j ∈ Finset.Icc 2 (min L (Fintype.card α)), (1 : ℝ) / j := by
  classical
  let s := Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L)
  let t := Finset.Icc 2 (min L (Fintype.card α))
  have hmaps (c : Perm α) (hc : c ∈ s) : c.support.card ∈ t := by
    obtain ⟨hcyc, hL⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_Icc.mpr ⟨hcyc.two_le_card_support, le_min hL (Finset.card_le_univ _)⟩
  rw [sum_shortCycleCount_eq_sum_cycleComplement]
  change (∑ c ∈ s, (Nat.factorial (Fintype.card α - c.support.card) : ℝ)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  obtain ⟨hj₂, hmin⟩ := Finset.mem_Icc.mp hj
  have hjk : j ≤ Fintype.card α := hmin.trans (min_le_right _ _)
  have hjL : j ≤ L := hmin.trans (min_le_left _ _)
  have hfiber : s.filter (fun c ↦ c.support.card = j) =
      Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card = j) := by
    ext c
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hc, _⟩, h⟩
      exact ⟨hc, h⟩
    · rintro ⟨hc, rfl⟩
      exact ⟨⟨hc, hjL⟩, rfl⟩
  rw [hfiber]
  exact sum_cycleComplement_support_card (α := α) j hj₂ hjk

/-- The total number of marked short cycles over all permutations of Fin k. -/
theorem sum_shortCycleCount (k L : ℕ) :
    (∑ g : Perm (Fin k), (shortCycleCount L g : ℝ)) =
      (Nat.factorial k : ℝ) * ∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j := by
  simpa only [Fintype.card_fin] using sum_shortCycleCount_general (α := Fin k) L

private theorem shortCycleCount_remove {g c : Perm α} {L : ℕ}
    (hc : c ∈ g.cycleFactorsFinset) (hL : c.support.card ≤ L) :
    (shortCycleCount L (g * c⁻¹) : ℝ) = (shortCycleCount L g : ℝ) - 1 := by
  have hd := (disjoint_mul_inv_of_mem_cycleFactorsFinset hc).cycleType_mul
  rw [inv_mul_cancel_right, (mem_cycleFactorsFinset_iff.mp hc).1.cycleType] at hd
  have heq : shortCycleCount L g = shortCycleCount L (g * c⁻¹) + 1 := by
    simp [shortCycleCount, hd, Multiset.filter_add, Multiset.filter_singleton, hL]
  rw [heq, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

open scoped Classical in
private theorem sum_shortCyclePairs_eq_sum_cycleComplement (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ) * ((shortCycleCount L g : ℝ) - 1)) =
      ∑ c ∈ Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L),
        ∑ τ : Perm (CycleComplement c), (shortCycleCount L τ : ℝ) := by
  calc
    _ = ∑ g : Perm α, ∑ c ∈ g.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L),
        (shortCycleCount L (g * c⁻¹) : ℝ) := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      have hconst : ∀ c ∈ g.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L),
          (shortCycleCount L (g * c⁻¹) : ℝ) = (shortCycleCount L g : ℝ) - 1 := by
        intro c hc
        obtain ⟨hcg, hcL⟩ := Finset.mem_filter.mp hc
        exact shortCycleCount_remove hcg hcL
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← shortCycleCount_eq_card]
    _ = _ := sum_cycleFactors_remainders (· ≤ L) (fun t ↦ ((t.filter (· ≤ L)).card : ℝ))

private theorem shortCycleHarmonic_mono (L k k' : ℕ) (h : k ≤ k') :
    (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ≤
      ∑ j ∈ Finset.Icc 2 (min L k'), (1 : ℝ) / j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨h₂, hjmax⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨h₂, hjmax.trans (min_le_min_left L h)⟩
  · intro j _ _
    positivity

private theorem sum_shortCyclePairs_general (L : ℕ) :
    (∑ g : Perm α, (shortCycleCount L g : ℝ) * ((shortCycleCount L g : ℝ) - 1)) ≤
      (Nat.factorial (Fintype.card α) : ℝ) *
        (∑ j ∈ Finset.Icc 2 (min L (Fintype.card α)), (1 : ℝ) / j) ^ 2 := by
  classical
  let s := Finset.univ.filter (fun c : Perm α ↦ c.IsCycle ∧ c.support.card ≤ L)
  let H : ℝ := ∑ j ∈ Finset.Icc 2 (min L (Fintype.card α)), (1 : ℝ) / j
  rw [sum_shortCyclePairs_eq_sum_cycleComplement]
  change (∑ c ∈ s, ∑ τ : Perm (CycleComplement c), (shortCycleCount L τ : ℝ)) ≤
    (Nat.factorial (Fintype.card α) : ℝ) * H ^ 2
  calc
    _ ≤ ∑ c ∈ s, (Nat.factorial (Fintype.card α - c.support.card) : ℝ) * H := by
      refine Finset.sum_le_sum fun c _ ↦ ?_
      rw [sum_shortCycleCount_general, card_cycleComplement]
      exact mul_le_mul_of_nonneg_left (shortCycleHarmonic_mono L _ _ (Nat.sub_le _ _)) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← sum_shortCycleCount_eq_sum_cycleComplement (α := α) L,
        sum_shortCycleCount_general]
      change (Nat.factorial (Fintype.card α) : ℝ) * H * H = _
      rw [pow_two, mul_assoc]

/-- The total number of ordered pairs of distinct short cycles is at most
the number of permutations times the square of the mean short-cycle count. -/
theorem sum_shortCycleCount_mul_sub_one_le (k L : ℕ) :
    (∑ g : Perm (Fin k), (shortCycleCount L g : ℝ) * ((shortCycleCount L g : ℝ) - 1)) ≤
      (Nat.factorial k : ℝ) * (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ^ 2 := by
  simpa only [Fintype.card_fin] using sum_shortCyclePairs_general (α := Fin k) L

end LennonPittelFormalization

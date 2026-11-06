module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Data.Finset.Powerset

/-!
# Transferring a cycle-type filter to weighted support permutations

For a fixed support, restriction and transport to `Fin k` preserve cycle type.
The coefficient from counting permutations on that support is therefore at
most the corresponding count on all `k` positions. Ordering each support then
embeds the resulting weighted sum into the sum over independent label draws.
-/

@[expose] public section

open scoped BigOperators ENNReal
namespace LennonPittelFormalization

/-- A support of size `k` contributes once for each of its `k!` orderings,
and all these ordered supports form a subset of the independent draws. -/
theorem factorial_mul_sum_powersetCard_weights_le_one {α : Type*} [Fintype α]
    [DecidableEq α] (k : ℕ) (r : α → ℝ≥0∞) (hr : ∑ i, r i = 1) :
    (k.factorial : ℝ≥0∞) * ∑ s ∈ (Finset.univ : Finset α).powersetCard k,
      ∏ i ∈ s, r i ≤ 1 := by
  classical
  let T := (Finset.univ : Finset α).powersetCard k
  let I := Σ s : T, Fin k ≃ (↑s.val : Set α)
  let f (q : I) (i : Fin k) : α := (q.2 i).val
  have hRange (q : I) : Set.range (f q) = (q.1.val : Set α) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (q.2 i).property
    · intro ha
      obtain ⟨i, hi⟩ := q.2.surjective ⟨a, ha⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hf : Function.Injective f := by
    rintro ⟨s, e⟩ ⟨t, g⟩ h
    have hst : s = t := Subtype.ext (Finset.coe_injective (by
      rw [← hRange ⟨s, e⟩, ← hRange ⟨t, g⟩, h]))
    subst t
    exact congrArg (Sigma.mk s) (Equiv.ext (fun i ↦ Subtype.ext (congrFun h i)))
  have hprod (q : I) : (∏ i, r (f q i)) = ∏ i ∈ q.1.val, r i :=
    (Fintype.prod_equiv q.2 _ (fun i ↦ r i.val) (fun _ ↦ rfl)).trans
      (Finset.prod_coe_sort _ _)
  have hc (s : T) : Fintype.card (Fin k ≃ (↑s.val : Set α)) = k.factorial := by
    have hs : s.val.card = k := (Finset.mem_powersetCard.mp s.property).2
    let e : Fin k ≃ (↑s.val : Set α) := Fintype.equivOfCardEq (by simp [hs])
    simpa only [Fintype.card_fin] using Fintype.card_equiv e
  calc
    _ = ∑ q : I, ∏ i, r (f q i) := by
      rw [Fintype.sum_sigma]
      simp_rw [hprod]
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      exact congrArg (fun z : ℝ≥0∞ ↦ (k.factorial : ℝ≥0∞) * z)
        (Finset.sum_subtype T (fun _ ↦ Iff.rfl) (fun s ↦ ∏ i ∈ s, r i))
    _ = ∑ x ∈ Finset.univ.image f, ∏ i, r (x i) :=
      (Finset.sum_image (s := Finset.univ) (f := fun x : Fin k → α ↦ ∏ i, r (x i))
        (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ ∑ x : Fin k → α, ∏ i, r (x i) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 1 := by rw [← Fintype.prod_sum]; simp [hr]

open scoped Classical in
/-- Permutations of a specified support and cycle type inject into the
permutations of `Fin k` satisfying the same cycle-type condition. -/
theorem card_support_cycleType_le {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (s : Finset α) (hs : s.card = k) (Bad : Multiset ℕ → Prop) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter
      (fun σ ↦ σ.support = s ∧ Bad σ.cycleType)).card ≤
      ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter (fun σ ↦ Bad σ.cycleType)).card := by
  classical
  let e : Fin k ≃ (↑s : Set α) := Fintype.equivOfCardEq (by simp [hs])
  let P := (Finset.univ : Finset (Equiv.Perm α)).filter
    (fun σ ↦ σ.support = s ∧ Bad σ.cycleType)
  let Q := (Finset.univ : Finset (Equiv.Perm (Fin k))).filter (fun σ ↦ Bad σ.cycleType)
  have hP (σ : P) : σ.val.support = s ∧ Bad σ.val.cycleType :=
    (Finset.mem_filter_univ σ.val).mp σ.property
  let transport (σ : P) : Equiv.Perm (Fin k) :=
    e.symm.permCongr (σ.val.subtypePerm (Equiv.Perm.isInvariant_of_support_le (hP σ).1.le))
  have hrecover (σ : P) : (transport σ).extendDomain e = σ.val := by
    let p := σ.val.subtypePerm (Equiv.Perm.isInvariant_of_support_le (hP σ).1.le)
    have h : e.permCongr (transport σ) = p := e.permCongr.apply_symm_apply p
    change Equiv.Perm.ofSubtype (e.permCongr (transport σ)) = σ.val
    rw [h]
    exact Equiv.Perm.ofSubtype_subtypePerm
      (Equiv.Perm.isInvariant_of_support_le (hP σ).1.le)
      (fun a ha ↦ (hP σ).1 ▸ Equiv.Perm.mem_support.mpr ha)
  let f (σ : P) : Q := ⟨transport σ, (Finset.mem_filter_univ (transport σ)).mpr (by
    rw [← Equiv.Perm.cycleType_extendDomain e, hrecover]
    exact (hP σ).2)⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    have hh := congrArg (fun u : Q ↦ u.val.extendDomain e) h
    change (transport σ).extendDomain e = (transport τ).extendDomain e at hh
    simpa only [hrecover] using hh
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

open scoped Classical in
/-- The normalized weighted mass of permutations of support size `k`
that satisfy a cycle-type condition is bounded by the fraction of
permutations of `Fin k` satisfying the same condition. -/
theorem sum_supportPermutation_cycleType_weights_le {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (Bad : Multiset ℕ → Prop) (r : α → ℝ≥0∞) (hr : ∑ i, r i = 1) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm α)).filter
        (fun σ ↦ σ.support.card = k ∧ Bad σ.cycleType), ∏ i ∈ σ.support, r i) ≤
      (((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
        (fun σ ↦ Bad σ.cycleType)).card : ℝ≥0∞) / (k.factorial : ℝ≥0∞) := by
  classical
  let S := (Finset.univ : Finset (Equiv.Perm α)).filter
    (fun σ ↦ σ.support.card = k ∧ Bad σ.cycleType)
  let T := (Finset.univ : Finset α).powersetCard k
  let B := ((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
    (fun σ ↦ Bad σ.cycleType)).card
  have hmaps (σ : Equiv.Perm α) (hσ : σ ∈ S) : σ.support ∈ T :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hσ).2.1⟩
  change (∑ σ ∈ S, ∏ i ∈ σ.support, r i) ≤ (B : ℝ≥0∞) / (k.factorial : ℝ≥0∞)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun σ ↦ ∏ i ∈ σ.support, r i)]
  calc
    _ ≤ ∑ s ∈ T, (B : ℝ≥0∞) * ∏ i ∈ s, r i := by
      refine Finset.sum_le_sum fun s hs ↦ ?_
      let P := S.filter (fun σ ↦ σ.support = s)
      have hp : P.card ≤ B := by
        refine (Finset.card_le_card ?_).trans
          (card_support_cycleType_le s (Finset.mem_powersetCard.mp hs).2 Bad)
        intro σ hσ
        obtain ⟨hS, hSupp⟩ := Finset.mem_filter.mp hσ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSupp, (Finset.mem_filter.mp hS).2.2⟩
      have hp' : (P.card : ℝ≥0∞) ≤ B := by exact_mod_cast hp
      calc
        _ = ∑ σ ∈ P, ∏ i ∈ s, r i :=
          Finset.sum_congr rfl fun σ hσ ↦ by rw [(Finset.mem_filter.mp hσ).2]
        _ = (P.card : ℝ≥0∞) * ∏ i ∈ s, r i := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_left hp' _
    _ = (B : ℝ≥0∞) * ∑ s ∈ T, ∏ i ∈ s, r i := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      have hfac : (k.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      apply (ENNReal.le_div_iff_mul_le (Or.inl hfac)
        (Or.inl (ENNReal.natCast_ne_top _))).mpr
      calc
        _ = (B : ℝ≥0∞) * ((k.factorial : ℝ≥0∞) * ∑ s ∈ T, ∏ i ∈ s, r i) := by ac_rfl
        _ ≤ (B : ℝ≥0∞) * 1 :=
          mul_le_mul_right (factorial_mul_sum_powersetCard_weights_le_one k r hr) _
        _ = _ := mul_one _

end LennonPittelFormalization

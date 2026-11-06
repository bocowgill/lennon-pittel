module

public import LennonPittel.ReverseIIDLabelGood
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Multiplicity of ordered presentations of cycle collections

An injective labeling of a derangement extends it to a permutation of the
label space. Its support is exactly the image of the labeling, and all the
presentations of a given permutation are precisely the orderings of its support.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

private abbrev GoodLabeling (k : ℕ) (A : Finset α) (F : α → Finset α) :=
  Σ e : derangements (Fin k),
    {x : Fin k → α // x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e.val}

private abbrev GoodSupport (k : ℕ) (A : Finset α) (F : α → Finset α) :=
  {σ : Equiv.Perm α // σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i}

variable {k : ℕ} {A : Finset α} {F : α → Finset α}

private def labelingEmbedding (l : GoodLabeling k A F) : Fin k ↪ α :=
  ⟨l.2.val, l.2.property.1⟩

private def labelingPerm (l : GoodLabeling k A F) : Equiv.Perm α :=
  l.1.val.viaFintypeEmbedding (labelingEmbedding l)

omit [Fintype α] in
private theorem labelingPerm_apply (l : GoodLabeling k A F) (i : Fin k) :
    labelingPerm l (l.2.val i) = l.2.val (l.1.val i) :=
  l.1.val.viaFintypeEmbedding_apply_image (labelingEmbedding l) i

private theorem mem_labelingPerm_support (l : GoodLabeling k A F) (a : α) :
    a ∈ (labelingPerm l).support ↔ ∃ i, l.2.val i = a := by
  rw [Equiv.Perm.mem_support]
  constructor
  · intro h
    by_contra h'
    exact h (l.1.val.viaFintypeEmbedding_apply_notMem_range (labelingEmbedding l) h')
  · rintro ⟨i, rfl⟩
    rw [labelingPerm_apply]
    exact (labelingEmbedding l).injective.ne (l.1.property i)

private noncomputable def labelingOrder (l : GoodLabeling k A F) :
    Fin k ≃ (labelingPerm l).support :=
  Equiv.ofBijective (fun i ↦ ⟨l.2.val i, (mem_labelingPerm_support l _).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ l.2.property.1 (congrArg Subtype.val h), fun a ↦ by
      obtain ⟨i, hi⟩ := (mem_labelingPerm_support l _).mp a.property
      exact ⟨i, Subtype.ext hi⟩⟩

private noncomputable def labelingSupport (l : GoodLabeling k A F) : GoodSupport k A F :=
  ⟨labelingPerm l, by
    constructor
    · simpa only [Fintype.card_coe, Fintype.card_fin] using
        (Fintype.card_congr (labelingOrder l)).symm
    · intro a ha
      obtain ⟨i, rfl⟩ := (mem_labelingPerm_support l a).mp ha
      rw [labelingPerm_apply]
      exact ⟨l.2.property.2.1 i, l.2.property.2.2 i⟩⟩

private def supportPositionPerm (s : GoodSupport k A F) (t : Fin k ≃ s.val.support) :
    Equiv.Perm (Fin k) :=
  t.symm.permCongr s.val.subtypePermOfSupport

private theorem supportPositionPerm_label (s : GoodSupport k A F) (t : Fin k ≃ s.val.support)
    (i : Fin k) : (t (supportPositionPerm s t i)).val = s.val (t i).val := by
  simp only [supportPositionPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

private def supportLabeling (s : GoodSupport k A F) (t : Fin k ≃ s.val.support) :
    GoodLabeling k A F :=
  ⟨⟨supportPositionPerm s t, fun i hi ↦
      Equiv.Perm.mem_support.mp (t i).property
        ((supportPositionPerm_label s t i).symm.trans (congrArg (fun j ↦ (t j).val) hi))⟩,
    ⟨fun i ↦ (t i).val, Subtype.val_injective.comp t.injective,
      fun i ↦ (s.property.2 _ (t i).property).1, fun i ↦ by
        change (t (supportPositionPerm s t i)).val ∉ F (t i).val
        rw [supportPositionPerm_label]
        exact (s.property.2 _ (t i).property).2⟩⟩

private theorem labelingSupport_supportLabeling (s : GoodSupport k A F)
    (t : Fin k ≃ s.val.support) :
    labelingSupport (supportLabeling s t) = s := by
  apply Subtype.ext
  ext a
  change labelingPerm (supportLabeling s t) a = s.val a
  by_cases ha : a ∈ s.val.support
  · obtain ⟨i, hi⟩ := t.surjective ⟨a, ha⟩
    have hi' : (t i).val = a := congrArg Subtype.val hi
    rw [← hi']
    exact (labelingPerm_apply (supportLabeling s t) i).trans (supportPositionPerm_label s t i)
  · have hnot : a ∉ Set.range (labelingEmbedding (supportLabeling s t)) :=
      fun ⟨i, hi⟩ ↦ ha (hi ▸ (t i).property)
    exact ((supportLabeling s t).1.val.viaFintypeEmbedding_apply_notMem_range
      (labelingEmbedding (supportLabeling s t)) hnot).trans ((Equiv.Perm.notMem_support.mp ha).symm)

private noncomputable def supportOrderEquivFiber (s : GoodSupport k A F) :
    (Fin k ≃ s.val.support) ≃ {l : GoodLabeling k A F // labelingSupport l = s} := by
  let f (t : Fin k ≃ s.val.support) :
      {l : GoodLabeling k A F // labelingSupport l = s} :=
    ⟨supportLabeling s t, labelingSupport_supportLabeling s t⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro t u h
    exact Equiv.ext fun i ↦ Subtype.ext (congrArg (fun z ↦ z.val.2.val i) h)
  · rintro ⟨l, rfl⟩
    refine ⟨labelingOrder l, Subtype.ext (Sigma.subtype_ext ?_ rfl)⟩
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply (labelingEmbedding l).injective
    exact (supportPositionPerm_label (labelingSupport l) (labelingOrder l) i).trans
      (labelingPerm_apply l i)

private theorem card_supportFiber (s : GoodSupport k A F) :
    Nat.card {l : GoodLabeling k A F // labelingSupport l = s} = k.factorial := by
  classical
  let t : Fin k ≃ s.val.support := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, s.property.1])
  rw [← Nat.card_congr (supportOrderEquivFiber s), Nat.card_eq_fintype_card,
    ← Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin k)) t), Fintype.card_perm,
    Fintype.card_fin]

open scoped Classical in
/-- Every filtered support permutation of size `k` occurs once for each of the
`k!` orderings of its support, with the same product of label weights. -/
theorem sum_iidLabelGood_eq_factorial_mul_sum_support
    (k : ℕ) (r : α → ℝ≥0∞) (A : Finset α) (F : α → Finset α) :
    (∑ e : derangements (Fin k),
      ∑ x ∈ Finset.univ.filter
        (fun x ↦ x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e.val),
          ∏ i, r (x i)) =
      (k.factorial : ℝ≥0∞) * ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm α ↦ σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i),
          ∏ i ∈ σ.support, r i := by
  let W (s : GoodSupport k A F) : ℝ≥0∞ := ∏ i ∈ s.val.support, r i
  have hw (l : GoodLabeling k A F) : (∏ i, r (l.2.val i)) = W (labelingSupport l) := by
    calc
      _ = ∏ j : (labelingPerm l).support, r j.val :=
        Fintype.prod_equiv (labelingOrder l) (fun i ↦ r (l.2.val i))
          (fun j ↦ r j.val) (fun _ ↦ rfl)
      _ = _ := Finset.prod_coe_sort _ r
  calc
    _ = ∑ l : GoodLabeling k A F, ∏ i, r (l.2.val i) := by
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      exact Finset.sum_subtype _ (fun _ ↦ by simp) _
    _ = ∑ l : GoodLabeling k A F, W (labelingSupport l) :=
      Finset.sum_congr rfl (fun l _ ↦ hw l)
    _ = ∑ s : GoodSupport k A F, ∑ l : {l // labelingSupport l = s}, W (labelingSupport l.val) :=
      (Fintype.sum_fiberwise labelingSupport (fun l ↦ W (labelingSupport l))).symm
    _ = ∑ s : GoodSupport k A F, (k.factorial : ℝ≥0∞) * W s := by
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      have hc : Fintype.card {l // labelingSupport l = s} = k.factorial :=
        (Nat.card_eq_fintype_card.symm.trans (card_supportFiber s))
      calc
        _ = ∑ _l : {l // labelingSupport l = s}, W s :=
          Finset.sum_congr rfl (fun l _ ↦ congrArg W l.property)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
    _ = _ := by
      have h : (∑ s : GoodSupport k A F, W s) = ∑ σ ∈ Finset.univ.filter
          (fun σ : Equiv.Perm α ↦ σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i),
            ∏ i ∈ σ.support, r i := (Finset.sum_subtype
        (Finset.univ.filter (fun σ : Equiv.Perm α ↦
          σ.support.card = k ∧ ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i))
        (fun σ ↦ Finset.mem_filter_univ σ) (fun σ ↦ ∏ i ∈ σ.support, r i)).symm
      rw [← Finset.mul_sum, h]

end LennonPittelFormalization

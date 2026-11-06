module

public import LennonPittel.CoexposedRotationMultiplicity
public import LennonPittel.PivotCrossBlocker
public import LennonPittel.PivotIdealExposure
public import LennonPittel.RotationUndoSequences
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Powerset

/-!
# Disjoint families of truncated pivot decorations

A decorated matching identifies its pivot as its unique exposed long rotation.
It then identifies its decoration as the labels removed from that pivot's anchor.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ ν μ : Matching n} {hopt : IsManOptimal p μ₀}

/-- The length of a realized rotation is its number of moved men. -/
def rotationLength (r : Rotation p μ₀) : ℕ :=
  r.val.cycle.support.card

/-- An undo path fixes a man if every removed label fixes that man. -/
theorem RotationUndoSequence.partner_eq_of_fixed {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) (m : Fin n)
    (hm : ∀ r ∈ rs, r.val.cycle m = m) : μ m = ν m := by
  induction h with
  | nil => rfl
  | @cons a b r rs ha σ hlabel rest ih =>
    have hcycle : reverseRotationCycle a.symm σ.val m = m :=
      congrArg (fun q : Rotation p μ₀ ↦ q.val.cycle m) hlabel |>.trans
        (hm r List.mem_cons_self)
    have hstep := congrArg (fun M : Matching n ↦ M m)
      (eliminateRotation_undoReverseRotation a σ.val)
    change eliminateRotation (undoReverseRotation a σ.val)
      (reverseRotationCycle a.symm σ.val) m = a m at hstep
    rw [eliminateRotation_apply, hcycle] at hstep
    exact (ih (fun q hq ↦ hm q (List.mem_cons_of_mem _ hq))).trans hstep

/-- Undoing a subset that is disjoint from the pivot fixes its participating men. -/
theorem undoMaximalSubsetEmbedding_fixed_on_pivot (hopt : IsManOptimal p μ₀)
    (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
    (hdisj : ∀ s ∈ D, ∀ m, r.val.cycle m ≠ m → s.val.val.cycle m = m)
    (m : Fin n) (hm : r.val.cycle m ≠ m) :
    (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val m =
      (singletonRotationAnchor hopt r).val m := by
  obtain ⟨rs, _, hset, hp⟩ := exists_rotationUndoSequence_of_maximal_subset hopt
    (singletonRotationAnchor hopt r).property D
  apply hp.partner_eq_of_fixed m
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hset ▸ (show s ∈ {q | q ∈ rs} from hs)
  exact hdisj t ht m hm

/-- Under support disjointness, compatibility is precisely the absence of a cross blocker. -/
theorem pivot_isExposedAt_undo_iff_no_crossBlocker (hopt : IsManOptimal p μ₀)
    (r : Rotation p μ₀)
    (D : Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val))
    (hdisj : ∀ s ∈ D, ∀ m, r.val.cycle m ≠ m → s.val.val.cycle m = m) :
    r.IsExposedAt (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val
      ↔ ∀ m w, ¬ IsPivotCrossBlocker p (singletonRotationAnchor hopt r).val
        (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D).val
          r.val.cycle m w := by
  let A := singletonRotationAnchor hopt r
  let N := undoMaximalSubsetEmbedding hopt A.property D
  have hA := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  have hfix := undoMaximalSubsetEmbedding_fixed_on_pivot hopt r D hdisj
  have hlabel : rotationLabel N.val r.val.cycle = r.val :=
    (rotationLabel_eq_of_fixed_on_cycle hfix).trans hA.2
  change (IsExposedRotation p N.val r.val.cycle ∧ rotationLabel N.val r.val.cycle = r.val) ↔ _
  rw [and_iff_left hlabel]
  exact isExposedRotation_iff_no_pivotCrossBlocker hA.1 N.property hfix

/-- The individual compatibility tests suffice for a whole disjoint decoration. -/
theorem pivot_isExposedAt_undo_of_compatible_reverse_cycles (hopt : IsManOptimal p μ₀)
    (r : Rotation p μ₀) :
    let A := singletonRotationAnchor hopt r
    ∀ (D : Set (MaximalEliminatedRotation p μ₀ A.val))
      (rs : List {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p A.val σ}),
      rs.Nodup →
      {q | q ∈ rs.map (reverseExposedRotationLabel hopt A.property)} = Subtype.val '' D →
      (∀ s ∈ D, ∀ m, r.val.cycle m ≠ m → s.val.val.cycle m = m) →
      (∀ σ ∈ rs, IsExposedRotation p (undoReverseRotation A.val σ.val) r.val.cycle) →
      r.IsExposedAt (undoMaximalSubsetEmbedding hopt A.property D).val := by
  dsimp only
  intro D rs hnd hlabels hdisj hcompat
  let A := singletonRotationAnchor hopt r
  let N := undoMaximalSubsetEmbedding hopt A.property D
  have hpivot := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  obtain ⟨M, hseq, hpath⟩ :=
    exists_rotationUndoSequence_of_reverse_cycles hopt A.property rs hnd
  have hMI : eliminatedRotations p μ₀ M = eliminatedRotations p μ₀ N.val := by
    rw [hpath.eliminatedRotations_end, hlabels, eliminatedRotations_undoMaximalSubsetEmbedding]
  have hMN : M = N.val :=
    congrArg Subtype.val ((stableMatchingToRotationIdeal_bijective hopt).1
      (LowerSet.ext hMI : stableMatchingToRotationIdeal ⟨M, hpath.isStable_end⟩ =
        stableMatchingToRotationIdeal N))
  rw [hMN] at hseq
  have hfixed := undoMaximalSubsetEmbedding_fixed_on_pivot hopt r D hdisj
  refine ⟨?_, (rotationLabel_eq_of_fixed_on_cycle hfixed).trans hpivot.2⟩
  refine isExposedRotation_of_compatible_reverse_sequence hseq
    (hnd.map Subtype.val_injective) ?_ hpivot.1 hfixed ?_ ?_
  · intro σ hσ
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hσ
    exact s.property
  · intro σ hσ m hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hσ
    have hs' : reverseExposedRotationLabel hopt A.property s ∈ Subtype.val '' D :=
      hlabels ▸ (show reverseExposedRotationLabel hopt A.property s ∈
        {q | q ∈ rs.map (reverseExposedRotationLabel hopt A.property)} from
        List.mem_map_of_mem hs)
    obtain ⟨t, ht, htEq⟩ := hs'
    have hcycle : reverseRotationCycle A.val.symm s.val m = m := by
      change (reverseExposedRotationLabel hopt A.property s).val.cycle m = m
      rw [← htEq]
      exact hdisj t ht m hm
    have hstep : eliminateRotation (undoReverseRotation A.val s.val)
        (reverseRotationCycle A.val.symm s.val) m = A.val m :=
      congrArg (fun B : Matching n ↦ B m) (eliminateRotation_undoReverseRotation A.val s.val)
    simpa only [eliminateRotation_apply, hcycle] using hstep
  · intro σ hσ
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hσ
    exact hcompat s hs

/-- A truncated decoration consists of removed maximal labels of total length
at most `K`, with the pivot still exposed at the resulting matching. -/
structure PivotDecoration (hopt : IsManOptimal p μ₀) (K : ℕ) (r : Rotation p μ₀) where
  removed : Finset (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)
  totalLength_le : (∑ s ∈ removed, rotationLength s.val) ≤ K
  pivot_exposed : r.IsExposedAt
    (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property removed).val

namespace PivotDecoration

variable {K : ℕ} {r : Rotation p μ₀}

private theorem ext_removed {D E : PivotDecoration hopt K r} (h : D.removed = E.removed) :
    D = E := by
  cases D
  cases E
  cases h
  rfl

instance : Finite (PivotDecoration hopt K r) := by
  classical
  let := Fintype.ofFinite (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)
  exact Finite.of_injective (fun D ↦ D.removed) fun _ _ ↦ ext_removed

/-- A filtered decoration family is no larger than the set of all subsets
of reverse cycles at the pivot's singleton anchor. -/
theorem card_le_two_pow_reverseExposed (D : Finset (PivotDecoration hopt K r)) :
    D.card ≤ 2 ^ numExposedRotations (swapProfile p) (singletonRotationAnchor hopt r).val.symm := by
  classical
  let A := singletonRotationAnchor hopt r
  let : Fintype (MaximalEliminatedRotation p μ₀ A.val) := Fintype.ofFinite _
  have h := Nat.card_le_card_of_injective
    (fun d : D ↦ d.val.removed) (fun _ _ he ↦ Subtype.ext (ext_removed he))
  have hcard : Nat.card (MaximalEliminatedRotation p μ₀ A.val) =
      numExposedRotations (swapProfile p) A.val.symm :=
    Nat.card_congr (reverseExposedRotationEquivMaximal hopt A.property).symm
  rw [Nat.card_eq_finsetCard, Nat.card_eq_fintype_card, Fintype.card_finset,
    ← Nat.card_eq_fintype_card, hcard] at h
  exact h

/-- The stable matching generated by the decoration. -/
noncomputable def matching (D : PivotDecoration hopt K r) : {M : Matching n // IsStable p M} :=
  undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property D.removed

/-- The original pivot and the removed labels are all and only the exposed labels. -/
theorem isExposedAt_matching_iff (D : PivotDecoration hopt K r) (s : Rotation p μ₀) :
    s.IsExposedAt D.matching.val ↔ s = r ∨ s ∈ Subtype.val ''
      (↑D.removed :
        Set (MaximalEliminatedRotation p μ₀ (singletonRotationAnchor hopt r).val)) :=
  isExposedAt_undo_pivot_iff hopt r D.removed D.pivot_exposed s

/-- If the pivot is long, the resulting matching recovers it as the unique long exposed label. -/
theorem long_exposed_iff (D : PivotDecoration hopt K r) (hr : K < rotationLength r)
    (s : Rotation p μ₀) :
    (s.IsExposedAt D.matching.val ∧ K < rotationLength s) ↔ s = r := by
  constructor
  · rintro ⟨he, hl⟩
    rcases (D.isExposedAt_matching_iff s).mp he with hs | ⟨t, ht, rfl⟩
    · exact hs
    · have ht' : t ∈ D.removed := ht
      exact (not_lt_of_ge ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ht').trans
        D.totalLength_le) hl).elim
  · rintro rfl
    exact ⟨D.pivot_exposed, hr⟩

end PivotDecoration

/-- A pivot whose length is strictly greater than the decoration cap. -/
abbrev LongPivot (p : Profile n) (μ₀ : Matching n) (K : ℕ) :=
  {r : Rotation p μ₀ // K < rotationLength r}

/-- All truncated decoration families at long pivots embed into stable matchings. -/
noncomputable def pivotDecorationEmbedding (hopt : IsManOptimal p μ₀) (K : ℕ) :
    (Σ r : LongPivot p μ₀ K, PivotDecoration hopt K r.val) ↪
      {M : Matching n // IsStable p M} :=
  ⟨fun a ↦ a.2.matching, by
    rintro ⟨r, D⟩ ⟨s, E⟩ h
    change D.matching = E.matching at h
    have he : r.val.IsExposedAt E.matching.val := by
      rw [← h]
      exact D.pivot_exposed
    have hrs : r = s := Subtype.ext ((E.long_exposed_iff s.property r.val).mp ⟨he, r.property⟩)
    subst s
    let e := undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r.val).property
    have hsets : (↑D.removed : Set _) = ↑E.removed := e.injective h
    have hDE : D = E := PivotDecoration.ext_removed (Finset.coe_injective hsets)
    cases hDE
    rfl⟩

/-- An arbitrary filtering of the truncated families still counts distinct stable matchings. -/
theorem sum_card_pivotDecorations_le_numStableMatchings (hopt : IsManOptimal p μ₀) (K : ℕ)
    (P : Finset (LongPivot p μ₀ K)) (D : ∀ r : LongPivot p μ₀ K, Finset
      (PivotDecoration hopt K r.val)) :
    (∑ r ∈ P, (D r).card) ≤ numStableMatchings p := by
  classical
  calc
    _ = (P.sigma D).card := (Finset.card_sigma P D).symm
    _ = ((P.sigma D).map (pivotDecorationEmbedding hopt K)).card := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_univ _

end LennonPittelFormalization

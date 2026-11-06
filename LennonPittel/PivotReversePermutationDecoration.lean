module

public import LennonPittel.CoexposureCycleMoment
public import LennonPittel.PivotIncidenceCounting
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# From compatible reverse permutations to pivot decorations

The cycle factors of a realized reverse permutation identify the maximal
labels it removes. Their total length is the size of the permutation's
support, and undoing them gives the endpoint encoded by the permutation.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n}

private theorem RotationSequence.eq_mul_listProd {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) : ν = μ * rs.prod := by
  induction h with
  | nil => simp
  | cons _ _ _ ih =>
    rw [List.prod_cons, ← mul_assoc]
    simpa only [eliminateRotation, Equiv.Perm.mul_def] using ih

/-- Conjugating a reverse cycle by the anchor matching preserves its length. -/
theorem reverseExposedRotationLabel_length (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ σ}) :
    rotationLength (reverseExposedRotationLabel hopt hμ σ) = σ.val.support.card := by
  change (μ⁻¹ * σ.val * (μ⁻¹)⁻¹).support.card = _
  exact Equiv.Perm.card_support_conj

/-- A cycle factor of a realized reverse permutation is an exposed reverse rotation. -/
def reverseFactorEmbedding {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (↥σ.cycleFactorsFinset) ↪ {τ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ τ} :=
  ⟨fun τ ↦ ⟨τ.val, realizesSuccessorPermutation_iff_factors.mp hσ τ.val τ.property⟩,
    fun _ _ h ↦ Subtype.ext (congrArg
      (fun t : {τ : Equiv.Perm (Fin n) // IsReverseExposedRotation p μ τ} ↦ t.val) h)⟩

/-- Read the maximal labels removed by the cycle factors of a realized reverse permutation. -/
noncomputable def realizedReverseRemovedLabels (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {σ : Matching n} (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    Finset (MaximalEliminatedRotation p μ₀ μ) :=
  σ.cycleFactorsFinset.attach.map
    ((reverseFactorEmbedding hσ).trans (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding)

/-- The sum of the removed rotation lengths equals the size of the reverse support. -/
theorem realizedReverseRemovedLabels_totalLength (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (∑ t ∈ realizedReverseRemovedLabels hopt hμ hσ, rotationLength t.val) =
      σ.support.card := by
  rw [realizedReverseRemovedLabels, Finset.sum_map, card_support_eq_sum_cycleFactors_support]
  calc
    _ = ∑ t ∈ σ.cycleFactorsFinset.attach, t.val.support.card :=
      Finset.sum_congr rfl fun t _ ↦ reverseExposedRotationLabel_length hopt hμ
        (reverseFactorEmbedding hσ t)
    _ = _ := Finset.sum_attach σ.cycleFactorsFinset
      (fun t : Equiv.Perm (Fin n) ↦ t.support.card)

/-- The number of removed labels of length at most `L` equals the number of short cycle factors. -/
theorem realizedReverseRemovedLabels_short_card (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {σ : Matching n} (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (L : ℕ) :
    ((realizedReverseRemovedLabels hopt hμ hσ).filter
      (fun r ↦ rotationLength r.val ≤ L)).card = (σ.cycleType.filter (· ≤ L)).card := by
  rw [realizedReverseRemovedLabels, Finset.filter_map, Finset.card_map]
  have hlen (t : σ.cycleFactorsFinset) :
      rotationLength (((reverseFactorEmbedding hσ).trans
        (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding) t).val = t.val.support.card :=
    reverseExposedRotationLabel_length hopt hμ (reverseFactorEmbedding hσ t)
  simp only [Function.comp_def, hlen, Equiv.Perm.cycleType_def, Multiset.filter_map, Multiset.card_map]
  rw [Finset.filter_attach (fun t : Matching n ↦ t.support.card ≤ L), Finset.card_map,
    Finset.card_attach]
  rfl

/-- Undoing the maximal labels read from a realized reverse permutation gives exactly
the matching obtained by applying that permutation on the women’s side. -/
theorem undoMaximalSubsetEmbedding_realizedReverseRemovedLabels (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) :
    (undoMaximalSubsetEmbedding hopt hμ (realizedReverseRemovedLabels hopt hμ hσ)).val =
      undoReverseRotation μ σ := by
  classical
  let S := σ.cycleFactorsFinset
  let f := reverseFactorEmbedding hσ
  let rs := S.attach.toList.map f
  have hnd : rs.Nodup := S.attach.nodup_toList.map f.injective
  have hset : (rs.map Subtype.val).toFinset = S := by
    ext τ
    simp only [List.mem_toFinset, List.mem_map, rs, Finset.mem_toList]
    constructor
    · rintro ⟨_, ⟨t, _, rfl⟩, rfl⟩
      exact t.property
    · intro ht
      exact ⟨f ⟨τ, ht⟩, ⟨⟨τ, ht⟩, Finset.mem_attach S _, rfl⟩, rfl⟩
  have hprod : (rs.map Subtype.val).prod = σ := by
    let L := rs.map Subtype.val
    have hc : (↑L.toFinset : Set (Matching n)).Pairwise (Function.onFun Commute id) := by
      rw [show L.toFinset = S from hset]
      exact σ.cycleFactorsFinset_mem_commute
    calc
      _ = L.toFinset.noncommProd id hc := by
        simpa only [List.map_id] using
          (Finset.noncommProd_toFinset L id hc (hnd.map Subtype.val_injective)).symm
      _ = S.noncommProd id σ.cycleFactorsFinset_mem_commute :=
        Finset.noncommProd_congr hset (fun _ _ ↦ rfl) hc
      _ = σ := σ.cycleFactorsFinset_noncommProd
  obtain ⟨M, hseq, hpath⟩ := exists_rotationUndoSequence_of_reverse_cycles hopt hμ rs hnd
  have hM : M = undoReverseRotation μ σ := by
    have he := hseq.eq_mul_listProd
    rw [hprod] at he
    change M.symm = eliminateRotation μ.symm σ at he
    exact congrArg Equiv.symm he
  let D := realizedReverseRemovedLabels hopt hμ hσ
  let N := undoMaximalSubsetEmbedding hopt hμ D
  let e := f.trans (reverseExposedRotationEquivMaximal hopt hμ).toEmbedding
  have hD : D = S.attach.map e := rfl
  have hlabels : {q | q ∈ rs.map (reverseExposedRotationLabel hopt hμ)} =
      Subtype.val '' (D : Set (MaximalEliminatedRotation p μ₀ μ)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨t, ht, he⟩ := List.mem_map.mp hq
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
      refine ⟨e s, ?_, he⟩
      change e s ∈ D
      rw [hD]
      exact Finset.mem_map.mpr ⟨s, Finset.mem_attach S _, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      change t ∈ D at ht
      rw [hD] at ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
      exact List.mem_map.mpr ⟨f s, List.mem_map.mpr ⟨s, Finset.mem_toList.mpr hs, rfl⟩, rfl⟩
  have hMI : eliminatedRotations p μ₀ M = eliminatedRotations p μ₀ N.val := by
    rw [hpath.eliminatedRotations_end, hlabels, eliminatedRotations_undoMaximalSubsetEmbedding]
  have hMN : M = N.val :=
    congrArg Subtype.val ((stableMatchingToRotationIdeal_bijective hopt).1
      (LowerSet.ext hMI : stableMatchingToRotationIdeal ⟨M, hpath.isStable_end⟩ =
        stableMatchingToRotationIdeal N))
  exact hMN.symm.trans hM

/-- A short realized reverse permutation at the singleton anchor, disjoint from the pivot
participants, whose undo leaves the forward pivot exposed. -/
abbrev IsCompatibleReversePermutation (hopt : IsManOptimal p μ₀) (K : ℕ)
    (r : Rotation p μ₀) (σ : Matching n) : Prop :=
  let A := singletonRotationAnchor hopt r
  RealizesSuccessorPermutation (swapProfile p) A.val.symm σ ∧
    σ.support.card ≤ K ∧
    (∀ m ∈ r.val.cycle.support, A.val m ∉ σ.support) ∧
    IsExposedRotation p (undoReverseRotation A.val σ) r.val.cycle

/-- The finite type of compatible realized reverse permutations of total length at most `K`. -/
abbrev CompatibleReversePermutation (hopt : IsManOptimal p μ₀) (K : ℕ)
    (r : Rotation p μ₀) :=
  {σ : Matching n // IsCompatibleReversePermutation hopt K r σ}

/-- Translate a compatible reverse permutation into the corresponding truncated decoration. -/
noncomputable def compatibleReversePermutationToDecoration (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    PivotDecoration hopt K r := by
  let A := singletonRotationAnchor hopt r
  let D := realizedReverseRemovedLabels hopt A.property σ.property.1
  have hN : (undoMaximalSubsetEmbedding hopt A.property D).val =
      undoReverseRotation A.val σ.val :=
    undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt A.property σ.property.1
  have hfix (m : Fin n) (hm : r.val.cycle m ≠ m) :
      undoReverseRotation A.val σ.val m = A.val m := by
    have hsm : σ.val (A.val m) = A.val m := by
      by_contra hn
      exact σ.property.2.2.1 m (Equiv.Perm.mem_support.mpr hm) (Equiv.Perm.mem_support.mpr hn)
    apply (undoReverseRotation A.val σ.val).symm.injective
    rw [Equiv.symm_apply_apply]
    change m = A.val.symm (σ.val (A.val m))
    rw [hsm, Equiv.symm_apply_apply]
  have hpivot := ((eq_singletonRotationAnchor_iff hopt r A).mp rfl r).mpr rfl
  refine ⟨D, (realizedReverseRemovedLabels_totalLength hopt A.property σ.property.1).le.trans
    σ.property.2.1, ?_⟩
  change r.IsExposedAt (undoMaximalSubsetEmbedding hopt A.property D).val
  rw [hN]
  exact ⟨σ.property.2.2.2, (rotationLabel_eq_of_fixed_on_cycle hfix).trans hpivot.2⟩

/-- The decoration removes exactly the maximal labels of the reverse permutation's factors. -/
theorem compatibleReversePermutationToDecoration_removed (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).removed =
      realizedReverseRemovedLabels hopt (singletonRotationAnchor hopt r).property σ.property.1 :=
  rfl

/-- The decoration's stable matching is the explicit reverse-permutation endpoint. -/
theorem compatibleReversePermutationToDecoration_matching (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) (σ : CompatibleReversePermutation hopt K r) :
    (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      undoReverseRotation (singletonRotationAnchor hopt r).val σ.val :=
  undoMaximalSubsetEmbedding_realizedReverseRemovedLabels hopt
    (singletonRotationAnchor hopt r).property σ.property.1

/-- Distinct compatible reverse permutations give distinct pivot decorations. -/
noncomputable def compatibleReversePermutationEmbedding (hopt : IsManOptimal p μ₀)
    (K : ℕ) (r : Rotation p μ₀) :
    CompatibleReversePermutation hopt K r ↪ PivotDecoration hopt K r :=
  ⟨compatibleReversePermutationToDecoration hopt K r, by
    intro σ τ h
    have he := congrArg (fun D : PivotDecoration hopt K r ↦ D.matching.val) h
    change (compatibleReversePermutationToDecoration hopt K r σ).matching.val =
      (compatibleReversePermutationToDecoration hopt K r τ).matching.val at he
    rw [compatibleReversePermutationToDecoration_matching,
      compatibleReversePermutationToDecoration_matching] at he
    apply Subtype.ext
    apply Equiv.ext
    intro w
    exact (singletonRotationAnchor hopt r).val.symm.injective
      (congrArg (fun ν : Matching n ↦ ν.symm w) he)⟩

/-- Families indexed by their exact support size count distinct compatible decorations. -/
theorem sum_card_compatibleReversePermutationFamilies_le_card_pivotDecoration
    (hopt : IsManOptimal p μ₀) (K : ℕ) (r : Rotation p μ₀)
    (I : Finset ℕ) (S : ℕ → Finset (Matching n))
    (hcard : ∀ k ∈ I, ∀ σ ∈ S k, σ.support.card = k)
    (hσ : ∀ k ∈ I, ∀ σ ∈ S k, IsCompatibleReversePermutation hopt K r σ) :
    (∑ k ∈ I, (S k).card) ≤ Nat.card (PivotDecoration hopt K r) := by
  classical
  have hd : (I : Set ℕ).PairwiseDisjoint S := by
    intro k hk l hl hne
    exact Finset.disjoint_left.mpr fun σ hs ht ↦
      hne ((hcard k hk σ hs).symm.trans (hcard l hl σ ht))
  rw [← Finset.card_biUnion hd, ← Nat.card_eq_finsetCard]
  let f (σ : ↥(I.biUnion S)) : CompatibleReversePermutation hopt K r :=
    ⟨σ.val, by
      obtain ⟨k, hk, hs⟩ := Finset.mem_biUnion.mp σ.property
      exact hσ k hk σ.val hs⟩
  let e := compatibleReversePermutationEmbedding hopt K r
  exact Nat.card_le_card_of_injective (e ∘ f) (e.injective.comp fun _ _ h ↦
    Subtype.ext (congrArg (fun σ : CompatibleReversePermutation hopt K r ↦ σ.val) h))

end LennonPittelFormalization

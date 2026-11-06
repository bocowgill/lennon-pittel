module

public import LennonPittel.ReverseRotationPersistence
public import LennonPittel.UndoMaximalSubset

/-!
# Undo sequences for initially maximal rotations

Every list of distinct initially maximal labels can be undone by actual
reverse successor cycles. The eliminated set of the endpoint depends only
on the members of the list.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {hopt : IsManOptimal p μ₀}

/-- Each step uses a reverse cycle exposed at the current stable matching,
with the specified realized rotation label. -/
inductive RotationUndoSequence (hopt : IsManOptimal p μ₀) :
    Matching n → List (Rotation p μ₀) → Matching n → Prop where
  | nil {ν : Matching n} (hν : IsStable p ν) : RotationUndoSequence hopt ν [] ν
  | cons {ν τ : Matching n} {r : Rotation p μ₀} {rs : List (Rotation p μ₀)}
      (hν : IsStable p ν)
      (σ : {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ})
      (hlabel : reverseExposedRotationLabel hopt hν σ = r)
      (rest : RotationUndoSequence hopt (undoReverseRotation ν σ.val) rs τ) :
      RotationUndoSequence hopt ν (r :: rs) τ

/-- The endpoint of a legal undo sequence is stable. -/
theorem RotationUndoSequence.isStable_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) : IsStable p μ := by
  induction h with
  | nil hν => exact hν
  | cons _ _ _ _ ih => exact ih

/-- The eliminated set at the endpoint is the initial set minus the undone labels. -/
theorem RotationUndoSequence.eliminatedRotations_end {rs : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) :
    eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ ν \ {r | r ∈ rs} := by
  induction h with
  | nil => simp
  | cons hν σ hlabel _ ih =>
    rw [ih, eliminatedRotations_undoReverseRotation hopt hν σ, hlabel, Set.sdiff_sdiff]
    congr 1
    ext r
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]

/-- A distinct maximal label remains maximal after removing one maximal label. -/
private theorem maximal_mem_diff_singleton {α : Type*} [PartialOrder α] {I : Set α} {r s : α}
    (hs : Maximal (fun q ↦ q ∈ I) s) (hne : s ≠ r) :
    Maximal (fun q ↦ q ∈ I \ {r}) s :=
  ⟨⟨hs.prop, fun h ↦ hne (Set.mem_singleton_iff.mp h)⟩, fun _ h hsq ↦ hs.2 h.1 hsq⟩

/-- Every prescribed order of distinct initially maximal labels is a legal undo sequence. -/
theorem exists_rotationUndoSequence_of_nodup (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (rs : List (Rotation p μ₀)) (hnd : rs.Nodup)
    (hmax : ∀ r ∈ rs, Maximal (fun q ↦ q ∈ eliminatedRotations p μ₀ ν) r) :
    ∃ μ, RotationUndoSequence hopt ν rs μ := by
  induction rs generalizing ν with
  | nil => exact ⟨ν, .nil hν⟩
  | cons r rs ih =>
    have hr := hmax r List.mem_cons_self
    let e := reverseExposedRotationEquivMaximal hopt hν
    let σ := e.symm ⟨r, hr⟩
    have hlabel : reverseExposedRotationLabel hopt hν σ = r :=
      congrArg Subtype.val (e.apply_symm_apply ⟨r, hr⟩)
    have hstep := eliminatedRotations_undoReverseRotation hopt hν σ
    rw [hlabel] at hstep
    have htail (s : Rotation p μ₀) (hs : s ∈ rs) :
        Maximal
          (fun q ↦ q ∈ eliminatedRotations p μ₀ (undoReverseRotation ν σ.val)) s := by
      rw [hstep]
      exact maximal_mem_diff_singleton (hmax s (List.mem_cons_of_mem r hs))
        (fun h ↦ (List.nodup_cons.mp hnd).1 (h ▸ hs))
    obtain ⟨μ, hpath⟩ :=
      ih (σ.property.undo_stable hν) (List.nodup_cons.mp hnd).2 htail
    exact ⟨μ, .cons hν σ hlabel hpath⟩

/-- Two legal undo orders with the same labels have the same stable endpoint. -/
theorem RotationUndoSequence.endpoint_eq_of_same_labels {τ : Matching n}
    {rs ts : List (Rotation p μ₀)}
    (h : RotationUndoSequence hopt ν rs μ) (h' : RotationUndoSequence hopt ν ts τ)
    (hsame : ∀ r, r ∈ rs ↔ r ∈ ts) : μ = τ := by
  have hsets : {r | r ∈ rs} = {r | r ∈ ts} := Set.ext hsame
  have hideal : eliminatedRotations p μ₀ μ = eliminatedRotations p μ₀ τ := by
    rw [h.eliminatedRotations_end, h'.eliminatedRotations_end, hsets]
  have heq : (⟨μ, h.isStable_end⟩ : {a : Matching n // IsStable p a}) =
      ⟨τ, h'.isStable_end⟩ :=
    (stableMatchingToRotationIdeal_bijective hopt).1 (LowerSet.ext hideal)
  exact congrArg Subtype.val heq

/-- The canonical endpoint of a maximal subset is reached by every duplicate-free
enumeration of its labels. -/
theorem rotationUndoSequence_undoMaximalSubsetEmbedding
    (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (D : Set (MaximalEliminatedRotation p μ₀ ν)) (rs : List (Rotation p μ₀))
    (hnd : rs.Nodup) (horder : {r | r ∈ rs} = Subtype.val '' D) :
    RotationUndoSequence hopt ν rs (undoMaximalSubsetEmbedding hopt hν D).val := by
  have hmax (r : Rotation p μ₀) (hr : r ∈ rs) :
      Maximal (fun q ↦ q ∈ eliminatedRotations p μ₀ ν) r := by
    obtain ⟨s, _, rfl⟩ := horder ▸ (show r ∈ {r | r ∈ rs} from hr)
    exact s.property
  obtain ⟨μ, hpath⟩ := exists_rotationUndoSequence_of_nodup hopt hν rs hnd hmax
  have hideal : eliminatedRotations p μ₀ μ =
      eliminatedRotations p μ₀ (undoMaximalSubsetEmbedding hopt hν D).val := by
    rw [hpath.eliminatedRotations_end, horder, eliminatedRotations_undoMaximalSubsetEmbedding]
  have heq : (⟨μ, hpath.isStable_end⟩ : {a : Matching n // IsStable p a}) =
      undoMaximalSubsetEmbedding hopt hν D :=
    (stableMatchingToRotationIdeal_bijective hopt).1 (LowerSet.ext hideal)
  exact congrArg Subtype.val heq ▸ hpath

/-- Every subset of maximal eliminated labels has a legal undo sequence. -/
theorem exists_rotationUndoSequence_of_maximal_subset (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (D : Set (MaximalEliminatedRotation p μ₀ ν)) :
    ∃ rs : List (Rotation p μ₀), rs.Nodup ∧ {r | r ∈ rs} = Subtype.val '' D ∧
      RotationUndoSequence hopt ν rs (undoMaximalSubsetEmbedding hopt hν D).val := by
  classical
  let A : Finset (Rotation p μ₀) := (Subtype.val '' D).toFinite.toFinset
  have horder : {r | r ∈ A.toList} = Subtype.val '' D := by
    ext r
    simp [A]
  exact ⟨A.toList, A.nodup_toList, horder,
    rotationUndoSequence_undoMaximalSubsetEmbedding hopt hν D _ A.nodup_toList horder⟩

private theorem exists_aligned_undo_sequences {α : Type*} (hopt : IsManOptimal p μ₀)
    (hν : IsStable p ν) (rs : List α)
    (cycle : α → Equiv.Perm (Fin n)) (label : α → Rotation p μ₀)
    (hnd : (rs.map cycle).Nodup)
    (he : ∀ x ∈ rs, IsReverseExposedRotation p ν (cycle x))
    (hl : ∀ x (hx : x ∈ rs), reverseExposedRotationLabel hopt hν
      ⟨cycle x, he x hx⟩ = label x) :
    ∃ μ, RotationSequence (swapProfile p) ν.symm (rs.map cycle) μ.symm ∧
      RotationUndoSequence hopt ν (rs.map label) μ := by
  induction rs generalizing ν with
  | nil => exact ⟨ν, .nil (isStable_swapProfile_iff.mpr hν), .nil hν⟩
  | cons a rs ih =>
    have hσ := he a List.mem_cons_self
    have hν' := hσ.undo_stable hν
    have hdistinct (x : α) (hx : x ∈ rs) : cycle x ≠ cycle a := fun heq ↦
      (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨x, hx, heq⟩)
    have hnext (x : α) (hx : x ∈ rs) :
        IsReverseExposedRotation p (undoReverseRotation ν (cycle a)) (cycle x) :=
      (he x (List.mem_cons_of_mem a hx)).persist_undo hσ (hdistinct x hx)
    have hnextLabel (x : α) (hx : x ∈ rs) : reverseExposedRotationLabel hopt hν'
        ⟨cycle x, hnext x hx⟩ = label x :=
      (reverseExposedRotationLabel_persist_undo hopt hν (he x (List.mem_cons_of_mem a hx))
        hσ (hdistinct x hx)).trans (hl x (List.mem_cons_of_mem a hx))
    obtain ⟨μ, hcycles, hlabels⟩ :=
      ih hν' (List.nodup_cons.mp hnd).2 hnext hnextLabel
    refine ⟨μ, .cons (isStable_swapProfile_iff.mpr hν) hσ ?_,
      .cons hν ⟨cycle a, hσ⟩ (hl a List.mem_cons_self) hlabels⟩
    simpa only [undoReverseRotation, Equiv.symm_symm] using hcycles

/-- A prescribed order of distinct original reverse cycles is legal, and its steps
undo exactly the corresponding original labels in that order. -/
theorem exists_rotationUndoSequence_of_reverse_cycles
    (hopt : IsManOptimal p μ₀) (hν : IsStable p ν)
    (rs : List {σ : Equiv.Perm (Fin n) // IsReverseExposedRotation p ν σ}) (hnd : rs.Nodup) :
    ∃ μ, RotationSequence (swapProfile p) ν.symm (rs.map Subtype.val) μ.symm ∧
      RotationUndoSequence hopt ν (rs.map (reverseExposedRotationLabel hopt hν)) μ :=
  exists_aligned_undo_sequences hopt hν rs Subtype.val (reverseExposedRotationLabel hopt hν)
    (hnd.map Subtype.val_injective) (fun σ _ ↦ σ.property) (fun _ _ ↦ rfl)

end LennonPittelFormalization

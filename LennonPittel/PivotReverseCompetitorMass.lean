module

public import LennonPittel.PivotRelaxedArcEvents
public import LennonPittel.PivotReverseMaskLowerMoment

/-!
# Competitor mass at a fixed forward mask

A reverse column loses its diagonal and the forward-active cells. A relaxed
column loses the pivot men as well. These are deterministic identities and
bounds on the same spouse scores that define the reverse weights.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem sum_subtype_ne_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (j : α) :
    (∑ i : {i // i ≠ j}, f i.val) = (∑ i, f i) - f j := by
  have h := Finset.sum_erase_add (Finset.univ : Finset α) f (Finset.mem_univ j)
  rw [Finset.sum_subtype (p := fun x ↦ x ≠ j) _ (by simp) f] at h
  exact eq_sub_of_add_eq h

private theorem sum_subtype_bool_eq {α : Type*} [Fintype α] (b : α → Bool)
    (f : α → ℝ) :
    (∑ i : {i // b i = true}, f i.val) = (∑ i, if b i then f i else 0) := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

/-- Raw male spouse-score mass lost to the active off-diagonal cells of one column. -/
noncomputable def forwardMaskOmittedMass {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) : ℝ :=
  ∑ i : {i : Fin n // i ≠ j}, if flag ⟨(i.val, j), i.property⟩ then
    (diagonalPairAt d i.val).1 else 0

private def inactiveColumnEquiv {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    ForwardInactiveColumnIndex flag j ≃
      {i : {i : Fin n // i ≠ j} // flag ⟨(i.val, j), i.property⟩ ≠ true} where
  toFun q := by
    let i : {i : Fin n // i ≠ j} := ⟨forwardInactiveColumnMan q, fun h ↦
      q.val.val.property (h.trans q.property.symm)⟩
    have hcell : (⟨(i.val, j), i.property⟩ : OffDiagonalCellIndex n) = q.val.val :=
      Subtype.ext (Prod.ext rfl q.property.symm)
    exact ⟨i, by rw [hcell]; exact q.val.property⟩
  invFun i := ⟨⟨⟨(i.val.val, j), i.val.property⟩, i.property⟩, rfl⟩
  left_inv q := forwardInactiveColumnMan_injective flag j rfl
  right_inv i := Subtype.ext (Subtype.ext rfl)

/-- The total inactive mass is the full mass minus the diagonal and active entries. -/
theorem sum_forwardInactiveColumn_eq {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    (∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q) =
      (∑ i, (diagonalPairAt d i).1) - (diagonalPairAt d j).1 -
        forwardMaskOmittedMass d flag j := by
  classical
  let b (i : {i : Fin n // i ≠ j}) := flag ⟨(i.val, j), i.property⟩
  let f (i : Fin n) := (diagonalPairAt d i).1
  have ha : (∑ i : {i // b i = true}, f i.val.val) = forwardMaskOmittedMass d flag j :=
    sum_subtype_bool_eq b (fun i ↦ f i.val)
  have hi :
      (∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q) =
        ∑ i : {i // ¬ b i = true}, f i.val.val :=
    (inactiveColumnEquiv flag j).sum_comp (fun i ↦ f i.val.val)
  have h := Fintype.sum_subtype_add_sum_subtype (fun i ↦ b i = true) (fun i ↦ f i.val)
  rw [ha, ← hi, sum_subtype_ne_eq] at h
  linarith only [h]

/-- The raw competitor total removes just the target from the inactive column. -/
theorem sum_forwardInactiveCompetitor_eq {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {j : Fin n}
    (q : ForwardInactiveColumnIndex flag j) :
    (∑ t : {t : ForwardInactiveColumnIndex flag j // t ≠ q},
      forwardInactiveColumnThreshold d t.val) =
      (∑ i, (diagonalPairAt d i).1) - (diagonalPairAt d j).1 -
        forwardMaskOmittedMass d flag j - forwardInactiveColumnThreshold d q := by
  rw [sum_subtype_ne_eq, sum_forwardInactiveColumn_eq]

/-- The relaxed competitor test loses at most the full pivot weight in addition
to the diagonal, active-cell, and target weights. -/
theorem forwardKeptCompetitorMass_ge {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {P : Finset (Fin n)} {j : Fin n}
    (t : ForwardKeptColumnIndex flag P j) (hx : ∀ i, 0 ≤ (diagonalPairAt d i).1) :
    (∑ i, (diagonalPairAt d i).1) - (diagonalPairAt d j).1 -
        forwardMaskOmittedMass d flag j - (∑ i ∈ P, (diagonalPairAt d i).1) -
        forwardInactiveColumnThreshold d t.val ≤ forwardKeptCompetitorMass d t := by
  classical
  let f (i : Fin n) := (diagonalPairAt d i).1
  let g (q : ForwardInactiveColumnIndex flag j) := forwardInactiveColumnThreshold d q
  let p (q : ForwardInactiveColumnIndex flag j) := forwardInactiveColumnMan q ∉ P
  let e (q : {q // ¬ p q}) := forwardInactiveColumnMan q.val
  have hinj : Function.Injective e := fun _ _ h ↦
    Subtype.ext (forwardInactiveColumnMan_injective flag j h)
  have hsubset : Finset.univ.image e ⊆ P := by
    intro i hi
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hi
    exact not_not.mp q.property
  have homit : (∑ q : {q // ¬ p q}, g q.val) ≤ ∑ i ∈ P, f i := calc
    _ = ∑ i ∈ Finset.univ.image e, f i :=
      (Finset.sum_image fun _ _ _ _ h ↦ hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ ↦ hx i)
  have hsplit := Fintype.sum_subtype_add_sum_subtype p g
  change (∑ q : {q // p q}, g q.val) + (∑ q : {q // ¬ p q}, g q.val) =
    (∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q) at hsplit
  rw [sum_forwardInactiveColumn_eq] at hsplit
  have htarget := sum_subtype_ne_eq (fun q : {q // p q} ↦ g q.val) t
  change _ ≤ ∑ q : {q : {q // p q} // q ≠ t}, g q.val.val
  linarith only [homit, hsplit, htarget]

/-- The forbidden reverse targets are exactly the diagonal and active mass,
normalized by the total male spouse score. -/
theorem sum_forwardMaskForbiddenTargets_reverseSpouseWeights {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (w : Fin n)
    (hx : ∀ i, 0 ≤ (diagonalPairAt d i).1) (hX : 0 < ∑ i, (diagonalPairAt d i).1) :
    (∑ i ∈ forwardMaskForbiddenTargets μ flag w, reverseSpouseWeights μ d i) =
      ENNReal.ofReal (((diagonalPairAt d (μ.symm w)).1 +
        forwardMaskOmittedMass d flag (μ.symm w)) / (∑ i, (diagonalPairAt d i).1)) := by
  classical
  let F := forwardMaskForbiddenTargets μ flag w
  let f (i : Fin n) := (diagonalPairAt d i).1
  let X := ∑ i, f i
  let j := μ.symm w
  let a (q : ForwardInactiveColumnIndex flag j) := μ (forwardInactiveColumnMan q)
  have hinj : Function.Injective a := fun _ _ h ↦
    forwardInactiveColumnMan_injective flag j (μ.injective h)
  have himage : Finset.univ.image a = Fᶜ := by
    ext i
    rw [Finset.mem_image, Finset.mem_compl]
    constructor
    · rintro ⟨q, _, rfl⟩
      exact (notMem_forwardMaskForbiddenTargets_iff μ flag w _).mpr
        ⟨q, (μ.symm_apply_apply _).symm⟩
    · intro hi
      obtain ⟨q, hq⟩ := (notMem_forwardMaskForbiddenTargets_iff μ flag w i).mp hi
      exact ⟨q, Finset.mem_univ _, (congrArg μ hq).trans (μ.apply_symm_apply i)⟩
  have hinactive : (∑ i ∈ Fᶜ, f (μ.symm i)) =
      ∑ q : ForwardInactiveColumnIndex flag j, forwardInactiveColumnThreshold d q := calc
    _ = ∑ i ∈ Finset.univ.image a, f (μ.symm i) := by rw [himage]
    _ = _ := by
      rw [Finset.sum_image fun _ _ _ _ h ↦ hinj h]
      simp only [a, Equiv.symm_apply_apply, f, forwardInactiveColumnThreshold]
  have htotal : (∑ i, f (μ.symm i)) = X := μ.symm.sum_comp f
  have hsplit := Finset.sum_add_sum_compl F (fun i ↦ f (μ.symm i))
  rw [hinactive, htotal, sum_forwardInactiveColumn_eq] at hsplit
  have hF : (∑ i ∈ F, f (μ.symm i)) = f j + forwardMaskOmittedMass d flag j := by
    linarith only [hsplit]
  change (∑ i ∈ F, ENNReal.ofReal (f (μ.symm i) / X)) =
    ENNReal.ofReal ((f j + forwardMaskOmittedMass d flag j) / X)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (hx (μ.symm i)) hX.le),
    ← Finset.sum_div, hF]

end LennonPittelFormalization

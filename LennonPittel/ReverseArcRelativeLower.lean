module

public import LennonPittel.PivotReverseScoreSuccessor

/-!
# Lower bounds on available reverse successors

An available target has weight at least its normalized male spouse score
times a correction. We separate the exact quadratic and endpoint errors
from the convenient bound in terms of the largest competitor threshold.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Relative error in the lower successor-mass bound, in terms of the
competitor threshold sum `S` and sum of squares `Q`. -/
noncomputable def reverseSuccessorRelativeError (S Q : ℝ) : ℝ :=
  Q / S ^ 2 + 6 * (Q / S ^ 3) + Real.exp (-(S * (1 / 2)))

/-- Relative lower bound for a designated target in a normalized inactive column. -/
theorem reverseSuccessorColumnEvent_mass_ge_of_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    {y X δ : ℝ} {v : ι → ℝ} (i : ι) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hv : ∀ j, v j ∈ Icc 0 1)
    (hS : 0 < ∑ j : {j : ι // j ≠ i}, v j.val)
    (hSX : (∑ j : {j : ι // j ≠ i}, v j.val) ≤ X)
    (hδ : reverseSuccessorRelativeError (∑ j : {j : ι // j ≠ i}, v j.val)
      (∑ j : {j : ι // j ≠ i}, v j.val ^ 2) ≤ δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ) * ENNReal.ofReal (v i / X) ≤
      (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
        (reverseSuccessorColumnEvent y v i) := by
  let S := ∑ j : {j : ι // j ≠ i}, v j.val
  let Q := ∑ j : {j : ι // j ≠ i}, v j.val ^ 2
  have hraw := (reverseSuccessorPairEvent_mass_bounds hy0 hy1 (hv i)
    (fun j : {j : ι // j ≠ i} ↦ hv j.val) hS).1
  rw [reverseSuccessorPairEvent_mass hy0 hy1 (hv i)
    (fun j : {j : ι // j ≠ i} ↦ hv j.val)] at hraw
  rw [reverseSuccessorColumnEvent_mass i hy0 hy1 hv, ← ENNReal.ofReal_mul (sub_nonneg.mpr hδ1)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans hraw
  change (1 - δ) * (v i / X) ≤ v i * (1 / S - Q / S ^ 3 - 6 * Q / S ^ 4 -
    Real.exp (-(S * (1 / 2))) / S)
  calc
    _ = v i * ((1 - δ) / X) := by ring
    _ ≤ v i * ((1 - δ) / S) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (sub_nonneg.mpr hδ1) hS hSX) (hv i).1
    _ ≤ v i * ((1 - reverseSuccessorRelativeError S Q) / S) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (sub_le_sub_left hδ 1) hS.le) (hv i).1
    _ = _ := by
      unfold reverseSuccessorRelativeError
      have hS_ne : S ≠ 0 := hS.ne'
      field_simp [hS_ne]
      ring

/-- A maximum threshold controls both quadratic errors when the competitor sum
is at least half the total mass and the total is at least two. -/
theorem reverseSuccessorRelativeError_le {ι : Type*} [Fintype ι] {v : ι → ℝ} {X m : ℝ}
    (hv : ∀ j, 0 ≤ v j) (hm : 0 ≤ m) (hmax : ∀ j, v j ≤ m)
    (hX : 2 ≤ X) (hSlo : X / 2 ≤ ∑ j, v j) :
    reverseSuccessorRelativeError (∑ j, v j) (∑ j, v j ^ 2) ≤
      14 * m / X + Real.exp (-X / 4) := by
  let S := ∑ j, v j
  let Q := ∑ j, v j ^ 2
  have hSlo' : X / 2 ≤ S := hSlo
  have hhalf : 0 < X / 2 := by linarith only [hX]
  have hS1 : 1 ≤ S := by linarith only [hX, hSlo']
  have hS : 0 < S := hhalf.trans_le hSlo'
  have hQ : Q ≤ m * S := by
    dsimp only [Q, S]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hmax j) (hv j)
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ ↦ sq_nonneg (v j)
  have hquad : Q / S ^ 2 ≤ 2 * m / X := calc
    _ ≤ (m * S) / S ^ 2 := div_le_div_of_nonneg_right hQ (sq_nonneg S)
    _ = m / S := by field_simp [hS.ne']
    _ ≤ m / (X / 2) := div_le_div_of_nonneg_left hm hhalf hSlo'
    _ = _ := by rw [div_div_eq_mul_div, mul_comm m]
  have hcubic : Q / S ^ 3 ≤ 2 * m / X :=
    (div_le_div_of_nonneg_left hQ0 (pow_pos hS 2) (pow_le_pow_right₀ hS1 (by decide))).trans hquad
  have hexp : Real.exp (-(S * (1 / 2))) ≤ Real.exp (-X / 4) :=
    Real.exp_le_exp.mpr (by linarith only [hSlo'])
  change reverseSuccessorRelativeError S Q ≤ _
  unfold reverseSuccessorRelativeError
  rw [show 14 * m / X = 7 * (2 * m / X) by ring]
  linarith only [hquad, hcubic, hexp]

/-- The lower estimate in terms of the total mass and a maximum competitor threshold. -/
theorem reverseSuccessorColumnEvent_mass_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {y X m δ : ℝ} {v : ι → ℝ} (i : ι) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hv : ∀ j, v j ∈ Icc 0 1) (hm : 0 ≤ m)
    (hmax : ∀ j : {j : ι // j ≠ i}, v j.val ≤ m)
    (hX : 2 ≤ X)
    (hSlo : X / 2 ≤ ∑ j : {j : ι // j ≠ i}, v j.val)
    (hShi : (∑ j : {j : ι // j ≠ i}, v j.val) ≤ X)
    (hδ : 14 * m / X + Real.exp (-X / 4) ≤ δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ) * ENNReal.ofReal (v i / X) ≤
      (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
        (reverseSuccessorColumnEvent y v i) :=
  reverseSuccessorColumnEvent_mass_ge_of_error i hy0 hy1 hv
    ((show 0 < X / 2 by linarith only [hX]).trans_le hSlo) hShi
    ((reverseSuccessorRelativeError_le (fun j : {j : ι // j ≠ i} ↦ (hv j.val).1)
      hm hmax hX hSlo).trans hδ) hδ1

/-- A target present in the inactive mask has a relative lower arc bound.
The competitor sum omits both the spouse and the designated target. -/
theorem normalizedForwardInactiveColumnLaw_reverseArc_ge {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n)
    (q : ForwardInactiveColumnIndex flag i) (hq : q.val.val.val.1 = j) {X m δ : ℝ}
    (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1)
    (hx : ∀ k, (diagonalPairAt d k).1 ∈ Icc 0 1) (hX : 2 ≤ X)
    (hSlo : X / 2 ≤ ∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      (diagonalPairAt d k.val.val.val.val.1).1)
    (hShi : (∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      (diagonalPairAt d k.val.val.val.val.1).1) ≤ X)
    (hxmax : ∀ k, (diagonalPairAt d k).1 ≤ m)
    (hδ : 14 * m / X + Real.exp (-X / 4) ≤ δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (1 - δ) * ENNReal.ofReal ((diagonalPairAt d j).1 / X) ≤
      normalizedForwardInactiveColumnLaw d flag i (forwardInactiveReverseArcEvent d flag i j) := by
  have h := reverseSuccessorColumnEvent_mass_ge q hy0 hy1
    (fun k ↦ hx k.val.val.val.1) ((hx j).1.trans (hxmax j))
    (fun k ↦ hxmax k.val.val.val.val.1) hX hSlo hShi hδ hδ1
  rw [hq] at h
  refine h.trans (measure_mono ?_)
  exact subset_iUnion (fun s : {s : ForwardInactiveColumnIndex flag i // s.val.val.val.1 = j} ↦
    reverseSuccessorColumnEvent (diagonalPairAt d i).2
      (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) s.val) ⟨q, hq⟩

/-- The competing thresholds are a subcollection of the total male spouse scores,
with no duplication of the male indices. -/
theorem forwardInactiveCompetitor_sum_le_total {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n)
    (q : ForwardInactiveColumnIndex flag i) (hx : ∀ j, 0 ≤ (diagonalPairAt d j).1) :
    (∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      (diagonalPairAt d k.val.val.val.val.1).1) ≤ ∑ j, (diagonalPairAt d j).1 := by
  classical
  let label (k : {k : ForwardInactiveColumnIndex flag i // k ≠ q}) : Fin n :=
    k.val.val.val.val.1
  have hinj : Function.Injective label := fun k l h ↦
    Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext
      (Prod.ext h (k.val.property.trans l.val.property.symm)))))
  calc
    _ = ∑ j ∈ Finset.univ.image label, (diagonalPairAt d j).1 :=
      (Finset.sum_image fun _ _ _ _ h ↦ hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ ↦ hx j)

end LennonPittelFormalization

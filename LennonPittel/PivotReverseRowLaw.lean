module

public import LennonPittel.PivotReverseEligibility
public import LennonPittel.PittelRowApprox

/-!
# Exact successor mass in an inactive reverse column

All available candidates share the same rescaling of the woman's score.
After that rescaling, the reverse successor test is the ordinary successor
integral with starting threshold zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*}

/-- The designated inactive candidate is eligible and has the smallest
female score among eligible competitors. -/
def reverseSuccessorPairEvent (y x : ℝ) (v : ι → ℝ) :
    Set ((ℝ × ℝ) × (ι → ℝ × ℝ)) :=
  {z | y < z.1.2 ∧ z.1.1 < x ∧ ∀ j, ¬((z.2 j).2 < z.1.2 ∧ (z.2 j).1 < v j)}

/-- The designated reverse successor test is a measurable score event. -/
theorem measurableSet_reverseSuccessorPairEvent [Fintype ι] (y x : ℝ) (v : ι → ℝ) :
    MeasurableSet (reverseSuccessorPairEvent y x v) := by
  unfold reverseSuccessorPairEvent
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_lt measurable_const measurable_fst.snd).inter
    ((measurableSet_lt measurable_fst.fst measurable_const).inter
      (MeasurableSet.iInter fun j ↦ ?_))
  have h : Measurable (fun z : (ℝ × ℝ) × (ι → ℝ × ℝ) ↦ z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact ((measurableSet_lt h.snd measurable_fst.snd).inter
    (measurableSet_lt h.fst measurable_const)).compl

private theorem rowNonblockingLaw_zero_eq_unitScorePairLaw (v : ℝ) :
    rowNonblockingLaw 0 v = unitScorePairLaw := by
  unfold rowNonblockingLaw unitScorePairLaw
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simp only [mem_compl_iff, not_not, ofPred_mem_eq, Measure.prod_prod,
    unitScoreLaw_apply_Iio (show (0 : ℝ) ∈ Icc 0 1 by norm_num), ENNReal.ofReal_zero, zero_mul]

/-- The probability of a specified reverse successor in a normalized inactive
column is its male threshold times the integral of the competitor factors. -/
theorem reverseSuccessorPairEvent_mass [Fintype ι] {y x : ℝ} {v : ι → ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hx : x ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1) :
    ((unitScoreLaw.prod (inactiveFemaleScoreLaw y)).prod
      (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y)))
        (reverseSuccessorPairEvent y x v) =
      ENNReal.ofReal (x * scoreRowMass Finset.univ v 0 1) := by
  let a := 1 - y
  have ha : 0 < a := sub_pos.mpr hy1
  let g (z : ℝ × ℝ) := (z.2, y + a * z.1)
  let inactive := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  have hg : MeasurePreserving g unitScorePairLaw inactive :=
    ((MeasurePreserving.id unitScoreLaw).prod
      (measurePreserving_inactiveFemaleScoreLaw hy0 hy1)).comp Measure.measurePreserving_swap
  have hπ : MeasurePreserving (fun z : ι → ℝ × ℝ ↦ fun j ↦ g (z j))
      (Measure.pi fun _ : ι ↦ unitScorePairLaw) (Measure.pi fun _ : ι ↦ inactive) :=
    measurePreserving_pi _ _ fun _ ↦ hg
  have h := hg.prod hπ
  have hlt (s t : ℝ) : y + a * s < y + a * t ↔ s < t :=
    (add_lt_add_iff_left y).trans (mul_lt_mul_iff_of_pos_left ha)
  have hzero (t : ℝ) : y < y + a * t ↔ 0 < t := by
    simpa only [mul_zero, add_zero] using hlt 0 t
  have he : Prod.map g (fun z : ι → ℝ × ℝ ↦ fun j ↦ g (z j)) ⁻¹'
      reverseSuccessorPairEvent y x v = scoreSuccessorPairEvent 0 x v := by
    ext z
    simp only [mem_preimage, reverseSuccessorPairEvent, scoreSuccessorPairEvent, mem_ofPred_eq,
      Prod.map_fst, Prod.map_snd, g, hzero, hlt]
  change (inactive.prod (Measure.pi fun _ : ι ↦ inactive))
    (reverseSuccessorPairEvent y x v) = _
  rw [← h.map_eq, Measure.map_apply h.measurable
    (measurableSet_reverseSuccessorPairEvent y x v), he]
  simpa only [rowNonblockingLaw_zero_eq_unitScorePairLaw] using
    scoreSuccessorPairEvent_mass (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hx hv

/-- Quantitative two-sided estimates for the reverse row: the upper bound
is the reciprocal of the competitor sum, and the lower bound records the
finite interval and quadratic corrections. -/
theorem reverseSuccessorPairEvent_mass_bounds [Fintype ι] {y x : ℝ} {v : ι → ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hx : x ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1)
    (hsum : 0 < ∑ j, v j) :
    let a := ∑ j, v j
    let b := ∑ j, (v j) ^ 2
    let P := ((unitScoreLaw.prod (inactiveFemaleScoreLaw y)).prod
      (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y)))
        (reverseSuccessorPairEvent y x v)
    ENNReal.ofReal (x * (1 / a - b / a ^ 3 - 6 * b / a ^ 4 -
      Real.exp (-(a * (1 / 2))) / a)) ≤ P ∧ P ≤ ENNReal.ofReal (x / a) := by
  dsimp only
  rw [reverseSuccessorPairEvent_mass hy0 hy1 hx hv]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hx.1
    change _ ≤ pittelRowIntegral Finset.univ v 1
    simpa only [one_mul, mul_one] using
      (le_pittelRowIntegral Finset.univ v (s := 1) (L := 1 / 2) (m := 1)
        (by norm_num) (by norm_num) (fun j _ ↦ (hv j).1)
        (fun j _ ↦ by simpa only [one_mul] using (hv j).2) (fun j _ ↦ (hv j).2)
        (fun j _ ↦ by nlinarith [(hv j).2]) hsum)
  · apply ENNReal.ofReal_le_ofReal
    rw [← mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hx.1
    simpa only [mul_zero, neg_zero, Real.exp_zero] using
      (scoreRowMass_le_exp_tail (J := Finset.univ) (y := v)
        (fun j _ ↦ (hv j).1) (fun j _ ↦ (hv j).2) hsum le_rfl
        (a := 0) (b := 1) le_rfl zero_le_one le_rfl)

/-- The designated-candidate test in an array of inactive cells. The index
type contains exactly the available candidates in the column. -/
def reverseSuccessorColumnEvent [DecidableEq ι] (y : ℝ) (v : ι → ℝ) (i : ι) :
    Set (ι → ℝ × ℝ) :=
  (fun z : ι → ℝ × ℝ ↦ (z i, fun j : {j : ι // j ≠ i} ↦ z j.val)) ⁻¹'
    reverseSuccessorPairEvent y (v i) (fun j : {j : ι // j ≠ i} ↦ v j.val)

theorem measurableSet_reverseSuccessorColumnEvent [Fintype ι] [DecidableEq ι]
    (y : ℝ) (v : ι → ℝ) (i : ι) : MeasurableSet (reverseSuccessorColumnEvent y v i) :=
  (measurableSet_reverseSuccessorPairEvent y (v i) (fun j : {j : ι // j ≠ i} ↦ v j.val)).preimage
    ((measurable_pi_apply i).prodMk (Measurable.of_eval fun j ↦ measurable_pi_apply j.val))

/-- Splitting off one candidate rewrites its normalized column probability
as the one-dimensional reverse successor integral. -/
theorem reverseSuccessorColumnEvent_mass [Fintype ι] [DecidableEq ι] {y : ℝ} {v : ι → ℝ}
    (i : ι) (hy0 : 0 ≤ y) (hy1 : y < 1) (hv : ∀ j, v j ∈ Icc 0 1) :
    (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      (reverseSuccessorColumnEvent y v i) =
      ENNReal.ofReal (v i * scoreRowMass Finset.univ (fun j : {j : ι // j ≠ i} ↦ v j.val) 0 1) := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  have h := measurePreserving_rowTargetAndCompetitors (fun _ : ι ↦ ν) i
  rw [reverseSuccessorColumnEvent, ← Measure.map_apply h.measurable
    (measurableSet_reverseSuccessorPairEvent y _ _), h.map_eq]
  exact reverseSuccessorPairEvent_mass hy0 hy1 (hv i) fun j ↦ hv j.val

/-- If the omitted competitor mass leaves at least `X / a`, the relative
arc bound is the normalized target weight times `a`. -/
theorem reverseSuccessorColumnEvent_mass_le [Fintype ι] [DecidableEq ι] {y X a : ℝ}
    {v : ι → ℝ} (i : ι) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hv : ∀ j, v j ∈ Icc 0 1) (hX : 0 < X) (ha : 0 < a)
    (hcomp : X / a ≤ ∑ j : {j : ι // j ≠ i}, v j.val) :
    (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      (reverseSuccessorColumnEvent y v i) ≤ ENNReal.ofReal a * ENNReal.ofReal (v i / X) := by
  let S := ∑ j : {j : ι // j ≠ i}, v j.val
  have hS : 0 < S := (div_pos hX ha).trans_le hcomp
  have h := (reverseSuccessorPairEvent_mass_bounds hy0 hy1 (hv i)
    (fun j : {j : ι // j ≠ i} ↦ hv j.val) hS).2
  rw [reverseSuccessorPairEvent_mass hy0 hy1 (hv i) (fun j : {j : ι // j ≠ i} ↦ hv j.val)] at h
  rw [reverseSuccessorColumnEvent_mass i hy0 hy1 hv, ← ENNReal.ofReal_mul ha.le]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  change v i / S ≤ a * (v i / X)
  calc
    _ ≤ v i / (X / a) := div_le_div_of_nonneg_left (hv i).1 (div_pos hX ha) hcomp
    _ = _ := by rw [div_div_eq_mul_div]; ring

end LennonPittelFormalization

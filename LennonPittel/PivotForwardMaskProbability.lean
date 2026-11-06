module

public import LennonPittel.PivotForwardRevealCell

/-!
# The forward flag law at fixed spouse scores

After fixing spouse scores, the stability constraint is cellwise.
Normalizing and then reading the forward eligibility bits preserves the
product structure, including when only a single column is observed.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The forward bit of one score cell. -/
noncomputable def forwardCellFlag (x y : ℝ) (z : ℝ × ℝ) : Bool := by
  classical
  exact decide (z ∈ forwardEligibleScoreCell x y)

@[simp]
theorem forwardCellFlag_eq_true {x y : ℝ} {z : ℝ × ℝ} :
    forwardCellFlag x y z = true ↔ z ∈ forwardEligibleScoreCell x y := by
  classical
  simp [forwardCellFlag]

theorem measurable_forwardCellFlag (x y : ℝ) : Measurable (forwardCellFlag x y) := by
  apply measurable_to_bool
  simpa only [preimage, mem_singleton_iff, forwardCellFlag_eq_true, ofPred_mem_eq]
    using measurableSet_forwardEligibleScoreCell x y

/-- The observed forward mask from the off-diagonal scores. -/
noncomputable def forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (q : OffDiagonalCellIndex n) : Bool :=
  forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (z q)

theorem measurable_forwardMaskOfScores {n : ℕ} (d : DiagonalScorePairs n) :
    Measurable (forwardMaskOfScores d) :=
  Measurable.of_eval fun _ ↦ (measurable_forwardCellFlag _ _).comp (measurable_pi_apply _)

/-- Reading a specific mask is exactly the fixed-mask event. -/
theorem forwardMaskOfScores_eq_iff {n : ℕ} (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    forwardMaskOfScores d z = flag ↔ z ∈ forwardScoreMaskEvent d flag := by
  rw [funext_iff, forwardScoreMaskEvent, mem_univ_pi]
  apply forall_congr'
  intro q
  cases flag q with
  | false =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores, ← Bool.not_eq_true]
  | true =>
    simp [forwardScoreCellFlagEvent, forwardMaskOfScores]

private noncomputable def normalizedStableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  ((stableScoreCellLaw x y) univ)⁻¹ • stableScoreCellLaw x y

private instance (x y : ℝ) : IsFiniteMeasure (normalizedStableScoreCellLaw x y) := by
  constructor
  rw [normalizedStableScoreCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top

/-- The Boolean law of forward eligibility at one stable cell. -/
@[no_expose] noncomputable def forwardCellFlagProbabilityLaw (x y : ℝ) : Measure Bool :=
  Measure.map (forwardCellFlag x y) (normalizedStableScoreCellLaw x y)

/-- The normalized off-diagonal score law at fixed spouse scores and stability. -/
noncomputable def stableOffDiagonalProbabilityLaw {n : ℕ} (d : DiagonalScorePairs n) :
    Measure (OffDiagonalScorePairs n) :=
  (offDiagonalScoreLaw n (offDiagonalNonblocking d))⁻¹ •
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)

private theorem stableOffDiagonalProbabilityLaw_eq_pi {n : ℕ} (d : DiagonalScorePairs n) :
    stableOffDiagonalProbabilityLaw d = Measure.pi fun q : OffDiagonalCellIndex n ↦
      normalizedStableScoreCellLaw (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 := by
  symm
  refine Measure.pi_eq fun s _ ↦ ?_
  unfold stableOffDiagonalProbabilityLaw
  rw [offDiagonalScoreLaw_nonblocking, offDiagonalScoreLaw_restrict_nonblocking,
    Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [normalizedStableScoreCellLaw, Measure.smul_apply, smul_eq_mul,
    stableScoreCellLaw, Measure.restrict_apply_univ]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (measure_ne_top unitScorePairLaw _)),
    Finset.prod_mul_distrib]

/-- All off-diagonal forward flags have independent cell laws. -/
theorem map_forwardMaskOfScores_stableOffDiagonalProbabilityLaw {n : ℕ}
    (d : DiagonalScorePairs n) :
    Measure.map (forwardMaskOfScores d) (stableOffDiagonalProbabilityLaw d) =
      Measure.pi (fun q : OffDiagonalCellIndex n ↦
        forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.1).1
          (diagonalPairAt d q.val.2).2) := by
  rw [stableOffDiagonalProbabilityLaw_eq_pi]
  let μ (q : OffDiagonalCellIndex n) :=
    normalizedStableScoreCellLaw (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
  let f (q : OffDiagonalCellIndex n) :=
    forwardCellFlag (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
  let : ∀ q, IsFiniteMeasure ((μ q).map (f q)) :=
    fun _ ↦ Measure.isFiniteMeasure_map _ _
  exact Measure.pi_map_pi (μ := μ) (f := f) fun _ ↦
    (measurable_forwardCellFlag _ _).aemeasurable

private theorem one_sub_mul_pos {x y : ℝ} (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    0 < 1 - x * y :=
  sub_pos.mpr ((mul_le_of_le_one_right hx.1 hy.2.le).trans_lt hx.2)

/-- The fixed-diagonal stability event has positive mass for unit scores below one. -/
theorem offDiagonalScoreLaw_nonblocking_pos {n : ℕ} (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    0 < offDiagonalScoreLaw n (offDiagonalNonblocking d) := by
  rw [offDiagonalScoreLaw_nonblocking_of_mem_Icc d
    (fun i ↦ ⟨⟨(hd i).1.1, (hd i).1.2.le⟩, ⟨(hd i).2.1, (hd i).2.2.le⟩⟩)]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q _ ↦
    (ENNReal.ofReal_pos.mpr (one_sub_mul_pos (hd q.val.1).1 (hd q.val.2).2)).ne')

theorem stableOffDiagonalProbabilityLaw_isProbabilityMeasure {n : ℕ} (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    IsProbabilityMeasure (stableOffDiagonalProbabilityLaw d) := by
  constructor
  rw [stableOffDiagonalProbabilityLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel (offDiagonalScoreLaw_nonblocking_pos d hd).ne'
      (measure_ne_top _ _)]

/-- Recover the unnormalized stable restriction by multiplying by its stability mass. -/
theorem offDiagonalScoreLaw_restrict_nonblocking_eq_smul_probabilityLaw {n : ℕ}
    (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d) =
      offDiagonalScoreLaw n (offDiagonalNonblocking d) • stableOffDiagonalProbabilityLaw d := by
  rw [stableOffDiagonalProbabilityLaw, smul_smul,
    ENNReal.mul_inv_cancel (offDiagonalScoreLaw_nonblocking_pos d hd).ne' (measure_ne_top _ _),
    one_smul]

private theorem stableScoreCellLaw_univ {x y : ℝ} (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    stableScoreCellLaw x y univ = ENNReal.ofReal (1 - x * y) := by
  rw [stableScoreCellLaw, Measure.restrict_apply_univ]
  exact unitScorePairLaw_nonblockingScoreCell_of_mem_Icc ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩

theorem forwardCellFlagProbabilityLaw_isProbabilityMeasure {x y : ℝ}
    (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    IsProbabilityMeasure (forwardCellFlagProbabilityLaw x y) := by
  constructor
  rw [forwardCellFlagProbabilityLaw, Measure.map_apply (measurable_forwardCellFlag x y)
    MeasurableSet.univ, preimage_univ, normalizedStableScoreCellLaw, Measure.smul_apply,
    smul_eq_mul, stableScoreCellLaw_univ hx hy]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (one_sub_mul_pos hx hy)).ne'
    ENNReal.ofReal_ne_top

/-- The exact conditional probability that one nonblocking cell is active. -/
theorem forwardCellFlagProbabilityLaw_true {x y : ℝ} (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    forwardCellFlagProbabilityLaw x y {true} = ENNReal.ofReal ((1 - x) * y / (1 - x * y)) := by
  have hX : unitScoreLaw (Ioi x) = ENNReal.ofReal (1 - x) := by
    rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioi,
      show Ioi x ∩ Icc (0 : ℝ) 1 = Ioc x 1 by
        ext u
        exact ⟨fun ⟨h, _, h₁⟩ ↦ ⟨h, h₁⟩, fun ⟨h, h₁⟩ ↦ ⟨h, hx.1.trans h.le, h₁⟩⟩,
      Real.volume_Ioc]
  have hpre : forwardCellFlag x y ⁻¹' {true} = forwardEligibleScoreCell x y := by
    ext z
    exact forwardCellFlag_eq_true
  have hactive : stableScoreCellLaw x y (forwardEligibleScoreCell x y) =
      ENNReal.ofReal ((1 - x) * y) := by
    rw [← Measure.restrict_apply_univ, stableScoreCellLaw_restrict_forwardEligible,
      ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      hX, unitScoreLaw_Iio_of_mem_Icc ⟨hy.1, hy.2.le⟩,
      ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le)]
  rw [forwardCellFlagProbabilityLaw, Measure.map_apply (measurable_forwardCellFlag x y)
    (measurableSet_singleton true), hpre, normalizedStableScoreCellLaw, Measure.smul_apply,
    smul_eq_mul, stableScoreCellLaw_univ hx hy, hactive, ENNReal.ofReal_div_of_pos
    (one_sub_mul_pos hx hy), div_eq_mul_inv, mul_comm]

/-- In the stable-cell law, conditioning on nonblocking cannot increase the active bit
probability above the female spouse score. -/
theorem forwardCellFlagProbabilityLaw_true_toReal_le {x y : ℝ}
    (hx : x ∈ Ico 0 1) (hy : y ∈ Ico 0 1) :
    (forwardCellFlagProbabilityLaw x y {true}).toReal ≤ y := by
  rw [forwardCellFlagProbabilityLaw_true hx hy, ENNReal.toReal_ofReal
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1) (one_sub_mul_pos hx hy).le),
    div_le_iff₀ (one_sub_mul_pos hx hy)]
  rw [mul_comm y (1 - x * y)]
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_left (mul_le_of_le_one_right hx.1 hy.2.le) 1) hy.1

/-- Read the bits in column `j` using the men other than its diagonal entry. -/
def forwardColumnFlag {n : ℕ} (j : Fin n) (flag : OffDiagonalCellIndex n → Bool)
    (i : {i : Fin n // i ≠ j}) : Bool :=
  flag ⟨(i.val, j), i.property⟩

theorem measurable_forwardColumnFlag {n : ℕ} (j : Fin n) : Measurable (forwardColumnFlag j) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- The bits in any single column retain their independent cell laws. -/
theorem map_forwardColumnFlag_stableOffDiagonalProbabilityLaw {n : ℕ}
    (d : DiagonalScorePairs n) (j : Fin n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) :
    Measure.map (fun z ↦ forwardColumnFlag j (forwardMaskOfScores d z))
        (stableOffDiagonalProbabilityLaw d) =
      Measure.pi (fun i : {i : Fin n // i ≠ j} ↦
        forwardCellFlagProbabilityLaw (diagonalPairAt d i.val).1 (diagonalPairAt d j).2) := by
  classical
  let inColumn (q : OffDiagonalCellIndex n) : Prop := q.val.2 = j
  let J := {i : Fin n // i ≠ j}
  let ν (q : OffDiagonalCellIndex n) :=
    forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2
  let νj (i : J) :=
    forwardCellFlagProbabilityLaw (diagonalPairAt d i.val).1 (diagonalPairAt d j).2
  let : ∀ q, IsProbabilityMeasure (ν q) :=
    fun q ↦ forwardCellFlagProbabilityLaw_isProbabilityMeasure (hd q.val.1).1 (hd q.val.2).2
  let : ∀ i, IsProbabilityMeasure (νj i) :=
    fun i ↦ forwardCellFlagProbabilityLaw_isProbabilityMeasure (hd i.val).1 (hd j).2
  let e : Subtype inColumn ≃ J :=
    { toFun := fun q ↦ ⟨q.val.val.1, q.property ▸ q.val.property⟩
      invFun := fun i ↦ ⟨⟨(i.val, j), i.property⟩, rfl⟩
      left_inv := fun q ↦ Subtype.ext (Subtype.ext (Prod.ext rfl q.property.symm))
      right_inv := fun _ ↦ rfl }
  have hproj : MeasurePreserving (fun f (q : Subtype inColumn) ↦ f q.val)
      (Measure.pi ν) (Measure.pi fun q : Subtype inColumn ↦ ν q.val) :=
    measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd ν inColumn)
  have hν : (fun q : Subtype inColumn ↦ ν q.val) = fun q ↦ νj (e q) := by
    funext q
    change forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.val.1).1
      (diagonalPairAt d q.val.val.2).2 =
      forwardCellFlagProbabilityLaw (diagonalPairAt d q.val.val.1).1 (diagonalPairAt d j).2
    rw [show q.val.val.2 = j from q.property]
  rw [hν] at hproj
  have hcol : MeasurePreserving (forwardColumnFlag j) (Measure.pi ν) (Measure.pi νj) :=
    (measurePreserving_piCongrLeft νj e).comp hproj
  exact (hcol.comp ⟨measurable_forwardMaskOfScores d,
    map_forwardMaskOfScores_stableOffDiagonalProbabilityLaw d⟩).map_eq

end LennonPittelFormalization

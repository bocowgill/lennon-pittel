module

public import LennonPittel.CoexposureScoreProduct

/-!
# Exact product score law for two fixed matchings

Mark all spouse cells of either matching. Once their scores are fixed, stability at
these cells is decided and every remaining cell must avoid the union of two rectangles.
The remaining stable cells therefore have an exact product law before normalization.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The union of the spouse cells, indexed by the actual man and woman. -/
def JointSpouseCell (μ ν : Matching n) (q : ScorePairIndex n) : Prop :=
  μ q.1 = q.2 ∨ ν q.1 = q.2

instance (μ ν : Matching n) (q : ScorePairIndex n) : Decidable (JointSpouseCell μ ν q) :=
  inferInstanceAs (Decidable (_ ∨ _))

abbrev JointSpouseIndex (μ ν : Matching n) := {q : ScorePairIndex n // JointSpouseCell μ ν q}

abbrev JointOffSpouseIndex (μ ν : Matching n) := {q : ScorePairIndex n // ¬ JointSpouseCell μ ν q}

/-- The marked score array shares a single coordinate for every common spouse cell. -/
abbrev JointSpouseScores (μ ν : Matching n) := JointSpouseIndex μ ν → ℝ × ℝ

abbrev JointOffSpouseScores (μ ν : Matching n) := JointOffSpouseIndex μ ν → ℝ × ℝ

/-- The iid law of the union of spouse cells before either stability test. -/
noncomputable def jointSpouseScoreLaw (μ ν : Matching n) : Measure (JointSpouseScores μ ν) :=
  Measure.pi fun _ ↦ unitScorePairLaw

instance (μ ν : Matching n) : IsProbabilityMeasure (jointSpouseScoreLaw μ ν) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : JointSpouseIndex μ ν ↦
    unitScorePairLaw))

/-- The iid law of cells unmatched in both matchings before stability restrictions. -/
noncomputable def jointOffSpouseScoreLaw (μ ν : Matching n) :
    Measure (JointOffSpouseScores μ ν) :=
  Measure.pi fun _ ↦ unitScorePairLaw

instance (μ ν : Matching n) : IsProbabilityMeasure (jointOffSpouseScoreLaw μ ν) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : JointOffSpouseIndex μ ν ↦
    unitScorePairLaw))

private def scoresByCell (n : ℕ) : ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  (splitScorePairs (Equiv.refl (Fin n))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2).symm

private theorem measurePreserving_scoresByCell (n : ℕ) :
    MeasurePreserving (scoresByCell n) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) :=
  ((measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).symm _).comp
    (measurePreserving_splitScorePairs (Equiv.refl (Fin n)))

private theorem scoresByCell_apply (x : ScoreProfile n) (q : ScorePairIndex n) :
    scoresByCell n x q = (x (.inl q.1) q.2, x (.inr q.2) q.1) := by
  classical
  by_cases h : q.1 = q.2
  · obtain ⟨i, j⟩ := q
    change i = j at h
    subst j
    simpa [scoresByCell, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, diagonalPairAt] using
      diagonalPairAt_splitScorePairs (Equiv.refl (Fin n)) x i
  · simpa [scoresByCell, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, h] using
      splitScorePairs_offDiagonal_apply (Equiv.refl (Fin n)) x ⟨q, h⟩

/-- Split the raw score array into marked spouse and off-both-spouse cells. -/
@[no_expose] def splitTwoMatchingScores (μ ν : Matching n) :
    ScoreProfile n ≃ᵐ JointSpouseScores μ ν × JointOffSpouseScores μ ν :=
  (scoresByCell n).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      (JointSpouseCell μ ν))

/-- Before checking stability, the two parts are independent unit score pairs. -/
theorem measurePreserving_splitTwoMatchingScores (μ ν : Matching n) :
    MeasurePreserving (splitTwoMatchingScores μ ν) (continuousScoreLaw n)
      ((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    (JointSpouseCell μ ν)).comp (measurePreserving_scoresByCell n)

theorem splitTwoMatchingScores_spouse_apply (μ ν : Matching n) (x : ScoreProfile n)
    (q : JointSpouseIndex μ ν) :
    (splitTwoMatchingScores μ ν x).1 q = (x (.inl q.val.1) q.val.2, x (.inr q.val.2) q.val.1) :=
  scoresByCell_apply x q.val

theorem splitTwoMatchingScores_offSpouse_apply (μ ν : Matching n) (x : ScoreProfile n)
    (q : JointOffSpouseIndex μ ν) :
    (splitTwoMatchingScores μ ν x).2 q = (x (.inl q.val.1) q.val.2, x (.inr q.val.2) q.val.1) :=
  scoresByCell_apply x q.val

/-- A man's marked partner score in the first matching. -/
def jointManSpouseScoreLeft {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  (d ⟨(m, μ m), Or.inl rfl⟩).1

/-- A man's marked partner score in the second matching. -/
def jointManSpouseScoreRight {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  (d ⟨(m, ν m), Or.inr rfl⟩).1

/-- A woman's marked partner score in the first matching. -/
def jointWomanSpouseScoreLeft {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  (d ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2

/-- A woman's marked partner score in the second matching. -/
def jointWomanSpouseScoreRight {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  (d ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2

@[simp] theorem jointManSpouseScoreLeft_split (μ ν : Matching n) (x : ScoreProfile n) (m : Fin n) :
    jointManSpouseScoreLeft (splitTwoMatchingScores μ ν x).1 m = x (.inl m) (μ m) := by
  rw [jointManSpouseScoreLeft, splitTwoMatchingScores_spouse_apply]

@[simp] theorem jointManSpouseScoreRight_split (μ ν : Matching n) (x : ScoreProfile n) (m : Fin n) :
    jointManSpouseScoreRight (splitTwoMatchingScores μ ν x).1 m = x (.inl m) (ν m) := by
  rw [jointManSpouseScoreRight, splitTwoMatchingScores_spouse_apply]

@[simp] theorem jointWomanSpouseScoreLeft_split (μ ν : Matching n) (x : ScoreProfile n) (w : Fin n) :
    jointWomanSpouseScoreLeft (splitTwoMatchingScores μ ν x).1 w = x (.inr w) (μ.symm w) := by
  rw [jointWomanSpouseScoreLeft, splitTwoMatchingScores_spouse_apply]

@[simp] theorem jointWomanSpouseScoreRight_split (μ ν : Matching n) (x : ScoreProfile n) (w : Fin n) :
    jointWomanSpouseScoreRight (splitTwoMatchingScores μ ν x).1 w = x (.inr w) (ν.symm w) := by
  rw [jointWomanSpouseScoreRight, splitTwoMatchingScores_spouse_apply]

/-- Acceptable scores lie outside both strict blocking rectangles. -/
def jointNonblockingScoreCell (x₁ y₁ x₂ y₂ : ℝ) : Set (ℝ × ℝ) :=
  nonblockingScoreCell x₁ y₁ ∩ nonblockingScoreCell x₂ y₂

theorem measurableSet_jointNonblockingScoreCell (x₁ y₁ x₂ y₂ : ℝ) :
    MeasurableSet (jointNonblockingScoreCell x₁ y₁ x₂ y₂) :=
  (measurableSet_Iio.prod measurableSet_Iio).compl.inter
    (measurableSet_Iio.prod measurableSet_Iio).compl

/-- The admissible score pairs at a cell, given both arrays of partner thresholds. -/
def jointNonblockingCellAt {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (q : ScorePairIndex n) : Set (ℝ × ℝ) :=
  jointNonblockingScoreCell (jointManSpouseScoreLeft d q.1) (jointWomanSpouseScoreLeft d q.2)
    (jointManSpouseScoreRight d q.1) (jointWomanSpouseScoreRight d q.2)

/-- The joint stability test on all marked cells depends only on the marked scores. -/
def jointMarkedNonblocking (μ ν : Matching n) : Set (JointSpouseScores μ ν) :=
  {d | ∀ q : JointSpouseIndex μ ν, d q ∈ jointNonblockingCellAt d q.val}

/-- The remaining joint stability tests form a rectangle in the product of cell spaces. -/
def jointOffSpouseNonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    Set (JointOffSpouseScores μ ν) :=
  univ.pi fun q ↦ jointNonblockingCellAt d q.val

theorem measurableSet_jointMarkedNonblocking (μ ν : Matching n) :
    MeasurableSet (jointMarkedNonblocking μ ν) := by
  unfold jointMarkedNonblocking
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun q ↦ ?_
  have hfst (i : JointSpouseIndex μ ν) : Measurable (fun d : JointSpouseScores μ ν ↦ (d i).1) :=
    measurable_fst.comp (measurable_pi_apply i)
  have hsnd (i : JointSpouseIndex μ ν) : Measurable (fun d : JointSpouseScores μ ν ↦ (d i).2) :=
    measurable_snd.comp (measurable_pi_apply i)
  simpa only [jointNonblockingCellAt, jointNonblockingScoreCell, nonblockingScoreCell,
    jointManSpouseScoreLeft, jointWomanSpouseScoreLeft, jointManSpouseScoreRight,
    jointWomanSpouseScoreRight, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
    ← Set.ofPred_and, Set.compl_ofPred] using
      (((measurableSet_lt (hfst q) (hfst ⟨(q.val.1, μ q.val.1), Or.inl rfl⟩)).inter
        (measurableSet_lt (hsnd q) (hsnd ⟨(μ.symm q.val.2, q.val.2),
          Or.inl (μ.apply_symm_apply q.val.2)⟩))).compl.inter
      ((measurableSet_lt (hfst q) (hfst ⟨(q.val.1, ν q.val.1), Or.inr rfl⟩)).inter
        (measurableSet_lt (hsnd q) (hsnd ⟨(ν.symm q.val.2, q.val.2),
          Or.inr (ν.apply_symm_apply q.val.2)⟩))).compl)

theorem measurableSet_jointOffSpouseNonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    MeasurableSet (jointOffSpouseNonblocking d) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_jointNonblockingScoreCell _ _ _ _

private theorem isScoreStable_iff_forall_nonblockingScoreCell (μ : Matching n)
    (x : ScoreProfile n) :
    IsScoreStable x μ ↔ ∀ q : ScorePairIndex n,
      (x (.inl q.1) q.2, x (.inr q.2) q.1) ∈
        nonblockingScoreCell (x (.inl q.1) (μ q.1)) (x (.inr q.2) (μ.symm q.2)) := by
  simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio]
  constructor
  · intro h q hlt
    have hne : μ q.1 ≠ q.2 := fun heq ↦ (lt_irrefl _) (heq ▸ hlt.1)
    exact h q.1 q.2 ⟨hne, hlt.1, hlt.2⟩
  · intro h m w hblock
    exact h (m, w) ⟨hblock.2.1, hblock.2.2⟩

/-- Checking both matchings is exactly the marked test and the off-both-spouse tests. -/
theorem twoStable_iff_splitTwoMatchingScores (μ ν : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ∧ IsScoreStable x ν ↔
      (splitTwoMatchingScores μ ν x).1 ∈ jointMarkedNonblocking μ ν ∧
      (splitTwoMatchingScores μ ν x).2 ∈
        jointOffSpouseNonblocking (splitTwoMatchingScores μ ν x).1 := by
  let d := (splitTwoMatchingScores μ ν x).1
  let v := (splitTwoMatchingScores μ ν x).2
  have hleft := isScoreStable_iff_forall_nonblockingScoreCell μ x
  have hright := isScoreStable_iff_forall_nonblockingScoreCell ν x
  have hall : IsScoreStable x μ ∧ IsScoreStable x ν ↔ ∀ q : ScorePairIndex n,
      (x (.inl q.1) q.2, x (.inr q.2) q.1) ∈ jointNonblockingCellAt d q := by
    simp only [d, jointNonblockingCellAt, jointNonblockingScoreCell, Set.mem_inter_iff,
      jointManSpouseScoreLeft_split, jointManSpouseScoreRight_split,
      jointWomanSpouseScoreLeft_split, jointWomanSpouseScoreRight_split, hleft, hright, forall_and]
  rw [hall]
  change _ ↔ d ∈ jointMarkedNonblocking μ ν ∧ v ∈ jointOffSpouseNonblocking d
  constructor
  · intro h
    constructor
    · intro q
      rw [show d q = _ from splitTwoMatchingScores_spouse_apply μ ν x q]
      exact h q.val
    · refine Set.mem_pi.mpr fun q _ ↦ ?_
      rw [show v q = _ from splitTwoMatchingScores_offSpouse_apply μ ν x q]
      exact h q.val
  · rintro ⟨hd, hv⟩ q
    by_cases hq : JointSpouseCell μ ν q
    · simpa only [d, splitTwoMatchingScores_spouse_apply] using hd ⟨q, hq⟩
    · have h := Set.mem_pi.mp hv ⟨q, hq⟩ (Set.mem_univ _)
      simpa only [v, splitTwoMatchingScores_offSpouse_apply] using h

/-- A single unmarked pair retains only the part of its score law passing both stability tests. -/
noncomputable def jointOffSpouseCellLaw {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (q : JointOffSpouseIndex μ ν) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (jointNonblockingCellAt d q.val)

instance {μ ν : Matching n} (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) :
    IsFiniteMeasure (jointOffSpouseCellLaw d q) :=
  inferInstanceAs (IsFiniteMeasure (unitScorePairLaw.restrict (jointNonblockingCellAt d q.val)))

/-- The exact unnormalized joint law on the unmarked cells is a product. -/
theorem jointOffSpouseScoreLaw_restrict_nonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d) =
      Measure.pi (jointOffSpouseCellLaw d) :=
  Measure.restrict_pi_pi _ _

theorem jointOffSpouseScoreLaw_nonblocking {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) =
      ∏ q : JointOffSpouseIndex μ ν, unitScorePairLaw (jointNonblockingCellAt d q.val) :=
  Measure.pi_pi _ _

/-- Normalize the individual cell restriction by its total mass. -/
noncomputable def normalizedJointOffSpouseCellLaw {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) : Measure (ℝ × ℝ) :=
  (jointOffSpouseCellLaw d q univ)⁻¹ • jointOffSpouseCellLaw d q

instance {μ ν : Matching n} (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) :
    IsFiniteMeasure (normalizedJointOffSpouseCellLaw d q) := by
  constructor
  rw [normalizedJointOffSpouseCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top

/-- The normalized off-both-spouse law, with the marked array held fixed. -/
noncomputable def jointOffSpouseProbabilityLaw {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    Measure (JointOffSpouseScores μ ν) :=
  (jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d))⁻¹ •
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d)

/-- The normalized law also factors. It is a probability law when the stability mass is positive. -/
theorem jointOffSpouseProbabilityLaw_eq_pi {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    jointOffSpouseProbabilityLaw d = Measure.pi (normalizedJointOffSpouseCellLaw d) := by
  symm
  refine Measure.pi_eq fun s _ ↦ ?_
  rw [jointOffSpouseProbabilityLaw, jointOffSpouseScoreLaw_nonblocking,
    jointOffSpouseScoreLaw_restrict_nonblocking, Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [normalizedJointOffSpouseCellLaw, jointOffSpouseCellLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply_univ]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (measure_ne_top unitScorePairLaw _)),
    Finset.prod_mul_distrib]

theorem jointOffSpouseProbabilityLaw_isProbabilityMeasure {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hd : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    IsProbabilityMeasure (jointOffSpouseProbabilityLaw d) := by
  constructor
  rw [jointOffSpouseProbabilityLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    ENNReal.inv_mul_cancel hd (measure_ne_top _ _)]

/-- Recover the subprobability law by multiplying its normalized law by the stability mass. -/
theorem jointOffSpouseScoreLaw_restrict_eq_smul_probabilityLaw {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hd : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    (jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d) =
      jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) • jointOffSpouseProbabilityLaw d := by
  rw [jointOffSpouseProbabilityLaw, smul_smul, ENNReal.mul_inv_cancel hd (measure_ne_top _ _),
    one_smul]

private theorem unitScoreLaw_Ioi_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 1) :
    unitScoreLaw (Ioi x) = ENNReal.ofReal (1 - x) := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioi]
  rw [show Ioi x ∩ Icc 0 1 = Ioc x 1 by
    ext u
    exact ⟨fun ⟨hlt, _, hle⟩ ↦ ⟨hlt, hle⟩, fun ⟨hlt, hle⟩ ↦ ⟨hlt, hx.1.trans hlt.le, hle⟩⟩]
  exact Real.volume_Ioc

/-- Off-both stability has positive mass whenever the marked male thresholds are below one.
The rectangle above both male thresholds is always acceptable, irrespective of female scores. -/
theorem jointOffSpouseScoreLaw_nonblocking_pos {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (hL : ∀ m, jointManSpouseScoreLeft d m ∈ Ico 0 1)
    (hR : ∀ m, jointManSpouseScoreRight d m ∈ Ico 0 1) :
    0 < jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) := by
  rw [jointOffSpouseScoreLaw_nonblocking]
  refine pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q _ ↦ ?_)
  let a := max (jointManSpouseScoreLeft d q.val.1) (jointManSpouseScoreRight d q.val.1)
  have ha : a ∈ Ico 0 1 := ⟨(hL q.val.1).1.trans (le_max_left _ _),
    max_lt (hL q.val.1).2 (hR q.val.1).2⟩
  have hsub : Ioi a ×ˢ (univ : Set ℝ) ⊆ jointNonblockingCellAt d q.val := by
    intro p hp
    have hap : a < p.1 := hp.1
    exact ⟨fun h ↦ ((le_max_left _ _).trans hap.le).not_gt (show p.1 < _ from h.1),
      fun h ↦ ((le_max_right _ _).trans hap.le).not_gt (show p.1 < _ from h.1)⟩
  have hm : unitScorePairLaw (Ioi a ×ˢ (univ : Set ℝ)) = ENNReal.ofReal (1 - a) := by
    rw [unitScorePairLaw, Measure.prod_prod, measure_univ, mul_one,
      unitScoreLaw_Ioi_of_mem_Icc ⟨ha.1, ha.2.le⟩]
  exact ((ENNReal.ofReal_pos.mpr (sub_pos.mpr ha.2)).trans_le
    (hm ▸ measure_mono hsub)).ne'

/-- Two marked male spouse scores agree at a row where the matching agrees. -/
theorem jointManSpouseScoreLeft_eq_right {μ ν : Matching n} (d : JointSpouseScores μ ν)
    {m : Fin n} (hm : μ m = ν m) :
    jointManSpouseScoreLeft d m = jointManSpouseScoreRight d m := by
  unfold jointManSpouseScoreLeft jointManSpouseScoreRight
  exact congrArg (fun q : JointSpouseIndex μ ν ↦ (d q).1)
    (Subtype.ext (Prod.ext rfl hm))

/-- With a common male threshold, the union of the two blocking rectangles is one rectangle. -/
theorem jointNonblockingScoreCell_same_male (x y₁ y₂ : ℝ) :
    jointNonblockingScoreCell x y₁ x y₂ = nonblockingScoreCell x (max y₁ y₂) := by
  ext p
  simp only [jointNonblockingScoreCell, nonblockingScoreCell, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_prod, Set.mem_Iio, lt_max_iff]
  tauto

/-- At a common row, eligibility under the second matching has exact probability
`(1-x) y₂ / (1-x max y₁ y₂)`. It requires a strictly worse male score and a strictly
better female score than the corresponding partners in the second matching. -/
theorem normalizedJointOffSpouseCellLaw_commonRow_eligible {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (q : JointOffSpouseIndex μ ν) (hm : μ q.val.1 = ν q.val.1)
    (hx : jointManSpouseScoreRight d q.val.1 ∈ Ico 0 1)
    (hy₁ : jointWomanSpouseScoreLeft d q.val.2 ∈ Icc 0 1)
    (hy₂ : jointWomanSpouseScoreRight d q.val.2 ∈ Icc 0 1) :
    let x := jointManSpouseScoreRight d q.val.1
    let y₁ := jointWomanSpouseScoreLeft d q.val.2
    let y₂ := jointWomanSpouseScoreRight d q.val.2
    normalizedJointOffSpouseCellLaw d q (Ioi x ×ˢ Iio y₂) =
      ENNReal.ofReal ((1 - x) * y₂ / (1 - x * max y₁ y₂)) := by
  dsimp only
  let x := jointManSpouseScoreRight d q.val.1
  let y₁ := jointWomanSpouseScoreLeft d q.val.2
  let y₂ := jointWomanSpouseScoreRight d q.val.2
  change normalizedJointOffSpouseCellLaw d q (Ioi x ×ˢ Iio y₂) =
    ENNReal.ofReal ((1 - x) * y₂ / (1 - x * max y₁ y₂))
  have hy : max y₁ y₂ ∈ Icc 0 1 := ⟨hy₁.1.trans (le_max_left _ _), max_le hy₁.2 hy₂.2⟩
  have hden : 0 < 1 - x * max y₁ y₂ :=
    sub_pos.mpr ((mul_le_of_le_one_right hx.1 hy.2).trans_lt hx.2)
  have hsub : Ioi x ×ˢ Iio y₂ ⊆ nonblockingScoreCell x (max y₁ y₂) :=
    fun p hp hblock ↦ (show x < p.1 from hp.1).asymm (show p.1 < x from hblock.1)
  have hcell : jointNonblockingCellAt d q.val = nonblockingScoreCell x (max y₁ y₂) := by
    rw [jointNonblockingCellAt, jointManSpouseScoreLeft_eq_right d hm]
    exact jointNonblockingScoreCell_same_male _ _ _
  rw [normalizedJointOffSpouseCellLaw, Measure.smul_apply, smul_eq_mul,
    jointOffSpouseCellLaw, hcell, Measure.restrict_apply_univ,
    unitScorePairLaw_nonblockingScoreCell_of_mem_Icc ⟨hx.1, hx.2.le⟩ hy,
    Measure.restrict_apply (measurableSet_Ioi.prod measurableSet_Iio), inter_eq_left.mpr hsub,
    unitScorePairLaw, Measure.prod_prod, unitScoreLaw_Ioi_of_mem_Icc ⟨hx.1, hx.2.le⟩,
    unitScoreLaw_Iio_of_mem_Icc hy₂, ← ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le),
    ENNReal.ofReal_div_of_pos hden, div_eq_mul_inv, mul_comm]

/-- An exact weighted joint-stability integral. The marked stability test is outside, and each
unmarked cell is integrated against its own unnormalized acceptable score-pair law. -/
theorem continuousScoreLaw_lintegral_twoStable (μ ν : Matching n)
    {C : Set (JointSpouseScores μ ν)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ C},
      f x ∂continuousScoreLaw n) =
      ∫⁻ d in C ∩ jointMarkedNonblocking μ ν, ∫⁻ v, f ((splitTwoMatchingScores μ ν).symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν := by
  let e := splitTwoMatchingScores μ ν
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (e x).1 ∈ C}
  let T := C ∩ jointMarkedNonblocking μ ν
  let E : Set (JointSpouseScores μ ν × JointOffSpouseScores μ ν) :=
    {z | z.1 ∈ T ∧ z.2 ∈ jointOffSpouseNonblocking z.1}
  let f' := f ∘ e.symm
  have hS : MeasurableSet S := (measurableSet_isScoreStable μ).inter
    ((measurableSet_isScoreStable ν).inter ((measurable_fst.comp e.measurable) hC))
  have hT : MeasurableSet T := hC.inter (measurableSet_jointMarkedNonblocking μ ν)
  have hpre : e ⁻¹' E = S := by
    ext x
    simp only [Set.mem_preimage, E, S, T, Set.mem_ofPred_eq, Set.mem_inter_iff, e]
    have h := twoStable_iff_splitTwoMatchingScores μ ν x
    tauto
  have hE_pre : E = e.symm ⁻¹' S := by
    ext z
    have h := Set.ext_iff.mp hpre (e.symm z)
    simpa only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply] using h
  have hE : MeasurableSet E := hE_pre ▸ hS.preimage e.symm.measurable
  have hf' : Measurable f' := hf.comp e.symm.measurable
  calc
    _ = ∫⁻ z in E, f' z ∂((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)) := by
      rw [← (measurePreserving_splitTwoMatchingScores μ ν).setLIntegral_comp_preimage hE hf', hpre]
      simp [f', S, e]
    _ = _ := by
      rw [← lintegral_indicator hE, lintegral_prod _ (hf'.indicator hE).aemeasurable,
        ← lintegral_indicator hT]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ T
      · rw [Set.indicator_of_mem hd, ← jointOffSpouseScoreLaw_restrict_nonblocking,
          ← lintegral_indicator (measurableSet_jointOffSpouseNonblocking d)]
        refine lintegral_congr fun v ↦ ?_
        by_cases hv : v ∈ jointOffSpouseNonblocking d <;> simp [E, f', hd, hv, e]
      · rw [Set.indicator_of_notMem hd]
        simp [E, hd]

end LennonPittelFormalization

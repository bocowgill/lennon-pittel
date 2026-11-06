module

public import LennonPittel.ContinuousScoreBridge
public import LennonPittel.CoexposureScoreRow
public import LennonPittel.ExposedRotations
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Product score laws at a fixed matching

Regrouping the independent score coordinates at a fixed matching gives independent
diagonal and off-diagonal score pairs. Each off-diagonal pair must avoid one
rectangle for the matching to be stable.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The pair `(i,j)` labels man `i` and the woman currently matched to man `j`. -/
abbrev ScorePairIndex (n : ℕ) := Fin n × Fin n

/-- The two spouse scores, indexed by diagonal pairs. -/
abbrev DiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 = q.2} → ℝ × ℝ

/-- The two directional scores for each unmatched pair. -/
abbrev OffDiagonalScorePairs (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2} → ℝ × ℝ

/-- The law of two independent uniform unit scores. -/
noncomputable def unitScorePairLaw : Measure (ℝ × ℝ) :=
  unitScoreLaw.prod unitScoreLaw

instance : IsProbabilityMeasure unitScorePairLaw :=
  inferInstanceAs (IsProbabilityMeasure (unitScoreLaw.prod unitScoreLaw))

/-- The product law of the diagonal score pairs. -/
noncomputable def diagonalScoreLaw (n : ℕ) : Measure (DiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw

instance (n : ℕ) : IsProbabilityMeasure (diagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦
    unitScorePairLaw))

/-- The product law of the off-diagonal score pairs. -/
noncomputable def offDiagonalScoreLaw (n : ℕ) : Measure (OffDiagonalScorePairs n) :=
  Measure.pi fun _ ↦ unitScorePairLaw

instance (n : ℕ) : IsProbabilityMeasure (offDiagonalScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : {q : ScorePairIndex n // q.1 ≠ q.2} ↦
    unitScorePairLaw))

private theorem measurePreserving_scoreUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ Set.univ.pi fun j ↦ s (i,j)) by
    ext x
    simp [Set.mem_pi, Prod.forall]]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product']
  simp

def manScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  Equiv.prodCongr (Equiv.refl _) μ

def womanScoreIndex {n : ℕ} (μ : Matching n) : ScorePairIndex n ≃ ScorePairIndex n :=
  (manScoreIndex μ).trans (Equiv.prodComm _ _)

def scorePairEquiv {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ (ScorePairIndex n → ℝ × ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n ↦ Fin n → ℝ)).trans
    (((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ) (manScoreIndex μ).symm)).prodCongr
    ((MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
        (womanScoreIndex μ).symm)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)).symm

private theorem scorePairEquiv_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i j : Fin n) :
    scorePairEquiv μ x (i,j) = (x (.inl i) (μ j), x (.inr (μ j)) i) := by
  change ((MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (manScoreIndex μ).symm) (fun q ↦ x (.inl q.1) q.2) (i,j),
    (MeasurableEquiv.piCongrLeft (fun _ : ScorePairIndex n ↦ ℝ)
      (womanScoreIndex μ).symm) (fun q ↦ x (.inr q.1) q.2) (i,j)) = _
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    manScoreIndex, womanScoreIndex]

private theorem measurePreserving_scorePairEquiv {n : ℕ} (μ : Matching n) :
    MeasurePreserving (scorePairEquiv μ) (continuousScoreLaw n)
      (Measure.pi fun _ : ScorePairIndex n ↦ unitScorePairLaw) := by
  exact ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ (ScorePairIndex n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).symm).comp
    ((((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (manScoreIndex μ).symm).comp
      (measurePreserving_scoreUncurry n)).prod
      ((measurePreserving_piCongrLeft (fun _ ↦ unitScoreLaw) (womanScoreIndex μ).symm).comp
        (measurePreserving_scoreUncurry n))).comp
      (measurePreserving_sumPiEquivProdPi (fun _ ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)))

/-- Regroup the score array into spouse pairs and unmatched pairs. -/
def splitScorePairs {n : ℕ} (μ : Matching n) :
    ScoreProfile n ≃ᵐ DiagonalScorePairs n × OffDiagonalScorePairs n :=
  (scorePairEquiv μ).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ScorePairIndex n ↦ ℝ × ℝ)
      fun q ↦ q.1 = q.2)

/-- Regrouping independent scores preserves their law. -/
theorem measurePreserving_splitScorePairs {n : ℕ} (μ : Matching n) :
    MeasurePreserving (splitScorePairs μ) (continuousScoreLaw n)
      ((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) :=
  (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScorePairLaw)
    fun q : ScorePairIndex n ↦ q.1 = q.2).comp
    (measurePreserving_scorePairEquiv μ)

/-- The spouse scores for the man labeled `i` and the woman matched to him. -/
def diagonalPairAt {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ × ℝ :=
  d ⟨(i,i), rfl⟩

/-- The diagonal coordinates in the split are exactly the spouse scores. -/
theorem diagonalPairAt_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (i : Fin n) :
    diagonalPairAt (splitScorePairs μ x).1 i = (x (.inl i) (μ i), x (.inr (μ i)) i) :=
  scorePairEquiv_apply μ x i i

/-- An off-diagonal coordinate gives the two scores for the same unmatched pair. -/
theorem splitScorePairs_offDiagonal_apply {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (q : {q : ScorePairIndex n // q.1 ≠ q.2}) :
    (splitScorePairs μ x).2 q =
      (x (.inl q.val.1) (μ q.val.2), x (.inr (μ q.val.2)) q.val.1) :=
  scorePairEquiv_apply μ x q.val.1 q.val.2

/-- The lower tail of a uniform unit score at a cutoff in the unit interval. -/
theorem unitScoreLaw_Iio_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    unitScoreLaw (Set.Iio x) = ENNReal.ofReal x := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  rw [show Set.Iio x ∩ Set.Icc 0 1 = Set.Ico 0 x by
    ext t
    exact ⟨fun ⟨hlt, hlo, _⟩ ↦ ⟨hlo, hlt⟩,
      fun ⟨hlo, hlt⟩ ↦ ⟨hlt, hlo, hlt.le.trans hx.2⟩⟩]
  rw [Real.volume_Ico, sub_zero]

/-- The acceptable cells avoid the rectangle in which both people prefer each other. -/
def nonblockingScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  (Set.Iio x ×ˢ Set.Iio y)ᶜ

/-- An off-diagonal cell has mass one minus the product of the two lower tails. -/
theorem unitScorePairLaw_nonblockingScoreCell (x y : ℝ) :
    unitScorePairLaw (nonblockingScoreCell x y) =
      1 - unitScoreLaw (Set.Iio x) * unitScoreLaw (Set.Iio y) := by
  rw [nonblockingScoreCell, measure_compl (measurableSet_Iio.prod measurableSet_Iio)
    (measure_ne_top _ _), measure_univ, unitScorePairLaw, Measure.prod_prod]

/-- For spouse scores in the unit interval, the removed rectangle has area `x * y`. -/
theorem unitScorePairLaw_nonblockingScoreCell_of_mem_Icc {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    unitScorePairLaw (nonblockingScoreCell x y) = ENNReal.ofReal (1 - x * y) := by
  rw [unitScorePairLaw_nonblockingScoreCell, unitScoreLaw_Iio_of_mem_Icc hx,
    unitScoreLaw_Iio_of_mem_Icc hy, ← ENNReal.ofReal_mul hx.1, ENNReal.ofReal_sub _]
  · rw [ENNReal.ofReal_one]
  · exact mul_nonneg hx.1 hy.1

/-- All off-diagonal pairs avoid their blocking rectangles for the given spouse scores. -/
def offDiagonalNonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    Set (OffDiagonalScorePairs n) :=
  Set.univ.pi fun q ↦
    nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2

/-- The nonblocking event on the off-diagonal has a finite product mass. -/
theorem offDiagonalScoreLaw_nonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) =
      ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        unitScorePairLaw
          (nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2) :=
  Measure.pi_pi _ _

/-- The stability mass is the product of one minus each blocking rectangle's area. -/
theorem offDiagonalScoreLaw_nonblocking_of_mem_Icc {n : ℕ} (d : DiagonalScorePairs n)
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Set.Icc 0 1 ∧
      (diagonalPairAt d i).2 ∈ Set.Icc 0 1) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) =
      ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        ENNReal.ofReal (1 - (diagonalPairAt d q.val.1).1 * (diagonalPairAt d q.val.2).2) := by
  rw [offDiagonalScoreLaw_nonblocking]
  exact Finset.prod_congr rfl fun q _ ↦
    unitScorePairLaw_nonblockingScoreCell_of_mem_Icc (hd q.val.1).1 (hd q.val.2).2

/-- Score stability is exactly nonblocking of every cell in the split. -/
theorem isScoreStable_iff_splitScorePairs {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    IsScoreStable x μ ↔ (splitScorePairs μ x).2 ∈
      offDiagonalNonblocking (splitScorePairs μ x).1 := by
  constructor
  · intro h q _
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]
    exact fun ⟨hm, hw⟩ ↦ h q.val.1 (μ q.val.2)
      ⟨μ.injective.ne q.property, hm, by simpa only [Equiv.symm_apply_apply] using hw⟩
  · intro h i w hw
    let j := μ.symm w
    have hj : μ j = w := μ.apply_symm_apply w
    have hij : i ≠ j := fun he ↦ hw.1 ((congrArg μ he).trans hj)
    have hcell := h (i := ⟨(i,j), hij⟩) (Set.mem_univ _)
    simp only [nonblockingScoreCell, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hcell
    apply hcell
    exact ⟨by simpa only [hj] using hw.2.1, by simpa only [hj] using hw.2.2⟩

private def diagonalIndexEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 = q.2} ≃ Fin n where
  toFun q := q.val.1
  invFun i := ⟨(i,i), rfl⟩
  left_inv q := Subtype.ext (Prod.ext rfl q.property)
  right_inv _ := rfl

/-- The two spouse score vectors are independent products of uniform scores. -/
theorem measurePreserving_diagonalScoreVectors (n : ℕ) :
    MeasurePreserving (fun d : DiagonalScorePairs n ↦
      ((fun i ↦ (diagonalPairAt d i).1), (fun i ↦ (diagonalPairAt d i).2)))
      (diagonalScoreLaw n)
      ((Measure.pi fun _ : Fin n ↦ unitScoreLaw).prod
        (Measure.pi fun _ : Fin n ↦ unitScoreLaw)) := by
  exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw)).comp
    (measurePreserving_piCongrLeft (fun _ ↦ unitScorePairLaw) (diagonalIndexEquiv n))

/-- Almost every diagonal array has both spouse scores in the unit interval. -/
theorem ae_diagonalPairAt_mem_Icc (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).1 ∈ Set.Icc 0 1 ∧
      (diagonalPairAt d i).2 ∈ Set.Icc 0 1 := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Set.Icc 0 1 := ae_restrict_mem measurableSet_Icc
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Set.Icc 0 1 ∧ z.2 ∈ Set.Icc 0 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu).and
      ((Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw)
        (ν := unitScoreLaw)).ae hu)
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i,i), rfl⟩)).eventually hp

/-- A measurable spouse cutoff and fixed-matching stability integrate against the
off-diagonal stability mass. -/
theorem continuousScoreLaw_stable_and_diagonal {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} =
      ∫⁻ d, C.indicator (fun d ↦ offDiagonalScoreLaw n (offDiagonalNonblocking d)) d
        ∂diagonalScoreLaw n := by
  let E : Set (DiagonalScorePairs n × OffDiagonalScorePairs n) :=
    {z | z.1 ∈ C ∧ z.2 ∈ offDiagonalNonblocking z.1}
  have hE_pre : E = (splitScorePairs μ).symm ⁻¹'
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} := by
    ext z
    have h := isScoreStable_iff_splitScorePairs μ ((splitScorePairs μ).symm z)
    simpa [E, and_comm] using
      (and_congr_right fun _ : z.1 ∈ C ↦ h.symm)
  have hE : MeasurableSet E := hE_pre ▸
    (((measurableSet_isScoreStable μ).inter
      ((measurable_fst.comp (splitScorePairs μ).measurable) hC)).preimage
      (splitScorePairs μ).symm.measurable)
  calc
    _ = (continuousScoreLaw n) ((splitScorePairs μ) ⁻¹' E) := by
      congr 1
      ext x
      simp [E, ← isScoreStable_iff_splitScorePairs, and_comm]
    _ = (diagonalScoreLaw n).prod (offDiagonalScoreLaw n) E :=
      (measurePreserving_splitScorePairs μ).measure_preimage hE.nullMeasurableSet
    _ = _ := by
      rw [Measure.prod_apply hE]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ C
      · rw [Set.indicator_of_mem hd]
        congr 1
        ext v
        simp [E, hd]
      · rw [Set.indicator_of_notMem hd]
        have hempty : Prod.mk d ⁻¹' E = ∅ := by
          ext v
          simp [E, hd]
        rw [hempty, measure_empty]

/-- The fixed-matching stability formula with the explicit product of rectangle areas. -/
theorem continuousScoreLaw_stable_and_diagonal_prod {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} =
      ∫⁻ d, C.indicator (fun d ↦ ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
        ENNReal.ofReal (1 - (diagonalPairAt d q.val.1).1 * (diagonalPairAt d q.val.2).2)) d
        ∂diagonalScoreLaw n := by
  rw [continuousScoreLaw_stable_and_diagonal μ hC]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalPairAt_mem_Icc n] with d hd
  by_cases hc : d ∈ C
  · simpa only [Set.indicator_of_mem hc] using offDiagonalScoreLaw_nonblocking_of_mem_Icc d hd
  · simp only [Set.indicator_of_notMem hc]

/-- Unmatched score cells grouped by the man whose successor they determine. -/
abbrev OffDiagonalScoreRows (n : ℕ) := (i : Fin n) → {j : Fin n // i ≠ j} → ℝ × ℝ

/-- Regroup unmatched score cells into rows. -/
def offDiagonalRowsEquiv (n : ℕ) : OffDiagonalScorePairs n ≃ᵐ OffDiagonalScoreRows n where
  toFun v i j := v ⟨(i,j), j.property⟩
  invFun v q := v q.val.1 ⟨q.val.2, q.property⟩
  left_inv v := by
    funext q
    cases q
    rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval fun _ ↦
    Measurable.of_eval fun _ ↦ measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun q ↦
    (measurable_pi_apply (⟨q.val.2, q.property⟩ : {j : Fin n // q.val.1 ≠ j})).comp
      (measurable_pi_apply q.val.1)

private def offDiagonalIndexEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 ≠ q.2} ≃ (i : Fin n) × {j : Fin n // i ≠ j} where
  toFun q := ⟨q.val.1, ⟨q.val.2, q.property⟩⟩
  invFun q := ⟨(q.1, q.2.val), q.2.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- Product measures on cells regroup as a product of their row measures. -/
theorem measurePreserving_offDiagonalRowsEquiv {n : ℕ}
    (m : {q : ScorePairIndex n // q.1 ≠ q.2} → Measure (ℝ × ℝ))
    [∀ q, SigmaFinite (m q)] :
    MeasurePreserving (offDiagonalRowsEquiv n) (Measure.pi m)
      (Measure.pi fun i : Fin n ↦ Measure.pi fun j : {j : Fin n // i ≠ j} ↦
        m ⟨(i,j), j.property⟩) := by
  refine MeasurePreserving.symm (offDiagonalRowsEquiv n).symm ?_
  refine ⟨(offDiagonalRowsEquiv n).symm.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  rw [show (offDiagonalRowsEquiv n).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i ↦ Set.univ.pi fun j : {j : Fin n // i ≠ j} ↦ s ⟨(i,j), j.property⟩) by
    ext v
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine ⟨fun h i j ↦ ?_, fun h q ↦ ?_⟩
    · simpa [offDiagonalRowsEquiv] using h ⟨(i,j), j.property⟩
    · simpa [offDiagonalRowsEquiv] using h q.val.1 ⟨q.val.2, q.property⟩]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv (offDiagonalIndexEquiv n).symm _ _ fun _ ↦ rfl

/-- The measure of acceptable cells in one row, without normalization. -/
noncomputable def stableScoreRowLaw {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  Measure.pi fun j ↦ unitScorePairLaw.restrict
    (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)

instance {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) :
    IsFiniteMeasure (stableScoreRowLaw d i) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun j : {j : Fin n // i ≠ j} ↦
    unitScorePairLaw.restrict
      (nonblockingScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j.val).2)))

/-- Restricting to stability preserves the product structure, with each cell
restricted to the complement of its own blocking rectangle. -/
theorem offDiagonalScoreLaw_restrict_nonblocking {n : ℕ} (d : DiagonalScorePairs n) :
    (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d) =
      Measure.pi fun q : {q : ScorePairIndex n // q.1 ≠ q.2} ↦ unitScorePairLaw.restrict
        (nonblockingScoreCell (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2) :=
  Measure.restrict_pi_pi _ _

/-- The unnormalized stable off-diagonal law is the product of stable row laws. -/
theorem measurePreserving_offDiagonalRowsEquiv_stable {n : ℕ} (d : DiagonalScorePairs n) :
    MeasurePreserving (offDiagonalRowsEquiv n)
      ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))
      (Measure.pi (stableScoreRowLaw d)) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking]
  exact measurePreserving_offDiagonalRowsEquiv _

/-- Integrate a nonnegative score weight on stable profiles with a spouse cutoff,
first integrating the off-diagonal scores restricted to the nonblocking event. -/
theorem continuousScoreLaw_lintegral_stable_and_diagonal {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}, f x
      ∂continuousScoreLaw n) =
      ∫⁻ d in C, ∫⁻ v, f ((splitScorePairs μ).symm (d,v))
        ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) ∂diagonalScoreLaw n := by
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let E : Set (DiagonalScorePairs n × OffDiagonalScorePairs n) :=
    {z | z.1 ∈ C ∧ z.2 ∈ offDiagonalNonblocking z.1}
  let f' := f ∘ (splitScorePairs μ).symm
  have hS : MeasurableSet S := (measurableSet_isScoreStable μ).inter
    ((measurable_fst.comp (splitScorePairs μ).measurable) hC)
  have hE_pre : E = (splitScorePairs μ).symm ⁻¹' S := by
    ext z
    have h := isScoreStable_iff_splitScorePairs μ ((splitScorePairs μ).symm z)
    simpa [E, S, and_comm] using (and_congr_right fun _ : z.1 ∈ C ↦ h.symm)
  have hE : MeasurableSet E := hE_pre ▸ hS.preimage (splitScorePairs μ).symm.measurable
  have hpre : (splitScorePairs μ) ⁻¹' E = S := by
    ext x
    simp [E, S, ← isScoreStable_iff_splitScorePairs, and_comm]
  have hf' : Measurable f' := hf.comp (splitScorePairs μ).symm.measurable
  calc
    _ = ∫⁻ z in E, f' z ∂((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)) := by
      rw [← (measurePreserving_splitScorePairs μ).setLIntegral_comp_preimage hE hf', hpre]
      simp [f', S]
    _ = _ := by
      rw [← lintegral_indicator hE,
        lintegral_prod _ (hf'.indicator hE).aemeasurable, ← lintegral_indicator hC]
      refine lintegral_congr fun d ↦ ?_
      by_cases hd : d ∈ C
      · have hnon : MeasurableSet (offDiagonalNonblocking d) :=
          MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
        rw [Set.indicator_of_mem hd, ← lintegral_indicator hnon]
        refine lintegral_congr fun v ↦ ?_
        by_cases hv : v ∈ offDiagonalNonblocking d <;> simp [E, f', hd, hv]
      · rw [Set.indicator_of_notMem hd]
        simp [E, hd]

/-- The weighted fixed-matching score integral, with the inner integral on the
product of unnormalized stable successor rows. -/
theorem continuousScoreLaw_lintegral_stable_and_diagonal_rows {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}, f x
      ∂continuousScoreLaw n) =
      ∫⁻ d in C, ∫⁻ r, f ((splitScorePairs μ).symm (d,(offDiagonalRowsEquiv n).symm r))
        ∂(Measure.pi (stableScoreRowLaw d)) ∂diagonalScoreLaw n := by
  rw [continuousScoreLaw_lintegral_stable_and_diagonal μ hC hf]
  refine lintegral_congr fun d ↦ ?_
  rw [(measurePreserving_offDiagonalRowsEquiv_stable d).lintegral_map_equiv _
    (offDiagonalRowsEquiv n)]
  simp only [MeasurableEquiv.symm_apply_apply]

/-- Splitting a row into a chosen cell and its competitors preserves the product measure. -/
theorem measurePreserving_rowTargetAndCompetitors {ι X : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace X] (m : ι → Measure X)
    [∀ i, SigmaFinite (m i)] (j : ι) :
    MeasurePreserving (fun r : ι → X ↦ (r j, fun k : {k : ι // k ≠ j} ↦ r k.val))
      (Measure.pi m) ((m j).prod (Measure.pi fun k : {k : ι // k ≠ j} ↦ m k.val)) := by
  let : Unique {k : ι // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k ↦ Subtype.ext k.property⟩
  let : Fintype {k : ι // k = j} := Subtype.fintype (fun k ↦ k = j)
  exact ((measurePreserving_piUnique (fun k : {k : ι // k = j} ↦ m k.val)).prod
    (MeasurePreserving.id _)).comp (measurePreserving_piEquivPiSubtypeProd m fun k ↦ k = j)

/-- At almost every diagonal, the product of stable rows reconstructs
almost surely tie-free stable score profiles. -/
theorem ae_diagonal_ae_stableRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ᵐ r ∂Measure.pi (stableScoreRowLaw d),
      let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ := by
  have ht : ∀ᵐ z ∂((diagonalScoreLaw n).prod (offDiagonalScoreLaw n)),
      ∀ row, Function.Injective ((splitScorePairs μ).symm z row) :=
    ((measurePreserving_splitScorePairs μ).symm).quasiMeasurePreserving.ae (ae_injective_rows n)
  filter_upwards [Measure.ae_ae_of_ae_prod ht] with d hd
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  have hv : ∀ᵐ v ∂(offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d),
      (∀ row, Function.Injective ((splitScorePairs μ).symm (d,v) row)) ∧
        v ∈ offDiagonalNonblocking d :=
    (ae_restrict_of_ae hd).and (ae_restrict_mem hnon)
  have he := (measurePreserving_offDiagonalRowsEquiv_stable d).symm
  filter_upwards [he.quasiMeasurePreserving.ae hv] with r hr
  refine ⟨hr.1, (isScoreStable_iff_splitScorePairs μ _).2 ?_⟩
  simpa only [MeasurableEquiv.apply_symm_apply] using hr.2

/-- A chosen cell is eligible, and no competing cell beats its male score while
the woman in that cell would accept the man. -/
def scoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (j : {j : Fin n // i ≠ j}) : Set ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  {r | (diagonalPairAt d i).1 < (r j).1 ∧ (r j).2 < (diagonalPairAt d j.val).2 ∧
    ∀ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
      ¬ ((r k.val).1 < (r j).1 ∧ (r k.val).2 < (diagonalPairAt d k.val.val).2)}

/-- At a stable tie-free array, every rank successor satisfies the score-row event. -/
theorem scoreRowSuccessorEvent_of_isSuccessor {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (i : Fin n) (j : {j : Fin n // i ≠ j}) (hj : IsSuccessor (profileOfScores x) μ i (μ j.val)) :
    offDiagonalRowsEquiv n (splitScorePairs μ x).2 i ∈
      scoreRowSuccessorEvent (splitScorePairs μ x).1 i j := by
  have hcell (a : {a : Fin n // i ≠ a}) :
      offDiagonalRowsEquiv n (splitScorePairs μ x).2 i a =
        (x (.inl i) (μ a.val), x (.inr (μ a.val)) i) := by
    simpa [offDiagonalRowsEquiv] using
      splitScorePairs_offDiagonal_apply μ x ⟨(i,a.val),a.property⟩
  simp only [scoreRowSuccessorEvent, Set.mem_ofPred_eq, hcell, diagonalPairAt_splitScorePairs]
  have hman (w w' : Fin n) : (profileOfScores x).manRank i w < (profileOfScores x).manRank i w'
      ↔ x (.inl i) w < x (.inl i) w' :=
    rankPermutation_lt_iff (ht (.inl i)) w w'
  have hwoman (w m m' : Fin n) :
      (profileOfScores x).womanRank w m < (profileOfScores x).womanRank w m'
        ↔ x (.inr w) m < x (.inr w) m' :=
    rankPermutation_lt_iff (ht (.inr w)) m m'
  refine ⟨(hman _ _).1 hj.eligible.1, ?_, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using (hwoman _ _ _).1 hj.eligible.2
  · intro k hk
    have hwk : x (.inr (μ k.val.val)) i <
        x (.inr (μ k.val.val)) (μ.symm (μ k.val.val)) := by
      simpa only [Equiv.symm_apply_apply] using hk.2
    have hmle : x (.inl i) (μ i) ≤ x (.inl i) (μ k.val.val) :=
      le_of_not_gt fun h ↦ hs i (μ k.val.val) ⟨μ.injective.ne k.val.property, h, hwk⟩
    have hmne := (ht (.inl i)).ne (μ.injective.ne k.val.property)
    have hel : IsEligibleSuccessor (profileOfScores x) μ i (μ k.val.val) :=
      ⟨(hman _ _).2 (lt_of_le_of_ne hmle hmne), (hwoman _ _ _).2 hwk⟩
    exact (not_lt_of_ge (hj.min_rank _ hel)) ((hman _ _).2 hk.1)

/-- Rank successors of reconstructed profiles lie in the corresponding row events. -/
theorem scoreRowSuccessorEvent_of_isSuccessor_reconstructed {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hs : IsScoreStable ((splitScorePairs μ).symm (d,(offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d,(offDiagonalRowsEquiv n).symm r) row))
    (hj : IsSuccessor (profileOfScores ((splitScorePairs μ).symm
      (d,(offDiagonalRowsEquiv n).symm r))) μ i (μ j.val)) :
    r i ∈ scoreRowSuccessorEvent d i j := by
  simpa only [MeasurableEquiv.apply_symm_apply] using
    scoreRowSuccessorEvent_of_isSuccessor μ _ hs ht i j hj

/-- The product of the row masses is the total stable off-diagonal mass. -/
theorem prod_stableScoreRowLaw_univ {n : ℕ} (d : DiagonalScorePairs n) :
    (∏ i, stableScoreRowLaw d i univ) =
      offDiagonalScoreLaw n (offDiagonalNonblocking d) := by
  have h := (measurePreserving_offDiagonalRowsEquiv_stable d).measure_preimage
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simpa only [Set.preimage_univ, Measure.restrict_apply_univ, Measure.pi_univ] using h.symm

/-- The score-row successor event is measurable. -/
theorem measurableSet_scoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    MeasurableSet (scoreRowSuccessorEvent d i j) :=
  (measurableSet_scoreSuccessorPairEvent (diagonalPairAt d i).1 (diagonalPairAt d j.val).2
    (fun k : {k : {k : Fin n // i ≠ k} // k ≠ j} ↦ (diagonalPairAt d k.val.val).2)).preimage
    (measurePreserving_rowTargetAndCompetitors
      (fun _ : {k : Fin n // i ≠ k} ↦ unitScorePairLaw) j).measurable

/-- The actual unnormalized successor mass on the stable row satisfies the
row-probability bound, multiplied by the mass of the row. -/
theorem stableScoreRowLaw_successor_le {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hx : (diagonalPairAt d i).1 ∈ Ico (0 : ℝ) 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc (0 : ℝ) 1)
    (hsum : 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, (diagonalPairAt d k.val.val).2) :
    stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) ≤
      stableScoreRowLaw d i univ *
        ENNReal.ofReal ((diagonalPairAt d j.val).2 /
          ((1 - (diagonalPairAt d i).1 * (diagonalPairAt d j.val).2) *
            (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, (diagonalPairAt d k.val.val).2))) := by
  let x := (diagonalPairAt d i).1
  let y (k : {k : Fin n // i ≠ k}) := (diagonalPairAt d k.val).2
  let m (k : {k : Fin n // i ≠ k}) := rowNonblockingLaw x (y k)
  let E := scoreSuccessorPairEvent x (y j) (fun k : {k // k ≠ j} ↦ y k.val)
  have hpres := measurePreserving_rowTargetAndCompetitors m j
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have heq : stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) E :=
    hpres.measure_preimage hE.nullMeasurableSet
  have ht : stableScoreRowLaw d i univ =
      m j univ * ∏ k : {k // k ≠ j}, m k.val univ := by
    have h := hpres.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    calc
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) univ :=
        by simpa only [Set.preimage_univ, stableScoreRowLaw, m, x, y, unitScorePairLaw,
          rowNonblockingLaw, nonblockingScoreCell] using h
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) (univ ×ˢ univ) :=
        by rw [Set.univ_prod_univ]
      _ = _ := by rw [Measure.prod_prod, Measure.pi_univ]
  rw [heq, ht]
  exact scoreSuccessorPairEvent_mass_le hx (hy j.val) (fun k ↦ hy k.val.val) hsum

end LennonPittelFormalization

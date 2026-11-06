module

public import LennonPittel.ForwardSuccessorOutcome
public import LennonPittel.TruncatedScoreRowIntegral
public import LennonPittel.TwoStableScoreProduct

/-!
# Common forward rows under two-stable conditioning

Only the cells belonging to either matching are fixed. Conditioning on the
two stability tests preserves the product law on the remaining cells. At a
man with the same partner in both matchings, the union of the two forbidden
rectangles has the common male threshold and the larger female threshold.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Men who have the same partner in both marked matchings. -/
abbrev CommonMan {n : ℕ} (μ ν : Matching n) := {i : Fin n // μ i = ν i}

/-- Candidate husbands are indexed in the second matching; the current man is omitted. -/
abbrev CommonRowCandidate {n : ℕ} {μ ν : Matching n} (i : CommonMan μ ν) :=
  {j : Fin n // i.val ≠ j}

/-- In a common row, every candidate other than its partner is off both matchings. -/
def commonOffSpouseCell {n : ℕ} {μ ν : Matching n} (i : CommonMan μ ν)
    (j : CommonRowCandidate i) : JointOffSpouseIndex μ ν :=
  ⟨(i.val, ν j.val), by
    rintro (h | h)
    · exact j.property (ν.injective (i.property.symm.trans h))
    · exact j.property (ν.injective h)⟩

/-- Read the common rows, with women indexed by their husbands in the second matching. -/
def jointCommonRows {n : ℕ} {μ ν : Matching n} (v : JointOffSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i) : ℝ × ℝ :=
  v (commonOffSpouseCell i j)

/-- Restrict a cell to the complement of the blocking rectangle and normalize it. -/
noncomputable def commonRowCellLaw (x b : ℝ) : Measure (ℝ × ℝ) :=
  (rowNonblockingLaw x b univ)⁻¹ • rowNonblockingLaw x b

instance (x b : ℝ) : IsFiniteMeasure (commonRowCellLaw x b) := by
  constructor
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul, mul_comm]
  exact (ENNReal.mul_inv_ne_top _).lt_top

theorem jointCommonCellLaw_eq {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i) :
    normalizedJointOffSpouseCellLaw d (commonOffSpouseCell i j) =
      commonRowCellLaw (jointManSpouseScoreRight d i.val)
        (max (jointWomanSpouseScoreLeft d (ν j.val))
          (jointWomanSpouseScoreRight d (ν j.val))) := by
  have h : jointOffSpouseCellLaw d (commonOffSpouseCell i j) =
      rowNonblockingLaw (jointManSpouseScoreRight d i.val)
        (max (jointWomanSpouseScoreLeft d (ν j.val))
          (jointWomanSpouseScoreRight d (ν j.val))) := by
    unfold jointOffSpouseCellLaw jointNonblockingCellAt
    change unitScorePairLaw.restrict (jointNonblockingScoreCell
      (jointManSpouseScoreLeft d i.val) (jointWomanSpouseScoreLeft d (ν j.val))
      (jointManSpouseScoreRight d i.val) (jointWomanSpouseScoreRight d (ν j.val))) = _
    rw [jointManSpouseScoreLeft_eq_right d i.property, jointNonblockingScoreCell_same_male]
    rfl
  simp only [normalizedJointOffSpouseCellLaw, commonRowCellLaw, h]

/-- The conditional law of one common row, including all potential targets. -/
noncomputable def jointCommonRowLaw {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) : Measure (CommonRowCandidate i → ℝ × ℝ) :=
  Measure.pi fun j ↦ normalizedJointOffSpouseCellLaw d (commonOffSpouseCell i j)

private theorem normalizedJointOffSpouseCellLaw_isProbabilityMeasure
    {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0)
    (q : JointOffSpouseIndex μ ν) :
    IsProbabilityMeasure (normalizedJointOffSpouseCellLaw d q) := by
  rw [jointOffSpouseScoreLaw_nonblocking] at hpos
  constructor
  rw [normalizedJointOffSpouseCellLaw, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel _ (measure_ne_top _ _)]
  rw [jointOffSpouseCellLaw, Measure.restrict_apply_univ]
  exact Finset.prod_ne_zero_iff.mp hpos q (Finset.mem_univ q)

theorem jointCommonRowLaw_isProbabilityMeasure {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0)
    (i : CommonMan μ ν) : IsProbabilityMeasure (jointCommonRowLaw d i) := by
  let (j : CommonRowCandidate i) :=
    normalizedJointOffSpouseCellLaw_isProbabilityMeasure d hpos (commonOffSpouseCell i j)
  exact inferInstanceAs (IsProbabilityMeasure
    (Measure.pi fun j ↦ normalizedJointOffSpouseCellLaw d (commonOffSpouseCell i j)))

private theorem measurePreserving_pi_comp_embedding {ι κ X : Type*}
    [Fintype ι] [Fintype κ] [MeasurableSpace X] (m : ι → Measure X)
    [∀ i, IsProbabilityMeasure (m i)] (e : κ ↪ ι) :
    MeasurePreserving (fun v : ι → X ↦ fun k ↦ v (e k)) (Measure.pi m)
      (Measure.pi fun k ↦ m (e k)) := by
  classical
  let : Fintype (Set.range e) := Subtype.fintype (· ∈ Set.range e)
  let E := Equiv.ofInjective e e.injective
  let m' : κ → Measure X := fun k ↦ m (e k)
  have hm (i : Set.range e) : m' (E.symm i) = m i.val := by
    change m ((E (E.symm i)).val) = m i.val
    rw [E.apply_symm_apply]
  have h₁ := measurePreserving_fst.comp
    (measurePreserving_piEquivPiSubtypeProd m (· ∈ Set.range e))
  have h₂ := measurePreserving_piCongrLeft m' E.symm
  simp only [hm] at h₂
  convert h₂.comp h₁ using 1
  funext v k
  change v (e k) = (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ X) E.symm
    (fun i ↦ v i.val)) k
  have hk := (MeasurableEquiv.piCongrLeft_apply_apply E.symm (β := fun _ : κ ↦ X)
    (fun i ↦ v i.val) (E k)).symm
  rw [E.symm_apply_apply] at hk
  exact hk

private def regroupRows {ι X : Type*} {κ : ι → Type*} [MeasurableSpace X] :
    ((i : ι) × κ i → X) ≃ᵐ ((i : ι) → κ i → X) where
  toFun v i j := v ⟨i, j⟩
  invFun v q := v q.1 q.2
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval fun _ ↦
    Measurable.of_eval fun _ ↦ measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun q ↦
    (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)

private theorem measurePreserving_regroupRows {ι X : Type*} {κ : ι → Type*}
    [MeasurableSpace X] [Fintype ι] [∀ i, Fintype (κ i)]
    (m : ((i : ι) × κ i) → Measure X) [∀ q, SigmaFinite (m q)] :
    MeasurePreserving regroupRows (Measure.pi m)
      (Measure.pi fun i : ι ↦ Measure.pi fun j : κ i ↦ m ⟨i, j⟩) := by
  refine MeasurePreserving.symm regroupRows.symm ?_
  refine ⟨regroupRows.symm.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have hpre : regroupRows.symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi fun j ↦ s ⟨i, j⟩) := by
    ext v
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    exact ⟨fun h i j ↦ h ⟨i, j⟩, fun h q ↦ h q.1 q.2⟩
  rw [hpre]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_sigma' _).symm

/-- The projected common rows have an exact product law; no image-event test is applied. -/
theorem measurePreserving_jointCommonRows {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    MeasurePreserving jointCommonRows (jointOffSpouseProbabilityLaw d)
      (Measure.pi (jointCommonRowLaw d)) := by
  let e : ((i : CommonMan μ ν) × CommonRowCandidate i) ↪ JointOffSpouseIndex μ ν :=
    ⟨fun q ↦ commonOffSpouseCell q.1 q.2, by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have hi : i = i' :=
        Subtype.ext (congrArg (fun q : JointOffSpouseIndex μ ν ↦ q.val.1) h)
      subst i'
      have hj : j = j' := Subtype.ext (ν.injective
        (congrArg (fun q : JointOffSpouseIndex μ ν ↦ q.val.2) h))
      rw [hj]⟩
  let (q : JointOffSpouseIndex μ ν) :
    IsProbabilityMeasure (normalizedJointOffSpouseCellLaw d q) :=
    normalizedJointOffSpouseCellLaw_isProbabilityMeasure d hpos q
  rw [jointOffSpouseProbabilityLaw_eq_pi]
  exact (measurePreserving_regroupRows (fun q ↦ normalizedJointOffSpouseCellLaw d (e q))).comp
    (measurePreserving_pi_comp_embedding _ e)

/-- The fraction of the acceptable cell on which this candidate is forward eligible. -/
noncomputable def commonEligibilityWeight (x y b : ℝ) : ℝ :=
  (1 - x) * y / (1 - x * b)

private theorem commonDen_pos {x b : ℝ} (hx : x ∈ Ico 0 1) (hb : b ∈ Icc 0 1) :
    0 < 1 - x * b :=
  sub_pos.mpr ((mul_le_of_le_one_right hx.1 hb.2).trans_lt hx.2)

private theorem commonRowCellLaw_isProbabilityMeasure {x b : ℝ}
    (hx : x ∈ Ico 0 1) (hb : b ∈ Icc 0 1) :
    IsProbabilityMeasure (commonRowCellLaw x b) := by
  constructor
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel]
  · rw [rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb]
    exact ENNReal.ofReal_ne_zero_iff.mpr (commonDen_pos hx hb)
  · exact measure_ne_top _ _

private theorem unitScoreLaw_Ico_of_mem_Icc {x u : ℝ} (hx : 0 ≤ x) (hu : u ≤ 1) :
    unitScoreLaw (Ico x u) = ENNReal.ofReal (u - x) := by
  have hsub : Ico x u ⊆ Icc 0 1 := fun _ h ↦ ⟨hx.trans h.1, h.2.le.trans hu⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr hsub, Real.volume_Ico]

private theorem commonRowCellLaw_competitor_better {x y b u : ℝ} (hx : x ∈ Ico 0 1)
    (hy : y ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hyb : y ≤ b) (hu : u ∈ Icc x 1) :
    commonRowCellLaw x b (Iio u ×ˢ Iio y) = ENNReal.ofReal ((u - x) * y / (1 - x * b)) := by
  have hinter : (Iio u ×ˢ Iio y) ∩ (Iio x ×ˢ Iio b)ᶜ = Ico x u ×ˢ Iio y := by
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Iio, mem_Ico, mem_compl_iff]
    exact ⟨fun h ↦ ⟨⟨le_of_not_gt fun hp ↦ h.2 ⟨hp, h.1.2.trans_le hyb⟩, h.1.1⟩, h.1.2⟩,
      fun h ↦ ⟨⟨h.1.2, h.2⟩, fun hp ↦ h.1.1.not_gt hp.1⟩⟩
  rw [commonRowCellLaw, Measure.smul_apply, smul_eq_mul,
    rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb, rowNonblockingLaw,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Iio), hinter, Measure.prod_prod,
    unitScoreLaw_Ico_of_mem_Icc hx.1 hu.2, unitScoreLaw_Iio_of_mem_Icc hy,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hu.1),
    ENNReal.ofReal_div_of_pos (commonDen_pos hx hb), div_eq_mul_inv, mul_comm]

private theorem commonRowCellLaw_avoiding {x y b u : ℝ} (hx : x ∈ Ico 0 1)
    (hy : y ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hyb : y ≤ b) (hu : u ∈ Icc x 1) :
    commonRowCellLaw x b (Iio u ×ˢ Iio y)ᶜ =
      ENNReal.ofReal (1 - (u - x) * y / (1 - x * b)) := by
  let := commonRowCellLaw_isProbabilityMeasure hx hb
  rw [measure_compl (measurableSet_Iio.prod measurableSet_Iio) (measure_ne_top _ _),
    measure_univ, commonRowCellLaw_competitor_better hx hy hb hyb hu,
    ENNReal.ofReal_sub _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hu.1) hy.1)
      (commonDen_pos hx hb).le), ENNReal.ofReal_one]

theorem commonEligibilityWeight_bounds {x y b : ℝ} (hx : x ∈ Ico 0 1)
    (hy : y ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    (1 - x) * y ≤ commonEligibilityWeight x y b ∧ commonEligibilityWeight x y b ≤ y := by
  have hnum : 0 ≤ (1 - x) * y := mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1
  have hden := commonDen_pos hx hb
  unfold commonEligibilityWeight
  constructor
  · rw [le_div_iff₀ hden]
    exact mul_le_of_le_one_right hnum (sub_le_self _ (mul_nonneg hx.1 hb.1))
  · rw [div_le_iff₀ hden, mul_comm y]
    exact mul_le_mul_of_nonneg_right
      (sub_le_sub_left (mul_le_of_le_one_right hx.1 hb.2) _) hy.1

/-- Exact successor mass for independent cells with a common male threshold
and possibly different female thresholds for blocking and eligibility. -/
theorem commonRowSuccessorPairEvent_mass {ι : Type*} [Fintype ι] {x v b₀ : ℝ}
    {y b : ι → ℝ} (hx : x ∈ Ico 0 1) (hv : v ∈ Icc 0 1) (hb₀ : b₀ ∈ Icc 0 1)
    (hy : ∀ k, y k ∈ Icc 0 1) (hb : ∀ k, b k ∈ Icc 0 1)
    (hyb : ∀ k, y k ≤ b k) :
    ((commonRowCellLaw x b₀).prod (Measure.pi fun k ↦ commonRowCellLaw x (b k)))
        (scoreSuccessorPairEvent x v y) =
      ENNReal.ofReal (commonEligibilityWeight x v b₀ *
        scoreRowMass Finset.univ (fun k ↦ commonEligibilityWeight x (y k) (b k)) 0 1) := by
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let m := commonRowCellLaw x b₀
  let m' := Measure.pi fun k ↦ commonRowCellLaw x (b k)
  let r (k : ι) := y k / (1 - x * b k)
  let F (u : ℝ) := scoreRowKernel Finset.univ r (u - x)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hF : Continuous F := (continuous_scoreRowKernel Finset.univ r).comp
    (continuous_id.sub continuous_const)
  have hnonneg (u : ℝ) (hu : u ∈ Icc x 1) : ∀ k, 0 ≤ 1 - (u - x) * r k := by
    intro k
    apply sub_nonneg.mpr
    calc
      _ ≤ (1 - x) * r k := mul_le_mul_of_nonneg_right (sub_le_sub_right hu.2 _)
        (div_nonneg (hy k).1 (commonDen_pos hx (hb k)).le)
      _ = commonEligibilityWeight x (y k) (b k) := (mul_div_assoc ..).symm
      _ ≤ y k := (commonEligibilityWeight_bounds hx (hy k) (hb k)).2
      _ ≤ 1 := (hy k).2
  have hsupp : ∀ᵐ uv ∂m, uv ∈ Icc 0 1 ×ˢ Icc 0 1 := by
    apply Measure.ae_smul_measure
    unfold rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  have hsection :
      (fun uv ↦ m' (Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y)) =ᵐ[m]
        T.indicator (fun uv ↦ ENNReal.ofReal (F uv.1)) := by
    filter_upwards [hsupp] with uv huv
    by_cases ht : uv ∈ T
    · have hu : uv.1 ∈ Icc x 1 := ⟨(show x < uv.1 from ht.1).le, huv.1.2⟩
      have hpre : Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y =
          univ.pi (fun k ↦ (Iio uv.1 ×ˢ Iio (y k))ᶜ) := by
        ext z
        simp only [mem_preimage, scoreSuccessorPairEvent, mem_ofPred_eq, mem_pi, mem_univ,
          true_implies, mem_compl_iff, mem_prod, mem_Iio]
        exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ht.1, ht.2, h⟩⟩
      rw [hpre, Set.indicator_of_mem ht]
      change (Measure.pi _ _) = ENNReal.ofReal (F uv.1)
      rw [Measure.pi_pi]
      simp_rw [commonRowCellLaw_avoiding hx (hy _) (hb _) (hyb _) hu]
      unfold F scoreRowKernel r
      simp only [mul_div_assoc]
      exact (ENNReal.ofReal_prod_of_nonneg fun k _ ↦ hnonneg uv.1 hu k).symm
    · have hpre : Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        exact fun z hz ↦ ht ⟨hz.1, hz.2.1⟩
      rw [hpre, measure_empty, Set.indicator_of_notMem ht]
  change (m.prod m') (scoreSuccessorPairEvent x v y) = _
  rw [Measure.prod_apply (measurableSet_scoreSuccessorPairEvent x v y),
    lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio b₀ : Set (ℝ × ℝ))ᶜ :=
    fun _ h h' ↦ (show x < _ from h.1).asymm (show _ < x from h'.1)
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  have hrestrict : m.restrict T =
      (ENNReal.ofReal (1 - x * b₀))⁻¹ •
        ((volume.restrict (Ioc x 1)).prod (unitScoreLaw.restrict (Iio v))) := by
    dsimp [m, commonRowCellLaw]
    rw [Measure.restrict_smul, rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb₀,
      rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    change _ • (unitScoreLaw.prod unitScoreLaw).restrict (Ioi x ×ˢ Iio v) = _
    rw [← Measure.prod_restrict, hleft]
  have hoff (t : ℝ) : F (x + (1 - x) * t) =
      scoreRowKernel Finset.univ (fun k ↦ commonEligibilityWeight x (y k) (b k)) t := by
    unfold F scoreRowKernel
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    unfold r commonEligibilityWeight
    ring
  have haff : (1 - x) *
      scoreRowMass Finset.univ (fun k ↦ commonEligibilityWeight x (y k) (b k)) 0 1 =
        ∫ u in x..1, F u := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
      F (1 - x) x
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one, hoff] at h
    simpa only [show x + (1 - x) = 1 by ring, scoreRowMass] using h
  rw [hrestrict, lintegral_smul_measure]
  rw [show (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (F uv.1)) =
      (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (F uv.1) * (1 : ℝ≥0∞)) by simp only [mul_one]]
  rw [lintegral_prod_mul hF.measurable.ennreal_ofReal.aemeasurable measurable_const.aemeasurable,
    lintegral_const, one_mul, Measure.restrict_apply_univ, unitScoreLaw_Iio_of_mem_Icc hv,
    smul_eq_mul]
  have hmass :
      (∫⁻ u in Ioc x 1, ENNReal.ofReal (F u)) = ENNReal.ofReal (∫ u in x..1, F u) := by
    rw [intervalIntegral.integral_of_le hx.2.le, ofReal_integral_eq_lintegral_ofReal]
    · exact (hF.intervalIntegrable _ _).1
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc x 1))]
        with u hu
      exact Finset.prod_nonneg fun k _ ↦ hnonneg u ⟨hu.1.le, hu.2⟩ k
  rw [hmass, ← haff, ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le)]
  have hcoef :
      ENNReal.ofReal (commonEligibilityWeight x v b₀) =
        (ENNReal.ofReal (1 - x * b₀))⁻¹ * (ENNReal.ofReal (1 - x) * ENNReal.ofReal v) := by
    rw [commonEligibilityWeight, ENNReal.ofReal_div_of_pos (commonDen_pos hx hb₀),
      ENNReal.ofReal_mul (sub_nonneg.mpr hx.2.le), div_eq_mul_inv, mul_comm]
  rw [ENNReal.ofReal_mul ((mul_nonneg (sub_nonneg.mpr hx.2.le) hv.1).trans
    (commonEligibilityWeight_bounds hx hv hb₀).1), hcoef]
  ac_rfl

/-- The second matching's own spouse scores, indexed as a single marked diagonal. -/
def jointRightDiagonal {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    DiagonalScorePairs n :=
  fun q ↦ (jointManSpouseScoreRight d q.val.1, jointWomanSpouseScoreRight d (ν q.val.1))

@[simp]
theorem diagonalPairAt_jointRightDiagonal {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (j : Fin n) :
    diagonalPairAt (jointRightDiagonal d) j =
      (jointManSpouseScoreRight d j, jointWomanSpouseScoreRight d (ν j)) :=
  rfl

@[simp]
theorem jointRightDiagonal_split {n : ℕ} (μ ν : Matching n) (x : ScoreProfile n) :
    jointRightDiagonal (splitTwoMatchingScores μ ν x).1 = (splitScorePairs ν x).1 := by
  funext q
  obtain ⟨⟨i, j⟩, h⟩ := q
  change i = j at h
  subst j
  change diagonalPairAt (jointRightDiagonal (splitTwoMatchingScores μ ν x).1) i =
    diagonalPairAt (splitScorePairs ν x).1 i
  simp [diagonalPairAt_splitScorePairs]

/-- At a stable tie-free array, the common-row score event is the actual rank successor. -/
theorem jointCommonRowSuccessorEvent_iff_isSuccessor {n : ℕ} (μ ν : Matching n)
    (x : ScoreProfile n) (hs : IsScoreStable x ν) (ht : ∀ r, Function.Injective (x r))
    (i : CommonMan μ ν) (j : CommonRowCandidate i) :
    jointCommonRows (splitTwoMatchingScores μ ν x).2 i ∈
        scoreRowSuccessorEvent (jointRightDiagonal (splitTwoMatchingScores μ ν x).1) i.val j ↔
      IsSuccessor (profileOfScores x) ν i.val (ν j.val) := by
  have hrow : jointCommonRows (splitTwoMatchingScores μ ν x).2 i =
      offDiagonalRowsEquiv n (splitScorePairs ν x).2 i.val := by
    funext k
    change (splitTwoMatchingScores μ ν x).2 (commonOffSpouseCell i k) =
      (splitScorePairs ν x).2 ⟨(i.val, k.val), k.property⟩
    rw [splitTwoMatchingScores_offSpouse_apply, splitScorePairs_offDiagonal_apply]
    rfl
  rw [hrow, jointRightDiagonal_split]
  exact ⟨isSuccessor_of_scoreRowSuccessorEvent ν x ht i.val j,
    scoreRowSuccessorEvent_of_isSuccessor ν x hs ht i.val j⟩

/-- The exact eligible weight in a common row, indexed by the second matching. -/
noncomputable def jointCommonEligibility {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (i : CommonMan μ ν) (j : Fin n) : ℝ :=
  commonEligibilityWeight (jointManSpouseScoreRight d i.val)
    (jointWomanSpouseScoreRight d (ν j))
    (max (jointWomanSpouseScoreLeft d (ν j)) (jointWomanSpouseScoreRight d (ν j)))

/-- The common-row probability of an arc is its eligibility weight times the
independent competitor integral. -/
theorem jointCommonRowSuccessorEvent_mass {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) =
      ENNReal.ofReal (jointCommonEligibility d i j.val *
        scoreRowMass Finset.univ
          (fun k : {k : CommonRowCandidate i // k ≠ j} ↦
            jointCommonEligibility d i k.val.val) 0 1) := by
  let x := jointManSpouseScoreRight d i.val
  let y (k : CommonRowCandidate i) := jointWomanSpouseScoreRight d (ν k.val)
  let b (k : CommonRowCandidate i) :=
    max (jointWomanSpouseScoreLeft d (ν k.val)) (y k)
  let m (k : CommonRowCandidate i) := commonRowCellLaw x (b k)
  have hb (k : CommonRowCandidate i) : b k ∈ Icc 0 1 :=
    ⟨(hL _).1.trans (le_max_left _ _), max_le (hL _).2 (hR _).2⟩
  have hrow : jointCommonRowLaw d i = Measure.pi m := by
    unfold jointCommonRowLaw
    congr 1
    funext k
    exact jointCommonCellLaw_eq d i k
  rw [hrow]
  have hmap := measurePreserving_rowTargetAndCompetitors m j
  have hevent : scoreRowSuccessorEvent (jointRightDiagonal d) i.val j =
      (fun r : CommonRowCandidate i → ℝ × ℝ ↦
        (r j, fun k : {k : CommonRowCandidate i // k ≠ j} ↦ r k.val)) ⁻¹'
        scoreSuccessorPairEvent x (y j)
          (fun k : {k : CommonRowCandidate i // k ≠ j} ↦ y k.val) := by
    ext r
    simp only [scoreRowSuccessorEvent, diagonalPairAt_jointRightDiagonal, mem_preimage,
      scoreSuccessorPairEvent, mem_ofPred_eq]
    rfl
  rw [hevent, hmap.measure_preimage
    (measurableSet_scoreSuccessorPairEvent _ _ _).nullMeasurableSet]
  exact commonRowSuccessorPairEvent_mass hx (hR _) (hb j) (fun _ ↦ hR _)
    (fun k ↦ hb k.val) (fun _ ↦ le_max_right _ _)

private theorem sum_commonCompetitors_eq {n : ℕ} {μ ν : Matching n}
    (i : CommonMan μ ν) (j : CommonRowCandidate i) (g : Fin n → ℝ) :
    (∑ k : {k : CommonRowCandidate i // k ≠ j}, g k.val.val) =
      (∑ k, g k) - g i.val - g j.val := by
  classical
  have h₁ : (∑ k : {k : CommonRowCandidate i // k ≠ j}, g k.val.val) =
      (∑ k : CommonRowCandidate i, g k.val) - g j.val := by
    rw [← Finset.sum_subtype (Finset.univ.erase j) (p := (· ≠ j)) (by simp)
      (fun k : CommonRowCandidate i ↦ g k.val)]
    linarith only [Finset.sum_erase_add Finset.univ
      (fun k : CommonRowCandidate i ↦ g k.val) (Finset.mem_univ j)]
  rw [h₁, ← Finset.sum_subtype (Finset.univ.erase i.val) (p := (i.val ≠ ·))
    (by simp [ne_comm]) g]
  linarith only [Finset.sum_erase_add Finset.univ g (Finset.mem_univ i.val)]

/-- Comparison with the second matching's normalized female spouse scores.
The lower bound loses the male score, the squared normalized score mass, and
an exponential endpoint term; the upper bound loses the male score and the
weights of the omitted self and target. -/
theorem jointCommonRowSuccessorEvent_mass_bounds {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    let x := jointManSpouseScoreRight d i.val
    let y := fun k : Fin n ↦ jointWomanSpouseScoreRight d (ν k)
    let Y := ∑ k, y k
    let p := fun k ↦ y k / Y
    let δ := x + p i.val + p j.val
    0 < Y →
      ENNReal.ofReal ((1 - min 1 (x + 2 * (∑ k, (p k) ^ 2) + Real.exp (-Y / 2))) *
        p j.val) ≤ jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) ∧
      (δ ≤ 1 / 2 → jointCommonRowLaw d i
        (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) ≤
          ENNReal.ofReal ((1 + 2 * δ) * p j.val)) := by
  intro x y Y p δ hY
  let K := {k : CommonRowCandidate i // k ≠ j}
  let a (k : K) := jointCommonEligibility d i k.val.val
  let aj := jointCommonEligibility d i j.val
  let S := ∑ k, (p k) ^ 2
  let z := Real.exp (-Y / 2)
  have hweight (k : Fin n) : (1 - x) * y k ≤ jointCommonEligibility d i k ∧
      jointCommonEligibility d i k ≤ y k :=
    commonEligibilityWeight_bounds hx (hR _) ⟨(hL _).1.trans (le_max_left _ _),
      max_le (hL _).2 (hR _).2⟩
  have hnonneg (k : Fin n) : 0 ≤ jointCommonEligibility d i k :=
    (mul_nonneg (sub_nonneg.mpr hx.2.le) (hR _).1).trans (hweight k).1
  have ha (k : K) : a k ∈ Icc 0 1 :=
    ⟨hnonneg _, (hweight _).2.trans (hR _).2⟩
  have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hp (k : Fin n) : 0 ≤ p k := div_nonneg (hR _).1 hY.le
  have hz : 0 ≤ z := (Real.exp_pos _).le
  have hmass₀ : 0 ≤ scoreRowMass Finset.univ a 0 1 := by
    unfold scoreRowMass
    refine intervalIntegral.integral_nonneg zero_le_one fun t ht ↦ ?_
    exact Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right ht.2 (ha k).1).trans
        (by simpa only [one_mul] using (ha k).2))
  rw [jointCommonRowSuccessorEvent_mass d i j hx hL hR]
  change ENNReal.ofReal ((1 - min 1 (x + 2 * S + z)) * p j.val) ≤
    ENNReal.ofReal (aj * scoreRowMass Finset.univ a 0 1) ∧
      (δ ≤ 1 / 2 → ENNReal.ofReal (aj * scoreRowMass Finset.univ a 0 1) ≤
        ENNReal.ofReal ((1 + 2 * δ) * p j.val))
  constructor
  · apply ENNReal.ofReal_le_ofReal
    by_cases hδ : x + 2 * S + z ≤ 1
    · rw [min_eq_right hδ]
      have hsum : ∑ k : K, a k ≤ Y := calc
        _ ≤ ∑ k : K, y k.val.val := Finset.sum_le_sum fun k _ ↦ (hweight _).2
        _ = Y - y i.val - y j.val := sum_commonCompetitors_eq i j y
        _ ≤ Y := by linarith only [(hR (ν i.val)).1, (hR (ν j.val)).1]
      have hsquare : ∑ k : K, (a k) ^ 2 ≤ Y ^ 2 * S := calc
        _ ≤ ∑ k : K, (y k.val.val) ^ 2 := Finset.sum_le_sum fun k _ ↦
          pow_le_pow_left₀ (ha k).1 (hweight _).2 2
        _ = (∑ k, (y k) ^ 2) - (y i.val) ^ 2 - (y j.val) ^ 2 :=
          sum_commonCompetitors_eq i j (fun k ↦ (y k) ^ 2)
        _ ≤ ∑ k, (y k) ^ 2 := by linarith only [sq_nonneg (y i.val), sq_nonneg (y j.val)]
        _ = Y ^ 2 * S := by
          dsimp only [S, p]
          simp_rw [div_pow]
          rw [← Finset.sum_div]
          field_simp [hY.ne']
      have hm := scoreRowMass_lower_truncated (J := Finset.univ) (a := a)
        (fun k _ ↦ ha k) (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num)
        (fun k _ ↦ mul_le_of_le_one_right (by norm_num) (ha k).2) hY hsum hsquare
      have hs' : 2 * (Y ^ 2 * S) / Y ^ 2 = 2 * S := by field_simp [hY.ne']
      rw [hs', show -(Y * (1 / 2)) = -Y / 2 by ring] at hm
      have hR₀ : 0 ≤ 1 - z - 2 * S := by linarith only [hδ, hx.1]
      calc
        _ ≤ ((1 - x) * (1 - z - 2 * S)) * p j.val := by
          apply mul_le_mul_of_nonneg_right _ (hp _)
          nlinarith only [mul_nonneg hx.1
            (add_nonneg hz (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs))]
        _ = ((1 - x) * y j.val) * ((1 - z - 2 * S) / Y) := by dsimp only [p]; ring
        _ ≤ aj * ((1 - z - 2 * S) / Y) :=
          mul_le_mul_of_nonneg_right (hweight _).1 (div_nonneg hR₀ hY.le)
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (hnonneg _)
    · rw [min_eq_left (le_of_not_ge hδ), sub_self, zero_mul]
      exact mul_nonneg (hnonneg _) hmass₀
  · intro hδ
    apply ENNReal.ofReal_le_ofReal
    have hδ₀ : 0 ≤ δ := add_nonneg (add_nonneg hx.1 (hp _)) (hp _)
    have hr₁ : 0 < 1 - δ := by linarith only [hδ]
    have hr : 0 < (1 - δ) * Y := mul_pos hr₁ hY
    have heq : (1 - δ) * Y = (1 - x) * Y - y i.val - y j.val := by
      dsimp only [δ, p]
      field_simp [hY.ne']
      ring
    have hsum : (1 - δ) * Y ≤ ∑ k : K, a k := calc
      _ = (1 - x) * Y - y i.val - y j.val := heq
      _ ≤ (1 - x) * (Y - y i.val - y j.val) := by
        nlinarith only [mul_nonneg hx.1 ((hR (ν i.val)).1),
          mul_nonneg hx.1 ((hR (ν j.val)).1)]
      _ = (1 - x) * (∑ k : K, y k.val.val) := by rw [sum_commonCompetitors_eq]
      _ ≤ _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ ↦ (hweight _).1
    have hm : scoreRowMass Finset.univ a 0 1 ≤ 1 / ((1 - δ) * Y) := by
      simpa using scoreRowMass_le_exp_tail (fun k _ ↦ (ha k).1) (fun k _ ↦ (ha k).2)
        hr hsum le_rfl zero_le_one le_rfl
    calc
      _ ≤ y j.val * scoreRowMass Finset.univ a 0 1 :=
        mul_le_mul_of_nonneg_right (hweight _).2 hmass₀
      _ ≤ y j.val * (1 / ((1 - δ) * Y)) :=
        mul_le_mul_of_nonneg_left hm (hR _).1
      _ = (1 / (1 - δ)) * p j.val := by dsimp only [p]; field_simp [hr₁.ne', hY.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hr₁).mpr (by
        nlinarith only [mul_nonneg hδ₀ (show 0 ≤ 1 - 2 * δ by linarith only [hδ])])) (hp _)

/-- A single relative error works for every common row and target whenever
the common male score is at most `X` and all normalized female weights
are at most `P`. This is the deterministic form of the uniform arc estimate. -/
theorem jointCommonRowSuccessorEvent_mass_uniform {n : ℕ} {μ ν : Matching n}
    (d : JointSpouseScores μ ν) (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) {X P : ℝ}
    (hX : jointManSpouseScoreRight d i.val ≤ X) (hsmall : X + 2 * P ≤ 1 / 2) :
    let Y := ∑ k : Fin n, jointWomanSpouseScoreRight d (ν k)
    let p := fun k : Fin n ↦ jointWomanSpouseScoreRight d (ν k) / Y
    let E := 2 * X + 4 * P + Real.exp (-Y / 2)
    0 < Y → (∀ k, p k ≤ P) →
      ENNReal.ofReal ((1 - E) * p j.val) ≤
          jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) ∧
      jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) ≤
          ENNReal.ofReal ((1 + E) * p j.val) := by
  intro Y p E hY hP
  have hP₀ : 0 ≤ P := (div_nonneg (hR _).1 hY.le : 0 ≤ p j.val).trans (hP _)
  have hX₀ : 0 ≤ X := hx.1.trans hX
  have hp₀ (k : Fin n) : 0 ≤ p k := div_nonneg (hR _).1 hY.le
  have hp : ∑ k, p k = 1 := by
    dsimp only [p]
    rw [← Finset.sum_div, div_self hY.ne']
  have hsq : ∑ k, (p k) ^ 2 ≤ P := calc
    _ ≤ ∑ k, P * p k := Finset.sum_le_sum fun k _ ↦ by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hP k) (hp₀ k)
    _ = P := by rw [← Finset.mul_sum, hp, mul_one]
  have hδ : jointManSpouseScoreRight d i.val + p i.val + p j.val ≤ X + 2 * P := by
    linarith only [hX, hP i.val, hP j.val]
  obtain ⟨hl, hu⟩ := jointCommonRowSuccessorEvent_mass_bounds d i j hx hL hR hY
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) hl,
    le_trans (hu (hδ.trans hsmall)) (ENNReal.ofReal_le_ofReal ?_)⟩
  · apply mul_le_mul_of_nonneg_right _ (hp₀ _)
    apply sub_le_sub_left
    refine (min_le_right _ _).trans ?_
    dsimp only [E]
    linarith only [hX, hsq, hX₀, hP₀]
  · apply mul_le_mul_of_nonneg_right _ (hp₀ _)
    dsimp only [E]
    linarith only [hδ, (Real.exp_pos (-Y / 2)).le]

/-- At almost every marked array, the conditional off-spouse law reconstructs
tie-free scores and, on the marked nonblocking event, two stable matchings. -/
theorem ae_jointSpouse_ae_stableScoreProfile {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      let x := (splitTwoMatchingScores μ ν).symm (d, v)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ ∧ IsScoreStable x ν := by
  have ht : ∀ᵐ z ∂((jointSpouseScoreLaw μ ν).prod (jointOffSpouseScoreLaw μ ν)),
      ∀ row, Function.Injective ((splitTwoMatchingScores μ ν).symm z row) :=
    ((measurePreserving_splitTwoMatchingScores μ ν).symm).quasiMeasurePreserving.ae
      (ae_injective_rows n)
  filter_upwards [Measure.ae_ae_of_ae_prod ht] with d hd
  have hv : ∀ᵐ v ∂(jointOffSpouseScoreLaw μ ν).restrict (jointOffSpouseNonblocking d),
      (∀ row, Function.Injective ((splitTwoMatchingScores μ ν).symm (d, v) row)) ∧
        v ∈ jointOffSpouseNonblocking d :=
    (ae_restrict_of_ae hd).and (ae_restrict_mem (measurableSet_jointOffSpouseNonblocking d))
  have hv' := Measure.ae_smul_measure hv
    (jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d))⁻¹
  filter_upwards [hv'] with v hv'
  intro hm
  let x := (splitTwoMatchingScores μ ν).symm (d, v)
  exact ⟨hv'.1, (twoStable_iff_splitTwoMatchingScores μ ν x).2 (by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using And.intro hm hv'.2)⟩

/-- On the marked nonblocking event, every common-row successor event reads
out the rank arc, almost surely under the conditional law. -/
theorem ae_jointSpouse_ae_commonRowSuccessorEvent {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      ∀ (i : CommonMan μ ν) (j : CommonRowCandidate i),
        let x := (splitTwoMatchingScores μ ν).symm (d, v)
        jointCommonRows v i ∈ scoreRowSuccessorEvent (jointRightDiagonal d) i.val j ↔
          IsSuccessor (profileOfScores x) ν i.val (ν j.val) := by
  filter_upwards [ae_jointSpouse_ae_stableScoreProfile μ ν] with d hd
  filter_upwards [hd] with v hv
  intro hm i j
  let x := (splitTwoMatchingScores μ ν).symm (d, v)
  obtain ⟨ht, -, hs⟩ := hv hm
  simpa only [x, MeasurableEquiv.apply_symm_apply] using
    jointCommonRowSuccessorEvent_iff_isSuccessor μ ν x hs ht i j

/-- The marked scores are almost surely in the domain where the conditional law is positive. -/
theorem ae_jointSpouse_thresholds {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν,
      (∀ i, jointManSpouseScoreLeft d i ∈ Ico 0 1) ∧
      (∀ i, jointManSpouseScoreRight d i ∈ Ico 0 1) ∧
      (∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1) ∧
      (∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) := by
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc 0 1 := ae_restrict_mem measurableSet_Icc
  have hne : ∀ᵐ t ∂unitScoreLaw, t ≠ 1 := ae_iff.mpr (by simp)
  have hu' : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico 0 1 := by
    filter_upwards [hu, hne] with t ht ht'
    exact ⟨ht.1, lt_of_le_of_ne ht.2 ht'⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Ico 0 1 ∧ z.2 ∈ Icc 0 1 :=
    ((Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu').and
      ((Measure.quasiMeasurePreserving_snd (μ := unitScoreLaw)
        (ν := unitScoreLaw)).ae hu)
  have hd : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ q, (d q).1 ∈ Ico 0 1 ∧ (d q).2 ∈ Icc 0 1 :=
    ae_all_iff.2 fun q ↦ (Measure.tendsto_eval_ae_ae
      (μ := fun _ : JointSpouseIndex μ ν ↦ unitScorePairLaw) (i := q)).eventually hp
  filter_upwards [hd] with d h
  exact ⟨fun i ↦ (h ⟨(i, μ i), Or.inl rfl⟩).1,
    fun i ↦ (h ⟨(i, ν i), Or.inr rfl⟩).1,
    fun w ↦ (h ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2,
    fun w ↦ (h ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2⟩

/-- Replacing the second matching's female threshold by the larger threshold
gives the row's law, but not its eligibility rule. -/
private def jointMaxDiagonal {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν) :
    DiagonalScorePairs n :=
  fun q ↦ (jointManSpouseScoreRight d q.val.1,
    max (jointWomanSpouseScoreLeft d (ν q.val.1)) (jointWomanSpouseScoreRight d (ν q.val.1)))

private theorem jointCommonRowLaw_eq_normalizedStableScoreRowLaw
    {n : ℕ} {μ ν : Matching n} (d : JointSpouseScores μ ν) (i : CommonMan μ ν)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointCommonRowLaw d i = normalizedStableScoreRowLaw (jointMaxDiagonal d) i.val := by
  let x := jointManSpouseScoreRight d i.val
  let b (j : CommonRowCandidate i) :=
    max (jointWomanSpouseScoreLeft d (ν j.val)) (jointWomanSpouseScoreRight d (ν j.val))
  let m (j : CommonRowCandidate i) := rowNonblockingLaw x (b j)
  have hbase : stableScoreRowLaw (jointMaxDiagonal d) i.val = Measure.pi m := rfl
  rw [jointCommonRowLaw, normalizedStableScoreRowLaw, hbase, Measure.pi_univ]
  simp_rw [jointCommonCellLaw_eq, commonRowCellLaw]
  change Measure.pi (fun j ↦ (m j univ)⁻¹ • m j) = (∏ j, m j univ)⁻¹ • Measure.pi m
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (measure_ne_top _ _))]
  refine pi_smul_coordinates m _ fun j ↦ ENNReal.inv_ne_top.mpr ?_
  have hb : b j ∈ Icc 0 1 :=
    ⟨(hL _).1.trans (le_max_left _ _), max_le (hL _).2 (hR _).2⟩
  change rowNonblockingLaw x (b j) univ ≠ 0
  rw [rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hb]
  exact ENNReal.ofReal_ne_zero_iff.mpr (commonDen_pos hx hb)

section FiniteOutcomes

variable {n : ℕ} {μ ν : Matching n} [MeasurableSpace (Option (Fin n))]

/-- Read a finite successor outcome at each common row; discard noncommon rows. -/
noncomputable def jointCommonSuccessors (d : JointSpouseScores μ ν)
    (v : JointOffSpouseScores μ ν) (i : Fin n) : Option (Fin n) :=
  if hi : μ i = ν i then forwardSuccessorOutcome (jointRightDiagonal d) i
    (jointCommonRows v ⟨i, hi⟩) else none

/-- Conditional successor law for the second matching, set to no arc on a noncommon row. -/
noncomputable def jointCommonSuccessorLaw (d : JointSpouseScores μ ν) (i : Fin n) :
    Measure (Option (Fin n)) :=
  if hi : μ i = ν i then (jointCommonRowLaw d ⟨i, hi⟩).map
    (forwardSuccessorOutcome (jointRightDiagonal d) i) else Measure.dirac none

theorem jointCommonSuccessorLaw_isProbabilityMeasure (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) (i : Fin n) :
    IsProbabilityMeasure (jointCommonSuccessorLaw d i) := by
  unfold jointCommonSuccessorLaw
  split
  · rename_i hi
    let := jointCommonRowLaw_isProbabilityMeasure d hpos (⟨i, hi⟩ : CommonMan μ ν)
    infer_instance
  · infer_instance

private theorem measurePreserving_extendNone {ι : Type*} [Fintype ι]
    [MeasurableSpace (Option ι)] (P : ι → Prop) [DecidablePred P]
    (m : Subtype P → Measure (Option ι)) [∀ i, IsProbabilityMeasure (m i)] :
    MeasurePreserving
      (fun v : Subtype P → Option ι ↦ fun i ↦ if hi : P i then v ⟨i, hi⟩ else none)
      (Measure.pi m)
      (Measure.pi fun i ↦ if hi : P i then m ⟨i, hi⟩ else Measure.dirac none) := by
  classical
  let f (v : Subtype P → Option ι) (i : ι) := if hi : P i then v ⟨i, hi⟩ else none
  let m' (i : ι) := if hi : P i then m ⟨i, hi⟩ else Measure.dirac none
  let (i : ι) : IsProbabilityMeasure (m' i) := by
    dsimp only [m']
    split <;> infer_instance
  have hf : Measurable f := by
    refine Measurable.of_eval fun i ↦ ?_
    dsimp only [f]
    split
    · exact measurable_pi_apply _
    · exact measurable_const
  refine ⟨hf, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hf (MeasurableSet.univ_pi hs),
    ← Fintype.prod_subtype_mul_prod_subtype P (fun i ↦ m' i (s i))]
  have hpos : (∏ i : Subtype P, m' i.val (s i.val)) = ∏ i : Subtype P, m i (s i.val) :=
    Finset.prod_congr rfl fun i _ ↦ by simp only [m', dite_eq_left i.property]
  rw [hpos]
  by_cases h : ∀ i : {i // ¬P i}, (none : Option ι) ∈ s i.val
  · have hpre : f ⁻¹' univ.pi s = univ.pi (fun i : Subtype P ↦ s i.val) := by
      ext v
      simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, f]
      exact ⟨fun hv i ↦ by simpa only [dite_eq_left i.property] using hv i.val,
        fun hv i ↦ by
          by_cases hi : P i
          · simpa only [dite_eq_left hi] using hv ⟨i, hi⟩
          · simpa only [dite_eq_right hi] using h ⟨i, hi⟩⟩
    have hc : (∏ i : {i // ¬P i}, m' i.val (s i.val)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp only [m', dite_eq_right i.property, Measure.dirac_apply' _ (hs i.val), indicator_of_mem (h i),
        Pi.one_apply]
    rw [hpre, Measure.pi_pi, hc, mul_one]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hpre : f ⁻¹' univ.pi s = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun v hv ↦ hi ?_
      simpa only [f, dite_eq_right i.property] using Set.mem_pi.mp hv i.val (Set.mem_univ _)
    have hc : (∏ i : {i // ¬P i}, m' i.val (s i.val)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [m', dite_eq_right i.property, Measure.dirac_apply' _ (hs i.val), indicator_of_notMem hi]
    rw [hpre, measure_empty, hc, mul_zero]

/-- Conditioning only on the two marked spouse arrays and joint stability,
the finite common successor graph has independent rows. -/
theorem measurePreserving_jointCommonSuccessors (d : JointSpouseScores μ ν)
    (hpos : jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≠ 0) :
    MeasurePreserving (jointCommonSuccessors d) (jointOffSpouseProbabilityLaw d)
      (Measure.pi (jointCommonSuccessorLaw d)) := by
  let f (i : CommonMan μ ν) := forwardSuccessorOutcome (jointRightDiagonal d) i.val
  let m (i : CommonMan μ ν) := (jointCommonRowLaw d i).map (f i)
  let (i : CommonMan μ ν) := jointCommonRowLaw_isProbabilityMeasure d hpos i
  let (i : CommonMan μ ν) : IsProbabilityMeasure (m i) := by
    dsimp [m]
    infer_instance
  have hmap : MeasurePreserving (fun r i ↦ f i (r i)) (Measure.pi (jointCommonRowLaw d))
      (Measure.pi m) := by
    refine measurePreserving_pi _ _ fun i ↦ ⟨?_, rfl⟩
    exact measurable_forwardSuccessorOutcome _ _
  exact ((measurePreserving_extendNone (fun i ↦ μ i = ν i) m).comp hmap).comp
    (measurePreserving_jointCommonRows d hpos)

omit [MeasurableSpace (Option (Fin n))] in
/-- The conditional graph has the original rank arcs on common rows, almost surely. -/
theorem ae_jointSpouse_ae_commonSuccessors_eq_some_iff (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      ∀ (i : CommonMan μ ν) (j : CommonRowCandidate i),
        let x := (splitTwoMatchingScores μ ν).symm (d, v)
        jointCommonSuccessors d v i.val = some j.val ↔
          IsSuccessor (profileOfScores x) ν i.val (ν j.val) := by
  filter_upwards [ae_jointSpouse_ae_stableScoreProfile μ ν,
    ae_jointSpouse_ae_commonRowSuccessorEvent μ ν] with d hd he
  filter_upwards [hd, he] with v hv hr
  intro hm i j
  let x := (splitTwoMatchingScores μ ν).symm (d, v)
  have ht := (hv hm).1
  have hinj : Function.Injective (fun k : CommonRowCandidate i ↦ (jointCommonRows v i k).1) := by
    intro k l h
    apply Subtype.ext
    apply ν.injective
    apply ht (Sum.inl i.val)
    have hval (a : CommonRowCandidate i) : (jointCommonRows v i a).1 =
        x (Sum.inl i.val) (ν a.val) := by
      change (v (commonOffSpouseCell i a)).1 = _
      rw [← show (splitTwoMatchingScores μ ν x).2 = v by
        simp only [x, MeasurableEquiv.apply_symm_apply]]
      rw [splitTwoMatchingScores_offSpouse_apply]
      rfl
    simpa only [hval] using h
  rw [jointCommonSuccessors, dite_eq_left i.property,
    forwardSuccessorOutcome_eq_some_iff _ _ _ j hinj]
  exact hr hm i j

variable [MeasurableSingletonClass (Option (Fin n))]

/-- At every common row, the singleton outcome mass is the calculated arc probability. -/
theorem jointCommonSuccessorLaw_some (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointCommonSuccessorLaw d i.val {some j.val} =
      jointCommonRowLaw d i (scoreRowSuccessorEvent (jointRightDiagonal d) i.val j) := by
  rw [jointCommonSuccessorLaw, dite_eq_left i.property,
    Measure.map_apply (measurable_forwardSuccessorOutcome _ _) (measurableSet_singleton _)]
  apply measure_congr
  rw [jointCommonRowLaw_eq_normalizedStableScoreRowLaw d i hx hL hR]
  filter_upwards [ae_injective_fst_normalizedStableScoreRowLaw (jointMaxDiagonal d) i.val]
    with r hr
  exact propext (forwardSuccessorOutcome_eq_some_iff (jointRightDiagonal d) i.val r j hr)

/-- The uniform relative comparison holds for the finite arc law itself. -/
theorem jointCommonSuccessorLaw_some_uniform (d : JointSpouseScores μ ν)
    (i : CommonMan μ ν) (j : CommonRowCandidate i)
    (hx : jointManSpouseScoreRight d i.val ∈ Ico 0 1)
    (hL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) {X P : ℝ}
    (hX : jointManSpouseScoreRight d i.val ≤ X) (hsmall : X + 2 * P ≤ 1 / 2) :
    let Y := ∑ k : Fin n, jointWomanSpouseScoreRight d (ν k)
    let p := fun k : Fin n ↦ jointWomanSpouseScoreRight d (ν k) / Y
    let E := 2 * X + 4 * P + Real.exp (-Y / 2)
    0 < Y → (∀ k, p k ≤ P) →
      ENNReal.ofReal ((1 - E) * p j.val) ≤ jointCommonSuccessorLaw d i.val {some j.val} ∧
      jointCommonSuccessorLaw d i.val {some j.val} ≤ ENNReal.ofReal ((1 + E) * p j.val) := by
  dsimp only
  rw [jointCommonSuccessorLaw_some d i j hx hL hR]
  exact jointCommonRowSuccessorEvent_mass_uniform d i j hx hL hR hX hsmall

end FiniteOutcomes

/-- A candidate cycle supported on common labels is realized by the finite
conditional graph exactly when it is an exposed rotation at the second matching. -/
theorem ae_jointSpouse_ae_commonCycle_iff_exposed {n : ℕ} (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
      ∀ σ : Equiv.Perm (Fin n), σ.IsCycle → (∀ i ∈ σ.support, μ i = ν i) →
        let x := (splitTwoMatchingScores μ ν).symm (d, v)
        (∀ i ∈ σ.support, jointCommonSuccessors d v i = some (σ i)) ↔
          IsExposedRotation (profileOfScores x) ν σ := by
  filter_upwards [ae_jointSpouse_ae_commonSuccessors_eq_some_iff μ ν] with d hd
  filter_upwards [hd] with v hv
  intro hm σ hσ hC
  have harc (i : Fin n) (hi : σ i ≠ i) :=
    hv hm ⟨i, hC i (Equiv.Perm.mem_support.mpr hi)⟩ ⟨σ i, hi.symm⟩
  exact ⟨fun h ↦ ⟨hσ, fun i hi ↦ (harc i hi).mp (h i (Equiv.Perm.mem_support.mpr hi))⟩,
    fun h i hi ↦ (harc i (Equiv.Perm.mem_support.mp hi)).mpr
      (h.successor i (Equiv.Perm.mem_support.mp hi))⟩

end LennonPittelFormalization

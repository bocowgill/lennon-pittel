module

public import LennonPittel.CoexposureScoreProduct

/-!
# The score law after a one-cell forward reveal

A stable off-diagonal cell avoids the blocking rectangle. When it is
forward-eligible, its male score is revealed. Otherwise, stability and
ineligibility force its female score above the spouse score, outside a
null equality boundary.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- An off-diagonal score cell is forward-eligible when the man is worse off
with the candidate and the woman is better off. -/
def forwardEligibleScoreCell (x y : ℝ) : Set (ℝ × ℝ) :=
  Ioi x ×ˢ Iio y

theorem measurableSet_forwardEligibleScoreCell (x y : ℝ) :
    MeasurableSet (forwardEligibleScoreCell x y) :=
  measurableSet_Ioi.prod measurableSet_Iio

/-- The forward observation records the male score only in eligible cells. -/
noncomputable def forwardScoreCellReveal (x y : ℝ) (z : ℝ × ℝ) : Option ℝ := by
  classical
  exact if z ∈ forwardEligibleScoreCell x y then some z.1 else none

/-- The unnormalized law of a stable cell with fixed spouse scores. -/
noncomputable def stableScoreCellLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  unitScorePairLaw.restrict (nonblockingScoreCell x y)

instance (x y : ℝ) : IsFiniteMeasure (stableScoreCellLaw x y) :=
  inferInstanceAs (IsFiniteMeasure (unitScorePairLaw.restrict _))

/-- An active cell is a product of the two intervals in the eligible rectangle. -/
theorem stableScoreCellLaw_restrict_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y) =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y)) := by
  rw [stableScoreCellLaw, Measure.restrict_restrict_of_subset]
  · exact (Measure.prod_restrict (Ioi x) (Iio y)).symm
  · rintro z hz hblock
    have h₁ : x < z.1 := (mem_prod.mp hz).1
    have h₂ : z.1 < x := (mem_prod.mp hblock).1
    exact (not_lt_of_ge h₁.le) h₂

private theorem unitScorePairLaw_ae_fst_ne (x : ℝ) :
    ∀ᵐ z ∂unitScorePairLaw, z.1 ≠ x := by
  exact (Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw) (ν := unitScoreLaw)).ae
    (unitScoreLaw.ae_ne x)

/-- An inactive stable cell has an unrestricted male score and a female score
at least as large as the woman's spouse score. -/
theorem stableScoreCellLaw_restrict_not_forwardEligible (x y : ℝ) :
    (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y)ᶜ =
      unitScoreLaw.prod (unitScoreLaw.restrict (Ici y)) := by
  rw [stableScoreCellLaw,
    Measure.restrict_restrict (measurableSet_forwardEligibleScoreCell x y).compl]
  calc
    _ = unitScorePairLaw.restrict (univ ×ˢ Ici y) := by
      apply Measure.restrict_congr_set
      filter_upwards [unitScorePairLaw_ae_fst_ne x] with z hz
      apply propext
      change (¬ (x < z.1 ∧ z.2 < y)) ∧ (¬ (z.1 < x ∧ z.2 < y)) ↔ z ∈ univ ×ˢ Ici y
      simp only [mem_prod, mem_univ, true_and, mem_Ici]
      refine ⟨fun h ↦ le_of_not_gt ?_,
        fun hy ↦ ⟨fun h ↦ hy.not_gt h.2, fun h ↦ hy.not_gt h.2⟩⟩
      intro hy
      exact (lt_or_gt_of_ne hz).elim (fun hlt ↦ h.2 ⟨hlt, hy⟩) (fun hlt ↦ h.1 ⟨hlt, hy⟩)
    _ = _ := by rw [unitScorePairLaw, ← Measure.prod_restrict, Measure.restrict_univ]

/-- The one-cell reveal identity as an iterated integral. It handles exact
revealed values without conditioning on singleton events. -/
theorem lintegral_stableScoreCell_forwardReveal (x y : ℝ)
    (f : Option ℝ → ℝ × ℝ → ℝ≥0∞)
    (hsome : Measurable fun z : ℝ × ℝ ↦ f (some z.1) z)
    (hnone : Measurable (f none)) :
    (∫⁻ z, f (forwardScoreCellReveal x y z) z ∂stableScoreCellLaw x y) =
      (∫⁻ u in Ioi x, ∫⁻ v in Iio y, f (some u) (u, v) ∂unitScoreLaw ∂unitScoreLaw) +
        (∫⁻ u, ∫⁻ v in Ici y, f none (u, v) ∂unitScoreLaw ∂unitScoreLaw) := by
  classical
  calc
    _ = ∫⁻ z, (forwardEligibleScoreCell x y).piecewise
        (fun z ↦ f (some z.1) z) (f none) z ∂stableScoreCellLaw x y := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ forwardEligibleScoreCell x y
      · simp [forwardScoreCellReveal, hz]
      · simp [forwardScoreCellReveal, hz]
    _ = _ := by
      rw [lintegral_piecewise (measurableSet_forwardEligibleScoreCell x y).nullMeasurableSet,
        stableScoreCellLaw_restrict_forwardEligible,
        stableScoreCellLaw_restrict_not_forwardEligible,
        lintegral_prod _ hsome.aemeasurable, lintegral_prod _ hnone.aemeasurable]

/-- The normalized uniform law above a given female spouse score. -/
noncomputable def inactiveFemaleScoreLaw (y : ℝ) : Measure ℝ :=
  (unitScoreLaw (Ici y))⁻¹ • unitScoreLaw.restrict (Ici y)

theorem unitScoreLaw_Ici_of_mem_Icc {y : ℝ} (hy : y ∈ Icc 0 1) :
    unitScoreLaw (Ici y) = ENNReal.ofReal (1 - y) := by
  rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _),
    measure_univ, unitScoreLaw_Iio_of_mem_Icc hy, ENNReal.ofReal_sub _ hy.1, ENNReal.ofReal_one]

theorem inactiveFemaleScoreLaw_isProbabilityMeasure {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    IsProbabilityMeasure (inactiveFemaleScoreLaw y) := by
  have hm : unitScoreLaw (Ici y) ≠ 0 := by
    rw [unitScoreLaw_Ici_of_mem_Icc ⟨hy0, hy1.le⟩]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hy1)).ne'
  refine ⟨?_⟩
  rw [inactiveFemaleScoreLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hm (measure_ne_top _ _)]

/-- Normalizing the inactive branch keeps the male score uniform and independent
of the truncated female score. -/
theorem normalized_stableScoreCellLaw_not_forwardEligible (x y : ℝ) :
    (unitScoreLaw (Ici y))⁻¹ •
        (stableScoreCellLaw x y).restrict (forwardEligibleScoreCell x y)ᶜ =
      unitScoreLaw.prod (inactiveFemaleScoreLaw y) := by
  rw [stableScoreCellLaw_restrict_not_forwardEligible, inactiveFemaleScoreLaw,
    Measure.prod_smul_right]

/-- The set of cells with a prescribed value of the forward eligibility flag. -/
def forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  if b then forwardEligibleScoreCell x y else (forwardEligibleScoreCell x y)ᶜ

theorem measurableSet_forwardScoreCellFlagEvent (x y : ℝ) (b : Bool) :
    MeasurableSet (forwardScoreCellFlagEvent x y b) := by
  cases b
  · exact (measurableSet_forwardEligibleScoreCell x y).compl
  · exact measurableSet_forwardEligibleScoreCell x y

/-- The cell law for a specified forward flag. Both branches are unnormalized. -/
noncomputable def forwardScoreCellFlagLaw (x y : ℝ) (b : Bool) : Measure (ℝ × ℝ) :=
  if b then (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))
  else unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))

instance (x y : ℝ) (b : Bool) : IsFiniteMeasure (forwardScoreCellFlagLaw x y b) := by
  cases b
  · exact inferInstanceAs
      (IsFiniteMeasure (unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))))
  · exact inferInstanceAs
      (IsFiniteMeasure ((unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio y))))

theorem stableScoreCellLaw_restrict_flag (x y : ℝ) (b : Bool) :
    (stableScoreCellLaw x y).restrict (forwardScoreCellFlagEvent x y b) =
      forwardScoreCellFlagLaw x y b := by
  cases b
  · exact stableScoreCellLaw_restrict_not_forwardEligible x y
  · exact stableScoreCellLaw_restrict_forwardEligible x y

/-- Index type for the off-diagonal score cells at a fixed matching. -/
abbrev OffDiagonalCellIndex (n : ℕ) := {q : ScorePairIndex n // q.1 ≠ q.2}

/-- The off-diagonal profiles with exactly the prescribed forward mask. -/
def forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (OffDiagonalScorePairs n) :=
  univ.pi fun q ↦ forwardScoreCellFlagEvent
    (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q)

theorem measurableSet_forwardScoreMaskEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardScoreMaskEvent d flag) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦
    measurableSet_forwardScoreCellFlagEvent _ _ _)

/-- Under a fixed forward mask and fixed spouse scores, all off-diagonal cells
still factor, with the interval laws for their respective flags. -/
theorem offDiagonalScoreLaw_restrict_nonblocking_mask {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag) =
      Measure.pi fun q : OffDiagonalCellIndex n ↦ forwardScoreCellFlagLaw
        (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking, forwardScoreMaskEvent, Measure.restrict_pi_pi]
  congr 1
  funext q
  exact stableScoreCellLaw_restrict_flag _ _ _

/-- Split a fixed-mask law into the product of all active cells and all inactive
cells. In particular the inactive factor does not change when integrating over
the revealed male scores, which are functions of the active cells. -/
theorem measurePreserving_offDiagonalScoreLaw_splitMask {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : OffDiagonalCellIndex n ↦ ℝ × ℝ)
        (fun q ↦ flag q = true))
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag))
      ((Measure.pi fun q : {q : OffDiagonalCellIndex n // flag q = true} ↦
        (unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)).prod
          (unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2))).prod
        (Measure.pi fun q : {q : OffDiagonalCellIndex n // flag q ≠ true} ↦
          unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2)))) := by
  rw [offDiagonalScoreLaw_restrict_nonblocking_mask]
  convert measurePreserving_piEquivPiSubtypeProd
    (fun q : OffDiagonalCellIndex n ↦ forwardScoreCellFlagLaw
      (diagonalPairAt d q.val.1).1 (diagonalPairAt d q.val.2).2 (flag q))
    (fun q ↦ flag q = true) using 2
  · congr 1
    funext q
    simp [forwardScoreCellFlagLaw, q.property]
  · congr 1
    funext q
    simp [forwardScoreCellFlagLaw, q.property]

/-- Active cell indices under a fixed forward mask. -/
abbrev ForwardActiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q = true}

/-- Inactive cell indices under a fixed forward mask. -/
abbrev ForwardInactiveCellIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  {q : OffDiagonalCellIndex n // flag q ≠ true}

/-- The part of the fixed-mask law that is not revealed by the forward observation. -/
noncomputable def forwardScoreMaskInactiveLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  Measure.pi fun q ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2))

instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveLaw d flag) := by
  unfold forwardScoreMaskInactiveLaw
  infer_instance

/-- The observation within a fixed mask records only active male scores.
Pairing it with the inactive score array lets us state their joint law. -/
def forwardScoreMaskRevealAndInactive {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (z : OffDiagonalScorePairs n) :
    (ForwardActiveCellIndex flag → ℝ) × (ForwardInactiveCellIndex flag → ℝ × ℝ) :=
  (fun q ↦ (z q.val).1, fun q ↦ z q.val)

theorem measurable_forwardScoreMaskRevealAndInactive {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardScoreMaskRevealAndInactive flag) :=
  (Measurable.of_eval fun q ↦ measurable_fst.comp (measurable_pi_apply q.val)).prodMk
    (Measurable.of_eval fun q ↦ measurable_pi_apply q.val)

/-- The exact marginal law of the revealed active male scores at a fixed mask. -/
noncomputable def forwardScoreMaskActiveMaleLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) : Measure (ForwardActiveCellIndex flag → ℝ) :=
  Measure.pi fun q ↦
    unitScoreLaw (Iio (diagonalPairAt d q.val.val.2).2) •
      unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)

instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskActiveMaleLaw d flag) := by
  have (q : ForwardActiveCellIndex flag) : IsFiniteMeasure
      (unitScoreLaw (Iio (diagonalPairAt d q.val.val.2).2) •
        unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)) :=
    Measure.smul_finite _ (measure_ne_top _ _)
  unfold forwardScoreMaskActiveMaleLaw
  infer_instance

/-- Under a fixed mask, the forward observation and the unopened inactive cells
have a product law, with the active female scores integrated out. -/
theorem map_forwardScoreMaskRevealAndInactive {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure.map (forwardScoreMaskRevealAndInactive flag)
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag)) =
      (forwardScoreMaskActiveMaleLaw d flag).prod (forwardScoreMaskInactiveLaw d flag) := by
  let μ (q : ForwardActiveCellIndex flag) :=
    (unitScoreLaw.restrict (Ioi (diagonalPairAt d q.val.val.1).1)).prod
      (unitScoreLaw.restrict (Iio (diagonalPairAt d q.val.val.2).2))
  have (q : ForwardActiveCellIndex flag) : IsFiniteMeasure (μ q) := by
    unfold μ
    infer_instance
  have hproj : MeasurePreserving
      (fun z : ForwardActiveCellIndex flag → ℝ × ℝ ↦ fun q ↦ (z q).1)
      (Measure.pi μ) (Measure.pi fun q ↦ (μ q).map Prod.fst) :=
    measurePreserving_pi μ _ (fun _ ↦ ⟨measurable_fst, rfl⟩)
  have hsplit := measurePreserving_offDiagonalScoreLaw_splitMask d flag
  have h := ((hproj.prod (MeasurePreserving.id (forwardScoreMaskInactiveLaw d flag))).comp
    hsplit).map_eq
  change Measure.map (forwardScoreMaskRevealAndInactive flag) _ =
    (Measure.pi fun q ↦ (μ q).map Prod.fst).prod (forwardScoreMaskInactiveLaw d flag) at h
  simpa only [μ, Measure.map_fst_prod, Measure.restrict_apply_univ,
    forwardScoreMaskActiveMaleLaw] using h

/-- Inactive cells targeting a woman, indexed by her husband in the fixed matching. -/
abbrev ForwardInactiveColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (j : Fin n) := {q : ForwardInactiveCellIndex flag // q.val.val.2 = j}

/-- Reindex the inactive score array by female column. -/
def forwardInactiveColumnsEquiv {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    (ForwardInactiveCellIndex flag → ℝ × ℝ) ≃ᵐ
      ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) where
  toFun z _ q := z q.val
  invFun z q := z q.val.val.2 ⟨q, rfl⟩
  left_inv _ := rfl
  right_inv z := by
    funext j q
    obtain ⟨q, rfl⟩ := q
    rfl
  measurable_toFun := Measurable.of_eval fun _ ↦
    Measurable.of_eval fun _ ↦ measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun q ↦
    (measurable_pi_apply (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)).comp
      (measurable_pi_apply q.val.val.2)

private theorem measurePreserving_forwardInactiveColumnsEquiv_pi {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool)
    (μ : ForwardInactiveCellIndex flag → Measure (ℝ × ℝ)) [∀ q, SigmaFinite (μ q)] :
    MeasurePreserving (forwardInactiveColumnsEquiv flag) (Measure.pi μ)
      (Measure.pi fun j : Fin n ↦
        Measure.pi fun q : ForwardInactiveColumnIndex flag j ↦ μ q.val) := by
  let e := (forwardInactiveColumnsEquiv flag).symm
  refine MeasurePreserving.symm e ⟨e.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  rw [show e ⁻¹' (univ.pi s) = univ.pi
      (fun j : Fin n ↦ univ.pi fun q : ForwardInactiveColumnIndex flag j ↦ s q.val) by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, e,
      forwardInactiveColumnsEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
      Equiv.symm, Equiv.coe_fn_mk]
    constructor
    · intro h j q
      obtain ⟨q, rfl⟩ := q
      exact h q
    · intro h q
      exact h q.val.val.2 ⟨q, rfl⟩]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv
    (Equiv.sigmaFiberEquiv (fun q : ForwardInactiveCellIndex flag ↦ q.val.val.2))
    (fun q : Σ j : Fin n, ForwardInactiveColumnIndex flag j ↦ μ q.2.val (s q.2.val))
    (fun q : ForwardInactiveCellIndex flag ↦ μ q (s q)) (fun _ ↦ rfl)

/-- Under a fixed mask, inactive cells are independent by female column,
with all their female scores truncated at the corresponding spouse score. -/
noncomputable def forwardScoreMaskInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure ((j : Fin n) → ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun j : Fin n ↦ Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))

instance {n : ℕ} (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    IsFiniteMeasure (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveColumnLaw
  infer_instance

theorem measurePreserving_forwardInactiveColumnsEquiv {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurePreserving (forwardInactiveColumnsEquiv flag) (forwardScoreMaskInactiveLaw d flag)
      (forwardScoreMaskInactiveColumnLaw d flag) := by
  unfold forwardScoreMaskInactiveLaw forwardScoreMaskInactiveColumnLaw
  convert measurePreserving_forwardInactiveColumnsEquiv_pi flag
    (fun q ↦ unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d q.val.val.2).2)))
    using 2
  funext j
  congr 1
  funext q
  rw [q.property]

/-- After the exact forward reveal, the untouched reverse columns have their
product law as an independent factor of the revealed scores. -/
theorem map_forwardScoreMaskRevealAndInactiveColumns {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measure.map
      (Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag)
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag)) =
      (forwardScoreMaskActiveMaleLaw d flag).prod (forwardScoreMaskInactiveColumnLaw d flag) := by
  rw [← Measure.map_map (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable)
    (measurable_forwardScoreMaskRevealAndInactive flag), map_forwardScoreMaskRevealAndInactive,
    ← Measure.map_prod_map _ _ measurable_id (forwardInactiveColumnsEquiv flag).measurable,
    Measure.map_id, (measurePreserving_forwardInactiveColumnsEquiv d flag).map_eq]

/-- The probability law of one inactive column after removing the mass of its mask. -/
noncomputable def normalizedForwardInactiveColumnLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (j : Fin n) :
    Measure (ForwardInactiveColumnIndex flag j → ℝ × ℝ) :=
  Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
    unitScoreLaw.prod (inactiveFemaleScoreLaw (diagonalPairAt d j).2)

theorem normalizedForwardInactiveColumnLaw_isProbabilityMeasure {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (j : Fin n)
    (hy0 : 0 ≤ (diagonalPairAt d j).2) (hy1 : (diagonalPairAt d j).2 < 1) :
    IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag j) := by
  have := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  unfold normalizedForwardInactiveColumnLaw
  infer_instance

private theorem pi_smul_finite {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i))
    [∀ i, IsFiniteMeasure (ν i)] (a : ι → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) :
    (Measure.pi fun i ↦ a i • ν i) = (∏ i, a i) • Measure.pi ν := by
  have (i : ι) : IsFiniteMeasure (a i • ν i) := Measure.smul_finite (ν i) (ha i)
  refine Measure.pi_eq fun s _ ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

/-- The inactive mask probability is a scalar; after it is removed the
inactive columns retain their independent probability laws. -/
theorem forwardScoreMaskInactiveColumnLaw_eq_smul {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (hy0 : ∀ j, 0 ≤ (diagonalPairAt d j).2) (hy1 : ∀ j, (diagonalPairAt d j).2 < 1) :
    forwardScoreMaskInactiveColumnLaw d flag =
      (∏ j, (ENNReal.ofReal (1 - (diagonalPairAt d j).2)) ^
        Fintype.card (ForwardInactiveColumnIndex flag j)) •
        Measure.pi (normalizedForwardInactiveColumnLaw d flag) := by
  let a (j : Fin n) := ENNReal.ofReal (1 - (diagonalPairAt d j).2)
  have (j : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag j) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag j (hy0 j) (hy1 j)
  have hcolumn (j : Fin n) :
      (Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
        unitScoreLaw.prod (unitScoreLaw.restrict (Ici (diagonalPairAt d j).2))) =
        a j ^ Fintype.card (ForwardInactiveColumnIndex flag j) •
          normalizedForwardInactiveColumnLaw d flag j := by
    let y := (diagonalPairAt d j).2
    have := inactiveFemaleScoreLaw_isProbabilityMeasure (hy0 j) (hy1 j)
    have hcell : unitScoreLaw.prod (unitScoreLaw.restrict (Ici y)) =
        a j • (unitScoreLaw.prod (inactiveFemaleScoreLaw y)) := by
      rw [inactiveFemaleScoreLaw, Measure.prod_smul_right, smul_smul,
        unitScoreLaw_Ici_of_mem_Icc ⟨hy0 j, (hy1 j).le⟩]
      change _ = (a j * (a j)⁻¹) • _
      rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hy1 j))).ne'
        ENNReal.ofReal_ne_top, one_smul]
    change (Measure.pi fun _ : ForwardInactiveColumnIndex flag j ↦
      unitScoreLaw.prod (unitScoreLaw.restrict (Ici y))) = _
    simp_rw [hcell]
    simpa only [Finset.prod_const, Finset.card_univ, normalizedForwardInactiveColumnLaw] using
      pi_smul_finite (fun _ : ForwardInactiveColumnIndex flag j ↦
        unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (fun _ ↦ a j)
        (fun _ ↦ ENNReal.ofReal_ne_top)
  unfold forwardScoreMaskInactiveColumnLaw
  simp_rw [hcolumn]
  exact pi_smul_finite (normalizedForwardInactiveColumnLaw d flag) _
    (fun j ↦ ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

end LennonPittelFormalization

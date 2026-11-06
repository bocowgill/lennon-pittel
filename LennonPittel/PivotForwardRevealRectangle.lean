module

public import LennonPittel.PivotReverseMaskJointLaw

/-!
# Section bounds under a fixed forward reveal

The exact revealed-score factor is retained when a column event depends on
the revealed male scores. A uniform bound on each normalized section then
bounds the whole event by that bound times the restricted mass.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The active male observations at a fixed mask. -/
abbrev ForwardRevealedMaleScores {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  ForwardActiveCellIndex flag → ℝ

/-- The inactive observations indexed first by column. -/
abbrev ForwardInactiveColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :=
  (i : Fin n) → ForwardInactiveColumnIndex flag i → ℝ × ℝ

/-- Pair the revealed observations with the unrevealed score columns. -/
def forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    OffDiagonalScorePairs n → ForwardRevealedMaleScores flag × ForwardInactiveColumns flag :=
  Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag

theorem measurable_forwardRevealWithColumns {n : ℕ} (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (forwardRevealWithColumns flag) :=
  (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable).comp
    (measurable_forwardScoreMaskRevealAndInactive flag)

/-- Restricting the revealed male observations restricts only the first
factor of the joint law. -/
theorem map_forwardMaskRevealLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (U : Set (ForwardRevealedMaleScores flag))
    (hU : MeasurableSet U) :
    Measure.map (forwardRevealWithColumns flag) (forwardMaskRevealLaw d flag U) =
      ((forwardScoreMaskActiveMaleLaw d flag).restrict U).prod
        (forwardScoreMaskInactiveColumnLaw d flag) := by
  let V : Set (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) := U ×ˢ univ
  have hpre : forwardRevealWithColumns flag ⁻¹' V =
      (Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' U := by
    ext z
    simp [V, forwardRevealWithColumns]
  unfold forwardMaskRevealLaw
  rw [← hpre, ← Measure.restrict_map (measurable_forwardRevealWithColumns flag)
    (hU.prod MeasurableSet.univ)]
  change (Measure.map _ _).restrict V = _
  rw [show Measure.map (forwardRevealWithColumns flag)
      (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
        (forwardScoreMaskEvent d flag)) = _ from
    map_forwardScoreMaskRevealAndInactiveColumns d flag]
  dsimp only [V]
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- A section bound for a score event in the original restricted law.
The column event may depend measurably on the active observations. -/
theorem forwardMaskRevealLaw_measure_le_of_column_sections {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (hU : MeasurableSet U)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    {E : Set (OffDiagonalScorePairs n)}
    (V : Set (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag))
    (hV : MeasurableSet V) {b : ℝ≥0∞}
    (hsub : E ≤ᵐ[forwardMaskRevealLaw d flag U] forwardRevealWithColumns flag ⁻¹' V)
    (hb : ∀ a ∈ U, (Measure.pi (normalizedForwardInactiveColumnLaw d flag))
      (Prod.mk a ⁻¹' V) ≤ b) :
    forwardMaskRevealLaw d flag U E ≤
      ((forwardScoreMaskActiveMaleLaw d flag) U * (forwardScoreMaskInactiveColumnLaw d flag) univ) *
        b := by
  let R := forwardScoreMaskActiveMaleLaw d flag
  let L := forwardScoreMaskInactiveColumnLaw d flag
  have (i : Fin n) : IsProbabilityMeasure (normalizedForwardInactiveColumnLaw d flag i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  calc
    _ ≤ forwardMaskRevealLaw d flag U (forwardRevealWithColumns flag ⁻¹' V) :=
      measure_mono_ae hsub
    _ = ((R.restrict U).prod L) V := by
      rw [← Measure.map_apply (measurable_forwardRevealWithColumns flag) hV,
        map_forwardMaskRevealLaw d flag U hU]
    _ = ∫⁻ a in U, L (Prod.mk a ⁻¹' V) ∂R := Measure.prod_apply hV
    _ ≤ ∫⁻ _ in U, L univ * b ∂R := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with a ha
      change forwardScoreMaskInactiveColumnLaw d flag _ ≤
        forwardScoreMaskInactiveColumnLaw d flag univ * b
      rw [forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1, Measure.smul_apply,
        Measure.smul_apply, smul_eq_mul, smul_eq_mul, measure_univ, mul_one]
      exact mul_le_mul_right (hb a ha) _
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]; ac_rfl

/-- In a product probability law, replace one coordinate's ordinary test
by a marked test. The marked coordinate contributes one extra factor. -/
theorem measure_pi_markedColumn_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (ν : ∀ i, Measure (β i))
    [∀ i, IsProbabilityMeasure (ν i)] (S : Finset ι) (B : ∀ i, Set (β i))
    (p : ι → ℝ≥0∞) (w : ι) (hw : w ∈ S) (cross : Set (β w)) (a : ℝ≥0∞)
    (hB : ∀ i ∈ S, ν i (B i) ≤ p i) (hcross : ν w cross ≤ p w * a) :
    (Measure.pi ν) {z | (∀ i ∈ S, z i ∈ B i) ∧ z w ∈ cross} ≤
      (∏ i ∈ S, p i) * a := by
  let C (i : ι) : Set (β i) :=
    if h : i = w then h.symm ▸ cross else if i ∈ S then B i else univ
  have hsub : {z | (∀ i ∈ S, z i ∈ B i) ∧ z w ∈ cross} ⊆ univ.pi C := by
    intro z hz
    refine mem_pi.mpr fun i _ ↦ ?_
    by_cases h : i = w
    · subst i
      simpa only [C, dite_eq_left rfl] using hz.2
    · by_cases hi : i ∈ S
      · simpa only [C, dite_eq_right h, ite_eq_left hi] using hz.1 i hi
      · simp only [C, dite_eq_right h, ite_eq_right hi, mem_univ]
  calc
    _ ≤ (Measure.pi ν) (univ.pi C) := measure_mono hsub
    _ = ∏ i, ν i (C i) := Measure.pi_pi ν C
    _ ≤ ∏ i, if i ∈ S then p i * (if i = w then a else 1) else 1 := by
      refine Finset.prod_le_prod fun i _ ↦ ?_
      by_cases h : i = w
      · subst i
        simpa only [C, dite_eq_left rfl, ite_eq_left rfl, ite_eq_left hw, ite_true] using hcross
      · by_cases hi : i ∈ S
        · simpa only [C, dite_eq_right h, ite_eq_left hi, ite_eq_right h, mul_one] using hB i hi
        · simp only [C, dite_eq_right h, ite_eq_right hi, measure_univ, le_refl]
    _ = _ := by
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_mul_distrib,
        Finset.prod_ite_eq_of_mem' S w _ hw]

/-- Sum the marked-coordinate bounds over all possible marked pairs.
No independence between distinct marked pairs is needed. -/
theorem measure_pi_exists_markedColumn_le {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (ν : ∀ i, Measure (β i))
    [∀ i, IsProbabilityMeasure (ν i)] (S : Finset ι) (P : Finset τ)
    (B : ∀ i, Set (β i)) (cross : ∀ (_ : τ) i, Set (β i)) (p : ι → ℝ≥0∞) (a : τ → ℝ≥0∞)
    (hB : ∀ i ∈ S, ν i (B i) ≤ p i)
    (hcross : ∀ m ∈ P, ∀ i ∈ S, ν i (cross m i) ≤ p i * a m) :
    (Measure.pi ν) {z | (∀ i ∈ S, z i ∈ B i) ∧ ∃ m ∈ P, ∃ i ∈ S, z i ∈ cross m i} ≤
      (∏ i ∈ S, p i) * (S.card : ℝ≥0∞) * ∑ m ∈ P, a m := by
  classical
  let E (q : P × S) : Set ((i : ι) → β i) :=
    {z | (∀ i ∈ S, z i ∈ B i) ∧ z q.2.val ∈ cross q.1.val q.2.val}
  have hsub : {z | (∀ i ∈ S, z i ∈ B i) ∧ ∃ m ∈ P, ∃ i ∈ S, z i ∈ cross m i} ⊆
      ⋃ q, E q := by
    rintro z ⟨h, m, hm, i, hi, hc⟩
    exact mem_iUnion.mpr ⟨⟨⟨m, hm⟩, ⟨i, hi⟩⟩, h, hc⟩
  calc
    _ ≤ ∑ q : P × S, (Measure.pi ν) (E q) :=
      (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ q : P × S, (∏ i ∈ S, p i) * a q.1.val :=
      Finset.sum_le_sum fun q _ ↦ measure_pi_markedColumn_le ν S B p q.2.val q.2.property
        (cross q.1.val q.2.val) (a q.1.val) hB (hcross _ q.1.property _ q.2.property)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum, Finset.sum_coe_sort]
      ac_rfl

end LennonPittelFormalization

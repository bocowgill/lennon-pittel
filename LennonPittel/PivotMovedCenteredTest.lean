module

public import LennonPittel.PivotEnlargedConditionalMean
public import LennonPittel.PivotLaterRevealReplay

/-!
# The moved-women test at a later stable matching

A reverse decoration at a later matching is moved-only when each woman in
its support changed partners since the earlier matching. The enlarged reveal
at the earlier matching determines this count and the later conditional mean.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ}

/-- A stable matching strictly later than the first in men's preference order.
Stability of the earlier matching is imposed separately by its marked law. -/
def IsStrictLaterStable (x : ScoreProfile n) (μ ν : Matching n) : Prop :=
  IsScoreStable x ν ∧ μ ≠ ν ∧ MenWeaklyPrefer (profileOfScores x) μ ν

theorem measurableSet_isStrictLaterStable (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsStrictLaterStable x μ ν} :=
  (measurableSet_isScoreStable ν).inter ((MeasurableSet.const _).inter
    (measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | MenWeaklyPrefer p μ ν})))

/-- Keep only the filtered choices supported on women who changed husbands. -/
noncomputable def markedMovedChoices (μ ν σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (markedFilteredChoices ν σ flag K L t x).filter
    (fun τ ↦ ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w)

theorem mem_markedMovedChoices {μ ν σ τ : Matching n} {flag : OffDiagonalCellIndex n → Bool}
    {K L : ℕ} {t : ℝ} {x : ScoreProfile n} :
    τ ∈ markedMovedChoices μ ν σ flag K L t x ↔
      τ ∈ markedFilteredChoices ν σ flag K L t x ∧
        ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w := by
  classical
  simp only [markedMovedChoices, Finset.mem_filter]

/-- The moved-only count at the later pivot, zero off its eligibility event.
The comparison order of the marks is imposed separately. -/
noncomputable def localMovedDecorationCount (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsLocallyEligiblePivot b A B x ν σ then
    ((markedMovedChoices μ ν σ (forwardMaskOfScores (splitScorePairs ν x).1
      (splitScorePairs ν x).2) K L (reverseIncrementCutoff n (maleSpouseTotal x ν)) x).card : ℝ)
    else 0

theorem localMovedDecorationCount_nonneg (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n)
    (x : ScoreProfile n) : 0 ≤ localMovedDecorationCount b A B K L μ ν σ x := by
  classical
  unfold localMovedDecorationCount
  split <;> positivity

theorem localMovedDecorationCount_le (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n)
    (x : ScoreProfile n) :
    localMovedDecorationCount b A B K L μ ν σ x ≤ localFilteredDecorationCount b A B K L ν σ x := by
  classical
  by_cases h : IsLocallyEligiblePivot b A B x ν σ
  · simp only [localMovedDecorationCount, localFilteredDecorationCount, ite_eq_left h, Nat.cast_le]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  · simp only [localMovedDecorationCount, localFilteredDecorationCount, ite_eq_right h, le_refl]

private theorem measurable_moved_mask_switch {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [Countable β]
    [MeasurableSingletonClass β] {M : α → β} (hM : Measurable M)
    {f : β → α → γ} (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x ↦ f (M x) x) := by
  intro s hs
  let E (j : β) := {x : α | M x = j ∧ f j x ∈ s}
  have he : (fun x ↦ f (M x) x) ⁻¹' s = ⋃ j, E j := by
    ext x
    change f (M x) x ∈ s ↔ x ∈ ⋃ j, E j
    simp only [mem_iUnion, E, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨M x, rfl, hx⟩, fun ⟨j, hj, hx⟩ ↦ hj.symm ▸ hx⟩
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ (hM (measurableSet_singleton j)).inter (hf j hs)

theorem measurable_localMovedDecorationCount (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    Measurable (localMovedDecorationCount b A B K L μ ν σ) := by
  classical
  let M (x : ScoreProfile n) :=
    forwardMaskOfScores (splitScorePairs ν x).1 (splitScorePairs ν x).2
  let t (x : ScoreProfile n) := reverseIncrementCutoff n (maleSpouseTotal x ν)
  let f (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :=
    ((markedMovedChoices μ ν σ flag K L (t x) x).card : ℝ)
  have hM : Measurable M := (measurable_jointForwardMaskOfScores n).comp
    (splitScorePairs ν).measurable
  have ht : Measurable t := measurable_const.div (measurable_maleSpouseTotal ν)
  have hf (flag : OffDiagonalCellIndex n → Bool) : Measurable (f flag) := by
    have hmem (τ : Matching n) :
        MeasurableSet {x : ScoreProfile n | τ ∈ markedMovedChoices μ ν σ flag K L (t x) x} := by
      simp only [mem_markedMovedChoices, ofPred_and]
      exact (measurableSet_mem_markedFilteredChoices ν σ τ flag K L ht).inter
        (MeasurableSet.const _)
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using
      ENNReal.measurable_toReal.comp (measurable_finsetCard_of_mem _ hmem)
  exact (measurable_moved_mask_switch hM hf).ite
    (measurableSet_isLocallyEligiblePivot b A B ν σ) measurable_const

/-- The earlier full reveal determines whether a fixed matching is strictly later and stable. -/
theorem FullForwardRevealAgrees.isStrictLaterStable_iff
    {x y : ScoreProfile n} {μ ν : Matching n} (h : FullForwardRevealAgrees x y μ)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hμx : IsStable (profileOfScores x) μ) (hμy : IsStable (profileOfScores y) μ) :
    IsStrictLaterStable x μ ν ↔ IsStrictLaterStable y μ ν := by
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v μ)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hμu : IsStable (profileOfScores u) μ) (hμv : IsStable (profileOfScores v) μ)
      (hs : IsStrictLaterStable u μ ν) : IsStrictLaterStable v μ ν := by
    obtain ⟨hνv, hμνv, _⟩ := huv.later hu hv hμu hμv
      ((isStable_profileOfScores_iff hu ν).mpr hs.1) hs.2.2
    exact ⟨(isStable_profileOfScores_iff hv ν).mp hνv, hs.2.1, hμνv⟩
  exact ⟨transport h hx hy hμx hμy, transport h.symm hy hx hμy hμx⟩

/-- At a later stable mark, replaying the earlier full reveal preserves the moved-only count. -/
theorem FullForwardRevealAgrees.localMovedDecorationCount_eq_of_later
    {x y : ScoreProfile n} {μ ν : Matching n} (h : FullForwardRevealAgrees x y μ)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hμx : IsStable (profileOfScores x) μ) (hμy : IsStable (profileOfScores y) μ)
    (hνx : IsStable (profileOfScores x) ν) (hμν : MenWeaklyPrefer (profileOfScores x) μ ν)
    (b A B : ℝ) (K L : ℕ) (σ : Matching n) :
    localMovedDecorationCount b A B K L μ ν σ x = localMovedDecorationCount b A B K L μ ν σ y := by
  classical
  obtain ⟨_, _, hνReveal⟩ := h.later hx hy hμx hμy hνx hμν
  have hE := hνReveal.locallyEligible_iff b A B σ
  by_cases hEx : IsLocallyEligiblePivot b A B x ν σ
  · have hEy := hE.mp hEx
    have hσ := (hEx.isSoleForwardExposed hx).1
    have htot : maleSpouseTotal x ν = maleSpouseTotal y ν := by
      rw [← reverseDiagonalMaleTotal_splitScorePairs ν x, ← reverseDiagonalMaleTotal_splitScorePairs ν y,
        hνReveal.diagonal_eq]
    simp only [localMovedDecorationCount, ite_eq_left hEx, ite_eq_left hEy,
      ← hνReveal.mask_eq, ← htot]
    congr 2
    ext τ
    simp only [mem_markedMovedChoices, mem_markedFilteredChoices]
    by_cases hw : ∀ w ∈ τ.support, ν.symm w ≠ μ.symm w
    · rw [h.mem_filteredReverseSupportFamily_iff_of_changed hx hy hμx hμy hνx hμν
        hσ hw _ _ _ _]
    · simp only [hw, and_false]
  · simp only [localMovedDecorationCount, ite_eq_right hEx, ite_eq_right (mt hE.mpr hEx)]

private noncomputable def actualLaterMovedCenteredTest (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x μ ν then
    localMovedDecorationCount b A B K L μ ν σ x - localPivotInactiveMean b A B K L ν σ x else 0

/-- The moved count minus the later full-count mean, restricted to strictly
later stable marks and evaluated on the completion of the earlier reveal. -/
@[no_expose] noncomputable def laterMovedCenteredTest (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) (x : ScoreProfile n) : ℝ :=
  actualLaterMovedCenteredTest b A B K L μ ν σ
    (pivotFullRevealCompletion μ (pivotFullReveal μ x))

theorem measurable_laterMovedCenteredTest (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    Measurable[pivotFullRevealSpace μ] (laterMovedCenteredTest b A B K L μ ν σ) := by
  have hbase : Measurable (actualLaterMovedCenteredTest b A B K L μ ν σ) :=
    ((measurable_localMovedDecorationCount b A B K L μ ν σ).sub
      ((measurable_maleReveal_localPivotInactiveMean b A B K L ν σ).mono
        (pivotMaleRevealSpace_le ν) le_rfl)).ite (measurableSet_isStrictLaterStable μ ν)
          measurable_const
  exact hbase.comp (measurable_pivotFullRevealCompletion_from_reveal μ)

open scoped Classical in
/-- On the earlier marked law the completed test equals its actual-score
version, with the true conditional mean at the later mark. -/
theorem laterMovedCenteredTest_ae_eq (b A B : ℝ) (K L : ℕ) (μ ν σ : Matching n) :
    laterMovedCenteredTest b A B K L μ ν σ =ᵐ[stableMarkScoreLaw μ]
      fun x ↦ if IsStrictLaterStable x μ ν then
        localMovedDecorationCount b A B K L μ ν σ x -
          localPivotConditionalMean b A B K L ν σ x else 0 := by
  have hmean : ∀ᵐ x ∂stableMarkScoreLaw μ, IsScoreStable x ν →
      localPivotInactiveMean b A B K L ν σ x = localPivotConditionalMean b A B K L ν σ x := by
    apply ae_restrict_of_ae
    exact (ae_restrict_iff' (measurableSet_isScoreStable ν)).mp
      (localPivotInactiveMean_ae_eq_conditionalMean b A B K L ν σ)
  filter_upwards [ae_restrict_mem (measurableSet_isScoreStable μ),
    ae_restrict_of_ae (ae_injective_rows n), ae_restrict_of_ae (ae_unitOpen_scores n),
    hmean] with x hμs hx hu hmean
  let y := pivotFullRevealCompletion μ (pivotFullReveal μ x)
  obtain ⟨hy, hμy, h⟩ := pivotFullRevealCompletion_spec (A := μ) hx (fun r i ↦ (hu r i).2)
  have hμx := (isStable_profileOfScores_iff hx μ).mpr hμs
  have hs : IsStrictLaterStable x μ ν ↔ IsStrictLaterStable y μ ν :=
    h.isStrictLaterStable_iff hx hy hμx hμy
  change (if IsStrictLaterStable y μ ν then
    localMovedDecorationCount b A B K L μ ν σ y - localPivotInactiveMean b A B K L ν σ y
    else 0) = _
  by_cases hsx : IsStrictLaterStable x μ ν
  · have hsy := hs.mp hsx
    have hνx := (isStable_profileOfScores_iff hx ν).mpr hsx.1
    have hmov := h.localMovedDecorationCount_eq_of_later hx hy hμx hμy hνx hsx.2.2 b A B K L σ
    obtain ⟨_, _, hνReveal⟩ := h.later hx hy hμx hμy hνx hsx.2.2
    have hreveal : pivotMaleReveal ν x = pivotMaleReveal ν y := by
      have hfull := fullForwardRevealAgrees_iff_pivotFullReveal_eq.mp hνReveal
      simpa only [pivotFullReveal_fst] using congrArg Prod.fst hfull
    have hmeanXY : localPivotInactiveMean b A B K L ν σ x =
        localPivotInactiveMean b A B K L ν σ y := by
      unfold localPivotInactiveMean
      rw [hreveal]
    rw [ite_eq_left hsy, ite_eq_left hsx, ← hmov, ← hmeanXY, hmean hsx.1]
  · rw [ite_eq_right (mt hs.mpr hsx), ite_eq_right hsx]

/-- The centered test is bounded on the earlier marked law by the number of
permutations; this bound does not require either mark to be locally eligible. -/
theorem laterMovedCenteredTest_abs_le_factorial_ae (b A B : ℝ) (K L : ℕ)
    (μ ν σ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ, |laterMovedCenteredTest b A B K L μ ν σ x| ≤ (n.factorial : ℝ) := by
  classical
  have hmean : ∀ᵐ x ∂stableMarkScoreLaw μ, IsScoreStable x ν →
      localPivotConditionalMean b A B K L ν σ x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
    apply ae_restrict_of_ae
    exact (ae_restrict_iff' (measurableSet_isScoreStable ν)).mp
      (localPivotConditionalMean_mem_Icc_ae b A B K L ν σ)
  filter_upwards [laterMovedCenteredTest_ae_eq b A B K L μ ν σ, hmean] with x he hmean
  rw [he]
  by_cases hs : IsStrictLaterStable x μ ν
  · rw [ite_eq_left hs, abs_le]
    have hh := hmean hs.1
    have hm0 := localMovedDecorationCount_nonneg b A B K L μ ν σ x
    have hmle := (localMovedDecorationCount_le b A B K L μ ν σ x).trans
      (localFilteredDecorationCount_le_factorial b A B K L ν σ x)
    constructor <;> linarith [hh.1, hh.2]
  · rw [ite_eq_right hs, abs_zero]
    positivity

end LennonPittelFormalization

module

public import LennonPittel.PivotCenteredReduction
public import LennonPittel.PivotSharedReverse

/-!
# The residual count as actual pairs of eligible choices

Subtracting the moved-only later count leaves precisely the choices that move
an unchanged woman. The resulting finite count maps to the shared-switch
toggle without forgetting the eligibility of either original mark.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization
namespace PivotCountParameters

variable {n : ℕ}

/-- The forward mask at a fixed anchor, independent of the marked cycle. -/
noncomputable def residualChoiceFlag (x : ScoreProfile n) (μ _ : Matching n) :
    OffDiagonalCellIndex n → Bool :=
  forwardMaskOfScores (splitScorePairs μ x).1 (splitScorePairs μ x).2

/-- The reverse increment cutoff at an anchor. -/
noncomputable def residualChoiceCutoff (x : ScoreProfile n) (μ _ : Matching n) : ℝ :=
  reverseIncrementCutoff n (maleSpouseTotal x μ)

private noncomputable def choices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : Finset (Matching n) :=
  markedFilteredChoices i.1 i.2 (residualChoiceFlag x i.1 i.2)
    q.supportCap q.shortCutoff (residualChoiceCutoff x i.1 i.2) x

/-- The actual filtered choices, with an empty set when the mark fails either
stability or eligibility. -/
@[no_expose] noncomputable def eligibleChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : Finset (Matching n) := by
  classical
  exact if IsScoreStable x i.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2
    then q.choices x i else ∅

private noncomputable def residualLaterChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i j : PivotMark n) : Finset (Matching n) := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2 then
    (q.choices x j).filter (fun τ ↦ ¬ ∀ w ∈ τ.support, j.1.symm w ≠ i.1.symm w)
    else ∅

/-- The extended local count is the cardinality of its choices. -/
theorem count_eq_card_eligibleChoices (q : PivotCountParameters) (x : ScoreProfile n)
    (i : PivotMark n) : q.count i x = (q.eligibleChoices x i).card := by
  classical
  by_cases hs : IsScoreStable x i.1 <;>
    by_cases he : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 <;>
    simp [count, onStableMark, localCount, localFilteredDecorationCount,
      eligibleChoices, choices, residualChoiceFlag, residualChoiceCutoff, hs, he]

private theorem localLaterResidual_eq_card (q : PivotCountParameters) (x : ScoreProfile n)
    (i j : PivotMark n) : q.localLaterResidual i j x = (q.residualLaterChoices x i j).card := by
  classical
  by_cases ho : IsStrictLaterStable x i.1 j.1
  · by_cases he : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2
    · let p (τ : Matching n) := ∀ w ∈ τ.support, j.1.symm w ≠ i.1.symm w
      have h := Finset.card_filter_add_card_filter_not (s := q.choices x j) p
      have hc : (((q.choices x j).filter p).card : ℝ) +
          (((q.choices x j).filter (fun τ ↦ ¬ p τ)).card : ℝ) =
          ((q.choices x j).card : ℝ) := by exact_mod_cast h
      rw [localLaterResidual, ite_eq_left ho, localCount, localFilteredDecorationCount, ite_eq_left he,
        localMovedDecorationCount, ite_eq_left he, residualLaterChoices, ite_eq_left ⟨ho, he⟩]
      change ((q.choices x j).card : ℝ) - (((q.choices x j).filter p).card : ℝ) =
        (((q.choices x j).filter (fun τ ↦ ¬ p τ)).card : ℝ)
      linarith only [hc]
    · simp [localLaterResidual, localCount, localFilteredDecorationCount,
        localMovedDecorationCount, residualLaterChoices, ho, he]
  · simp [localLaterResidual, residualLaterChoices, ho]

/-- Ordered marks paired with an earlier filtered choice and a shared later choice. -/
@[no_expose] noncomputable def residualChoicePairs (q : PivotCountParameters) (x : ScoreProfile n) :
    Finset (Σ _ : PivotMark n × PivotMark n, Matching n × Matching n) :=
  Finset.univ.sigma fun ij ↦ (q.eligibleChoices x ij.1).product
    (q.residualLaterChoices x ij.1 ij.2)

/-- The actual real-valued summand counts these finite ordered pairs. -/
theorem comparableResidualMass_eq_card (q : PivotCountParameters) (x : ScoreProfile n) :
    q.comparableResidualMass x = (q.residualChoicePairs x).card := by
  rw [residualChoicePairs, Finset.card_sigma, Nat.cast_sum, Fintype.sum_prod_type]
  unfold comparableResidualMass
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  change q.comparableResidualTerm i j x =
    (((q.eligibleChoices x i).product (q.residualLaterChoices x i j)).card : ℝ)
  rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul, comparableResidualTerm,
    q.count_eq_card_eligibleChoices, q.localLaterResidual_eq_card]

private theorem data_of_eligibleChoices {q : PivotCountParameters} {x : ScoreProfile n}
    {i : PivotMark n} {a : Matching n} (h : a ∈ q.eligibleChoices x i) :
    IsScoreStable x i.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
      a ∈ q.choices x i := by
  classical
  unfold eligibleChoices at h
  split at h
  · rename_i hi
    exact ⟨hi.1, hi.2, h⟩
  · exact (Finset.notMem_empty _ h).elim

/-- Membership retains both mark hypotheses and all the original filters. -/
theorem eligibleChoices_data {q : PivotCountParameters} {x : ScoreProfile n}
    {i : PivotMark n} {a : Matching n} (h : a ∈ q.eligibleChoices x i) :
    IsScoreStable x i.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
      a ∈ markedFilteredChoices i.1 i.2 (residualChoiceFlag x i.1 i.2)
        q.supportCap q.shortCutoff (residualChoiceCutoff x i.1 i.2) x :=
  data_of_eligibleChoices h

private theorem data_of_residualLaterChoices {q : PivotCountParameters} {x : ScoreProfile n}
    {i j : PivotMark n} {a : Matching n} (h : a ∈ q.residualLaterChoices x i j) :
    IsStrictLaterStable x i.1 j.1 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2 ∧
      a ∈ q.choices x j ∧ ∃ w ∈ a.support, i.1.symm w = j.1.symm w := by
  classical
  unfold residualLaterChoices at h
  split at h
  · rename_i hj
    obtain ⟨ha, hnot⟩ := Finset.mem_filter.mp h
    push Not at hnot
    obtain ⟨w, hw, heq⟩ := hnot
    exact ⟨hj.1, hj.2, ha, w, hw, heq.symm⟩
  · exact (Finset.notMem_empty _ h).elim

theorem residualChoicePair_eligible (q : PivotCountParameters) {x : ScoreProfile n}
    (a : ↥(q.residualChoicePairs x)) :
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x a.val.1.1.1 a.val.1.1.2 ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x
        a.val.1.2.1 a.val.1.2.2 := by
  have h := Finset.mem_product.mp (Finset.mem_sigma.mp a.property).2
  exact ⟨(data_of_eligibleChoices h.1).2.1, (data_of_residualLaterChoices h.2).2.1⟩

/-- Recover the ordered pair of marked choices counted by the residual summand. -/
@[no_expose] noncomputable def residualMarkedPairOfChoice (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row))
    (hlong : ∀ i : PivotMark n,
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.supportCap < i.2.support.card)
    (hcut : ∀ i : PivotMark n, 0 ≤ residualChoiceCutoff x i.1 i.2)
    (a : ↥(q.residualChoicePairs x)) :
    ResidualMarkedPair x q.supportCap q.shortCutoff (residualChoiceFlag x) (residualChoiceCutoff x) :=
  let h := Finset.mem_product.mp (Finset.mem_sigma.mp a.property).2
  let he := data_of_eligibleChoices h.1
  let hl := data_of_residualLaterChoices h.2
  ⟨⟨a.val.1.1.1, a.val.1.1.2, a.val.2.1, (isStable_profileOfScores_iff hties _).mpr he.1,
      he.2.1.isSoleForwardExposed hties, hlong _ he.2.1, hcut _, he.2.2⟩,
    ⟨a.val.1.2.1, a.val.1.2.2, a.val.2.2, (isStable_profileOfScores_iff hties _).mpr hl.1.1,
      hl.2.1.isSoleForwardExposed hties, hlong _ hl.2.1, hcut _, hl.2.2.1⟩,
    hl.1.2.2, hl.1.2.1, hl.2.2.2⟩


/-- The reconstructed pair retains eligibility at both marks. -/
theorem residualMarkedPairOfChoice_eligible (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut)
    (a : ↥(q.residualChoicePairs x)) :
    let R := q.residualMarkedPairOfChoice hties hlong hcut a
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget
        x R.early.anchor R.early.cycle ∧
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget
        x R.late.anchor R.late.cycle :=
  q.residualChoicePair_eligible a

theorem residualMarkedPairOfChoice_injective (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut) :
    Function.Injective (q.residualMarkedPairOfChoice hties hlong hcut) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun R ↦ (⟨((R.early.anchor, R.early.cycle), (R.late.anchor, R.late.cycle)),
    (R.early.reverse, R.late.reverse)⟩ :
      Σ _ : PivotMark n × PivotMark n, Matching n × Matching n)) hab

/-- The finite comparable residual is at most twice the number of toggle images
satisfying any condition proved for the actual eligible choices. -/
theorem comparableResidualMass_le_twice_restrict (q : PivotCountParameters)
    {x : ScoreProfile n} {μ₀ : Matching n} (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut)
    {Q : IncomparableStableMatchingPair (profileOfScores x) μ₀ → Prop}
    (hQ : ∀ a : ↥(q.residualChoicePairs x),
      Q ((q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt).toggleImage) :
    q.comparableResidualMass x ≤ 2 * (Nat.card {MN // Q MN} : ℝ) := by
  let f (a : ↥(q.residualChoicePairs x)) :=
    (q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt
  let P (R : ResidualPivotPair hopt q.supportCap) := ∃ a, f a = R
  let e (a : ↥(q.residualChoicePairs x)) : {R // P R} := ⟨f a, ⟨a, rfl⟩⟩
  have hinj : Function.Injective f :=
    (ResidualMarkedPair.toResidualPivotPair_injective hopt).comp
      (q.residualMarkedPairOfChoice_injective hties hlong hcut)
  have hcard := Nat.card_le_card_of_injective e
    (fun _ _ h ↦ hinj (congrArg Subtype.val h))
  have ht : Nat.card {R // P R} ≤ 2 * Nat.card {MN // Q MN} := by
    apply ResidualPivotPair.card_le_twice_incomparable_restrict
    rintro _ ⟨a, rfl⟩
    exact hQ a
  rw [q.comparableResidualMass_eq_card]
  rw [Nat.card_eq_finsetCard] at hcard
  exact_mod_cast hcard.trans ht

end PivotCountParameters
end LennonPittelFormalization

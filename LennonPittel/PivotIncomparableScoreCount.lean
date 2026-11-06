module

public import LennonPittel.PivotResidualCountBridge

/-!
# Integrating the eligible residual image count

The target count is written over fixed labeled matching pairs. It uses
the two stability tests and both preference-order failures, not a choice
of a man-optimal matching in the score probability space.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The event for a fixed ordered incomparable pair, with a further score test. -/
def scoreIncomparablePairEvent (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (μ ν : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    IncomparableAnchors (profileOfScores x) μ ν ∧ Q x μ ν}

theorem measurableSet_scoreIncomparablePairEvent
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) (μ ν : Matching n) :
    MeasurableSet (scoreIncomparablePairEvent Q μ ν) :=
  (measurableSet_isScoreStable μ).inter ((measurableSet_isScoreStable ν).inter
    ((measurableSet_incomparableAnchors μ ν).inter (hQ μ ν)))

/-- The finite set of ordered incomparable matching pairs satisfying the extra score test. -/
noncomputable def incomparableScorePairs
    (Q : ScoreProfile n → Matching n → Matching n → Prop)
    (x : ScoreProfile n) : Finset (Matching n × Matching n) := by
  classical
  exact Finset.univ.filter (fun mn ↦ x ∈ scoreIncomparablePairEvent Q mn.1 mn.2)

theorem mem_incomparableScorePairs {Q : ScoreProfile n → Matching n → Matching n → Prop}
    {x : ScoreProfile n} {mn : Matching n × Matching n} :
    mn ∈ incomparableScorePairs Q x ↔ x ∈ scoreIncomparablePairEvent Q mn.1 mn.2 := by
  classical
  simp [incomparableScorePairs]

/-- Count qualifying ordered incomparable matching pairs in a score array. -/
noncomputable def incomparableScorePairCount
    (Q : ScoreProfile n → Matching n → Matching n → Prop) (x : ScoreProfile n) : ℝ :=
  (incomparableScorePairs Q x).card

theorem incomparableScorePairCount_eq_sum
    (Q : ScoreProfile n → Matching n → Matching n → Prop) (x : ScoreProfile n) :
    incomparableScorePairCount Q x =
      ∑ mn : Matching n × Matching n,
        (scoreIncomparablePairEvent Q mn.1 mn.2).indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  simp only [incomparableScorePairCount, incomparableScorePairs, indicator_apply]
  rw [← Finset.sum_filter]
  simp

theorem integrable_incomparableScorePairCount
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) :
    Integrable (incomparableScorePairCount Q) (continuousScoreLaw n) := by
  have h (mn : Matching n × Matching n) :
      Integrable ((scoreIncomparablePairEvent Q mn.1 mn.2).indicator (fun _ ↦ (1 : ℝ)))
        (continuousScoreLaw n) :=
    (integrable_const _).indicator (measurableSet_scoreIncomparablePairEvent hQ mn.1 mn.2)
  exact (integrable_finsetSum _ fun mn _ ↦ h mn).congr
    (Eventually.of_forall fun x ↦ (incomparableScorePairCount_eq_sum Q x).symm)

/-- The expected count is the sum of the original-law masses of the fixed-pair events. -/
theorem integral_incomparableScorePairCount
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν}) :
    (∫ x, incomparableScorePairCount Q x ∂continuousScoreLaw n) =
      ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real (scoreIncomparablePairEvent Q μ ν) := by
  simp_rw [incomparableScorePairCount_eq_sum]
  rw [integral_finsetSum _ (fun mn _ ↦ (integrable_const _).indicator
    (measurableSet_scoreIncomparablePairEvent hQ mn.1 mn.2)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [integral_indicator_const _ (measurableSet_scoreIncomparablePairEvent hQ μ ν), smul_eq_mul,
    mul_one]

private theorem card_incomparableStableMatchingPair_restrict_le
    {Q : ScoreProfile n → Matching n → Matching n → Prop} {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) {μ₀ : Matching n}
    (hopt : IsManOptimal (profileOfScores x) μ₀) :
    Nat.card {MN : IncomparableStableMatchingPair (profileOfScores x) μ₀ //
        Q x MN.val.1.val MN.val.2.val} ≤ (incomparableScorePairs Q x).card := by
  classical
  let f (z : {MN : IncomparableStableMatchingPair (profileOfScores x) μ₀ //
      Q x MN.val.1.val MN.val.2.val}) : ↥(incomparableScorePairs Q x) := by
    let a := z.val.val.1
    let b := z.val.val.2
    refine ⟨(a.val, b.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨(isStable_profileOfScores_iff hties _).mp a.property,
      (isStable_profileOfScores_iff hties _).mp b.property,
      ⟨fun h ↦ z.val.property.1 ((eliminatedRotations_subset_iff hopt a.property b.property).mpr h),
        fun h ↦ z.val.property.2 ((eliminatedRotations_subset_iff hopt b.property a.property).mpr h)⟩,
      z.property⟩
  have h : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have hp := congrArg Subtype.val hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))
  simpa only [Nat.card_eq_finsetCard] using Nat.card_le_card_of_injective f h

namespace PivotCountParameters

theorem residualChoiceCutoff_nonneg {x : ScoreProfile n}
    (hx : ∀ r i, 0 ≤ x r i) (i : PivotMark n) :
    0 ≤ residualChoiceCutoff x i.1 i.2 := by
  unfold residualChoiceCutoff reverseIncrementCutoff
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _))
    (Finset.sum_nonneg fun m _ ↦ hx (.inl m) (i.1 m))

/-- Count the toggle images in the score space without making a measurable
selection of a man-optimal reference matching. -/
theorem comparableResidualMass_le_twice_scorePairCount (q : PivotCountParameters)
    {Q : ScoreProfile n → Matching n → Matching n → Prop} {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (hlong) (hcut)
    (hQ : ∀ μ₀ (hopt : IsManOptimal (profileOfScores x) μ₀) (a : ↥(q.residualChoicePairs x)),
      Q x ((q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt).toggleImage.val.1.val
        ((q.residualMarkedPairOfChoice hties hlong hcut a).toResidualPivotPair hopt).toggleImage.val.2.val) :
    q.comparableResidualMass x ≤ 2 * incomparableScorePairCount Q x := by
  classical
  by_cases h : Nonempty ↥(q.residualChoicePairs x)
  · let a := Classical.choice h
    let R := q.residualMarkedPairOfChoice hties hlong hcut a
    obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨R.early.anchor, R.early.stable⟩
    have hc := q.comparableResidualMass_le_twice_restrict hopt hties hlong hcut
      (Q := fun MN ↦ Q x MN.val.1.val MN.val.2.val) (hQ μ₀ hopt)
    exact hc.trans (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (card_incomparableStableMatchingPair_restrict_le (Q := Q) hties hopt))
      (by norm_num))
  · have hz : (q.residualChoicePairs x).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun _ hm ↦ h ⟨⟨_, hm⟩⟩
    rw [q.comparableResidualMass_eq_card, hz, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- An almost-sure geometric image bound suffices for the comparable contribution. -/
theorem integral_comparableResidualMass_le_twice_sum (q : PivotCountParameters)
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν})
    (h : q.comparableResidualMass ≤ᵐ[continuousScoreLaw n]
      fun x ↦ 2 * incomparableScorePairCount Q x) :
    (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
      2 * ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real (scoreIncomparablePairEvent Q μ ν) := by
  have hR : Integrable (q.comparableResidualMass (n := n)) (continuousScoreLaw n) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_comparableResidualTerm i j
  have hi := integral_mono_ae hR ((integrable_incomparableScorePairCount hQ).const_mul 2) h
  rw [integral_const_mul, integral_incomparableScorePairCount hQ] at hi
  exact hi

end PivotCountParameters
end LennonPittelFormalization

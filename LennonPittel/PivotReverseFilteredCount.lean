module

public import LennonPittel.PivotCompatibleLowerMoment
public import LennonPittel.PivotReverseIncrementFilter
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The subset-closed filters on compatible reverse collections

Both the short-cycle cap and the score-increment cutoff are tests on the
chosen collection at its anchor. Removing cycles preserves either test.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The forbidden side of the short-cycle cap, as a predicate on cycle type. -/
def shortCycleCapBad (L : ℕ) (T : Multiset ℕ) : Prop :=
  (3 / 2 : ℝ) * Real.log (L : ℝ) < ((T.filter (· ≤ L)).card : ℝ)

/-- All moved women in the reverse collection pass the increment cutoff. -/
def reverseCollectionIncrementGood {n : ℕ} (x : ScoreProfile n) (μ σ : Matching n)
    (t : ℝ) : Prop :=
  ∀ w ∈ σ.support, reverseScoreIncrement x μ w (μ.symm (σ w)) ≤ t

theorem measurableSet_reverseCollectionIncrementGood {n : ℕ} (μ σ : Matching n) (t : ℝ) :
    MeasurableSet {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ t} := by
  have he : {x : ScoreProfile n | reverseCollectionIncrementGood x μ σ t} =
      ⋂ w : σ.support, {x : ScoreProfile n |
        reverseScoreIncrement x μ w.val (μ.symm (σ w.val)) ≤ t} := by
    ext x
    exact ⟨fun hx ↦ mem_iInter.mpr fun w ↦ hx w.val w.property,
      fun hx w hw ↦ mem_iInter.mp hx ⟨w, hw⟩⟩
  rw [he]
  exact MeasurableSet.iInter fun w ↦ measurableSet_le
    (measurable_reverseScoreIncrement μ w.val (μ.symm (σ w.val))) measurable_const

/-- The two tests are preserved by taking a subcollection of cycle factors. -/
theorem reverseCollectionFilters_mono {n : ℕ} (x : ScoreProfile n) (μ σ τ : Matching n)
    (L : ℕ) (t : ℝ) (hsub : τ.cycleFactorsFinset ⊆ σ.cycleFactorsFinset)
    (hcap : ¬ shortCycleCapBad L σ.cycleType) (hinc : reverseCollectionIncrementGood x μ σ t) :
    ¬ shortCycleCapBad L τ.cycleType ∧ reverseCollectionIncrementGood x μ τ t := by
  have hcard : (τ.cycleType.filter (· ≤ L)).card ≤ (σ.cycleType.filter (· ≤ L)).card := by
    simp only [Equiv.Perm.cycleType_def, Multiset.filter_map, Multiset.card_map]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  refine ⟨not_lt.mpr ((Nat.cast_le.mpr hcard).trans (not_lt.mp hcap)), ?_⟩
  intro w hw
  obtain ⟨c, hc, hwc⟩ := Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hw
  have hcs := hsub hc
  have hws := Equiv.Perm.mem_cycleFactorsFinset_support_le hcs hwc
  have heq : τ w = σ w := ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 w hwc).symm.trans
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcs).2 w hwc)
  rw [heq]
  exact hinc w hws

/-- Failing the increment test in a realized collection forces the global
long finite successor event at the same anchor. -/
theorem mem_scoreLongReverseSuccessorEvent_of_not_incrementGood {n : ℕ}
    (x : ScoreProfile n) (μ σ : Matching n) (t : ℝ)
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
    (hbad : ¬ reverseCollectionIncrementGood x μ σ t) : x ∈ scoreLongReverseSuccessorEvent μ t := by
  classical
  by_contra h
  apply hbad
  intro w hw
  exact le_of_not_gt fun ht ↦ h ⟨w, μ.symm (σ w), hσ w hw, ht⟩

/-- The compatible family at size `k` after both filters. -/
noncomputable def filteredReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)).filter fun σ ↦
    (¬ shortCycleCapBad L σ.cycleType) ∧ reverseCollectionIncrementGood x μ σ t

/-- The compatible family lost to the score-increment test at size `k`. -/
noncomputable def incrementRejectedReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (t : ℝ) (x : ScoreProfile n) :
    Finset (Matching n) := by
  classical
  exact (compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)).filter fun σ ↦
    ¬ reverseCollectionIncrementGood x μ σ t

/-- All static candidates of size `k` that fail the short-cycle cap. -/
noncomputable def shortCycleRejectedCandidates {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) : Finset (Matching n) := by
  classical
  exact (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
    (forwardMaskForbiddenTargets μ flag)).filter fun σ ↦ shortCycleCapBad L σ.cycleType

/-- A finite-set-valued test with measurable membership events has a measurable count. -/
theorem measurable_finsetCard_of_mem {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (F : Ω → Finset α) (hF : ∀ a, MeasurableSet {z | a ∈ F z}) :
    Measurable (fun z ↦ ((F z).card : ℝ≥0∞)) := by
  classical
  let G (a : α) := ({z | a ∈ F z} : Set Ω).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hG (a : α) : Measurable (G a) := measurable_const.indicator (hF a)
  have he : (fun z ↦ ((F z).card : ℝ≥0∞)) = fun z ↦ ∑ a, G a z := by
    funext z
    have hs : Finset.univ.filter (fun a ↦ a ∈ F z) = F z := by ext a; simp
    simp only [G, indicator_apply, mem_ofPred_eq, ← Finset.sum_filter, hs]
    simp
  rw [he]
  exact Finset.measurable_sum _ fun a _ ↦ hG a

private theorem measurableSet_mem_compatibleReverseSupportFamily {n : ℕ} (μ ρ σ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) :
    MeasurableSet {x : ScoreProfile n | σ ∈ compatibleReverseSupportFamily μ ρ flag k
      (profileOfScores x)} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete : MeasurableSet {p : Profile n |
    σ ∈ compatibleReverseSupportFamily μ ρ flag k p})

theorem measurable_card_filteredReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) :
    Measurable (fun x ↦ ((filteredReverseSupportFamily μ ρ flag k L t x).card : ℝ≥0∞)) := by
  apply measurable_finsetCard_of_mem
  intro σ
  simp only [filteredReverseSupportFamily, Finset.mem_filter, ofPred_and]
  exact (measurableSet_mem_compatibleReverseSupportFamily μ ρ σ flag k).inter
    ((MeasurableSet.const _).inter (measurableSet_reverseCollectionIncrementGood μ σ t))

theorem measurable_card_incrementRejectedReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (t : ℝ) :
    Measurable (fun x ↦ ((incrementRejectedReverseSupportFamily μ ρ flag k t x).card : ℝ≥0∞)) := by
  apply measurable_finsetCard_of_mem
  intro σ
  simp only [incrementRejectedReverseSupportFamily, Finset.mem_filter, ofPred_and]
  exact (measurableSet_mem_compatibleReverseSupportFamily μ ρ σ flag k).inter
    (measurableSet_reverseCollectionIncrementGood μ σ t).compl

/-- At each support size, any compatible collection omitted by both filters
is counted by at least one of the two rejection counts. -/
theorem card_compatibleReverseSupportFamily_le_filtered_add_rejections {n : ℕ}
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ)
    (x : ScoreProfile n) :
    (compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)).card ≤
      (filteredReverseSupportFamily μ ρ flag k L t x).card +
      realizedReversePermutationCount (shortCycleRejectedCandidates μ ρ flag k L)
        (swapProfile (profileOfScores x)) μ.symm +
      (incrementRejectedReverseSupportFamily μ ρ flag k t x).card := by
  classical
  let S := compatibleReverseSupportFamily μ ρ flag k (profileOfScores x)
  let F := filteredReverseSupportFamily μ ρ flag k L t x
  let A := (shortCycleRejectedCandidates μ ρ flag k L).filter
    (RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm)
  let B := incrementRejectedReverseSupportFamily μ ρ flag k t x
  have hsub : S ⊆ (F ∪ A) ∪ B := by
    intro σ hσ
    simp only [Finset.mem_union]
    by_cases hi : reverseCollectionIncrementGood x μ σ t
    · left
      by_cases hs : shortCycleCapBad L σ.cycleType
      · right
        have hm := mem_compatibleReversePermutations.mp hσ
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hm.1, hs⟩, hm.2.1⟩
      · left
        exact Finset.mem_filter.mpr ⟨hσ, hs, hi⟩
    · right
      exact Finset.mem_filter.mpr ⟨hσ, hi⟩
  calc
    _ ≤ ((F ∪ A) ∪ B).card := Finset.card_le_card hsub
    _ ≤ (F ∪ A).card + B.card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le F A) _

/-- Distinct support sizes give disjoint families, so their realized counts
sum to at most the number of all subsets of exposed cycles. -/
theorem sum_card_realizedReverseFamilies_le_two_pow {n : ℕ} (p : Profile n) (M : Matching n)
    (I : Finset ℕ) (S : ℕ → Finset (Matching n))
    (hsize : ∀ k ∈ I, ∀ σ ∈ S k, σ.support.card = k)
    (hreal : ∀ k ∈ I, ∀ σ ∈ S k, RealizesSuccessorPermutation p M σ) :
    (∑ k ∈ I, (S k).card) ≤ 2 ^ numExposedRotations p M := by
  classical
  have hd : (I : Set ℕ).PairwiseDisjoint S := by
    intro k hk l hl hne
    exact Finset.disjoint_left.mpr fun σ hs ht ↦ hne ((hsize k hk σ hs).symm.trans (hsize l hl σ ht))
  rw [← Finset.card_biUnion hd, ← Nat.card_eq_finsetCard, ← card_realizesSuccessorPermutation p M]
  let f (σ : ↥(I.biUnion S)) : {σ : Matching n // RealizesSuccessorPermutation p M σ} :=
    ⟨σ.val, by
      obtain ⟨k, hk, hs⟩ := Finset.mem_biUnion.mp σ.property
      exact hreal k hk σ.val hs⟩
  exact Nat.card_le_card_of_injective f fun _ _ h ↦ Subtype.ext
    (congrArg (fun y : {σ : Matching n // RealizesSuccessorPermutation p M σ} ↦ y.val) h)

/-- All increment rejections, across all support sizes, are bounded by the
total cycle-subset count on the global long-increment event. -/
theorem sum_card_incrementRejectedReverseSupportFamily_le_indicator {n : ℕ}
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool) (I : Finset ℕ) (t : ℝ)
    (x : ScoreProfile n) :
    (∑ k ∈ I, ((incrementRejectedReverseSupportFamily μ ρ flag k t x).card : ℝ≥0∞)) ≤
      (scoreLongReverseSuccessorEvent μ t).indicator (fun x ↦ (2 : ℝ≥0∞) ^
        numExposedRotations (swapProfile (profileOfScores x)) μ.symm) x := by
  classical
  let S := fun k ↦ incrementRejectedReverseSupportFamily μ ρ flag k t x
  have hσ (k : ℕ) (σ : Matching n) (h : σ ∈ S k) :
      σ.support.card = k ∧ RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ ∧
        ¬ reverseCollectionIncrementGood x μ σ t := by
    obtain ⟨hc, hb⟩ := Finset.mem_filter.mp h
    have hm := mem_compatibleReversePermutations.mp hc
    exact ⟨(mem_goodReverseSupportPermutations.mp hm.1).1, hm.2.1, hb⟩
  by_cases hx : x ∈ scoreLongReverseSuccessorEvent μ t
  · rw [indicator_of_mem hx]
    exact_mod_cast sum_card_realizedReverseFamilies_le_two_pow
      (swapProfile (profileOfScores x)) μ.symm I S (fun k _ σ h ↦ (hσ k σ h).1)
        (fun k _ σ h ↦ (hσ k σ h).2.1)
  · rw [indicator_of_notMem hx]
    have hz (k : ℕ) : S k = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun σ h ↦
      hx (mem_scoreLongReverseSuccessorEvent_of_not_incrementGood x μ σ t
        (hσ k σ h).2.1 (hσ k σ h).2.2)
    change (∑ k ∈ I, ((S k).card : ℝ≥0∞)) ≤ 0
    simp only [hz, Finset.card_empty, Nat.cast_zero, Finset.sum_const_zero, le_refl]

end LennonPittelFormalization

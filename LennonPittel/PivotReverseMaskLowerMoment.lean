module

public import LennonPittel.PivotReverseMaskJointLaw
public import LennonPittel.ReverseArcRelativeLower
public import LennonPittel.ReverseCycleLabelMultiplicity
public import LennonPittel.ReverseDerangementFraction
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lower moment for the unfiltered reverse cycle collections

Good iid labels give a lower bound for a weighted sum over support
permutations. The exact fixed-mask product law transfers this weight to
the expected number of realized reverse cycle collections. Compatibility
and the later short-cycle and increment filters are not imposed here.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

open scoped Classical in
/-- The candidate permutations of support size `k`, excluding the pivot
labels and allowing only the permitted directed arcs. -/
noncomputable def goodReverseSupportPermutations {n : ℕ} (k : ℕ)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ ↦ σ.support.card = k ∧
    ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i

theorem mem_goodReverseSupportPermutations {n k : ℕ} {A : Finset (Fin n)}
    {F : Fin n → Finset (Fin n)} {σ : Matching n} :
    σ ∈ goodReverseSupportPermutations k A F ↔ σ.support.card = k ∧
      ∀ i ∈ σ.support, i ∉ A ∧ σ i ∉ F i := by
  classical
  simp [goodReverseSupportPermutations]

/-- The three union-bound losses for the iid proposal of the labels. -/
noncomputable def reverseGoodLabelLoss {n : ℕ} (k : ℕ) (r : Fin n → ℝ≥0∞)
    (A : Finset (Fin n)) (η : ℝ≥0∞) : ℝ≥0∞ :=
  (k.choose 2 : ℝ≥0∞) * (∑ i, (r i) ^ 2) + (k : ℝ≥0∞) * (∑ i ∈ A, r i) + k * η

/-- The weight surviving the iid exclusion tests contributes at least one
third of that weight after division by the number of ordered presentations. -/
theorem goodReverseSupportPermutations_weight_ge {n k : ℕ} (hk : 2 ≤ k)
    (r : Fin n → ℝ≥0∞) (hr : ∑ i, r i = 1)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) (η : ℝ≥0∞)
    (hη : ∀ i, ∑ j ∈ F i, r j ≤ η) :
    (1 - reverseGoodLabelLoss k r A η) / 3 ≤
      ∑ σ ∈ goodReverseSupportPermutations k A F, ∏ i ∈ σ.support, r i := by
  classical
  apply div_three_le_of_derangement_mul_le_factorial_mul hk
  calc
    _ = ∑ _e : derangements (Fin k), (1 - reverseGoodLabelLoss k r A η) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ e : derangements (Fin k), ∑ x ∈ Finset.univ.filter
        (fun x ↦ x ∈ iidLabelGood (A : Set (Fin n)) (fun i ↦ ↑(F i)) e.val), ∏ i, r (x i) := by
      refine Finset.sum_le_sum fun e _ ↦ ?_
      have he := iidLabelGood_sum_weights_lower r hr A F (e.val : Fin k → Fin k)
        (fun i ↦ e.property i) η hη
      simp only [Fintype.card_fin] at he
      unfold reverseGoodLabelLoss
      refine he.trans_eq (Finset.sum_congr ?_ fun _ _ ↦ rfl)
      ext x
      simp
    _ = _ := by
      unfold goodReverseSupportPermutations
      convert sum_iidLabelGood_eq_factorial_mul_sum_support k r A F using 2
      refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext σ
      simp

/-- The masked-out targets in each column, indexed by women on both sides
so a target index denotes her current husband. -/
noncomputable def forwardMaskForbiddenTargets {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬ ∃ q : ForwardInactiveColumnIndex flag (μ.symm i),
    q.val.val.val.1 = μ.symm j

theorem notMem_forwardMaskForbiddenTargets_iff {n : ℕ} (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    j ∉ forwardMaskForbiddenTargets μ flag i ↔
      ∃ q : ForwardInactiveColumnIndex flag (μ.symm i), q.val.val.val.1 = μ.symm j := by
  classical
  simp [forwardMaskForbiddenTargets]

/-- A count of selected permutations that are unions of actual exposed cycles. -/
noncomputable def realizedReversePermutationCount {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (M : Matching n) : ℕ := by
  classical
  exact (S.filter (RealizesSuccessorPermutation p M)).card

/-- The first moment of the count is the sum of the actual permutation probabilities. -/
theorem lintegral_realizedReversePermutationCount {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (S : Finset (Matching n)) :
    (∫⁻ z, (realizedReversePermutationCount S (P z) M : ℝ≥0∞) ∂ν) =
      ∑ σ ∈ S, ν {z | RealizesSuccessorPermutation (P z) M σ} := by
  classical
  let E (σ : Matching n) : Set Ω := {z | RealizesSuccessorPermutation (P z) M σ}
  have hm (σ : Matching n) : MeasurableSet (E σ) :=
    hP (MeasurableSet.of_discrete : MeasurableSet {p : Profile n |
      RealizesSuccessorPermutation p M σ})
  have hpoint (z : Ω) : (realizedReversePermutationCount S (P z) M : ℝ≥0∞) =
      ∑ σ ∈ S, (E σ).indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
    calc
      _ = ∑ σ ∈ S.filter (RealizesSuccessorPermutation (P z) M), (1 : ℝ≥0∞) := by
        simp [realizedReversePermutationCount]
      _ = _ := by simp only [Finset.sum_filter, Set.indicator_apply, E, Set.mem_ofPred_eq]
  simp_rw [hpoint]
  rw [lintegral_finsetSum _ (fun σ _ ↦ measurable_const.indicator (hm σ))]
  exact Finset.sum_congr rfl fun σ _ ↦ lintegral_indicator_one (hm σ)

/-- Normalized male spouse-score weights indexed by the corresponding women. -/
noncomputable def reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n) :
    Fin n → ℝ≥0∞ := fun j ↦
  ENNReal.ofReal ((diagonalPairAt d (μ.symm j)).1 / ∑ i, (diagonalPairAt d i).1)

theorem sum_reverseSpouseWeights {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n)
    (hx : ∀ i, 0 ≤ (diagonalPairAt d i).1) (hX : 0 < ∑ i, (diagonalPairAt d i).1) :
    ∑ i, reverseSpouseWeights μ d i = 1 := by
  let X := ∑ i, (diagonalPairAt d i).1
  let w (i : Fin n) := (diagonalPairAt d (μ.symm i)).1 / X
  change (∑ i, ENNReal.ofReal (w i)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (hx _) hX.le),
    ← Fintype.sum_equiv μ (fun i ↦ (diagonalPairAt d i).1 / X) w
      (fun i ↦ by simp only [w, Equiv.symm_apply_apply]), ← Finset.sum_div,
    div_self hX.ne', ENNReal.ofReal_one]

/-- For one support size, the expected number of reverse cycle collections
before compatibility is bounded below by the good-label probability, the
derangement fraction, and the product of the per-arc lower factors. -/
theorem lintegral_realizedReverseSupportCount_fixedMask_ge {n k : ℕ}
    (μ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardActiveCellIndex flag → ℝ)) (hU : MeasurableSet U)
    (A : Finset (Fin n)) (hk : 2 ≤ k) (η : ℝ≥0∞)
    (hη : ∀ i, ∑ j ∈ forwardMaskForbiddenTargets μ flag i, reverseSpouseWeights μ d j ≤ η)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1)
    (hX : 2 ≤ ∑ i, (diagonalPairAt d i).1)
    (hcomp : ∀ (i : Fin n) (q : ForwardInactiveColumnIndex flag i),
      (∑ j, (diagonalPairAt d j).1) / 2 ≤
        ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
          (diagonalPairAt d t.val.val.val.val.1).1)
    {m δ : ℝ} (hm : ∀ i, (diagonalPairAt d i).1 ≤ m)
    (hδ : 14 * m / (∑ i, (diagonalPairAt d i).1) +
      Real.exp (-(∑ i, (diagonalPairAt d i).1) / 4) ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    let F := forwardMaskForbiddenTargets μ flag
    let r := reverseSpouseWeights μ d
    let c := (forwardScoreMaskActiveMaleLaw d flag) U *
      (forwardScoreMaskInactiveColumnLaw d flag) univ
    c * ENNReal.ofReal (1 - δ) ^ k * ((1 - reverseGoodLabelLoss k r A η) / 3) ≤
      ∫⁻ z, (realizedReversePermutationCount (goodReverseSupportPermutations k A F)
        (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞)
        ∂forwardMaskRevealLaw d flag U := by
  intro F r c
  let S := goodReverseSupportPermutations k A F
  let ν := forwardMaskRevealLaw d flag U
  let P (z : OffDiagonalScorePairs n) :=
    swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))
  have hP : Measurable P :=
    (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
      ((measurable_profileOfScores n).comp
        ((splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have hr : ∑ i, r i = 1 := sum_reverseSpouseWeights μ d (fun i ↦ (hx i).1) (by linarith)
  change _ ≤ ∫⁻ z, (realizedReversePermutationCount S (P z) μ.symm : ℝ≥0∞) ∂ν
  rw [lintegral_realizedReversePermutationCount ν P hP μ.symm S]
  calc
    _ ≤ c * ENNReal.ofReal (1 - δ) ^ k * ∑ σ ∈ S, ∏ i ∈ σ.support, r i :=
      mul_le_mul_right (goodReverseSupportPermutations_weight_ge hk r hr A F η hη) _
    _ = ∑ σ ∈ S, c * (ENNReal.ofReal (1 - δ) ^ k * ∏ i ∈ σ.support, r i) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
      have hmem := mem_goodReverseSupportPermutations.mp hσ
      rw [show ν {z | RealizesSuccessorPermutation (P z) μ.symm σ} = _ from
        measure_realizesReverseSuccessorPermutation_fixedMask μ σ d flag U hU hy0 hy1 ht]
      refine mul_le_mul_right ?_ c
      calc
        _ = ∏ i ∈ σ.support, ENNReal.ofReal (1 - δ) * r (σ i) := by
          rw [σ.prod_comp σ.support (fun j ↦ ENNReal.ofReal (1 - δ) * r j)
            (fun _ h ↦ Equiv.Perm.mem_support.mpr h), Finset.prod_mul_distrib,
            Finset.prod_const, hmem.1]
        _ ≤ _ := by
          refine Finset.prod_le_prod fun i hi ↦ ?_
          obtain ⟨q, hq⟩ := (notMem_forwardMaskForbiddenTargets_iff μ flag i (σ i)).mp
            (hmem.2 i hi).2
          exact normalizedForwardInactiveColumnLaw_reverseArc_ge d flag (μ.symm i)
            (μ.symm (σ i)) q hq (hy0 _) (hy1 _) hx hX (hcomp _ q)
            (forwardInactiveCompetitor_sum_le_total d flag _ q (fun j ↦ (hx j).1)) hm hδ hδ1

/-- A small cumulative arc perturbation and a small label loss leave at
least three sixteenths of a collection in expectation per support size. -/
theorem reverseSupportCoefficient_ge {k : ℕ} {δ : ℝ} {L : ℝ≥0∞}
    (hδ : δ ≤ 1) (hkδ : (k : ℝ) * δ ≤ 1 / 4) (hL : L ≤ ENNReal.ofReal (1 / 4)) :
    ENNReal.ofReal (3 / 16) ≤ ENNReal.ofReal (1 - δ) ^ k * ((1 - L) / 3) := by
  have harc : ENNReal.ofReal (3 / 4) ≤ ENNReal.ofReal (1 - δ) ^ k :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans (ofReal_one_sub_nat_mul_le_pow_one_sub k hδ)
  have hsurvive : ENNReal.ofReal (3 / 4) ≤ 1 - L := by
    calc
      _ = 1 - ENNReal.ofReal (1 / 4) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num
      _ ≤ _ := tsub_le_tsub_left hL _
  have hfrac : ENNReal.ofReal (1 / 4) ≤ (1 - L) / 3 := by
    calc
      _ = ENNReal.ofReal (3 / 4) / 3 := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
        norm_num
      _ ≤ _ := ENNReal.div_le_div_right hsurvive _
  calc
    _ = ENNReal.ofReal (3 / 4) * ENNReal.ofReal (1 / 4) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      norm_num
    _ ≤ _ := mul_le_mul' harc hfrac

/-- Summing the unfiltered lower moment over support sizes from two to
`K` gives a linear lower bound in the support cutoff. -/
theorem lintegral_realizedReverseSupportCounts_truncated_fixedMask_ge {n K : ℕ}
    (μ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardActiveCellIndex flag → ℝ)) (hU : MeasurableSet U)
    (A : Finset (Fin n)) (η : ℝ≥0∞)
    (hη : ∀ i, ∑ j ∈ forwardMaskForbiddenTargets μ flag i, reverseSpouseWeights μ d j ≤ η)
    (hL : ∀ k ∈ Finset.Icc 2 K,
      reverseGoodLabelLoss k (reverseSpouseWeights μ d) A η ≤ ENNReal.ofReal (1 / 4))
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1)
    (hX : 2 ≤ ∑ i, (diagonalPairAt d i).1)
    (hcomp : ∀ (i : Fin n) (q : ForwardInactiveColumnIndex flag i),
      (∑ j, (diagonalPairAt d j).1) / 2 ≤
        ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
          (diagonalPairAt d t.val.val.val.val.1).1)
    {m δ : ℝ} (hm : ∀ i, (diagonalPairAt d i).1 ≤ m)
    (hδ : 14 * m / (∑ i, (diagonalPairAt d i).1) +
      Real.exp (-(∑ i, (diagonalPairAt d i).1) / 4) ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hKδ : (K : ℝ) * δ ≤ 1 / 4)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    let F := forwardMaskForbiddenTargets μ flag
    let c := (forwardScoreMaskActiveMaleLaw d flag) U *
      (forwardScoreMaskInactiveColumnLaw d flag) univ
    c * ENNReal.ofReal (3 / 16) * ((K - 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ z, (∑ k ∈ Finset.Icc 2 K,
        (realizedReversePermutationCount (goodReverseSupportPermutations k A F)
          (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞))
        ∂forwardMaskRevealLaw d flag U := by
  intro F c
  let P (z : OffDiagonalScorePairs n) :=
    swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))
  let f (k : ℕ) (z : OffDiagonalScorePairs n) : ℝ≥0∞ :=
    realizedReversePermutationCount (goodReverseSupportPermutations k A F) (P z) μ.symm
  let ν := forwardMaskRevealLaw d flag U
  have hP : Measurable P :=
    (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
      ((measurable_profileOfScores n).comp
        ((splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have hf (k : ℕ) : Measurable (f k) :=
    (show Measurable (fun p : Profile n ↦ (realizedReversePermutationCount
      (goodReverseSupportPermutations k A F) p μ.symm : ℝ≥0∞)) from
        fun _ _ ↦ MeasurableSet.of_discrete).comp hP
  change _ ≤ ∫⁻ z, (∑ k ∈ Finset.Icc 2 K, f k z) ∂ν
  rw [lintegral_finsetSum _ (fun k _ ↦ hf k)]
  calc
    _ = ∑ _k ∈ Finset.Icc 2 K, (c * ENNReal.ofReal (3 / 16)) := by
      rw [Finset.sum_const, Nat.card_Icc, show K + 1 - 2 = K - 1 by omega, nsmul_eq_mul, mul_comm]
    _ ≤ _ := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hkr := Finset.mem_Icc.mp hk
      have hkδ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkr.2) hδ0).trans hKδ
      have h := reverseSupportCoefficient_ge hδ1 hkδ (hL k hk)
      have hbound := lintegral_realizedReverseSupportCount_fixedMask_ge μ d flag U hU A hkr.1 η
        hη hy0 hy1 hx hX hcomp hm hδ hδ1 ht
      change c * ENNReal.ofReal (1 - δ) ^ k *
        ((1 - reverseGoodLabelLoss k (reverseSpouseWeights μ d) A η) / 3) ≤
        ∫⁻ z, f k z ∂ν at hbound
      rw [mul_assoc] at hbound
      exact (mul_le_mul_right h c).trans hbound

end LennonPittelFormalization

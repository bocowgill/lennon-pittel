module

public import LennonPittel.PivotReverseMaskJointLaw
public import LennonPittel.ReverseCycleCollectionMoment

/-!
# Reverse cycle second moment after a fixed forward reveal

The original score law restricted to one diagonal and forward mask factors
into the revealed male observations and the unopened columns. The reverse
cycle moment can be bounded on any measurable event in the revealed data.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- At almost every spouse-score vector, reconstruction is tie-free almost
surely under the original off-diagonal product law. Restricting to a fixed
mask or to revealed information preserves this null-set assertion. -/
theorem ae_diagonal_ae_injective_scoreRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ᵐ z ∂offDiagonalScoreLaw n,
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r) :=
  Measure.ae_ae_of_ae_prod
    (((measurePreserving_splitScorePairs μ).symm).quasiMeasurePreserving.ae (ae_injective_rows n))

/-- The upper reverse-cycle moment on a fixed forward mask, with an
arbitrary measurable restriction on the active male observations.
The competitor thresholds must retain the indicated share of the total
male spouse score. -/
theorem lintegral_four_pow_numReverseExposedRotations_fixedMask_le {n : ℕ}
    (μ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (A : Set (ForwardActiveCellIndex flag → ℝ)) (hA : MeasurableSet A) (hn : 0 < n)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1)
    {δ C : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ))
    (hcomp : ∀ (i : Fin n) (q : ForwardInactiveColumnIndex flag i),
      (∑ j, (diagonalPairAt d j).1) / (1 + δ) ≤
        ∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
          (diagonalPairAt d k.val.val.val.val.1).1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag)
    let G := (Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A
    (∫⁻ z in G, (4 : ℝ≥0∞) ^ numExposedRotations
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm ∂ν) ≤
      (forwardScoreMaskActiveMaleLaw d flag) A *
        (forwardScoreMaskInactiveColumnLaw d flag) univ *
        ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * (n : ℝ) * Real.sqrt n) := by
  intro ν G
  let X := ∑ i, (diagonalPairAt d i).1
  let w (j : Fin n) := (diagonalPairAt d (μ.symm j)).1 / X
  let P (z : OffDiagonalScorePairs n) :=
    swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))
  have hP : Measurable P :=
    (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
      ((measurable_profileOfScores n).comp
        ((splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have hw₀ (j : Fin n) : 0 ≤ w j := div_nonneg (hx _).1 hX.le
  have hw : ∑ j, w j = 1 := by
    rw [← Fintype.sum_equiv μ (fun i ↦ (diagonalPairAt d i).1 / X) w
      (fun i ↦ by simp only [w, Equiv.symm_apply_apply]), ← Finset.sum_div]
    exact div_self hX.ne'
  refine lintegral_four_pow_numExposedRotations_le_mul (ν.restrict G) P hP μ.symm
    ((forwardScoreMaskActiveMaleLaw d flag) A * (forwardScoreMaskInactiveColumnLaw d flag) univ)
    hn hw₀ hw hδ₀ hδ fun σ ↦ ?_
  change forwardMaskRevealLaw d flag A {z | RealizesSuccessorPermutation (P z) μ.symm σ} ≤ _
  rw [measure_realizesReverseSuccessorPermutation_fixedMask μ σ d flag A hA hy0 hy1 ht]
  refine mul_le_mul_right (Finset.prod_le_prod fun i _ ↦ ?_) _
  exact normalizedForwardInactiveColumnLaw_reverseArc_le d flag (μ.symm i) (μ.symm (σ i))
    (hy0 _) (hy1 _) hx hX (by positivity) (fun q _ ↦ hcomp _ q)

end LennonPittelFormalization

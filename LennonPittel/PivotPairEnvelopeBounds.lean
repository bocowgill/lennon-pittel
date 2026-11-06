module

public import LennonPittel.PivotIncomparableDecorations
public import LennonPittel.PivotPairEnvelopeScale
public import LennonPittel.PivotVarianceClosure
public import LennonPittel.TwoStablePairPerSizeBounds

/-!
# From the labeled pair bounds to the two variance terms

For count-count pairs both orientations are long. For comparable residual
images, the irregular size sector is small and the regular sector must
have a forced-cycle or background-cycle exception.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ}

private theorem sum_scoreTwoLongOrientations_le (hn : 0 < n) {b : ℝ} (hb : 0 < b) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent (ScoreTwoLongOrientations b) μ ν)) ≤
      longPairEnvelope (Real.exp 72) b n := by
  classical
  let S := (validPairSizeFinset n).filter fun s ↦
    b * Real.sqrt (n : ℝ) ≤ (s.1 : ℝ) ∧ b * Real.sqrt (n : ℝ) ≤ (s.2 : ℝ)
  have hS (s : ℕ × ℕ) (hs : s ∈ S) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  rw [scorePairMass_real_eq_sum_sizeMass (measurableSet_scoreTwoLongOrientations b) S ?_]
  · exact sum_twoStablePairSizeWeights_le hn S
      (fun s ↦ (scorePairSizeMass (ScoreTwoLongOrientations b) s).toReal)
      (Real.exp_pos 72).le
      (fun s hs ↦ scorePairSizeMass_toReal_le_kernel (measurableSet_scoreTwoLongOrientations b)
        (hS s hs))
      (sum_twoStablePairSizeKernel_le_both_long hn S hS hb
        (fun s hs ↦ (Finset.mem_filter.mp hs).2))
  · intro μ ν
    filter_upwards [ae_validPairSizes_of_scoreIncomparablePairEvent
      (ScoreTwoLongOrientations b) μ ν] with x hx he
    exact Finset.mem_filter.mpr ⟨mem_validPairSizeFinset.mpr (hx he), he.2.2.2⟩

theorem PivotCountParameters.integral_incomparableCountProductMass_le_envelope
    (q : PivotCountParameters) (hn : 0 < n) {κ : ℝ} (hb : 0 < q.lowerLength)
    (hκ : κ < q.lowerLength) (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) ≤
      longPairEnvelope (Real.exp 72) q.lowerLength n :=
  (q.integral_incomparableCountProducts_le_sum hn hκ hcap).trans
    (sum_scoreTwoLongOrientations_le hn hb)

private theorem eventually_sum_residualPairMass_le {α : ℝ} (hα : 0 < α) (hα' : α < 1 / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℝ, ∀ K : ℕ,
      (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
        (scoreIncomparablePairEvent (IsResidualPairGeometry b K (pivotShortCycleCutoff α n)) μ ν)) ≤
        (Real.exp 72 * (1 + Real.log n)) *
          (8 * (n : ℝ) ^ 2 * (2 + α * Real.log n) + 4 +
            (1600 / Real.log (pivotShortCycleCutoff α n : ℝ)) *
              (12 * (n : ℝ) ^ 2 * (1 + Real.log n))) := by
  classical
  filter_upwards [eventually_backgroundShortCutoff_large hα,
    eventually_scorePairSizeMass_toReal_le_background hα hα',
    eventually_gt_atTop (0 : ℕ)] with n hL hbackground hn
  intro b K
  let L := pivotShortCycleCutoff α n
  let R := IsResidualPairGeometry (n := n) b K L
  let w (s : ℕ × ℕ) := (scorePairSizeMass R s).toReal
  let S := validPairSizeFinset n
  let G := S.filter (RegularPairSizes n α)
  let J := S.filter fun s ↦ ¬ RegularPairSizes n α s
  have hR (μ ν : Matching n) : MeasurableSet {x | R x μ ν} :=
    measurableSet_isResidualPairGeometry b K L μ ν
  have hG (s : ℕ × ℕ) (hs : s ∈ G) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  have hJ (s : ℕ × ℕ) (hs : s ∈ J) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  have hgood (s : ℕ × ℕ) (hs : s ∈ G) :
      w s ≤ (Real.exp 72 * (1600 / Real.log (L : ℝ))) *
        (1 + Real.log n) * twoStablePairSizeKernel n s := by
    have hreg := (Finset.mem_filter.mp hs).2
    have hcut : L ≤ s.1 :=
      pivotShortCycleCutoff_le_of_rpow_lt hα.le hn hreg.2.1
    have hf := scorePairSizeMass_toReal_le_forced hR (hG s hs) hL.1 hcut hL.2
    have hb := hbackground hR (fun _ _ _ h ↦ h.late_scores) (hG s hs) hreg
    calc
      _ ≤ (scorePairSizeMass (fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L) s).toReal +
          (scorePairSizeMass
            (fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L) s).toReal := by
        apply scorePairSizeMass_toReal_le_add
        intro μ ν
        exact Eventually.of_forall fun x hx _ ↦
          (scoreResidualPairEvent_subset_shortCycleExceptions hL.1 μ ν hx).imp
            (fun h ↦ ⟨hx.2.2.2, h⟩) (fun h ↦ ⟨hx.2.2.2, h⟩)
      _ ≤ _ := (add_le_add hf hb).trans_eq (by ring)
  have hreg_sum : (∑ s ∈ G, w s) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        ((1600 / Real.log (L : ℝ)) * (12 * (n : ℝ) ^ 2 * (1 + Real.log n))) := by
    have hlog : 0 ≤ Real.log (L : ℝ) := by linarith [hL.2]
    calc
      _ ≤ (Real.exp 72 * (1600 / Real.log (L : ℝ))) *
            (1 + Real.log n) * (12 * (n : ℝ) ^ 2 * (1 + Real.log n)) :=
        sum_twoStablePairSizeWeights_le hn G w (by positivity) hgood
          (sum_twoStablePairSizeKernel_le_total hn G hG)
      _ = _ := by ring
  have hirreg_sum : (∑ s ∈ J, w s) ≤
      (Real.exp 72 * (1 + Real.log n)) * (8 * (n : ℝ) ^ 2 * (2 + α * Real.log n) + 4) :=
    sum_twoStablePairSizeWeights_le hn J w (Real.exp_pos 72).le
      (fun s hs ↦ scorePairSizeMass_toReal_le_kernel hR (hJ s hs))
      (sum_twoStablePairSizeKernel_le_not_regular hn J hJ hα.le
        (fun s hs ↦ (Finset.mem_filter.mp hs).2))
  rw [scorePairMass_real_eq_sum_validPairSizeMass hR]
  change (∑ s ∈ S, w s) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (RegularPairSizes n α)]
  exact (add_le_add hreg_sum hirreg_sum).trans_eq (by ring)

/-- Both estimates concern the actual centered count, with the same short-cycle cutoff. -/
theorem eventually_pivotPairIntegrals_le_envelopes {b A B κ α : ℝ} (hb : 0 < b)
    (hκ : 0 < κ) (hκb : κ < b) (hα : 0 < α) (hα' : α < 1 / 10) :
    ∀ᶠ n : ℕ in atTop,
      let q : PivotCountParameters := ⟨b, A, B, pivotDecorationSupportCap κ n,
        pivotShortCycleCutoff α n⟩
      (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
        residualPairEnvelope (Real.exp 72) α n ∧
      (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) ≤
        longPairEnvelope (Real.exp 72) b n := by
  have hK := eventually_pivotDecorationSupportCap_bounds hκ
  have hL := eventually_pivotShortCycleCutoff_le (hα'.trans (by norm_num)) hκ
    (hK.mono fun n h ↦ h.2.2.trans (Nat.cast_le.mpr (Nat.sub_le _ _)))
  filter_upwards [hK, hL, eventually_residualEndpointIncrementBudget κ,
    eventually_sum_residualPairMass_le hα hα', eventually_gt_atTop (0 : ℕ)]
    with n hnK hnL hbudget hres hn
  dsimp only
  let q : PivotCountParameters := ⟨b, A, B, pivotDecorationSupportCap κ n,
    pivotShortCycleCutoff α n⟩
  refine ⟨?_, q.integral_incomparableCountProductMass_le_envelope hn hb hκb hnK.2.1⟩
  have h := q.integral_comparableResidualMass_le_geometry hn hκb hnK.2.1 hnL
    (hbudget _ hnK.2.1)
  exact h.trans ((mul_le_mul_of_nonneg_left (hres b (pivotDecorationSupportCap κ n))
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by unfold residualPairEnvelope; ring))

end LennonPittelFormalization

module

public import LennonPittel.DAProposalCoupon
public import LennonPittel.DALowerEndpoint
public import LennonPittel.DAUpperEndpoint
public import LennonPittel.ScoreRotationAnchorProbability

/-!
# The extreme stable matchings cross the pivot score band

The same proposal cap applies to both sides. At the man-optimal endpoint the
women's total cannot be unusually small without seeing many rare small scores.
At the woman-optimal endpoint the proposers' final scores are bounded by their
rank order statistics. Together the two bounds discharge the endpoint hypothesis
of the singleton-anchor abundance theorem.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology LennonPittelFormalization

namespace LennonPittelFormalization

theorem measure_scoreDAProposalCount_gt (n T : ℕ) :
    continuousScoreLaw n {x | T < (DAState.run (profileOfScores x) (n * n)).proposalCount} =
      (uniformProfile n).toMeasure {p | T < (DAState.run p (n * n)).proposalCount} := by
  let E : Set (Profile n) := {p | T < (DAState.run p (n * n)).proposalCount}
  have hm := measurePreserving_profileOfScores n
  change continuousScoreLaw n (profileOfScores ⁻¹' E) = (uniformProfile n).toMeasure E
  rw [← Measure.map_apply hm.measurable MeasurableSet.of_discrete, hm.map_eq]

/-- Both endpoints of the rotation walk cross the required band with high probability. -/
theorem tendsto_measure_badScoreWalkBandEndpoints :
    Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0) := by
  have hcap : Tendsto (fun n ↦ continuousScoreLaw n {x |
      daProposalCap n < (DAState.run (profileOfScores x) (n * n)).proposalCount}) atTop (𝓝 0) := by
    simpa only [measure_scoreDAProposalCount_gt] using
      tendsto_measure_daProposalCount_gt_daProposalCap
  have hstart : Tendsto (fun n ↦ continuousScoreLaw n {x |
      scoreWalkFemaleTotal x 0 ≤ (n : ℝ) ^ (2 / 5 : ℝ)}) atTop (𝓝 0) :=
    tendsto_measure_badManOptimalScore_of_proposalCap daProposalCap
      eventually_daProposalCap_le hcap
  have hend := tendsto_measure_badScoreWalkUpperEndpoint eventually_daProposalCap_le
    tendsto_measure_daProposalCount_gt_daProposalCap
  have hsum := hstart.add hend
  rw [add_zero] at hsum
  refine tendsto_const_nhds.squeeze' hsum (Eventually.of_forall fun _ ↦ zero_le) ?_
  apply Eventually.of_forall
  intro n
  have he : (scoreWalkBandEndpoints n)ᶜ =
      {x | scoreWalkFemaleTotal x 0 ≤ (n : ℝ) ^ (2 / 5 : ℝ)} ∪
      {x | (n : ℝ) ^ (1 / 5 : ℝ) < scoreWalkFemaleTotal x (n * (n - 1))} := by
    ext x
    simp only [scoreWalkBandEndpoints, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union,
      not_and_or, not_lt, not_le]
  rw [he]
  exact measure_union_le _ _

/-- For each loss tolerance there are fixed square-root length cutoffs for which
the singleton-anchor score-and-length certificate holds with that loss eventually. -/
theorem exists_eventually_measure_badScoreWalkAnchorAbundance_le
    {η : ℝ} (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)ᶜ ≤
        ENNReal.ofReal η :=
  exists_eventually_measure_badScoreWalkAnchorAbundance_le_of_endpoints
    tendsto_measure_badScoreWalkBandEndpoints hη

end LennonPittelFormalization

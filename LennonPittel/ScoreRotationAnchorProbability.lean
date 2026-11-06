module

public import LennonPittel.ScoreRotationAnchorAbundance
public import LennonPittel.ScoreRotationNonTiny

/-!
# Probability of the singleton-anchor abundance certificate

For any allowed loss, fixed positive square-root cutoffs capture enough
rotations. Their singleton anchors inherit the wider score band. The only
probability input to this score-and-length certificate not supplied here
is that the walk actually starts above and finishes below the band.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- Outside an arbitrarily small loss, the endpoint event implies that
order square-root times logarithm many singleton anchors meet the band
and fixed square-root length cutoffs. -/
theorem exists_eventually_measure_scoreWalkBandEndpoints_diff_anchorAbundance_le
    {η : ℝ} (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n
        (scoreWalkBandEndpoints n \ scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤
        ENNReal.ofReal η := by
  obtain ⟨b, A, hb, hb₁, hA, hband⟩ :=
    exists_eventually_measure_scoreWalkBandEndpoints_diff_sqrtAbundance_le
      (η := η / 3) (by positivity)
  refine ⟨b, A, hb, hb₁, hA, ?_⟩
  let K (n : ℕ) := b * Real.sqrt (n : ℝ)
  have hK : ∀ᶠ n : ℕ in atTop, 81 ≤ K n :=
    ((Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hb).eventually_ge_atTop 81
  have himp := eventually_scoreWalkAnchorAbundance_of_bandAbundance K hK
  have hg := tendsto_measure_badCoexposureScores_zero_of_mean_upper (C := 1) zero_le_one
    (by simpa only [one_mul] using eventually_expectedNumStableMatchings_le_sizeLog)
  have hη₀ := ENNReal.ofReal_pos.mpr (show 0 < η / 3 by positivity)
  filter_upwards [himp, hband, hg.eventually_lt_const hη₀,
    tendsto_measure_badNonTinyRotation_zero.eventually_lt_const hη₀]
    with n himp hband hg hnon
  let E := scoreWalkBandEndpoints n
  let B := scoreWalkBandAbundanceAtCutoffs n (K n) A
  let Q := scoreWalkAnchorAbundanceAtCutoffs n (K n) A
  have hsub : E \ Q ⊆ ((E \ B) ∪ (goodCoexposureScores n)ᶜ) ∪ badNonTinyRotation n := by
    intro x hx
    by_cases hB : x ∈ B
    · by_cases hG : x ∈ goodCoexposureScores n
      · by_cases hN : x ∈ badNonTinyRotation n
        · exact Or.inr hN
        · exfalso
          apply hx.2
          refine himp hG hB fun μ hμ σ hσ hlen ↦ ?_
          simpa only [nonTinyRotationShare, neg_div] using
            exists_nonTiny_participant_of_not_mem_badNonTinyRotation hN hμ hσ hlen
      · exact Or.inl (Or.inr hG)
    · exact Or.inl (Or.inl ⟨hx.1, hB⟩)
  change continuousScoreLaw n (E \ Q) ≤ _
  calc
    _ ≤ continuousScoreLaw n
        (((E \ B) ∪ (goodCoexposureScores n)ᶜ) ∪ badNonTinyRotation n) := measure_mono hsub
    _ ≤ continuousScoreLaw n (E \ B) + continuousScoreLaw n (goodCoexposureScores n)ᶜ +
        continuousScoreLaw n (badNonTinyRotation n) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) :=
      add_le_add (add_le_add hband hg.le) hnon.le
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- If the two extreme score estimates hold with high probability, the
singleton-anchor score-and-length certificate holds up to any fixed loss. -/
theorem exists_eventually_measure_badScoreWalkAnchorAbundance_le_of_endpoints
    (hend : Tendsto (fun n ↦ continuousScoreLaw n (scoreWalkBandEndpoints n)ᶜ) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)ᶜ ≤
        ENNReal.ofReal η := by
  obtain ⟨b, A, hb, hb₁, hA, ha⟩ :=
    exists_eventually_measure_scoreWalkBandEndpoints_diff_anchorAbundance_le
      (η := η / 2) (by positivity)
  refine ⟨b, A, hb, hb₁, hA, ?_⟩
  have hη₀ := ENNReal.ofReal_pos.mpr (show 0 < η / 2 by positivity)
  filter_upwards [hend.eventually_lt_const hη₀, ha] with n he ha
  let E := scoreWalkBandEndpoints n
  let Q := scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A
  have hsub : Qᶜ ⊆ Eᶜ ∪ (E \ Q) := by
    intro x hx
    by_cases h : x ∈ E
    · exact Or.inr ⟨h, hx⟩
    · exact Or.inl h
  calc
    _ ≤ continuousScoreLaw n (Eᶜ ∪ (E \ Q)) := measure_mono hsub
    _ ≤ continuousScoreLaw n Eᶜ + continuousScoreLaw n (E \ Q) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add he.le ha
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end LennonPittelFormalization

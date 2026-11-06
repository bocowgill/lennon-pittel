module

public import LennonPittel.CoexposureScoreMomentBound
public import LennonPittel.CoexposureSpouseShells
public import LennonPittel.CoexposureSpouseMarginal

/-!
# The exceptional-score limit and the co-exposure refutation
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private def smallScoreException {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ smallSpouseScoreSet n}

private def largeRelativeScoreException {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n}

private theorem badStableScoreMass_le_cutoffSums {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n (badStableSpouseScores n μ) ≤
      continuousScoreLaw n (smallScoreException μ) +
        continuousScoreLaw n (largeRelativeScoreException μ) +
          continuousScoreLaw n (badMaleSpouseScores μ) := by
  classical
  let exceptions : Set (ScoreProfile n) :=
    (smallScoreException μ ∪ largeRelativeScoreException μ) ∪ badMaleSpouseScores μ
  have hsub : badStableSpouseScores n μ ≤ᶠ[ae (continuousScoreLaw n)] exceptions := by
    filter_upwards [ae_unitOpen_scores n] with x hx
    intro hbad
    let y := femaleSpouseByHusband μ x
    have hy (j : Fin n) : y j ∈ Ioo (0 : ℝ) 1 :=
      hx (.inr (μ j)) (μ.symm (μ j))
    have hs_eq : femaleSpouseTotal x μ = spouseVectorTotal y :=
      femaleSpouseTotal_eq_sum_byHusband μ x
    by_cases hs : 2 ≤ femaleSpouseTotal x μ
    · by_cases hw : ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤
          12 * Real.log n / n
      · have hm : ¬∀ i, maleSpouseScore x μ i ≤
            8 * Real.log n / (femaleSpouseTotal x μ - 1) :=
          fun hm ↦ hbad.2 ⟨hs, hw, hm⟩
        obtain ⟨i, hi⟩ := not_forall.mp hm
        exact Or.inr ⟨hbad.1, hs, i, lt_of_not_ge hi⟩
      · obtain ⟨j, hj⟩ := not_forall.mp hw
        have htotal : spouseVectorTotal y ≤ (n : ℝ) :=
          calc
            spouseVectorTotal y ≤ ∑ _ : Fin n, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ ↦ (hy i).2.le
            _ = _ := by simp
        refine Or.inl (Or.inr ⟨hbad.1, fun i ↦ (hy i).1.le, hs_eq ▸ hs,
          htotal, μ.symm j, ?_⟩)
        change 12 * Real.log n / n < y (μ.symm j) / spouseVectorTotal y
        rw [← hs_eq]
        simpa only [y, femaleSpouseByHusband, Equiv.apply_symm_apply] using lt_of_not_ge hj
    · exact Or.inl (Or.inl ⟨hbad.1, fun i ↦ (hy i).1.le, hs_eq ▸ lt_of_not_ge hs⟩)
  calc
    _ ≤ continuousScoreLaw n exceptions := measure_mono_ae hsub
    _ ≤ continuousScoreLaw n (smallScoreException μ ∪ largeRelativeScoreException μ) +
        continuousScoreLaw n (badMaleSpouseScores μ) := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl

private theorem badScoreMass_le_cutoffSums (n : ℕ) :
    continuousScoreLaw n (goodCoexposureScores n)ᶜ ≤
      (∑ μ : Matching n, continuousScoreLaw n (smallScoreException μ)) +
      (∑ μ : Matching n, continuousScoreLaw n (largeRelativeScoreException μ)) +
      ∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ) := by
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n (badStableSpouseScores n μ) :=
      measure_badCoexposureScores_le_sum n
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (smallScoreException μ) +
        continuousScoreLaw n (largeRelativeScoreException μ) +
          continuousScoreLaw n (badMaleSpouseScores μ)) :=
      Finset.sum_le_sum fun μ _ ↦ badStableScoreMass_le_cutoffSums μ
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- The probability that some stable matching fails a spouse-score cutoff tends to zero,
provided the stable-matching mean has the usual upper bound. -/
theorem tendsto_measure_badCoexposureScores_zero_of_mean_upper {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)) :
    Tendsto (fun n ↦ continuousScoreLaw n (goodCoexposureScores n)ᶜ) atTop (𝓝 0) := by
  have hsmall := tendsto_sum_stable_smallSpouseScore_zero
  have hlarge := tendsto_sum_stable_largeRelativeSpouseScore_zero
  have hmale := tendsto_sum_measure_badMaleSpouseScores_zero_of_mean_upper hC hmean
  have htotal := (hsmall.add hlarge).add hmale
  simp only [add_zero] at htotal
  exact tendsto_const_nhds.squeeze' htotal (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall badScoreMass_le_cutoffSums)

/-- The co-exposure event at the dyadic threshold for reciprocal-log tolerance tends to zero,
assuming the positive limiting mean ratio. This concerns co-exposure, not the stable-count tail. -/
theorem tendsto_uniformProfile_coexposure_zero_of_mean_asymptotic {a : ℝ} (ha : 0 < a)
    (hmean : Tendsto
      (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n)) atTop (𝓝 a)) :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | HasCoexposedRotations p (coexposedRotationThreshold reciprocalLogTolerance n)})
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hweight⟩ := eventually_lintegral_goodScoreCoexposureWeight_le_sqrt
  have hupper := (eventual_target_lower_and_mean_upper_of_tendsto ha hmean).2
  exact tendsto_uniformProfile_coexposure_zero_of_weight_growth
    goodCoexposureScores measurableSet_goodCoexposureScores ha hC (by norm_num) hmean
    (tendsto_measure_badCoexposureScores_zero_of_mean_upper (by positivity) hupper) hweight

end LennonPittelFormalization

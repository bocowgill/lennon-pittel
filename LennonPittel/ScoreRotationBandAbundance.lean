module

public import LennonPittel.ScoreRotationClockMaximal
public import LennonPittel.ScoreRotationLengthBudgets

/-!
# Abundance of in-band rotations, apart from the endpoint event

The clock and length estimates imply that profiles with the required
endpoint scores but too few in-band rotations have arbitrarily small
probability. The probability of the endpoint event itself is separate.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- The comparison-selected walk starts above the pivot band and ends below it. -/
def scoreWalkBandEndpoints (n : ℕ) : Set (ScoreProfile n) :=
  {x | (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0 ∧
    scoreWalkFemaleTotal x (n * (n - 1)) ≤ (n : ℝ) ^ (1 / 5 : ℝ)}

theorem measurable_scoreWalkFemaleTotal (n k : ℕ) :
    Measurable (fun x : ScoreProfile n ↦ scoreWalkFemaleTotal x k) := by
  let : MeasurableSpace (Matching n) := ⊤
  let : DiscreteMeasurableSpace (Matching n) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have h : Measurable (fun z : Matching n × ScoreProfile n ↦ femaleSpouseTotal z.2 z.1) :=
    measurable_from_prod_countable_right measurable_femaleSpouseTotal
  exact h.comp ((measurable_scoreWalkCheckpoint n k).prodMk measurable_id)

theorem measurableSet_scoreWalkBandEndpoints (n : ℕ) :
    MeasurableSet (scoreWalkBandEndpoints n) :=
  (measurableSet_lt measurable_const (measurable_scoreWalkFemaleTotal n 0)).inter
    (measurableSet_le (measurable_scoreWalkFemaleTotal n (n * (n - 1))) measurable_const)

/-- Distinct intermediate-length realized rotations with exposures in the pivot band. -/
def scoreWalkBandAbundanceAtCutoffs (n : ℕ) (K A : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
    Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
    ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
      (r.val.cycle.support.card : ℝ) ≤ A * Real.sqrt n ∧
      ∃ t < n * (n - 1), r.IsExposedAt (scoreWalkMatching x t) ∧
        scoreWalkFemaleTotal x t ∈ Ioc ((n : ℝ) ^ (1 / 5 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))}

/-- A convenient sub-square-root instance of the rotation count event. -/
abbrev scoreWalkBandAbundance (n : ℕ) (A : ℝ) : Set (ScoreProfile n) :=
  scoreWalkBandAbundanceAtCutoffs n ((n : ℝ) ^ (1 / 4 : ℝ)) A

private theorem scoreWalkBandAbundanceAtCutoffs_of_budgets {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} {K A : ℝ} (hA : 1 ≤ A) (hx : x ∈ goodCoexposureScores n)
    (hgeom : x ∈ goodFemaleLogGeometry n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (hcap : rotationStepRelativeCap n ≤ 1 / 2)
    (hsep : (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2)
    (hlog : Real.log 2 + 6 ≤ Real.log n / 25)
    (hend : x ∈ scoreWalkBandEndpoints n)
    (hclock : ∀ t ≤ n * (n - 1), |scoreWalkClock x t| ≤ (1 / 100 : ℝ) * (n * Real.log n))
    (hshort : profileSingletonAnchorLengthWeight (profileOfScores x)
      (shortRotationLengthWeight K) ≤ (1 / 50 : ℝ) * (n * Real.log n))
    (hlong : profileSingletonAnchorLengthWeight (profileOfScores x)
      (longRotationLengthWeight (A * Real.sqrt n)) ≤ (1 / 50 : ℝ) * (n * Real.log n)) :
    x ∈ scoreWalkBandAbundanceAtCutoffs n K A := by
  let L := A * Real.sqrt n
  obtain ⟨a, b, hab, hbN, hband, -, hmid⟩ :=
    exists_scoreWalk_pivot_band_middle_count hn hx hgeom hlen hcap hsep hend.1 hend.2 hclock K L
  obtain ⟨S, hScard, hS⟩ := exists_scoreWalkSegment_middle_realizedRotations
    (fun j ↦ hx.1 (.inr j)) hab.le K L
  rw [← hScard] at hmid
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hL : 0 < L := mul_pos hA₀ (Real.sqrt_pos.mpr hn₀)
  have h10 : (n : ℝ) * Real.log n / 10 ≤ L * (S.card : ℝ) := by
    have hlog' := mul_le_mul_of_nonneg_left hlog hn₀.le
    linarith only [hlog', hshort, hlong, hmid]
  refine ⟨S, (mul_le_mul_iff_right₀ hL).mp ?_, ?_⟩
  · calc
      L * (Real.sqrt n * Real.log n / (10 * A)) =
          (Real.sqrt n)^2 * Real.log n / 10 := by
        dsimp [L]
        field_simp [hA₀.ne']
      _ = _ := by rw [Real.sq_sqrt hn₀.le]
      _ ≤ _ := h10
  · intro r hr
    obtain ⟨hrlo, hrhi, t, hat, htb, hex⟩ := hS r hr
    exact ⟨hrlo, hrhi, t, htb.trans_le hbN, hex, hband t hat htb⟩

private theorem tendsto_measure_badFemaleLogGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ) atTop (𝓝 0) := by
  have hrate :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  exact tendsto_const_nhds.squeeze' hrate (Eventually.of_forall fun _ ↦ zero_le)
    (eventually_measure_badFemaleLogGeometry_le 1)

private theorem eventually_pivotBand_separated :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2 := by
  have hpow := (tendsto_rpow_atTop (by norm_num : 0 < (1 / 5 : ℝ))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpow.eventually_gt_atTop 2, eventually_gt_atTop (0 : ℕ)] with n hn hn₀
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  have hsq : ((n : ℝ) ^ (1 / 5 : ℝ))^2 = (n : ℝ) ^ (2 / 5 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hnr]
    norm_num
  rw [← hsq]
  change 2 < (n : ℝ) ^ (1 / 5 : ℝ) at hn
  nlinarith

/-- Charge the missing in-band rotations to the two length tails, plus an
arbitrarily small slack for the vanishing geometric and clock failures. -/
theorem eventually_measure_scoreWalkBandEndpoints_diff_abundanceAtCutoffs_le
    (K : ℕ → ℝ) {A : ℝ} (hA : 1 ≤ A) {δ ηs ηl : ℝ}
    (hδ : 0 < δ) (hηs : 0 ≤ ηs) (hηl : 0 ≤ ηl)
    (hshort : ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight
        (profileOfScores x) (shortRotationLengthWeight (K n))} ≤ ENNReal.ofReal ηs)
    (hlong : ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight
        (profileOfScores x) (longRotationLengthWeight (A * Real.sqrt n))} ≤ ENNReal.ofReal ηl) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      (scoreWalkBandEndpoints n \ scoreWalkBandAbundanceAtCutoffs n (K n) A) ≤
      ENNReal.ofReal (δ + ηs + ηl) := by
  let B₁ (n : ℕ) := (goodCoexposureScores n)ᶜ ∪
    profileOfScores ⁻¹' longStableExposedRotationEvent n (rotationLengthCutoff n)
  let B₂ (n : ℕ) := (goodFemaleLogGeometry n)ᶜ
  let B₃ (n : ℕ) : Set (ScoreProfile n) :=
    {x | ∃ k ≤ n * (n - 1), (1 / 100 : ℝ) * (n * Real.log n) ≤ |scoreWalkClock x k|}
  let B₄ (n : ℕ) : Set (ScoreProfile n) :=
    {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight (profileOfScores x)
      (shortRotationLengthWeight (K n))}
  let B₅ (n : ℕ) : Set (ScoreProfile n) :=
    {x | (1 / 50 : ℝ) * (n * Real.log n) < profileSingletonAnchorLengthWeight (profileOfScores x)
      (longRotationLengthWeight (A * Real.sqrt n))}
  let small (n : ℕ) := (continuousScoreLaw n (B₁ n) + continuousScoreLaw n (B₂ n)) +
    continuousScoreLaw n (B₃ n)
  have hs : Tendsto small atTop (𝓝 0) := by
    simpa only [add_zero] using
      (tendsto_measure_badRotationStepGeometry_zero.add
        tendsto_measure_badFemaleLogGeometry_zero).add
        (tendsto_measure_scoreWalkClock_large (ε := 1 / 100) (by norm_num))
  have hcap := tendsto_rotationStepRelativeCap.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (25 * (Real.log 2 + 6))
  have hδ₀ : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  filter_upwards [hs.eventually_lt_const hδ₀, hshort, hlong, hcap, hlog,
    eventually_pivotBand_separated, eventually_gt_atTop (0 : ℕ)]
    with n hsmall hshort hlong hcap hlog hsep hn
  change 25 * (Real.log 2 + 6) ≤ Real.log (n : ℝ) at hlog
  have hsub : scoreWalkBandEndpoints n \ scoreWalkBandAbundanceAtCutoffs n (K n) A ⊆
      (((B₁ n ∪ B₂ n) ∪ B₃ n) ∪ B₄ n) ∪ B₅ n := by
    intro x hx
    by_contra! h
    have hnone :
        (x ∉ B₁ n ∧ x ∉ B₂ n) ∧ x ∉ B₃ n ∧ x ∉ B₄ n ∧ x ∉ B₅ n := by
      simp only [mem_union, not_or] at h
      tauto
    have hgood : x ∈ goodCoexposureScores n := by
      by_contra! hbad
      exact hnone.1.1 (Or.inl hbad)
    have hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n) :=
      fun hbad ↦ hnone.1.1 (Or.inr hbad)
    have hgeom : x ∈ goodFemaleLogGeometry n := by
      by_contra! hbad
      exact hnone.1.2 hbad
    apply hx.2
    exact scoreWalkBandAbundanceAtCutoffs_of_budgets hn hA hgood hgeom hlen hcap.le hsep
      (by linarith only [hlog]) hx.1
      (fun t ht ↦ (lt_of_not_ge (fun hb ↦ hnone.2.1 ⟨t, ht, hb⟩)).le)
      (le_of_not_gt hnone.2.2.1) (le_of_not_gt hnone.2.2.2)
  calc
    _ ≤ continuousScoreLaw n ((((B₁ n ∪ B₂ n) ∪ B₃ n) ∪ B₄ n) ∪ B₅ n) :=
      measure_mono hsub
    _ ≤ small n + continuousScoreLaw n (B₄ n) + continuousScoreLaw n (B₅ n) :=
      (measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add
          ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
        le_rfl)
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal ηs + ENNReal.ofReal ηl :=
      add_le_add (add_le_add hsmall.le hshort) hlong
    _ = _ := by
      rw [← ENNReal.ofReal_add hδ.le hηs, ← ENNReal.ofReal_add (by positivity) hηl]

/-- The special case with a sub-square-root cutoff. -/
theorem exists_eventually_measure_scoreWalkBandEndpoints_diff_abundance_le {η : ℝ}
    (hη : 0 < η) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkBandEndpoints n \ scoreWalkBandAbundance n A) ≤
        ENNReal.ofReal η := by
  obtain ⟨A, hA, hlong⟩ := exists_eventually_measure_longRotationLengthBudget_bad
    (ε := 1 / 50) (η := η / 3) (by norm_num) (by positivity)
  have hshort := (tendsto_measure_shortRotationLengthBudget_bad
    (ε := 1 / 50) (by norm_num)).eventually_lt_const
      (ENNReal.ofReal_pos.mpr (show 0 < η / 3 by positivity))
  have hh := eventually_measure_scoreWalkBandEndpoints_diff_abundanceAtCutoffs_le
    (fun n ↦ (n : ℝ) ^ (1 / 4 : ℝ)) hA
    (δ := η / 3) (ηs := η / 3) (ηl := η / 3) (by positivity) (by positivity) (by positivity)
    (hshort.mono fun _ h ↦ h.le) hlong
  rw [show η / 3 + η / 3 + η / 3 = η by ring] at hh
  exact ⟨A, hA, hh⟩

/-- The pivot-family estimate with both cutoffs fixed on the square-root scale. -/
theorem exists_eventually_measure_scoreWalkBandEndpoints_diff_sqrtAbundance_le {η : ℝ}
    (hη : 0 < η) :
    ∃ b A : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n
        (scoreWalkBandEndpoints n \ scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤
        ENNReal.ofReal η := by
  obtain ⟨b, hb, hb₁, hshort⟩ := exists_eventually_measure_shortRotationLengthBudget_bad
    (ε := 1 / 50) (η := η / 3) (by norm_num) (by positivity)
  obtain ⟨A, hA, hlong⟩ := exists_eventually_measure_longRotationLengthBudget_bad
    (ε := 1 / 50) (η := η / 3) (by norm_num) (by positivity)
  have hh := eventually_measure_scoreWalkBandEndpoints_diff_abundanceAtCutoffs_le
    (fun n ↦ b * Real.sqrt n) hA
    (δ := η / 3) (ηs := η / 3) (ηl := η / 3) (by positivity) (by positivity) (by positivity)
    hshort hlong
  rw [show η / 3 + η / 3 + η / 3 = η by ring] at hh
  exact ⟨b, A, hb, hb₁, hA, hh⟩

end LennonPittelFormalization

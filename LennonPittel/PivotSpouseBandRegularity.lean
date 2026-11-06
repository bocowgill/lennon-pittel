module

public import LennonPittel.PivotSpouseProductLower
public import LennonPittel.PivotSpouseBandMask
public import LennonPittel.CoexposureScoreRefutation

/-!
# Simultaneous base score and mask regularity

Uniform probability bounds come from exceptional marked counts. The resulting
global event is used to count eligible anchors, not as part of the local reveal.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The usual spouse cutoffs and the product lower bound place a matching
below the upper score-band edge in the concrete diagonal band. -/
theorem splitScorePairs_mem_pivotBaseDiagonalBand {n : ℕ} {x : ScoreProfile n}
    (μ : Matching n) (hunit : ∀ row i, x row i ∈ Ioo (0 : ℝ) 1)
    (hgood : GoodSpouseScores x μ) (hprod : (n : ℝ) / 128 ≤
      maleSpouseTotal x μ * femaleSpouseTotal x μ)
    (hY : femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ)) :
    (splitScorePairs μ x).1 ∈ pivotBaseDiagonalBand n := by
  let d := (splitScorePairs μ x).1
  have hm (i : Fin n) : (diagonalPairAt d i).1 = maleSpouseScore x μ i :=
    congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
  have hf (i : Fin n) : (diagonalPairAt d i).2 = femaleSpouseByHusband μ x i := by
    rw [diagonalPairAt_splitScorePairs, femaleSpouseByHusband, femaleSpouseScore,
      Equiv.symm_apply_apply]
  have hX' : reverseDiagonalMaleTotal d = maleSpouseTotal x μ :=
    Finset.sum_congr rfl fun i _ ↦ hm i
  have hY' : pivotDiagonalFemaleTotal d = femaleSpouseTotal x μ :=
    (Finset.sum_congr rfl fun i _ ↦ hf i).trans (femaleSpouseTotal_eq_sum_byHusband μ x).symm
  change (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
    2 ≤ pivotDiagonalFemaleTotal d ∧ pivotDiagonalFemaleTotal d ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧
    (n : ℝ) / 128 ≤ reverseDiagonalMaleTotal d * pivotDiagonalFemaleTotal d ∧
    (∀ i, (diagonalPairAt d i).2 / pivotDiagonalFemaleTotal d ≤ 12 * Real.log n / n) ∧
    ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (pivotDiagonalFemaleTotal d - 1)
  rw [hX', hY']
  refine ⟨?_, hgood.1, hY, hprod, ?_, ?_⟩
  · intro i
    rw [diagonalPairAt_splitScorePairs]
    exact ⟨⟨(hunit (.inl i) (μ i)).1.le, (hunit (.inl i) (μ i)).2⟩,
      ⟨(hunit (.inr (μ i)) i).1.le, (hunit (.inr (μ i)) i).2⟩⟩
  · intro i
    rw [hf]
    exact hgood.2.1 (μ i)
  · intro i
    rw [hm]
    exact hgood.2.2 i

/-- A rank-stable matching violates the logarithmic female-total lower bound. -/
def rankStableSmallFemaleTotalEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}

/-- A rank-stable matching in the concrete diagonal band fails its mask bound. -/
def rankStableBadPivotMaskEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    let z := splitScorePairs μ x
    z.1 ∈ pivotBaseDiagonalBand n ∧ z.2 ∈ badForwardMask z.1 ((n : ℝ) ^ (-11 / 20 : ℝ))}

/-- The logarithmic exception estimate applies simultaneously to all stable matchings. -/
theorem eventually_measure_rankStableSmallFemaleTotalEvent_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (rankStableSmallFemaleTotalEvent n) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le p] with n h
  let E (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  have hsub : rankStableSmallFemaleTotalEvent n ≤ᵐ[continuousScoreLaw n] ⋃ μ, E μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hY⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hY⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  exact h

/-- The actual score band has no heavy mask at any stable matching except on
an event whose probability is smaller than any fixed inverse power. -/
theorem eventually_measure_rankStableBadPivotMaskEvent_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (rankStableBadPivotMaskEvent n) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badForwardMaskAnchorEvent_on_pivotBaseDiagonalBand_le
      (p + 2), eventually_expectedNumStableMatchings_le_sizeLog,
      eventually_gt_atTop (1 : ℕ)] with n h hm hn
  let E (μ : Matching n) := badForwardMaskAnchorEvent μ (pivotBaseDiagonalBand n)
    ((n : ℝ) ^ (-11 / 20 : ℝ))
  have hsub : rankStableBadPivotMaskEvent n ≤ᵐ[continuousScoreLaw n] ⋃ μ, E μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hd, hb⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hd, hb⟩
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hm' : expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
    rw [sq]
    exact hm.trans (mul_le_mul_of_nonneg_left hlog hn₀.le)
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  refine h.trans ?_
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(p + 2))) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hm') _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_two, ← Real.rpow_add hn₀,
        show (2 : ℝ) + -(p + 2) = -p by ring]

/-- The base score geometry needed for the pivot proof, holding simultaneously
at all stable matchings; the mask is tested only below the upper score-band edge. -/
def goodPivotBaseGeometry (n : ℕ) : Set (ScoreProfile n) :=
  {x | x ∈ goodCoexposureScores n ∧
    (∀ μ : Matching n, IsStable (profileOfScores x) μ →
      (9 / 10 : ℝ) * Real.log n ≤ femaleSpouseTotal x μ ∧
      (n : ℝ) / 128 ≤ maleSpouseTotal x μ * femaleSpouseTotal x μ) ∧
    ∀ μ : Matching n, IsStable (profileOfScores x) μ →
      femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ) →
      let z := splitScorePairs μ x
      z.1 ∈ pivotBaseDiagonalBand n ∧ z.2 ∉ badForwardMask z.1 ((n : ℝ) ^ (-11 / 20 : ℝ))}

private def rankStableSmallSpouseProductEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}

private theorem badPivotBaseGeometry_subset (n : ℕ) :
    (goodPivotBaseGeometry n)ᶜ ⊆
      (((goodCoexposureScores n)ᶜ ∪ rankStableSmallFemaleTotalEvent n) ∪
        rankStableSmallSpouseProductEvent n) ∪ rankStableBadPivotMaskEvent n := by
  intro x hx
  by_cases hc : x ∈ goodCoexposureScores n
  · by_cases hsmall : x ∈ rankStableSmallFemaleTotalEvent n
    · exact Or.inl (Or.inl (Or.inr hsmall))
    · by_cases hprod : x ∈ rankStableSmallSpouseProductEvent n
      · exact Or.inl (Or.inr hprod)
      · by_cases hmask : x ∈ rankStableBadPivotMaskEvent n
        · exact Or.inr hmask
        · exfalso
          apply hx
          have hprod' (μ : Matching n) (hμ : IsStable (profileOfScores x) μ) :
              (n : ℝ) / 128 ≤ maleSpouseTotal x μ * femaleSpouseTotal x μ :=
            le_of_not_gt fun h ↦ hprod ⟨μ, hμ, h⟩
          refine ⟨hc, fun μ hμ ↦ ⟨le_of_not_gt (fun h ↦ hsmall ⟨μ, hμ, h⟩),
            hprod' μ hμ⟩, ?_⟩
          intro μ hμ hY
          have hd := splitScorePairs_mem_pivotBaseDiagonalBand μ hc.2.1 (hc.2.2 μ hμ)
            (hprod' μ hμ) hY
          exact ⟨hd, fun h ↦ hmask ⟨μ, hμ, hd, h⟩⟩
  · exact Or.inl (Or.inl (Or.inl hc))

/-- With high probability the base score and mask bounds hold simultaneously.
This does not assert abundance of singleton pivots in the band. -/
theorem tendsto_measure_badPivotBaseGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodPivotBaseGeometry n)ᶜ) atTop (𝓝 0) := by
  have hcoex := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    (C := 1) zero_le_one
    (by simpa only [one_mul] using eventually_expectedNumStableMatchings_le_sizeLog)
  have hrate : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hzero {f : ℕ → ℝ≥0∞}
      (h : ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) :
      Tendsto f atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze' hrate (Eventually.of_forall fun _ ↦ zero_le) h
  have hsmall := hzero (eventually_measure_rankStableSmallFemaleTotalEvent_le 1)
  have hprod := hzero (eventually_measure_exists_stable_smallSpouseProduct_le 1)
  have hmask := hzero (eventually_measure_rankStableBadPivotMaskEvent_le 1)
  have hmajor := ((hcoex.add hsmall).add hprod).add hmask
  simp only [add_zero] at hmajor
  refine tendsto_const_nhds.squeeze' hmajor (Eventually.of_forall fun _ ↦ zero_le) ?_
  exact Eventually.of_forall fun n ↦ (measure_mono (badPivotBaseGeometry_subset n)).trans
    ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))

end LennonPittelFormalization

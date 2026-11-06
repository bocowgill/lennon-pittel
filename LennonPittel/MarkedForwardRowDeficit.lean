module

public import LennonPittel.ForwardRowDeficitConcentration
public import LennonPittel.PivotForwardRowDeficit
public import LennonPittel.PivotSpouseSquareRegularity

/-!
# The forward endpoint deficit at stable marks

The weighted loss from the finite upper endpoint of each successor integral
has a superpolynomial tail under the marked score law.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private theorem eventually_forwardEndpointMean_le :
    ∀ᶠ n : ℕ in atTop, ∀ Y : ℝ, (9 / 10 : ℝ) * Real.log n ≤ Y →
      (Real.exp 1 - 1) * (4 * Real.exp 1 * Y * Real.exp (-Y)) ≤
        (n : ℝ) ^ (-3 / 4 : ℝ) / 2 := by
  let C := 40 * Real.exp 1 * (Real.exp 1 - 1)
  have he₁ : 0 ≤ Real.exp 1 - 1 := by linarith only [Real.exp_one_gt_two]
  have hC : 0 ≤ C := by
    unfold C
    positivity
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (3 / 50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hpow.eventually_ge_atTop (2 * C)] with n hn hc
  intro Y hY
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsmall : Y ≤ 10 * Real.exp (Y / 10) := by
    linarith only [Real.add_one_le_exp (Y / 10)]
  have hfactor : 0 ≤ 4 * Real.exp 1 * (Real.exp 1 - 1) * Real.exp (-Y) := by
    positivity
  have he : Real.exp (-(9 / 10 : ℝ) * Y) ≤ (n : ℝ) ^ (-81 / 100 : ℝ) := by
    rw [Real.rpow_def_of_pos hn₀]
    apply Real.exp_le_exp.mpr
    linarith only [hY]
  have hd : C ≤ (n : ℝ) ^ (3 / 50 : ℝ) / 2 := by linarith only [hc]
  calc
    _ = Y * (4 * Real.exp 1 * (Real.exp 1 - 1) * Real.exp (-Y)) := by ring
    _ ≤ (10 * Real.exp (Y / 10)) *
        (4 * Real.exp 1 * (Real.exp 1 - 1) * Real.exp (-Y)) :=
      mul_le_mul_of_nonneg_right hsmall hfactor
    _ = C * Real.exp (-(9 / 10 : ℝ) * Y) := by
      rw [show -(9 / 10 : ℝ) * Y = Y / 10 + -Y by ring, Real.exp_add]
      unfold C
      ring
    _ ≤ C * (n : ℝ) ^ (-81 / 100 : ℝ) := mul_le_mul_of_nonneg_left he hC
    _ ≤ ((n : ℝ) ^ (3 / 50 : ℝ) / 2) * (n : ℝ) ^ (-81 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hn₀.le _)
    _ = _ := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hn₀]
      congr 2
      norm_num

private theorem eventually_forwardEndpointRate_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ (-3 / 4 : ℝ) / 2) /
      (12 * Real.log n / n)) ≤ (n : ℝ) ^ (-q) := by
  have h := (((isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) 2 (by norm_num)).const_mul_left
    (24 * q)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), h] with n hn hh
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₁]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have habs : |(24 * q) * Real.log (n : ℝ) ^ (2 : ℝ)| ≤ |(n : ℝ) ^ (1 / 4 : ℝ)| := hh
  rw [abs_of_nonneg (Real.rpow_nonneg hn₀.le _), Real.rpow_two] at habs
  have hle := (le_abs_self _).trans habs
  have hB : 0 < 12 * Real.log (n : ℝ) / n := by positivity
  have hp : (n : ℝ) ^ (-3 / 4 : ℝ) * n = (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (-3 / 4 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
  have haux : q * Real.log (n : ℝ) ≤
      ((n : ℝ) ^ (-3 / 4 : ℝ) / 2) / (12 * Real.log n / n) := by
    apply (le_div_iff₀ hB).mpr
    rw [← mul_div_assoc, div_le_iff₀ hn₀, div_mul_eq_mul_div, hp, le_div_iff₀ (by norm_num)]
    linarith only [hle]
  rw [show (n : ℝ) ^ (-q) = Real.exp (Real.log n * -q) from Real.rpow_def_of_pos hn₀ _]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith only [haux]

/-- A large weighted endpoint error with the logarithmic total and share cutoffs. -/
def badForwardEndpointVectors (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | (2 ≤ spouseVectorTotal z.2 ∧ (9 / 10 : ℝ) * Real.log n ≤ spouseVectorTotal z.2 ∧
      ∀ i, z.2 i / spouseVectorTotal z.2 ≤ 12 * Real.log n / n) ∧
    (n : ℝ) ^ (-3 / 4 : ℝ) < forwardWeightedEndpointError z.1 z.2}

theorem measurableSet_badForwardEndpointVectors (n : ℕ) :
    MeasurableSet (badForwardEndpointVectors n) := by
  have hY : Measurable fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseVectorTotal z.2 :=
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i).comp measurable_snd
  unfold badForwardEndpointVectors
  simp only [ofPred_and, ofPred_forall]
  exact ((measurableSet_le measurable_const hY).inter
    ((measurableSet_le measurable_const hY).inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le
        (((measurable_pi_apply i).comp measurable_snd).div hY) measurable_const))).inter
    (measurableSet_lt measurable_const (measurable_forwardWeightedEndpointError n))

private theorem eventually_forwardEndpointSection_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin n → ℝ, (∀ j, y j ∈ Icc (0 : ℝ) 1) →
      (∫⁻ x, (badForwardEndpointVectors n).indicator
        (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) ∂spouseVectorLaw n) ≤
      femaleSpouseStabilityDensity y * ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_forwardEndpointMean_le, eventually_forwardEndpointRate_le q,
    eventually_gt_atTop (1 : ℕ)] with n hmean hrate hn
  intro y hy
  let Y := spouseVectorTotal y
  let B := {x : Fin n → ℝ | (n : ℝ) ^ (-3 / 4 : ℝ) < forwardWeightedEndpointError x y}
  by_cases hg : 2 ≤ Y ∧ (9 / 10 : ℝ) * Real.log n ≤ Y ∧
      ∀ i, y i / Y ≤ 12 * Real.log n / n
  · have hB : MeasurableSet B := measurableSet_lt measurable_const
      ((measurable_forwardWeightedEndpointError n).comp (measurable_id.prodMk measurable_const))
    have hpoint (x : Fin n → ℝ) :
        (badForwardEndpointVectors n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2)
          (x, y) = B.indicator (fun x ↦ spouseStabilityKernel x y) x := by
      have hmem : (x, y) ∈ badForwardEndpointVectors n ↔ x ∈ B := and_iff_right hg
      by_cases hx : x ∈ B
      · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
      · rw [indicator_of_notMem (hmem.not.mpr hx), indicator_of_notMem hx]
    have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
    have hlog := Real.log_pos hn₁
    have hwidth : 0 < 12 * Real.log (n : ℝ) / n := by positivity
    simp_rw [hpoint]
    rw [lintegral_indicator hB, ← withDensity_apply _ hB,
      spouseStabilityKernel_withDensity_eq y hy hg.1, Measure.smul_apply, smul_eq_mul]
    apply mul_le_mul_right
    refine (measure_pi_forwardWeightedEndpointError_gt_le y hy hg.1 hwidth hg.2.2 _).trans ?_
    apply ENNReal.ofReal_le_ofReal
    refine (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hwidth).mpr ?_)).trans hrate
    linarith only [hmean Y hg.2.1]
  · have hz (x : Fin n → ℝ) :
        (badForwardEndpointVectors n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2)
          (x, y) = 0 := indicator_of_notMem (fun h ↦ hg h.1) _
    simp_rw [hz, lintegral_zero]
    exact zero_le

/-- A score-stable mark in the logarithmic score geometry with a large endpoint error. -/
def badForwardEndpointMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧
    ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ badForwardEndpointVectors n}

/-- The marked expected number of bad endpoint tests is eventually at most
any fixed inverse power of the market size. -/
theorem eventually_sum_measure_badForwardEndpointMark_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ μ : Matching n, continuousScoreLaw n (badForwardEndpointMark μ)) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_forwardEndpointSection_le (q + 2),
    eventually_expectedNumStableMatchings_le_sizeLog, eventually_gt_atTop (1 : ℕ)]
    with n hsec hmean hn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : Real.log (n : ℝ) ≤ n :=
    (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hmean' : expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
    rw [sq]
    exact hmean.trans (mul_le_mul_of_nonneg_left hlog hn₀.le)
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal ((n : ℝ) ^ (-(q + 2))) := Finset.sum_le_sum fun μ _ ↦
      measure_stable_and_spouseVectors_le_of_section μ (measurableSet_badForwardEndpointVectors n)
        ENNReal.ofReal_ne_top hsec
    _ = ENNReal.ofReal (expectedNumStableMatchings n) *
        ENNReal.ofReal ((n : ℝ) ^ (-(q + 2))) := by
      rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(q + 2))) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hmean') le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_two, ← Real.rpow_add hn₀,
        show (2 : ℝ) + -(q + 2) = -q by ring]

def rankStableBadForwardEndpointEvent (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
    ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈
      badForwardEndpointVectors n}

/-- The bound controls the probability of a large endpoint error
at any rank-stable matching in the logarithmic score geometry. -/
theorem eventually_measure_exists_rankStable_badForwardEndpoint_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      (rankStableBadForwardEndpointEvent n) ≤ ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_sum_measure_badForwardEndpointMark_le q] with n hn
  have hsub : rankStableBadForwardEndpointEvent n ≤ᵐ[continuousScoreLaw n]
      ⋃ μ : Matching n, badForwardEndpointMark μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hz⟩ := hbad
    exact mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hz⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rwa [tsum_fintype]

/-- The score regularity event, with the endpoint loss tested at every stable mark. -/
def goodForwardReferenceGeometry (n : ℕ) : Set (ScoreProfile n) :=
  goodPivotScoreGeometry n \ rankStableBadForwardEndpointEvent n

/-- On the common good event, the reference row comparison is available at
every stable matching, including those outside the pivot score band. -/
theorem eventually_hasForwardReferenceDeficit_of_goodGeometry :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ goodForwardReferenceGeometry n, ∀ μ : Matching n,
      IsStable (profileOfScores x) μ →
      HasForwardReferenceDeficit (splitScorePairs μ x).1 (3 * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
  filter_upwards [eventually_hasForwardReferenceDeficit, eventually_gt_atTop (0 : ℕ)]
    with n href hn
  intro x hx μ hμ
  let d := (splitScorePairs μ x).1
  let xm (i : Fin n) := maleSpouseScore x μ i
  let yf := femaleSpouseByHusband μ x
  have hmale (i : Fin n) : (diagonalPairAt d i).1 = xm i :=
    congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
  have hfemale (i : Fin n) : (diagonalPairAt d i).2 = yf i := by
    simp only [d, diagonalPairAt_splitScorePairs, yf, femaleSpouseByHusband, femaleSpouseScore,
      Equiv.symm_apply_apply]
  have hY : pivotDiagonalFemaleTotal d = femaleSpouseTotal x μ :=
    (Finset.sum_congr rfl fun i _ ↦ hfemale i).trans (femaleSpouseTotal_eq_sum_byHusband μ x).symm
  have hY' : spouseVectorTotal yf = femaleSpouseTotal x μ :=
    (femaleSpouseTotal_eq_sum_byHusband μ x).symm
  have hw (i : Fin n) : forwardSpouseWeight d i = femaleSpouseScore x μ (μ i) /
      femaleSpouseTotal x μ := by
    change (diagonalPairAt d i).2 / pivotDiagonalFemaleTotal d = _
    rw [hfemale i, hY]
    rfl
  have hg := hx.1.1.1.2.2 μ hμ
  have hu := hx.1.1.1.2.1
  have hlog := (hx.1.1.2.1 μ hμ).1
  have hpt (i : Fin n) : yf i / spouseVectorTotal yf ≤ 12 * Real.log n / n := by
    rw [hY']
    exact hg.2.1 (μ i)
  have he : forwardWeightedEndpointError xm yf ≤ (n : ℝ) ^ (-3 / 4 : ℝ) :=
    le_of_not_gt fun h ↦ hx.2 ⟨μ, hμ, ⟨hY'.symm ▸ hg.1, hY'.symm ▸ hlog, hpt⟩, h⟩
  apply href d
  · intro i
    rw [hmale i]
    exact ⟨(hu (.inl i) (μ i)).1.le, (hu (.inl i) (μ i)).2⟩
  · intro i
    rw [hfemale i]
    simpa only [yf, femaleSpouseByHusband, femaleSpouseScore, Equiv.symm_apply_apply] using
      (show x (.inr (μ i)) i ∈ Icc 0 1 from ⟨(hu (.inr (μ i)) i).1.le, (hu (.inr (μ i)) i).2.le⟩)
  · rw [hY]
    exact hg.1
  · intro i
    rw [hw i]
    exact hg.2.1 (μ i)
  · intro i
    rw [hmale i, hY]
    exact hg.2.2 i
  · simp_rw [hw]
    rw [Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)]
    exact (spouseSquareWeights_of_goodPivotScoreGeometry hn hx.1 μ hμ).2
  · simp_rw [hw, hmale, hY]
    simpa only [forwardWeightedEndpointError, hY', yf, femaleSpouseByHusband, neg_mul] using he

/-- The augmented simultaneous score event has probability tending to one. -/
theorem tendsto_measure_badForwardReferenceGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodForwardReferenceGeometry n)ᶜ) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have he : Tendsto (fun n ↦ continuousScoreLaw n (rankStableBadForwardEndpointEvent n))
      atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze' hr (Eventually.of_forall fun _ ↦ zero_le)
      (eventually_measure_exists_rankStable_badForwardEndpoint_le 1)
  have hmajor := tendsto_measure_badPivotScoreGeometry_zero.add he
  simp only [add_zero] at hmajor
  refine tendsto_const_nhds.squeeze' hmajor (Eventually.of_forall fun _ ↦ zero_le) ?_
  exact Eventually.of_forall fun n ↦ by
    rw [goodForwardReferenceGeometry, Set.sdiff_eq, compl_inter, compl_compl]
    exact measure_union_le _ _

end LennonPittelFormalization

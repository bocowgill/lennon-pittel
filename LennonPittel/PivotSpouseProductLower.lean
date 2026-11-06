module

public import LennonPittel.CoexposureSpouseShells
public import LennonPittel.StableMaleSpouseRowLaw
public import LennonPittel.IndependentFlagLowerTail
public import LennonPittel.FiniteProductDensity
public import LennonPittel.PittelFirstMoment
public import LennonPittel.SmallSpouseTotalLog

/-!
# The lower spouse-score product at a stable mark

For fixed female spouse scores, the male coordinates have a product law after
normalization. A positive fraction fall in a short interval on scale `1 / Y`,
so the product of the two spouse totals is rarely smaller than `n / 128`.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The sum of the men's spouse scores at a matching. -/
def maleSpouseTotal {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ i, maleSpouseScore x μ i

theorem measurable_maleSpouseTotal {n : ℕ} (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseTotal x μ) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_maleSpouseScore μ i

/-- A measurable test on the two spouse vectors corresponding to a small
score product and female total at least two. -/
def lowSpouseProductVectorSet (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | 2 ≤ spouseVectorTotal z.2 ∧
    spouseVectorTotal z.1 * spouseVectorTotal z.2 < (n : ℝ) / 128}

theorem measurableSet_lowSpouseProductVectorSet (n : ℕ) :
    MeasurableSet (lowSpouseProductVectorSet n) := by
  have h : Measurable (@spouseVectorTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  exact (measurableSet_le measurable_const (h.comp measurable_snd)).inter
    (measurableSet_lt ((h.comp measurable_fst).mul (h.comp measurable_snd)) measurable_const)

private theorem measurable_jointSpouseStabilityKernel (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseStabilityKernel z.1 z.2) := by
  unfold spouseStabilityKernel scoreRowKernel
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd)

private theorem ae_spouseVector_nonnegative_unit (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ j, y j ∈ Icc (0 : ℝ) 1 :=
  ae_all_iff.2 fun j ↦
    (measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) j).quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Icc)

/-- A bound on each female-vector section transfers to the original score
law at a stable mark. The female marginal retains the whole stability mass. -/
theorem measure_stable_and_spouseVectors_le_of_section {n : ℕ} (μ : Matching n)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (hsec : ∀ y : Fin n → ℝ, (∀ j, y j ∈ Icc (0 : ℝ) 1) →
      (∫⁻ x, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) ∂spouseVectorLaw n) ≤
        femaleSpouseStabilityDensity y * a) :
    continuousScoreLaw n
        {x | IsScoreStable x μ ∧
          ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} * a := by
  rw [continuousScoreLaw_stable_and_spouseVectors μ hB,
    lintegral_prod_symm' _ ((measurable_jointSpouseStabilityKernel n).indicator hB)]
  calc
    _ ≤ ∫⁻ y, femaleSpouseStabilityDensity y * a ∂spouseVectorLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_spouseVector_nonnegative_unit n] with y hy
      exact hsec y hy
    _ = _ := by
      rw [lintegral_mul_const' a _ ha]
      have h := continuousScoreLaw_stable_and_femaleSpouse μ (B := univ) MeasurableSet.univ
      simpa only [mem_univ, and_true, Measure.restrict_univ] using
        congrArg (fun b : ℝ≥0∞ ↦ b * a) h.symm

open scoped Classical in
/-- A small spouse-score product forces fewer than `n / 32` of the male
scores into the interval used by the independent-trials estimate. -/
theorem flagCount_lt_of_spouseProduct_lt {n : ℕ} {x : Fin n → ℝ} {Y : ℝ} {A : Set ℝ}
    (hY : 0 < Y) (hA : A ⊆ Ioi (1 / (4 * Y))) (hx : ∀ i, 0 ≤ x i)
    (hbad : spouseVectorTotal x * Y < (n : ℝ) / 128) :
    (∑ i, if x i ∈ A then (1 : ℝ) else 0) < (n : ℝ) / 32 := by
  have h₁ (i : Fin n) : (if x i ∈ A then (1 : ℝ) else 0) ≤ 4 * Y * x i := by
    by_cases hi : x i ∈ A
    · rw [ite_eq_left hi]
      have hl : 1 / (4 * Y) < x i := hA hi
      have h := ((div_lt_iff₀ (by positivity : 0 < 4 * Y)).mp hl).le
      simpa only [mul_comm (x i)] using h
    · rw [ite_eq_right hi]
      exact mul_nonneg (by positivity) (hx i)
  have hs : (∑ i, if x i ∈ A then (1 : ℝ) else 0) ≤ 4 * (spouseVectorTotal x * Y) := by
    calc
      _ ≤ ∑ i, 4 * Y * x i := Finset.sum_le_sum fun i _ ↦ h₁ i
      _ = _ := by rw [← Finset.mul_sum, spouseVectorTotal]; ring
  exact hs.trans_lt (by linarith only [hbad])

/-- At a fixed female vector the male stability density is a scalar
multiple of the product of its normalized row laws. -/
theorem spouseStabilityKernel_withDensity_eq {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y) :
    (spouseVectorLaw n).withDensity (fun x ↦ spouseStabilityKernel x y) =
      femaleSpouseStabilityDensity y • Measure.pi (normalizedStableMaleSpouseRowLaw y) := by
  let f (i : Fin n) (t : ℝ) :=
    ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t)
  let ν := stableMaleSpouseRowLaw y
  let (i : Fin n) : IsFiniteMeasure (ν i) := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  have hf (i : Fin n) : Measurable (f i) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  let : ∀ i, IsFiniteMeasure (((fun _ : Fin n ↦ unitScoreLaw) i).withDensity (f i)) :=
    fun i ↦ stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  have htilt : (spouseVectorLaw n).withDensity (fun x ↦ spouseStabilityKernel x y) =
      Measure.pi ν :=
    pi_withDensity_product (fun _ : Fin n ↦ unitScoreLaw) f hf
  have hmass : (∏ i : Fin n, ν i univ) = femaleSpouseStabilityDensity y :=
    Finset.prod_congr rfl fun i _ ↦ stableMaleSpouseRowLaw_univ y hy i
  rw [htilt, pi_eq_prod_smul_pi_normalized ν
    (fun i ↦ (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'), hmass]
  rfl

/-- The small-product event under the normalized male row product has
probability at most `exp(-n/128)`. -/
theorem measure_pi_spouseProduct_lt_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y) :
    (Measure.pi (normalizedStableMaleSpouseRowLaw y))
      {x | spouseVectorTotal x * spouseVectorTotal y < (n : ℝ) / 128} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  let Y := spouseVectorTotal y
  let ν := normalizedStableMaleSpouseRowLaw y
  let A : Set ℝ := Ioc (1 / (4 * Y)) (1 / (2 * Y))
  let (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedStableMaleSpouseRowLaw_isProbabilityMeasure y hy hs i
  have hY : 0 < Y := by linarith
  have htail := measure_pi_flagCount_lt_le ν (fun _ ↦ A) (fun _ ↦ measurableSet_Ioc)
    (normalizedStableMaleSpouseRowLaw_goodInterval_ge y hy hs)
  rw [Fintype.card_fin] at htail
  have hae : ∀ᵐ x ∂Measure.pi ν, ∀ i, 0 ≤ x i := ae_all_iff.2 fun i ↦
    ((measurePreserving_eval ν i).quasiMeasurePreserving.ae
      (ae_normalizedStableMaleSpouseRowLaw_mem_Icc y i)).mono fun _ hx ↦ hx.1
  refine (measure_mono_ae ?_).trans htail
  filter_upwards [hae] with x hx hbad
  exact flagCount_lt_of_spouseProduct_lt (A := A) hY (fun _ hi ↦ hi.1) hx hbad

/-- The joint spouse-vector law gives the same relative bound without
normalizing the probability of the stable mark. -/
theorem lintegral_lowSpouseProductVectorSection_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, (lowSpouseProductVectorSet n).indicator
        (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) ∂spouseVectorLaw n) ≤
      femaleSpouseStabilityDensity y * ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  by_cases hs : 2 ≤ spouseVectorTotal y
  · let B : Set (Fin n → ℝ) :=
      {x | spouseVectorTotal x * spouseVectorTotal y < (n : ℝ) / 128}
    have htotal : Measurable (@spouseVectorTotal n) :=
      Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
    have hB : MeasurableSet B := measurableSet_lt (htotal.mul_const _) measurable_const
    have hpoint (x : Fin n → ℝ) :
        (lowSpouseProductVectorSet n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2)
          (x, y) = B.indicator (fun x ↦ spouseStabilityKernel x y) x := by
      have hmem : (x, y) ∈ lowSpouseProductVectorSet n ↔ x ∈ B := by
        exact and_iff_right hs
      by_cases hx : x ∈ B
      · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]
      · rw [indicator_of_notMem (hmem.not.mpr hx), indicator_of_notMem hx]
    simp_rw [hpoint]
    rw [lintegral_indicator hB, ← withDensity_apply _ hB,
      spouseStabilityKernel_withDensity_eq y hy hs, Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (measure_pi_spouseProduct_lt_le y hy hs) _
  · have hz (x : Fin n → ℝ) :
        (lowSpouseProductVectorSet n).indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) =
          0 := indicator_of_notMem (fun h ↦ hs h.1) _
    simp_rw [hz, lintegral_zero]
    exact zero_le

/-- A stable mark with female total at least two rarely has a spouse-score
product below `n / 128`. -/
theorem measure_stable_spouseProduct_lt_le {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  simpa only [lowSpouseProductVectorSet, mem_ofPred_eq, spouseVectorTotal,
    ← femaleSpouseTotal_eq_sum_byHusband, maleSpouseTotal] using
    measure_stable_and_spouseVectors_le_of_section μ (measurableSet_lowSpouseProductVectorSet n)
      ENNReal.ofReal_ne_top lintegral_lowSpouseProductVectorSection_le

/-- The fixed-mark bound summed over all complete matchings. -/
theorem sum_measure_stable_spouseProduct_lt_le (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) := by
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) :=
      Finset.sum_le_sum fun μ _ ↦ measure_stable_spouseProduct_lt_le μ
    _ = _ := by rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]

/-- A convenient eventual upper bound following from Pittel's verified
first-moment asymptotic. -/
theorem eventually_expectedNumStableMatchings_le_sizeLog :
    ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤ (n : ℝ) * Real.log n := by
  have he : (Real.exp 1)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ ((by norm_num : (1 : ℝ) < 2).trans Real.exp_one_gt_two)
  filter_upwards [(tendsto_order.mp tendsto_expectedNumStableMatchings_div_size_log).2 1 he,
    eventually_gt_atTop (1 : ℕ)] with n h hn
  have hn' : 1 < (n : ℝ) := by exact_mod_cast hn
  have hnorm : 0 < (n : ℝ) * Real.log n := mul_pos (by linarith) (Real.log_pos hn')
  simpa only [one_mul] using (div_le_iff₀ hnorm).mp h.le

private theorem eventually_sizeSq_mul_exp_le_neg_rpow (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (2 : ℕ) * Real.exp (-(n : ℝ) / 128) ≤
      (n : ℝ) ^ (-p) := by
  have hlog := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    (128 * (p + 2))).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog] with n hn hnlog
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have habs : |128 * (p + 2) * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hnlog
  rw [Real.rpow_one, abs_of_nonneg hn₀.le] at habs
  have h := (le_abs_self _).trans habs
  have hl : (p + 2) * Real.log n ≤ (n : ℝ) / 128 := by linarith
  have hE : Real.exp (-(n : ℝ) / 128) ≤ (n : ℝ) ^ (-(p + 2)) := by
    rw [Real.rpow_def_of_pos hn₀]
    exact Real.exp_le_exp.mpr (by linarith only [hl])
  calc
    _ ≤ (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-(p + 2)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = _ := by
      rw [← Real.rpow_two, ← Real.rpow_add hn₀, show (2 : ℝ) + -(p + 2) = -p by ring]

/-- For female total at least two, the expected exceptional count is
eventually smaller than any fixed inverse power of the market size. -/
theorem eventually_sum_measure_stable_spouseProduct_lt_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n
        {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
          maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_expectedNumStableMatchings_le_sizeLog,
    eventually_gt_atTop (1 : ℕ), eventually_sizeSq_mul_exp_le_neg_rpow p] with n hm hn hrate
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log (n : ℝ) ≤ n :=
    (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hm' : expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
    rw [sq]
    exact hm.trans (mul_le_mul_of_nonneg_left hlog hn₀.le)
  refine (sum_measure_stable_spouseProduct_lt_le n).trans ?_
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ)) * ENNReal.ofReal (Real.exp (-(n : ℝ) / 128)) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hm') _
    _ = ENNReal.ofReal ((n : ℝ) ^ (2 : ℕ) * Real.exp (-(n : ℝ) / 128)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrate

/-- Stable marks at which the product of the two totals is below `n / 128`. -/
def badSpouseProductMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧
    maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}

/-- The expected number of small-product stable marks is smaller than any
fixed inverse power, including marks with a very small female total. -/
theorem eventually_sum_measure_badSpouseProductMark_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badSpouseProductMark μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  have hL : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le (p + 1),
    eventually_sum_measure_stable_spouseProduct_lt_le (p + 1), hL,
    eventually_ge_atTop (2 : ℕ)] with n hsmall hbulk hnlog hn
  let A (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128}
  have hcover (μ : Matching n) : badSpouseProductMark μ ⊆ A μ ∪ B μ := by
    intro x hx
    by_cases hY : 2 ≤ femaleSpouseTotal x μ
    · exact Or.inr ⟨hx.1, hY, hx.2⟩
    · exact Or.inl ⟨hx.1, (lt_of_not_ge hY).trans_le hnlog⟩
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (A μ) + continuousScoreLaw n (B μ)) :=
      Finset.sum_le_sum fun μ _ ↦ (measure_mono (hcover μ)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hsmall hbulk
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add ha ha]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = 2 * a := (two_mul _).symm
        _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₂ ha
        _ = _ := calc
          _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -(p + 1) = -p by ring]

/-- The probability that any rank-stable matching has a small spouse-score
product is bounded by the expected number of exceptional marks. -/
theorem eventually_measure_exists_stable_smallSpouseProduct_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
        maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badSpouseProductMark_le p] with n h
  have hsub : {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧
        maleSpouseTotal x μ * femaleSpouseTotal x μ < (n : ℝ) / 128} ≤ᵐ[continuousScoreLaw n]
      ⋃ μ : Matching n, badSpouseProductMark μ := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    obtain ⟨μ, hμ, hp⟩ := hbad
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx μ).mp hμ, hp⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rwa [tsum_fintype]

end LennonPittelFormalization

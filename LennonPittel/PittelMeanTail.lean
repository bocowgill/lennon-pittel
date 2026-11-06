module

public import LennonPittel.CoexposureSpouseShells

/-!
# Radial windows for Pittel's first moment

The upper and lower radial windows both have logarithmic width asymptotic to
`log n`. The region below the windows has negligible first-moment mass.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The unit cube of feasible female spouse scores. -/
def pittelScoreCube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ ↦ Icc (0 : ℝ) 1

theorem measurableSet_pittelScoreCube (n : ℕ) : MeasurableSet (pittelScoreCube n) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)

/-- The fixed-matching density extended by zero to the ambient vector space. -/
noncomputable def pittelDensity (n : ℕ) : (Fin n → ℝ) → ℝ≥0∞ :=
  (pittelScoreCube n).indicator femaleSpouseStabilityDensity

theorem measurable_pittelDensity (n : ℕ) : Measurable (pittelDensity n) :=
  (measurable_femaleSpouseStabilityDensity n).indicator (measurableSet_pittelScoreCube n)

theorem pittelDensity_eq_ofReal_prod {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    pittelDensity n y =
      ENNReal.ofReal (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) := by
  rw [pittelDensity, indicator_of_mem (show y ∈ pittelScoreCube n from fun j _ ↦ hy j)]
  unfold femaleSpouseStabilityDensity
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro i _
  unfold scoreRowMass
  refine intervalIntegral.integral_nonneg (by norm_num) fun x hx ↦ ?_
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy j).1
    _ ≤ 1 := by simpa only [one_mul] using (hy j).2)

/-- A crude bound, sufficient for atypical angles and small radii at least two. -/
theorem pittelDensity_le_inv_pow {n : ℕ} {y : Fin n → ℝ} (hs : 2 ≤ spouseVectorTotal y) :
    pittelDensity n y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n) := by
  by_cases hy : y ∈ pittelScoreCube n
  · have hcube (i : Fin n) : y i ∈ Icc (0 : ℝ) 1 := hy i (mem_univ i)
    rw [pittelDensity_eq_ofReal_prod hcube]
    apply ENNReal.ofReal_le_ofReal
    simpa only [spouseVectorTotal, Fintype.card_fin] using
      scoreRowMass_prod_le_inv_pow y hcube hs
  · simp [pittelDensity, indicator_of_notMem hy]

/-- The density vanishes when the radius exceeds the cube's total capacity. -/
theorem pittelDensity_eq_zero_of_size_lt {n : ℕ} {y : Fin n → ℝ}
    (hy : (n : ℝ) < spouseVectorTotal y) : pittelDensity n y = 0 := by
  refine indicator_of_notMem (fun h ↦ hy.not_ge ?_) _
  calc
    spouseVectorTotal y ≤ ∑ _ : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ (h i (mem_univ i)).2
    _ = (n : ℝ) := by simp

/-- Sum the fixed-matching density identity over the matching labels. -/
theorem sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B}) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y in B, pittelDensity n y) := by
  simp_rw [continuousScoreLaw_stable_and_femaleSpouse _ hB]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [spouseVectorLaw_eq_restrict_volume, Measure.restrict_restrict hB]
  change (n.factorial : ℝ≥0∞) *
    (∫⁻ y in B ∩ pittelScoreCube n, femaleSpouseStabilityDensity y) = _
  unfold pittelDensity
  rw [setLIntegral_indicator (measurableSet_pittelScoreCube n),
    inter_comm B (pittelScoreCube n)]

/-- Knuth's integral in the existing independent uniform preference model. -/
theorem ofReal_expectedNumStableMatchings_eq_pittelDensity (n : ℕ) :
    ENNReal.ofReal (expectedNumStableMatchings n) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y, pittelDensity n y) := by
  rw [← sum_measure_scoreStable_eq_expected]
  simpa only [mem_univ, and_true, Measure.restrict_univ] using
    (sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity
      (n := n) MeasurableSet.univ)

/-- Both windows start at six times the natural logarithm of the size. -/
noncomputable def pittelRadiusLower (n : ℕ) : ℝ := 6 * Real.log n

/-- This upper radius makes the entire typical angular region fit inside the cube. -/
noncomputable def pittelRadiusUpper (n : ℕ) : ℝ := n / (Real.log n) ^ 2

private theorem tendsto_log_nat_atTop : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem eventually_two_le_pittelRadiusLower : ∀ᶠ n in atTop, 2 ≤ pittelRadiusLower n := by
  filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
  unfold pittelRadiusLower
  linarith

theorem eventually_pittelRadiusLower_le_upper :
    ∀ᶠ n in atTop, pittelRadiusLower n ≤ pittelRadiusUpper n := by
  have h : Tendsto (fun n : ℕ ↦ 6 * (Real.log n)^3 / (n : ℝ)) atTop (𝓝 0) := by
    have h' := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)).const_mul 6
    simpa [Function.comp_def, mul_div_assoc] using h'
  filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one, eventually_gt_atTop (1 : ℕ)]
    with n hn hn'
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn')
  have hb : 6 * (Real.log n) ^ 3 < (n : ℝ) := by
    simpa only [one_mul] using (div_lt_iff₀ hpos).mp hn
  unfold pittelRadiusLower pittelRadiusUpper
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  calc
    6 * Real.log n * Real.log n ^ 2 = 6 * Real.log n ^ 3 := by ring
    _ ≤ (n : ℝ) := hb.le

theorem eventually_pittelRadiusUpper_le_size :
    ∀ᶠ n in atTop, pittelRadiusUpper n ≤ (n : ℝ) := by
  filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
  unfold pittelRadiusUpper
  apply div_le_self (Nat.cast_nonneg _)
  nlinarith

private theorem tendsto_log_log_nat_ratio_zero :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log n) / Real.log n) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_log_nat_atTop

theorem tendsto_log_pittelRadiusLower_ratio_zero :
    Tendsto (fun n : ℕ ↦ Real.log (pittelRadiusLower n) / Real.log n) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ ↦ Real.log 6 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat_atTop
  have h := hconst.add tendsto_log_log_nat_ratio_zero
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hn
  rw [pittelRadiusLower, Real.log_mul (by norm_num) hn.ne', add_div]

theorem tendsto_log_pittelWindowUpper_ratio_one :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) / pittelRadiusLower n) / Real.log n)
      atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_log_pittelRadiusLower_ratio_zero
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)]
    with n hlog hn
  have hL : 0 < pittelRadiusLower n := mul_pos (by norm_num) hlog
  rw [Real.log_div (by exact_mod_cast hn.ne') hL.ne', sub_div, div_self hlog.ne']

theorem tendsto_log_pittelWindowLower_ratio_one :
    Tendsto (fun n : ℕ ↦ Real.log (pittelRadiusUpper n / pittelRadiusLower n) / Real.log n)
      atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_log_log_nat_ratio_zero.const_mul 2)).sub tendsto_log_pittelRadiusLower_ratio_zero
  simp only [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0, eventually_gt_atTop (0 : ℕ)]
    with n hlog hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < pittelRadiusLower n := mul_pos (by norm_num) hlog
  have hU : 0 < pittelRadiusUpper n := div_pos hn' (sq_pos_of_pos hlog)
  rw [Real.log_div hU.ne' hL.ne', pittelRadiusUpper,
    Real.log_div hn'.ne' (pow_ne_zero _ hlog.ne'), Real.log_pow, sub_div, sub_div,
    div_self hlog.ne', mul_div_assoc]
  norm_num

/-- A logarithmic window measured using its nonnegative `1 / s` density. -/
theorem lintegral_Ioc_inv_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal s⁻¹) = ENNReal.ofReal (Real.log (b / a)) := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ s⁻¹) volume a b :=
    (continuousOn_id.inv₀ fun _ hs ↦
      (ha.trans_le ((uIcc_of_le hab ▸ hs).1)).ne').intervalIntegrable
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi),
    ← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using
    inv_nonneg.mpr (ha.trans hs.1).le

private theorem measurable_pittelTotal (n : ℕ) : Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

private theorem pittelDensity_eq_zero_of_exists_neg {n : ℕ} {y : Fin n → ℝ}
    (hy : ¬∀ i, 0 ≤ y i) : pittelDensity n y = 0 := by
  exact indicator_of_notMem (fun h ↦ hy fun i ↦ (h i (mem_univ i)).1) _

private theorem pittelDensity_mass_single_shell_le {n : ℕ} {l r : ℝ}
    (hl : 2 ≤ l) (hr : 0 ≤ r) :
    (∫⁻ y in scoreSimplex n r ∩ {y | l ≤ spouseVectorTotal y}, pittelDensity n y) ≤
      ENNReal.ofReal (Real.exp 2 * (r / l) ^ n / (n.factorial : ℝ)) := by
  let S := scoreSimplex n r ∩ {y | l ≤ spouseVectorTotal y}
  have hS : MeasurableSet S :=
    (measurableSet_scoreSimplex _ _).inter (measurableSet_le measurable_const
      (measurable_pittelTotal n))
  have hl' : 0 < l := by linarith
  have hc' : 0 ≤ Real.exp 2 / l ^ n := by positivity
  calc
    _ ≤ ∫⁻ _ in S, ENNReal.ofReal (Real.exp 2 / l ^ n) := by
      apply setLIntegral_mono' hS
      intro y hy
      exact (pittelDensity_le_inv_pow (hl.trans hy.2)).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (Real.exp_pos _).le
          (pow_pos hl' _) (pow_le_pow_left₀ hl'.le hy.2 _)))
    _ = ENNReal.ofReal (Real.exp 2 / l ^ n) * volume S := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (Real.exp 2 / l ^ n) * ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n hr]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc', div_pow]
      congr 1
      ring

private theorem pittelDensity_mass_ge_two_le {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 2 ≤ R) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y},
      pittelDensity n y) ≤
      ENNReal.ofReal (Real.exp 3 * ((n : ℝ) * Real.log (R / 2) + 2)) := by
  let N : ℕ := ⌈(n : ℝ) * Real.log (R / 2)⌉₊
  let r (j : ℕ) : ℝ := 2 * Real.exp ((j : ℝ) / n)
  let S (j : Fin (N + 1)) := scoreSimplex n (r (j + 1)) ∩ {y | r j ≤ spouseVectorTotal y}
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hr₂ (j : ℕ) : 2 ≤ r j := by
    dsimp [r]
    have he := Real.one_le_exp_iff.mpr (div_nonneg (Nat.cast_nonneg j) hn'.le)
    linarith
  have hRlog : 0 ≤ (n : ℝ) * Real.log (R / 2) :=
    mul_nonneg hn'.le (Real.log_nonneg (by linarith))
  have hcover : scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y} ⊆ ⋃ j, S j := by
    intro y hy
    let s := spouseVectorTotal y
    have hs₂ : 2 ≤ s := hy.2
    have hsR : s ≤ R := hy.1.2
    have hs₀ : 0 < s / 2 := by linarith
    let j : ℕ := ⌊(n : ℝ) * Real.log (s / 2)⌋₊
    have hlog : 0 ≤ Real.log (s / 2) := Real.log_nonneg (by linarith)
    have hle : (j : ℝ) ≤ (n : ℝ) * Real.log (s / 2) :=
      Nat.floor_le (mul_nonneg hn'.le hlog)
    have hlt : (n : ℝ) * Real.log (s / 2) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hj : j ≤ N := by
      apply Nat.floor_le_of_le
      refine (mul_le_mul_of_nonneg_left ?_ hn'.le).trans (Nat.le_ceil _)
      apply Real.log_le_log hs₀
      linarith
    have h₁ : (j : ℝ) / n ≤ Real.log (s / 2) :=
      (div_le_iff₀ hn').mpr (by rwa [mul_comm])
    have h₂ : Real.log (s / 2) ≤ ((j + 1 : ℕ) : ℝ) / n := by
      apply (le_div_iff₀ hn').mpr
      push_cast
      linarith
    have hl : r j ≤ s := by
      have he := Real.exp_le_exp.mpr h₁
      rw [Real.exp_log hs₀] at he
      dsimp [r]
      linarith
    have hu : s ≤ r (j + 1) := by
      have he := Real.exp_le_exp.mpr h₂
      rw [Real.exp_log hs₀] at he
      dsimp [r]
      linarith
    exact mem_iUnion.mpr ⟨⟨j, Nat.lt_succ_of_le hj⟩, ⟨hy.1.1, hu⟩, hl⟩
  have hlocal (j : Fin (N + 1)) : (∫⁻ y in S j, pittelDensity n y) ≤
      ENNReal.ofReal (Real.exp 3 / (n.factorial : ℝ)) := by
    refine (pittelDensity_mass_single_shell_le (hr₂ (j : ℕ)) (by positivity)).trans_eq ?_
    have hratio : r ((j : ℕ) + 1) / r j = Real.exp (1 / (n : ℝ)) := by
      dsimp only [r]
      rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0), ← Real.exp_sub]
      push_cast
      congr 1
      ring
    rw [hratio, ← Real.exp_nat_mul, show (n : ℝ) * (1 / (n : ℝ)) = 1 by
      field_simp, ← Real.exp_add]
    norm_num
  calc
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ j : Fin (N + 1), ∫⁻ y in S j, pittelDensity n y := by
      have h := (lintegral_mono_set hcover).trans (by simpa [tsum_fintype] using
        (lintegral_iUnion_le (μ := volume) S (pittelDensity n)))
      exact mul_le_mul_right h _
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (N + 1),
          ENNReal.ofReal (Real.exp 3 / (n.factorial : ℝ)) := by
      gcongr with j _
      exact hlocal j
    _ = ENNReal.ofReal (Real.exp 3 * ((N : ℝ) + 1)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (by linarith [Nat.ceil_lt_add_one hRlog])
        (Real.exp_pos _).le

private noncomputable def pittelTinyMass (n : ℕ) : ℝ≥0∞ :=
  (n.factorial : ℝ≥0∞) * (∫⁻ y in smallSpouseScoreSet n, pittelDensity n y)

private theorem tendsto_pittelTinyMass_zero : Tendsto pittelTinyMass atTop (𝓝 0) := by
  refine tendsto_sum_stable_smallSpouseScore_zero.congr fun n ↦ ?_
  exact sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity
    (measurableSet_smallSpouseScoreSet n)

private theorem pittelSmallMass_le {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 2 ≤ R) :
    (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y | spouseVectorTotal y ≤ R}, pittelDensity n y) ≤
      pittelTinyMass n + ENNReal.ofReal (Real.exp 3 * ((n : ℝ) * Real.log (R / 2) + 2)) := by
  have hEq :
      (∫⁻ y in {y | spouseVectorTotal y ≤ R}, pittelDensity n y) =
        ∫⁻ y in scoreSimplex n R, pittelDensity n y := by
    rw [← lintegral_indicator (measurableSet_le (measurable_pittelTotal n) measurable_const),
      ← lintegral_indicator (measurableSet_scoreSimplex n R)]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : ∀ i, 0 ≤ y i
    · by_cases hsum : spouseVectorTotal y ≤ R
      · rw [indicator_of_mem (show y ∈ {z | spouseVectorTotal z ≤ R} from hsum),
          indicator_of_mem (show y ∈ scoreSimplex n R from ⟨hy, hsum⟩)]
      · rw [indicator_of_notMem (show y ∉ {z | spouseVectorTotal z ≤ R} from hsum),
          indicator_of_notMem (show y ∉ scoreSimplex n R from fun h ↦ hsum h.2)]
    · by_cases hsum : spouseVectorTotal y ≤ R
      · rw [indicator_of_mem (show y ∈ {z | spouseVectorTotal z ≤ R} from hsum),
          pittelDensity_eq_zero_of_exists_neg hy,
          indicator_of_notMem (show y ∉ scoreSimplex n R from fun h ↦ hy h.1)]
      · rw [indicator_of_notMem (show y ∉ {z | spouseVectorTotal z ≤ R} from hsum),
          indicator_of_notMem (show y ∉ scoreSimplex n R from fun h ↦ hsum h.2)]
  have hsub : scoreSimplex n R ⊆
      smallSpouseScoreSet n ∪ (scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y}) := by
    intro y hy
    by_cases hs : 2 ≤ spouseVectorTotal y
    · exact Or.inr ⟨hy, hs⟩
    · exact Or.inl ⟨hy.1, lt_of_not_ge hs⟩
  rw [hEq]
  calc
    _ ≤ (n.factorial : ℝ≥0∞) *
        ((∫⁻ y in smallSpouseScoreSet n, pittelDensity n y) +
          ∫⁻ y in scoreSimplex n R ∩ {y | 2 ≤ spouseVectorTotal y}, pittelDensity n y) :=
      mul_le_mul_right ((lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)) _
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add le_rfl (pittelDensity_mass_ge_two_le hn hR)

private theorem tendsto_log_pittelRadiusLower_half_ratio_zero :
    Tendsto (fun n : ℕ ↦ Real.log (pittelRadiusLower n / 2) / Real.log n) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat_atTop
  have h := tendsto_log_pittelRadiusLower_ratio_zero.sub hconst
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_two_le_pittelRadiusLower] with n hn
  rw [Real.log_div (by linarith : pittelRadiusLower n ≠ 0) (by norm_num), sub_div]

private theorem tendsto_pittelNormalizer_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log n) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_log_nat_atTop

private theorem tendsto_pittelSmallMass_bound_ratio_zero :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (Real.exp 3 * ((n : ℝ) * Real.log (pittelRadiusLower n / 2) + 2)) /
        ENNReal.ofReal ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun n : ℕ ↦ (2 : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_pittelNormalizer_atTop
  have h := (tendsto_log_pittelRadiusLower_half_ratio_zero.add hconst).const_mul (Real.exp 3)
  simp only [add_zero, mul_zero] at h
  have h' := ENNReal.tendsto_ofReal h
  simp only [ENNReal.ofReal_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hn' hlog)]
  congr 1
  field_simp

/-- The scores below the logarithmic window contribute a vanishing fraction of
the `n log n` scale. -/
theorem tendsto_pittelSmallMass_ratio_zero :
    Tendsto (fun n : ℕ ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y | spouseVectorTotal y ≤ pittelRadiusLower n}, pittelDensity n y) /
        ENNReal.ofReal ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have h := tendsto_pittelTinyMass_zero.add tendsto_pittelSmallMass_bound_ratio_zero
  simp only [zero_add] at h
  refine tendsto_const_nhds.squeeze' h (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_two_le_pittelRadiusLower,
    tendsto_pittelNormalizer_atTop.eventually_ge_atTop 1] with n hn hL hnorm
  have hd : 1 ≤ ENNReal.ofReal ((n : ℝ) * Real.log n) := by
    simpa using ENNReal.ofReal_le_ofReal hnorm
  refine (ENNReal.div_le_div_right (pittelSmallMass_le hn hL) _).trans ?_
  rw [ENNReal.add_div]
  gcongr
  calc
    _ ≤ pittelTinyMass n / 1 := ENNReal.div_le_div_left hd _
    _ = _ := div_one _

end LennonPittelFormalization

module

public import LennonPittel.ExponentialSpouseSquareTail
public import LennonPittel.ExponentialSpouseAngles
public import LennonPittel.MarkedSpouseAngleComparison
public import LennonPittel.ScoreSideSwap
public import LennonPittel.PivotSpouseBandRegularity

/-!
# Squared spouse weights at all stable matchings

An angular tail transfers through the stability integral, then across the
two sides by symmetry. The resulting bound supplies the collision input
in the local reverse-decoration certificate.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- Share vectors with a large dimension-scaled sum of squared entries. -/
def largeSpouseAngularSquareSet (n : ℕ) : Set (Fin n → ℝ) :=
  {w | 24 < pittelAngularSquareScore w}

theorem measurableSet_largeSpouseAngularSquareSet (n : ℕ) :
    MeasurableSet (largeSpouseAngularSquareSet n) := by
  have h : Measurable (pittelAngularSquareScore : (Fin n → ℝ) → ℝ) := by
    unfold pittelAngularSquareScore
    fun_prop
  exact measurableSet_lt measurable_const h

/-- The simplex angular probability has a superpolynomial tail at this fixed threshold. -/
theorem eventually_measure_spouseAngularSquare_gt_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, spouseAngularLaw n (largeSpouseAngularSquareSet n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_measure_iidExponential_angleSquare_gt_le p hp] with n hn h
  rw [← map_spouseAngle_pi_expMeasure_one hn,
    Measure.map_apply (measurable_spouseAngle n) (measurableSet_largeSpouseAngularSquareSet n)]
  exact h

/-- A score-stable mark whose female squared shares exceed the fixed cutoff. -/
def badFemaleSpouseSquareMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ spouseAngle (femaleSpouseByHusband μ x) ∈
    largeSpouseAngularSquareSet n}

/-- A score-stable mark whose male squared shares exceed the fixed cutoff. -/
def badMaleSpouseSquareMark {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ spouseAngle (fun i ↦ maleSpouseScore x μ i) ∈
    largeSpouseAngularSquareSet n}

/-- On a stable mark, the male exception has exactly the female mass for the
inverse matching. The statistic is invariant under reindexing by spouses. -/
theorem measure_badMaleSpouseSquareMark_eq_female {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n (badMaleSpouseSquareMark μ) =
      continuousScoreLaw n (badFemaleSpouseSquareMark μ.symm) := by
  let S := (spouseAngle : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' largeSpouseAngularSquareSet n
  have hS : MeasurableSet S := (measurableSet_largeSpouseAngularSquareSet n).preimage
    (measurable_spouseAngle n)
  exact scoreStable_maleSpouseStatistic_measure_eq_female μ hS fun v e ↦ by
    change (24 < pittelAngularSquareScore (spouseAngle (v ∘ e))) ↔
      24 < pittelAngularSquareScore (spouseAngle v)
    rw [pittelAngularSquareScore_spouseAngle_comp_equiv]

private theorem size_mul_neg_rpow_shift {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (n : ℝ) * (n : ℝ) ^ (-(p + 1)) = (n : ℝ) ^ (-p) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn', show (1 : ℝ) + -(p + 1) = -p by ring]

private theorem cube_mul_neg_rpow_shift {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (n : ℝ) ^ (3 : ℕ) * (n : ℝ) ^ (-(p + 4)) = (n : ℝ) ^ (-(p + 1)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ = (n : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (-(p + 4)) := by rw [Real.rpow_ofNat]
    _ = _ := by rw [← Real.rpow_add hn', show (3 : ℝ) + -(p + 4) = -(p + 1) by ring]

/-- The expected number of female square-weight exceptions is smaller
than every fixed inverse power of the market size. -/
theorem eventually_sum_measure_badFemaleSpouseSquareMark_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badFemaleSpouseSquareMark μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  have hL : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  have hC : ∀ᶠ n : ℕ in atTop, Real.exp 2 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [eventually_measure_spouseAngularSquare_gt_le (p + 4) (by positivity),
    eventually_sum_stable_smallSpouseTotalLog_le (p + 1), hL, hC,
    eventually_ge_atTop (2 : ℕ)] with n hangle hsmall hnlog hnC hn
  let E (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      spouseAngle (femaleSpouseByHusband μ x) ∈ largeSpouseAngularSquareSet n}
  have hn' : 0 < n := by omega
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hcoef : Real.exp 2 * (n : ℝ) * Real.log n ≤ (n : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ (n : ℝ) * n * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnC hn₀.le) hlog₀
      _ ≤ (n : ℝ) * n * n := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  have hbulk : (∑ μ : Matching n, continuousScoreLaw n (B μ)) ≤ ENNReal.ofReal a := by
    refine (sum_measure_scoreStable_and_femaleSpouseAngle_le hn
      (measurableSet_largeSpouseAngularSquareSet n)).trans ?_
    calc
      _ ≤ ENNReal.ofReal ((n : ℝ) ^ (3 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(p + 4))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) hangle
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), cube_mul_neg_rpow_shift hn' p]
  have hcover (μ : Matching n) : badFemaleSpouseSquareMark μ ⊆ E μ ∪ B μ := by
    intro x hx
    by_cases hY : 2 ≤ femaleSpouseTotal x μ
    · exact Or.inr ⟨hx.1, hY, hx.2⟩
    · exact Or.inl ⟨hx.1, (lt_of_not_ge hY).trans_le hnlog⟩
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (E μ) + continuousScoreLaw n (B μ)) :=
      Finset.sum_le_sum fun μ _ ↦ (measure_mono (hcover μ)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hsmall hbulk
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add ha ha]
      apply ENNReal.ofReal_le_ofReal
      exact (two_mul a).symm.le.trans
        ((mul_le_mul_of_nonneg_right hn₂ ha).trans_eq (size_mul_neg_rpow_shift hn' p))

/-- The same marked expectation bound for male square-weight exceptions. -/
theorem eventually_sum_measure_badMaleSpouseSquareMark_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseSquareMark μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badFemaleSpouseSquareMark_le p hp] with n h
  let e : Matching n ≃ Matching n := ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
  simp_rw [measure_badMaleSpouseSquareMark_eq_female]
  exact (Equiv.sum_comp e (fun μ ↦ continuousScoreLaw n (badFemaleSpouseSquareMark μ))).le.trans h

/-- Both sides' squared shares satisfy the cutoff simultaneously at every stable matching. -/
def goodSpouseSquareWeights (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∀ μ : Matching n, IsStable (profileOfScores x) μ →
    pittelAngularSquareScore (spouseAngle (fun i ↦ maleSpouseScore x μ i)) ≤ 24 ∧
    pittelAngularSquareScore (spouseAngle (femaleSpouseByHusband μ x)) ≤ 24}

/-- A union bound on the marked exceptions gives simultaneous square regularity. -/
theorem eventually_measure_badSpouseSquareWeights_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (goodSpouseSquareWeights n)ᶜ ≤
      ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badMaleSpouseSquareMark_le (p + 1) (by positivity),
    eventually_sum_measure_badFemaleSpouseSquareMark_le (p + 1) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with n hm hf hn
  let M := ⋃ μ : Matching n, badMaleSpouseSquareMark μ
  let F := ⋃ μ : Matching n, badFemaleSpouseSquareMark μ
  let U : Set (ScoreProfile n) := M ∪ F
  have hsub : (goodSpouseSquareWeights n)ᶜ ≤ᵐ[continuousScoreLaw n] U := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    by_contra hnot
    apply hbad
    intro μ hμ
    have hs := (isStable_profileOfScores_iff hx μ).mp hμ
    exact ⟨le_of_not_gt fun h ↦ hnot (Or.inl (mem_iUnion.mpr ⟨μ, hs, h⟩)),
      le_of_not_gt fun h ↦ hnot (Or.inr (mem_iUnion.mpr ⟨μ, hs, h⟩))⟩
  have hn' : 0 < n := by omega
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (n : ℝ) ^ (-(p + 1)) := Real.rpow_nonneg (by positivity) _
  have hM : continuousScoreLaw n M ≤ ENNReal.ofReal ((n : ℝ) ^ (-(p + 1))) :=
    (measure_iUnion_le _).trans (by rwa [tsum_fintype])
  have hF : continuousScoreLaw n F ≤ ENNReal.ofReal ((n : ℝ) ^ (-(p + 1))) :=
    (measure_iUnion_le _).trans (by rwa [tsum_fintype])
  calc
    _ ≤ continuousScoreLaw n M + continuousScoreLaw n F :=
      (measure_mono_ae hsub).trans (measure_union_le M F)
    _ ≤ _ := (add_le_add hM hF).trans (by
      rw [← ENNReal.ofReal_add ha ha]
      apply ENNReal.ofReal_le_ofReal
      exact (two_mul _).symm.le.trans
        ((mul_le_mul_of_nonneg_right hn₂ ha).trans_eq (size_mul_neg_rpow_shift hn' p)))

/-- The actual ENNReal collision weights used by the reverse-permutation count. -/
theorem sum_reverseSpouseWeights_sq_le_of_angularSquare {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (μ : Matching n)
    (hscore : ∀ i, 0 ≤ maleSpouseScore x μ i)
    (h : pittelAngularSquareScore (spouseAngle (fun i ↦ maleSpouseScore x μ i)) ≤ 24) :
    (∑ j, (reverseSpouseWeights μ (splitScorePairs μ x).1 j) ^ 2) ≤
      ENNReal.ofReal (24 / (n : ℝ)) := by
  let d := (splitScorePairs μ x).1
  let v (i : Fin n) := maleSpouseScore x μ i
  let w := spouseAngle v
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hweight (i : Fin n) : reverseSpouseWeights μ d (μ i) = ENNReal.ofReal (w i) := by
    have he (j : Fin n) : (diagonalPairAt d j).1 = v j :=
      congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x j)
    simp only [reverseSpouseWeights, Equiv.symm_apply_apply, he, w, spouseAngle]
  have hw (i : Fin n) : 0 ≤ w i :=
    div_nonneg (hscore i) (Finset.sum_nonneg fun j _ ↦ hscore j)
  have hreal : (∑ i, (w i) ^ 2) ≤ 24 / (n : ℝ) := by
    apply (le_div_iff₀ hn').mpr
    simpa only [pittelAngularSquareScore, mul_comm] using h
  calc
    _ = ∑ i, (reverseSpouseWeights μ d (μ i)) ^ 2 :=
      (Equiv.sum_comp μ (fun j ↦ (reverseSpouseWeights μ d j) ^ 2)).symm
    _ = ∑ i, ENNReal.ofReal ((w i) ^ 2) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hweight, ENNReal.ofReal_pow (hw i)]
    _ = ENNReal.ofReal (∑ i, (w i) ^ 2) :=
      (ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ sq_nonneg _).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The squared female shares in the original indexing, as used by the
forward rotation and forest counts. -/
theorem sum_femaleSpouseShares_sq_le_of_angularSquare {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (μ : Matching n)
    (h : pittelAngularSquareScore (spouseAngle (femaleSpouseByHusband μ x)) ≤ 24) :
    (∑ j, (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2) ≤ 24 / (n : ℝ) := by
  let w := spouseAngle (femaleSpouseByHusband μ x)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have he (i : Fin n) : w i = femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
    change (femaleSpouseByHusband μ x i / ∑ j, femaleSpouseByHusband μ x j) = _
    rw [← femaleSpouseTotal_eq_sum_byHusband]
    rfl
  calc
    _ = ∑ i, (femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ) ^ 2 :=
      (Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)).symm
    _ = ∑ i, (w i) ^ 2 := Finset.sum_congr rfl fun i _ ↦ congrArg (· ^ (2 : ℕ)) (he i).symm
    _ ≤ _ := by
      apply (le_div_iff₀ hn').mpr
      simpa only [pittelAngularSquareScore, mul_comm] using h

/-- Base score and mask regularity together with both square-weight cutoffs. -/
def goodPivotScoreGeometry (n : ℕ) : Set (ScoreProfile n) :=
  goodPivotBaseGeometry n ∩ goodSpouseSquareWeights n

/-- On the simultaneous event, the exact reverse weights meet the square
budget in the filtered moment, and the forward shares meet the same cutoff. -/
theorem spouseSquareWeights_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ j, (reverseSpouseWeights μ (splitScorePairs μ x).1 j) ^ 2) ≤
      ENNReal.ofReal (24 / (n : ℝ)) ∧
    (∑ j, (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2) ≤ 24 / (n : ℝ) := by
  have hsq := hx.2 μ hμ
  have hunit := hx.1.1.2.1
  exact ⟨sum_reverseSpouseWeights_sq_le_of_angularSquare hn μ
    (fun i ↦ (hunit (.inl i) (μ i)).1.le) hsq.1,
    sum_femaleSpouseShares_sq_le_of_angularSquare hn μ hsq.2⟩

/-- The aligned forward and reverse shares have a mixed first moment at
most the common square budget. This is the overlap weight for one label. -/
theorem sum_spouseShares_mul_le_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ i, (femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ) *
      (maleSpouseScore x μ i / maleSpouseTotal x μ)) ≤ 24 / (n : ℝ) := by
  let p (i : Fin n) := femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ
  let r (i : Fin n) := maleSpouseScore x μ i / maleSpouseTotal x μ
  have hp : (∑ i, (p i) ^ 2) ≤ 24 / (n : ℝ) :=
    (Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)).le.trans
      (spouseSquareWeights_of_goodPivotScoreGeometry hn hx μ hμ).2
  have hr : (∑ i, (r i) ^ 2) ≤ 24 / (n : ℝ) := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    apply (le_div_iff₀ hn').mpr
    simpa only [pittelAngularSquareScore, spouseAngle, r, maleSpouseTotal, mul_comm] using
      (hx.2 μ hμ).1
  change (∑ i, p i * r i) ≤ _
  calc
    _ ≤ ∑ i, ((p i) ^ 2 + (r i) ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ ↦ by nlinarith only [sq_nonneg (p i - r i)]
    _ = ((∑ i, (p i) ^ 2) + (∑ i, (r i) ^ 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hp, hr]

/-- One additional forward factor costs at most the normalized male
maximum times the forward square budget. -/
theorem sum_spouseShares_sq_mul_le_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ i, (femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ) ^ 2 *
      (maleSpouseScore x μ i / maleSpouseTotal x μ)) ≤
      (2048 * Real.log n / n) * (24 / (n : ℝ)) := by
  let p (i : Fin n) := femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ
  let B := 2048 * Real.log n / (n : ℝ)
  have hp : (∑ i, (p i) ^ 2) ≤ 24 / (n : ℝ) :=
    (Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)).le.trans
      (spouseSquareWeights_of_goodPivotScoreGeometry hn hx μ hμ).2
  have hgood := hx.1.1.2.2 μ hμ
  have hr (i : Fin n) : maleSpouseScore x μ i / maleSpouseTotal x μ ≤ B :=
    normalizedMaleScore_le_of_spouseProduct hn hgood.1 (hx.1.2.1 μ hμ).2 (hgood.2.2 i)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ i, (p i) ^ 2 * B :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)
    _ = (∑ i, (p i) ^ 2) * B := (Finset.sum_mul ..).symm
    _ ≤ (24 / (n : ℝ)) * B := mul_le_mul_of_nonneg_right hp hB
    _ = _ := mul_comm _ _

/-- The enhanced regularity event still holds with high probability. -/
theorem tendsto_measure_badPivotScoreGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (goodPivotScoreGeometry n)ᶜ) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simp only [Real.rpow_neg_one]
    simpa only [ENNReal.ofReal_zero, one_div] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hs : Tendsto (fun n ↦ continuousScoreLaw n (goodSpouseSquareWeights n)ᶜ)
      atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze' hr (Eventually.of_forall fun _ ↦ zero_le)
      (eventually_measure_badSpouseSquareWeights_le 1 (by norm_num))
  have hmajor := tendsto_measure_badPivotBaseGeometry_zero.add hs
  simp only [add_zero] at hmajor
  refine tendsto_const_nhds.squeeze' hmajor (Eventually.of_forall fun _ ↦ zero_le) ?_
  exact Eventually.of_forall fun n ↦ by
    rw [goodPivotScoreGeometry, compl_inter]
    exact measure_union_le _ _

end LennonPittelFormalization

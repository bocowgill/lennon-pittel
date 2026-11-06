module

public import LennonPittel.CoexposureGoodScores
public import LennonPittel.CoexposureRateComparison
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Volume bounds for spouse-score shells

Nonnegative spouse scores with sum at most a given radius form a simplex.
A lower bound on one coordinate translates that simplex to a smaller one.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace LennonPittelFormalization

/-- Nonnegative arrays whose coordinate sum is at most the given radius. -/
def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}

/-- The simplex cut out by a nonnegative coordinate sum is measurable. -/
theorem measurableSet_scoreSimplex (n : ℕ) (s : ℝ) :
    MeasurableSet (scoreSimplex n s) := by
  unfold scoreSimplex
  rw [ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const)

/-- The volume of a positive-orthant simplex. -/
theorem volume_scoreSimplex (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume (scoreSimplex n s) = ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) := by
  induction n generalizing s with
  | zero =>
    simp [scoreSimplex, hs, volume_pi]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    let S : Set (ℝ × (Fin n → ℝ)) :=
      {a | 0 ≤ a.1 ∧ a.2 ∈ scoreSimplex n (s - a.1)}
    have heq : e ⁻¹' S = scoreSimplex (n + 1) s := by
      ext y
      simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth, Fin.succAbove_zero, Set.mem_preimage, S, scoreSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.sum_univ_succ]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.1⟩, by linarith [h.2.2]⟩,
        fun h ↦ ⟨h.1.1, h.1.2, by linarith [h.2]⟩⟩
    have hS : MeasurableSet S :=
      e.measurableSet_preimage.mp (heq.symm ▸ measurableSet_scoreSimplex _ _)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove _ _
    rw [← heq, he.measure_preimage_emb e.measurableEmbedding]
    change ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S = _
    rw [Measure.prod_apply hS]
    let f (t : ℝ) : ℝ := (s - t) ^ n / (n.factorial : ℝ)
    have hslice (t : ℝ) :
        volume (Prod.mk t ⁻¹' S) = (Icc 0 s).indicator (fun t ↦ ENNReal.ofReal (f t)) t := by
      by_cases ht : t ∈ Icc 0 s
      · rw [indicator_of_mem ht, ← ih (sub_nonneg.mpr ht.2)]
        congr 1
        ext y
        change (0 ≤ t ∧ y ∈ scoreSimplex n (s - t)) ↔ y ∈ scoreSimplex n (s - t)
        exact and_iff_right ht.1
      · rw [indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          change 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s - t at hy
          have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ ↦ hy.2.1 i
          exact ht ⟨hy.1, by linarith [hy.2.2]⟩
        rw [hempty, measure_empty]
    rw [lintegral_congr hslice, lintegral_indicator measurableSet_Icc]
    have hfi : IntegrableOn f (Icc 0 s) := (by fun_prop : Continuous f).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hfi
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ by
        dsimp only [f]
        exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (Nat.cast_nonneg _))]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    congr 1
    dsimp only [f]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) s, sub_self,
      sub_zero, integral_pow, zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]

/-- Translating one coordinate reduces the radius by its lower bound. -/
theorem volume_scoreSimplex_coordinate_lower_bound (n : ℕ) (i : Fin n) {s a : ℝ}
    (ha : 0 ≤ a) (has : a ≤ s) :
    volume (scoreSimplex n s ∩ {y | a ≤ y i}) =
      ENNReal.ofReal ((s - a) ^ n / (n.factorial : ℝ)) := by
  have htrans : (fun y : Fin n → ℝ ↦ y + Pi.single i a) ⁻¹'
      (scoreSimplex n s ∩ {y | a ≤ y i}) = scoreSimplex n (s - a) := by
    ext y
    simp only [mem_preimage, mem_inter_iff, scoreSimplex, mem_ofPred_eq, Pi.add_apply,
      Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true, Pi.single_eq_same]
    constructor
    · rintro ⟨⟨hy, hsum⟩, hi⟩
      refine ⟨fun j ↦ ?_, by linarith⟩
      by_cases h : j = i
      · subst j
        linarith
      · simpa only [Pi.single_eq_of_ne h, add_zero] using hy j
    · rintro ⟨hy, hsum⟩
      refine ⟨⟨fun j ↦ add_nonneg (hy j) ?_, by linarith⟩, by linarith [hy i]⟩
      by_cases h : j = i
      · subst j
        simpa only [Pi.single_eq_same] using ha
      · rw [Pi.single_eq_of_ne h]
  let v : Fin n → ℝ := Pi.single i a
  have hmeasure := (measurePreserving_add_right (volume : Measure (Fin n → ℝ))
    v).measure_preimage_emb (measurableEmbedding_addRight v)
      (scoreSimplex n s ∩ {y | a ≤ y i})
  change volume ((fun y : Fin n → ℝ ↦ y + Pi.single i a) ⁻¹'
      (scoreSimplex n s ∩ {y | a ≤ y i})) = _ at hmeasure
  rw [htrans, volume_scoreSimplex n (sub_nonneg.mpr has)] at hmeasure
  exact hmeasure.symm

/-- A large relative coordinate in a positive-score shell costs simplex volume. -/
theorem volume_scoreSimplex_shell_large_coordinate_le (n : ℕ) (i : Fin n)
    {l u a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hau : a * l ≤ u) :
    volume {y : Fin n → ℝ | y ∈ scoreSimplex n u ∧ l ≤ ∑ j, y j ∧
      a < y i / (∑ j, y j)} ≤ ENNReal.ofReal ((u - a * l) ^ n / (n.factorial : ℝ)) := by
  rw [← volume_scoreSimplex_coordinate_lower_bound n i (mul_nonneg ha hl.le) hau]
  apply measure_mono
  intro y hy
  exact ⟨hy.1, (mul_le_mul_of_nonneg_left hy.2.1 ha).trans
    ((lt_div_iff₀ (hl.trans_le hy.2.1)).mp hy.2.2).le⟩

/-- The exposure weight of a good mark, and zero for a mark that fails a cutoff. -/
noncomputable def goodScoreMarkedWeight (n : ℕ) :
    ScoreProfile n × Matching n → ℝ≥0∞ :=
  {z | GoodSpouseScores z.1 z.2}.indicator
    fun z ↦ (2 : ℝ≥0∞) ^ numExposedRotations (profileOfScores z.1) z.2

/-- The marked exposure weight is measurable on the score space times the finite mark space. -/
theorem measurable_goodScoreMarkedWeight (n : ℕ) : Measurable (goodScoreMarkedWeight n) := by
  apply measurable_from_prod_countable_left
  intro μ
  have hweight : Measurable (fun p : Profile n ↦ (2 : ℝ≥0∞) ^ numExposedRotations p μ) :=
    fun _ _ ↦ MeasurableSpace.measurableSet_top
  exact (hweight.comp (measurable_profileOfScores n)).indicator
    (measurableSet_goodSpouseScores μ)

open Classical in
private theorem coexposureWeight_eq_sum_ite {n : ℕ} (p : Profile n) :
    coexposureWeight p = ∑ μ : Matching n,
      if IsStable p μ then 2 ^ numExposedRotations p μ else 0 := by
  classical
  unfold coexposureWeight
  calc
    _ = ∑ μ ∈ Finset.univ.filter (IsStable p), 2 ^ numExposedRotations p μ :=
      (Finset.sum_subtype (Finset.univ.filter (IsStable p)) (by simp)
        (fun μ ↦ (2 : ℕ) ^ numExposedRotations p μ)).symm
    _ = _ := Finset.sum_filter _ _

/-- The profile weight restricted to the all-good event is bounded by summing only
over good stable marks, even if other matchings fail a cutoff. -/
theorem lintegral_goodScoreCoexposureWeight_le_marked (n : ℕ) :
    (∫⁻ x, scoreCoexposureWeight n (goodCoexposureScores n) x ∂(continuousScoreLaw n)) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) *
        (∫⁻ z, goodScoreMarkedWeight n z ∂(scoreMarkedLaw n)) := by
  classical
  rw [continuous_mark_counting_identity n (measurable_goodScoreMarkedWeight n)]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ goodCoexposureScores n
  · rw [scoreCoexposureWeight, Set.indicator_of_mem hx, coexposureWeight_eq_sum_ite]
    push_cast
    apply Finset.sum_le_sum
    intro μ _
    by_cases hm : IsStable (profileOfScores x) μ
    · have hs := (isStable_profileOfScores_iff hx.1 μ).mp hm
      have hg := hx.2.2 μ hm
      simp [hm, scoreMarkEvent, goodScoreMarkedWeight, hs, hg]
    · simp [hm]
  · simp [scoreCoexposureWeight, Set.indicator_of_notMem hx]

private theorem sum_scoreStableMass_eq_mean (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ}) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  calc
    _ = ∑ μ : Matching n, ∫⁻ x, {x | IsScoreStable x μ}.indicator 1 x
        ∂(continuousScoreLaw n) := by
      simp_rw [lintegral_indicator_one (measurableSet_isScoreStable _)]
    _ = ∫⁻ x, ∑ μ : Matching n, (scoreMarkEvent n).indicator 1 (x, μ)
        ∂(continuousScoreLaw n) :=
      (lintegral_finsetSum _ fun μ _ ↦
        measurable_const.indicator (measurableSet_isScoreStable μ)).symm
    _ = _ := markedNormalizer_scoreMarkEvent n

/-- Summing fixed-matching bounds gives a bound on the all-good profile weight. -/
theorem lintegral_goodScoreCoexposureWeight_le_of_fixed_moment {n : ℕ} {L : ℝ≥0∞}
    (h : ∀ μ : Matching n, (∫⁻ x in {x | IsScoreStable x μ ∧ GoodSpouseScores x μ},
      (2 : ℝ≥0∞) ^ numExposedRotations (profileOfScores x) μ ∂(continuousScoreLaw n)) ≤
        L * continuousScoreLaw n {x | IsScoreStable x μ}) :
    (∫⁻ x, scoreCoexposureWeight n (goodCoexposureScores n) x ∂(continuousScoreLaw n)) ≤
      L * ENNReal.ofReal (expectedNumStableMatchings n) := by
  let f (μ : Matching n) (x : ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ GoodSpouseScores x μ}.indicator
      (fun y ↦ (2 : ℝ≥0∞) ^ numExposedRotations (profileOfScores y) μ) x
  have hf (μ : Matching n) : Measurable (f μ) := by
    have hp : Measurable (fun p : Profile n ↦ (2 : ℝ≥0∞) ^ numExposedRotations p μ) :=
      fun _ _ ↦ MeasurableSpace.measurableSet_top
    exact (hp.comp (measurable_profileOfScores n)).indicator
      ((measurableSet_isScoreStable μ).inter (measurableSet_goodSpouseScores μ))
  have hterm (μ : Matching n) (x : ScoreProfile n) :
      (scoreMarkEvent n).indicator (goodScoreMarkedWeight n) (x, μ) = f μ x := by
    by_cases hs : IsScoreStable x μ <;> by_cases hg : GoodSpouseScores x μ <;>
      simp [scoreMarkEvent, goodScoreMarkedWeight, f, hs, hg]
  calc
    _ ≤ ENNReal.ofReal (expectedNumStableMatchings n) *
        (∫⁻ z, goodScoreMarkedWeight n z ∂(scoreMarkedLaw n)) :=
      lintegral_goodScoreCoexposureWeight_le_marked n
    _ = ∫⁻ x, ∑ μ : Matching n, f μ x ∂(continuousScoreLaw n) := by
      simp only [continuous_mark_counting_identity n (measurable_goodScoreMarkedWeight n), hterm]
    _ = ∑ μ : Matching n, ∫⁻ x, f μ x ∂(continuousScoreLaw n) :=
      lintegral_finsetSum _ fun μ _ ↦ hf μ
    _ ≤ ∑ μ : Matching n, L * continuousScoreLaw n {x | IsScoreStable x μ} := by
      apply Finset.sum_le_sum
      intro μ _
      exact (lintegral_indicator
        ((measurableSet_isScoreStable μ).inter (measurableSet_goodSpouseScores μ)) _).trans_le (h μ)
    _ = _ := by rw [← Finset.mul_sum, sum_scoreStableMass_eq_mean]

/-- The exact score-space reduction to marked bad-score and moment estimates. -/
theorem tendsto_uniformProfile_coexposure_zero_of_marked_bounds
    {a C r : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hr : r < 4 / 7)
    (hmean : Tendsto
      (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n)) atTop (𝓝 a))
    (hbad : Tendsto (fun n ↦ ENNReal.ofReal (expectedNumStableMatchings n) *
      scoreMarkedLaw n (badSpouseMark n)) atTop (𝓝 0))
    (hmoment : ∀ᶠ n : ℕ in atTop, (∫⁻ z, goodScoreMarkedWeight n z ∂(scoreMarkedLaw n)) ≤
      ENNReal.ofReal (C * (n : ℝ) ^ r)) :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | HasCoexposedRotations p (coexposedRotationThreshold reciprocalLogTolerance n)})
      atTop (𝓝 0) := by
  apply tendsto_uniformProfile_coexposure_zero_of_weight_growth goodCoexposureScores
    measurableSet_goodCoexposureScores ha hC hr hmean
  · exact tendsto_const_nhds.squeeze' hbad (Eventually.of_forall fun _ ↦ zero_le)
      (Eventually.of_forall measure_badCoexposureScores_le_marked)
  · filter_upwards [hmoment] with n hn
    refine (lintegral_goodScoreCoexposureWeight_le_marked n).trans ?_
    have hmean_nonneg : 0 ≤ expectedNumStableMatchings n :=
      integral_nonneg fun _ ↦ Nat.cast_nonneg _
    rw [mul_comm (C * (n : ℝ) ^ r), ENNReal.ofReal_mul hmean_nonneg]
    gcongr

end LennonPittelFormalization

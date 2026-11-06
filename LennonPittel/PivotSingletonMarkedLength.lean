module

public import LennonPittel.PivotSingletonLength
public import LennonPittel.SingletonAnchorCounting
public import LennonPittel.SingletonDiagonalExceptions

/-!
# Marked expectations of sole forward lengths

The singleton-anchor correspondence transfers a length weight to one stable
mark per rotation. A diagonal exception is therefore charged only once per
mark, irrespective of the number of lengths or permutations under study.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The score-stable mark has the tested diagonal and one exposed rotation
of the given length. -/
def scoreStableSingletonLengthEvent {n : ℕ} (μ : Matching n)
    (C : Set (DiagonalScorePairs n)) (k : ℕ) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧
    HasSoleForwardExposedLength (profileOfScores x) μ k}

theorem measurableSet_scoreStableSingletonLengthEvent {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) (k : ℕ) :
    MeasurableSet (scoreStableSingletonLengthEvent μ C k) :=
  (measurableSet_isScoreStable μ).inter
    (((measurable_fst.comp (splitScorePairs μ).measurable) hC).inter
      (measurable_profileOfScores n (MeasurableSet.of_discrete :
        MeasurableSet {p : Profile n | HasSoleForwardExposedLength p μ k})))

/-- The event that the diagonal of a score-stable mark lies outside the cutoff. -/
def badSingletonLengthDiagonalEvent {n : ℕ} (μ : Matching n)
    (C : Set (DiagonalScorePairs n)) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∉ C}

theorem measurableSet_badSingletonLengthDiagonalEvent {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) :
    MeasurableSet (badSingletonLengthDiagonalEvent μ C) :=
  (measurableSet_isScoreStable μ).inter
    ((measurable_fst.comp (splitScorePairs μ).measurable) hC.compl)

open scoped Classical in
private theorem sum_singletonAnchor_indicators_le {n : ℕ} (μ : Matching n)
    (C : Set (DiagonalScorePairs n)) (g : ℕ → ℝ≥0∞) {B : ℝ≥0∞}
    (hB : ∀ k ∈ Finset.Icc 2 n, g k ≤ B) (x : ScoreProfile n) :
    (∑ σ : Matching n, (scoreStableSingletonAnchorEvent μ σ).indicator
      (fun _ ↦ g σ.support.card) x) ≤
      (∑ k ∈ Finset.Icc 2 n, (scoreStableSingletonLengthEvent μ C k).indicator
        (fun _ ↦ g k) x) + (badSingletonLengthDiagonalEvent μ C).indicator (fun _ ↦ B) x := by
  by_cases he : ∃ σ : Matching n, x ∈ scoreStableSingletonAnchorEvent μ σ
  · obtain ⟨σ, hx⟩ := he
    have hsum : (∑ ρ : Matching n, (scoreStableSingletonAnchorEvent μ ρ).indicator
        (fun _ ↦ g ρ.support.card) x) = g σ.support.card := by
      rw [Finset.sum_eq_single σ]
      · exact indicator_of_mem hx _
      · intro ρ _ hne
        exact indicator_of_notMem (fun h ↦ hne (hx.2.2 ρ h.2.1)) _
      · simp
    rw [hsum]
    have hk : σ.support.card ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr
      ⟨hx.2.1.isCycle.two_le_card_support, (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)⟩
    by_cases hd : (splitScorePairs μ x).1 ∈ C
    · have hmem : x ∈ scoreStableSingletonLengthEvent μ C σ.support.card :=
        ⟨hx.1, hd, σ, hx.2, rfl⟩
      have hle : g σ.support.card ≤
          ∑ k ∈ Finset.Icc 2 n, (scoreStableSingletonLengthEvent μ C k).indicator
            (fun _ ↦ g k) x := by
        calc
          _ = (scoreStableSingletonLengthEvent μ C σ.support.card).indicator
              (fun _ ↦ g σ.support.card) x := (indicator_of_mem hmem _).symm
          _ ≤ _ := Finset.single_le_sum
            (f := fun k ↦ (scoreStableSingletonLengthEvent μ C k).indicator (fun _ ↦ g k) x)
            (fun _ _ ↦ zero_le) hk
      exact hle.trans (le_add_of_nonneg_right zero_le)
    · rw [indicator_of_mem (show x ∈ badSingletonLengthDiagonalEvent μ C from ⟨hx.1, hd⟩)]
      exact (hB _ hk).trans (le_add_of_nonneg_left zero_le)
  · have hz (σ : Matching n) : (scoreStableSingletonAnchorEvent μ σ).indicator
        (fun _ ↦ g σ.support.card) x = 0 :=
      indicator_of_notMem (fun h ↦ he ⟨σ, h⟩) _
    simp only [hz, Finset.sum_const_zero, zero_le]

/-- A uniform conditional length bound controls all nonnegative length
weights; exceptional stable diagonals are charged only at the weight cap. -/
theorem lintegral_profileSingletonAnchorLengthWeight_le_of_lengthEvents (n : ℕ)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) (g : ℕ → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : ∀ k ∈ Finset.Icc 2 n, g k ≤ B)
    {a : ℕ → ℝ≥0∞}
    (hgood : ∀ (μ : Matching n) k, k ∈ Finset.Icc 2 n →
      continuousScoreLaw n (scoreStableSingletonLengthEvent μ C k) ≤
        continuousScoreLaw n {x | IsScoreStable x μ} * a k) :
    (∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * (∑ k ∈ Finset.Icc 2 n, g k * a k) +
        B * ∑ μ : Matching n, continuousScoreLaw n (badSingletonLengthDiagonalEvent μ C) := by
  classical
  rw [lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent]
  let m (μ : Matching n) := continuousScoreLaw n {x | IsScoreStable x μ}
  let e (μ : Matching n) := continuousScoreLaw n (badSingletonLengthDiagonalEvent μ C)
  have hm (μ : Matching n) :
      (∑ σ : Matching n, g σ.support.card *
        continuousScoreLaw n (scoreStableSingletonAnchorEvent μ σ)) ≤
        m μ * (∑ k ∈ Finset.Icc 2 n, g k * a k) + B * e μ := by
    let f (σ : Matching n) := (scoreStableSingletonAnchorEvent μ σ).indicator
      (fun _ ↦ g σ.support.card)
    let q (k : ℕ) := (scoreStableSingletonLengthEvent μ C k).indicator (fun _ ↦ g k)
    let v := (badSingletonLengthDiagonalEvent μ C).indicator (fun _ ↦ B)
    have hf (σ : Matching n) : Measurable (f σ) :=
      measurable_const.indicator (measurableSet_scoreStableSingletonAnchorEvent μ σ)
    have hq (k : ℕ) : Measurable (q k) :=
      measurable_const.indicator (measurableSet_scoreStableSingletonLengthEvent μ hC k)
    calc
      _ = ∫⁻ x, ∑ σ : Matching n, f σ x ∂continuousScoreLaw n := by
        rw [lintegral_finsetSum _ (fun σ _ ↦ hf σ)]
        exact Finset.sum_congr rfl fun σ _ ↦
          (lintegral_indicator_const (measurableSet_scoreStableSingletonAnchorEvent μ σ) _).symm
      _ ≤ ∫⁻ x, (∑ k ∈ Finset.Icc 2 n, q k x) + v x ∂continuousScoreLaw n :=
        lintegral_mono (sum_singletonAnchor_indicators_le μ C g hB)
      _ = (∑ k ∈ Finset.Icc 2 n, g k *
          continuousScoreLaw n (scoreStableSingletonLengthEvent μ C k)) + B * e μ := by
        rw [lintegral_add_left (Finset.measurable_sum _ fun k _ ↦ hq k),
          lintegral_finsetSum _ (fun k _ ↦ hq k)]
        congr 1
        · exact Finset.sum_congr rfl fun k _ ↦
            lintegral_indicator_const (measurableSet_scoreStableSingletonLengthEvent μ hC k) _
        · exact lintegral_indicator_const (measurableSet_badSingletonLengthDiagonalEvent μ hC) _
      _ ≤ _ := by
        rw [Finset.mul_sum]
        refine add_le_add (Finset.sum_le_sum fun k hk ↦ ?_) le_rfl
        exact (mul_le_mul_right (hgood μ k hk) _).trans_eq (by ac_rfl)
  refine (Finset.sum_le_sum fun μ _ ↦ hm μ).trans_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  unfold m e
  rw [sum_measure_scoreStable_eq_expected]

/-- The uniform forest-error budget on the local singleton score geometry. -/
noncomputable def singletonLengthBudget (n : ℕ) : ℝ :=
  3 * (n : ℝ) ^ (-3 / 4 : ℝ) + 24 / (n : ℝ)

/-- The per-length upper bound used by the marked transfer. -/
noncomputable def singletonLengthEnvelope (n k : ℕ) : ℝ :=
  Real.exp 5 * singletonLengthGaussian n k * (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ))

theorem singletonLengthEnvelope_nonneg (n k : ℕ) : 0 ≤ singletonLengthEnvelope n k := by
  unfold singletonLengthEnvelope singletonLengthBudget singletonLengthGaussian
  positivity

/-- The uniform conditional length bound transfers to stable-mark mass
on the measurable diagonal cutoff. -/
theorem eventually_measure_scoreStableSingletonLengthEvent_le :
    ∀ᶠ n : ℕ in atTop, ∀ (μ : Matching n) k, k ∈ Finset.Icc 2 n →
      continuousScoreLaw n (scoreStableSingletonLengthEvent μ (singletonLengthGoodDiagonal n) k) ≤
        continuousScoreLaw n {x | IsScoreStable x μ} *
          ENNReal.ofReal (singletonLengthEnvelope n k) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds,
    eventually_hasForwardReferenceDeficit_of_singletonLengthGoodDiagonal] with n hp hdef
  obtain ⟨hn, hη₀, hη, hA, hB, hδ⟩ := hp
  intro μ k hk
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  refine measure_scoreStable_diagonal_rankEvent_le μ
    (measurableSet_singletonLengthGoodDiagonal n) (fun _ h ↦ ⟨h.2.1, h.2.2.1⟩)
    {p | HasSoleForwardExposedLength p μ k} ?_
  filter_upwards [ae_diagonal_measureReal_soleForwardExposedLength_le hn μ hη₀ hη hA hB hδ]
    with d hd
  intro h
  have hsq : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) := h.2.2.2.2.1
  have hk₀ := (Finset.mem_Icc.mp hk).1
  have hk₁ := (Finset.mem_Icc.mp hk).2
  refine (hd h.1 h.2.1 h.2.2.1 _ (hdef d h) k hk₀ hk₁).trans ?_
  unfold singletonLengthEnvelope singletonLengthBudget singletonLengthGaussian
  gcongr

/-- The marked transfer for an arbitrary nonnegative real length weight,
with the exceptional score mass bounded at its cap. -/
theorem eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian :
    ∀ᶠ n : ℕ in atTop, ∀ (g : ℕ → ℝ) (B : ℝ),
      (∀ k, 0 ≤ g k) → (∀ k ∈ Finset.Icc 2 n, g k ≤ B) →
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) *
          ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) +
          ENNReal.ofReal B * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_measure_scoreStableSingletonLengthEvent_le,
    eventually_sum_measure_badSingletonLengthDiagonal_le] with n hgood hbad
  intro g B hg hB
  have hb := lintegral_profileSingletonAnchorLengthWeight_le_of_lengthEvents n
    (measurableSet_singletonLengthGoodDiagonal n) (fun k ↦ ENNReal.ofReal (g k))
    (fun k hk ↦ ENNReal.ofReal_le_ofReal (hB k hk)) hgood
  refine hb.trans ?_
  have hsum : (∑ k ∈ Finset.Icc 2 n, ENNReal.ofReal (g k) *
      ENNReal.ofReal (singletonLengthEnvelope n k)) =
      ENNReal.ofReal (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) := by
    simp_rw [← ENNReal.ofReal_mul (hg _)]
    exact (ENNReal.ofReal_sum_of_nonneg fun k _ ↦
      mul_nonneg (hg k) (singletonLengthEnvelope_nonneg n k)).symm
  rw [hsum]
  exact add_le_add le_rfl (mul_le_mul_right hbad _)

theorem singletonLengthBudget_le {n : ℕ} (hn : 0 < n) :
    singletonLengthBudget n ≤ 27 / (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (3 / 4 : ℝ) ≤ n := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn₁ (show (3 / 4 : ℝ) ≤ 1 by norm_num)
  calc
    _ = 3 / (n : ℝ) ^ (3 / 4 : ℝ) + 24 / (n : ℝ) := by
      unfold singletonLengthBudget
      rw [show (-3 / 4 : ℝ) = -(3 / 4) by ring, Real.rpow_neg hn₀.le]
      simp only [div_eq_mul_inv]
    _ ≤ 3 / (n : ℝ) ^ (3 / 4 : ℝ) + 24 / (n : ℝ) ^ (3 / 4 : ℝ) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp)
    _ = _ := by ring

/-- Under the uniform preference law, the expected number of realized
rotations has the square-root scale times the logarithm. -/
theorem eventually_lintegral_profileSingletonAnchorCount_le :
    ∀ᶠ n : ℕ in atTop,
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal ((Real.exp 5 * (108 + 48 * Real.exp 4)) *
          Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian,
    eventually_expectedNumStableMatchings_le_sizeLog, eventually_gt_atTop (0 : ℕ)]
    with n h hmean hn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  let C := Real.exp 5 * (108 + 48 * Real.exp 4)
  have hsum : (∑ k ∈ Finset.Icc 2 n, singletonLengthEnvelope n k) ≤ C / Real.sqrt n := by
    have h₀ : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
    calc
      _ = Real.exp 5 * ∑ k ∈ Finset.Icc 2 n, singletonLengthGaussian n k *
          (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ)) := by
        rw [Finset.mul_sum]
        simp only [singletonLengthEnvelope, mul_assoc]
      _ ≤ Real.exp 5 * ((4 * 27 + 2 * Real.exp 4 * 24) / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left
          (singletonLengthGaussian_countSum_le_inv_sqrt hn h₀ (by positivity)
            (singletonLengthBudget_le hn) le_rfl) (Real.exp_pos _).le
      _ = _ := by unfold C; ring
  have h' := h (fun _ ↦ 1) 1 (fun _ ↦ zero_le_one) (fun _ _ ↦ le_rfl)
  simp only [ENNReal.ofReal_one, one_mul] at h'
  refine h'.trans ?_
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) * Real.log n) * ENNReal.ofReal (C / Real.sqrt n) +
        ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) :=
      add_le_add
        (mul_le_mul' (ENNReal.ofReal_le_ofReal hmean) (ENNReal.ofReal_le_ofReal hsum)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hn₀.le hl),
        ← ENNReal.ofReal_add (by dsimp [C]; positivity) (by positivity)]
      congr 1
      have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn₀.le
      have hquot : (n : ℝ) / Real.sqrt n = Real.sqrt n :=
        (div_eq_iff (Real.sqrt_pos.mpr hn₀).ne').mpr (by simpa only [pow_two] using hs.symm)
      calc
        _ = C * ((n : ℝ) / Real.sqrt n) * Real.log n + (n : ℝ) ^ (-3 : ℝ) := by ring
        _ = _ := by rw [hquot]

open scoped Classical in
/-- The expected total length of rotations longer than the square-root
cutoff is bounded by a term decaying in the cutoff and a vanishing error. -/
theorem eventually_lintegral_profileSingletonAnchorLongLength_le :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦
        ENNReal.ofReal (if a * Real.sqrt (n : ℝ) < (k : ℝ) then k else 0))
        ∂(uniformProfile n).toMeasure) ≤
        ENNReal.ofReal ((n : ℝ) * Real.log n) *
          ENNReal.ofReal (Real.exp 5 *
            ((54 * Real.exp 4) / Real.sqrt (Real.sqrt (n : ℝ)) +
              144 * Real.exp 16 * Real.exp (-a))) +
          ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) := by
  filter_upwards [eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian,
    eventually_expectedNumStableMatchings_le_sizeLog, eventually_gt_atTop (0 : ℕ)]
    with n h hmean hn
  intro a
  let g (k : ℕ) : ℝ := if a * Real.sqrt (n : ℝ) < (k : ℝ) then k else 0
  have hg (k : ℕ) : 0 ≤ g k := by unfold g; split <;> positivity
  have hcap (k : ℕ) (hk : k ∈ Finset.Icc 2 n) : g k ≤ (n : ℝ) := by
    unfold g
    split
    · exact_mod_cast (Finset.mem_Icc.mp hk).2
    · positivity
  have h₀ : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
  have hsum : (∑ k ∈ Finset.Icc 2 n, g k * singletonLengthEnvelope n k) ≤
      Real.exp 5 * ((54 * Real.exp 4) / Real.sqrt (Real.sqrt (n : ℝ)) +
        144 * Real.exp 16 * Real.exp (-a)) := by
    calc
      _ = Real.exp 5 * ∑ k ∈ (Finset.Icc 2 n).filter (fun k : ℕ ↦
          a * Real.sqrt (n : ℝ) < (k : ℝ)), (k : ℝ) * singletonLengthGaussian n k *
            (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ)) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        by_cases hk : a * Real.sqrt (n : ℝ) < (k : ℝ)
        · simp only [g, singletonLengthEnvelope, ite_eq_left hk]
          ring
        · simp [g, hk]
      _ ≤ Real.exp 5 * ((2 * Real.exp 4 * 27) / Real.sqrt (Real.sqrt (n : ℝ)) +
          6 * Real.exp 16 * Real.exp (-a) * 24) :=
        mul_le_mul_of_nonneg_left
          (singletonLengthGaussian_longSum_le_of_budgets hn a h₀ (by positivity)
            (singletonLengthBudget_le hn) le_rfl) (Real.exp_pos _).le
      _ = _ := by ring
  have he : ENNReal.ofReal (n : ℝ) * ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) =
      ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (Nat.cast_pos.mpr hn)]; norm_num
  refine (h g n hg hcap).trans ?_
  rw [he]
  exact add_le_add
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hmean) (ENNReal.ofReal_le_ofReal hsum)) le_rfl

end LennonPittelFormalization

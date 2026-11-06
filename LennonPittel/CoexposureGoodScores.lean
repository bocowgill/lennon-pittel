module

public import LennonPittel.ContinuousScoreBridge
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Good spouse scores for the co-exposure estimate

The three cutoffs concern the women's total spouse score, their normalized
spouse scores, and the men's spouse scores. We require these cutoffs at every
stable matching, while restricting the sampled scores to tie-free rows in
the open unit interval.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal LennonPittelFormalization

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The score that a man gives to his partner under the matching. -/
def maleSpouseScore (x : ScoreProfile n) (μ : Matching n) (i : Fin n) : ℝ :=
  x (.inl i) (μ i)

/-- The score that a woman gives to her partner under the matching. -/
def femaleSpouseScore (x : ScoreProfile n) (μ : Matching n) (j : Fin n) : ℝ :=
  x (.inr j) (μ.symm j)

/-- The sum of the women's spouse scores. -/
def femaleSpouseTotal (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, femaleSpouseScore x μ j

/-- The three cutoffs used in the fixed-matching score bound. -/
def GoodSpouseScores (x : ScoreProfile n) (μ : Matching n) : Prop :=
  2 ≤ femaleSpouseTotal x μ ∧
    (∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 12 * Real.log n / n) ∧
    (∀ i, maleSpouseScore x μ i ≤ 8 * Real.log n / (femaleSpouseTotal x μ - 1))

/-- Tie-free open-unit score arrays with good spouse scores at all stable matchings. -/
def goodCoexposureScores (n : ℕ) : Set (ScoreProfile n) :=
  {x | (∀ r, Function.Injective (x r)) ∧ (∀ r i, x r i ∈ Ioo (0 : ℝ) 1) ∧
    ∀ μ, IsStable (profileOfScores x) μ → GoodSpouseScores x μ}

/-- A fixed matching is score-stable and violates at least one cutoff. -/
def badStableSpouseScores (n : ℕ) (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ ¬GoodSpouseScores x μ}

private theorem measurable_scoreCoordinate (r : Fin n ⊕ Fin n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ x r i) :=
  (measurable_pi_apply i).comp (measurable_pi_apply r)

theorem measurable_maleSpouseScore (μ : Matching n) (i : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ maleSpouseScore x μ i) :=
  measurable_scoreCoordinate (.inl i) (μ i)

theorem measurable_femaleSpouseScore (μ : Matching n) (j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseScore x μ j) :=
  measurable_scoreCoordinate (.inr j) (μ.symm j)

theorem measurable_femaleSpouseTotal (μ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ femaleSpouseTotal x μ) :=
  Finset.measurable_sum _ (fun j _ ↦ measurable_femaleSpouseScore μ j)

theorem measurableSet_goodSpouseScores (μ : Matching n) :
    MeasurableSet {x : ScoreProfile n | GoodSpouseScores x μ} := by
  unfold GoodSpouseScores
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_le measurable_const (measurable_femaleSpouseTotal μ)).inter
    ((MeasurableSet.iInter fun j ↦ measurableSet_le
      ((measurable_femaleSpouseScore μ j).div (measurable_femaleSpouseTotal μ))
      measurable_const).inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le (measurable_maleSpouseScore μ i)
        (measurable_const.div ((measurable_femaleSpouseTotal μ).sub measurable_const))))

theorem measurableSet_badStableSpouseScores (n : ℕ) (μ : Matching n) :
    MeasurableSet (badStableSpouseScores n μ) :=
  (measurableSet_isScoreStable μ).inter (measurableSet_goodSpouseScores μ).compl

private theorem measurableSet_tieFreeScores (n : ℕ) :
    MeasurableSet {x : ScoreProfile n | ∀ r, Function.Injective (x r)} := by
  simp only [Function.Injective, Set.ofPred_forall]
  refine MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun i ↦
    MeasurableSet.iInter fun j ↦ ?_
  by_cases hij : i = j
  · simp [hij]
  · simpa only [hij, imp_false, Set.compl_ofPred] using
      (measurableSet_eq_fun (measurable_scoreCoordinate r i)
        (measurable_scoreCoordinate r j)).compl

theorem measurableSet_goodCoexposureScores (n : ℕ) :
    MeasurableSet (goodCoexposureScores n) := by
  unfold goodCoexposureScores
  simp only [Set.ofPred_and]
  refine (measurableSet_tieFreeScores n).inter (MeasurableSet.inter ?_ ?_)
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun i ↦
      (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)).preimage
        (measurable_scoreCoordinate r i)
  · rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun μ ↦ ?_
    have hStable : MeasurableSet {x : ScoreProfile n | IsStable (profileOfScores x) μ} :=
      (MeasurableSpace.measurableSet_top :
        MeasurableSet {p : Profile n | IsStable p μ}).preimage (measurable_profileOfScores n)
    convert hStable.compl.union (measurableSet_goodSpouseScores μ) using 1
    ext x
    exact imp_iff_not_or

/-- Every coordinate of the iid score array lies in the open unit interval almost surely. -/
theorem ae_unitOpen_scores (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r i, x r i ∈ Ioo (0 : ℝ) 1 := by
  have hopen : ∀ᵐ t ∂unitScoreLaw, t ∈ Ioo (0 : ℝ) 1 := by
    rw [unitScoreLaw, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact ae_all_iff.2 fun r ↦ ae_all_iff.2 fun i ↦
    (Measure.tendsto_eval_ae_ae (i := r)
      (μ := fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw)).eventually
      ((Measure.tendsto_eval_ae_ae (i := i) (μ := fun _ : Fin n ↦ unitScoreLaw)).eventually hopen)

/-- The bad global event agrees almost everywhere with a union over fixed bad stable marks. -/
theorem badCoexposureScores_ae_eq_iUnion (n : ℕ) :
    (goodCoexposureScores n)ᶜ =ᵐ[continuousScoreLaw n]
      ⋃ μ : Matching n, badStableSpouseScores n μ := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x hrow hopen
  apply propext
  constructor
  · intro hbad
    have hfail : ¬∀ μ, IsStable (profileOfScores x) μ → GoodSpouseScores x μ :=
      fun hgood ↦ hbad ⟨hrow, hopen, hgood⟩
    obtain ⟨μ, hμ⟩ := not_forall.mp hfail
    obtain ⟨hs, hb⟩ := Classical.not_imp.mp hμ
    exact Set.mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hrow μ).mp hs, hb⟩
  · intro hbad hgood
    obtain ⟨μ, hs, hb⟩ := Set.mem_iUnion.mp hbad
    exact hb (hgood.2.2 μ ((isStable_profileOfScores_iff hrow μ).mpr hs))

/-- Count exceptional score arrays by summing the bad probability of each fixed stable mark. -/
theorem measure_badCoexposureScores_le_sum (n : ℕ) :
    continuousScoreLaw n (goodCoexposureScores n)ᶜ ≤
      ∑ μ : Matching n, continuousScoreLaw n (badStableSpouseScores n μ) :=
  (measure_congr (badCoexposureScores_ae_eq_iUnion n)).le.trans
    (measure_iUnion_fintype_le _ _)

/-- The marked matching's spouse scores fail a cutoff. -/
def badSpouseMark (n : ℕ) : Set (ScoreProfile n × Matching n) :=
  {z | ¬GoodSpouseScores z.1 z.2}

theorem measurableSet_badSpouseMark (n : ℕ) : MeasurableSet (badSpouseMark n) :=
  (measurable_from_prod_countable_left fun μ ↦
    measurableSet_setOfPred.mp (measurableSet_goodSpouseScores μ).compl).setOf

/-- The expected number of bad stable matchings is the mean stable count times the
probability of bad scores under the stable-mark law. -/
theorem sum_measure_badStableSpouseScores_eq_marked (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n (badStableSpouseScores n μ)) =
      ENNReal.ofReal (expectedNumStableMatchings n) * (scoreMarkedLaw n) (badSpouseMark n) := by
  let f : ScoreProfile n × Matching n → ℝ≥0∞ := (badSpouseMark n).indicator 1
  have hf : Measurable f := measurable_const.indicator (measurableSet_badSpouseMark n)
  have heq (μ : Matching n) :
      (fun x ↦ (scoreMarkEvent n).indicator f (x, μ)) =
        (badStableSpouseScores n μ).indicator 1 := by
    ext x
    by_cases hs : IsScoreStable x μ <;> by_cases hg : GoodSpouseScores x μ <;>
      simp [scoreMarkEvent, f, badSpouseMark, badStableSpouseScores, hs, hg]
  have hμ (μ : Matching n) :
      Measurable (fun x ↦ (scoreMarkEvent n).indicator f (x, μ)) := by
    rw [heq μ]
    exact measurable_const.indicator (measurableSet_badStableSpouseScores n μ)
  calc
    (∑ μ : Matching n, continuousScoreLaw n (badStableSpouseScores n μ)) =
        ∑ μ : Matching n, ∫⁻ x, (scoreMarkEvent n).indicator f (x, μ)
          ∂(continuousScoreLaw n) := by
      congr 1
      ext μ
      rw [heq μ, lintegral_indicator_one (measurableSet_badStableSpouseScores n μ)]
    _ = ∫⁻ x, ∑ μ : Matching n, (scoreMarkEvent n).indicator f (x, μ)
          ∂(continuousScoreLaw n) :=
      (lintegral_finsetSum _ fun μ _ ↦ hμ μ).symm
    _ = _ := by
      rw [← continuous_mark_counting_identity n hf]
      rw [show (∫⁻ z, f z ∂scoreMarkedLaw n) = (scoreMarkedLaw n) (badSpouseMark n)
        from lintegral_indicator_one (measurableSet_badSpouseMark n)]

/-- The bad-score probability is bounded by the normalized stable-mark exception count. -/
theorem measure_badCoexposureScores_le_marked (n : ℕ) :
    continuousScoreLaw n (goodCoexposureScores n)ᶜ ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * (scoreMarkedLaw n) (badSpouseMark n) :=
  (measure_badCoexposureScores_le_sum n).trans_eq (sum_measure_badStableSpouseScores_eq_marked n)

/-- The normalized female spouse scores sum to one on the good event. -/
theorem GoodSpouseScores.weight_sum {x : ScoreProfile n} {μ : Matching n}
    (h : GoodSpouseScores x μ) :
    ∑ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ = 1 := by
  rw [← Finset.sum_div]
  change femaleSpouseTotal x μ / femaleSpouseTotal x μ = 1
  exact div_self (by linarith [h.1])

/-- Good cutoffs uniformly bound the area of every potential blocking rectangle. -/
theorem GoodSpouseScores.spouseProduct_le {x : ScoreProfile n} {μ : Matching n}
    (h : GoodSpouseScores x μ) (hopen : ∀ r i, x r i ∈ Ioo (0 : ℝ) 1) (i j : Fin n) :
    maleSpouseScore x μ i * femaleSpouseScore x μ j ≤ 192 * (Real.log n) ^ 2 / n := by
  let s := femaleSpouseTotal x μ
  have hs : 2 ≤ s := h.1
  have hspos : 0 < s := by linarith
  have hsone : 0 < s - 1 := by linarith
  have hx : maleSpouseScore x μ i ≤ 8 * Real.log n / (s - 1) := h.2.2 i
  have hy : femaleSpouseScore x μ j / s ≤ 12 * Real.log n / n := h.2.1 j
  have hx0 : 0 ≤ maleSpouseScore x μ i := (hopen (.inl i) (μ i)).1.le
  have hy0 : 0 ≤ femaleSpouseScore x μ j := (hopen (.inr j) (μ.symm j)).1.le
  have hscale : s / (s - 1) ≤ 2 := (div_le_iff₀ hsone).2 (by linarith)
  calc
    maleSpouseScore x μ i * femaleSpouseScore x μ j =
        (maleSpouseScore x μ i * (femaleSpouseScore x μ j / s)) * s := by
          rw [mul_assoc, div_mul_cancel₀ _ hspos.ne']
    _ ≤ (8 * Real.log n / (s - 1) * (12 * Real.log n / n)) * s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hx hy (div_nonneg hy0 hspos.le) (hx0.trans hx)) hspos.le
    _ = (96 * (Real.log n) ^ 2 / n) * (s / (s - 1)) := by ring
    _ ≤ (96 * (Real.log n) ^ 2 / n) * 2 := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = 192 * (Real.log n) ^ 2 / n := by ring

/-- With zero agents, the stable empty matching fails the female-total cutoff. -/
theorem goodCoexposureScores_zero : goodCoexposureScores 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hs : IsStable (profileOfScores x) (Equiv.refl (Fin 0)) := fun m ↦ Fin.elim0 m
  have h := (hx.2.2 _ hs).1
  norm_num [femaleSpouseTotal] at h

-- Three agents already admit arrays satisfying all three inequalities for every matching.
example : (goodCoexposureScores 3).Nonempty := by
  let x : ScoreProfile 3 := fun _ i ↦ 3 / 4 + (i.val : ℝ) / 16
  have hxi (i : Fin 3) : (3 : ℝ) / 4 ≤ 3 / 4 + (i.val : ℝ) / 16 ∧
      3 / 4 + (i.val : ℝ) / 16 ≤ 7 / 8 := by
    have hlo : (0 : ℝ) ≤ i.val := by positivity
    have hn : i.val ≤ 2 := by omega
    have hhi : (i.val : ℝ) ≤ 2 := by exact_mod_cast hn
    constructor <;> linarith
  refine ⟨x, ?_, ?_, ?_⟩
  · intro r i j he
    apply Fin.ext
    have hr : (i.val : ℝ) = j.val := by dsimp [x] at he; linarith
    exact_mod_cast hr
  · intro r i
    exact ⟨by dsimp [x]; linarith [(hxi i).1], by dsimp [x]; linarith [(hxi i).2]⟩
  · intro μ _
    have hlo : 9 / 4 ≤ femaleSpouseTotal x μ := calc
      9 / 4 = ∑ j : Fin 3, (3 / 4 : ℝ) := by norm_num
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ (hxi (μ.symm j)).1
    have hhi : femaleSpouseTotal x μ ≤ 21 / 8 := calc
      _ ≤ ∑ j : Fin 3, (7 / 8 : ℝ) := Finset.sum_le_sum fun j _ ↦ (hxi (μ.symm j)).2
      _ = 21 / 8 := by norm_num
    have hlog : (1 / 2 : ℝ) < Real.log 3 :=
      (show (1 / 2 : ℝ) < Real.log 2 by linarith [Real.log_two_gt_d9]).trans_le
        (Real.log_le_log (by norm_num) (by norm_num))
    refine ⟨by linarith, ?_, ?_⟩
    · intro j
      have hy : femaleSpouseScore x μ j ≤ 7 / 8 := (hxi (μ.symm j)).2
      have hb : femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 1 :=
        (div_le_iff₀ (by linarith)).2 (by linarith)
      exact hb.trans (by norm_num; linarith)
    · intro i
      apply (le_div_iff₀ (by linarith)).2
      have hx : maleSpouseScore x μ i ≤ 7 / 8 := (hxi (μ i)).2
      have hb : femaleSpouseTotal x μ - 1 ≤ 13 / 8 := by linarith
      have hp := mul_le_mul hx hb (by linarith) (by norm_num : (0 : ℝ) ≤ 7 / 8)
      norm_num
      linarith

end LennonPittelFormalization

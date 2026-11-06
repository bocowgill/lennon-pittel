module

public import LennonPittel.PivotSingletonLength
public import LennonPittel.ReverseSupportWeightUpper
public import Mathlib.Probability.Independence.Integration

/-!
# Exponential cutoffs at marked stable matchings

Independent rows give a product bound for an exponentially tilted prescribed
cycle. Summing the label products first avoids a factorial loss in the union
bound. A separate disintegration lemma transfers the conditional bounds to
the original score law without conditioning on the selection of an anchor.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private theorem sum_supportPermutation_weights_le_pow {n k : ℕ} (q : Fin n → ℝ≥0∞)
    (hzero : (∑ j, q j) ≠ 0) (htop : (∑ j, q j) ≠ ∞) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k),
      ∏ i ∈ σ.support, q i) ≤ (∑ j, q j) ^ k := by
  classical
  let Q := ∑ j, q j
  let p (j : Fin n) := Q⁻¹ * q j
  have hp : ∑ j, p j = 1 := by
    simp only [p, ← Finset.mul_sum]
    exact ENNReal.inv_mul_cancel hzero htop
  have hq (j : Fin n) : q j = Q * p j := by
    change q j = Q * (Q⁻¹ * q j)
    rw [← mul_assoc, ENNReal.mul_inv_cancel hzero htop, one_mul]
  have he :
      (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k),
        ∏ i ∈ σ.support, q i) =
      Q ^ k * ∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k),
        ∏ i ∈ σ.support, p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    conv_lhs => simp only [hq, Finset.prod_mul_distrib, Finset.prod_const,
      (Finset.mem_filter.mp hσ).2]
  rw [he]
  exact (mul_le_mul_right (sum_supportPermutation_weights_le_one k p hp) (Q ^ k)).trans_eq
    (mul_one _)

section IndependentRows

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
  (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
  (out : ∀ i, Ω i → Option (Fin n)) (g : ∀ i, Fin n → Ω i → ℝ)
  [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]

/-- The one-row tilted mass of a specified successor arc. -/
noncomputable def tiltedForwardArc (i j : Fin n) : Ω i → ℝ≥0∞ :=
  {x | out i x = some j}.indicator fun x ↦ ENNReal.ofReal (Real.exp (g i j x))

/-- A prescribed cycle with large score has probability bounded by its tilted arc product. -/
theorem measure_pi_cycle_sum_gt_le (hout : ∀ i, Measurable (out i))
    (hg : ∀ i j, Measurable (g i j)) (σ : Matching n) (t : ℝ) :
    Measure.pi ν {y | RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
      t < ∑ i ∈ σ.support, g i (σ i) (y i)} ≤
      ENNReal.ofReal (Real.exp (-t)) *
        ∏ i ∈ σ.support, ∫⁻ x, tiltedForwardArc out g i (σ i) x ∂ν i := by
  classical
  let F (i : Fin n) := tiltedForwardArc out g i (σ i)
  have hF (i : Fin n) : Measurable (F i) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hg i _))).indicator
      (measurableSet_eq_fun (hout i) measurable_const)
  have hFπ (i : Fin n) : Measurable (fun y : ∀ j, Ω j ↦ F i (y i)) :=
    (hF i).comp (measurable_pi_apply i)
  let G (y : ∀ i, Ω i) := ENNReal.ofReal (Real.exp (-t)) * ∏ i ∈ σ.support, F i (y i)
  have hG : Measurable G := measurable_const.mul (σ.support.measurable_prod fun i _ ↦ hFπ i)
  calc
    _ ≤ ∫⁻ y, G y ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hG.aemeasurable
      intro y hy
      have he : (∏ i ∈ σ.support, F i (y i)) =
          ∏ i ∈ σ.support, ENNReal.ofReal (Real.exp (g i (σ i) (y i))) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact indicator_of_mem (s := {x | out i x = some (σ i)}) (hy.1.2 i hi)
          (fun x ↦ ENNReal.ofReal (Real.exp (g i (σ i) x)))
      unfold G
      rw [he, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _),
        ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (by linarith [hy.2]))
    _ = _ := by
      unfold G
      rw [lintegral_const_mul _ (σ.support.measurable_prod fun i _ ↦ hFπ i),
        lintegral_prod_eq_prod_lintegral_of_indepFun σ.support _
          (iIndepFun_pi fun i ↦ (hF i).aemeasurable) hFπ]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦
        (measurePreserving_eval ν i).lintegral_comp (hF i)

/-- A union bound over cycles of one length. The total tilted mass is the
sum of the target arc bounds, raised to that length. -/
theorem measure_pi_exists_cycle_length_sum_gt_le
    (hout : ∀ i, Measurable (out i)) (hg : ∀ i j, Measurable (g i j))
    (q : Fin n → ℝ≥0∞) (hzero : (∑ j, q j) ≠ 0) (htop : (∑ j, q j) ≠ ∞)
    (harc : ∀ i j, i ≠ j → (∫⁻ x, tiltedForwardArc out g i j x ∂ν i) ≤ q j)
    (k : ℕ) (t : ℝ) :
    Measure.pi ν {y | ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
      σ.support.card = k ∧ t < ∑ i ∈ σ.support, g i (σ i) (y i)} ≤
      ENNReal.ofReal (Real.exp (-t)) * (∑ j, q j) ^ k := by
  classical
  let S := Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k)
  let E (σ : Matching n) := {y : ∀ i, Ω i | RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
    t < ∑ i ∈ σ.support, g i (σ i) (y i)}
  have he :
      {y | ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
        σ.support.card = k ∧ t < ∑ i ∈ σ.support, g i (σ i) (y i)} =
        ⋃ σ ∈ S, E σ := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, S, E, Finset.mem_filter_univ]
    constructor
    · rintro ⟨σ, hσ, hk, ht⟩
      exact ⟨σ, hk, hσ, ht⟩
    · rintro ⟨σ, hk, hσ, ht⟩
      exact ⟨σ, hσ, hk, ht⟩
  rw [he]
  calc
    _ ≤ ∑ σ ∈ S, Measure.pi ν (E σ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ σ ∈ S, ENNReal.ofReal (Real.exp (-t)) * ∏ i ∈ σ.support, q i :=
      Finset.sum_le_sum fun σ _ ↦ (measure_pi_cycle_sum_gt_le ν out g hout hg σ t).trans <|
        mul_le_mul_right (calc
          _ ≤ ∏ i ∈ σ.support, q (σ i) :=
            Finset.prod_le_prod fun i hi ↦ harc i (σ i) (Equiv.Perm.mem_support.mp hi).symm
          _ = _ := σ.prod_comp σ.support q (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi)) _
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_right (sum_supportPermutation_weights_le_pow q hzero htop) _

end IndependentRows

/-- Transfer a score event from the normalized rows at a fixed stable mark.
The cutoff on diagonals need not depend on the identity of the chosen cycle. -/
theorem measure_scoreStable_diagonal_scoreEvent_le {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    (hvalid : ∀ d ∈ C, (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) ∧
      ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    {E : Set (ScoreProfile n)} (hE : MeasurableSet E) {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hrow : ∀ᵐ d ∂diagonalScoreLaw n, d ∈ C →
      (Measure.pi (normalizedStableScoreRowLaw d))
        {r | (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) ∈ E} ≤ a) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} * a := by
  let D : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let f : ScoreProfile n → ℝ≥0∞ := E.indicator 1
  have hf : Measurable f := measurable_const.indicator hE
  have hleft : continuousScoreLaw n
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E} =
      ∫⁻ x in D, f x ∂continuousScoreLaw n := by
    rw [show f = E.indicator 1 from rfl, lintegral_indicator_one hE, Measure.restrict_apply hE]
    congr 1
    ext x
    change (IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E) ↔
      (x ∈ E ∧ IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C)
    tauto
  rw [hleft, continuousScoreLaw_lintegral_stable_and_diagonal_rows μ hC hf]
  let m (d : DiagonalScorePairs n) := offDiagonalScoreLaw n (offDiagonalNonblocking d)
  have hM : (∫⁻ d, m d ∂diagonalScoreLaw n) = continuousScoreLaw n {x | IsScoreStable x μ} := by
    simpa only [mem_univ, and_true, indicator_univ, m] using
      (continuousScoreLaw_stable_and_diagonal μ (C := univ) MeasurableSet.univ).symm
  calc
    _ ≤ ∫⁻ d in C, m d * a ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hrow] with d hd hr
      obtain ⟨hx, hy⟩ := hvalid d hd
      let R := (splitScorePairs μ).symm ∘ fun r : OffDiagonalScoreRows n ↦
        (d, (offDiagonalRowsEquiv n).symm r)
      let B := R ⁻¹' E
      have hB : MeasurableSet B := hE.preimage
        ((splitScorePairs μ).symm.measurable.comp
          (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
      have hfun : (fun r ↦ f ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) =
          B.indicator 1 := by
        funext r
        change E.indicator 1 (R r) = _
        by_cases hb : r ∈ B
        · rw [indicator_of_mem (show R r ∈ E from hb), indicator_of_mem hb]
          rfl
        · rw [indicator_of_notMem (show R r ∉ E from hb), indicator_of_notMem hb]
      rw [pi_stableScoreRowLaw_eq_smul_normalized d hx hy, hfun, lintegral_smul_measure,
        lintegral_indicator_one hB, smul_eq_mul]
      exact mul_le_mul_right (hr hd) _
    _ ≤ ∫⁻ d, m d * a ∂diagonalScoreLaw n :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by rw [lintegral_mul_const' _ _ ha, hM]

/-- Sum a fixed-mark conditional estimate over all stable marks. -/
theorem measure_exists_scoreStable_diagonal_event_le {n : ℕ}
    (C : Set (DiagonalScorePairs n)) (E : Matching n → Set (ScoreProfile n)) (a : ℝ≥0∞)
    (h : ∀ μ : Matching n,
      continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ} ≤
        continuousScoreLaw n {x | IsScoreStable x μ} * a) :
    continuousScoreLaw n {x | ∃ μ : Matching n, IsScoreStable x μ ∧
      (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ} ≤ ENNReal.ofReal (expectedNumStableMatchings n) * a := by
  let F (μ : Matching n) :=
    {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ}
  have he : {x | ∃ μ : Matching n, IsScoreStable x μ ∧
      (splitScorePairs μ x).1 ∈ C ∧ x ∈ E μ} = ⋃ μ, F μ := by
    ext x
    change (∃ μ : Matching n, x ∈ F μ) ↔ x ∈ ⋃ μ, F μ
    exact mem_iUnion.symm
  rw [he]
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n (F μ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} * a :=
      Finset.sum_le_sum fun μ _ ↦ h μ
    _ = _ := by rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]

end LennonPittelFormalization

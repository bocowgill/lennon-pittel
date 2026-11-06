module

public import LennonPittel.PivotReverseCompetitorMass
public import LennonPittel.PivotForwardMaskProbability
public import LennonPittel.WeightedBoolProductTail
public import LennonPittel.CoexposureSpouseMarginal
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rare heavy columns of the forward mask

The omitted reverse weight is a weighted sum of independent forward flags.
On the eligibility score band, its tail is smaller than every inverse power.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The normalized law of a stable fixed-score column has an exponentially
small chance to omit more than `u` of the total male spouse weight. -/
theorem measure_forwardMaskOmittedMass_gt_le {n : ℕ} (d : DiagonalScorePairs n)
    (j : Fin n) {B u : ℝ}
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1) (hB : 0 < B)
    (hw : ∀ i, (diagonalPairAt d i).1 / (∑ l, (diagonalPairAt d l).1) ≤ B)
    (hy : 2 * (Real.exp 1 - 1) * (diagonalPairAt d j).2 ≤ u) :
    (stableOffDiagonalProbabilityLaw d)
      {z | u * (∑ i, (diagonalPairAt d i).1) <
        forwardMaskOmittedMass d (forwardMaskOfScores d z) j} ≤
      ENNReal.ofReal (Real.exp (-u / (2 * B))) := by
  let X := ∑ i, (diagonalPairAt d i).1
  let y := (diagonalPairAt d j).2
  let J := {i : Fin n // i ≠ j}
  let ν (i : J) := forwardCellFlagProbabilityLaw (diagonalPairAt d i.val).1 y
  let w (i : J) := (diagonalPairAt d i.val).1 / X
  let g (z : OffDiagonalScorePairs n) := forwardColumnFlag j (forwardMaskOfScores d z)
  let E : Set (J → Bool) := {b | u < ∑ i, if b i then w i else 0}
  let : ∀ i : J, IsProbabilityMeasure (ν i) :=
    fun i ↦ forwardCellFlagProbabilityLaw_isProbabilityMeasure (hd i.val).1 (hd j).2
  have hw₀ (i : J) : 0 ≤ w i := div_nonneg (hd i.val).1.1 hX.le
  have hsum : (∑ i : J, w i) ≤ 1 := by
    let v (i : Fin n) := (diagonalPairAt d i).1 / X
    change (∑ i : {i : Fin n // i ≠ j}, v i.val) ≤ _
    rw [← Finset.sum_subtype (Finset.univ.filter (· ≠ j)) (by simp) v]
    calc
      _ ≤ ∑ i, v i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ div_nonneg (hd i).1.1 hX.le)
      _ = 1 := by simp only [v, ← Finset.sum_div, X, div_self hX.ne']
  have hmean : (∑ i : J, w i * (ν i {true}).toReal) ≤ y := calc
    _ ≤ ∑ i : J, w i * y := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (forwardCellFlagProbabilityLaw_true_toReal_le
        (hd i.val).1 (hd j).2) (hw₀ i)
    _ = (∑ i : J, w i) * y := (Finset.sum_mul ..).symm
    _ ≤ 1 * y := mul_le_mul_of_nonneg_right hsum (hd j).2.1
    _ = y := one_mul _
  have htail := measure_pi_weightedBoolTail_le_of_mean_le ν w u hB
    (fun i ↦ ⟨hw₀ i, hw i.val⟩) hmean
  change (Measure.pi ν) E ≤ _ at htail
  have hg : Measurable g := (measurable_forwardColumnFlag j).comp
    (measurable_forwardMaskOfScores d)
  rw [← map_forwardColumnFlag_stableOffDiagonalProbabilityLaw d j hd,
    Measure.map_apply hg MeasurableSet.of_discrete] at htail
  have hE : g ⁻¹' E = {z | u * X < forwardMaskOmittedMass d (forwardMaskOfScores d z) j} := by
    ext z
    change (u < ∑ i : J, if g z i then w i else 0) ↔ _
    have he : (∑ i : J, if g z i then w i else 0) =
        forwardMaskOmittedMass d (forwardMaskOfScores d z) j / X := by
      rw [forwardMaskOmittedMass, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change (if g z i then w i else 0) =
        (if g z i then (diagonalPairAt d i.val).1 else 0) / X
      split <;> simp [w, *]
    rw [he, lt_div_iff₀ hX]
    rfl
  rw [hE] at htail
  refine htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  rw [show -u / (2 * B) = (-u / 2) / B by ring]
  exact div_le_div_of_nonneg_right (by linarith only [hy]) hB.le

/-- The off-diagonal arrays whose forward mask has a heavy active column. -/
def badForwardMask {n : ℕ} (d : DiagonalScorePairs n) (u : ℝ) : Set (OffDiagonalScorePairs n) :=
  ⋃ j : Fin n, {z | u * (∑ i, (diagonalPairAt d i).1) <
    forwardMaskOmittedMass d (forwardMaskOfScores d z) j}

theorem measurableSet_badForwardMask {n : ℕ} (d : DiagonalScorePairs n) (u : ℝ) :
    MeasurableSet (badForwardMask d u) := by
  apply MeasurableSet.iUnion
  intro j
  exact (measurable_forwardMaskOfScores d)
    (MeasurableSet.of_discrete : MeasurableSet {f : OffDiagonalCellIndex n → Bool |
      u * (∑ i, (diagonalPairAt d i).1) < forwardMaskOmittedMass d f j})

/-- The complement of the exceptional event gives every column bound at once. -/
theorem forwardMaskOmittedMass_le_of_notMem_badForwardMask {n : ℕ}
    (d : DiagonalScorePairs n) {u : ℝ} {z : OffDiagonalScorePairs n}
    (h : z ∉ badForwardMask d u) (j : Fin n) :
    forwardMaskOmittedMass d (forwardMaskOfScores d z) j ≤
      u * (∑ i, (diagonalPairAt d i).1) :=
  le_of_not_gt fun hj ↦ h (Set.mem_iUnion.mpr ⟨j, hj⟩)

/-- Union bound over columns. No joint independence of the column events
is needed for this step. -/
theorem measure_badForwardMask_le {n : ℕ} (d : DiagonalScorePairs n) {B u : ℝ}
    (hd : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1)
    (hX : 0 < ∑ i, (diagonalPairAt d i).1) (hB : 0 < B)
    (hw : ∀ i, (diagonalPairAt d i).1 / (∑ l, (diagonalPairAt d l).1) ≤ B)
    (hy : ∀ j, 2 * (Real.exp 1 - 1) * (diagonalPairAt d j).2 ≤ u) :
    (stableOffDiagonalProbabilityLaw d) (badForwardMask d u) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-u / (2 * B))) := by
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal (Real.exp (-u / (2 * B))) :=
      Finset.sum_le_sum fun j _ ↦ measure_forwardMaskOmittedMass_gt_le d j hd hX hB hw (hy j)
    _ = _ := by simp [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n)]

/-- The mean and Chernoff-exponent budgets at the score-band scales.
The exponent dominates `(p+1) log n`, including the union over all columns. -/
theorem eventually_forwardMaskRate (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      2 * (Real.exp 1 - 1) * (Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n) ≤
        (n : ℝ) ^ (-11 / 20 : ℝ) ∧
      (n : ℝ) * Real.exp (-((n : ℝ) ^ (-11 / 20 : ℝ)) /
        (2 * (Cx * Real.log n / n))) ≤ (n : ℝ) ^ (-p) := by
  have h₁ := (((isLittleO_log_rpow_atTop (r := (1 / 20 : ℝ)) (by norm_num)).const_mul_left
    (2 * (Real.exp 1 - 1) * Cy)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have h₂ := (((isLittleO_log_rpow_rpow_atTop (s := (9 / 20 : ℝ)) 2 (by norm_num)).const_mul_left
    (2 * Cx * (p + 1))).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), h₁, h₂] with n hn h₁n h₂n
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have hb : 0 < 2 * (Cx * Real.log (n : ℝ) / n) := by positivity
  have hm : 2 * (Real.exp 1 - 1) * Cy * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    have h : |2 * (Real.exp 1 - 1) * Cy * Real.log (n : ℝ)| ≤
        |(n : ℝ) ^ (1 / 20 : ℝ)| := h₁n
    rw [abs_of_nonneg (Real.rpow_nonneg hn₀.le _)] at h
    exact (le_abs_self _).trans h
  have hh : 2 * Cx * (p + 1) * Real.log (n : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ (9 / 20 : ℝ) := by
    have h : |2 * Cx * (p + 1) * Real.log (n : ℝ) ^ (2 : ℝ)| ≤
        |(n : ℝ) ^ (9 / 20 : ℝ)| := h₂n
    rw [Real.rpow_two, abs_of_nonneg (Real.rpow_nonneg hn₀.le _)] at h
    exact (le_abs_self _).trans h
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hn₀.le (-3 / 5 : ℝ))
  rw [← Real.rpow_add hn₀, show (1 / 20 : ℝ) + (-3 / 5) = -11 / 20 by norm_num] at hm'
  have hE : (p + 1) * Real.log (n : ℝ) ≤
      (n : ℝ) ^ (-11 / 20 : ℝ) / (2 * (Cx * Real.log (n : ℝ) / n)) := by
    apply (le_div_iff₀ hb).mpr
    rw [show (p + 1) * Real.log (n : ℝ) * (2 * (Cx * Real.log (n : ℝ) / n)) =
      (2 * Cx * (p + 1) * Real.log (n : ℝ) ^ (2 : ℕ)) / n by ring]
    apply (div_le_iff₀ hn₀).mpr
    have hpow : (n : ℝ) ^ (-11 / 20 : ℝ) * n = (n : ℝ) ^ (9 / 20 : ℝ) := calc
      _ = (n : ℝ) ^ (-11 / 20 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
    rwa [hpow]
  refine ⟨hn, ?_, ?_⟩
  · convert hm' using 1
    ring
  · calc
      _ ≤ (n : ℝ) * Real.exp (-((p + 1) * Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          rw [neg_div]
          exact neg_le_neg hE)) hn₀.le
      _ = (n : ℝ) ^ (-p) := by
        rw [show -((p + 1) * Real.log (n : ℝ)) = Real.log (n : ℝ) * (-(p + 1)) by ring,
          ← Real.rpow_def_of_pos hn₀]
        calc
          _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + (-(p + 1)) = -p by ring]

/-- Uniformly in the spouse scores in the band, a heavy active column has
probability at most `n^(-p)` for every fixed exponent `p` and all large `n`. -/
theorem eventually_measure_badForwardMask_le (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) →
      0 < (∑ i, (diagonalPairAt d i).1) →
      (∀ i, (diagonalPairAt d i).1 / (∑ j, (diagonalPairAt d j).1) ≤ Cx * Real.log n / n) →
      (∀ j, (diagonalPairAt d j).2 ≤ Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n) →
      (stableOffDiagonalProbabilityLaw d) (badForwardMask d ((n : ℝ) ^ (-11 / 20 : ℝ))) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_forwardMaskRate Cx Cy p hx] with n h d hd hX hw hy
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast h.1)
  have he : 0 ≤ 2 * (Real.exp 1 - 1) := by
    have := Real.one_le_exp (by norm_num : 0 ≤ (1 : ℝ))
    linarith
  exact (measure_badForwardMask_le d hd hX (by positivity) hw (fun j ↦
    (mul_le_mul_of_nonneg_left (hy j) he).trans h.2.1)).trans
    (ENNReal.ofReal_le_ofReal h.2.2)

/-- The same uniform rate on the unnormalized stability law. The stability
mass is retained as a factor for later integration over spouse scores. -/
theorem eventually_restrict_nonblocking_badForwardMask_le (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) →
      0 < (∑ i, (diagonalPairAt d i).1) →
      (∀ i, (diagonalPairAt d i).1 / (∑ j, (diagonalPairAt d j).1) ≤ Cx * Real.log n / n) →
      (∀ j, (diagonalPairAt d j).2 ≤ Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n) →
      ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))
        (badForwardMask d ((n : ℝ) ^ (-11 / 20 : ℝ))) ≤
      offDiagonalScoreLaw n (offDiagonalNonblocking d) * ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_measure_badForwardMask_le Cx Cy p hx] with n h d hd hX hw hy
  rw [offDiagonalScoreLaw_restrict_nonblocking_eq_smul_probabilityLaw d hd,
    Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (h d hd hX hw hy) _

/-- An upper score-share bound on the band gives the absolute female
threshold used by the mask concentration theorem. -/
theorem femaleScore_le_of_share_of_band {n : ℕ} {Y y C : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hY : 0 < Y) (hY' : Y ≤ (n : ℝ) ^ (2 / 5 : ℝ))
    (hy : y / Y ≤ C * Real.log n / n) :
    y ≤ C * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn₁
  have he : (n : ℝ) ^ (2 / 5 : ℝ) / n = (n : ℝ) ^ (-3 / 5 : ℝ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn₀]
    norm_num
  calc
    _ ≤ (C * Real.log n / n) * Y := (div_le_iff₀ hY).mp hy
    _ ≤ (C * Real.log n / n) * (n : ℝ) ^ (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hY' (by positivity)
    _ = C * ((n : ℝ) ^ (2 / 5 : ℝ) / n) * Real.log n := by ring
    _ = _ := by rw [he]

/-- Measurability jointly in the spouse diagonal and off-diagonal scores. -/
theorem measurableSet_jointBadForwardMask (n : ℕ) (u : ℝ) :
    MeasurableSet {z : DiagonalScorePairs n × OffDiagonalScorePairs n |
      z.2 ∈ badForwardMask z.1 u} := by
  let Ω := DiagonalScorePairs n × OffDiagonalScorePairs n
  let x (i : Fin n) (z : Ω) := (diagonalPairAt z.1 i).1
  let y (j : Fin n) (z : Ω) := (diagonalPairAt z.1 j).2
  let idx (i : Fin n) : {q : ScorePairIndex n // q.1 = q.2} := ⟨(i, i), rfl⟩
  have hx (i : Fin n) : Measurable (x i) :=
    ((measurable_pi_apply (idx i)).comp measurable_fst).fst
  have hy (j : Fin n) : Measurable (y j) :=
    ((measurable_pi_apply (idx j)).comp measurable_fst).snd
  have homit (j : Fin n) :
      Measurable (fun z : Ω ↦ forwardMaskOmittedMass z.1 (forwardMaskOfScores z.1 z.2) j) := by
    apply Finset.measurable_sum
    intro i _
    let q : OffDiagonalCellIndex n := ⟨(i.val, j), i.property⟩
    let zq (z : Ω) := z.2 q
    have hzq : Measurable zq := (measurable_pi_apply q).comp measurable_snd
    have hactive : MeasurableSet {z : Ω | forwardMaskOfScores z.1 z.2 q = true} := by
      have he : {z : Ω | forwardMaskOfScores z.1 z.2 q = true} =
          {z | x i.val z < (zq z).1} ∩ {z | (zq z).2 < y j z} := by
        ext z
        exact forwardCellFlag_eq_true.trans Set.mem_prod
      rw [he]
      exact (measurableSet_lt (hx i.val) hzq.fst).inter (measurableSet_lt hzq.snd (hy j))
    exact Measurable.ite hactive (hx i.val) measurable_const
  have he : {z : Ω | z.2 ∈ badForwardMask z.1 u} =
      ⋃ j : Fin n, {z : Ω | u * (∑ i, x i z) <
        forwardMaskOmittedMass z.1 (forwardMaskOfScores z.1 z.2) j} := by
    ext z
    simp only [badForwardMask, mem_ofPred_eq, mem_iUnion, x]
  rw [he]
  exact MeasurableSet.iUnion fun j ↦ measurableSet_lt
    (measurable_const.mul (Finset.measurable_sum _ (fun i _ ↦ hx i))) (homit j)

/-- The score-level event of a stable mark in a diagonal band with a heavy mask column. -/
def badForwardMaskAnchorEvent {n : ℕ} (μ : Matching n) (C : Set (DiagonalScorePairs n))
    (u : ℝ) : Set (ScoreProfile n) :=
  {x | let z := splitScorePairs μ x
       IsScoreStable x μ ∧ z.1 ∈ C ∧ z.2 ∈ badForwardMask z.1 u}

/-- Integrate a uniform fixed-diagonal exception bound without dividing
by the probability of a stable mark or of its diagonal band. -/
theorem measure_badForwardMaskAnchorEvent_le {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C) (u : ℝ) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (h : ∀ d ∈ C,
      ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) (badForwardMask d u) ≤
        offDiagonalScoreLaw n (offDiagonalNonblocking d) * a) :
    continuousScoreLaw n (badForwardMaskAnchorEvent μ C u) ≤
      continuousScoreLaw n {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C} * a := by
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let B : Set (ScoreProfile n) := (splitScorePairs μ) ⁻¹'
    {z | z.2 ∈ badForwardMask z.1 u}
  have hB : MeasurableSet B := (measurableSet_jointBadForwardMask n u).preimage
    (splitScorePairs μ).measurable
  let ν (d : DiagonalScorePairs n) := (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)
  have hS : continuousScoreLaw n S = ∫⁻ d in C, (ν d) univ ∂diagonalScoreLaw n := by
    simpa only [lintegral_const, one_mul, ν, S, Measure.restrict_apply_univ] using
      (continuousScoreLaw_lintegral_stable_and_diagonal μ hC
        (f := fun _ ↦ (1 : ℝ≥0∞)) measurable_const)
  have hsection (d : DiagonalScorePairs n) :
      (∫⁻ z, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) ((splitScorePairs μ).symm (d, z)) ∂ν d) =
        (ν d) (badForwardMask d u) := by
    rw [← lintegral_indicator_one (measurableSet_badForwardMask d u)]
    apply lintegral_congr
    intro z
    have he : ((splitScorePairs μ).symm (d, z)) ∈ B ↔ z ∈ badForwardMask d u := by
      change ((splitScorePairs μ) ((splitScorePairs μ).symm (d, z))).2 ∈
        badForwardMask ((splitScorePairs μ) ((splitScorePairs μ).symm (d, z))).1 u ↔ _
      rw [MeasurableEquiv.apply_symm_apply]
    by_cases hz : z ∈ badForwardMask d u
    · rw [Set.indicator_of_mem (he.mpr hz), Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem (he.not.mpr hz), Set.indicator_of_notMem hz]
  have hBS : badForwardMaskAnchorEvent μ C u = B ∩ S := by
    ext x
    change (_ ∧ _ ∧ _) ↔ _ ∧ (_ ∧ _)
    tauto
  calc
    _ = ∫⁻ d in C, ∫⁻ z, B.indicator (fun _ ↦ (1 : ℝ≥0∞))
        ((splitScorePairs μ).symm (d, z)) ∂ν d ∂diagonalScoreLaw n := by
      rw [hBS, ← Measure.restrict_apply hB, ← lintegral_indicator_one hB]
      exact continuousScoreLaw_lintegral_stable_and_diagonal μ hC
        (measurable_const.indicator hB)
    _ ≤ ∫⁻ d in C, (ν d) univ * a ∂diagonalScoreLaw n := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem (μ := diagonalScoreLaw n) hC] with d hd
      rw [hsection d]
      simpa only [ν, Measure.restrict_apply_univ] using h d hd
    _ = _ := by rw [lintegral_mul_const' a _ ha, ← hS]

/-- On every measurable diagonal score band satisfying the stated bounds,
the expected number of bad-mask stable marks is at most the stable-count
first moment times an arbitrary fixed inverse power of the market size. -/
theorem eventually_sum_measure_badForwardMaskAnchorEvent_le (Cx Cy p : ℝ) (hx : 0 < Cx) :
    ∀ᶠ n : ℕ in atTop, ∀ C : Set (DiagonalScorePairs n), MeasurableSet C →
      (∀ d ∈ C,
        (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
        0 < (∑ i, (diagonalPairAt d i).1) ∧
        (∀ i, (diagonalPairAt d i).1 / (∑ j, (diagonalPairAt d j).1) ≤ Cx * Real.log n / n) ∧
        (∀ j, (diagonalPairAt d j).2 ≤ Cy * (n : ℝ) ^ (-3 / 5 : ℝ) * Real.log n)) →
      (∑ μ : Matching n, continuousScoreLaw n
        (badForwardMaskAnchorEvent μ C ((n : ℝ) ^ (-11 / 20 : ℝ)))) ≤
        ENNReal.ofReal (expectedNumStableMatchings n) * ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_restrict_nonblocking_badForwardMask_le Cx Cy p hx]
    with n h C hC hband
  let a := ENNReal.ofReal ((n : ℝ) ^ (-p))
  calc
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} * a := by
      refine Finset.sum_le_sum fun μ _ ↦ ?_
      refine (measure_badForwardMaskAnchorEvent_le μ hC _ ENNReal.ofReal_ne_top
        (fun d hd ↦ ?_)).trans (mul_le_mul_left (measure_mono fun _ hx ↦ hx.1) a)
      obtain ⟨hd₁, hX, hw, hy⟩ := hband d hd
      exact h d hd₁ hX hw hy
    _ = _ := by rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]

end LennonPittelFormalization

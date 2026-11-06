module

public import LennonPittel.IndependentFlagLowerTail
public import LennonPittel.ScoreRotationBandCrossing
public import LennonPittel.ScoreSideSwap
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Interval.Finset.Fin

/-!
# The woman-optimal score from a proposal-count cap

A uniform bound on each row's order statistics applies even to the spouse
selected adaptively by deferred acceptance. Each selected rank plus one is
exactly the corresponding proposer's contribution to the proposal count.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- A simultaneous upper threshold for the score at a given one-based rank. -/
noncomputable def daRankScoreThreshold (n k : ℕ) : ℝ :=
  16 * ((k : ℝ) + Real.log n) / n

/-- At a given rank, too few coordinates lie below its score threshold. -/
def badRankThresholdRow (n : ℕ) (k : Fin n) : Set (Fin n → ℝ) :=
  {y | (∑ j, if y j ≤ daRankScoreThreshold n (k.val + 1) then (1 : ℝ) else 0) < k.val + 1}

private theorem measurableSet_badRankThresholdRow (n : ℕ) (k : Fin n) :
    MeasurableSet (badRankThresholdRow n k) :=
  measurableSet_lt (Finset.measurable_sum _ fun j _ ↦
    Measurable.ite (measurableSet_le (measurable_pi_apply j) measurable_const)
      measurable_const measurable_const) measurable_const

private theorem unitScoreLaw_Iic {a : ℝ} (ha' : a ≤ 1) :
    unitScoreLaw (Iic a) = ENNReal.ofReal a := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iic,
    show Iic a ∩ Icc 0 1 = Icc 0 a by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans ha'⟩⟩,
    Real.volume_Icc, sub_zero]

private theorem measure_badRankThresholdRow_le {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (Measure.pi fun _ : Fin n ↦ unitScoreLaw) (badRankThresholdRow n k) ≤
      ENNReal.ofReal (Real.exp (-4 * Real.log n)) := by
  let q := daRankScoreThreshold n (k.val + 1)
  let ν := Measure.pi fun _ : Fin n ↦ unitScoreLaw
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hq : 0 ≤ q := by
    unfold q daRankScoreThreshold
    positivity
  by_cases hq₁ : q ≤ 1
  · have hmass : ∀ _ : Fin n, ENNReal.ofReal q ≤ unitScoreLaw (Iic q) :=
      fun _ ↦ (unitScoreLaw_Iic hq₁).ge
    have htail := measure_pi_flagCount_lt_le_exp
      (fun _ : Fin n ↦ unitScoreLaw) (fun _ ↦ Iic q)
      (fun _ ↦ measurableSet_Iic) q ((k.val : ℝ) + 1) hq hmass
    refine htail.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    rw [Fintype.card_fin]
    have hhalf : (1 / 2 : ℝ) ≤ 1 - Real.exp (-1) := by
      rw [Real.exp_neg, inv_eq_one_div]
      have h := Real.exp_one_gt_d9
      have h' : 1 / Real.exp 1 ≤ (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf (show 0 ≤ q * n by positivity)
    have hqmul : q * (n : ℝ) = 16 * ((k.val : ℝ) + 1 + Real.log n) := by
      simp only [q, daRankScoreThreshold, Nat.cast_add, Nat.cast_one]
      exact div_mul_cancel₀ _ hn₀.ne'
    rw [hqmul] at hmul
    rw [mul_assoc, hqmul]
    linarith only [hmul, hlog, Nat.cast_nonneg (α := ℝ) k.val]
  · have hae : ∀ᵐ y ∂ν, ∀ i, y i ∈ Icc (0 : ℝ) 1 :=
      ae_all_iff.2 fun i ↦
        (measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).quasiMeasurePreserving.ae
          (ae_restrict_mem measurableSet_Icc)
    have hz : ν (badRankThresholdRow n k) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae] with y hy
      change ¬ (∑ j, if y j ≤ q then (1 : ℝ) else 0) < _
      have hh (j : Fin n) : y j ≤ q := (hy j).2.trans (le_of_not_ge hq₁)
      simp only [hh, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, not_lt]
      exact_mod_cast Nat.succ_le_of_lt k.isLt
    change ν (badRankThresholdRow n k) ≤ _
    rw [hz]
    exact zero_le

/-- Failure of the rank-score bound in at least one female row and rank. -/
def daBadFemaleRankThreshold (n : ℕ) : Set (ScoreProfile n) :=
  ⋃ w : Fin n, ⋃ k : Fin n, (fun x : ScoreProfile n ↦ x (.inr w)) ⁻¹' badRankThresholdRow n k

/-- The simultaneous female rank-score bound has only an inverse-square exception. -/
theorem measure_daBadFemaleRankThreshold_le {n : ℕ} (hn : 0 < n) :
    continuousScoreLaw n (daBadFemaleRankThreshold n) ≤ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ)) := by
  have hrow (w k : Fin n) :
      continuousScoreLaw n ((fun x : ScoreProfile n ↦ x (.inr w)) ⁻¹'
        badRankThresholdRow n k) ≤ ENNReal.ofReal (Real.exp (-4 * Real.log n)) := by
    rw [continuousScoreLaw, (measurePreserving_eval (fun _ : Fin n ⊕ Fin n ↦ Measure.pi
      fun _ : Fin n ↦ unitScoreLaw) (.inr w)).measure_preimage
      (measurableSet_badRankThresholdRow n k).nullMeasurableSet]
    exact measure_badRankThresholdRow_le hn k
  unfold daBadFemaleRankThreshold
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _w : Fin n, ∑ _k : Fin n, ENNReal.ofReal (Real.exp (-4 * Real.log n)) := by
      gcongr with w _
      exact (measure_iUnion_le _).trans (by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun k _ ↦ hrow w k)
    _ = _ := by
      have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_comm (-4) (Real.log n), ← Real.rpow_def_of_pos hn₀,
        Real.rpow_neg hn₀.le, Real.rpow_neg hn₀.le,
        show (4 : ℝ) = (4 : ℕ) by norm_num, show (2 : ℝ) = (2 : ℕ) by norm_num,
        Real.rpow_natCast, Real.rpow_natCast]
      field_simp

/-- A score in a tie-free row is at most the threshold for its rank
whenever the row has sufficiently many scores below that threshold. -/
theorem femaleScore_le_daRankScoreThreshold {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ w, Function.Injective (x (.inr w))) (hgood : x ∉ daBadFemaleRankThreshold n)
    (w m : Fin n) :
    x (.inr w) m ≤ daRankScoreThreshold n ((rankPermutation (x (.inr w)) m).val + 1) := by
  let y := x (.inr w)
  let e := rankPermutation y
  let k := e m
  let q := daRankScoreThreshold n (k.val + 1)
  have hcount : (k.val : ℝ) + 1 ≤ ∑ j, if y j ≤ q then (1 : ℝ) else 0 := by
    apply le_of_not_gt
    intro h
    exact hgood (mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨k, h⟩⟩)
  change y m ≤ q
  by_contra! h
  have hbound : (∑ j, if y j ≤ q then (1 : ℝ) else 0) ≤
      ∑ j, if e j < k then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : y j ≤ q
    · have hlt : e j < k := (rankPermutation_lt_iff (hx w) j m).mpr (hj.trans_lt h)
      simp only [hj, hlt, ite_true, le_refl]
    · simp only [hj, ite_false]
      split <;> norm_num
  have hcard : (∑ j, if e j < k then (1 : ℝ) else 0) = k.val := by
    rw [Equiv.sum_comp e (fun j ↦ if j < k then (1 : ℝ) else 0), ← Finset.sum_filter,
      show Finset.univ.filter (fun j ↦ j < k) = Finset.Iio k by ext j; simp,
      Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_Iio]
  rw [hcard] at hbound
  linarith

private theorem scoreWalkMatching_horizon_symm_eq_swap_da {n : ℕ} (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) :
    (scoreWalkMatching x (n * (n - 1))).symm =
      DAState.matching (swapProfile (profileOfScores x)) := by
  let p := swapProfile (profileOfScores x)
  let μ := (scoreWalkMatching x (n * (n - 1))).symm
  let ν := DAState.matching p
  have hμ : IsManOptimal p μ := (scoreRotationWalk_da_optimal_endpoints x hx).2.2
  have hν : IsManOptimal p ν := DAState.isManOptimal_matching p
  change μ = ν
  apply Equiv.ext
  intro w
  exact (p.manRank w).injective (le_antisymm (hμ.2 ν hν.1 w) (hν.2 μ hμ.1 w))

/-- On the uniform order-statistic event, a deterministic proposal cap
bounds the female spouse total at the end of the rotation walk. -/
theorem scoreWalkFemaleTotal_horizon_le_of_proposalCount {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : ∀ w, Function.Injective (x (.inr w)))
    (hgood : x ∉ daBadFemaleRankThreshold n) {T : ℕ}
    (hT : (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount ≤ T) :
    scoreWalkFemaleTotal x (n * (n - 1)) ≤ 16 * ((T : ℝ) / n + Real.log n) := by
  let p := swapProfile (profileOfScores x)
  let s := DAState.run p (n * n)
  let μ := DAState.matching p
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrank (w : Fin n) : (rankPermutation (x (.inr w)) (μ w)).val + 1 = s.count w :=
    (DAState.valid_run p _).held_last (s.held_toMatching (DAState.complete_run_sq p) w)
  have hsum : (∑ w, (s.count w : ℝ)) ≤ T := by
    exact_mod_cast hT
  change (∑ w, x (.inr w) ((scoreWalkMatching x (n * (n - 1))).symm w)) ≤ _
  rw [scoreWalkMatching_horizon_symm_eq_swap_da x hx]
  calc
    _ ≤ ∑ w, daRankScoreThreshold n (s.count w) := by
      refine Finset.sum_le_sum fun w _ ↦ ?_
      simpa only [hrank w] using femaleScore_le_daRankScoreThreshold hx hgood w (μ w)
    _ = 16 * ((∑ w, (s.count w : ℝ)) / n + Real.log n) := by
      simp only [daRankScoreThreshold, ← Finset.sum_div, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    _ ≤ _ := by gcongr

private theorem measure_swapDAProposalCount_gt (n T : ℕ) :
    continuousScoreLaw n
        {x | T < (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount} =
      (uniformProfile n).toMeasure {p | T < (DAState.run p (n * n)).proposalCount} := by
  let E : Set (Profile n) := {p | T < (DAState.run p (n * n)).proposalCount}
  have hp : MeasurePreserving (profileOfScores ∘ @swapScoreSides n) (continuousScoreLaw n)
      (uniformProfile n).toMeasure :=
    (measurePreserving_profileOfScores n).comp (measurePreserving_swapScoreSides n)
  change continuousScoreLaw n ((profileOfScores ∘ @swapScoreSides n) ⁻¹' E) = _
  exact hp.measure_preimage (MeasurableSet.of_discrete (s := E)).nullMeasurableSet

private theorem eventually_proposalCountScoreBound_le_rpow {T : ℕ → ℕ} {C : ℝ}
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ C * n * Real.log n) :
    ∀ᶠ n : ℕ in atTop, 16 * ((T n : ℝ) / n + Real.log n) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 / 5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun n : ℕ ↦ (16 * (C + 1)) *
      (Real.log n / (n : ℝ) ^ (1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlog.const_mul (16 * (C + 1))
  filter_upwards [hT, eventually_gt_atTop (0 : ℕ), hscaled.eventually_lt_const zero_lt_one]
    with n hTn hn hsmall
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdiv : (T n : ℝ) / n ≤ C * Real.log n :=
    (div_le_iff₀ hn₀).mpr (by simpa only [mul_right_comm C] using hTn)
  calc
    16 * ((T n : ℝ) / n + Real.log n) ≤ 16 * (C * Real.log n + Real.log n) := by
      gcongr
    _ = 16 * (C + 1) * Real.log n := by ring
    _ ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← mul_div_assoc] at hsmall
      exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hn₀ _)).mp hsmall).le.trans_eq (one_mul _)

/-- An ordinal proposal-count cap of order n log n, holding with high
probability, puts the woman-optimal score below n^(1/5) with high probability. -/
theorem tendsto_measure_badScoreWalkUpperEndpoint {T : ℕ → ℕ} {C : ℝ}
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ C * n * Real.log n)
    (hcap : Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | T n < (DAState.run p (n * n)).proposalCount}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ continuousScoreLaw n
      {x | (n : ℝ) ^ (1 / 5 : ℝ) < scoreWalkFemaleTotal x (n * (n - 1))}) atTop (𝓝 0) := by
  have hrare : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  have hsum := hrare.add hcap
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_proposalCountScoreBound_le_rpow hT]
    with n hn hsmall
  let E : Set (ScoreProfile n) :=
    {x | T n < (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount}
  let B : Set (ScoreProfile n) := daBadFemaleRankThreshold n ∪ E
  have hsub : {x | (n : ℝ) ^ (1 / 5 : ℝ) < scoreWalkFemaleTotal x (n * (n - 1))} ≤ᵐ[
      continuousScoreLaw n] B := by
    filter_upwards [ae_injective_rows n] with x hx hbad
    by_contra hgood
    have hx₁ : x ∉ daBadFemaleRankThreshold n := fun h ↦ hgood (Or.inl h)
    have hx₂ : (DAState.run (swapProfile (profileOfScores x)) (n * n)).proposalCount ≤ T n :=
      le_of_not_gt fun h ↦ hgood (Or.inr h)
    exact not_lt_of_ge
      ((scoreWalkFemaleTotal_horizon_le_of_proposalCount hn (fun w ↦ hx (.inr w)) hx₁ hx₂).trans
        hsmall) hbad
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
  exact add_le_add (measure_daBadFemaleRankThreshold_le hn) (measure_swapDAProposalCount_gt n _).le

end LennonPittelFormalization

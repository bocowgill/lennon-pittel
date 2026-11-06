module

public import LennonPittel.PivotForwardForest
public import LennonPittel.PivotMarkedCutoffBridge
public import LennonPittel.PivotSpouseSquareRegularity
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Exponential tilt for heavy forward-cycle supports

At a fixed marked diagonal, forward arcs are bounded by the female weight
of their target, up to a common multiplicative slack. Tilting each target
weight by the exponential of its normalized male weight bounds the mass
of cycles whose support has unusually large male weight.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

private theorem exp_le_one_add_two_mul {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    Real.exp t ≤ 1 + 2 * t := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (show 0 ≤ 1 - t by linarith) ht (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  nlinarith only [h, mul_nonneg ht (sub_nonneg.mpr Real.exp_one_lt_three.le)]

/-- The total of the tilted weights costs at most twice the mixed first moment. -/
theorem sum_expTilt_le {ι : Type*} [Fintype ι] {p r : ι → ℝ} {θ : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    (ht : ∀ i, 0 ≤ θ * r i ∧ θ * r i ≤ 1) :
    (∑ i, p i * Real.exp (θ * r i)) ≤ 1 + 2 * θ * ∑ i, p i * r i := by
  calc
    _ ≤ ∑ i, p i * (1 + 2 * (θ * r i)) := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (exp_le_one_add_two_mul (ht i).1 (ht i).2) (hp i)
    _ = _ := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hp₁]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The exponential cutoff at a positive power beats any fixed inverse power. -/
theorem eventually_exp_neg_size_rpow_le (a q : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ a)) ≤ (n : ℝ) ^ (-q) := by
  have hlog := (((isLittleO_log_rpow_atTop ha).const_mul_left q).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog] with n hn h
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |q * Real.log n| ≤ |(n : ℝ) ^ a| := h
  rw [abs_of_nonneg (Real.rpow_nonneg hnR.le _)] at habs
  rw [show (n : ℝ) ^ (-q) = Real.exp (Real.log n * -q) from Real.rpow_def_of_pos hnR _]
  apply Real.exp_le_exp.mpr
  linarith only [(le_abs_self (q * Real.log n)).trans habs]

/-- The inverse-power estimate for the tilted mass of cycles of any
fixed length within the square-root cutoff. -/
theorem eventually_supportMassTilt_pow_mul_le {A H R : ℝ}
    (hH : 0 ≤ H) (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt n →
      ∀ (p r : Fin n → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
        (∀ i, 0 ≤ r i ∧ r i ≤ R * Real.log n / n) → (∑ i, p i * r i) ≤ H / n →
      Real.exp (-((n : ℝ) ^ (3 / 4 : ℝ)) *
          (((1 + 2 * H) * A + 1) / Real.sqrt n)) *
        ((1 + coexposureSuccessorPerturbation n) *
          ∑ i, p i * Real.exp ((n : ℝ) ^ (3 / 4 : ℝ) * r i)) ^ k ≤ (n : ℝ) ^ (-q) := by
  have hlog := (((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left
    R).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds, hlog,
    eventually_exp_neg_size_rpow_le (1 / 4) q (by norm_num)] with n hn hl hdecay
  intro k hk p r hp hp₁ hr hpr
  let x : ℝ := n
  let t : ℝ := x ^ (1 / 4 : ℝ)
  let θ : ℝ := x ^ (3 / 4 : ℝ)
  let s : ℝ := Real.sqrt x
  let B : ℝ := (1 + 2 * H) * A + 1
  let δ := coexposureSuccessorPerturbation n
  have hx : 0 < x := Nat.cast_pos.mpr hn.1
  have ht : 0 < t := Real.rpow_pos_of_pos hx _
  have hθ : 0 < θ := Real.rpow_pos_of_pos hx _
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have ht₁ : 1 ≤ t := Real.one_le_rpow (Nat.one_le_cast.mpr hn.1) (by norm_num)
  have hθt : θ * t = x := by
    dsimp [θ, t]
    rw [← Real.rpow_add hx, show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have htt : t * t = s := by
    dsimp [t, s]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have hst : s * t = θ := by
    dsimp [s, t, θ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have hlog' : R * Real.log x ≤ t := by
    have ha : |R * Real.log x| ≤ |t| := hl
    rw [abs_of_pos ht] at ha
    exact (le_abs_self _).trans ha
  have hscale : θ / x = 1 / t := by
    rw [← hθt]
    field_simp
  have hδ : δ ≤ 1 / t := by
    refine hn.2.2.1.trans (one_div_le_one_div_of_le ht ?_)
    change t ≤ s
    rw [← htt]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht₁ ht.le
  have htilt : ∀ i, 0 ≤ θ * r i ∧ θ * r i ≤ 1 := by
    intro i
    refine ⟨mul_nonneg hθ.le (hr i).1, ?_⟩
    calc
      _ ≤ θ * (R * Real.log x / x) := mul_le_mul_of_nonneg_left (hr i).2 hθ.le
      _ ≤ θ * (t / x) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hlog' hx.le) hθ.le
      _ = 1 := by rw [← mul_div_assoc, hθt, div_self hx.ne']
  have hsum : (∑ i, p i * Real.exp (θ * r i)) ≤ 1 + 2 * H / t := by
    refine (sum_expTilt_le hp hp₁ htilt).trans ?_
    calc
      _ ≤ 1 + 2 * θ * (H / x) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hpr (mul_nonneg (by norm_num) hθ.le)) _
      _ = _ := by rw [show 2 * θ * (H / x) = (2 * H) * (θ / x) by ring, hscale]; ring
  have hsumExp : (∑ i, p i * Real.exp (θ * r i)) ≤ Real.exp (2 * H / t) :=
    hsum.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * H / t))
  have hdExp : 1 + δ ≤ Real.exp (1 / t) :=
    (add_le_add_right hδ 1).trans (by simpa only [add_comm] using Real.add_one_le_exp (1 / t))
  have hbase : (1 + δ) * (∑ i, p i * Real.exp (θ * r i)) ≤
      Real.exp ((1 + 2 * H) / t) := by
    rw [add_div, Real.exp_add]
    exact mul_le_mul hdExp hsumExp
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hbase₀ : 0 ≤ (1 + δ) * (∑ i, p i * Real.exp (θ * r i)) :=
    mul_nonneg (by linarith only [hn.2.1])
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (Real.exp_pos _).le)
  change Real.exp (-θ * (B / s)) *
    ((1 + δ) * ∑ i, p i * Real.exp (θ * r i)) ^ k ≤ _
  calc
    _ ≤ Real.exp (-θ * (B / s)) * Real.exp ((1 + 2 * H) / t) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase₀ hbase _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsDiv : s / t = t := by rw [← htt, mul_div_cancel_right₀ _ ht.ne']
      have hθDiv : θ / s = t := by rw [← hst, mul_comm, mul_div_cancel_right₀ _ hs.ne']
      have hK : (k : ℝ) * ((1 + 2 * H) / t) ≤ ((1 + 2 * H) * A) * t := by
        calc
          _ ≤ (A * s) * ((1 + 2 * H) / t) :=
            mul_le_mul_of_nonneg_right hk (div_nonneg (by positivity) ht.le)
          _ = _ := by
            rw [show A * s * ((1 + 2 * H) / t) = ((1 + 2 * H) * A) * (s / t) by ring, hsDiv]
      rw [show -θ * (B / s) = -B * (θ / s) by ring, hθDiv]
      dsimp [B]
      linarith only [hK]
    _ ≤ _ := hdecay

/-- The normalized male spouse score indexed by its man at the marked diagonal. -/
noncomputable def pivotSupportMaleWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).1 / reverseDiagonalMaleTotal d

theorem measurable_pivotSupportMaleWeight {n : ℕ} (i : Fin n) :
    Measurable fun d : DiagonalScorePairs n ↦ pivotSupportMaleWeight d i := by
  have hcoord (j : Fin n) : Measurable fun d : DiagonalScorePairs n ↦ (diagonalPairAt d j).1 :=
    measurable_fst.comp (measurable_pi_apply _)
  exact (hcoord i).div (Finset.measurable_sum _ fun j _ ↦ hcoord j)

theorem pivotSupportMaleWeight_splitScorePairs {n : ℕ}
    (x : ScoreProfile n) (μ : Matching n) (i : Fin n) :
    pivotSupportMaleWeight (splitScorePairs μ x).1 i =
      maleSpouseScore x μ i / maleSpouseTotal x μ := by
  simp only [pivotSupportMaleWeight, reverseDiagonalMaleTotal, diagonalPairAt_splitScorePairs,
    maleSpouseScore, maleSpouseTotal]

theorem forwardSpouseWeight_splitScorePairs {n : ℕ}
    (x : ScoreProfile n) (μ : Matching n) (i : Fin n) :
    forwardSpouseWeight (splitScorePairs μ x).1 i =
      femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
  rw [femaleSpouseTotal_eq_sum_byHusband μ x]
  simp only [forwardSpouseWeight, diagonalPairAt_splitScorePairs, femaleSpouseByHusband,
    femaleSpouseScore, Equiv.symm_apply_apply]

/-- The all-stable score regularity event supplies the local mixed weight bound. -/
theorem sum_diagonalSpouseWeights_mul_le_of_goodPivotScoreGeometry {n : ℕ} (hn : 0 < n)
    {x : ScoreProfile n} (hx : x ∈ goodPivotScoreGeometry n) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ) :
    (∑ i, forwardSpouseWeight (splitScorePairs μ x).1 i *
      pivotSupportMaleWeight (splitScorePairs μ x).1 i) ≤ 24 / (n : ℝ) := by
  simpa only [pivotSupportMaleWeight_splitScorePairs, forwardSpouseWeight_splitScorePairs] using
    sum_spouseShares_mul_le_of_goodPivotScoreGeometry hn hx μ hμ

/-- On a base-band diagonal the male and female shares meet the hypotheses
of the exponential tilt, provided the mixed budget is at most `24 / n`. -/
theorem eventually_diagonalSupportMassTilt_pow_mul_le (A q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt n →
      ∀ d ∈ pivotBaseDiagonalBand n,
        (∑ i, forwardSpouseWeight d i * pivotSupportMaleWeight d i) ≤ 24 / (n : ℝ) →
      Real.exp (-((n : ℝ) ^ (3 / 4 : ℝ)) * ((49 * A + 1) / Real.sqrt n)) *
        ((1 + coexposureSuccessorPerturbation n) * ∑ i,
          forwardSpouseWeight d i *
            Real.exp ((n : ℝ) ^ (3 / 4 : ℝ) * pivotSupportMaleWeight d i)) ^ k ≤
        (n : ℝ) ^ (-q) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_supportMassTilt_pow_mul_le (A := A) (H := 24) (R := 2048) (by norm_num) q]
    with n hn h
  intro k hk d hd hmix
  have hY : 0 < pivotDiagonalFemaleTotal d :=
    (by norm_num : (0 : ℝ) < 2).trans_le hd.2.1
  have hXY := hd.2.2.2.1
  have hXY₀ : 0 < reverseDiagonalMaleTotal d * pivotDiagonalFemaleTotal d :=
    (div_pos (Nat.cast_pos.mpr hn) (by norm_num : (0 : ℝ) < 128)).trans_le hXY
  have hX : 0 < reverseDiagonalMaleTotal d := pos_of_mul_pos_left hXY₀ hY.le
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hd.1 i).2.1 hY.le
  have hp₁ : ∑ i, forwardSpouseWeight d i = 1 := by
    simp only [forwardSpouseWeight, ← Finset.sum_div]
    exact div_self hY.ne'
  have hr (i : Fin n) :
      0 ≤ pivotSupportMaleWeight d i ∧ pivotSupportMaleWeight d i ≤ 2048 * Real.log n / n :=
    ⟨div_nonneg (hd.1 i).1.1 hX.le,
      normalizedMaleScore_le_of_spouseProduct hn hd.2.1 hXY (hd.2.2.2.2.2 i)⟩
  simpa only [show (1 + 2 * 24 : ℝ) = 49 by norm_num] using h k hk _ _ hp hp₁ hr hmix

/-- Conditional on a base-band diagonal, a heavy exposed cycle of a fixed
length within the square-root cutoff has arbitrarily small inverse-power mass. -/
theorem eventually_measure_pi_heavyForwardSupport_length_le (A q : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt n →
      ∀ d ∈ pivotBaseDiagonalBand n,
        (∑ i, forwardSpouseWeight d i * pivotSupportMaleWeight d i) ≤ 24 / (n : ℝ) →
      Measure.pi (normalizedStableScoreRowLaw d)
        {y : OffDiagonalScoreRows n |
          ∃ σ : Matching n,
            RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (y i)) σ ∧
            σ.support.card = k ∧
            (49 * A + 1) / Real.sqrt n < ∑ i ∈ σ.support, pivotSupportMaleWeight d i} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds,
    eventually_diagonalSupportMassTilt_pow_mul_le A q] with n hn htilt
  intro k hk d hd hmix
  let θ := (n : ℝ) ^ (3 / 4 : ℝ)
  let B := (49 * A + 1) / Real.sqrt (n : ℝ)
  let c := 1 + coexposureSuccessorPerturbation n
  let p := forwardSpouseWeight d
  let r := pivotSupportMaleWeight d
  have hθ : 0 < θ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn.1) _
  have hc : 0 < c := by dsimp [c]; linarith only [hn.2.1]
  have hY : 0 < pivotDiagonalFemaleTotal d := (by norm_num : (0 : ℝ) < 2).trans_le hd.2.1
  have hX : 0 < reverseDiagonalMaleTotal d :=
    pos_of_mul_pos_left (lt_of_lt_of_le (div_pos (Nat.cast_pos.mpr hn.1)
      (by norm_num : (0 : ℝ) < 128)) hd.2.2.2.1) hY.le
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hd.1 i).2.1 hY.le
  have hr (i : Fin n) : 0 ≤ r i := div_nonneg (hd.1 i).1.1 hX.le
  have hp₁ : ∑ i, p i = 1 := by
    simp only [p, forwardSpouseWeight, ← Finset.sum_div]
    exact div_self hY.ne'
  let w (j : Fin n) := ENNReal.ofReal (c * (p j * Real.exp (θ * r j)))
  have hw : ∑ j, w j = ENNReal.ofReal (c * ∑ j, p j * Real.exp (θ * r j)) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    exact fun j _ ↦ mul_nonneg hc.le (mul_nonneg (hp j) (Real.exp_nonneg _))
  have hw₀ : (∑ j, w j) ≠ 0 := by
    have hh : 1 ≤ ∑ j, p j * Real.exp (θ * r j) := by
      rw [← hp₁]
      exact Finset.sum_le_sum fun j _ ↦ le_mul_of_one_le_right (hp j)
        (Real.one_le_exp (mul_nonneg hθ.le (hr j)))
    rw [hw]
    exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hc (zero_lt_one.trans_le hh))
  have hwt : (∑ j, w j) ≠ ∞ := by rw [hw]; exact ENNReal.ofReal_ne_top
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  let ν := normalizedStableScoreRowLaw d
  let out := forwardSuccessorOutcome d
  let g (i j : Fin n) (_ : {l : Fin n // i ≠ l} → ℝ × ℝ) := θ * r j
  have hx (i : Fin n) := (hd.1 i).1
  have hy (i : Fin n) : (diagonalPairAt d i).2 ∈ Icc 0 1 :=
    ⟨(hd.1 i).2.1, (hd.1 i).2.2.le⟩
  have hg : d ∈ goodDiagonalScores n := ⟨hd.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩
  let (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  have hout (i : Fin n) : Measurable (out i) := measurable_forwardSuccessorOutcome d i
  have harc (i j : Fin n) (hij : i ≠ j) :
      (∫⁻ x, tiltedForwardArc out g i j x ∂ν i) ≤ w j := by
    let E := {x | out i x = some j}
    have hE : MeasurableSet E := measurableSet_eq_fun (hout i) measurable_const
    have hM : ν i E ≤ ENNReal.ofReal (c * p j) := by
      have hmap : forwardSuccessorOutcomeLaw d i {some j} = ν i E :=
        Measure.map_apply (hout i) (measurableSet_singleton _)
      have hR : (ν i E).toReal ≤ c * p j := by
        rw [← hmap]
        exact forwardOutcomeWeight_some_le_of_goodDiagonalScores hg hx hy hn.2.2.2.1
          hn.2.2.2.2.1 hn.2.2.2.2.2 i ⟨j, hij⟩
      simpa only [ENNReal.ofReal_toReal (measure_ne_top (ν i) E)] using
        ENNReal.ofReal_le_ofReal hR
    change (∫⁻ x, E.indicator (fun _ ↦ ENNReal.ofReal (Real.exp (θ * r j))) x ∂ν i) ≤
      w j
    rw [lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (θ * r j)) * ENNReal.ofReal (c * p j) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        ring
  have hsub :
      {y : OffDiagonalScoreRows n |
        ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
          σ.support.card = k ∧ B < ∑ i ∈ σ.support, r i} ⊆
      {y : OffDiagonalScoreRows n |
        ∃ σ : Matching n, RealizesDirectedCycle (fun i ↦ out i (y i)) σ ∧
          σ.support.card = k ∧ θ * B < ∑ i ∈ σ.support, g i (σ i) (y i)} := by
    rintro y ⟨σ, hσ, hk', hmass⟩
    refine ⟨σ, hσ, hk', ?_⟩
    change θ * B < ∑ i ∈ σ.support, θ * r (σ i)
    rw [← Finset.mul_sum, σ.sum_comp σ.support r (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi)]
    exact mul_lt_mul_of_pos_left hmass hθ
  refine (measure_mono hsub).trans ((measure_pi_exists_cycle_length_sum_gt_le ν out g hout
    (fun _ _ ↦ measurable_const) w hw₀ hwt harc k (θ * B)).trans ?_)
  rw [hw, ← ENNReal.ofReal_pow (mul_nonneg hc.le
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (Real.exp_nonneg _))),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← neg_mul]
  exact ENNReal.ofReal_le_ofReal (htilt k hk d hd hmix)

end LennonPittelFormalization

module

public import LennonPittel.CoexposureMomentObstruction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The exponent gap in the co-exposure obstruction

The integer inequality `2 ^ 11 ≤ 3 ^ 7` turns a linear lower bound on the
Lennon–Pittel threshold into a lower bound of order `n ^ (11 / 7)` on the
Markov denominator. This module proves the limiting comparison from stated
growth bounds, without assuming that Pittel's mean theorem has been formalized.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

private theorem two_rpow_le_three : (2 : ℝ) ^ (11 / 7 : ℝ) ≤ 3 := by
  calc
    _ = ((2 : ℝ) ^ (11 : ℕ)) ^ (1 / 7 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num)]
      congr 1
      norm_num
    _ ≤ ((3 : ℝ) ^ (7 : ℕ)) ^ (1 / 7 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by norm_num) (by norm_num)
    _ = 3 := by
      rw [← Real.rpow_natCast_mul (by norm_num), show (↑(7 : ℕ) : ℝ) * (1 / 7) = 1 by norm_num,
        Real.rpow_one]

/-- The base-three Markov denominator grows at least as the (11/7)th power
of the target when the base-two threshold inequality holds. -/
theorem rpow_le_three_pow_of_le_two_pow {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hk : t ≤ (2 : ℝ) ^ k) : t ^ (11 / 7 : ℝ) ≤ (3 : ℝ) ^ k := by
  calc
    _ ≤ ((2 : ℝ) ^ k) ^ (11 / 7 : ℝ) := Real.rpow_le_rpow ht hk (by norm_num)
    _ = ((2 : ℝ) ^ (11 / 7 : ℝ)) ^ k := by
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) two_rpow_le_three k

/-- A linear target and a weighted moment of order at most (n^rlog n)
for (r<11/7) force the normalized Markov term to vanish. -/
theorem tendsto_coexposure_normalized_weight_of_growth (W : ℕ → ℝ≥0∞) {c C r : ℝ}
    (hc : 0 < c) (hr : r < 11 / 7)
    (htarget : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ≤ reciprocalLogTolerance n * expectedNumStableMatchings n)
    (hweight : ∀ᶠ n : ℕ in atTop, W n ≤ ENNReal.ofReal (C * (n : ℝ) ^ r * Real.log n)) :
    Tendsto (fun n ↦ W n / (3 : ℝ≥0∞) ^ coexposedRotationThreshold reciprocalLogTolerance n)
      atTop (𝓝 0) := by
  let q : ℝ := 11 / 7
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (q - r)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hr)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hupper :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C / c ^ q * (Real.log n / (n : ℝ) ^ (q - r))))
        atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hlog)
  refine tendsto_const_nhds.squeeze' hupper (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [htarget, hweight, eventually_gt_atTop (0 : ℕ)] with n ht hw hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden :
      c ^ q * (n : ℝ) ^ q ≤ (3 : ℝ) ^ coexposedRotationThreshold reciprocalLogTolerance n :=
    calc
      _ = (c * (n : ℝ)) ^ q := (Real.mul_rpow hc.le hn'.le).symm
      _ ≤ _ := rpow_le_three_pow_of_le_two_pow (by positivity)
        (ht.trans (coexposedRotationThreshold_spec reciprocalLogTolerance n))
  have hden' :
      ENNReal.ofReal (c ^ q * (n : ℝ) ^ q) ≤
        (3 : ℝ≥0∞) ^ coexposedRotationThreshold reciprocalLogTolerance n := by
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3),
      show ENNReal.ofReal (3 : ℝ) = 3 by norm_num] using ENNReal.ofReal_le_ofReal hden
  calc
    _ ≤ ENNReal.ofReal (C * (n : ℝ) ^ r * Real.log n) /
        ENNReal.ofReal (c ^ q * (n : ℝ) ^ q) := ENNReal.div_le_div hw hden'
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity), Real.rpow_sub hn']
      congr 1
      field_simp

/-- A positive limit for the mean divided by (n\log n) gives the linear
target lower bound and a mean upper bound. The asymptotic is an input. -/
theorem eventual_target_lower_and_mean_upper_of_tendsto {a : ℝ} (ha : 0 < a)
    (hmean : Tendsto
      (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n)) atTop (𝓝 a)) :
    (∀ᶠ n : ℕ in atTop,
      (a / 4) * (n : ℝ) ≤ reciprocalLogTolerance n * expectedNumStableMatchings n) ∧
      (∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤ (2 * a) * ((n : ℝ) * Real.log n)) := by
  have hlow := (tendsto_order.mp hmean).1 (a / 2) (by linarith)
  have hhigh := (tendsto_order.mp hmean).2 (2 * a) (by linarith)
  have hpos (n : ℕ) (hn : 2 ≤ n) : 1 < (n : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  constructor
  · filter_upwards [hlow, eventually_ge_atTop (2 : ℕ)] with n hn hn₂
    have hn₂' : (2 : ℝ) ≤ n := by exact_mod_cast hn₂
    have hpoly : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n :=
      calc
        _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) hpoly
        _ = _ := by norm_num [Real.log_pow]
    rw [reciprocalLogTolerance, inv_mul_eq_div]
    apply (le_div_iff₀ (Real.log_pos (by linarith))).mpr
    calc
      _ ≤ (a / 4 * (n : ℝ)) * (2 * Real.log n) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (a / 2) * ((n : ℝ) * Real.log n) := by ring
      _ ≤ _ := ((lt_div_iff₀ (mul_pos (by positivity) (Real.log_pos (hpos n hn₂)))).mp hn).le
  · filter_upwards [hhigh, eventually_ge_atTop (2 : ℕ)] with n hn hn₂
    exact ((div_lt_iff₀ (mul_pos (by positivity) (Real.log_pos (hpos n hn₂)))).mp hn).le

/-- The normalized weighted moment vanishes if the weighted count grows at most
as the mean times (n^s), for (s<4/7), and the normalized mean has a positive limit. -/
theorem tendsto_coexposure_normalized_weight_of_mean_asymptotic (W : ℕ → ℝ≥0∞)
    {a C s : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hs : s < 4 / 7)
    (hmean : Tendsto
      (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n)) atTop (𝓝 a))
    (hweight : ∀ᶠ n : ℕ in atTop,
      W n ≤ ENNReal.ofReal (C * (n : ℝ) ^ s * expectedNumStableMatchings n)) :
    Tendsto (fun n ↦ W n / (3 : ℝ≥0∞) ^ coexposedRotationThreshold reciprocalLogTolerance n)
      atTop (𝓝 0) := by
  obtain ⟨hlower, hupper⟩ := eventual_target_lower_and_mean_upper_of_tendsto ha hmean
  refine tendsto_coexposure_normalized_weight_of_growth W (C := C * (2 * a)) (r := s + 1)
    (by positivity) (by linarith) hlower ?_
  filter_upwards [hweight, hupper, eventually_gt_atTop (0 : ℕ)] with n hw hm hn
  refine hw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ C * (n : ℝ) ^ s * ((2 * a) * ((n : ℝ) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      rw [Real.rpow_add (Nat.cast_pos.mpr hn), Real.rpow_one]
      ring

/-- The exceptional-score and weighted-growth estimates, together with a
positive normalized-mean limit, imply the zero co-exposure limit. -/
theorem tendsto_uniformProfile_coexposure_zero_of_weight_growth
    (G : ∀ n, Set (ScoreProfile n)) (hG : ∀ n, MeasurableSet (G n))
    {a C s : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hs : s < 4 / 7)
    (hmean : Tendsto
      (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n)) atTop (𝓝 a))
    (hbad : Tendsto (fun n ↦ continuousScoreLaw n (G n)ᶜ) atTop (𝓝 0))
    (hweight : ∀ᶠ n : ℕ in atTop,
      (∫⁻ x, scoreCoexposureWeight n (G n) x ∂(continuousScoreLaw n)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ s * expectedNumStableMatchings n)) :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | HasCoexposedRotations p (coexposedRotationThreshold reciprocalLogTolerance n)})
      atTop (𝓝 0) :=
  tendsto_uniformProfile_coexposure_zero_of_score_moment _ G hG hbad
    (tendsto_coexposure_normalized_weight_of_mean_asymptotic _ ha hC hs hmean hweight)

end LennonPittelFormalization

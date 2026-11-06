module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Tactic.NormNum

/-!
# Expected loss from a rare filter event

Cauchy–Schwarz controls the expected count removed by an event using only
its mass and a second moment of the original count.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LennonPittelFormalization

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first moment restricted to an event is at most the square root of
its mass times the square root of the full second moment. -/
theorem lintegral_restrict_le_rpow_measure_mul_secondMoment (μ : Measure Ω) (E : Set Ω)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x in E, f x ∂μ) ≤ (μ E) ^ (1 / 2 : ℝ) *
      (∫⁻ x, f x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ (μ E) ^ (1 / 2 : ℝ) *
        (∫⁻ x in E, f x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
      simpa only [Pi.mul_apply, one_mul, one_pow, lintegral_const,
        Measure.restrict_apply_univ, ENNReal.rpow_two] using
        ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict E) (p := 2) (q := 2)
          (Real.holderConjugate_iff.mpr (by norm_num)) (f := fun _ ↦ 1)
          measurable_const.aemeasurable hf.aemeasurable
    _ ≤ _ := mul_le_mul_right
      (ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl) (by norm_num)) _

/-- When the event mass and second moment both contain the same mass factor,
it appears to the first power in the bound on the restricted first moment. -/
theorem lintegral_restrict_le_mass_mul_filterLoss (μ : Measure Ω) (E : Set Ω)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) {c p M : ℝ≥0∞} (hE : μ E ≤ c * p)
    (hM : (∫⁻ x, f x ^ (2 : ℕ) ∂μ) ≤ c * M) :
    (∫⁻ x in E, f x ∂μ) ≤ c * p ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ (μ E) ^ (1 / 2 : ℝ) * (∫⁻ x, f x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) :=
      lintegral_restrict_le_rpow_measure_mul_secondMoment μ E hf
    _ ≤ (c * p) ^ (1 / 2 : ℝ) * (c * M) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hE (by norm_num)) (ENNReal.rpow_le_rpow hM (by norm_num))
    _ = _ := by
      have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have hcs : c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hhalf hhalf,
          show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
          ENNReal.rpow_one]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ENNReal.mul_rpow_of_nonneg _ _ hhalf]
      calc
        _ = (c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ)) * p ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) :=
          by ac_rfl
        _ = _ := by rw [hcs]

/-- A tail of order `n⁻⁷` and a second moment of order `n * √n` give a
loss coefficient bounded by `√C / n²` for `n ≥ 1`. -/
theorem filterLossFactor_le_sqrt_div_sq (n C : ℝ) (hn : 1 ≤ n) (hC : 0 ≤ C) :
    ENNReal.ofReal (n ^ (-7 : ℝ)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (C * n * Real.sqrt n) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt C / n ^ (2 : ℕ)) := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hp : 0 ≤ n ^ (-7 : ℝ) := Real.rpow_nonneg hnpos.le _
  have hM : 0 ≤ C * n * Real.sqrt n := mul_nonneg (mul_nonneg hC hnpos.le) (Real.sqrt_nonneg _)
  have hh : 0 ≤ (1 / 2 : ℝ) := by norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg hp hh, ENNReal.ofReal_rpow_of_nonneg hM hh,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hp _)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.sqrt_eq_rpow n, Real.mul_rpow (mul_nonneg hC hnpos.le) (Real.rpow_nonneg hnpos.le _),
    Real.mul_rpow hC hnpos.le, ← Real.rpow_mul hnpos.le (-7), ← Real.rpow_mul hnpos.le (1 / 2),
    Real.sqrt_eq_rpow C]
  calc
    _ = C ^ (1 / 2 : ℝ) * (n ^ ((-7 : ℝ) * (1 / 2)) * n ^ (1 / 2 : ℝ) *
        n ^ ((1 / 2 : ℝ) * (1 / 2))) := by ac_rfl
    _ = C ^ (1 / 2 : ℝ) * n ^ (-11 / 4 : ℝ) := by
      rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      norm_num
    _ ≤ C ^ (1 / 2 : ℝ) * n ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (by norm_num))
        (Real.rpow_nonneg hC _)
    _ = _ := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_two]
      exact (div_eq_mul_inv _ _).symm

/-- A convenient finite-scale bound on a count lost to an event with relative
mass at most `n⁻⁷`. The full second moment retains the same mass factor. -/
theorem lintegral_restrict_le_mass_mul_sqrt_div_sq (μ : Measure Ω) (E : Set Ω)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) {c : ℝ≥0∞} {n C : ℝ}
    (hn : 1 ≤ n) (hC : 0 ≤ C) (hE : μ E ≤ c * ENNReal.ofReal (n ^ (-7 : ℝ)))
    (hM : (∫⁻ x, f x ^ (2 : ℕ) ∂μ) ≤ c * ENNReal.ofReal (C * n * Real.sqrt n)) :
    (∫⁻ x in E, f x ∂μ) ≤ c * ENNReal.ofReal (Real.sqrt C / n ^ (2 : ℕ)) := by
  exact (lintegral_restrict_le_mass_mul_filterLoss μ E hf hE hM).trans
    (by rw [mul_assoc]; exact mul_le_mul_right (filterLossFactor_le_sqrt_div_sq n C hn hC) c)

end LennonPittelFormalization

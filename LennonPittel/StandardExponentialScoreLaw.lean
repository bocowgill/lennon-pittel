module

public import Mathlib.Probability.Distributions.Exponential

/-!
# Integrals for the rate-one exponential law
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LennonPittelFormalization

private theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl

private theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

private theorem lintegral_expMeasure_one (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂expMeasure 1) = ∫⁻ x, exponentialPDF 1 x * f x :=
  lintegral_withDensity_eq_lintegral_mul volume (measurable_exponentialPDF 1) hf

/-- The rate-one exponential law is supported on the nonnegative reals. -/
theorem ae_expMeasure_one_nonneg : ∀ᵐ x ∂expMeasure 1, 0 ≤ x := by
  rw [ae_iff, expMeasure_eq_withDensity]
  simp only [not_le]
  change volume.withDensity (exponentialPDF 1) (Iio 0) = 0
  rw [withDensity_apply _ measurableSet_Iio, lintegral_exponentialPDF_of_nonpos le_rfl]

/-- The upper tail of a rate-one exponential variable is exponential. -/
theorem expMeasure_one_Ioi {L : ℝ} (hL : 0 ≤ L) :
    expMeasure 1 (Ioi L) = ENNReal.ofReal (Real.exp (-L)) := by
  rw [expMeasure_eq_withDensity, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun (g := fun x ↦ ENNReal.ofReal (Real.exp (-x))) measurableSet_Ioi
      (fun x hx ↦ by simp [exponentialPDF_of_nonneg (hL.trans hx.le)])]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi L)
    (ae_of_all _ fun x ↦ (Real.exp_pos (-x)).le), integral_exp_neg_Ioi]

/-- The second moment of a rate-one exponential variable is two. -/
theorem lintegral_expMeasure_one_sq :
    (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂expMeasure 1) = (2 : ℝ≥0∞) := by
  rw [lintegral_expMeasure_one _ (by fun_prop)]
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (x ^ 2) = 2 * gammaPDF 3 1 x := by
    by_cases hx : 0 ≤ x
    · have hGamma : Real.Gamma 3 = 2 := by
        norm_num [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
          Nat.factorial]
      rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      norm_num [hGamma, Real.rpow_two]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  have hγ : Measurable (gammaPDF 3 1) := (measurable_gammaPDFReal 3 1).ennreal_ofReal
  rw [lintegral_const_mul _ hγ,
    lintegral_gammaPDF_eq_one (by norm_num) (by norm_num), mul_one]

/-- The negative exponential moment of a rate-one exponential variable is one half. -/
theorem lintegral_expMeasure_one_exp_neg :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂expMeasure 1) = (1 / 2 : ℝ≥0∞) := by
  rw [lintegral_expMeasure_one _ (by fun_prop)]
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (Real.exp (-x)) =
        ENNReal.ofReal (1 / 2) * exponentialPDF 2 x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      congr 1
      simp only [one_mul, ← Real.exp_add]
      rw [show -x + -x = -(2 * x) by ring]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  rw [lintegral_const_mul _ (measurable_exponentialPDF 2),
    lintegral_exponentialPDF_eq_one (by norm_num), mul_one,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

end LennonPittelFormalization

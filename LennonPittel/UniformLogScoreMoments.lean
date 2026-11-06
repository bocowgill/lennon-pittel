module

public import LennonPittel.CoexposureScoreProduct
public import LennonPittel.StandardExponentialScoreLaw
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Variance

/-!
# Logarithmic moments of uniform unit scores

The negative log of a uniform unit score has the rate-one exponential law.
Its first and second moments yield the centering and variance of the score increment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem ae_unitScoreLaw_mem_Icc : ∀ᵐ u ∂unitScoreLaw, u ∈ Icc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

private theorem ae_unitScoreLaw_pos : ∀ᵐ u ∂unitScoreLaw, 0 < u := by
  filter_upwards [ae_unitScoreLaw_mem_Icc, unitScoreLaw.ae_ne 0] with u hu hu0
  exact lt_of_le_of_ne hu.1 hu0.symm

private theorem ae_negLog_unitScoreLaw_nonneg :
    0 ≤ᵐ[unitScoreLaw] fun u ↦ -Real.log u := by
  filter_upwards [ae_unitScoreLaw_mem_Icc] with u hu
  exact neg_nonneg.mpr (Real.log_nonpos hu.1 hu.2)

/-- A negative log sends the uniform unit score law to the rate-one exponential law. -/
theorem measurePreserving_negLog_unitScoreLaw :
    MeasurePreserving (fun u : ℝ ↦ -Real.log u) unitScoreLaw (expMeasure 1) := by
  have hm : Measurable (fun u : ℝ ↦ -Real.log u) := Real.measurable_log.neg
  refine ⟨hm, Measure.ext_of_Iic _ _ (fun a ↦ ?_)⟩
  rw [Measure.map_apply hm measurableSet_Iic]
  have hCDF : expMeasure 1 (Iic a) =
      ENNReal.ofReal (if 0 ≤ a then 1 - Real.exp (-a) else 0) := by
    change volume.withDensity (exponentialPDF 1) (Iic a) = _
    rw [withDensity_apply _ measurableSet_Iic,
      lintegral_exponentialPDF_eq_antiDeriv (by norm_num), one_mul]
  rw [hCDF]
  by_cases ha : 0 ≤ a
  · have hpre : (fun u : ℝ ↦ -Real.log u) ⁻¹' Iic a =ᵐ[unitScoreLaw]
        (Iio (Real.exp (-a)))ᶜ := by
      filter_upwards [ae_unitScoreLaw_pos] with u hu
      change (-Real.log u ≤ a) = (¬ u < Real.exp (-a))
      have hneg : -Real.log u ≤ a ↔ -a ≤ Real.log u := by
        constructor <;> intro h <;> linarith
      exact propext (hneg.trans ((Real.le_log_iff_exp_le hu).trans not_lt.symm))
    rw [measure_congr hpre, measure_compl measurableSet_Iio (measure_ne_top _ _), measure_univ,
      unitScoreLaw_Iio_of_mem_Icc ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)⟩,
      ite_eq_left ha, ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  · have hpre : (fun u : ℝ ↦ -Real.log u) ⁻¹' Iic a =ᵐ[unitScoreLaw] (∅ : Set ℝ) := by
      filter_upwards [ae_negLog_unitScoreLaw_nonneg] with u hu
      change (-Real.log u ≤ a) = False
      exact eq_false fun h ↦ ha (hu.trans h)
    rw [measure_congr hpre, measure_empty, ite_eq_right ha, ENNReal.ofReal_zero]

private theorem lintegral_expMeasure_one_id :
    (∫⁻ x, ENNReal.ofReal x ∂expMeasure 1) = 1 := by
  have hPDF : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [show expMeasure (1 : ℝ) = volume.withDensity (exponentialPDF 1) from rfl,
    lintegral_withDensity_eq_lintegral_mul volume hPDF ENNReal.measurable_ofReal]
  have h (x : ℝ) : exponentialPDF 1 x * ENNReal.ofReal x = gammaPDF 2 1 x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num [mul_comm]
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx), zero_mul]
  exact (lintegral_congr h).trans (lintegral_gammaPDF_eq_one (by norm_num) (by norm_num))

private theorem lintegral_negLog_unitScoreLaw :
    (∫⁻ u, ENNReal.ofReal (-Real.log u) ∂unitScoreLaw) = 1 :=
  (measurePreserving_negLog_unitScoreLaw.lintegral_comp ENNReal.measurable_ofReal).trans
    lintegral_expMeasure_one_id

private theorem lintegral_sq_negLog_unitScoreLaw :
    (∫⁻ u, ENNReal.ofReal ((-Real.log u) ^ 2) ∂unitScoreLaw) = 2 :=
  (measurePreserving_negLog_unitScoreLaw.lintegral_comp
    (show Measurable (fun x : ℝ ↦ ENNReal.ofReal (x ^ 2)) by fun_prop)).trans
      lintegral_expMeasure_one_sq

/-- The negative log of a uniform unit score is integrable. -/
theorem integrable_negLog_unitScoreLaw :
    Integrable (fun u ↦ -Real.log u) unitScoreLaw := by
  refine ⟨Real.measurable_log.neg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal ae_negLog_unitScoreLaw_nonneg, lintegral_negLog_unitScoreLaw]
  exact ENNReal.one_lt_top

/-- The square of the negative log of a uniform unit score is integrable. -/
theorem integrable_sq_negLog_unitScoreLaw :
    Integrable (fun u ↦ (-Real.log u) ^ 2) unitScoreLaw := by
  refine ⟨(Real.measurable_log.neg.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u ↦ sq_nonneg (-Real.log u)),
    lintegral_sq_negLog_unitScoreLaw]
  exact ENNReal.ofNat_lt_top

/-- The negative log of a uniform unit score is square-integrable. -/
theorem memLp_two_negLog_unitScoreLaw :
    MemLp (fun u ↦ -Real.log u) 2 unitScoreLaw :=
  (memLp_two_iff_integrable_sq Real.measurable_log.neg.aestronglyMeasurable).mpr
    integrable_sq_negLog_unitScoreLaw

/-- The negative log of a uniform unit score has mean one. -/
theorem integral_negLog_unitScoreLaw :
    (∫ u, -Real.log u ∂unitScoreLaw) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae ae_negLog_unitScoreLaw_nonneg
    integrable_negLog_unitScoreLaw.aestronglyMeasurable, lintegral_negLog_unitScoreLaw,
    ENNReal.toReal_one]

/-- The negative log of a uniform unit score has second moment two. -/
theorem integral_sq_negLog_unitScoreLaw :
    (∫ u, (-Real.log u) ^ 2 ∂unitScoreLaw) = 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u ↦ sq_nonneg (-Real.log u))
    integrable_sq_negLog_unitScoreLaw.aestronglyMeasurable, lintegral_sq_negLog_unitScoreLaw]
  norm_num

/-- The centered negative log of a uniform unit score is square-integrable. -/
theorem memLp_two_centeredNegLog_unitScoreLaw :
    MemLp (fun u ↦ -Real.log u - 1) 2 unitScoreLaw :=
  memLp_two_negLog_unitScoreLaw.sub (memLp_const 1)

/-- The centered negative log of a uniform unit score has mean zero. -/
theorem integral_centeredNegLog_unitScoreLaw :
    (∫ u, -Real.log u - 1 ∂unitScoreLaw) = 0 := by
  rw [integral_sub integrable_negLog_unitScoreLaw (integrable_const 1),
    integral_negLog_unitScoreLaw, integral_const, probReal_univ, one_smul, sub_self]

/-- The centered negative log of a uniform unit score has mean square one. -/
theorem integral_sq_centeredNegLog_unitScoreLaw :
    (∫ u, (-Real.log u - 1) ^ 2 ∂unitScoreLaw) = 1 := by
  have hpoly (u : ℝ) : (-Real.log u - 1) ^ 2 =
      (-Real.log u) ^ 2 - 2 * (-Real.log u) + 1 := by ring
  have hmul : Integrable (fun u ↦ 2 * (-Real.log u)) unitScoreLaw :=
    integrable_negLog_unitScoreLaw.const_mul 2
  have hsub : Integrable (fun u ↦ (-Real.log u) ^ 2 - 2 * (-Real.log u)) unitScoreLaw :=
    integrable_sq_negLog_unitScoreLaw.sub hmul
  simp_rw [hpoly]
  rw [integral_add hsub (integrable_const 1), integral_sub integrable_sq_negLog_unitScoreLaw hmul,
    integral_sq_negLog_unitScoreLaw, integral_const_mul, integral_negLog_unitScoreLaw,
    integral_const, probReal_univ, one_smul]
  norm_num

section FiniteProduct

variable {ι : Type*}

/-- Centering the total score increment is the same as centering each coordinate. -/
theorem sum_negLog_sub_card_eq_sum_centeredNegLog (s : Finset ι) (u : ι → ℝ) :
    (∑ i ∈ s, -Real.log (u i)) - (s.card : ℝ) =
      ∑ i ∈ s, (-Real.log (u i) - 1) := by
  simp [Finset.sum_sub_distrib, nsmul_eq_mul]

variable [Fintype ι]

local notation "unitScorePi" => Measure.pi (fun _ : ι ↦ unitScoreLaw)
local notation "incrementAt" => fun (i : ι) (u : ι → ℝ) ↦ -Real.log (u i) - 1

private theorem memLp_two_centeredNegLog_eval (i : ι) :
    MemLp (incrementAt i) 2 unitScorePi :=
  memLp_two_centeredNegLog_unitScoreLaw.comp_measurePreserving (measurePreserving_eval _ i)

private theorem integral_centeredNegLog_eval (i : ι) :
    (∫ u, incrementAt i u ∂unitScorePi) = 0 :=
  (integral_comp_eval (μ := fun _ : ι ↦ unitScoreLaw) (i := i)
    memLp_two_centeredNegLog_unitScoreLaw.aestronglyMeasurable).trans
    integral_centeredNegLog_unitScoreLaw

private theorem variance_centeredNegLog_eval (i : ι) :
    variance (incrementAt i) unitScorePi = 1 := by
  rw [variance_of_integral_eq_zero (memLp_two_centeredNegLog_eval i).aemeasurable
    (integral_centeredNegLog_eval i)]
  exact (integral_comp_eval (μ := fun _ : ι ↦ unitScoreLaw) (i := i)
    (show AEStronglyMeasurable (fun u : ℝ ↦ (-Real.log u - 1) ^ 2)
      unitScoreLaw from by fun_prop)).trans integral_sq_centeredNegLog_unitScoreLaw

/-- A finite sum of centered logarithmic increments is square-integrable. -/
theorem memLp_two_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    MemLp (fun u ↦ ∑ i ∈ s, (-Real.log (u i) - 1)) 2 unitScorePi :=
  memLp_finsetSum s fun i _ ↦ memLp_two_centeredNegLog_eval i

/-- The square of the centered logarithmic sum is integrable. -/
theorem integrable_sq_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    Integrable (fun u ↦ (∑ i ∈ s, (-Real.log (u i) - 1)) ^ 2) unitScorePi :=
  (memLp_two_iff_integrable_sq
    (memLp_two_sum_centeredNegLog_unitScoreLaw_pi s).aestronglyMeasurable).mp
      (memLp_two_sum_centeredNegLog_unitScoreLaw_pi s)

/-- A finite sum of centered logarithmic increments has mean zero. -/
theorem integral_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    (∫ u, ∑ i ∈ s, (-Real.log (u i) - 1) ∂unitScorePi) = 0 := by
  rw [integral_finsetSum s (fun i _ ↦ (memLp_two_centeredNegLog_eval i).integrable (by norm_num))]
  exact Finset.sum_eq_zero fun i _ ↦ integral_centeredNegLog_eval i

/-- The centered second moment equals the number of independent score increments. -/
theorem integral_sq_sum_centeredNegLog_unitScoreLaw_pi (s : Finset ι) :
    (∫ u, (∑ i ∈ s, (-Real.log (u i) - 1)) ^ 2 ∂unitScorePi) = (s.card : ℝ) := by
  have hind : iIndepFun incrementAt unitScorePi :=
    iIndepFun_pi (X := fun _ : ι ↦ fun u : ℝ ↦ -Real.log u - 1) (fun _ ↦ by fun_prop)
  have hvar := IndepFun.variance_sum (s := s) (fun i _ ↦ memLp_two_centeredNegLog_eval i)
    (by intro _ _ _ _ hij; exact hind.indepFun hij)
  simp only [variance_centeredNegLog_eval, Finset.sum_const, nsmul_eq_mul, mul_one] at hvar
  have hsum : (∑ i ∈ s, incrementAt i) = fun u ↦ ∑ i ∈ s, (-Real.log (u i) - 1) := by
    funext u
    simp only [Finset.sum_apply]
  rw [hsum, variance_of_integral_eq_zero
    (memLp_two_sum_centeredNegLog_unitScoreLaw_pi s).aemeasurable
    (integral_sum_centeredNegLog_unitScoreLaw_pi s)] at hvar
  exact hvar

end FiniteProduct

end LennonPittelFormalization

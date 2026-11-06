module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Independence.Integration

/-!
# Concentration of a weighted Boolean product

The exponential moment factors across coordinates. The chord bound for
\(e^u\) on \([0,1]\) makes the tail depend only on the mean and the weight cap.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem exp_le_secant_on_unit {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel (1 : ℝ) x)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith

private theorem lintegral_exp_weightedBool_le (ν : Measure Bool) [IsProbabilityMeasure ν]
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (∫⁻ b, ENNReal.ofReal (Real.exp (if b then u else 0)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * u * (ν {true}).toReal)) := by
  have hmass : (ν {true}).toReal + (ν {false}).toReal = 1 := by
    have he := lintegral_fintype (μ := ν) (fun _ : Bool ↦ (1 : ℝ≥0∞))
    simp only [lintegral_const, measure_univ, mul_one, Fintype.sum_bool, one_mul] at he
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← he, ENNReal.toReal_one]
  have hp : 0 ≤ (ν {true}).toReal := ENNReal.toReal_nonneg
  rw [lintegral_fintype, Fintype.sum_bool]
  simp only [Bool.coe_false, ite_true, ite_false, Real.exp_zero]
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν {true}),
    ← ENNReal.ofReal_toReal (measure_ne_top ν {false}),
    ← ENNReal.ofReal_mul (Real.exp_pos u).le, ← ENNReal.ofReal_mul zero_le_one,
    ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos u).le hp)
      (mul_nonneg zero_le_one ENNReal.toReal_nonneg)]
  simp only [ENNReal.toReal_ofReal hp]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (1 + (Real.exp 1 - 1) * u) * (ν {true}).toReal + 1 * (ν {false}).toReal :=
      add_le_add (mul_le_mul_of_nonneg_right (exp_le_secant_on_unit hu) hp) le_rfl
    _ = ((Real.exp 1 - 1) * u * (ν {true}).toReal) + 1 := by linarith only [hmass]
    _ ≤ _ := Real.add_one_le_exp _

/-- An exponential upper tail for a finite weighted sum of independent Boolean flags.
The upper bound uses only their individual true probabilities and the weight cap. -/
theorem measure_pi_weightedBoolTail_le {ι : Type*} [Fintype ι]
    (ν : ι → Measure Bool) [∀ i, IsProbabilityMeasure (ν i)]
    (w : ι → ℝ) {B : ℝ} (t : ℝ) (hB : 0 < B) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ B) :
    (Measure.pi ν) {f | t < ∑ i, if f i then w i else 0} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) *
        ∑ i, w i * (ν i {true}).toReal) / B)) := by
  let X (i : ι) (b : Bool) := ENNReal.ofReal (Real.exp (if b then w i / B else 0))
  let C (i : ι) := ((Real.exp 1 - 1) * (w i * (ν i {true}).toReal)) / B
  let F (f : ι → Bool) := ENNReal.ofReal (Real.exp ((-t + ∑ i, if f i then w i else 0) / B))
  have hX (i : ι) : Measurable (X i) := measurable_of_finite _
  have hXpi (i : ι) : Measurable (fun f : ι → Bool ↦ X i (f i)) :=
    (hX i).comp (measurable_pi_apply i)
  have hfactor (f : ι → Bool) :
      F f = ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, X i (f i) := by
    unfold F X
    rw [add_div, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Finset.sum_div,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    cases f i <;> simp
  have hmgf (i : ι) :
      (∫⁻ f : ι → Bool, X i (f i) ∂Measure.pi ν) ≤ ENNReal.ofReal (Real.exp (C i)) := by
    rw [(measurePreserving_eval ν i).lintegral_comp (hX i)]
    have hunit : w i / B ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (hw i).1 hB.le, (div_le_one hB).mpr (hw i).2⟩
    have hC : C i = (Real.exp 1 - 1) * (w i / B) * (ν i {true}).toReal := by
      unfold C
      ring
    rw [hC]
    exact lintegral_exp_weightedBool_le (ν i) hunit
  calc
    _ ≤ ∫⁻ f, F f ∂Measure.pi ν := by
      apply meas_le_lintegral₀ (measurable_of_finite F).aemeasurable
      intro f hf
      have harg : 0 ≤ (-t + ∑ i, if f i then w i else 0) / B :=
        div_nonneg (by simpa only [neg_add_eq_sub] using sub_nonneg.mpr hf.le) hB.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg)
    _ = ENNReal.ofReal (Real.exp (-t / B)) *
        ∏ i, ∫⁻ f : ι → Bool, X i (f i) ∂Measure.pi ν := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod (fun i _ ↦ hXpi i)),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi (fun i ↦ (hX i).aemeasurable)) hXpi]
    _ ≤ ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, ENNReal.ofReal (Real.exp (C i)) :=
      mul_le_mul_right (Finset.prod_le_prod (fun i _ ↦ hmgf i)) _
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
      simp only [C, ← Finset.sum_div, ← Finset.mul_sum, ← add_div]

/-- A deterministic upper bound on the mean can replace the sum of the individual means. -/
theorem measure_pi_weightedBoolTail_le_of_mean_le {ι : Type*} [Fintype ι]
    (ν : ι → Measure Bool) [∀ i, IsProbabilityMeasure (ν i)]
    (w : ι → ℝ) {B : ℝ} (t : ℝ) (hB : 0 < B) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ B)
    {m : ℝ} (hm : (∑ i, w i * (ν i {true}).toReal) ≤ m) :
    (Measure.pi ν) {f | t < ∑ i, if f i then w i else 0} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) * m) / B)) := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (zero_le_one : (0 : ℝ) ≤ 1))
  refine (measure_pi_weightedBoolTail_le ν w t hB hw).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  exact div_le_div_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm he)) hB.le

end LennonPittelFormalization

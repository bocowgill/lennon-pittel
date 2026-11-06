module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Independence.Integration

/-!
# A Chernoff bound for a finite product of bounded variables

The exponential moment factors across coordinates. The chord of the
exponential on `[0, 1]` bounds each factor in terms of the corresponding mean.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem exp_le_chord_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  have h := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel (1 : ℝ) x)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith

private theorem lintegral_exp_bounded_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (g : Ω → ℝ) (hg : Measurable g)
    {B m : ℝ} (hB : 0 < B) (hb : ∀ z, g z ∈ Icc 0 B) (hm : 0 ≤ m)
    (hmass : (∫⁻ z, ENNReal.ofReal (g z) ∂ν) ≤ ENNReal.ofReal m) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (g z / B)) ∂ν) ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * m / B)) := by
  let c : ℝ := (Real.exp 1 - 1) / B
  have he : 1 ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
  have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr he) hB.le
  calc
    _ ≤ ∫⁻ z, (1 + ENNReal.ofReal c * ENNReal.ofReal (g z)) ∂ν := by
      apply lintegral_mono
      intro z
      change ENNReal.ofReal (Real.exp (g z / B)) ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal (g z)
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg hc (hb z).1)]
      apply ENNReal.ofReal_le_ofReal
      rw [show c * g z = (Real.exp 1 - 1) * (g z / B) by dsimp [c]; ring]
      exact exp_le_chord_of_mem_Icc ⟨div_nonneg (hb z).1 hB.le, (div_le_one hB).mpr (hb z).2⟩
    _ = 1 + ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (g z) ∂ν := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hg.ennreal_ofReal]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal m :=
      add_le_add le_rfl (mul_le_mul_right hmass _)
    _ = ENNReal.ofReal (1 + c * m) := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (mul_nonneg hc hm)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [show (Real.exp 1 - 1) * m / B = c * m by dsimp [c]; ring]
      simpa only [add_comm] using Real.add_one_le_exp (c * m)

/-- A finite sum of independent bounded nonnegative variables has an explicit upper-tail bound. -/
theorem measure_pi_boundedSum_gt_le {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (g : ∀ i, Ω i → ℝ) (hg : ∀ i, Measurable (g i)) {B : ℝ} (hB : 0 < B)
    (hb : ∀ i z, g i z ∈ Icc 0 B) (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hmass : ∀ i, (∫⁻ z, ENNReal.ofReal (g i z) ∂ν i) ≤ ENNReal.ofReal (m i)) (t : ℝ) :
    (Measure.pi ν) {x | t < ∑ i, g i (x i)} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) * ∑ i, m i) / B)) := by
  let X (i : ι) (z : Ω i) := ENNReal.ofReal (Real.exp (g i z / B))
  let C (i : ι) := (Real.exp 1 - 1) * m i / B
  let F (x : ∀ i, Ω i) := ENNReal.ofReal (Real.exp ((-t + ∑ i, g i (x i)) / B))
  have hX (i : ι) : Measurable (X i) := (Real.continuous_exp.measurable.comp
    ((hg i).div_const B)).ennreal_ofReal
  have hXpi (i : ι) : Measurable (fun x : ∀ j, Ω j ↦ X i (x i)) :=
    (hX i).comp (measurable_pi_apply i)
  have hfactor (x : ∀ i, Ω i) :
      F x = ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, X i (x i) := by
    unfold F X
    rw [add_div, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Finset.sum_div,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  have hF : Measurable F := by
    rw [show F = (fun x ↦ ENNReal.ofReal (Real.exp (-t / B)) * ∏ i, X i (x i)) from
      funext hfactor]
    exact measurable_const.mul (Finset.univ.measurable_prod fun i _ ↦ hXpi i)
  have hmgf (i : ι) :
      (∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν) ≤ ENNReal.ofReal (Real.exp (C i)) := by
    rw [(measurePreserving_eval ν i).lintegral_comp (hX i)]
    exact lintegral_exp_bounded_le (ν i) (g i) (hg i) hB (hb i) (hm i) (hmass i)
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hF.aemeasurable
      intro x hx
      have harg : 0 ≤ (-t + ∑ i, g i (x i)) / B :=
        div_nonneg (by simpa only [neg_add_eq_sub] using sub_nonneg.mpr hx.le) hB.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg)
    _ = ENNReal.ofReal (Real.exp (-t / B)) *
        ∏ i, ∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν := by
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

end LennonPittelFormalization

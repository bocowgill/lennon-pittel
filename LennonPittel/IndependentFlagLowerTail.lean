module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Independence.Integration

/-!
# Lower tails for counts of independent events

A negative exponential turns a lower-count event into an upper-tail event.
The exponential moment factors over independent coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

open scoped Classical in
private theorem lintegral_exp_neg_flag_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {A : Set Ω} (hA : MeasurableSet A)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp : ENNReal.ofReal p ≤ ν A) :
    (∫⁻ x, if x ∈ A then ENNReal.ofReal (Real.exp (-1)) else 1 ∂ν) ≤
      ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * p)) := by
  let q := (ν A).toReal
  have hfin := measure_ne_top ν A
  have hfin' := measure_ne_top ν Aᶜ
  have hpq : p ≤ q := by
    simpa only [ENNReal.toReal_ofReal hp₀] using ENNReal.toReal_mono hfin hp
  have hcomp : (ν Aᶜ).toReal = 1 - q := by
    rw [measure_compl hA hfin, measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  have hd : 0 ≤ 1 - Real.exp (-1) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    _ = ENNReal.ofReal (Real.exp (-1)) * ν A + ν Aᶜ := by
      change (∫⁻ x, A.piecewise (fun _ ↦ ENNReal.ofReal (Real.exp (-1)))
        (fun _ ↦ 1) x ∂ν) = _
      rw [lintegral_piecewise hA.nullMeasurableSet]
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
    _ = ENNReal.ofReal (-(1 - Real.exp (-1)) * q + 1) := by
      rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hfin',
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, hcomp]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * q)) :=
      ENNReal.ofReal_le_ofReal (Real.add_one_le_exp _)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hpq (neg_nonpos.mpr hd)))

open scoped Classical in
/-- A negative exponential moment bounds the lower tail of a finite independent event count. -/
theorem measure_pi_flagCount_lt_le_exp {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i)) (p t : ℝ)
    (hp₀ : 0 ≤ p) (hp : ∀ i, ENNReal.ofReal p ≤ ν i (A i)) :
    (Measure.pi ν) {x | (∑ i, if x i ∈ A i then (1 : ℝ) else 0) < t} ≤
      ENNReal.ofReal (Real.exp (t - (1 - Real.exp (-1)) * p * (Fintype.card ι : ℝ))) := by
  let X (i : ι) (x : Ω i) := if x ∈ A i then ENNReal.ofReal (Real.exp (-1)) else 1
  let F (x : ∀ i, Ω i) := ENNReal.ofReal (Real.exp (t - ∑ i, if x i ∈ A i then (1 : ℝ) else 0))
  have hX (i : ι) : Measurable (X i) := Measurable.ite (hA i) measurable_const measurable_const
  have hXpi (i : ι) : Measurable (fun x : ∀ j, Ω j ↦ X i (x i)) :=
    (hX i).comp (measurable_pi_apply i)
  have hfactor (x : ∀ i, Ω i) :
      F x = ENNReal.ofReal (Real.exp t) * ∏ i, X i (x i) := by
    unfold F X
    rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split <;> simp
  have hF : Measurable F := by
    rw [show F = (fun x ↦ ENNReal.ofReal (Real.exp t) * ∏ i, X i (x i)) from funext hfactor]
    exact measurable_const.mul (Finset.univ.measurable_prod fun i _ ↦ hXpi i)
  have hmgf (i : ι) : (∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν) ≤
      ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * p)) := by
    rw [(measurePreserving_eval ν i).lintegral_comp (hX i)]
    exact lintegral_exp_neg_flag_le (ν i) (hA i) hp₀ (hp i)
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      refine meas_le_lintegral₀ hF.aemeasurable fun x hx ↦ ?_
      have h : 0 ≤ t - ∑ i, if x i ∈ A i then (1 : ℝ) else 0 := sub_nonneg.mpr hx.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ = ENNReal.ofReal (Real.exp t) * ∏ i, ∫⁻ x : ∀ j, Ω j, X i (x i) ∂Measure.pi ν := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod fun i _ ↦ hXpi i),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi (fun i ↦ (hX i).aemeasurable)) hXpi]
    _ ≤ ENNReal.ofReal (Real.exp t) * ∏ _i : ι,
        ENNReal.ofReal (Real.exp (-(1 - Real.exp (-1)) * p)) :=
      mul_le_mul_right (Finset.prod_le_prod fun i _ ↦ hmgf i) _
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 2
      ring

open scoped Classical in
/-- If each independent event has probability at least one sixteenth, then fewer
than one thirty-second of the events occur with probability at most `exp (-n / 128)`. -/
theorem measure_pi_flagCount_lt_le {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i))
    (hp : ∀ i, ENNReal.ofReal (1 / 16) ≤ ν i (A i)) :
    (Measure.pi ν) {x | (∑ i, if x i ∈ A i then (1 : ℝ) else 0) < (Fintype.card ι : ℝ) / 32} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) / 128)) := by
  refine (measure_pi_flagCount_lt_le_exp ν A hA (1 / 16) _ (by norm_num) hp).trans ?_
  have he : Real.exp (-1) ≤ 3 / 8 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    linarith only [Real.exp_one_gt_d9]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith only [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))]

end LennonPittelFormalization

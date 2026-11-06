module

public import LennonPittel.ExponentialSpouseSquareTail
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Concentration of the logarithmic excess of exponential shares

The logarithm of the common normalizing radius and the sum of coordinate
logarithms admit separate upper-tail estimates. Both estimates are geometric.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- The sum of negative logarithms of the shares scaled by their number. -/
noncomputable def spouseAngularLogExcess {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ i, -Real.log ((n : ℝ) * p i)

theorem measurable_spouseAngularLogExcess (n : ℕ) :
    Measurable (@spouseAngularLogExcess n) := by
  unfold spouseAngularLogExcess
  fun_prop

/-- The radial contribution separates from the sum of the coordinate logarithms. -/
theorem spouseAngularLogExcess_spouseAngle {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    spouseAngularLogExcess (spouseAngle x) =
      (n : ℝ) * Real.log ((∑ i, x i) / n) - ∑ i, Real.log (x i) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hT : 0 < ∑ i, x i := by
    have i : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun j _ ↦ hx j) ⟨i, Finset.mem_univ i⟩
  unfold spouseAngularLogExcess
  calc
    _ = ∑ i, (Real.log ((∑ j, x j) / n) - Real.log (x i)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [spouseAngle, Real.log_mul hn'.ne' (div_pos (hx i) hT).ne',
        Real.log_div (hx i).ne' hT.ne', Real.log_div hT.ne' hn'.ne']
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp

private theorem ae_expMeasure_one_pos : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hvol : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  have hne : ∀ᵐ x ∂expMeasure 1, x ≠ 0 :=
    (withDensity_absolutelyContinuous volume (exponentialPDF 1)).ae_le hvol
  filter_upwards [ae_expMeasure_one_nonneg, hne] with x hx hnx
  exact lt_of_le_of_ne hx (Ne.symm hnx)

private theorem lintegral_expMeasure_one_density (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂expMeasure 1) = ∫⁻ x, exponentialPDF 1 x * f x :=
  lintegral_withDensity_eq_lintegral_mul volume
    (measurable_exponentialPDFReal 1).ennreal_ofReal hf

private theorem lintegral_expMeasure_one_exp_half :
    (∫⁻ x, ENNReal.ofReal (Real.exp (x / 2)) ∂expMeasure 1) = ENNReal.ofReal 2 := by
  rw [lintegral_expMeasure_one_density _ (by fun_prop)]
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (Real.exp (x / 2)) =
        ENNReal.ofReal 2 * exponentialPDF (1 / 2) x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      simp only [one_mul, ← Real.exp_add]
      rw [show -x + x / 2 = -(1 / 2 * x) by ring]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  have he : Measurable (exponentialPDF (1 / 2)) :=
    (measurable_exponentialPDFReal _).ennreal_ofReal
  rw [lintegral_const_mul _ he,
    lintegral_exponentialPDF_eq_one (by norm_num), mul_one]

private theorem lintegral_expMeasure_one_neg_half_rpow :
    (∫⁻ x, ENNReal.ofReal (x ^ (-1 / 2 : ℝ)) ∂expMeasure 1) =
      ENNReal.ofReal (Real.Gamma (1 / 2)) := by
  rw [lintegral_expMeasure_one_density _ (by fun_prop)]
  have hΓ := Real.Gamma_pos_of_pos (by norm_num : 0 < (1 / 2 : ℝ))
  have h (x : ℝ) :
      exponentialPDF 1 x * ENNReal.ofReal (x ^ (-1 / 2 : ℝ)) =
        ENNReal.ofReal (Real.Gamma (1 / 2)) * gammaPDF (1 / 2) 1 x := by
    by_cases hx : 0 ≤ x
    · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hΓ.le]
      congr 1
      rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]
      simp only [Real.one_rpow, one_mul]
      field_simp
    · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx),
        zero_mul, mul_zero]
  simp_rw [h]
  have hγ : Measurable (gammaPDF (1 / 2) 1) :=
    (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [lintegral_const_mul _ hγ,
    lintegral_gammaPDF_eq_one (by norm_num) (by norm_num), mul_one]

private theorem lintegral_expMeasure_one_exp_neg_log_half_le :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-Real.log x / 2)) ∂expMeasure 1) ≤ ENNReal.ofReal 2 := by
  have h : (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-Real.log x / 2))) =ᵐ[expMeasure 1]
      (fun x ↦ ENNReal.ofReal (x ^ (-1 / 2 : ℝ))) := by
    filter_upwards [ae_expMeasure_one_pos] with x hx
    rw [Real.rpow_def_of_pos hx]
    congr 2
    ring
  rw [lintegral_congr_ae h, lintegral_expMeasure_one_neg_half_rpow, Real.Gamma_one_half_eq]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt Real.pi_lt_four.le
    _ = _ := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem measure_iidExponential_sum_gt_le (n : ℕ)
    {g : ℝ → ℝ} (hg : Measurable g) (a : ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hmg : (∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂expMeasure 1) ≤ ENNReal.ofReal m) :
    iidExponentialScoreLaw n {x | a * (n : ℝ) < ∑ i, g (x i)} ≤
      ENNReal.ofReal ((Real.exp (-a) * m) ^ n) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  let f (t : ℝ) := ENNReal.ofReal (Real.exp (g t))
  let F (x : Fin n → ℝ) := ENNReal.ofReal (Real.exp (-a * (n : ℝ) + ∑ i, g (x i)))
  have hf : Measurable f := by unfold f; fun_prop
  have hF : Measurable F := by unfold F; fun_prop
  have hcoord (i : Fin n) : Measurable (fun x : Fin n → ℝ ↦ f (x i)) :=
    hf.comp (measurable_pi_apply i)
  have hfactor (x : Fin n → ℝ) :
      F x = ENNReal.ofReal (Real.exp (-a * (n : ℝ))) * ∏ i, f (x i) := by
    unfold F f
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  have hrow (i : Fin n) : (∫⁻ x : Fin n → ℝ, f (x i) ∂Measure.pi ν) ≤ ENNReal.ofReal m := by
    rw [(measurePreserving_eval ν i).lintegral_comp hf]
    exact hmg
  change (Measure.pi ν) _ ≤ _
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hF.aemeasurable
      intro x hx
      change a * (n : ℝ) < ∑ i, g (x i) at hx
      have h : 0 ≤ -a * (n : ℝ) + ∑ i, g (x i) := by linarith only [hx]
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ ≤ ENNReal.ofReal (Real.exp (-a * (n : ℝ))) * ENNReal.ofReal m ^ n := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod fun i _ ↦ hcoord i),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi fun _ ↦ hf.aemeasurable) hcoord]
      apply mul_le_mul_right
      exact (Finset.prod_le_prod fun i _ ↦ hrow i).trans_eq (by simp)
    _ = _ := by
      rw [← ENNReal.ofReal_pow hm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [mul_comm (-a), Real.exp_nat_mul, mul_pow]

private noncomputable def logTailFactor : ℝ := Real.exp (-1) * 2

private theorem logTailFactor_pos : 0 < logTailFactor := by
  unfold logTailFactor
  positivity

private theorem logTailFactor_lt_one : logTailFactor < 1 := by
  unfold logTailFactor
  rw [Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _), mul_one]
  exact Real.exp_one_gt_two

private theorem measure_iidExponential_radius_gt_le (n : ℕ) :
    iidExponentialScoreLaw n {x | 2 * (n : ℝ) < ∑ i, x i} ≤
      ENNReal.ofReal (logTailFactor ^ n) := by
  have h (x : Fin n → ℝ) : 2 * (n : ℝ) < ∑ i, x i ↔
      1 * (n : ℝ) < ∑ i, x i / 2 := by
    rw [← Finset.sum_div, one_mul]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm (n : ℝ) (2 : ℝ)]
  simp_rw [h]
  exact measure_iidExponential_sum_gt_le n (g := fun x ↦ x / 2) (by fun_prop) 1
    (by norm_num) lintegral_expMeasure_one_exp_half.le

private theorem measure_iidExponential_neg_log_sum_gt_le (n : ℕ) :
    iidExponentialScoreLaw n {x | 4 * (n : ℝ) < ∑ i, -Real.log (x i)} ≤
      ENNReal.ofReal (logTailFactor ^ n) := by
  have h (x : Fin n → ℝ) : 4 * (n : ℝ) < ∑ i, -Real.log (x i) ↔
      2 * (n : ℝ) < ∑ i, -Real.log (x i) / 2 := by
    rw [← Finset.sum_div]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show 2 * (n : ℝ) * 2 = 4 * (n : ℝ) by ring]
  simp_rw [h]
  refine (measure_iidExponential_sum_gt_le n (g := fun x ↦ -Real.log x / 2) (by fun_prop) 2
    (by norm_num) lintegral_expMeasure_one_exp_neg_log_half_le).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity) _ n
  unfold logTailFactor
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by norm_num)

private theorem measure_iidExponential_spouseAngularLogExcess_gt_le {n : ℕ} (hn : 0 < n) :
    iidExponentialScoreLaw n {x | 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x)} ≤
      ENNReal.ofReal (logTailFactor ^ n) + ENNReal.ofReal (logTailFactor ^ n) := by
  let ν (_ : Fin n) := expMeasure (1 : ℝ)
  have hae : ∀ᵐ x ∂iidExponentialScoreLaw n, ∀ i, 0 < x i :=
    ae_all_iff.2 fun i ↦
      (measurePreserving_eval ν i).quasiMeasurePreserving.ae ae_expMeasure_one_pos
  let A : Set (Fin n → ℝ) := {x | 2 * (n : ℝ) < ∑ i, x i}
  let B : Set (Fin n → ℝ) := {x | 4 * (n : ℝ) < ∑ i, -Real.log (x i)}
  let U : Set (Fin n → ℝ) := A ∪ B
  have hsub : {x | 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x)}
      ≤ᵐ[iidExponentialScoreLaw n] U := by
    filter_upwards [hae] with x hx hbad
    by_cases hA : x ∈ A
    · exact Or.inl hA
    by_cases hB : x ∈ B
    · exact Or.inr hB
    exfalso
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hT : 0 < ∑ i, x i :=
      Finset.sum_pos (fun j _ ↦ hx j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hdiv : (∑ i, x i) / (n : ℝ) ≤ 2 :=
      (div_le_iff₀ hn').mpr (le_of_not_gt hA)
    have hlog : Real.log ((∑ i, x i) / (n : ℝ)) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hT hn')
      linarith only [h, hdiv]
    have hsum : -(∑ i, Real.log (x i)) ≤ 4 * (n : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact le_of_not_gt hB
    change 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x) at hbad
    rw [spouseAngularLogExcess_spouseAngle hn x hx] at hbad
    linarith only [hbad, hn', hsum, mul_le_mul_of_nonneg_left hlog hn'.le]
  exact (measure_mono_ae hsub).trans ((measure_union_le A B).trans
    (add_le_add (measure_iidExponential_radius_gt_le n)
      (measure_iidExponential_neg_log_sum_gt_le n)))

private theorem eventually_logTailFactor_le_neg_rpow (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, logTailFactor ^ n ≤ (n : ℝ) ^ (-p) := by
  have hq : 0 < -Real.log logTailFactor :=
    neg_pos.mpr (Real.log_neg logTailFactor_pos logTailFactor_lt_one)
  have h := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    (p / -Real.log logTailFactor)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (0 : ℕ), h] with n hn hnlog
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |p / -Real.log logTailFactor * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hnlog
  rw [Real.rpow_one, abs_of_nonneg hn'.le] at habs
  have hle : p * Real.log (n : ℝ) ≤ (n : ℝ) * -Real.log logTailFactor := by
    apply (div_le_iff₀ hq).mp
    rw [mul_div_right_comm]
    exact (le_abs_self _).trans habs
  rw [Real.rpow_def_of_pos hn', ← Real.exp_log logTailFactor_pos, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by linarith only [hle])

/-- The logarithmic excess of exponential shares exceeds six times their number
with probability smaller than any fixed inverse power, eventually. -/
theorem eventually_measure_iidExponential_spouseAngularLogExcess_gt_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, iidExponentialScoreLaw n
      {x | 6 * (n : ℝ) < spouseAngularLogExcess (spouseAngle x)} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_logTailFactor_le_neg_rpow (p + 1)] with n hn hq
  have hn' : 0 < n := by omega
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  refine (measure_iidExponential_spouseAngularLogExcess_gt_le hn').trans ?_
  refine (add_le_add (ENNReal.ofReal_le_ofReal hq) (ENNReal.ofReal_le_ofReal hq)).trans ?_
  rw [← ENNReal.ofReal_add ha ha]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = 2 * a := by ring
    _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₂ ha
    _ = _ := calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -(p + 1) = -p by ring]

end LennonPittelFormalization

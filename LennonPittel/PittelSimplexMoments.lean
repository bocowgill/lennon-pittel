module

public import LennonPittel.PittelSimplexRadial
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Angular moments for Pittel's first moment

An exponential tilt of radial integration factors into one Gamma integral in
each score coordinate. Comparing the two evaluations gives exact moments of
the relative scores.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

private theorem integrableOn_exp_neg_mul_pow (a : ℕ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x ^ a) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (show 0 < (a : ℝ) + 1 by positivity)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _
  rw [add_sub_cancel_right, Real.rpow_natCast]

private theorem integral_exp_neg_mul_pow (a : ℕ) :
    (∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ a) = (a.factorial : ℝ) := by
  rw [← Real.Gamma_nat_eq_factorial]
  rw [Real.Gamma_eq_integral (by positivity)]
  simp only [add_sub_cancel_right, Real.rpow_natCast]

private theorem restrict_nonneg_eq_pi (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict {x | ∀ i, 0 ≤ x i} =
      Measure.pi (fun _ : Fin n ↦ (volume : Measure ℝ).restrict (Ioi 0)) := by
  have heq : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = univ.pi (fun _ ↦ Ici 0) := by
    ext x
    simp [Pi.le_def]
  rw [heq, volume_pi, Measure.restrict_pi_pi]
  simp only [Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]

private theorem lintegral_exp_monomial {n : ℕ} (a : Fin n → ℕ) :
    (∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ a i)
      ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
      ENNReal.ofReal (∏ i, ((a i).factorial : ℝ)) := by
  simp only [← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  rw [restrict_nonneg_eq_pi, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_fin_nat_prod_eq_prod (fun (i : Fin n) (t : ℝ) ↦ Real.exp (-t) * t ^ a i)]
    simp_rw [integral_exp_neg_mul_pow]
  · exact Integrable.fintype_prod_dep fun i ↦ integrableOn_exp_neg_mul_pow (a i)
  · have hs : MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
      rw [ofPred_forall]
      exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)
    rw [← restrict_nonneg_eq_pi]
    filter_upwards [ae_restrict_mem hs] with x hx
    exact Finset.prod_nonneg fun i _ ↦ mul_nonneg (Real.exp_pos _).le (pow_nonneg (hx i) _)

private theorem measurable_exp_monomial (n : ℕ) (a : Fin n → ℕ) :
    Measurable (fun x : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ a i)) := by
  fun_prop

private theorem lintegral_exp_monomial_radius {n : ℕ} (a : Fin n → ℕ)
    (μ : Measure (Fin n → ℝ))
    (hμ : ∀ᵐ w ∂μ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) (s : ℝ) (hs : 0 < s) :
    (∫⁻ w, ENNReal.ofReal
      (Real.exp (-(∑ i, s * w i)) * ∏ i, (s * w i) ^ a i) ∂μ) =
      ENNReal.ofReal (Real.exp (-s) * s ^ (∑ i, a i)) *
        (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) := by
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hμ] with w hw
  rw [← Finset.mul_sum, hw.2, mul_one, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]

private theorem lintegral_radial_factor (n k : ℕ) :
    (∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)) *
        ENNReal.ofReal (Real.exp (-s) * s ^ k)) =
      ENNReal.ofReal (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) := by
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal ((Real.exp (-s) * s ^ (n - 1 + k)) /
          ((n - 1).factorial : ℝ)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hs.le _) (by positivity)), pow_add]
      congr 1
      ring
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_exp_neg_mul_pow (n - 1 + k)).div_const _)]
      · rw [integral_div, integral_exp_neg_mul_pow]
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hs.le _)) (by positivity)

private theorem lintegral_angle_monomial_of_radial {n : ℕ} (a : Fin n → ℕ)
    (μ : Measure (Fin n → ℝ)) [SFinite μ]
    (hμ : ∀ᵐ w ∂μ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (hrad : ∀ {f : (Fin n → ℝ) → ℝ≥0∞}, Measurable f →
      (∫⁻ x, f x ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
        ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂μ
          ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
            (fun s ↦ ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))))) :
    (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) =
      ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ)) := by
  let k := ∑ i, a i
  let c := ∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ
  let f (x : Fin n → ℝ) :=
    ENNReal.ofReal (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ a i)
  let g (s : ℝ) := ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))
  let h (s : ℝ) := ENNReal.ofReal (Real.exp (-s) * s ^ k)
  have hF : Measurable (fun (z : ℝ × (Fin n → ℝ)) ↦ f (fun i ↦ z.1 * z.2 i)) := by
    fun_prop
  have hEq := hrad (f := f) (measurable_exp_monomial n a)
  rw [lintegral_exp_monomial a, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable g by fun_prop) (Measurable.lintegral_prod_right hF)] at hEq
  have hInner : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      (∫⁻ w, f (fun i ↦ s * w i) ∂μ) = h s * c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact lintegral_exp_monomial_radius a μ hμ s hs
  have hMul :
      ENNReal.ofReal (∏ i, ((a i).factorial : ℝ)) =
        ENNReal.ofReal (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) * c := by
    rw [hEq]
    calc
      _ = ∫⁻ s in Ioi (0 : ℝ), (g s * h s) * c := by
        apply lintegral_congr_ae
        filter_upwards [hInner] with s hs
        rw [Pi.mul_apply, hs, mul_assoc]
      _ = _ := by
        rw [lintegral_mul_const _ (show Measurable (fun s ↦ g s * h s) by fun_prop),
          lintegral_radial_factor]
  have hpos : 0 < (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) := by
    positivity
  change c = _
  rw [show (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
      ((n - 1 + ∑ i, a i).factorial : ℝ) =
      (∏ i, ((a i).factorial : ℝ)) /
        (((n - 1 + k).factorial : ℝ) / ((n - 1).factorial : ℝ)) by
      rw [div_div_eq_mul_div],
    ENNReal.ofReal_div_of_pos hpos, ENNReal.eq_div_iff (by positivity) ENNReal.ofReal_ne_top]
  exact hMul.symm

private theorem integral_angle_monomial_of_lintegral {n : ℕ} (μ : Measure (Fin n → ℝ))
    (hμ : ∀ᵐ w ∂μ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1)
    (a : Fin n → ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hm : (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) = ENNReal.ofReal r) :
    (∫ w, ∏ i, w i ^ a i ∂μ) = r := by
  have hn : 0 ≤ᵐ[μ] fun w ↦ ∏ i, w i ^ a i :=
    hμ.mono fun w hw ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (hw.1 i) _
  have hi : Integrable (fun w ↦ ∏ i, w i ^ a i) μ :=
    ⟨(show Measurable (fun w : Fin n → ℝ ↦ ∏ i, w i ^ a i) by
      fun_prop).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr (hm ▸ ENNReal.ofReal_lt_top)⟩
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hn) hr).mp
    ((ofReal_integral_eq_lintegral_ofReal hi hn).trans hm)

private theorem lintegral_angle_power_of_monomial {n : ℕ} (μ : Measure (Fin n → ℝ))
    (hm : ∀ a : Fin n → ℕ, (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂μ) =
      ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ)))
    (i : Fin n) (k : ℕ) :
    (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂μ) =
      ENNReal.ofReal ((k.factorial : ℝ) * ((n - 1).factorial : ℝ) /
        ((n - 1 + k).factorial : ℝ)) := by
  have hPow (w : Fin n → ℝ) : (∏ j, w j ^ (Pi.single i k) j) = w i ^ k := by
    rw [Fintype.prod_eq_single i]
    · simp
    · intro j hj
      simp [Pi.single_eq_of_ne hj]
  have hFact : (∏ j, (((Pi.single i k : Fin n → ℕ) j).factorial : ℝ)) =
      (k.factorial : ℝ) := by
    rw [Fintype.prod_eq_single i]
    · simp
    · intro j hj
      simp [Pi.single_eq_of_ne hj]
  simpa only [hPow, hFact, Finset.sum_pi_single', Finset.mem_univ, ite_true] using
    hm (Pi.single i k)

private theorem factorial_power_quotient_le {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (k.factorial : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + k).factorial : ℝ)
      ≤ ((k : ℝ) / n) ^ k := by
  have hn1 : n - 1 + 1 = n := by omega
  have hden : (((n - 1).factorial : ℝ) * (n : ℝ) ^ k) ≤ ((n - 1 + k).factorial : ℝ) := by
    exact_mod_cast (hn1 ▸ Nat.factorial_mul_pow_le_factorial (m := n - 1) (n := k))
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ (k : ℝ) ^ k * (((n - 1).factorial : ℝ) * (n : ℝ) ^ k) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hfac (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

private theorem measure_angle_large_coordinate_of_power {n : ℕ} {μ : Measure (Fin n → ℝ)}
    (hn : 0 < n) (i : Fin n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (hm : (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂μ) =
      ENNReal.ofReal ((k.factorial : ℝ) * ((n - 1).factorial : ℝ) /
        ((n - 1 + k).factorial : ℝ))) :
    μ {w | t < w i} ≤ ENNReal.ofReal (((k : ℝ) / n / t) ^ k) := by
  have hmeas : Measurable (fun w : Fin n → ℝ ↦ ENNReal.ofReal (w i ^ k)) := by fun_prop
  calc
    _ ≤ μ {w | ENNReal.ofReal (t ^ k) ≤ ENNReal.ofReal (w i ^ k)} := by
      apply measure_mono
      intro w hw
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le hw.le _)
    _ ≤ (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂μ) / ENNReal.ofReal (t ^ k) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ _ := by
      rw [hm, div_pow, ENNReal.ofReal_div_of_pos (pow_pos ht _)]
      exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal (factorial_power_quotient_le hn k)) _

/-- Directions with an unusually large coordinate have vanishing probability. -/
private theorem tendsto_measure_angle_max_of_power
    (μ : ∀ n : ℕ, Measure (Fin n → ℝ))
    (hm : ∀ {n}, 0 < n → ∀ (i : Fin n) (k : ℕ),
      (∫⁻ w, ENNReal.ofReal (w i ^ k) ∂(μ n)) =
        ENNReal.ofReal ((k.factorial : ℝ) * ((n - 1).factorial : ℝ) /
          ((n - 1 + k).factorial : ℝ))) :
    Tendsto (fun n ↦ μ n {w | ∃ i, 12 * Real.log n / n < w i}) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hbound : ∀ᶠ n : ℕ in atTop,
      μ n {w | ∃ i, 12 * Real.log n / n < w i} ≤ ENNReal.ofReal ((n : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0, hlog.eventually_ge_atTop 1] with n hn hl
    change 1 ≤ Real.log (n : ℝ) at hl
    let k : ℕ := ⌈2 * Real.log (n : ℝ)⌉₊
    let t : ℝ := 12 * Real.log (n : ℝ) / n
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlogpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hl
    have ht : 0 < t := by dsimp [t]; positivity
    have hklo : 2 * Real.log (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
    have hkhi : (k : ℝ) ≤ 3 * Real.log (n : ℝ) := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.log (n : ℝ) by positivity)
      change (k : ℝ) < 2 * Real.log (n : ℝ) + 1 at h
      linarith
    have hratio : (k : ℝ) / n / t ≤ 4⁻¹ := by
      dsimp only [t]
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity : 0 < 12 * Real.log (n : ℝ))]
      rw [div_mul_cancel₀ _ hnR.ne']
      linarith
    have hpow : ((k : ℝ) / n / t) ^ k ≤ ((n : ℝ) ^ 2)⁻¹ := by
      calc
        _ ≤ (4⁻¹ : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hratio _
        _ ≤ Real.exp (-1) ^ k := by
          apply pow_le_pow_left₀ (by norm_num)
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) (Real.exp_one_lt_three.le.trans (by norm_num))
        _ = Real.exp (-(k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-(2 * Real.log (n : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hklo)
        _ = _ := by
          rw [Real.exp_neg, ← Nat.cast_two (R := ℝ), Real.exp_nat_mul, Real.exp_log hnR]
    calc
      _ ≤ ∑ i : Fin n, μ n {w | t < w i} := by
        rw [ofPred_exists]
        exact measure_iUnion_fintype_le _ _
      _ ≤ ∑ _ : Fin n, ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum fun i _ ↦ (measure_angle_large_coordinate_of_power hn i k ht
          (hm hn i k)).trans (ENNReal.ofReal_le_ofReal hpow)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hzero : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_inv_atTop_zero.comp hcast)
  exact tendsto_const_nhds.squeeze' hzero (Eventually.of_forall fun _ ↦ zero_le) hbound

/-- Relative scores in the region used to compute the leading coefficient of the mean. -/
def pittelTypicalAngles (n : ℕ) (η : ℝ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, w i ≤ 12 * Real.log n / n) ∧
    |(n : ℝ) * (∑ i, w i ^ 2) - 2| ≤ η}

theorem measurableSet_pittelTypicalAngles (n : ℕ) (η : ℝ) :
    MeasurableSet (pittelTypicalAngles n η) := by
  unfold pittelTypicalAngles
  simp only [ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const
    (measurable_pi_apply i)).inter ((measurableSet_eq_fun (by fun_prop) measurable_const).inter
    ((MeasurableSet.iInter fun i ↦ measurableSet_le (measurable_pi_apply i)
      measurable_const).inter (measurableSet_le (by fun_prop) measurable_const)))


private theorem pittel_integrable_coord_pow {n : ℕ} {μ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (k : ℕ) : Integrable (fun w ↦ w i ^ k) μ := by
  refine Integrable.of_bound ((continuous_apply i).pow k).aestronglyMeasurable
    1 (hμ.mono fun w hw ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hw i).1 k)]
  exact pow_le_one₀ (hw i).1 (hw i).2

private theorem pittel_integrable_coord_sq_mul_sq {n : ℕ} {μ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (i j : Fin n) : Integrable (fun w ↦ w i ^ 2 * w j ^ 2) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (hμ.mono fun w hw ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [one_mul] using mul_le_mul (pow_le_one₀ (hw i).1 (hw i).2)
    (pow_le_one₀ (hw j).1 (hw j).2) (sq_nonneg (w j)) (zero_le_one : (0 : ℝ) ≤ 1)

private theorem pittel_prod_coord_pow_single {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    (∏ j, w j ^ Pi.single i k j) = w i ^ k := by
  rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same]

private theorem pittel_prod_factorial_single {n : ℕ} (i : Fin n) (k : ℕ) :
    (∏ j, (Nat.factorial ((Pi.single i k : Fin n → ℕ) j) : ℝ)) = (k.factorial : ℝ) := by
  rw [Finset.prod_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same]

private theorem pittel_prod_factorial_two {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∏ l, (Nat.factorial ((Pi.single i 2 + Pi.single j 2 : Fin n → ℕ) l) : ℝ)) = 4 := by
  have hpoint (l : Fin n) :
      Nat.factorial ((Pi.single i 2 + Pi.single j 2 : Fin n → ℕ) l) =
        Nat.factorial ((Pi.single i 2 : Fin n → ℕ) l) *
          Nat.factorial ((Pi.single j 2 : Fin n → ℕ) l) := by
    by_cases hi : l = i
    · subst l
      simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hi]
  simp_rw [hpoint, Nat.cast_mul, Finset.prod_mul_distrib, pittel_prod_factorial_single]
  norm_num [Nat.factorial]

private theorem pittel_factorial_add_two {n : ℕ} (hn : 0 < n) :
    ((n - 1 + 2).factorial : ℝ) = (n - 1).factorial * n * ((n : ℝ) + 1) := by
  have hsplit : n - 1 + 2 = (n - 1 + 1) + 1 := by omega
  rw [hsplit, Nat.factorial_succ, Nat.factorial_succ, show n - 1 + 1 = n by omega]
  push_cast
  ring

private theorem pittel_factorial_add_four {n : ℕ} (hn : 0 < n) :
    ((n - 1 + 4).factorial : ℝ) =
      (n - 1).factorial * n * ((n : ℝ) + 1) * (n + 2) * (n + 3) := by
  have hsplit : n - 1 + 4 = (n - 1 + 2 + 1) + 1 := by omega
  rw [hsplit, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [pittel_factorial_add_two hn, Nat.cast_sub (show 1 ≤ n by omega)]
  push_cast
  ring

/-- The dimension times the sum of squared shares. -/
noncomputable def pittelAngularSquareScore {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (n : ℝ) * ∑ i, w i ^ 2

section Moments

variable {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
variable (hμ : ∀ᵐ w ∂μ, ∀ i, w i ∈ Icc (0 : ℝ) 1)
variable (hmoment : ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂μ) =
  (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
    ((n - 1 + ∑ i, a i).factorial : ℝ))

include hmoment in
omit [IsProbabilityMeasure μ] in
private theorem pittel_integral_coord_pow (i : Fin n) (k : ℕ) :
    (∫ w, w i ^ k ∂μ) =
      (k.factorial : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + k).factorial : ℝ) := by
  simpa [pittel_prod_coord_pow_single, pittel_prod_factorial_single, Finset.sum_pi_single'] using
    hmoment (Pi.single i k)

include hmoment in
omit [IsProbabilityMeasure μ] in
private theorem pittel_integral_coord_sq_mul_sq (i j : Fin n) (hij : i ≠ j) :
    (∫ w, w i ^ 2 * w j ^ 2 ∂μ) =
      (4 : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ) := by
  have h := hmoment (Pi.single i 2 + Pi.single j 2)
  rw [pittel_prod_factorial_two i j hij] at h
  simpa [Pi.add_apply, pow_add, Finset.prod_mul_distrib, pittel_prod_coord_pow_single,
    Finset.sum_add_distrib, Finset.sum_pi_single'] using h

include hμ hmoment in
private theorem pittel_integral_squareScore (hn : 0 < n) :
    (∫ w, pittelAngularSquareScore w ∂μ) = 2 * (n : ℝ) / ((n : ℝ) + 1) := by
  have hf : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [pittelAngularSquareScore]
  rw [integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ pittel_integrable_coord_pow hμ i 2)]
  simp_rw [pittel_integral_coord_pow hmoment, pittel_factorial_add_two hn]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Nat.factorial]
  field_simp

include hμ hmoment in
private theorem pittel_integral_squareScore_sq (hn : 0 < n) :
    (∫ w, pittelAngularSquareScore w ^ 2 ∂μ) =
      4 * (n : ℝ) ^ 2 * ((n : ℝ) + 5) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  classical
  have hf : (0 : ℝ) < (n - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hprod (i : Fin n) :
      (∑ j, ∫ w, w i ^ 2 * w j ^ 2 ∂μ) =
        ((n - 1 : ℕ) : ℝ) * (4 * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ)) +
          24 * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · have hcard : (Finset.univ.erase i).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      calc
        _ = ∑ _ ∈ Finset.univ.erase i,
            (4 : ℝ) * ((n - 1).factorial : ℝ) / ((n - 1 + 4).factorial : ℝ) :=
          Finset.sum_congr rfl fun j hj ↦ pittel_integral_coord_sq_mul_sq hmoment i j
            (Finset.ne_of_mem_erase hj).symm
        _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    · simp_rw [← pow_add]
      norm_num [pittel_integral_coord_pow hmoment i 4, Nat.factorial]
  simp_rw [pittelAngularSquareScore, mul_pow, sq (∑ i : Fin n, _), Finset.sum_mul_sum]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ pittel_integrable_coord_sq_mul_sq hμ i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ pittel_integrable_coord_sq_mul_sq hμ _ j), hprod,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    pittel_factorial_add_four hn, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  field_simp
  ring

include hμ in
private theorem pittel_integrable_squareScore :
    Integrable (fun w ↦ pittelAngularSquareScore w) μ := by
  unfold pittelAngularSquareScore
  exact (integrable_finsetSum _ fun i _ ↦ pittel_integrable_coord_pow hμ i 2).const_mul _

include hμ in
private theorem pittel_integrable_squareScore_sq :
    Integrable (fun w ↦ pittelAngularSquareScore w ^ 2) μ := by
  simp_rw [pittelAngularSquareScore, mul_pow, sq (∑ i : Fin n, _), Finset.sum_mul_sum]
  exact (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    pittel_integrable_coord_sq_mul_sq hμ i j).const_mul _

include hμ in
private theorem pittel_integrable_squareScore_deviation :
    Integrable (fun w ↦ (pittelAngularSquareScore w - 2) ^ 2) μ := by
  have heq : (fun w : Fin n → ℝ ↦ (pittelAngularSquareScore w - 2) ^ 2) =
      fun w ↦ pittelAngularSquareScore w ^ 2 - 4 * pittelAngularSquareScore w + 4 := by
    funext w
    ring
  rw [heq]
  exact ((pittel_integrable_squareScore_sq hμ).sub
    ((pittel_integrable_squareScore hμ).const_mul _)).add (integrable_const _)

include hμ hmoment in
private theorem pittel_integral_squareScore_deviation (hn : 0 < n) :
    (∫ w, (pittelAngularSquareScore w - 2) ^ 2 ∂μ) =
      4 * ((n : ℝ) ^ 2 - (n : ℝ) + 6) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have heq (w : Fin n → ℝ) : (pittelAngularSquareScore w - 2) ^ 2 =
      pittelAngularSquareScore w ^ 2 - 4 * pittelAngularSquareScore w + 4 := by ring
  have hlin : Integrable (fun w : Fin n → ℝ ↦ 4 * pittelAngularSquareScore w) μ :=
    (pittel_integrable_squareScore hμ).const_mul _
  have hsub : Integrable (fun w : Fin n → ℝ ↦
      pittelAngularSquareScore w ^ 2 - 4 * pittelAngularSquareScore w) μ :=
    (pittel_integrable_squareScore_sq hμ).sub hlin
  simp_rw [heq]
  rw [integral_add hsub (integrable_const (4 : ℝ)),
    integral_sub (pittel_integrable_squareScore_sq hμ) hlin,
    integral_const_mul, integral_const, probReal_univ, one_smul,
    pittel_integral_squareScore_sq hμ hmoment hn, pittel_integral_squareScore hμ hmoment hn]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  field_simp
  ring

include hμ hmoment in
private theorem pittel_angular_measure_deviation_le (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    μ {w | η < |pittelAngularSquareScore w - 2|} ≤ ENNReal.ofReal (28 / (η ^ 2 * n)) := by
  let f (w : Fin n → ℝ) : ℝ := (pittelAngularSquareScore w - 2) ^ 2
  have hf : Measurable (fun w ↦ ENNReal.ofReal (f w)) := by
    dsimp [f, pittelAngularSquareScore]
    fun_prop
  have hηsq : 0 < η ^ 2 := by positivity
  have hmark := meas_ge_le_lintegral_div (μ := μ) hf.aemeasurable
    (ε := ENNReal.ofReal (η ^ 2)) (by positivity) ENNReal.ofReal_ne_top
  have hinc : {w | η < |pittelAngularSquareScore w - 2|} ⊆
      {w | ENNReal.ofReal (η ^ 2) ≤ ENNReal.ofReal (f w)} := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    dsimp [f]
    rw [← sq_abs (pittelAngularSquareScore w - 2)]
    exact (sq_le_sq₀ hη.le (abs_nonneg _)).mpr (le_of_lt hw)
  refine (measure_mono hinc).trans (hmark.trans ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal (pittel_integrable_squareScore_deviation hμ)
      (Eventually.of_forall fun w ↦ sq_nonneg (pittelAngularSquareScore w - 2)),
    ← ENNReal.ofReal_div_of_pos hηsq, pittel_integral_squareScore_deviation hμ hmoment hn]
  apply ENNReal.ofReal_le_ofReal
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 4 * ((n : ℝ) ^ 2 - (n : ℝ) + 6) ≤ 28 * (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hden : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    _ ≤ (28 * (n : ℝ) ^ 2 / (n : ℝ) ^ 3) / η ^ 2 := by
      exact div_le_div_of_nonneg_right (div_le_div₀ (by positivity) hnum (by positivity) hden)
        hηsq.le
    _ = _ := by field_simp

end Moments

/-- Dirichlet moments force the angular square sum, multiplied by dimension, to converge to two. -/
theorem tendsto_pittel_angular_measure_deviation_zero
    (μ : ∀ n : ℕ, Measure (Fin n → ℝ))
    (hprob : ∀ n > 0, IsProbabilityMeasure (μ n))
    (hsupp : ∀ n > 0, ∀ᵐ w ∂(μ n), ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ n > 0, ∀ a : Fin n → ℕ, (∫ w, ∏ i, w i ^ a i ∂(μ n)) =
      (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n ↦ μ n {w | η < |pittelAngularSquareScore w - 2|}) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((28 / η ^ 2) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (28 / η ^ 2))
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let := hprob n hn
  rw [div_div]
  exact pittel_angular_measure_deviation_le (hsupp n hn) (hmom n hn) hn hη

/-- Exact Dirichlet monomial moments of the relative spouse-score law. -/
theorem lintegral_spouseAngularLaw_monomial {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) :
    (∫⁻ w, ENNReal.ofReal (∏ i, w i ^ a i) ∂(spouseAngularLaw n)) =
      ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ)) :=
  lintegral_angle_monomial_of_radial a (spouseAngularLaw n) (ae_spouseAngularLaw hn)
    (lintegral_spouseRadialAngular hn)

/-- The same exact angular moments, written as real-valued expectations. -/
theorem integral_spouseAngularLaw_monomial {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) :
    (∫ w, ∏ i, w i ^ a i ∂(spouseAngularLaw n)) =
      (∏ i, ((a i).factorial : ℝ)) * ((n - 1).factorial : ℝ) /
        ((n - 1 + ∑ i, a i).factorial : ℝ) :=
  integral_angle_monomial_of_lintegral _ (ae_spouseAngularLaw hn) a (by positivity)
    (lintegral_spouseAngularLaw_monomial hn a)

/-- The angular region with the required maximum-share and square-sum bounds has probability
tending to one, expressed here as vanishing complement mass. -/
theorem tendsto_measure_compl_pittelTypicalAngles_zero {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ spouseAngularLaw n (pittelTypicalAngles n η)ᶜ) atTop (𝓝 0) := by
  have hmax := tendsto_measure_angle_max_of_power spouseAngularLaw fun hn i k ↦
    lintegral_angle_power_of_monomial _ (lintegral_spouseAngularLaw_monomial hn) i k
  have hsupp (n : ℕ) (hn : 0 < n) :
      ∀ᵐ w ∂(spouseAngularLaw n), ∀ i, w i ∈ Icc (0 : ℝ) 1 :=
    (ae_spouseAngularLaw hn).mono fun w hw i ↦
      ⟨hw.1 i, hw.2 ▸ Finset.single_le_sum (f := w) (fun j _ ↦ hw.1 j) (Finset.mem_univ i)⟩
  have hsq := tendsto_pittel_angular_measure_deviation_zero spouseAngularLaw
    (fun _ _ ↦ inferInstance) hsupp (fun _ hn a ↦ integral_spouseAngularLaw_monomial hn a) hη
  have hsum := hmax.add hsq
  simp only [add_zero] at hsum
  refine tendsto_const_nhds.squeeze' hsum (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let B : Set (Fin n → ℝ) := {w | ∃ i, 12 * Real.log n / n < w i}
  let C : Set (Fin n → ℝ) := {w | η < |pittelAngularSquareScore w - 2|}
  let D : Set (Fin n → ℝ) := B ∪ C
  have hsub : (pittelTypicalAngles n η)ᶜ ≤ᵐ[spouseAngularLaw n] D := by
    filter_upwards [ae_spouseAngularLaw hn] with w hw
    intro hbad
    by_cases hB : w ∈ B
    · exact Or.inl hB
    · apply Or.inr
      change η < |pittelAngularSquareScore w - 2|
      apply lt_of_not_ge
      intro hC
      apply hbad
      refine ⟨hw.1, hw.2, fun i ↦ le_of_not_gt (fun hi ↦ hB ⟨i, hi⟩), hC⟩
  exact (measure_mono_ae hsub).trans (measure_union_le B C)

theorem tendsto_probReal_compl_pittelTypicalAngles_zero {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (spouseAngularLaw n).real (pittelTypicalAngles n η)ᶜ)
      atTop (𝓝 0) := by
  simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_measure_compl_pittelTypicalAngles_zero hη)

theorem tendsto_probReal_pittelTypicalAngles_one {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ ↦ (spouseAngularLaw n).real (pittelTypicalAngles n η))
      atTop (𝓝 1) := by
  have ht := tendsto_const_nhds.sub (tendsto_probReal_compl_pittelTypicalAngles_zero hη)
      (a := (1 : ℝ))
  simp only [sub_zero] at ht
  refine ht.congr fun n ↦ ?_
  rw [probReal_compl_eq_one_sub (measurableSet_pittelTypicalAngles n η)]
  ring

end LennonPittelFormalization

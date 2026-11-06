module

public import LennonPittel.PittelMeanTail
public import LennonPittel.PittelSimplexRadial

/-!
# Comparing stable marks with the angular law

The stability density is at most a constant times the inverse radial power.
After the radial density cancels that power, an angular event costs its
probability under the uniform simplex share law times a logarithmic factor.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem factorial_mul_radial_inv_power {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C) :
    (n.factorial : ℝ≥0∞) *
        (∫⁻ s in Icc l u, ENNReal.ofReal (C / s ^ n) ∂spouseRadialLaw n) =
      ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) := by
  have hd : Measurable (fun s : ℝ ↦
      ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))) := by fun_prop
  have hg : Measurable (fun s : ℝ ↦ ENNReal.ofReal (C / s ^ n)) := by fun_prop
  rw [spouseRadialLaw, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hg measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc l u ⊆ Ioi 0 from fun _ hs ↦ hl.trans_le hs.1),
    ← restrict_Ioc_eq_restrict_Icc,
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n.factorial)]
  calc
    _ = ∫⁻ s in Ioc l u, ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc l u))]
        with s hs
      have hs' : 0 < s := hl.trans hs.1
      have hnat := Nat.factorial_succ (n - 1)
      rw [show n - 1 + 1 = n by omega] at hnat
      have hnfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
        exact_mod_cast hnat
      change (n.factorial : ℝ≥0∞) *
          (ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)) *
            ENNReal.ofReal (C / s ^ n)) =
        ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hnfac]
      congr 1
      rw [← show n - 1 + 1 = n by omega, pow_succ s (n - 1)]
      field_simp
      simp [mul_comm]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_inv_of_pos hl hlu,
        ← ENNReal.ofReal_mul (by positivity)]

/-- An exceptional female share vector at a stable mark costs at most its
angular probability times the radial logarithmic bound. -/
theorem sum_measure_scoreStable_and_femaleSpouseAngle_le {n : ℕ} (hn : 2 ≤ n)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A}) ≤
      ENNReal.ofReal (Real.exp 2 * (n : ℝ) * Real.log n) * spouseAngularLaw n A := by
  let B : Set (Fin n → ℝ) := {y | 2 ≤ spouseVectorTotal y ∧ spouseAngle y ∈ A}
  let Q : Set (Fin n → ℝ) := {y | ∀ i, 0 ≤ y i}
  let R : Set ℝ := Icc 2 (n : ℝ)
  let f := B.indicator (pittelDensity n)
  let g (s : ℝ) := ENNReal.ofReal (Real.exp 2 / s ^ n)
  have hn' : 0 < n := by omega
  have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : MeasurableSet B := (measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)).inter
      (hA.preimage (measurable_spouseAngle n))
  have hQ : MeasurableSet Q := by
    change MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le measurable_const (measurable_pi_apply i)
  have hf : Measurable f := (measurable_pittelDensity n).indicator hB
  have he (μ : Matching n) :
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A} =
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} := by
    ext x
    change (IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A) ↔
      (IsScoreStable x μ ∧ 2 ≤ spouseVectorTotal (femaleSpouseByHusband μ x) ∧
        spouseAngle (femaleSpouseByHusband μ x) ∈ A)
    rw [femaleSpouseTotal_eq_sum_byHusband, spouseVectorTotal]
  have horthant : (∫⁻ y, f y) = ∫⁻ y, f y ∂(volume.restrict Q) := by
    rw [← lintegral_indicator hQ]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ Q
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hcube : y ∉ pittelScoreCube n := fun hy' ↦ hy fun i ↦ (hy' i (mem_univ i)).1
      have hz : pittelDensity n y = 0 := indicator_of_notMem hcube _
      by_cases hy' : y ∈ B
      · simp only [f, indicator_of_mem hy', hz]
      · exact indicator_of_notMem hy' _
  have hinner (s : ℝ) : (∫⁻ w, f (fun i ↦ s * w i) ∂spouseAngularLaw n) ≤
      R.indicator g s * spouseAngularLaw n A := by
    by_cases hs : s ∈ R
    · rw [indicator_of_mem hs, ← setLIntegral_const, ← lintegral_indicator hA]
      apply lintegral_mono_ae
      filter_upwards [ae_spouseAngularLaw hn'] with w hw
      have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 2).trans_le hs.1
      have hsum : spouseVectorTotal (fun i ↦ s * w i) = s := by
        simp only [spouseVectorTotal, ← Finset.mul_sum, hw.2, mul_one]
      have hangle : spouseAngle (fun i ↦ s * w i) = w := by
        funext i
        change s * w i / spouseVectorTotal (fun j ↦ s * w j) = w i
        rw [hsum, mul_comm s, mul_div_cancel_right₀ _ hs0.ne']
      by_cases hwA : w ∈ A
      · have hmem : (fun i ↦ s * w i) ∈ B := by
          change 2 ≤ spouseVectorTotal (fun i ↦ s * w i) ∧
            spouseAngle (fun i ↦ s * w i) ∈ A
          rw [hsum, hangle]
          exact ⟨hs.1, hwA⟩
        simp only [f, indicator_of_mem hmem, indicator_of_mem hwA]
        simpa only [g, hsum] using
          (pittelDensity_le_inv_pow (y := fun i ↦ s * w i) (hsum.symm ▸ hs.1))
      · have hmem : (fun i ↦ s * w i) ∉ B := fun h ↦ hwA (hangle ▸ h.2)
        simp only [f, indicator_of_notMem hmem, indicator_of_notMem hwA, le_refl]
    · rw [indicator_of_notMem hs, zero_mul, ← lintegral_zero]
      apply lintegral_mono_ae
      filter_upwards [ae_spouseAngularLaw hn'] with w hw
      have hsum : spouseVectorTotal (fun i ↦ s * w i) = s := by
        simp only [spouseVectorTotal, ← Finset.mul_sum, hw.2, mul_one]
      by_cases hmem : (fun i ↦ s * w i) ∈ B
      · have hs2 : 2 ≤ s := hsum ▸ hmem.1
        have hsn : (n : ℝ) < s := lt_of_not_ge fun h ↦ hs ⟨hs2, h⟩
        simp only [f, indicator_of_mem hmem,
          pittelDensity_eq_zero_of_size_lt (hsum.symm ▸ hsn), le_refl]
      · simp only [f, indicator_of_notMem hmem, le_refl]
  simp_rw [he]
  rw [sum_measure_scoreStable_and_femaleSpouse_eq_pittelDensity hB, ← lintegral_indicator hB,
    show B.indicator (pittelDensity n) = f from rfl, horthant,
    lintegral_spouseRadialAngular hn' hf]
  calc
    _ ≤ (n.factorial : ℝ≥0∞) *
        (∫⁻ s, R.indicator g s * spouseAngularLaw n A ∂spouseRadialLaw n) :=
      mul_le_mul_right (lintegral_mono hinner) _
    _ = ENNReal.ofReal ((n : ℝ) * Real.exp 2 * Real.log ((n : ℝ) / 2)) *
        spouseAngularLaw n A := by
      rw [lintegral_mul_const' _ _ (measure_ne_top _ _), lintegral_indicator measurableSet_Icc,
        ← mul_assoc]
      rw [factorial_mul_radial_inv_power hn' (by norm_num) h2n (Real.exp_nonneg _)]
    _ ≤ _ := by
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      rw [mul_comm (n : ℝ) (Real.exp 2)]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith))
        (by positivity)

end LennonPittelFormalization

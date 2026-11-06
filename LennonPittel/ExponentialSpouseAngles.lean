module

public import LennonPittel.PittelSimplexRadial
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Integration

/-!
# Exponential representation of spouse shares

An independent rate-one exponential vector has a joint density depending only on
its total. Thus normalizing its coordinates by that total leaves the angular law
of the nonnegative simplex.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace LennonPittelFormalization

private theorem pi_withDensity_product_of_sigmaFinite {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] :
    (Measure.pi ν).withDensity (fun x ↦ ∏ i, f i (x i)) =
      Measure.pi (fun i ↦ (ν i).withDensity (f i)) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  let g (i : ι) := (s i).indicator (f i)
  have hg (i : ι) : Measurable (g i) := (hf i).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  calc
    _ = ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi ν := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ univ.pi s
      · rw [indicator_of_mem hx]
        exact Finset.prod_congr rfl fun i _ ↦
          (indicator_of_mem (mem_univ_pi.mp hx i) (f i)).symm
      · obtain ⟨i, hi⟩ := not_forall.mp (mt mem_univ_pi.mpr hx)
        rw [indicator_of_notMem hx]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi (f i))).symm
    _ = ∏ i, ∫⁻ x : ∀ j, Ω j, g i (x i) ∂Measure.pi ν :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _
        (iIndepFun_pi fun i ↦ (hg i).aemeasurable)
        (fun i ↦ (hg i).comp (measurable_pi_apply i))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [(measurePreserving_eval ν i).lintegral_comp (hg i), withDensity_apply _ (hs i)]
      exact lintegral_indicator (hs i) (f i)

private theorem expMeasure_one_eq_withDensity_Ici :
    expMeasure 1 =
      (volume.restrict (Ici 0)).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-x))) := by
  rw [expMeasure, gammaMeasure, ← withDensity_indicator measurableSet_Ici]
  congr 1
  funext x
  change exponentialPDF 1 x = _
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x <;> simp [hx]

private theorem ofReal_exp_mul_ofReal_exp_neg (x : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp (-x)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, ENNReal.ofReal_one]

private theorem expMeasure_one_withDensity_exp :
    (expMeasure 1).withDensity (fun x ↦ ENNReal.ofReal (Real.exp x)) =
      volume.restrict (Ici 0) := by
  rw [expMeasure_one_eq_withDensity_Ici, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have h : (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-x))) *
      (fun x ↦ ENNReal.ofReal (Real.exp x)) = 1 := by
    funext x
    exact (mul_comm _ _).trans (ofReal_exp_mul_ofReal_exp_neg x)
  rw [h, withDensity_one]

/-- Independent exponential coordinates have density `exp (-∑ i, x i)` on the orthant. -/
theorem pi_expMeasure_one_eq_withDensity_spouseOrthant (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ expMeasure 1) =
      (volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}).withDensity
        (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i)))) := by
  let ν : Fin n → Measure ℝ := fun _ ↦ expMeasure 1
  let f : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp x)
  let hν : ∀ i, IsProbabilityMeasure (ν i) := fun _ ↦
    isProbabilityMeasure_expMeasure (by norm_num)
  let hσ : ∀ i, SigmaFinite ((ν i).withDensity f) := fun _ ↦
    expMeasure_one_withDensity_exp.symm ▸ inferInstance
  have hf : Measurable f := by fun_prop
  have hsum : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hprod : (fun x : Fin n → ℝ ↦ ∏ i, f (x i)) =
      (fun x ↦ ENNReal.ofReal (Real.exp (∑ i, x i))) := by
    funext x
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ Real.exp_nonneg _)]
  have hbox : (univ.pi fun _ : Fin n ↦ Ici (0 : ℝ)) = {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    ext x
    exact Set.mem_univ_pi
  have htilt : (Measure.pi ν).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (∑ i, x i))) =
      volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    have hpi := @pi_withDensity_product_of_sigmaFinite _ _ _ _ ν hν (fun _ ↦ f) (fun _ ↦ hf) hσ
    rw [← hprod, hpi, ← hbox, volume_pi, Measure.restrict_pi_pi]
    exact congrArg Measure.pi (funext fun _ ↦ expMeasure_one_withDensity_exp)
  rw [← htilt, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have h : (fun x : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (∑ i, x i))) *
      (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i)))) = 1 := by
    funext x
    exact ofReal_exp_mul_ofReal_exp_neg _
  rw [h, withDensity_one]

private theorem map_spouseAngle_pi_expMeasure_one_apply {n : ℕ} (hn : 0 < n)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Measure.map spouseAngle (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) A =
      (∫⁻ s, ENNReal.ofReal (Real.exp (-s)) ∂spouseRadialLaw n) * spouseAngularLaw n A := by
  let E : Set (Fin n → ℝ) := spouseAngle ⁻¹' A
  let F : (Fin n → ℝ) → ℝ≥0∞ :=
    E.indicator (fun x ↦ ENNReal.ofReal (Real.exp (-(∑ i, x i))))
  have hE : MeasurableSet E := hA.preimage (measurable_spouseAngle n)
  have hsum : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hF : Measurable F :=
    (hsum.neg.exp.ennreal_ofReal).indicator hE
  calc
    _ = ∫⁻ x, F x ∂(volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}) := by
      rw [Measure.map_apply (measurable_spouseAngle n) hA,
        pi_expMeasure_one_eq_withDensity_spouseOrthant, withDensity_apply _ hE,
        ← lintegral_indicator hE]
    _ = ∫⁻ s, ∫⁻ w, F (fun i ↦ s * w i) ∂spouseAngularLaw n ∂spouseRadialLaw n :=
      lintegral_spouseRadialAngular hn hF
    _ = ∫⁻ s, ENNReal.ofReal (Real.exp (-s)) * spouseAngularLaw n A ∂spouseRadialLaw n := by
      apply lintegral_congr_ae
      filter_upwards [ae_spouseRadialLaw_pos n] with s hs
      calc
        _ = ∫⁻ w, ENNReal.ofReal (Real.exp (-s)) * A.indicator 1 w ∂spouseAngularLaw n := by
          apply lintegral_congr_ae
          filter_upwards [ae_spouseAngularLaw hn] with w hw
          have htotal : (∑ i, s * w i) = s := by
            rw [← Finset.mul_sum, hw.2, mul_one]
          have hangle : spouseAngle (fun i ↦ s * w i) = w := by
            funext i
            unfold spouseAngle
            rw [htotal, mul_div_cancel_left₀ _ hs.ne']
          by_cases hwA : w ∈ A
          · have hmem : (fun i ↦ s * w i) ∈ E := by
              change spouseAngle (fun i ↦ s * w i) ∈ A
              rwa [hangle]
            simp [F, indicator_of_mem hmem, indicator_of_mem hwA, htotal]
          · have hmem : (fun i ↦ s * w i) ∉ E := by
              change spouseAngle (fun i ↦ s * w i) ∉ A
              rwa [hangle]
            simp [F, indicator_of_notMem hmem, indicator_of_notMem hwA]
        _ = _ := by
          have hI : Measurable (A.indicator (1 : (Fin n → ℝ) → ℝ≥0∞)) :=
            measurable_const.indicator hA
          rw [lintegral_const_mul _ hI, lintegral_indicator_one hA]
    _ = _ := lintegral_mul_const _ (by fun_prop)

/-- Normalizing independent rate-one exponentials gives the exact spouse angular law. -/
theorem map_spouseAngle_pi_expMeasure_one {n : ℕ} (hn : 0 < n) :
    Measure.map spouseAngle (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) = spouseAngularLaw n := by
  let (_i : Fin n) : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have htotal := map_spouseAngle_pi_expMeasure_one_apply hn (A := univ) MeasurableSet.univ
  rw [Measure.map_apply (measurable_spouseAngle n) MeasurableSet.univ, preimage_univ,
    measure_univ, measure_univ, mul_one] at htotal
  ext1 A hA
  rw [map_spouseAngle_pi_expMeasure_one_apply hn hA, ← htotal, one_mul]

end LennonPittelFormalization

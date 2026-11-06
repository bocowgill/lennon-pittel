module

public import LennonPittel.CoexposureScoreEstimates
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Radial decomposition of nonnegative spouse scores

The sum of the scores is the radius, and dividing by it gives a vector of
shares. Scaling a simplex sector proves independence of the two coordinates
without needing a differentiable chart on the simplex boundary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LennonPittelFormalization

/-- The score shares obtained by normalizing the coordinate sum. -/
noncomputable def spouseAngle {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i / (∑ j, x j)

theorem measurable_spouseAngle (n : ℕ) : Measurable (@spouseAngle n) :=
  Measurable.of_eval fun i ↦ (measurable_pi_apply i).div
    (Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j)

/-- The angular law is the share vector of a uniform point in the unit simplex. -/
noncomputable def spouseAngularLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (n.factorial : ℝ≥0∞) • Measure.map spouseAngle (volume.restrict (scoreSimplex n 1))

theorem isProbabilityMeasure_spouseAngularLaw (n : ℕ) :
    IsProbabilityMeasure (spouseAngularLaw n) := by
  refine ⟨?_⟩
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n)
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
    volume_scoreSimplex n zero_le_one]
  have hf : (n.factorial : ℝ≥0∞) ≠ 0 := by positivity
  rw [one_pow, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast,
    smul_eq_mul, ENNReal.mul_inv_cancel hf (by simp)]

instance (n : ℕ) : IsProbabilityMeasure (spouseAngularLaw n) :=
  isProbabilityMeasure_spouseAngularLaw n

/-- The radial part of Lebesgue measure on the nonnegative orthant. -/
noncomputable def spouseRadialLaw (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun s ↦ ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)))

instance (n : ℕ) : SigmaFinite (spouseRadialLaw n) := by
  unfold spouseRadialLaw
  infer_instance

theorem ae_spouseRadialLaw_pos (n : ℕ) :
    ∀ᵐ s ∂(spouseRadialLaw n), 0 < s := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

private theorem measurable_spouseTotal (n : ℕ) :
    Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

private theorem measurableSet_spouseOrthant (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)

theorem ae_spouseAngularLaw {n : ℕ} (hn : 0 < n) :
    ∀ᵐ w ∂(spouseAngularLaw n), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 := by
  have hs0 : volume (scoreSimplex n 0) = 0 := by
    rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
  have hu := ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_scoreSimplex n 1)
  have hz : ∀ᵐ x ∂((volume : Measure (Fin n → ℝ)).restrict (scoreSimplex n 1)),
      x ∉ scoreSimplex n 0 := by
    rw [ae_iff]
    change (volume.restrict (scoreSimplex n 1)) {x | ¬ x ∉ scoreSimplex n 0} = 0
    simp only [not_not, ofPred_mem_eq]
    rw [Measure.restrict_apply (measurableSet_scoreSimplex n 0)]
    exact le_antisymm ((measure_mono inter_subset_left).trans_eq hs0) zero_le
  rw [spouseAngularLaw]
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_spouseAngle n).aemeasurable
    (show MeasurableSet {w : Fin n → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} from
      (measurableSet_spouseOrthant n).inter
        (measurableSet_eq_fun (measurable_spouseTotal n) measurable_const))]
  · filter_upwards [hu, hz] with x hx hx0
    have hsum : 0 < ∑ i, x i := lt_of_not_ge fun h ↦ hx0 ⟨hx.1, h⟩
    exact ⟨fun i ↦ div_nonneg (hx.1 i) hsum.le, by
      simp only [spouseAngle, ← Finset.sum_div, div_self hsum.ne']⟩

/-- Dilating all coordinates by the same factor rescales Lebesgue volume by its n-th power. -/
theorem volume_preimage_spouseScale (n : ℕ) {c : ℝ} (hc : 0 < c)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    volume ((fun (x : Fin n → ℝ) i ↦ c⁻¹ * x i) ⁻¹' s) =
      ENNReal.ofReal (c ^ n) * volume s := by
  let M := Matrix.diagonal (fun _ : Fin n ↦ c⁻¹)
  have hdet : Matrix.det M = (c⁻¹) ^ n := by simp [M]
  have hm : Matrix.det M ≠ 0 := by rw [hdet]; positivity
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hm
  have heq : ⇑(Matrix.toLin' M) = fun x i ↦ c⁻¹ * x i := by
    funext x i
    simp [M, Matrix.diagonal_toLin', LinearMap.smul_apply]
  rw [heq, hdet, ← inv_pow, inv_inv, abs_of_nonneg (by positivity)] at h
  rw [← smul_eq_mul, ← Measure.smul_apply, ← h, Measure.map_apply (by fun_prop) hs]

/-- The radial mass of the interval from zero through a given cutoff. -/
theorem spouseRadialLaw_Iic {n : ℕ} (hn : 0 < n) (u : ℝ) :
    spouseRadialLaw n (Iic u) = ENNReal.ofReal ((max u 0) ^ n / (n.factorial : ℝ)) := by
  rw [spouseRadialLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have heq : Iic u ∩ Ioi (0 : ℝ) = Ioc 0 u := by ext; simp [and_comm]
  rw [heq]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le]
    let f : ℝ → ℝ := fun s ↦ s ^ (n - 1) / ((n - 1).factorial : ℝ)
    have hf : Continuous f := by fun_prop
    change (∫⁻ s in Ioc 0 u, ENNReal.ofReal (f s)) = _
    rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
    · rw [← intervalIntegral.integral_of_le hu.le]
      congr 1
      unfold f
      have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [intervalIntegral.integral_div, integral_pow, hpred, zero_pow hn.ne', sub_zero]
      have hfac : n.factorial = n * (n - 1).factorial := by
        nth_rw 1 [← hpred]
        rw [Nat.factorial_succ, hpred]
      rw [hfac, Nat.cast_mul, div_div]
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hpred
      rw [hcast]
    · exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs ↦ by
        exact div_nonneg (pow_nonneg hs.1.le _) (Nat.cast_nonneg _)
  · have hu' : u ≤ 0 := le_of_not_gt hu
    simp [Ioc_eq_empty_of_le hu', max_eq_right hu', zero_pow hn.ne']

private def angularSector (n : ℕ) (u : ℝ) (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  scoreSimplex n u ∩ spouseAngle ⁻¹' t

private theorem measurableSet_angularSector {n : ℕ} (u : ℝ) {t : Set (Fin n → ℝ)}
    (ht : MeasurableSet t) : MeasurableSet (angularSector n u t) :=
  (measurableSet_scoreSimplex n u).inter (ht.preimage (measurable_spouseAngle n))

private theorem spouseAngle_scale {n : ℕ} (x : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    spouseAngle (fun i ↦ c * x i) = spouseAngle x := by
  funext i
  simp only [spouseAngle, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

private theorem volume_angularSector {n : ℕ} (u : ℝ) (hu : 0 < u)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) =
      ENNReal.ofReal (u ^ n) * volume (angularSector n 1 t) := by
  rw [← volume_preimage_spouseScale n hu (measurableSet_angularSector 1 ht)]
  congr 1
  ext x
  simp only [angularSector, mem_inter_iff, mem_preimage,
    spouseAngle_scale x (inv_ne_zero hu.ne')]
  have hmul : ∀ z : ℝ, u⁻¹ * z ≤ 1 ↔ z ≤ u := fun z ↦ by
    rw [inv_mul_eq_div, div_le_iff₀ hu, one_mul]
  simp only [scoreSimplex, mem_ofPred_eq, ← Finset.mul_sum, hmul]
  have hsign : ∀ z : ℝ, 0 ≤ u⁻¹ * z ↔ 0 ≤ z := fun z ↦
    (mul_nonneg_iff_of_pos_left (inv_pos.mpr hu))
  simp only [hsign]

private theorem spouseAngularLaw_apply {n : ℕ} {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    spouseAngularLaw n t = (n.factorial : ℝ≥0∞) * volume (angularSector n 1 t) := by
  rw [spouseAngularLaw, Measure.smul_apply, Measure.map_apply (measurable_spouseAngle n) ht,
    Measure.restrict_apply (ht.preimage (measurable_spouseAngle n))]
  simp only [smul_eq_mul, angularSector, inter_comm]

private theorem volume_angularSector_eq_mul {n : ℕ} (hn : 0 < n) (u : ℝ)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    volume (angularSector n u t) = spouseRadialLaw n (Iic u) * spouseAngularLaw n t := by
  rw [spouseRadialLaw_Iic hn, spouseAngularLaw_apply ht]
  by_cases hu : 0 < u
  · rw [max_eq_left hu.le, volume_angularSector u hu ht, ← mul_assoc]
    congr 1
    have hnR' : (0 : ℝ) < n.factorial := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ hnR'.ne']
  · have hu' : u ≤ 0 := le_of_not_gt hu
    have hsub : angularSector n u t ⊆ scoreSimplex n 0 :=
      fun _ hx ↦ ⟨hx.1.1, hx.1.2.trans hu'⟩
    have h0 : volume (scoreSimplex n 0) = 0 := by
      rw [volume_scoreSimplex n le_rfl, zero_pow hn.ne', zero_div, ENNReal.ofReal_zero]
    simp only [max_eq_right hu', zero_pow hn.ne', zero_div, ENNReal.ofReal_zero, zero_mul]
    exact le_antisymm ((measure_mono hsub).trans_eq h0) zero_le

private def angularRay {n : ℕ} (t : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i} ∩ spouseAngle ⁻¹' t

private theorem measure_angularRay_radius {n : ℕ} (hn : 0 < n)
    {t : Set (Fin n → ℝ)} (ht : MeasurableSet t) :
    Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t)) =
      spouseAngularLaw n t • spouseRadialLaw n := by
  let μ := Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i) (volume.restrict (angularRay t))
  let ν := spouseAngularLaw n t • spouseRadialLaw n
  have hμ (u : ℝ) : μ (Iic u) = volume (angularSector n u t) := by
    change (Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i)
      (volume.restrict (angularRay t))) (Iic u) = _
    rw [Measure.map_apply (measurable_spouseTotal n) measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage (measurable_spouseTotal n))]
    congr 1
    ext x
    simp only [angularRay, angularSector, scoreSimplex, mem_inter_iff, mem_preimage,
      mem_Iic, mem_ofPred_eq]
    tauto
  have hcdf (u : ℝ) : μ (Iic u) = ν (Iic u) := by
    change μ (Iic u) = (spouseAngularLaw n t • spouseRadialLaw n) (Iic u)
    rw [hμ, volume_angularSector_eq_mul hn u ht, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hfin (u : ℝ) : μ (Iic u) ≠ ∞ := by
    rw [hμ]
    exact ne_top_of_le_ne_top (by rw [volume_scoreSimplex n (le_max_right u 0)]; simp)
      (measure_mono fun x hx ↦ ⟨hx.1.1, hx.1.2.trans (le_max_left u 0)⟩ :
        volume (angularSector n u t) ≤ volume (scoreSimplex n (max u 0)))
  apply Measure.ext_of_Ioc' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hfin b) (measure_mono fun _ hx ↦ hx.2)
  · intro a b hab
    have hν (u : ℝ) : ν (Iic u) ≠ ∞ := hcdf u ▸ hfin u
    rw [← show Iic b \ Iic a = Ioc a b by ext x; simp [and_comm],
      measure_sdiff (Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (hfin a),
      measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet (hν a),
      hcdf a, hcdf b]

private theorem measure_map_spouseRadialAngular {n : ℕ} (hn : 0 < n) :
    Measure.map (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x))
      (volume.restrict {x : Fin n → ℝ | ∀ i, 0 ≤ x i}) =
      (spouseRadialLaw n).prod (spouseAngularLaw n) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  have hmeas : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [Measure.map_apply hmeas (hs.prod ht), Measure.restrict_apply ((hs.prod ht).preimage hmeas)]
  rw [← mul_comm, ← smul_eq_mul, ← Measure.smul_apply, ← measure_angularRay_radius hn ht,
    Measure.map_apply (measurable_spouseTotal n) hs,
    Measure.restrict_apply (hs.preimage (measurable_spouseTotal n))]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, angularRay]
  tauto

/-- Integrating over nonnegative score vectors is integrating their radius and shares
under the product of the radial measure and the angular probability law. -/
theorem lintegral_spouseRadialAngular {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume.restrict {x | ∀ i, 0 ≤ x i})) =
      ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂(spouseAngularLaw n) ∂(spouseRadialLaw n) := by
  let decode : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun p i ↦ p.1 * p.2 i
  have hdecode : Measurable decode := by unfold decode; fun_prop
  have hpair : Measurable (fun x : Fin n → ℝ ↦ (∑ i, x i, spouseAngle x)) :=
    (measurable_spouseTotal n).prodMk (measurable_spouseAngle n)
  rw [← lintegral_prod (fun p ↦ f (decode p)) (hf.comp hdecode).aemeasurable,
    ← measure_map_spouseRadialAngular hn]
  change _ = ∫⁻ z, (f ∘ decode) z ∂(Measure.map (fun x : Fin n → ℝ ↦
    (∑ i, x i, spouseAngle x)) (volume.restrict {x | ∀ i, 0 ≤ x i}))
  rw [lintegral_map (hf.comp hdecode) hpair]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ)))
    (measurableSet_spouseOrthant n)] with x hx
  congr 1
  funext i
  change x i = (∑ j, x j) * (x i / ∑ j, x j)
  by_cases h : (∑ j, x j) = 0
  · have hle : x i ≤ ∑ j, x j :=
      Finset.single_le_sum (fun j _ ↦ hx j) (Finset.mem_univ i)
    rw [h, zero_mul]
    exact le_antisymm (h ▸ hle) (hx i)
  · field_simp

end LennonPittelFormalization

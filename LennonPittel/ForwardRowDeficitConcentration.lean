module

public import LennonPittel.StableMaleSpouseRowLaw
public import LennonPittel.CoexposureSpouseShells
public import LennonPittel.BoundedProductChernoff

/-!
# Concentration of the weighted forward endpoint error

At fixed female spouse scores, the normalized male spouse-score rows are
independent. Multiplying the endpoint error by the stability row density
cancels the dependence on the male score, except for the omitted diagonal
factor. This gives a small mean for the weighted sum.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The weighted endpoint loss in the forward-successor comparison. -/
noncomputable def forwardWeightedEndpointError {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, (y i / spouseVectorTotal y) * Real.exp (-(1 - x i) * spouseVectorTotal y)

/-- The weighted endpoint loss is measurable in the two spouse vectors. -/
theorem measurable_forwardWeightedEndpointError (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ forwardWeightedEndpointError z.1 z.2) := by
  unfold forwardWeightedEndpointError spouseVectorTotal
  fun_prop

private theorem lintegral_stableMaleSpouseRowLaw_endpointError_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (-(1 - z) * spouseVectorTotal y))
      ∂stableMaleSpouseRowLaw y i) ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-spouseVectorTotal y)) := by
  let Y := spouseVectorTotal y
  let K := scoreRowKernel (Finset.univ.erase i) y
  have hK : Measurable (fun z ↦ ENNReal.ofReal (K z)) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hg : Measurable (fun z : ℝ ↦ ENNReal.ofReal (Real.exp (-(1 - z) * Y))) := by
    fun_prop
  have herase : (∑ j ∈ Finset.univ.erase i, y j) = Y - y i :=
    eq_sub_of_add_eq (Finset.sum_erase_add _ y (Finset.mem_univ i))
  unfold stableMaleSpouseRowLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ hK hg]
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (Real.exp 1 * Real.exp (-Y)) ∂unitScoreLaw := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
        MeasurableSet (Icc (0 : ℝ) 1))] with z hz
      change ENNReal.ofReal (K z) * ENNReal.ofReal (Real.exp (-(1 - z) * Y)) ≤ _
      rw [mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hkernel := scoreRowKernel_le_exp (J := Finset.univ.erase i)
        (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hz
      rw [herase] at hkernel
      calc
        _ ≤ Real.exp (-(1 - z) * Y) * Real.exp (-(Y - y i) * z) :=
          mul_le_mul_of_nonneg_left hkernel (Real.exp_pos _).le
        _ = Real.exp (y i * z) * Real.exp (-Y) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          ((mul_le_mul_of_nonneg_right (hy i).2 hz.1).trans (by simpa using hz.2)))
          (Real.exp_pos _).le
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The conditional one-row endpoint error has a uniform first-moment bound. -/
theorem lintegral_normalizedStableMaleSpouseRowLaw_endpointError_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y) (i : Fin n) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (-(1 - z) * spouseVectorTotal y))
      ∂normalizedStableMaleSpouseRowLaw y i) ≤
      ENNReal.ofReal (4 * Real.exp 1 * spouseVectorTotal y *
        Real.exp (-spouseVectorTotal y)) := by
  let Y := spouseVectorTotal y
  have hY : 0 < Y := by linarith
  have hsum : ∑ j ∈ Finset.univ.erase i, y j ≤ Y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
  have hmass : ENNReal.ofReal (1 / (4 * Y)) ≤ stableMaleSpouseRowLaw y i univ := by
    rw [stableMaleSpouseRowLaw_univ y hy i]
    exact ENNReal.ofReal_le_ofReal
      (scoreRowMass_lower (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) (by linarith) hsum)
  have hinv : (stableMaleSpouseRowLaw y i univ)⁻¹ ≤ ENNReal.ofReal (4 * Y) := by
    calc
      _ ≤ (ENNReal.ofReal (1 / (4 * Y)))⁻¹ := ENNReal.inv_le_inv.mpr hmass
      _ = _ := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [normalizedStableMaleSpouseRowLaw, lintegral_smul_measure, smul_eq_mul]
  calc
    _ ≤ ENNReal.ofReal (4 * Y) * ENNReal.ofReal (Real.exp 1 * Real.exp (-Y)) :=
      mul_le_mul' hinv (lintegral_stableMaleSpouseRowLaw_endpointError_le y hy i)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Under the exact male spouse-score product law, the weighted endpoint
error has a Chernoff bound in terms of an upper bound for the female shares. -/
theorem measure_pi_forwardWeightedEndpointError_gt_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ spouseVectorTotal y)
    {B : ℝ} (hB : 0 < B) (hp : ∀ i, y i / spouseVectorTotal y ≤ B) (t : ℝ) :
    (Measure.pi (normalizedStableMaleSpouseRowLaw y)) {x | t < forwardWeightedEndpointError x y} ≤
      ENNReal.ofReal (Real.exp ((-t + (Real.exp 1 - 1) *
        (4 * Real.exp 1 * spouseVectorTotal y * Real.exp (-spouseVectorTotal y))) / B)) := by
  let Y := spouseVectorTotal y
  let ν := normalizedStableMaleSpouseRowLaw y
  let p (i : Fin n) := y i / Y
  let g (i : Fin n) (z : ℝ) := p i * min (Real.exp (-(1 - z) * Y)) 1
  let C := 4 * Real.exp 1 * Y * Real.exp (-Y)
  have hY : 0 < Y := by linarith
  have (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedStableMaleSpouseRowLaw_isProbabilityMeasure y hy hs i
  have hp0 (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have hC : 0 ≤ C := by unfold C; positivity
  have hg (i : Fin n) : Measurable (g i) := by unfold g; fun_prop
  have hb (i : Fin n) (z : ℝ) : g i z ∈ Icc 0 B := by
    refine ⟨mul_nonneg (hp0 i) (le_min (Real.exp_pos _).le zero_le_one), ?_⟩
    exact (mul_le_of_le_one_right (hp0 i) (min_le_right _ _)).trans (hp i)
  have hmean (i : Fin n) : (∫⁻ z, ENNReal.ofReal (g i z) ∂ν i) ≤ ENNReal.ofReal (p i * C) := by
    have hExp : Measurable (fun z : ℝ ↦ ENNReal.ofReal (Real.exp (-(1 - z) * Y))) := by
      fun_prop
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (p i) * ENNReal.ofReal (Real.exp (-(1 - z) * Y)) ∂ν i := by
        apply lintegral_mono
        intro z
        change ENNReal.ofReal (g i z) ≤
          ENNReal.ofReal (p i) * ENNReal.ofReal (Real.exp (-(1 - z) * Y))
        rw [← ENNReal.ofReal_mul (hp0 i)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) (hp0 i))
      _ = ENNReal.ofReal (p i) * ∫⁻ z, ENNReal.ofReal (Real.exp (-(1 - z) * Y)) ∂ν i :=
        lintegral_const_mul _ hExp
      _ ≤ _ := by
        rw [ENNReal.ofReal_mul (hp0 i)]
        exact mul_le_mul_right
          (lintegral_normalizedStableMaleSpouseRowLaw_endpointError_le y hy hs i) _
  have hpSum : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div]
    exact div_self hY.ne'
  have hsum : (∑ i, p i * C) = C := by rw [← Finset.sum_mul, hpSum, one_mul]
  have hsupp : ∀ᵐ x ∂Measure.pi ν, ∀ i, x i ∈ Icc (0 : ℝ) 1 :=
    ae_all_iff.2 fun i ↦ (measurePreserving_eval ν i).quasiMeasurePreserving.ae
      (ae_normalizedStableMaleSpouseRowLaw_mem_Icc y i)
  have hsub : {x | t < forwardWeightedEndpointError x y} ≤ᵐ[Measure.pi ν]
      {x | t < ∑ i, g i (x i)} := by
    filter_upwards [hsupp] with x hx hxt
    have he (i : Fin n) : min (Real.exp (-(1 - x i) * Y)) 1 =
        Real.exp (-(1 - x i) * Y) :=
      min_eq_left (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (hx i).2)) hY.le))
    change t < ∑ i, g i (x i)
    change t < ∑ i, p i * Real.exp (-(1 - x i) * Y) at hxt
    simpa only [g, he] using hxt
  refine (measure_mono_ae hsub).trans ?_
  simpa only [hsum] using measure_pi_boundedSum_gt_le ν g hg hB hb (fun i ↦ p i * C)
    (fun i ↦ mul_nonneg (hp0 i) hC) hmean t

end LennonPittelFormalization

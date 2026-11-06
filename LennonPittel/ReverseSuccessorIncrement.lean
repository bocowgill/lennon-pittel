module

public import LennonPittel.PivotReverseRowLaw

/-!
# The first moment of a designated reverse-successor increment

An available target contributes its male-score threshold. The increment of its
female score is weighted by the probability that no competitor beats it.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*}

private theorem integrableOn_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(a * t))) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t)) (Ioi 0) := by
    simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm] using
      (Real.GammaIntegral_convergent (s := 2) (by norm_num))
  have hscaled : IntegrableOn (fun t : ℝ ↦ (a * t) * Real.exp (-(a * t))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 0 ha).mpr (by simpa only [mul_zero] using h)
  unfold IntegrableOn
  simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using hscaled.const_mul a⁻¹

/-- Weighting the row kernel by the normalized increment costs a second reciprocal
of the competitor sum. -/
theorem scoreRowIncrement_le {J : Finset ι} {v : ι → ℝ}
    (hv : ∀ j ∈ J, v j ∈ Icc 0 1) (ha : 0 < ∑ j ∈ J, v j) :
    (∫ t in (0 : ℝ)..1, t * scoreRowKernel J v t) ≤ 1 / (∑ j ∈ J, v j) ^ 2 := by
  let a := ∑ j ∈ J, v j
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, t * Real.exp (-(a * t)) := by
      refine intervalIntegral.integral_mono_on zero_le_one
        ((continuous_id.mul (continuous_scoreRowKernel J v)).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht ↦ ?_
      refine mul_le_mul_of_nonneg_left ?_ ht.1
      simpa only [a, neg_mul] using scoreRowKernel_le_exp
        (fun j hj ↦ (hv j hj).1) (fun j hj ↦ (hv j hj).2) ht
    _ ≤ ∫ t : ℝ in Ioi 0, t * Real.exp (-(a * t)) := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      refine setIntegral_mono_set (integrableOn_mul_exp_neg_mul_Ioi ha) ?_
        (Filter.Eventually.of_forall fun t ht ↦ ht.1)
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))]
        with t ht
      exact mul_nonneg ht.le (Real.exp_nonneg _)
    _ = 1 / a ^ 2 := by
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ha
      have hΓ : Real.Gamma 2 = 1 := by
        simp
      simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, hΓ,
        div_pow] using h

/-- The exact target-score marginal on the successor event when all cell scores
are uniform on the unit interval and the starting threshold is zero. -/
theorem scoreSuccessorPairEvent_zero_lintegral [Fintype ι] {x : ℝ} {v : ι → ℝ}
    (hx : x ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, (scoreSuccessorPairEvent 0 x v).indicator (fun z ↦ f z.1.1) z
      ∂(unitScorePairLaw.prod (Measure.pi fun _ : ι ↦ unitScorePairLaw))) =
      (∫⁻ t in Ioc (0 : ℝ) 1, f t * ENNReal.ofReal (scoreRowKernel Finset.univ v t)) *
        ENNReal.ofReal x := by
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Iio x
  let Q := Measure.pi fun _ : ι ↦ unitScorePairLaw
  let E := scoreSuccessorPairEvent 0 x v
  let G : ℝ → ℝ≥0∞ := fun t ↦ f t * ENNReal.ofReal (scoreRowKernel Finset.univ v t)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have hG : Measurable G := hf.mul (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hsupp : ∀ᵐ uv ∂unitScorePairLaw, uv ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    unfold unitScorePairLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  change (∫⁻ z, E.indicator (fun z ↦ f z.1.1) z ∂(unitScorePairLaw.prod Q)) = _
  rw [lintegral_prod (E.indicator (fun z ↦ f z.1.1))
    ((hf.comp measurable_fst.fst).indicator hE).aemeasurable]
  have hsection :
      (fun uv ↦ ∫⁻ z, E.indicator (fun z ↦ f z.1.1) (uv, z) ∂Q) =ᵐ[unitScorePairLaw]
        T.indicator (fun uv ↦ G uv.1) := by
    filter_upwards [hsupp] with uv hu
    simp_rw [← Set.indicator_comp_right (Prod.mk uv), Function.comp_def,
      lintegral_indicator_const (measurable_prodMk_left hE)]
    by_cases ht : uv ∈ T
    · have hsec : Prod.mk uv ⁻¹' E = Set.pi univ (fun j ↦ (Iio uv.1 ×ˢ Iio (v j))ᶜ) := by
        ext z
        simp only [mem_preimage, E, scoreSuccessorPairEvent, mem_ofPred_eq, mem_pi, mem_univ,
          true_implies, mem_compl_iff, mem_prod, mem_Iio]
        exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ht.1, ht.2, h⟩⟩
      have hK : ∀ j : ι, 0 ≤ 1 - uv.1 * v j := fun j ↦ sub_nonneg.mpr (calc
        uv.1 * v j ≤ 1 * v j := mul_le_mul_of_nonneg_right hu.1.2 (hv j).1
        _ ≤ 1 := by simpa using (hv j).2)
      have hmass (j : ι) :
          unitScorePairLaw (Iio uv.1 ×ˢ Iio (v j))ᶜ = ENNReal.ofReal (1 - uv.1 * v j) := by
        rw [measure_compl (measurableSet_Iio.prod measurableSet_Iio) (measure_ne_top _ _),
          measure_univ, unitScorePairLaw, Measure.prod_prod, unitScoreLaw_apply_Iio hu.1,
          unitScoreLaw_apply_Iio (hv j), ← ENNReal.ofReal_mul hu.1.1, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ (mul_nonneg hu.1.1 (hv j).1)]
      rw [hsec, Set.indicator_of_mem ht]
      change f uv.1 * (Measure.pi fun _ : ι ↦ unitScorePairLaw) _ =
        f uv.1 * ENNReal.ofReal (∏ j, (1 - uv.1 * v j))
      rw [Measure.pi_pi, ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ hK j)]
      simp only [hmass]
    · have hsec : Prod.mk uv ⁻¹' E = ∅ := by
        exact eq_empty_iff_forall_notMem.mpr fun _ h ↦ ht ⟨h.1, h.2.1⟩
      rw [hsec, measure_empty, mul_zero, Set.indicator_of_notMem ht]
  rw [lintegral_congr_ae hsection, lintegral_indicator hT]
  have hleft : unitScoreLaw.restrict (Ioi (0 : ℝ)) = volume.restrict (Ioc 0 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext t
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, h.1.le, h.2⟩⟩
  have hrestrict : unitScorePairLaw.restrict T =
      (volume.restrict (Ioc (0 : ℝ) 1)).prod (unitScoreLaw.restrict (Iio x)) := by
    rw [← hleft, unitScorePairLaw]
    exact (Measure.prod_restrict _ _).symm
  rw [hrestrict]
  change (∫⁻ uv : ℝ × ℝ, G uv.1 ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
    (unitScoreLaw.restrict (Iio x)))) = _
  have hfun : (fun uv : ℝ × ℝ ↦ G uv.1) = (fun uv : ℝ × ℝ ↦ G uv.1 * 1) := by simp
  rw [hfun, lintegral_prod_mul hG.aemeasurable measurable_const.aemeasurable, lintegral_const,
    one_mul, Measure.restrict_apply_univ, unitScoreLaw_apply_Iio hx]

/-- The exact increment moment for a designated reverse successor in an
inactive column. The affine scale of the female coordinate is retained. -/
theorem reverseSuccessorPairEvent_increment_lintegral [Fintype ι] {y x : ℝ} {v : ι → ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hx : x ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1) :
    (∫⁻ z, (reverseSuccessorPairEvent y x v).indicator
      (fun z ↦ ENNReal.ofReal (z.1.2 - y)) z
      ∂((unitScoreLaw.prod (inactiveFemaleScoreLaw y)).prod
        (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y)))) =
      ENNReal.ofReal
        ((1 - y) * x * (∫ t in (0 : ℝ)..1, t * scoreRowKernel Finset.univ v t)) := by
  let a := 1 - y
  have ha : 0 < a := sub_pos.mpr hy1
  let g (z : ℝ × ℝ) := (z.2, y + a * z.1)
  let inactive := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  have hg : MeasurePreserving g unitScorePairLaw inactive :=
    ((MeasurePreserving.id unitScoreLaw).prod
      (measurePreserving_inactiveFemaleScoreLaw hy0 hy1)).comp Measure.measurePreserving_swap
  have hπ : MeasurePreserving (fun z : ι → ℝ × ℝ ↦ fun j ↦ g (z j))
      (Measure.pi fun _ : ι ↦ unitScorePairLaw) (Measure.pi fun _ : ι ↦ inactive) :=
    measurePreserving_pi _ _ fun _ ↦ hg
  let E := reverseSuccessorPairEvent y x v
  let E₀ := scoreSuccessorPairEvent 0 x v
  have hE : MeasurableSet E := by
    unfold E reverseSuccessorPairEvent
    simp only [ofPred_and, ofPred_forall]
    refine (measurableSet_lt measurable_const measurable_fst.snd).inter
      ((measurableSet_lt measurable_fst.fst measurable_const).inter
        (MeasurableSet.iInter fun j ↦ ?_))
    have h : Measurable (fun z : (ℝ × ℝ) × (ι → ℝ × ℝ) ↦ z.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    exact ((measurableSet_lt h.snd measurable_fst.snd).inter
      (measurableSet_lt h.fst measurable_const)).compl
  have hlt (s t : ℝ) : y + a * s < y + a * t ↔ s < t :=
    (add_lt_add_iff_left y).trans (mul_lt_mul_iff_of_pos_left ha)
  have hzero (t : ℝ) : y < y + a * t ↔ 0 < t := by
    simpa only [mul_zero, add_zero] using hlt 0 t
  have he : Prod.map g (fun z : ι → ℝ × ℝ ↦ fun j ↦ g (z j)) ⁻¹' E = E₀ := by
    ext z
    simp only [mem_preimage, E, E₀, reverseSuccessorPairEvent, scoreSuccessorPairEvent,
      mem_ofPred_eq, Prod.map_fst, Prod.map_snd, g, hzero, hlt]
  have hm : Measurable (E.indicator (fun z ↦ ENNReal.ofReal (z.1.2 - y))) :=
    (measurable_fst.snd.sub_const _).ennreal_ofReal.indicator hE
  change (∫⁻ z, E.indicator (fun z ↦ ENNReal.ofReal (z.1.2 - y)) z
    ∂(inactive.prod (Measure.pi fun _ : ι ↦ inactive))) = _
  rw [← (hg.prod hπ).map_eq, lintegral_map hm (hg.prod hπ).measurable]
  have hfun (z : (ℝ × ℝ) × (ι → ℝ × ℝ)) :
      ENNReal.ofReal ((Prod.map g (fun w : ι → ℝ × ℝ ↦ fun j ↦ g (w j)) z).1.2 - y) =
        ENNReal.ofReal (a * z.1.1) := by
    simp only [Prod.map_fst, g, add_sub_cancel_left]
  simp_rw [← Set.indicator_comp_right, he, Function.comp_def, hfun]
  change (∫⁻ z, (scoreSuccessorPairEvent 0 x v).indicator
    (fun z ↦ ENNReal.ofReal (a * z.1.1)) z
    ∂(unitScorePairLaw.prod (Measure.pi fun _ : ι ↦ unitScorePairLaw))) = _
  rw [scoreSuccessorPairEvent_zero_lintegral hx hv
    ((measurable_const_mul a).ennreal_ofReal)]
  let K := scoreRowKernel Finset.univ v
  have hK {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : 0 ≤ K t := by
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (calc
      t * v j ≤ 1 * v j := mul_le_mul_of_nonneg_right ht.2 (hv j).1
      _ ≤ 1 := by simpa using (hv j).2)
  have hI :
      (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (a * t) * ENNReal.ofReal (K t)) =
        ENNReal.ofReal (a * (∫ t in (0 : ℝ)..1, t * K t)) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
      ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))]
        with t ht
      rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg ha.le ht.1.le)]
    · exact (Continuous.intervalIntegrable
        (show Continuous (fun t : ℝ ↦ a * (t * K t)) by
          exact continuous_const.mul (continuous_id.mul (continuous_scoreRowKernel _ _)))
        0 1).1
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))]
        with t ht
      exact mul_nonneg ha.le (mul_nonneg ht.1.le (hK ht))
  rw [hI, mul_comm _ (ENNReal.ofReal x), ← ENNReal.ofReal_mul hx.1]
  congr 1
  change x * (a * _) = a * x * _
  ring

/-- The unnormalized first increment moment is at most the target threshold
times the affine scale, divided by the square of the available competitor sum. -/
theorem reverseSuccessorPairEvent_increment_le [Fintype ι] {y x : ℝ} {v : ι → ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) (hx : x ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1)
    (hsum : 0 < ∑ j, v j) :
    (∫⁻ z, (reverseSuccessorPairEvent y x v).indicator
      (fun z ↦ ENNReal.ofReal (z.1.2 - y)) z
      ∂((unitScoreLaw.prod (inactiveFemaleScoreLaw y)).prod
        (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y)))) ≤
      ENNReal.ofReal ((1 - y) * x / (∑ j, v j) ^ 2) := by
  rw [reverseSuccessorPairEvent_increment_lintegral hy0 hy1 hx hv, ← mul_one_div]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (scoreRowIncrement_le (fun j _ ↦ hv j) hsum) (mul_nonneg (sub_nonneg.mpr hy1.le) hx.1))

end LennonPittelFormalization

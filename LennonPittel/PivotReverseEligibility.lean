module

public import LennonPittel.PivotForwardRevealCell

/-!
# Reverse eligibility in an inactive score cell

In an inactive cell the female score is a rescaled uniform draw on the
interval above her spouse's score. Independently, the male score is uniform.
These facts give the exact reverse-eligibility and increment probabilities.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LennonPittelFormalization

/-- Rescaling a unit score to the interval above the female spouse score
gives the normalized inactive law. -/
theorem measurePreserving_inactiveFemaleScoreLaw {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    MeasurePreserving (fun u : ℝ ↦ y + (1 - y) * u) unitScoreLaw
      (inactiveFemaleScoreLaw y) := by
  let a := 1 - y
  have ha : 0 < a := sub_pos.mpr hy1
  let f (u : ℝ) := y + a * u
  have hf : Measurable f := by unfold f; fun_prop
  have hpre : f ⁻¹' Icc y 1 = Icc 0 1 := by
    ext u
    change (y ≤ y + a * u ∧ y + a * u ≤ 1) ↔ (0 ≤ u ∧ u ≤ 1)
    have hae : y + a = 1 := by dsimp [a]; ring
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨nonneg_of_mul_nonneg_right (by linarith) ha, le_of_not_gt fun h ↦ ?_⟩
      linarith [mul_lt_mul_of_pos_left h ha]
    · rintro ⟨h0, h1⟩
      exact ⟨by linarith [mul_nonneg ha.le h0],
        by linarith [mul_le_mul_of_nonneg_left h1 ha.le]⟩
  have hmap : Measure.map f (volume : Measure ℝ) = ENNReal.ofReal a⁻¹ • volume := by
    change Measure.map ((y + ·) ∘ (a * ·)) volume = _
    rw [← Measure.map_map (measurable_const_add y) (measurable_const_mul a),
      Real.map_volume_mul_left ha.ne', abs_of_nonneg (inv_nonneg.mpr ha.le),
      Measure.map_smul, map_add_left_eq_self]
    exact (measurable_const_add y).aemeasurable
  have hs : Ici y ∩ Icc (0 : ℝ) 1 = Icc y 1 := by
    ext u
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hy0.trans h.1, h.2⟩⟩
  refine ⟨hf, ?_⟩
  change Measure.map f unitScoreLaw = _
  rw [unitScoreLaw, ← hpre, ← Measure.restrict_map hf measurableSet_Icc, hmap,
    inactiveFemaleScoreLaw, unitScoreLaw_Ici_of_mem_Icc ⟨hy0, hy1.le⟩,
    ← ENNReal.ofReal_inv_of_pos ha, Measure.restrict_smul, unitScoreLaw,
    Measure.restrict_restrict measurableSet_Ici, hs]

/-- The reverse cell test succeeds with probability `x`, and its
normalized female increment has a uniform lower tail. -/
theorem inactiveCell_reverseEligible_increment_mass {x y t : ℝ} (hx : x ∈ Icc 0 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) (ht : t ∈ Icc 0 1) :
    (unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      {z | z.1 < x ∧ y < z.2 ∧ z.2 < y + (1 - y) * t} =
      ENNReal.ofReal x * ENNReal.ofReal t := by
  let a := 1 - y
  have ha : 0 < a := sub_pos.mpr hy1
  let f (u : ℝ) := y + a * u
  have hpre : f ⁻¹' Ioo y (y + a * t) = Ioo 0 t := by
    ext u
    change (y < y + a * u ∧ y + a * u < y + a * t) ↔ (0 < u ∧ u < t)
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨pos_of_mul_pos_right (by linarith) ha.le, lt_of_not_ge fun h ↦ ?_⟩
      linarith [mul_le_mul_of_nonneg_left h ha.le]
    · rintro ⟨h0, h1⟩
      exact ⟨by linarith [mul_pos ha h0], by linarith [mul_lt_mul_of_pos_left h1 ha]⟩
  have hI : unitScoreLaw (Ioo 0 t) = ENNReal.ofReal t := by
    rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo 0 t ⊆ Icc 0 1 from
        fun _ h ↦ ⟨h.1.le, h.2.le.trans ht.2⟩), Real.volume_Ioo, sub_zero]
  have hV : inactiveFemaleScoreLaw y (Ioo y (y + a * t)) = ENNReal.ofReal t := by
    have hmp : MeasurePreserving f unitScoreLaw (inactiveFemaleScoreLaw y) :=
      measurePreserving_inactiveFemaleScoreLaw hy0 hy1
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable measurableSet_Ioo, hpre, hI]
  change (unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (Iio x ×ˢ Ioo y (y + a * t)) = _
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  rw [Measure.prod_prod, unitScoreLaw_Iio_of_mem_Icc hx, hV]

end LennonPittelFormalization

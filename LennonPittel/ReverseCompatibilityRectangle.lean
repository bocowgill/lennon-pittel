module

public import LennonPittel.ReverseSuccessorIncrement

/-!
# The crossed-cell probability in a reverse compatibility test

The male score in an inactive cell is uniform on the unit interval. The
female score is independently uniform above the woman's old spouse score.
After omitting the crossed cell from the successor tests, the width of the
female window can be a measurable function of the remaining scores.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The mass of a score interval is at most its length, including clipped intervals. -/
theorem unitScoreLaw_Ioo_le (a b : ℝ) :
    unitScoreLaw (Ioo a b) ≤ ENNReal.ofReal (b - a) := by
  exact (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := Icc 0 1) (Ioo a b)).trans_eq
    Real.volume_Ioo

/-- An open interval inside the score range has mass equal to its length. -/
theorem unitScoreLaw_Ioo_eq {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitScoreLaw (Ioo a b) = ENNReal.ofReal (b - a) := by
  have hsub : Ioo a b ⊆ Icc 0 1 := fun _ hz ↦ ⟨ha.trans hz.1.le, hz.2.le.trans hb⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub, Real.volume_Ioo]

/-- The female window above her spouse score has mass at most its relative width. -/
theorem inactiveFemaleScoreLaw_Ioo_le {y : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1) (b : ℝ) :
    inactiveFemaleScoreLaw y (Ioo y b) ≤ ENNReal.ofReal ((b - y) / (1 - y)) := by
  rw [inactiveFemaleScoreLaw, Measure.smul_apply, smul_eq_mul,
    unitScoreLaw_Ici_of_mem_Icc ⟨hy₀, hy₁.le⟩, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (fun _ hz ↦ hz.1.le), ENNReal.ofReal_div_of_pos (sub_pos.mpr hy₁),
    div_eq_mul_inv, mul_comm (ENNReal.ofReal (b - y))]
  exact mul_le_mul_right (unitScoreLaw_Ioo_le y b) _

/-- The relative-width formula is exact when the female window fits inside the unit interval. -/
theorem inactiveFemaleScoreLaw_Ioo_eq {y b : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1) (hb : b ≤ 1) :
    inactiveFemaleScoreLaw y (Ioo y b) = ENNReal.ofReal ((b - y) / (1 - y)) := by
  rw [inactiveFemaleScoreLaw, Measure.smul_apply, smul_eq_mul,
    unitScoreLaw_Ici_of_mem_Icc ⟨hy₀, hy₁.le⟩, Measure.restrict_apply measurableSet_Ioo,
    inter_eq_left.mpr (fun _ hz ↦ hz.1.le), unitScoreLaw_Ioo_eq hy₀ hb,
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hy₁), div_eq_mul_inv, mul_comm]

/-- The open rectangle with old scores `x,y` and increments `dx,dy`. -/
def reverseCompatibilityRectangle (x y dx dy : ℝ) : Set (ℝ × ℝ) :=
  Ioo x (x + dx) ×ˢ Ioo y (y + dy)

/-- The crossed-cell probability is bounded by the rectangle's normalized area. -/
theorem inactiveCell_compatibilityRectangle_mass_le {x y dx dy : ℝ}
    (hy₀ : 0 ≤ y) (hy₁ : y < 1) :
    (unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (reverseCompatibilityRectangle x y dx dy) ≤
      ENNReal.ofReal (dx / (1 - y)) * ENNReal.ofReal dy := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy₀ hy₁
  unfold reverseCompatibilityRectangle
  rw [Measure.prod_prod]
  refine (mul_le_mul' (unitScoreLaw_Ioo_le x (x + dx))
    (inactiveFemaleScoreLaw_Ioo_le hy₀ hy₁ (y + dy))).trans_eq ?_
  rw [add_sub_cancel_left, add_sub_cancel_left, ENNReal.ofReal_div_of_pos (sub_pos.mpr hy₁),
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hy₁)]
  simp only [div_eq_mul_inv]
  ac_rfl

/-- The normalized area formula is exact when both windows stay inside their score ranges. -/
theorem inactiveCell_compatibilityRectangle_mass {x y dx dy : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x + dx ≤ 1) (hy₀ : 0 ≤ y) (hy₁ : y < 1) (hy₂ : y + dy ≤ 1)
    (hdx : 0 ≤ dx) :
    (unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (reverseCompatibilityRectangle x y dx dy) =
      ENNReal.ofReal (dx * dy / (1 - y)) := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy₀ hy₁
  rw [reverseCompatibilityRectangle, Measure.prod_prod, unitScoreLaw_Ioo_eq hx₀ hx₁,
    inactiveFemaleScoreLaw_Ioo_eq hy₀ hy₁ hy₂, add_sub_cancel_left, add_sub_cancel_left,
    ← ENNReal.ofReal_mul hdx, mul_div_assoc]

/-- Under the product with the remainder law, the crossed-cell probability on a
relaxed event is bounded by the fixed male width times the weighted female increment. -/
theorem inactiveCell_compatibilityRectangle_prod_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {E : Set Ω} (hE : MeasurableSet E) {dy : Ω → ℝ} (hdy : Measurable dy)
    {x y dx : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1) :
    (μ.prod (unitScoreLaw.prod (inactiveFemaleScoreLaw y)))
      {z | z.1 ∈ E ∧ z.2 ∈ reverseCompatibilityRectangle x y dx (dy z.1)} ≤
      ENNReal.ofReal (dx / (1 - y)) * ∫⁻ t in E, ENNReal.ofReal (dy t) ∂μ := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy₀ hy₁
  let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  let S : Set (Ω × (ℝ × ℝ)) :=
    {z | z.1 ∈ E ∧ z.2 ∈ reverseCompatibilityRectangle x y dx (dy z.1)}
  have hS : MeasurableSet S := by
    change MeasurableSet ((Prod.fst ⁻¹' E) ∩
      {z : Ω × (ℝ × ℝ) | z.2 ∈ reverseCompatibilityRectangle x y dx (dy z.1)})
    refine (hE.preimage measurable_fst).inter ?_
    change MeasurableSet ((fun z : Ω × (ℝ × ℝ) ↦ z.2.1) ⁻¹' Ioo x (x + dx) ∩
      ({z | y < z.2.2} ∩ {z | z.2.2 < y + dy z.1}))
    exact (measurableSet_Ioo.preimage measurable_snd.fst).inter
      ((measurableSet_lt measurable_const measurable_snd.snd).inter
        (measurableSet_lt measurable_snd.snd (measurable_const.add (hdy.comp measurable_fst))))
  change (μ.prod ν) S ≤ _
  rw [Measure.prod_apply hS, ← lintegral_const_mul _ hdy.ennreal_ofReal, ← lintegral_indicator hE]
  refine lintegral_mono fun t ↦ ?_
  by_cases ht : t ∈ E
  · have hsec : Prod.mk t ⁻¹' S = reverseCompatibilityRectangle x y dx (dy t) := by
      ext z
      simp [S, ht]
    rw [hsec, indicator_of_mem ht]
    exact inactiveCell_compatibilityRectangle_mass_le hy₀ hy₁
  · have hsec : Prod.mk t ⁻¹' S = ∅ := by
      ext z
      simp [S, ht]
    simp [hsec]

/-- The female normalization cancels the affine scale in an increment bound. -/
theorem inactiveCell_compatibilityRectangle_prod_mass_le_of_increment_bound {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) {E : Set Ω} (hE : MeasurableSet E) {dy : Ω → ℝ}
    (hdy : Measurable dy) {x y dx K : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1) (hdx : 0 ≤ dx)
    (hK : (∫⁻ t in E, ENNReal.ofReal (dy t) ∂μ) ≤ ENNReal.ofReal ((1 - y) * K)) :
    (μ.prod (unitScoreLaw.prod (inactiveFemaleScoreLaw y)))
      {z | z.1 ∈ E ∧ z.2 ∈ reverseCompatibilityRectangle x y dx (dy z.1)} ≤
      ENNReal.ofReal (dx * K) := by
  refine (inactiveCell_compatibilityRectangle_prod_mass_le μ hE hdy hy₀ hy₁).trans ?_
  refine (mul_le_mul_right hK _).trans_eq ?_
  rw [← ENNReal.ofReal_mul (div_nonneg hdx (sub_nonneg.mpr hy₁.le)), ← mul_assoc,
    div_mul_cancel₀ dx (sub_ne_zero.mpr hy₁.ne')]

/-- One omitted cell blocks a prescribed relaxed successor with probability
at most the male window times the target threshold divided by the squared
kept competitor mass. The omitted cell is a separate product coordinate. -/
theorem inactiveCell_reverseSuccessorCrossBlocker_mass_le {ι : Type*} [Fintype ι]
    {y x target dx : ℝ} {v : ι → ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1) (hdx : 0 ≤ dx)
    (htarget : target ∈ Icc 0 1) (hv : ∀ j, v j ∈ Icc 0 1) (hS : 0 < ∑ j, v j) :
    let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
    let μ := ν.prod (Measure.pi fun _ : ι ↦ ν)
    (μ.prod ν) {z | z.1 ∈ reverseSuccessorPairEvent y target v ∧
      z.2 ∈ reverseCompatibilityRectangle x y dx (z.1.1.2 - y)} ≤
      ENNReal.ofReal (dx * (target / (∑ j, v j) ^ 2)) := by
  dsimp only
  have hE := measurableSet_reverseSuccessorPairEvent y target v
  refine inactiveCell_compatibilityRectangle_prod_mass_le_of_increment_bound _
    hE (measurable_fst.snd.sub_const y) hy₀ hy₁ hdx ?_
  simpa only [lintegral_indicator hE, mul_div_assoc] using
    reverseSuccessorPairEvent_increment_le hy₀ hy₁ htarget hv hS

end LennonPittelFormalization

module

public import LennonPittel.CoexposureSpouseMarginal

/-!
# Male spouse scores at a fixed female spouse vector

The stability kernel for a male spouse score is a single row product.
After normalization, a short interval of scores of order the reciprocal
female total carries a uniform positive probability.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The unnormalized male spouse-score law in row `i` of the stability kernel. -/
noncomputable def stableMaleSpouseRowLaw {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : Measure ℝ :=
  unitScoreLaw.withDensity (fun t ↦ ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t))

/-- The male spouse-score law conditional on the fixed female spouse vector and stability. -/
noncomputable def normalizedStableMaleSpouseRowLaw {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    Measure ℝ :=
  (stableMaleSpouseRowLaw y i univ)⁻¹ • stableMaleSpouseRowLaw y i

/-- The total unnormalized mass is the integrated row kernel. -/
theorem stableMaleSpouseRowLaw_univ {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    stableMaleSpouseRowLaw y i univ =
      ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1) := by
  rw [stableMaleSpouseRowLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_scoreRowKernel_unitScoreLaw _ y hy

/-- The unnormalized male spouse-score law has finite total mass. -/
theorem stableMaleSpouseRowLaw_isFiniteMeasure {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    IsFiniteMeasure (stableMaleSpouseRowLaw y i) :=
  ⟨(stableMaleSpouseRowLaw_univ y hy i).symm ▸ ENNReal.ofReal_lt_top⟩

/-- On the score band, every stability row has positive total mass. -/
theorem stableMaleSpouseRowLaw_univ_pos {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    0 < stableMaleSpouseRowLaw y i univ := by
  have hle : ∑ j ∈ Finset.univ.erase i, y j ≤ ∑ j, y j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
  have hY : 0 < ∑ j, y j := by linarith
  rw [stableMaleSpouseRowLaw_univ y hy i, ENNReal.ofReal_pos]
  exact (by positivity : 0 < 1 / (4 * ∑ j, y j)).trans_le
    (scoreRowMass_lower (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) (by linarith) hle)

/-- The normalized male spouse-score row is a probability measure. -/
theorem normalizedStableMaleSpouseRowLaw_isProbabilityMeasure {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    IsProbabilityMeasure (normalizedStableMaleSpouseRowLaw y i) := by
  have := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  refine ⟨?_⟩
  rw [normalizedStableMaleSpouseRowLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'
    (measure_ne_top _ _)

/-- The unnormalized row is its total mass times the normalized row law. -/
theorem stableMaleSpouseRowLaw_eq_smul_normalized {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    stableMaleSpouseRowLaw y i =
      stableMaleSpouseRowLaw y i univ • normalizedStableMaleSpouseRowLaw y i := by
  have := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  rw [normalizedStableMaleSpouseRowLaw, smul_smul,
    ENNReal.mul_inv_cancel (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'
      (measure_ne_top _ _), one_smul]

/-- The normalized row is supported on the unit interval. -/
theorem ae_normalizedStableMaleSpouseRowLaw_mem_Icc {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    ∀ᵐ t ∂normalizedStableMaleSpouseRowLaw y i, t ∈ Icc (0 : ℝ) 1 := by
  have h := withDensity_absolutelyContinuous unitScoreLaw
    (fun t ↦ ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t))
  exact (Measure.smul_absolutelyContinuous.trans h).ae_le
    (ae_restrict_mem (μ := volume) measurableSet_Icc)

private theorem scoreRowMass_erase_le_two_div {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤ 2 / ∑ j, y j := by
  let Y := ∑ j, y j
  have hY : 0 < Y := by linarith
  have hrate : 0 < Y - 1 := by linarith
  have hsum := Finset.sum_erase_add (s := Finset.univ) y (Finset.mem_univ i)
  have herase : Y - 1 ≤ ∑ j ∈ Finset.univ.erase i, y j := by
    linarith only [hsum, (hy i).2]
  calc
    _ ≤ 1 / (Y - 1) := by
      simpa using scoreRowMass_le_exp_tail (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
        hrate herase (a := 0) (b := 1) le_rfl zero_le_one le_rfl
    _ ≤ 2 / Y := by
      apply (div_le_div_iff₀ hrate hY).mpr
      linarith

private theorem one_div_eight_mul_le_stableMaleSpouseRowLaw_goodInterval {n : ℕ}
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    ENNReal.ofReal (1 / (8 * ∑ j, y j)) ≤
      stableMaleSpouseRowLaw y i (Ioc (1 / (4 * ∑ j, y j)) (1 / (2 * ∑ j, y j))) := by
  let Y := ∑ j, y j
  let a := 1 / (4 * Y)
  let b := 1 / (2 * Y)
  have hY : 0 < Y := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : b ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2 * Y)).mpr (by linarith)
  have hle : ∑ j ∈ Finset.univ.erase i, y j ≤ Y :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
  have hsub : Ioc a b ⊆ Icc (0 : ℝ) 1 :=
    fun _ ht ↦ ⟨ha.trans ht.1.le, ht.2.trans hb⟩
  have hvol : unitScoreLaw (Ioc a b) = ENNReal.ofReal (b - a) := by
    rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr hsub, Real.volume_Ioc]
  have hhalf : (1 / 2 : ℝ) * (b - a) = 1 / (8 * Y) := by
    dsimp [a, b]
    field_simp
    norm_num
  change ENNReal.ofReal (1 / (8 * Y)) ≤ stableMaleSpouseRowLaw y i (Ioc a b)
  rw [← hhalf, ENNReal.ofReal_mul (by norm_num), ← hvol, stableMaleSpouseRowLaw,
    withDensity_apply _ measurableSet_Ioc]
  have heq : ENNReal.ofReal (1 / 2 : ℝ) * unitScoreLaw (Ioc a b) =
      ∫⁻ _t in Ioc a b, ENNReal.ofReal (1 / 2 : ℝ) ∂unitScoreLaw := by
    rw [lintegral_const, Measure.restrict_apply_univ]
  rw [heq]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := unitScoreLaw)
    (measurableSet_Ioc : MeasurableSet (Ioc a b))] with t ht
  have ht0 : 0 ≤ t := ha.trans ht.1.le
  have hprod : t * (∑ j ∈ Finset.univ.erase i, y j) ≤ 1 / 2 := calc
    _ ≤ t * Y := mul_le_mul_of_nonneg_left hle ht0
    _ ≤ b * Y := mul_le_mul_of_nonneg_right ht.2 hY.le
    _ = _ := by
      dsimp [b]
      field_simp
  apply ENNReal.ofReal_le_ofReal
  exact (by linarith : (1 / 2 : ℝ) ≤ 1 - t * ∑ j ∈ Finset.univ.erase i, y j).trans
    (one_sub_sum_le_scoreRowKernel (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
      ⟨ht0, ht.2.trans hb⟩)

/-- A normalized stability row assigns probability at least one sixteenth
to male scores between one quarter and one half of the reciprocal female total. -/
theorem normalizedStableMaleSpouseRowLaw_goodInterval_ge {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) (i : Fin n) :
    ENNReal.ofReal (1 / 16 : ℝ) ≤
      normalizedStableMaleSpouseRowLaw y i
        (Ioc (1 / (4 * ∑ j, y j)) (1 / (2 * ∑ j, y j))) := by
  let Y := ∑ j, y j
  let A := Ioc (1 / (4 * Y)) (1 / (2 * Y))
  let M := stableMaleSpouseRowLaw y i univ
  have := stableMaleSpouseRowLaw_isFiniteMeasure y hy i
  have hM₀ : M ≠ 0 := (stableMaleSpouseRowLaw_univ_pos y hy hs i).ne'
  have hMtop : M ≠ ⊤ := measure_ne_top _ _
  have hbound : ENNReal.ofReal (1 / 16 : ℝ) * M ≤ stableMaleSpouseRowLaw y i A := calc
    _ ≤ ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal (2 / Y) := by
      apply mul_le_mul_right _ _
      rw [show M = _ from stableMaleSpouseRowLaw_univ y hy i]
      exact ENNReal.ofReal_le_ofReal (scoreRowMass_erase_le_two_div y hy hs i)
    _ = ENNReal.ofReal (1 / (8 * Y)) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ ≤ _ := one_div_eight_mul_le_stableMaleSpouseRowLaw_goodInterval y hy hs i
  calc
    _ = ENNReal.ofReal (1 / 16 : ℝ) * (M⁻¹ * M) := by
      rw [ENNReal.inv_mul_cancel hM₀ hMtop, mul_one]
    _ = M⁻¹ * (ENNReal.ofReal (1 / 16 : ℝ) * M) := by ac_rfl
    _ ≤ M⁻¹ * stableMaleSpouseRowLaw y i A := mul_le_mul_right hbound _
    _ = _ := by rw [normalizedStableMaleSpouseRowLaw, Measure.smul_apply, smul_eq_mul]

end LennonPittelFormalization

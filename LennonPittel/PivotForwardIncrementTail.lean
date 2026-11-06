module

public import LennonPittel.PivotMarkedCutoffBridge
public import LennonPittel.PivotSpouseBandMask
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential moment of the forward successor increment

For a prescribed arc, condition on its target cell and multiply the probabilities
that each competitor fails to beat it. Relative to the stable row mass, this gives
exponential decay in the target's excess above the incumbent score.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private theorem lintegral_scoreSuccessorPairEvent [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in scoreSuccessorPairEvent x v y, f z.1.1
      ∂((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))) =
      (∫⁻ u in Ioc x 1, f u * ENNReal.ofReal (scoreRowKernel Finset.univ y u)) *
        ENNReal.ofReal v := by
  let ν := rowNonblockingLaw x v
  let Q := Measure.pi fun j ↦ rowNonblockingLaw x (y j)
  let E := scoreSuccessorPairEvent x v y
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let G : ℝ → ℝ≥0∞ := fun u ↦ f u * ENNReal.ofReal (scoreRowKernel Finset.univ y u)
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hG : Measurable G := hf.mul (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hsupp : ∀ᵐ uv ∂ν, uv ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    unfold ν rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  change (∫⁻ z in E, f z.1.1 ∂(ν.prod Q)) = _
  rw [← lintegral_indicator hE, lintegral_prod (E.indicator (fun z ↦ f z.1.1))
    ((hf.comp measurable_fst.fst).indicator hE).aemeasurable]
  have hsection :
      (fun uv ↦ ∫⁻ z, E.indicator (fun z ↦ f z.1.1) (uv, z) ∂Q) =ᵐ[ν]
        T.indicator (fun uv ↦ G uv.1) := by
    filter_upwards [hsupp] with uv hu
    simp_rw [← Set.indicator_comp_right (Prod.mk uv), Function.comp_def,
      lintegral_indicator_const (measurable_prodMk_left hE)]
    by_cases ht : uv ∈ T
    · have hsec : Prod.mk uv ⁻¹' E = Set.pi univ (fun j ↦ (Iio uv.1 ×ˢ Iio (y j))ᶜ) := by
        ext z
        simp only [mem_preimage, E, scoreSuccessorPairEvent, mem_ofPred_eq, Set.mem_pi, mem_univ,
          true_implies, mem_compl_iff, mem_prod, mem_Iio]
        exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ht.1, ht.2, h⟩⟩
      rw [hsec, Set.indicator_of_mem ht]
      change f uv.1 * Q _ = f uv.1 * ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)
      have hnonneg (j : ι) : 0 ≤ 1 - uv.1 * y j := sub_nonneg.mpr (calc
        uv.1 * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hu.1.2 (hy j).1
        _ ≤ 1 := by simpa using (hy j).2)
      dsimp only [Q]
      rw [Measure.pi_pi]
      simp only [rowNonblockingLaw_apply_avoiding ht.1.le hu.1 (hy _), scoreRowKernel,
        ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ hnonneg j)]
    · have hsec : Prod.mk uv ⁻¹' E = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun _ h ↦ ht ⟨h.1, h.2.1⟩
      rw [hsec, measure_empty, mul_zero, Set.indicator_of_notMem ht]
  rw [lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio v : Set (ℝ × ℝ))ᶜ := by
    intro uv h h'
    exact (not_lt_of_ge (show x < uv.1 from h.1).le) (show uv.1 < x from h'.1)
  have hrestrict : ν.restrict T =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio v)) := by
    dsimp only [ν]
    rw [rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    exact (Measure.prod_restrict _ _).symm
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  rw [hrestrict, hleft]
  rw [show (fun uv : ℝ × ℝ ↦ G uv.1) = (fun uv : ℝ × ℝ ↦ G uv.1 * 1) by simp]
  rw [lintegral_prod_mul hG.aemeasurable measurable_const.aemeasurable, lintegral_const,
    one_mul, Measure.restrict_apply_univ, unitScoreLaw_apply_Iio hv]

private theorem scoreRowKernel_le_at_mul_exp {J : Finset ι} {y : ι → ℝ} {x u : ℝ}
    (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxu : x ≤ u) (hu : u ≤ 1) :
    scoreRowKernel J y u ≤
      scoreRowKernel J y x * Real.exp (-(u - x) * ∑ j ∈ J, y j) := by
  unfold scoreRowKernel
  have hnonneg (j : ι) (hj : j ∈ J) : 0 ≤ 1 - u * y j := by
    exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hu (hy j hj).1).trans
      (by simpa only [one_mul] using (hy j hj).2))
  calc
    _ ≤ ∏ j ∈ J, (1 - x * y j) * Real.exp (-((u - x) * y j)) := by
      apply Finset.prod_le_prod₀ hnonneg
      intro j hj
      have hden : 0 ≤ 1 - x * y j :=
        (hnonneg j hj).trans (sub_le_sub_left (mul_le_mul_of_nonneg_right hxu (hy j hj).1) 1)
      refine (show 1 - u * y j ≤ (1 - x * y j) * (1 - (u - x) * y j) by
        nlinarith only [mul_nonneg (mul_nonneg hx (hy j hj).1)
          (mul_nonneg (sub_nonneg.mpr hxu) (hy j hj).1)]).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg _) hden
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ (neg_mul (u - x) (y j)).symm

private theorem lintegral_exp_neg_increment_le {x a : ℝ} (ha : 0 < a) :
    (∫⁻ u in Ioc x 1, ENNReal.ofReal (Real.exp (-a * (u - x)))) ≤
      ENNReal.ofReal (1 / a) := by
  refine (lintegral_mono_set (μ := volume) Ioc_subset_Ioi_self).trans_eq ?_
  have he (u : ℝ) : Real.exp (-a * (u - x)) = Real.exp (a * x) * Real.exp (-a * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hf : IntegrableOn (fun u : ℝ ↦ Real.exp (-a * (u - x))) (Ioi x) := by
    rw [show (fun u : ℝ ↦ Real.exp (-a * (u - x))) =
      (fun u : ℝ ↦ Real.exp (a * x) * Real.exp (-a * u)) from funext he]
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) x).const_mul (Real.exp (a * x))
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun _ ↦ Real.exp_nonneg _)]
  congr 1
  rw [show (fun u : ℝ ↦ Real.exp (-a * (u - x))) =
      (fun u : ℝ ↦ Real.exp (a * x) * Real.exp (-a * u)) from funext he,
    integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr ha), neg_div_neg_eq,
    ← mul_div_assoc, ← Real.exp_add]
  rw [show a * x + -a * x = 0 by ring, Real.exp_zero]

private theorem sum_forwardCompetitors {n : ℕ} (y : Fin n → ℝ)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val) =
      (∑ k, y k) - y i - y j.val := by
  classical
  have houter : (∑ k : {k : Fin n // i ≠ k}, y k.val) = (∑ k, y k) - y i := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp [ne_comm]) y]
    linarith [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]
  let f := fun k : {k : Fin n // i ≠ k} ↦ y k.val
  change (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, f k.val) =
    (∑ k, y k) - y i - f j
  rw [← Finset.sum_subtype (Finset.univ.erase j) (by simp) f]
  linarith [Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)]

/-- The normalized stable row has a controlled exponential moment on a
prescribed successor event. The tilt uses one quarter of the female total. -/
theorem lintegral_forwardSuccessor_exp_le {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hx : (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2))
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc (0 : ℝ) 1)
    (hY : 4 ≤ ∑ k, (diagonalPairAt d k).2) :
    (∫⁻ r in scoreRowSuccessorEvent d i j,
      ENNReal.ofReal (Real.exp (((∑ k, (diagonalPairAt d k).2) / 4) *
        ((r j).1 - (diagonalPairAt d i).1))) ∂normalizedStableScoreRowLaw d i) ≤
      ENNReal.ofReal (8 * forwardSpouseWeight d j.val) := by
  classical
  let x := (diagonalPairAt d i).1
  let y (k : Fin n) := (diagonalPairAt d k).2
  let Y := ∑ k, y k
  let z (k : {k : {k : Fin n // i ≠ k} // k ≠ j}) := y k.val.val
  let K := scoreRowKernel Finset.univ z
  let m (k : {k : Fin n // i ≠ k}) := rowNonblockingLaw x (y k.val)
  let f (u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((Y / 4) * (u - x)))
  let E := scoreSuccessorPairEvent x (y j.val) z
  let Erow := scoreRowSuccessorEvent d i j
  let ν := stableScoreRowLaw d i
  let νsplit := (m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)
  let split := fun r : {k : Fin n // i ≠ k} → ℝ × ℝ ↦
    (r j, fun k : {k // k ≠ j} ↦ r k.val)
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hY₀ : 0 < Y := (by norm_num : (0 : ℝ) < 4).trans_le hY
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hK : 0 ≤ K x := by
    unfold K scoreRowKernel
    exact Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right hx'.2 (hy k.val.val).1).trans
        (by simpa only [one_mul] using (hy k.val.val).2))
  have hpres : MeasurePreserving split ν νsplit := measurePreserving_rowTargetAndCompetitors m j
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have hErow : MeasurableSet Erow := measurableSet_scoreRowSuccessorEvent _ _ _
  have hsplit :
      (∫⁻ r in Erow, f (r j).1 ∂ν) = ∫⁻ u in E, f u.1.1 ∂νsplit := by
    rw [← lintegral_indicator hErow, ← lintegral_indicator hE]
    exact hpres.lintegral_comp ((hf.comp measurable_fst.fst).indicator hE)
  have hden (k : Fin n) : 1 / 2 ≤ 1 - x * y k := by
    have hxy : x * y k ≤ x := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hy k).2 hx.1
    linarith only [hxy, hx.2]
  have hmass : ν univ = ENNReal.ofReal ((1 - x * y j.val) * K x) := by
    have hh := hpres.measure_preimage (s := univ) MeasurableSet.univ.nullMeasurableSet
    rw [preimage_univ] at hh
    rw [hh, ← univ_prod_univ]
    change (m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val) (univ ×ˢ univ) = _
    rw [Measure.prod_prod, Measure.pi_univ]
    have hm (k : {k : Fin n // i ≠ k}) : m k univ = ENNReal.ofReal (1 - x * y k.val) :=
      rowNonblockingLaw_apply_univ hx' (hy k.val)
    have hden₀ (k : Fin n) : 0 ≤ 1 - x * y k :=
      (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hden k)
    simp_rw [hm]
    rw [← ENNReal.ofReal_prod_of_nonneg
        (fun (k : {k : {k : Fin n // i ≠ k} // k ≠ j}) _ ↦ hden₀ k.val.val),
      ← ENNReal.ofReal_mul (hden₀ j.val)]
    rfl
  have hS : Y / 2 ≤ ∑ k, z k := by
    change Y / 2 ≤ ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val
    rw [sum_forwardCompetitors y i j]
    linarith only [hY, (hy i).2, (hy j.val).2]
  have hI : (∫⁻ u in Ioc x 1, f u * ENNReal.ofReal (K u)) ≤
      ENNReal.ofReal (K x) * ENNReal.ofReal (4 / Y) := by
    let g (u : ℝ) := ENNReal.ofReal (Real.exp (-(Y / 4) * (u - x)))
    have hg : Measurable g := by
      dsimp only [g]
      fun_prop
    calc
      _ ≤ ∫⁻ u in Ioc x 1, ENNReal.ofReal (K x) * g u := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := x) (b := 1))]
          with u hu
        have hker := scoreRowKernel_le_at_mul_exp (J := Finset.univ) (y := z)
          (fun k _ ↦ hy k.val.val) hx.1 hu.1.le hu.2
        change K u ≤ K x * _ at hker
        have hexp : (Y / 4) * (u - x) + -(u - x) * ∑ k, z k ≤ -(Y / 4) * (u - x) := by
          nlinarith only [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hu.1.le)]
        calc
          _ ≤ f u * ENNReal.ofReal (K x * Real.exp (-(u - x) * ∑ k, z k)) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hker) _
          _ ≤ _ := by
            rw [ENNReal.ofReal_mul hK, ← mul_assoc, mul_comm (f u), mul_assoc]
            apply mul_le_mul_right
            change ENNReal.ofReal (Real.exp _) * ENNReal.ofReal (Real.exp _) ≤ ENNReal.ofReal _
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
      _ = ENNReal.ofReal (K x) * (∫⁻ u in Ioc x 1, g u) := lintegral_const_mul _ hg
      _ ≤ _ := mul_le_mul_right
        ((lintegral_exp_neg_increment_le (x := x) (by positivity : 0 < Y / 4)).trans_eq
          (congrArg ENNReal.ofReal (by ring))) _
  have hun : (∫⁻ r in Erow, f (r j).1 ∂ν) ≤
      ν univ * ENNReal.ofReal (8 * forwardSpouseWeight d j.val) := by
    have he :
        (∫⁻ u in E, f u.1.1 ∂νsplit) =
          (∫⁻ u in Ioc x 1, f u * ENNReal.ofReal (K u)) * ENNReal.ofReal (y j.val) :=
      lintegral_scoreSuccessorPairEvent (y := z) hx' (hy j.val) (fun k ↦ hy k.val.val) hf
    rw [hsplit, he]
    refine (mul_le_mul_left hI _).trans ?_
    rw [hmass, ← ENNReal.ofReal_mul hK,
      ← ENNReal.ofReal_mul (mul_nonneg hK (by positivity)),
      ← ENNReal.ofReal_mul (mul_nonneg (by linarith [hden j.val]) hK)]
    apply ENNReal.ofReal_le_ofReal
    change K x * (4 / Y) * y j.val ≤ (1 - x * y j.val) * K x * (8 * (y j.val / Y))
    calc
      _ = (1 / 2) * (K x * (8 * (y j.val / Y))) := by ring
      _ ≤ (1 - x * y j.val) * (K x * (8 * (y j.val / Y))) :=
        mul_le_mul_of_nonneg_right (hden j.val)
          (mul_nonneg hK (mul_nonneg (by norm_num) (div_nonneg (hy j.val).1 hY₀.le)))
      _ = _ := by ring
  change (∫⁻ r in Erow, f (r j).1 ∂normalizedStableScoreRowLaw d i) ≤ _
  rw [normalizedStableScoreRowLaw, setLIntegral_smul_measure, smul_eq_mul]
  refine (mul_le_mul_right hun _).trans ?_
  rw [← mul_assoc]
  simpa only [one_mul] using mul_le_mul_left (ENNReal.inv_mul_le_one (ν univ))
    (ENNReal.ofReal (8 * forwardSpouseWeight d j.val))

/-- An arc's extra male score above the spouse score. There is no diagonal arc. -/
def forwardRowScoreIncrement {n : ℕ} (d : DiagonalScorePairs n) (i j : Fin n)
    (r : {k : Fin n // i ≠ k} → ℝ × ℝ) : ℝ :=
  if h : i ≠ j then (r ⟨j, h⟩).1 - (diagonalPairAt d i).1 else 0

@[simp]
theorem forwardRowScoreIncrement_self {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {k : Fin n // i ≠ k} → ℝ × ℝ) :
    forwardRowScoreIncrement d i i r = 0 := by
  simp [forwardRowScoreIncrement]

theorem measurable_forwardRowScoreIncrement {n : ℕ} (d : DiagonalScorePairs n) (i j : Fin n) :
    Measurable (forwardRowScoreIncrement d i j) := by
  unfold forwardRowScoreIncrement
  by_cases h : i ≠ j
  · have hm : Measurable (fun r : {k : Fin n // i ≠ k} → ℝ × ℝ ↦ r ⟨j, h⟩) :=
      measurable_pi_apply _
    simpa only [dite_eq_left h] using hm.fst.sub_const (diagonalPairAt d i).1
  · simp only [dite_eq_right h]
    exact measurable_const

/-- In a marked score array, the off-diagonal increment is the difference
of the corresponding prospective and current spouse scores. -/
theorem forwardRowScoreIncrement_splitScorePairs {n : ℕ} (μ : Matching n)
    (x : ScoreProfile n) {i j : Fin n} (hij : i ≠ j) :
    forwardRowScoreIncrement (splitScorePairs μ x).1 i j
      (offDiagonalRowsEquiv n (splitScorePairs μ x).2 i) =
      x (.inl i) (μ j) - x (.inl i) (μ i) := by
  simp only [forwardRowScoreIncrement, dite_eq_left hij]
  change ((splitScorePairs μ x).2 ⟨(i, j), hij⟩).1 -
      (diagonalPairAt (splitScorePairs μ x).1 i).1 = _
  rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]

/-- The exponential-moment bound expressed using the finite successor outcome. -/
theorem lintegral_tiltedForwardArc_increment_le {n : ℕ}
    (d : DiagonalScorePairs n) (i j : Fin n) (hij : i ≠ j)
    (hx : (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2))
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc (0 : ℝ) 1)
    (hY : 4 ≤ pivotDiagonalFemaleTotal d) :
    (∫⁻ r, tiltedForwardArc (forwardSuccessorOutcome d)
      (fun i j r ↦ (pivotDiagonalFemaleTotal d / 4) * forwardRowScoreIncrement d i j r)
      i j r ∂normalizedStableScoreRowLaw d i) ≤
      ENNReal.ofReal (8 * forwardSpouseWeight d j) := by
  let a : {k : Fin n // i ≠ k} := ⟨j, hij⟩
  let f : ({k : Fin n // i ≠ k} → ℝ × ℝ) → ℝ≥0∞ := fun r ↦
    ENNReal.ofReal (Real.exp (((∑ k, (diagonalPairAt d k).2) / 4) *
      ((r a).1 - (diagonalPairAt d i).1)))
  have he :
      tiltedForwardArc (forwardSuccessorOutcome d)
          (fun i j r ↦ (pivotDiagonalFemaleTotal d / 4) * forwardRowScoreIncrement d i j r)
          i j =ᵐ[normalizedStableScoreRowLaw d i] (scoreRowSuccessorEvent d i a).indicator f := by
    filter_upwards [ae_injective_fst_normalizedStableScoreRowLaw d i] with r hr
    have hiff := forwardSuccessorOutcome_eq_some_iff d i r a hr
    by_cases h : r ∈ scoreRowSuccessorEvent d i a
    · have h' : forwardSuccessorOutcome d i r = some j := hiff.mpr h
      simp only [tiltedForwardArc, indicator_of_mem, mem_ofPred_eq, h', h,
        forwardRowScoreIncrement, dite_eq_left hij, f, a, pivotDiagonalFemaleTotal]
    · have h' : forwardSuccessorOutcome d i r ≠ some j := fun h' ↦ h (hiff.mp h')
      rw [tiltedForwardArc, indicator_of_notMem (show
        r ∉ {x | forwardSuccessorOutcome d i x = some j} from h'), indicator_of_notMem h]
  rw [lintegral_congr_ae he, lintegral_indicator (measurableSet_scoreRowSuccessorEvent _ _ _)]
  exact lintegral_forwardSuccessor_exp_le d i a hx hy hY

/-- One marked diagonal has a forward cycle of the given length with
total normalized male increment exceeding the specified threshold. -/
def forwardIncrementOverflowRowEvent {n : ℕ}
    (d : DiagonalScorePairs n) (k : ℕ) (t : ℝ) : Set (OffDiagonalScoreRows n) :=
  {r | ∃ σ : Matching n,
    RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ ∧
      σ.support.card = k ∧ t < pivotDiagonalFemaleTotal d *
        ∑ i ∈ σ.support, forwardRowScoreIncrement d i (σ i) (r i)}

/-- The finite-size bound is uniform over diagonals; the tilt weights sum to eight. -/
theorem measure_forwardIncrementOverflowRowEvent_le {n : ℕ} (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2))
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc (0 : ℝ) 1)
    (hY : 4 ≤ pivotDiagonalFemaleTotal d) (k : ℕ) (t : ℝ) :
    Measure.pi (normalizedStableScoreRowLaw d) (forwardIncrementOverflowRowEvent d k t) ≤
      ENNReal.ofReal (Real.exp (-(t / 4))) * (8 : ℝ≥0∞) ^ k := by
  let : MeasurableSpace (Option (Fin n)) := ⊤
  have : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  have (i : Fin n) := normalizedStableScoreRowLaw_isProbabilityMeasure d i
    ⟨(hx i).1, (hx i).2.trans_lt (by norm_num)⟩ hy
  let Y := pivotDiagonalFemaleTotal d
  let q (j : Fin n) := ENNReal.ofReal (8 * forwardSpouseWeight d j)
  let g (i j : Fin n) := fun r ↦ (Y / 4) * forwardRowScoreIncrement d i j r
  have hY₀ : 0 < Y := (by norm_num : (0 : ℝ) < 4).trans_le hY
  have hq₀ (j : Fin n) : 0 ≤ 8 * forwardSpouseWeight d j :=
    mul_nonneg (by norm_num) (div_nonneg (hy j).1 hY₀.le)
  have hq : (∑ j, q j) = 8 := by
    unfold q
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hq₀ j), ← Finset.mul_sum]
    have h : (∑ j, forwardSpouseWeight d j) = 1 := by
      unfold forwardSpouseWeight
      rw [← Finset.sum_div]
      exact div_self hY₀.ne'
    rw [h, mul_one]
    norm_num
  have he : forwardIncrementOverflowRowEvent d k t = {r | ∃ σ : Matching n,
      RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ ∧
      σ.support.card = k ∧ t / 4 < ∑ i ∈ σ.support, g i (σ i) (r i)} := by
    ext r
    unfold forwardIncrementOverflowRowEvent
    simp only [mem_ofPred_eq, g, ← Finset.mul_sum]
    refine exists_congr fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
    change t < Y * _ ↔ t / 4 < (Y / 4) * _
    rw [show ∀ z : ℝ, (Y / 4) * z = Y * z / 4 from fun z ↦ by ring]
    exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).symm
  rw [he, ← hq]
  exact measure_pi_exists_cycle_length_sum_gt_le (normalizedStableScoreRowLaw d)
    (forwardSuccessorOutcome d) g (measurable_forwardSuccessorOutcome d)
    (fun i j ↦ (measurable_forwardRowScoreIncrement d i j).const_mul _)
    q (by rw [hq]; norm_num) (by rw [hq]; norm_num)
    (fun i j hij ↦ lintegral_tiltedForwardArc_increment_le d i j hij (hx i) hy hY) k (t / 4)

/-- At lengths at most a fixed square-root scale, the increment cutoff
has smaller conditional probability than any inverse polynomial. -/
theorem eventually_measure_forwardIncrementOverflowRowEvent_le {A p : ℝ} :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n, d ∈ pivotBaseDiagonalBand n →
      (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d →
      ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt (n : ℝ) →
        Measure.pi (normalizedStableScoreRowLaw d)
          (forwardIncrementOverflowRowEvent d k ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ))) ≤
          ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  let hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog (a C : ℝ) (ha : 0 < a) :
      Tendsto (fun n : ℕ ↦ C * (Real.log n / (n : ℝ) ^ a)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp hcast)
  have h4 := Tendsto.eventually_ge_atTop
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hcast) 4
  filter_upwards [eventually_ge_atTop (1 : ℕ), h4,
    (hlog (1 / 10) 16 (by norm_num)).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    (hlog (1 / 2) p (by norm_num)).eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with n hn h4 hsmall hpow
  intro d hd hband k hk
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hY : 4 ≤ pivotDiagonalFemaleTotal d := h4.trans hband
  have hX (i : Fin n) : (diagonalPairAt d i).1 ∈ Icc (0 : ℝ) (1 / 2) := by
    refine ⟨(hd.1 i).1.1, (hd.2.2.2.2.2 i).trans ?_⟩
    calc
      _ ≤ 8 * Real.log n / ((n : ℝ) ^ (1 / 10 : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = 16 * (Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)) := by ring
      _ ≤ _ := hsmall.le
  have hy (i : Fin n) : (diagonalPairAt d i).2 ∈ Icc (0 : ℝ) 1 :=
    ⟨(hd.1 i).2.1, (hd.1 i).2.2.le⟩
  have hpow' : p * Real.log n ≤ Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hn₀ (1 / 2))).mp
      (show p * Real.log n / (n : ℝ) ^ (1 / 2 : ℝ) < 1 from
        by simpa only [mul_div_assoc] using hpow)
    simpa only [one_mul] using h.le
  have hexp : (8 : ℝ) ≤ Real.exp 8 := by
    linarith only [Real.add_one_le_exp (8 : ℝ)]
  refine (measure_forwardIncrementOverflowRowEvent_le d hX hy hY k _).trans ?_
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-((4 * (8 * A + 1) * Real.sqrt (n : ℝ)) / 4))) *
        (ENNReal.ofReal (Real.exp 8)) ^ k := by
      apply mul_le_mul_right
      apply pow_le_pow_left'
      exact (show (8 : ℝ≥0∞) = ENNReal.ofReal (8 : ℝ) by norm_num) ▸
        ENNReal.ofReal_le_ofReal hexp
    _ ≤ _ := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, Real.rpow_def_of_pos hn₀]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith only [hk, hpow']

end LennonPittelFormalization

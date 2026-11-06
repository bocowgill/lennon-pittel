module

public import LennonPittel.PivotAggregateMean
public import LennonPittel.PivotEnlargedConditionalMean
public import LennonPittel.PivotMovedCenteredTest
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Centering at fixed labeled marks

The local counts and means are computed with a fixed anchor. In a sum
under the original law the corresponding term is zero when that anchor
is not stable. This is the only change of measure used below.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Common choices for the filtered families in a finite market. -/
structure PivotCountParameters where
  lowerLength : ℝ
  upperLength : ℝ
  geometryBudget : ℝ
  supportCap : ℕ
  shortCutoff : ℕ

/-- A labeled anchor matching and a candidate forward pivot. -/
abbrev PivotMark (n : ℕ) := Matching n × Matching n

theorem integrable_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ᵐ x ∂ν, |f x| ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable <|
    hC.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx

theorem integrable_mul_of_ae_abs_le_real {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : 0 ≤ C) (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ D) :
    Integrable (f * g) ν := by
  apply integrable_of_ae_abs_le_real (hf.mul hg) (C := C * D)
  filter_upwards [hf', hg'] with x hx hy
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hC

namespace PivotCountParameters

variable {n : ℕ}

noncomputable def localCount (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2

noncomputable def localMean (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  localPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff i.1 i.2

noncomputable def localCentered (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  q.localCount i - q.localMean i

/-- Extend a statistic at the marked stable matching by zero off its stability event. -/
noncomputable def onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    ScoreProfile n → ℝ :=
  {x | IsScoreStable x i.1}.indicator f

noncomputable def count (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCount i)

noncomputable def mean (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localMean i)

noncomputable def centered (q : PivotCountParameters) (i : PivotMark n) :
    ScoreProfile n → ℝ :=
  onStableMark i (q.localCentered i)

theorem measurable_localCount (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localCount i) :=
  measurable_localFilteredDecorationCount _ _ _ _ _ _ _

theorem stronglyMeasurable_maleReveal_localMean (q : PivotCountParameters) (i : PivotMark n) :
    StronglyMeasurable[pivotMaleRevealSpace i.1] (q.localMean i) :=
  stronglyMeasurable_condExp

theorem measurable_localMean (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localMean i) :=
  ((q.stronglyMeasurable_maleReveal_localMean i).mono (pivotMaleRevealSpace_le i.1)).measurable

theorem measurable_localCentered (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.localCentered i) := (q.measurable_localCount i).sub (q.measurable_localMean i)

theorem measurable_onStableMark (i : PivotMark n) {f : ScoreProfile n → ℝ} (hf : Measurable f) :
    Measurable (onStableMark i f) := hf.indicator (measurableSet_isScoreStable i.1)

theorem measurable_count (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.count i) :=
  measurable_onStableMark i (q.measurable_localCount i)

theorem measurable_mean (q : PivotCountParameters) (i : PivotMark n) : Measurable (q.mean i) :=
  measurable_onStableMark i (q.measurable_localMean i)

theorem measurable_centered (q : PivotCountParameters) (i : PivotMark n) :
    Measurable (q.centered i) := measurable_onStableMark i (q.measurable_localCentered i)

theorem localCount_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.localCount i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  ⟨localFilteredDecorationCount_nonneg _ _ _ _ _ _ _ _,
    localFilteredDecorationCount_le_factorial _ _ _ _ _ _ _ _⟩

theorem localMean_mem_Icc_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1, q.localMean i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) :=
  localPivotConditionalMean_mem_Icc_ae _ _ _ _ _ _ _

/-- A pivot that fails the measurable local eligibility test has zero conditional mean. -/
theorem localMean_zero_on_ineligible_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.localMean i x = 0 := by
  let E : Set (ScoreProfile n) :=
    {x | IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2}
  have hE : MeasurableSet[pivotMaleRevealSpace i.1] E :=
    measurableSet_isLocallyEligiblePivot_maleRevealSpace _ _ _ _ _
  have hE' : MeasurableSet E := pivotMaleRevealSpace_le i.1 _ hE
  have hz : q.localCount i =ᵐ[(stableMarkScoreLaw i.1).restrict Eᶜ] 0 := by
    filter_upwards [ae_restrict_mem hE'.compl] with x hx
    exact localFilteredDecorationCount_of_not_eligible _ _ hx
  exact (ae_restrict_iff' hE'.compl).mp (condExp_ae_eq_restrict_zero hE.compl hz)

theorem ae_scoreLaw_on_stableMark (i : PivotMark n) {P : ScoreProfile n → Prop}
    (h : ∀ᵐ x ∂stableMarkScoreLaw i.1, P x) :
    ∀ᵐ x ∂continuousScoreLaw n, IsScoreStable x i.1 → P x :=
  (ae_restrict_iff' (measurableSet_isScoreStable i.1)).mp h

theorem count_mem_Icc (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.count i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [count, onStableMark, indicator_of_mem h] using q.localCount_mem_Icc i x
  · simp [count, onStableMark, h]

theorem mean_mem_Icc_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n, q.mean i x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  filter_upwards [ae_scoreLaw_on_stableMark i (q.localMean_mem_Icc_ae i)] with x hx
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simpa only [mean, onStableMark, indicator_of_mem h] using hx h
  · simp [mean, onStableMark, h]

theorem centered_eq_sub (q : PivotCountParameters) (i : PivotMark n) (x : ScoreProfile n) :
    q.centered i x = q.count i x - q.mean i x := by
  by_cases h : x ∈ {y | IsScoreStable y i.1}
  · simp only [centered, count, mean, onStableMark, indicator_of_mem h, localCentered, Pi.sub_apply]
  · simp only [centered, count, mean, onStableMark, indicator_of_notMem h, sub_zero]

theorem abs_centered_le_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n, |q.centered i x| ≤ (n.factorial : ℝ) := by
  filter_upwards [q.mean_mem_Icc_ae i] with x hx
  have hz := q.count_mem_Icc i x
  rw [q.centered_eq_sub]
  exact abs_le.mpr ⟨by linarith [hz.1, hx.2], by linarith [hz.2, hx.1]⟩

theorem integral_onStableMark (i : PivotMark n) (f : ScoreProfile n → ℝ) :
    (∫ x, onStableMark i f x ∂continuousScoreLaw n) = ∫ x, f x ∂stableMarkScoreLaw i.1 :=
  integral_indicator (measurableSet_isScoreStable i.1)

theorem integral_sq_centered_le_localCount_sq (q : PivotCountParameters) (i : PivotMark n) :
    (∫ x, (q.centered i x) ^ 2 ∂continuousScoreLaw n) ≤
      ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1 := by
  have he : (fun x ↦ (q.centered i x) ^ 2) =
      onStableMark i (fun x ↦ (q.localCentered i x) ^ 2) := by
    funext x
    by_cases hx : x ∈ {y | IsScoreStable y i.1}
    · simp only [centered, onStableMark, indicator_of_mem hx]
    · simp [centered, onStableMark, hx]
  rw [he, integral_onStableMark]
  let ν := stableMarkScoreLaw i.1
  let Z := q.localCount i
  let M := q.localMean i
  let C := (n.factorial : ℝ)
  have hZ (x : ScoreProfile n) : |Z x| ≤ C := by
    rw [abs_of_nonneg (q.localCount_mem_Icc i x).1]
    exact (q.localCount_mem_Icc i x).2
  have hM : ∀ᵐ x ∂ν, |M x| ≤ C := (q.localMean_mem_Icc_ae i).mono fun x hx ↦
    (abs_of_nonneg hx.1).symm ▸ hx.2
  have hi {f g : ScoreProfile n → ℝ} (hf : Measurable f) (hg : Measurable g)
      (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ C) :
      Integrable (f * g) ν :=
    integrable_mul_of_ae_abs_le_real hf hg (by positivity) hf' hg'
  have hZZ := hi (q.measurable_localCount i) (q.measurable_localCount i)
    (Eventually.of_forall hZ) (Eventually.of_forall hZ)
  have hZM := hi (q.measurable_localCount i) (q.measurable_localMean i) (Eventually.of_forall hZ) hM
  have hMM := hi (q.measurable_localMean i) (q.measurable_localMean i) hM hM
  have hzero := integral_localPivotCentered_mul_eq_zero q.lowerLength q.upperLength
    q.geometryBudget q.supportCap q.shortCutoff i.1 i.2 M
    (((q.stronglyMeasurable_maleReveal_localMean i).mono
      (pivotMaleRevealSpace_le_full i.1)).aestronglyMeasurable) hZM hMM
  change (∫ x, (Z x - M x) * M x ∂ν) = 0 at hzero
  have hZM_eq : (∫ x, (Z * M) x ∂ν) = ∫ x, (M * M) x ∂ν := by
    apply sub_eq_zero.mp
    calc
      _ = ∫ x, (Z * M) x - (M * M) x ∂ν := (integral_sub hZM hMM).symm
      _ = _ := by simpa only [sub_mul, Pi.mul_apply] using hzero
  change (∫ x, (Z x - M x) ^ 2 ∂ν) ≤ _
  have hre : (fun x ↦ (Z x - M x) ^ 2) = fun x ↦
      ((Z * Z) x - 2 * (Z * M) x) + (M * M) x := by
    funext x
    simp only [Pi.mul_apply]
    ring
  have hsplit : (∫ x, ((Z * Z) x - 2 * (Z * M) x) + (M * M) x ∂ν) =
      (∫ x, (Z * Z) x ∂ν) - (∫ x, 2 * (Z * M) x ∂ν) + ∫ x, (M * M) x ∂ν := by
    calc
      _ = (∫ x, (Z * Z) x - 2 * (Z * M) x ∂ν) + ∫ x, (M * M) x ∂ν :=
        integral_add (hZZ.sub (hZM.const_mul 2)) hMM
      _ = _ := congrArg (· + ∫ x, (M * M) x ∂ν) (integral_sub hZZ (hZM.const_mul 2))
  rw [hre, hsplit, integral_const_mul, hZM_eq]
  have hnn : 0 ≤ ∫ x, (M * M) x ∂ν := integral_nonneg fun x ↦ mul_self_nonneg (M x)
  simp_rw [pow_two]
  change (∫ x, (Z * Z) x ∂ν) - 2 * (∫ x, (M * M) x ∂ν) + (∫ x, (M * M) x ∂ν) ≤
    ∫ x, (Z * Z) x ∂ν
  linarith

private noncomputable def localLaterCentered (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.localCentered j x else 0

/-- The part of the later count that uses at least one unchanged woman. -/
noncomputable def localLaterResidual (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.localCount j x -
    localMovedDecorationCount q.lowerLength q.upperLength q.geometryBudget q.supportCap
      q.shortCutoff i.1 j.1 j.2 x else 0

theorem localLaterResidual_mem_Icc (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : q.localLaterResidual i j x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  classical
  unfold localLaterResidual
  split
  · exact ⟨sub_nonneg.mpr (localMovedDecorationCount_le _ _ _ _ _ _ _ _ _),
      (sub_le_self _ (localMovedDecorationCount_nonneg _ _ _ _ _ _ _ _ _)).trans
        (q.localCount_mem_Icc j x).2⟩
  · simp

theorem measurable_localLaterResidual (q : PivotCountParameters) (i j : PivotMark n) :
    Measurable (q.localLaterResidual i j) :=
  ((q.measurable_localCount j).sub (measurable_localMovedDecorationCount _ _ _ _ _ _ _ _)).ite
    (measurableSet_isStrictLaterStable i.1 j.1) measurable_const

private theorem abs_localCentered_le_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂stableMarkScoreLaw i.1, |q.localCentered i x| ≤ (n.factorial : ℝ) := by
  filter_upwards [q.localMean_mem_Icc_ae i] with x hx
  have hz := q.localCount_mem_Icc i x
  change |q.localCount i x - q.localMean i x| ≤ _
  exact abs_le.mpr ⟨by linarith [hz.1, hx.2], by linarith [hz.2, hx.1]⟩

/-- The ordered comparable summand under the original score law. -/
noncomputable def comparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ := by
  classical
  exact if IsStrictLaterStable x i.1 j.1 then q.centered i x * q.centered j x else 0

/-- The nonnegative residual comparable summand under the original score law. -/
noncomputable def comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n)
    (x : ScoreProfile n) : ℝ :=
  q.count i x * q.localLaterResidual i j x

theorem measurable_comparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Measurable (q.comparableCenteredTerm i j) :=
  ((q.measurable_centered i).mul (q.measurable_centered j)).ite
    (measurableSet_isStrictLaterStable i.1 j.1) measurable_const

theorem measurable_comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Measurable (q.comparableResidualTerm i j) :=
  (q.measurable_count i).mul (q.measurable_localLaterResidual i j)

theorem integrable_comparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.comparableCenteredTerm i j) (continuousScoreLaw n) := by
  classical
  refine integrable_of_ae_abs_le_real (q.measurable_comparableCenteredTerm i j)
    (C := (n.factorial : ℝ) * (n.factorial : ℝ)) ?_
  filter_upwards [q.abs_centered_le_ae i, q.abs_centered_le_ae j] with x hi hj
  by_cases h : IsStrictLaterStable x i.1 j.1
  · rw [comparableCenteredTerm, ite_eq_left h, abs_mul]
    exact mul_le_mul hi hj (abs_nonneg _) (by positivity)
  · rw [comparableCenteredTerm, ite_eq_right h, abs_zero]
    positivity

theorem integrable_comparableResidualTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.comparableResidualTerm i j) (continuousScoreLaw n) :=
  integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_localLaterResidual i j)
    (by positivity) (Eventually.of_forall fun x ↦
      (abs_of_nonneg (q.count_mem_Icc i x).1).symm ▸ (q.count_mem_Icc i x).2)
    (Eventually.of_forall fun x ↦
      (abs_of_nonneg (q.localLaterResidual_mem_Icc i j x).1).symm ▸
        (q.localLaterResidual_mem_Icc i j x).2)

private theorem integral_local_comparable_le_residual (q : PivotCountParameters) (i j : PivotMark n) :
    (∫ x, q.localCentered i x * q.localLaterCentered i j x ∂stableMarkScoreLaw i.1) ≤
      ∫ x, q.localCount i x * q.localLaterResidual i j x ∂stableMarkScoreLaw i.1 := by
  classical
  let ν := stableMarkScoreLaw i.1
  let Z := q.localCount i
  let M := q.localMean i
  let W := q.localCentered i
  let R := q.localLaterResidual i j
  let T := laterMovedCenteredTest q.lowerLength q.upperLength q.geometryBudget q.supportCap
    q.shortCutoff i.1 j.1 j.2
  let C := (n.factorial : ℝ)
  have hTm : Measurable[pivotFullRevealSpace i.1] T :=
    measurable_laterMovedCenteredTest _ _ _ _ _ _ _ _
  have hT : Measurable T := hTm.mono (pivotFullRevealSpace_le i.1) le_rfl
  have hTb : ∀ᵐ x ∂ν, |T x| ≤ C := laterMovedCenteredTest_abs_le_factorial_ae _ _ _ _ _ _ _ _
  have hZ : ∀ᵐ x ∂ν, |Z x| ≤ C := Eventually.of_forall fun x ↦
    (abs_of_nonneg (q.localCount_mem_Icc i x).1).symm ▸ (q.localCount_mem_Icc i x).2
  have hM : ∀ᵐ x ∂ν, |M x| ≤ C := (q.localMean_mem_Icc_ae i).mono fun x hx ↦
    (abs_of_nonneg hx.1).symm ▸ hx.2
  have hW : ∀ᵐ x ∂ν, |W x| ≤ C := q.abs_localCentered_le_ae i
  have hR : ∀ᵐ x ∂ν, |R x| ≤ C := Eventually.of_forall fun x ↦
    (abs_of_nonneg (q.localLaterResidual_mem_Icc i j x).1).symm ▸
      (q.localLaterResidual_mem_Icc i j x).2
  have hi {f g : ScoreProfile n → ℝ} (hf : Measurable f) (hg : Measurable g)
      (hf' : ∀ᵐ x ∂ν, |f x| ≤ C) (hg' : ∀ᵐ x ∂ν, |g x| ≤ C) : Integrable (f * g) ν :=
    integrable_mul_of_ae_abs_le_real hf hg (by positivity) hf' hg'
  have hWR : Integrable (W * R) ν := hi (q.measurable_localCentered i)
    (q.measurable_localLaterResidual i j) hW hR
  have hZR : Integrable (Z * R) ν := hi (q.measurable_localCount i)
    (q.measurable_localLaterResidual i j) hZ hR
  have hWT : Integrable (W * T) ν := hi (q.measurable_localCentered i) hT hW hTb
  have hzero : (∫ x, W x * T x ∂ν) = 0 :=
    integral_localPivotCentered_mul_eq_zero q.lowerLength q.upperLength q.geometryBudget
      q.supportCap q.shortCutoff i.1 i.2 T hTm.stronglyMeasurable.aestronglyMeasurable
      (hi (q.measurable_localCount i) hT hZ hTb) (hi (q.measurable_localMean i) hT hM hTb)
  have hs : (fun x ↦ W x * q.localLaterCentered i j x) =ᵐ[ν]
      fun x ↦ W x * T x + W x * R x := by
    filter_upwards [laterMovedCenteredTest_ae_eq q.lowerLength q.upperLength q.geometryBudget
      q.supportCap q.shortCutoff i.1 j.1 j.2] with x hx
    change T x = _ at hx
    rw [hx]
    by_cases h : IsStrictLaterStable x i.1 j.1
    · simp only [localLaterCentered, R, localLaterResidual, ite_eq_left h, localCentered,
        localCount, localMean, Pi.sub_apply]
      ring
    · simp [localLaterCentered, R, localLaterResidual, h]
  change (∫ x, W x * q.localLaterCentered i j x ∂ν) ≤ ∫ x, Z x * R x ∂ν
  calc
    _ = (∫ x, W x * T x ∂ν) + ∫ x, W x * R x ∂ν :=
      (integral_congr_ae hs).trans (integral_add hWT hWR)
    _ = _ := by rw [hzero, zero_add]
    _ ≤ _ := by
      apply integral_mono_ae hWR hZR
      filter_upwards [q.localMean_mem_Icc_ae i] with x hx
      have hw : W x ≤ Z x := sub_le_self _ hx.1
      exact mul_le_mul_of_nonneg_right hw (q.localLaterResidual_mem_Icc i j x).1

/-- In expectation the ordered comparable centered term is bounded by
the product of the early count and the residual later count. -/
theorem integral_comparableCenteredTerm_le_residual (q : PivotCountParameters) (i j : PivotMark n) :
    (∫ x, q.comparableCenteredTerm i j x ∂continuousScoreLaw n) ≤
      ∫ x, q.comparableResidualTerm i j x ∂continuousScoreLaw n := by
  classical
  have hC : q.comparableCenteredTerm i j =
      onStableMark i (fun x ↦ q.localCentered i x * q.localLaterCentered i j x) := by
    funext x
    by_cases h : IsStrictLaterStable x i.1 j.1
    · have hj : x ∈ {y | IsScoreStable y j.1} := h.1
      by_cases hi : x ∈ {y | IsScoreStable y i.1} <;>
        simp [comparableCenteredTerm, localLaterCentered, centered, onStableMark, hi, hj, h]
    · by_cases hi : x ∈ {y | IsScoreStable y i.1} <;>
        simp [comparableCenteredTerm, localLaterCentered, onStableMark, hi, h]
  have hR : q.comparableResidualTerm i j =
      onStableMark i (fun x ↦ q.localCount i x * q.localLaterResidual i j x) := by
    funext x
    by_cases h : x ∈ {y | IsScoreStable y i.1} <;>
      simp [comparableResidualTerm, count, onStableMark, h]
  rw [hC, hR, integral_onStableMark, integral_onStableMark]
  exact q.integral_local_comparable_le_residual i j

end PivotCountParameters

end LennonPittelFormalization

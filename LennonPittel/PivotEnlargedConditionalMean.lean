module

public import LennonPittel.PivotConditionalMean
public import LennonPittel.PivotDecorationRevealInvariance
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The two forward reveals give the same marked mean

The active female scores are independent of the inactive columns on each
fixed mask and diagonal. The count can be evaluated after filling those
active female scores with arbitrary canonical values. Its inactive-column
average therefore satisfies the conditional-expectation tests for both reveals.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The nonnegative count evaluated on the canonical section of the smaller reveal. -/
noncomputable def localPivotInactiveStatistic (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (s : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    ℝ≥0∞ :=
  ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ (reverseRevealFill μ s.1 flag s.2))

theorem measurable_localPivotInactiveStatistic (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (localPivotInactiveStatistic b A B K L μ ρ flag) :=
  ENNReal.measurable_ofReal.comp ((measurable_localFilteredDecorationCount b A B K L μ ρ).comp
    (measurable_reverseRevealFill μ flag))

private theorem localPivotInactiveStatistic_le (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool)
    (s : DiagonalScorePairs n × ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    localPivotInactiveStatistic b A B K L μ ρ flag s ≤ ENNReal.ofReal (n.factorial : ℝ) :=
  ENNReal.ofReal_le_ofReal (localFilteredDecorationCount_le_factorial b A B K L μ ρ _)

/-- The explicit conditional mean obtained by averaging only the inactive columns. -/
noncomputable def localPivotInactiveMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  (pivotInactiveMeanFromReveal (localPivotInactiveStatistic b A B K L μ ρ)
    (pivotMaleReveal μ x)).toReal

theorem measurable_maleReveal_localPivotInactiveMean (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) :
    Measurable[pivotMaleRevealSpace μ] (localPivotInactiveMean b A B K L μ ρ) := by
  have hmap : Measurable[pivotMaleRevealSpace μ] (pivotMaleReveal μ) :=
    fun S hS ↦ ⟨S, hS, rfl⟩
  exact ENNReal.measurable_toReal.comp
    ((measurable_pivotInactiveMeanFromReveal
      (measurable_localPivotInactiveStatistic b A B K L μ ρ)).comp hmap)

private theorem ae_localPivotInactiveMeanENN_le (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ, pivotInactiveMeanFromReveal
      (localPivotInactiveStatistic b A B K L μ ρ) (pivotMaleReveal μ x) ≤
        ENNReal.ofReal (n.factorial : ℝ) :=
  ae_pivotInactiveMeanFromReveal_le_stableMarkScoreLaw μ
    (localPivotInactiveStatistic_le b A B K L μ ρ)

theorem integrable_localPivotInactiveMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    Integrable (localPivotInactiveMean b A B K L μ ρ) (stableMarkScoreLaw μ) := by
  refine (integrable_const (n.factorial : ℝ)).mono'
    (((measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).mono
      (pivotMaleRevealSpace_le μ) le_rfl).aestronglyMeasurable) ?_
  filter_upwards [ae_localPivotInactiveMeanENN_le b A B K L μ ρ] with x hx
  have hnonneg : 0 ≤ localPivotInactiveMean b A B K L μ ρ x := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal (Nat.cast_nonneg _))

/-- The same inactive-column average tests against every enlarged-reveal event. -/
theorem setIntegral_localPivotInactiveMean_eq {b A B : ℝ} (K L : ℕ) (μ ρ : Matching n)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotFullRevealSpace μ] S) :
    (∫ x in S, localPivotInactiveMean b A B K L μ ρ x ∂stableMarkScoreLaw μ) =
      ∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ∂stableMarkScoreLaw μ := by
  let F := localPivotInactiveStatistic b A B K L μ ρ
  let Z := localFilteredDecorationCount b A B K L μ ρ
  let ν := stableMarkScoreLaw μ
  let m := localPivotInactiveMean b A B K L μ ρ
  have hfactor : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      ∀ᵐ z ∂forwardMaskRevealLaw d flag univ,
        ENNReal.ofReal (Z ((splitScorePairs μ).symm (d, z))) =
          F flag (d, (forwardRevealWithColumns flag z).1, (forwardRevealWithColumns flag z).2) := by
    filter_upwards [ae_diagonal_ae_localFilteredDecorationCount_eq_reverseRevealFill b A B K L μ ρ]
      with d hd flag
    exact (hd flag univ).mono fun z hz ↦ congrArg ENNReal.ofReal hz
  have he := setLIntegral_stableMark_fullReveal_eq_inactiveMean μ
    (measurable_localPivotInactiveStatistic b A B K L μ ρ)
    (ENNReal.measurable_ofReal.comp (measurable_localFilteredDecorationCount b A B K L μ ρ))
    (ae_diagonalFemale_mem_Ico n) hfactor hS
  have hraw : (fun x ↦ ENNReal.ofReal (m x)) =ᵐ[ν.restrict S]
      fun x ↦ pivotInactiveMeanFromReveal F (pivotMaleReveal μ x) := by
    filter_upwards [ae_restrict_of_ae (ae_localPivotInactiveMeanENN_le b A B K L μ ρ)] with x hx
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx)
  have hnm : 0 ≤ᵐ[ν.restrict S] m := Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
  have hnZ : 0 ≤ᵐ[ν.restrict S] Z :=
    Eventually.of_forall (localFilteredDecorationCount_nonneg b A B K L μ ρ)
  change (∫ x in S, m x ∂ν) = ∫ x in S, Z x ∂ν
  rw [integral_eq_lintegral_of_nonneg_ae hnm
      ((integrable_localPivotInactiveMean b A B K L μ ρ).integrableOn (s := S)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnZ
      ((integrable_localFilteredDecorationCount b A B K L μ ρ ν).integrableOn (s := S)).aestronglyMeasurable,
    lintegral_congr_ae hraw]
  exact congrArg ENNReal.toReal he.symm

/-- The explicit inactive-column average is a version of the smaller-reveal mean. -/
theorem localPivotInactiveMean_ae_eq_conditionalMean (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) :
    localPivotInactiveMean b A B K L μ ρ =ᵐ[stableMarkScoreLaw μ]
      localPivotConditionalMean b A B K L μ ρ := by
  let ν := stableMarkScoreLaw μ
  have hf := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg := integrable_localPivotInactiveMean b A B K L μ ρ
  have hm := (measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).stronglyMeasurable
  exact ae_eq_condExp_of_forall_setIntegral_eq (pivotMaleRevealSpace_le μ) hf
    (fun _ _ _ ↦ hg.integrableOn) (fun _ hS _ ↦
      setIntegral_localPivotInactiveMean_eq K L μ ρ (pivotMaleRevealSpace_le_full μ _ hS))
    hm.aestronglyMeasurable

/-- Exposing the active women's scores does not change the marked conditional mean. -/
theorem localPivotConditionalMean_ae_eq_fullReveal (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    localPivotConditionalMean b A B K L μ ρ =ᵐ[stableMarkScoreLaw μ]
      (stableMarkScoreLaw μ)[localFilteredDecorationCount b A B K L μ ρ|pivotFullRevealSpace μ] := by
  let ν := stableMarkScoreLaw μ
  have hf := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg := integrable_localPivotInactiveMean b A B K L μ ρ
  have hm := (measurable_maleReveal_localPivotInactiveMean b A B K L μ ρ).stronglyMeasurable
  have hG := ae_eq_condExp_of_forall_setIntegral_eq (pivotFullRevealSpace_le μ) hf
    (fun _ _ _ ↦ hg.integrableOn) (fun _ hS _ ↦ setIntegral_localPivotInactiveMean_eq K L μ ρ hS)
    (hm.mono (pivotMaleRevealSpace_le_full μ)).aestronglyMeasurable
  exact (localPivotInactiveMean_ae_eq_conditionalMean b A B K L μ ρ).symm.trans hG

theorem localPivotConditionalMean_mem_Icc_ae (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ x ∂stableMarkScoreLaw μ,
      localPivotConditionalMean b A B K L μ ρ x ∈ Icc (0 : ℝ) (n.factorial : ℝ) := by
  filter_upwards [localPivotInactiveMean_ae_eq_conditionalMean b A B K L μ ρ,
    ae_localPivotInactiveMeanENN_le b A B K L μ ρ] with x h hx
  rw [← h]
  exact ⟨ENNReal.toReal_nonneg, (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
    (ENNReal.toReal_ofReal (Nat.cast_nonneg _))⟩

/-- The centered local count integrates to zero against any integrable
product test measurable for the enlarged reveal. -/
theorem integral_localPivotCentered_mul_eq_zero (b A B : ℝ) (K L : ℕ)
    (μ ρ : Matching n) (g : ScoreProfile n → ℝ)
    (hg : AEStronglyMeasurable[pivotFullRevealSpace μ] g (stableMarkScoreLaw μ))
    (hZg : Integrable (localFilteredDecorationCount b A B K L μ ρ * g) (stableMarkScoreLaw μ))
    (hMg : Integrable (localPivotConditionalMean b A B K L μ ρ * g) (stableMarkScoreLaw μ)) :
    (∫ x, (localFilteredDecorationCount b A B K L μ ρ x -
      localPivotConditionalMean b A B K L μ ρ x) * g x ∂stableMarkScoreLaw μ) = 0 := by
  let ν := stableMarkScoreLaw μ
  let Z := localFilteredDecorationCount b A B K L μ ρ
  let M := localPivotConditionalMean b A B K L μ ρ
  let m := pivotFullRevealSpace μ
  have hpull : ν[Z * g|m] =ᵐ[ν] M * g :=
    (condExp_mul_of_aestronglyMeasurable_right hg hZg
      (integrable_localFilteredDecorationCount b A B K L μ ρ ν)).trans
      ((localPivotConditionalMean_ae_eq_fullReveal b A B K L μ ρ).symm.mono
        fun x hx ↦ congrArg (fun t : ℝ ↦ t * g x) hx)
  have heq : (∫ x, (Z * g) x ∂ν) = ∫ x, (M * g) x ∂ν :=
    (integral_condExp (pivotFullRevealSpace_le μ)).symm.trans (integral_congr_ae hpull)
  change (∫ x, (Z x - M x) * g x ∂ν) = 0
  simp_rw [sub_mul]
  exact (integral_sub hZg hMg).trans (sub_eq_zero.mpr heq)

end LennonPittelFormalization

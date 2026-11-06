module

public import LennonPittel.PivotRestrictedMoment
public import LennonPittel.PivotMarkedDecorationCount
public import LennonPittel.PivotFullRevealLaw

/-!
# A conditional lower bound at a marked stable matching

The lower bound is tested on every measurable smaller-reveal event. The
stable mark is fixed before conditioning, so its score law is the restriction
to its own stability event, without a random anchor-selection bias.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The real-valued lower bound, zero at an ineligible mark. -/
noncomputable def localPivotMeanFloor (b A B : ℝ) (K : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  {x | IsLocallyEligiblePivot b A B x μ ρ}.indicator
    (fun _ ↦ (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ)) x

theorem measurable_maleReveal_localPivotMeanFloor (b A B : ℝ) (K : ℕ) (μ ρ : Matching n) :
    Measurable[pivotMaleRevealSpace μ] (localPivotMeanFloor b A B K μ ρ) :=
  measurable_const.indicator (measurableSet_isLocallyEligiblePivot_maleRevealSpace b A B μ ρ)

theorem localPivotMeanFloor_nonneg (b A B : ℝ) (K : ℕ) (μ ρ : Matching n)
    (x : ScoreProfile n) : 0 ≤ localPivotMeanFloor b A B K μ ρ x :=
  Set.indicator_nonneg (fun _ _ ↦ by positivity) _

theorem integrable_localPivotMeanFloor (b A B : ℝ) (K : ℕ) (μ ρ : Matching n) :
    Integrable (localPivotMeanFloor b A B K μ ρ) (stableMarkScoreLaw μ) :=
  (integrable_const _).indicator (measurableSet_isLocallyEligiblePivot b A B μ ρ)

private theorem lintegral_fixedMask_meanFloor_le {b A B : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    {W : Set (PivotMaleRevealData n)} (hW : MeasurableSet W)
    (hcert : LocalPivotGeometry b A B μ ρ d flag →
      EligibleReverseMomentCertificate μ ρ d flag K L (localPivotIncrementCap B d)
        (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
        (B / Real.sqrt (n : ℝ))) :
    let R (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
    let S := pivotMaleReveal μ ⁻¹' W
    let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag)
    (∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal (localPivotMeanFloor b A B K μ ρ x)) (R z) ∂ν)
      ≤ ∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
        (localFilteredDecorationCount b A B K L μ ρ x)) (R z) ∂ν := by
  classical
  dsimp only
  let R (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
  let S := pivotMaleReveal μ ⁻¹' W
  let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)
  let c : ℝ := (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ)
  let U₀ := eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d)
  let U := U₀ ∩ (fun v ↦ pivotMaleRevealSection flag (d, v)) ⁻¹' W
  let V := (fun z ↦ (forwardRevealWithColumns flag z).1) ⁻¹' U
  let N (z : OffDiagonalScorePairs n) : ℝ≥0∞ := (markedFilteredChoices μ ρ flag K L
    (reverseIncrementCutoff n (reverseDiagonalMaleTotal d)) (R z)).card
  have hmask : ∀ᵐ z ∂ν, z ∈ forwardScoreMaskEvent d flag :=
    ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)
  change (∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal (localPivotMeanFloor b A B K μ ρ x)) (R z) ∂ν)
    ≤ ∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
      (localFilteredDecorationCount b A B K L μ ρ x)) (R z) ∂ν
  by_cases hgeo : LocalPivotGeometry b A B μ ρ d flag
  · have hU : MeasurableSet U := (measurableSet_eligiblePivotRevealSet d flag ρ _).inter
      (hW.preimage ((measurable_pivotMaleRevealSection flag).comp
        (measurable_const.prodMk measurable_id)))
    have hV : MeasurableSet V := hU.preimage (measurable_forwardRevealWithColumns flag).fst
    have hL : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localPivotMeanFloor b A B K μ ρ x)) (R z)) =ᵐ[ν]
        V.indicator (fun _ ↦ ENNReal.ofReal c) := by
      filter_upwards [hmask] with z hz
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hR := pivotMaleReveal_reconstruct μ d z flag hz
      by_cases h₁ : R z ∈ S <;> by_cases h₂ : IsLocallyEligiblePivot b A B (R z) μ ρ
      all_goals
        have h₁' : R z ∈ S ↔ pivotMaleRevealSection flag
            (d, (forwardRevealWithColumns flag z).1) ∈ W := by
          change pivotMaleReveal μ (R z) ∈ W ↔ _
          rw [show pivotMaleReveal μ (R z) = _ from hR]
        have h₂' : IsLocallyEligiblePivot b A B (R z) μ ρ ↔
            (forwardRevealWithColumns flag z).1 ∈ U₀ := (hE.trans (and_iff_right hgeo))
        have hV' : z ∈ V ↔ R z ∈ S ∧ IsLocallyEligiblePivot b A B (R z) μ ρ := by
          change ((forwardRevealWithColumns flag z).1 ∈ U₀ ∧
            pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) ∈ W) ↔ _
          rw [← h₁', ← h₂', and_comm]
        simp [localPivotMeanFloor, indicator_apply, hV', h₁, h₂, c]
    have hN : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localFilteredDecorationCount b A B K L μ ρ x)) (R z)) =ᵐ[ν] V.indicator N := by
      filter_upwards [hmask] with z hz
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hR := pivotMaleReveal_reconstruct μ d z flag hz
      have hV' : z ∈ V ↔ R z ∈ S ∧ IsLocallyEligiblePivot b A B (R z) μ ρ := by
        change ((forwardRevealWithColumns flag z).1 ∈ U₀ ∧
          pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) ∈ W) ↔ _
        change _ ↔ pivotMaleReveal μ (R z) ∈ W ∧ _
        rw [show pivotMaleReveal μ (R z) = _ from hR, hE, and_iff_right hgeo, and_comm]
      by_cases h₁ : R z ∈ S
      · by_cases h₂ : IsLocallyEligiblePivot b A B (R z) μ ρ
        · have hs : splitScorePairs μ (R z) = (d, z) := (splitScorePairs μ).apply_symm_apply _
          have hz' : (splitScorePairs μ (R z)).2 ∈
              forwardScoreMaskEvent (splitScorePairs μ (R z)).1 flag := by rw [hs]; exact hz
          rw [indicator_of_mem h₁, indicator_of_mem (hV'.mpr ⟨h₁, h₂⟩),
            localFilteredDecorationCount_of_eligible_of_fixedMask K L h₂ hz', hs]
          simp [N]
        · simp [localFilteredDecorationCount, hV', h₁, h₂]
      · simp [hV', h₁]
    rw [lintegral_congr_ae hL, lintegral_congr_ae hN, lintegral_indicator hV,
      lintegral_indicator hV, lintegral_const]
    change ENNReal.ofReal c * (forwardMaskRevealLaw d flag U) univ ≤
      ∫⁻ z, N z ∂forwardMaskRevealLaw d flag U
    have hc : ENNReal.ofReal c = ENNReal.ofReal (3 / 64) * ((K - 1 : ℕ) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
    rw [hc]
    calc
      _ = (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 64) *
          ((K - 1 : ℕ) : ℝ≥0∞) := by ac_rfl
      _ ≤ _ := ((hcert hgeo).filteredFamilyMoment_of_subset hU inter_subset_left).trans ?_
    apply lintegral_mono
    intro z
    change (∑ k ∈ Finset.Icc 2 K, ((filteredReverseSupportFamily μ ρ flag k L
      (reverseIncrementCutoff n (reverseDiagonalMaleTotal d)) (R z)).card : ℝ≥0∞)) ≤ N z
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (sum_card_filteredReverseSupportFamily_le_card_markedFilteredChoices
      μ ρ flag K L (reverseIncrementCutoff n (reverseDiagonalMaleTotal d)) (R z))
  · have hz : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localPivotMeanFloor b A B K μ ρ x)) (R z)) =ᵐ[ν] (fun _ ↦ 0) := by
      filter_upwards [hmask] with z hz
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hnot : ¬ IsLocallyEligiblePivot b A B (R z) μ ρ := fun h ↦ hgeo (hE.mp h).1
      simp [localPivotMeanFloor, indicator_apply, hnot]
    rw [lintegral_congr_ae hz, lintegral_zero]
    exact zero_le

/-- The local moment inequality on every measurable smaller-reveal test. -/
theorem setLIntegral_localPivotMeanFloor_le {b A B : ℝ} (K L : ℕ) (μ ρ : Matching n)
    (hcert : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      LocalPivotGeometry b A B μ ρ d flag →
      EligibleReverseMomentCertificate μ ρ d flag K L (localPivotIncrementCap B d)
        (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
        (B / Real.sqrt (n : ℝ)))
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫⁻ x in S, ENNReal.ofReal (localPivotMeanFloor b A B K μ ρ x) ∂stableMarkScoreLaw μ) ≤
      ∫⁻ x in S, ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x)
        ∂stableMarkScoreLaw μ := by
  have hSm := pivotMaleRevealSpace_le μ _ hS
  change ∃ W : Set (PivotMaleRevealData n), MeasurableSet W ∧ pivotMaleReveal μ ⁻¹' W = S at hS
  obtain ⟨W, hW, rfl⟩ := hS
  let S := pivotMaleReveal μ ⁻¹' W
  let f := fun x ↦ ENNReal.ofReal (localPivotMeanFloor b A B K μ ρ x)
  let g := fun x ↦ ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    ((measurable_maleReveal_localPivotMeanFloor b A B K μ ρ).mono (pivotMaleRevealSpace_le μ) le_rfl)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    (measurable_localFilteredDecorationCount b A B K L μ ρ)
  change (∫⁻ x in S, f x ∂stableMarkScoreLaw μ) ≤ ∫⁻ x in S, g x ∂stableMarkScoreLaw μ
  calc
    _ = ∫⁻ x, S.indicator f x ∂stableMarkScoreLaw μ := (lintegral_indicator hSm f).symm
    _ ≤ ∫⁻ x, S.indicator g x ∂stableMarkScoreLaw μ := by
      rw [lintegral_stableMarkScoreLaw μ (hf.indicator hSm),
        lintegral_stableMarkScoreLaw μ (hg.indicator hSm)]
      apply lintegral_mono_ae
      filter_upwards [hcert] with d hd
      rw [lintegral_offDiagonalNonblocking_eq_sum_masks d,
        lintegral_offDiagonalNonblocking_eq_sum_masks d]
      exact Finset.sum_le_sum fun flag _ ↦
        lintegral_fixedMask_meanFloor_le K L μ ρ d flag hW (hd flag)
    _ = _ := lintegral_indicator hSm g

/-- The real set-integral inequality used by the defining property of conditional expectation. -/
theorem setIntegral_localPivotMeanFloor_le {b A B : ℝ} (K L : ℕ) (μ ρ : Matching n)
    (hcert : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      LocalPivotGeometry b A B μ ρ d flag →
      EligibleReverseMomentCertificate μ ρ d flag K L (localPivotIncrementCap B d)
        (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
        (B / Real.sqrt (n : ℝ)))
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫ x in S, localPivotMeanFloor b A B K μ ρ x ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ∂stableMarkScoreLaw μ := by
  have hf := (integrable_localPivotMeanFloor b A B K μ ρ).integrableOn (s := S)
  have hg := (integrable_localFilteredDecorationCount b A B K L μ ρ
    (stableMarkScoreLaw μ)).integrableOn (s := S)
  have hnf : 0 ≤ᵐ[(stableMarkScoreLaw μ).restrict S] localPivotMeanFloor b A B K μ ρ :=
    Eventually.of_forall (localPivotMeanFloor_nonneg b A B K μ ρ)
  have hng : 0 ≤ᵐ[(stableMarkScoreLaw μ).restrict S] localFilteredDecorationCount b A B K L μ ρ :=
    Eventually.of_forall (localFilteredDecorationCount_nonneg b A B K L μ ρ)
  rw [integral_eq_lintegral_of_nonneg_ae hnf hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hng hg.aestronglyMeasurable]
  exact ENNReal.toReal_mono ((hasFiniteIntegral_iff_ofReal hng).mp hg.2).ne
    (setLIntegral_localPivotMeanFloor_le K L μ ρ hcert hS)

/-- The conditional mean of the local filtered count under the smaller reveal. -/
noncomputable def localPivotConditionalMean (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ScoreProfile n → ℝ :=
  (stableMarkScoreLaw μ)[localFilteredDecorationCount b A B K L μ ρ|pivotMaleRevealSpace μ]

/-- Every eligible mark has the same linear lower bound, almost surely. -/
theorem localPivotMeanFloor_le_conditionalMean_ae {b A B : ℝ} (K L : ℕ) (μ ρ : Matching n)
    (hcert : ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
      LocalPivotGeometry b A B μ ρ d flag →
      EligibleReverseMomentCertificate μ ρ d flag K L (localPivotIncrementCap B d)
        (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
        (B / Real.sqrt (n : ℝ))) :
    localPivotMeanFloor b A B K μ ρ ≤ᵐ[stableMarkScoreLaw μ]
      localPivotConditionalMean b A B K L μ ρ :=
  ae_le_condExp_of_forall_setIntegral_le (pivotMaleRevealSpace_le μ) (stableMarkScoreLaw μ)
    (integrable_localFilteredDecorationCount b A B K L μ ρ (stableMarkScoreLaw μ))
    (integrable_localPivotMeanFloor b A B K μ ρ)
    (measurable_maleReveal_localPivotMeanFloor b A B K μ ρ).stronglyMeasurable
    (fun _ hS ↦ setIntegral_localPivotMeanFloor_le K L μ ρ hcert hS)

/-- With the chosen asymptotic budgets the lower conditional bound is
uniform in all fixed marks, pivots, and lower and upper length cutoffs. -/
theorem eventually_localPivotMeanFloor_le_conditionalMean_ae (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),
      localPivotMeanFloor b A B (K n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]
        localPivotConditionalMean b A B (K n) (L n) μ ρ := by
  filter_upwards [eventually_ae_diagonal_localPivotGeometry_certificate K L hB hκ hK hL
    hsmallLabel hsmallCompat] with n hn μ ρ b A
  exact localPivotMeanFloor_le_conditionalMean_ae (K n) (L n) μ ρ <|
    (hn μ).mono fun d hd flag hgeom ↦ hd ρ flag hgeom

end LennonPittelFormalization

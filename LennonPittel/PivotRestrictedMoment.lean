module

public import LennonPittel.PivotLocalEligibility
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Lower moments on arbitrary forward reveal tests

The moment controls are inherited by every measurable subset of the eligible
revealed-score set. This lets us test a conditional mean by any revealed
event, including events of arbitrarily small mass.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Restricting the active male observations only decreases the marked law. -/
theorem forwardMaskRevealLaw_mono {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    {U V : Set (ForwardRevealedMaleScores flag)} (hUV : U ⊆ V) :
    forwardMaskRevealLaw d flag U ≤ forwardMaskRevealLaw d flag V :=
  Measure.restrict_mono (Set.preimage_mono hUV) le_rfl

/-- The same compatibility estimates hold on a smaller measurable reveal event. -/
theorem ReverseCompatibilityControls.restrict_reveal {n : ℕ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    {U V : Set (ForwardRevealedMaleScores flag)} {a D : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hV : MeasurableSet V) (hVU : V ⊆ U) :
    ReverseCompatibilityControls μ ρ d flag V a D :=
  ⟨hV, h.female_nonneg, h.female_lt_one, h.male_mem, h.male_total_pos, h.inflation_pos,
    h.kept_mass, fun v hv ↦ h.increment_nonneg v (hVU hv),
    fun v hv ↦ h.increment_sum_le v (hVU hv), h.tie_free,
    ae_mono (forwardMaskRevealLaw_mono d flag hVU) h.pivot_exposed⟩

/-- The same lower moment holds after imposing any measurable reveal test
inside the eligible set, with the correct mass of the tested event. -/
theorem EligibleReverseMomentCertificate.filteredFamilyMoment_of_subset
    {n K L : ℕ} {μ ρ : Matching n} {d : DiagonalScorePairs n}
    {flag : OffDiagonalCellIndex n → Bool} {D s u p : ℝ}
    (h : EligibleReverseMomentCertificate μ ρ d flag K L D s u p)
    {U : Set (ForwardRevealedMaleScores flag)} (hU : MeasurableSet U)
    (hsub : U ⊆ eligiblePivotRevealSet d flag ρ D) :
    (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 64) * ((K - 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ z, (∑ k ∈ Finset.Icc 2 K, ((filteredReverseSupportFamily μ ρ flag k L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal d))
        ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞)) ∂forwardMaskRevealLaw d flag U :=
  lintegral_sum_card_filteredReverseSupportFamily_ge μ ρ d flag U L h.short_scale h.n_pos
    (h.compatibility.restrict_reveal hU hsub) h.unfiltered h.upper
    h.relaxed_inflation_ge_one h.compatibility_budget h.short_budget h.increment_budget

section ConditionalOrder

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω}

/-- Test a measurable lower bound on the conditional mean by set integrals. -/
theorem ae_le_condExp_of_forall_setIntegral_le (hm : m ≤ m₀) (ν : @Measure Ω m₀)
    [IsFiniteMeasure ν] {f g : Ω → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (hgm : StronglyMeasurable[m] g)
    (h : ∀ S, MeasurableSet[m] S → (∫ x in S, g x ∂ν) ≤ ∫ x in S, f x ∂ν) :
    g ≤ᵐ[ν] ν[f|m] := by
  have hcm : StronglyMeasurable[m] (ν[f|m]) := stronglyMeasurable_condExp
  have hgi : Integrable g (ν.trim hm) := hg.trim hm hgm
  have hci : Integrable (ν[f|m]) (ν.trim hm) := integrable_condExp.trim hm hcm
  apply ae_of_ae_trim hm
  refine ae_le_of_forall_setIntegral_le hgi hci fun S hS _ ↦ ?_
  rw [← setIntegral_trim hm hgm hS, ← setIntegral_trim hm hcm hS, setIntegral_condExp hm hf hS]
  exact h S hS

end ConditionalOrder

/-- The unnormalized score law of a fixed stable marked matching. -/
noncomputable def stableMarkScoreLaw {n : ℕ} (μ : Matching n) : Measure (ScoreProfile n) :=
  (continuousScoreLaw n).restrict {x | IsScoreStable x μ}

instance {n : ℕ} (μ : Matching n) : IsFiniteMeasure (stableMarkScoreLaw μ) :=
  inferInstanceAs (IsFiniteMeasure ((continuousScoreLaw n).restrict _))

/-- Disintegrate the fixed stable mark over all spouse diagonals. -/
theorem lintegral_stableMarkScoreLaw {n : ℕ} (μ : Matching n)
    {f : ScoreProfile n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂stableMarkScoreLaw μ) =
      ∫⁻ d, ∫⁻ z, f ((splitScorePairs μ).symm (d, z))
        ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) ∂diagonalScoreLaw n := by
  simpa only [stableMarkScoreLaw, mem_univ, and_true, Measure.restrict_univ] using
    continuousScoreLaw_lintegral_stable_and_diagonal μ (C := univ) MeasurableSet.univ hf

/-- At a fixed diagonal the mask events form a measurable finite partition. -/
theorem lintegral_offDiagonalNonblocking_eq_sum_masks {n : ℕ}
    (d : DiagonalScorePairs n) (f : OffDiagonalScorePairs n → ℝ≥0∞) :
    (∫⁻ z, f z ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d))) =
      ∑ flag : OffDiagonalCellIndex n → Bool,
        ∫⁻ z in forwardScoreMaskEvent d flag, f z
          ∂((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)) := by
  classical
  have hU : (⋃ flag ∈ (Finset.univ : Finset (OffDiagonalCellIndex n → Bool)),
      forwardScoreMaskEvent d flag) = univ := by
    ext z
    constructor
    · exact fun _ ↦ mem_univ _
    · intro _
      exact mem_iUnion.mpr ⟨forwardMaskOfScores d z, mem_iUnion.mpr
        ⟨Finset.mem_univ _, (forwardMaskOfScores_eq_iff _ _ _).mp rfl⟩⟩
  let ν := (offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)
  calc
    _ = ∫⁻ z in ⋃ flag ∈ (Finset.univ : Finset (OffDiagonalCellIndex n → Bool)),
        forwardScoreMaskEvent d flag, f z ∂ν := by rw [hU, Measure.restrict_univ]
    _ = _ := by
      refine lintegral_biUnion_finset ?_ (fun flag _ ↦ measurableSet_forwardScoreMaskEvent d flag) _
      intro a _ b _ hab
      exact Set.disjoint_left.mpr fun z ha hb ↦ hab
        (((forwardMaskOfScores_eq_iff d z a).mpr ha).symm.trans
          ((forwardMaskOfScores_eq_iff d z b).mpr hb))

end LennonPittelFormalization

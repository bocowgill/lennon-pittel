module

public import LennonPittel.Model
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.ConditionalProbability

/-!
# Counting under a marked law

Drawing a finite mark uniformly, then conditioning on a measurable event, gives a normalized
counting formula for nonnegative or integrable real tests.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [Fintype A] [Nonempty A]

/-- The law of a uniform finite mark. -/
noncomputable def uniformMarkLaw (A : Type*) [MeasurableSpace A] [Fintype A] [Nonempty A] :
    Measure A :=
  (PMF.fintypeUniform A).toMeasure

instance uniformMarkLaw_isProbabilityMeasure : IsProbabilityMeasure (uniformMarkLaw A) :=
  inferInstanceAs (IsProbabilityMeasure (PMF.fintypeUniform A).toMeasure)

/-- The law of an independent uniform mark and a sample, conditioned on the marking event. -/
noncomputable def markedLaw (P : Measure Ω) (E : Set (Ω × A)) : Measure (Ω × A) :=
  ProbabilityTheory.cond (P.prod (uniformMarkLaw A)) E

/-- The expected number of admissible marks at the sample. -/
noncomputable def markedNormalizer (P : Measure Ω) (E : Set (Ω × A)) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ a, E.indicator 1 (ω, a) ∂P

/-- The conditional law is a probability measure when the marking event has positive mass. -/
theorem markedLaw_isProbabilityMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0) :
    IsProbabilityMeasure (markedLaw P E) :=
  ProbabilityTheory.cond_isProbabilityMeasure hpos

variable [MeasurableSingletonClass A]

private theorem lintegral_restrict_uniformMarkLaw (P : Measure Ω)
    {E : Set (Ω × A)} (hE : MeasurableSet E) {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in E, f z ∂P.prod (uniformMarkLaw A)) =
      (Fintype.card A : ℝ≥0∞)⁻¹ * (∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂P) := by
  rw [← lintegral_indicator hE, lintegral_prod _ (hf.indicator hE).aemeasurable]
  simp only [lintegral_fintype, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _), PMF.fintypeUniform_apply, ← Finset.sum_mul]
  rw [lintegral_mul_const' _ _ (by simp [Fintype.card_ne_zero]), mul_comm]

/-- The unconditioned probability of an admissible mark is the expected number of admissible
marks divided by the number of marks. -/
theorem uniform_mark_event_mass (P : Measure Ω) {E : Set (Ω × A)} (hE : MeasurableSet E) :
    (P.prod (uniformMarkLaw A)) E = (Fintype.card A : ℝ≥0∞)⁻¹ * markedNormalizer P E := by
  simpa [markedNormalizer] using
    lintegral_restrict_uniformMarkLaw P hE (f := 1) measurable_const

/-- Counting admissible marks pointwise and then averaging agrees with integrating under the
conditional joint law and multiplying by the expected number of admissible marks. -/
theorem marked_counting_identity (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hE : MeasurableSet E)
    (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0)
    {f : Ω × A → ℝ≥0∞} (hf : Measurable f) :
    markedNormalizer P E * (∫⁻ z, f z ∂markedLaw P E) =
      ∫⁻ ω, ∑ a, E.indicator f (ω, a) ∂P := by
  have hscaled : (Fintype.card A : ℝ≥0∞) * (P.prod (uniformMarkLaw A)) E =
      markedNormalizer P E := by
    rw [uniform_mark_event_mass P hE, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
  rw [← hscaled, markedLaw, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_restrict_uniformMarkLaw P hE hf]
  rw [mul_assoc, ← mul_assoc ((P.prod (uniformMarkLaw A)) E),
    ENNReal.mul_inv_cancel hpos (measure_lt_top _ _).ne, one_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]

private theorem integral_restrict_uniformMarkLaw (P : Measure Ω) [SFinite P]
    {E : Set (Ω × A)} (hE : MeasurableSet E) {f : Ω × A → ℝ}
    (hf : Integrable f (P.prod (uniformMarkLaw A))) :
    (∫ z in E, f z ∂P.prod (uniformMarkLaw A)) =
      ((Fintype.card A : ℝ≥0∞)⁻¹).toReal * (∫ ω, ∑ a, E.indicator f (ω, a) ∂P) := by
  rw [← integral_indicator hE, integral_prod _ (hf.indicator hE)]
  simp_rw [integral_fintype (memLp_one_iff_integrable.mp MemLp.of_discrete), measureReal_def,
    uniformMarkLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.fintypeUniform_apply, smul_eq_mul, ← Finset.mul_sum, integral_const_mul]

/-- The exact marked-counting formula for signed, integrable real tests. -/
theorem marked_integral_counting_identity (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Set (Ω × A)} (hE : MeasurableSet E)
    (hpos : (P.prod (uniformMarkLaw A)) E ≠ 0)
    {f : Ω × A → ℝ} (hf : Integrable f (P.prod (uniformMarkLaw A))) :
    (markedNormalizer P E).toReal * (∫ z, f z ∂markedLaw P E) =
      ∫ ω, ∑ a, E.indicator f (ω, a) ∂P := by
  have hscaled : (Fintype.card A : ℝ≥0∞) * (P.prod (uniformMarkLaw A)) E =
      markedNormalizer P E := by
    rw [uniform_mark_event_mass P hE, ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp), one_mul]
  have hm : ((P.prod (uniformMarkLaw A)) E).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpos, (measure_lt_top _ _).ne⟩
  have hc : (Fintype.card A : ℝ≥0∞).toReal ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [← hscaled, markedLaw, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul,
    integral_restrict_uniformMarkLaw P hE hf, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_inv]
  rw [mul_assoc, ← mul_assoc (((P.prod (uniformMarkLaw A)) E).toReal),
    mul_inv_cancel₀ hm, one_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

section StableMarriage

open StableMarriage

/-- Matchings are given the discrete measurable structure when used as finite marks. -/
scoped instance matchingMeasurableSpace (n : ℕ) : MeasurableSpace (Matching n) := ⊤

scoped instance matchingDiscreteMeasurableSpace (n : ℕ) :
    DiscreteMeasurableSpace (Matching n) :=
  ⟨fun _ ↦ trivial⟩

scoped instance profileDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (Profile n) :=
  ⟨fun _ ↦ trivial⟩

/-- The event that the marked matching is stable for its preference profile. -/
def stableMarkEvent (n : ℕ) : Set (Profile n × Matching n) :=
  {z | IsStable z.1 z.2}

theorem measurableSet_stableMarkEvent (n : ℕ) : MeasurableSet (stableMarkEvent n) :=
  .of_discrete

theorem sum_stableMarkEvent_indicator_one {n : ℕ} (p : Profile n) :
    (∑ a : Matching n, (stableMarkEvent n).indicator 1 (p, a)) =
      (numStableMatchings p : ℝ≥0∞) := by
  classical
  change (∑ a : Matching n, if IsStable p a then (1 : ℝ≥0∞) else 0) =
    (Fintype.card {a : Matching n // IsStable p a} : ℝ≥0∞)
  rw [Fintype.card_subtype, ← Finset.sum_filter]
  simp

/-- The finite-profile normalizer is the repository's real-valued expectation, viewed in
`ℝ≥0∞`. -/
theorem markedNormalizer_stableMarkEvent (n : ℕ) :
    markedNormalizer (uniformProfile n).toMeasure (stableMarkEvent n) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  rw [expectedNumStableMatchings, ofReal_integral_eq_lintegral_ofReal
    (memLp_one_iff_integrable.mp MemLp.of_discrete)
    (Filter.Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)]
  simp [markedNormalizer, sum_stableMarkEvent_indicator_one]

/-- The uniform independent profile and matching has positive probability of marking a stable
matching, since the identity is stable when everyone uses the same ordering. -/
theorem uniform_profile_stable_mark_ne_zero (n : ℕ) :
    ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) (stableMarkEvent n) ≠ 0 := by
  let p : Profile n := ⟨fun _ ↦ Equiv.refl _, fun _ ↦ Equiv.refl _⟩
  let m : Matching n := Equiv.refl _
  have hm : IsStable p m := fun _ _ hb ↦ lt_asymm hb.2.1 hb.2.2
  exact ne_of_gt <| calc
    0 < ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) {(p, m)} := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      simp only [uniformProfile, uniformMarkLaw, PMF.toMeasure_apply_singleton _ _
        (measurableSet_singleton _), PMF.fintypeUniform_apply]
      simp [pos_iff_ne_zero]
    _ ≤ ((uniformProfile n).toMeasure.prod (uniformMarkLaw (Matching n))) (stableMarkEvent n) :=
      measure_mono (Set.singleton_subset_iff.mpr hm)

/-- Exact marked counting for the repository's uniform preference model. -/
theorem stable_mark_counting_identity (n : ℕ) {f : Profile n × Matching n → ℝ≥0∞}
    (hf : Measurable f) :
    ENNReal.ofReal (expectedNumStableMatchings n) *
      (∫⁻ z, f z ∂markedLaw (uniformProfile n).toMeasure (stableMarkEvent n)) =
      ∫⁻ p, ∑ a, (stableMarkEvent n).indicator f (p, a) ∂(uniformProfile n).toMeasure := by
  simpa only [markedNormalizer_stableMarkEvent] using
    marked_counting_identity (uniformProfile n).toMeasure (measurableSet_stableMarkEvent n)
      (uniform_profile_stable_mark_ne_zero n) hf

end StableMarriage

end LennonPittelFormalization

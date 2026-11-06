module

public import LennonPittel.IidScoreRanks
public import LennonPittel.MarkedCounting
public import LennonPittel.ScoreRanks
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Continuous score and marked matching laws

The ranking map sends independent uniform scores to the finite uniform profile law.
The two stability events agree almost everywhere, including after an independent mark is drawn.
-/

@[expose] public section

open scoped BigOperators ENNReal LennonPittelFormalization
open MeasureTheory Set

namespace LennonPittelFormalization

/-- The uniform score law on the unit interval. -/
noncomputable def unitScoreLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitScoreLaw :=
  ⟨by simp [unitScoreLaw, Real.volume_Icc]⟩

instance : NullSingletonClass unitScoreLaw :=
  Measure.restrict.instNullSingletonClass _

private noncomputable def rankRowsEquiv (n : ℕ) :
    ((Fin n ⊕ Fin n) → Equiv.Perm (Fin n)) ≃ StableMarriage.Profile n where
  toFun p := ⟨p ∘ Sum.inl, p ∘ Sum.inr⟩
  invFun p := Sum.elim p.manRank p.womanRank
  left_inv _ := funext fun i ↦ Sum.rec (fun _ ↦ rfl) (fun _ ↦ rfl) i
  right_inv := fun ⟨_, _⟩ ↦ rfl

private theorem measurePreserving_rankRowsEquiv (n : ℕ) :
    MeasurePreserving (rankRowsEquiv n)
      (Measure.pi fun _ : Fin n ⊕ Fin n ↦
        (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure)
      (StableMarriage.uniformProfile n).toMeasure := by
  refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun p ↦ ?_⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton p)]
  rw [show (rankRowsEquiv n) ⁻¹' {p} = {(rankRowsEquiv n).symm p} by
    ext x
    simp [← Equiv.eq_symm_apply]]
  rw [StableMarriage.uniformProfile, PMF.toMeasure_apply_singleton _ p (measurableSet_singleton _)]
  simp [← Fintype.card_congr (rankRowsEquiv n), ENNReal.inv_pow]

/-- Independently sample one uniform score for each entry of every preference row. -/
noncomputable def continuousScoreLaw (n : ℕ) : Measure (ScoreProfile n) :=
  Measure.pi fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw

instance (n : ℕ) : IsProbabilityMeasure (continuousScoreLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ⊕ Fin n ↦
    Measure.pi fun _ : Fin n ↦ unitScoreLaw))

/-- All rows of the continuous score model are almost surely tie-free. -/
theorem ae_injective_rows (n : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∀ r, Function.Injective (x r) :=
  ae_all_iff.2 fun _ ↦ Measure.tendsto_eval_ae_ae.eventually (ae_injective_iid unitScoreLaw n)

/-- Ranking the score rows has exactly the uniform finite preference-profile law. -/
theorem measurePreserving_profileOfScores (n : ℕ) :
    MeasurePreserving (@profileOfScores n) (continuousScoreLaw n)
      (StableMarriage.uniformProfile n).toMeasure :=
  (measurePreserving_rankRowsEquiv n).comp
    (measurePreserving_pi _ _ fun _ ↦
      measurePreserving_rank_of_iid unitScoreLaw (measurable_rankPermutation n)
        (fun _ hx ↦ rankPermutation_lt_iff hx))

/-- The event that the independent mark is stable by score comparisons. -/
def scoreMarkEvent (n : ℕ) : Set (ScoreProfile n × StableMarriage.Matching n) :=
  {z | IsScoreStable z.1 z.2}

private theorem measurableSet_scoreMarkEvent (n : ℕ) :
    MeasurableSet (scoreMarkEvent n) :=
  measurableSet_scoreStableEvent n

/-- The rank conversion sends the score-and-mark law to the finite profile-and-mark law. -/
theorem measurePreserving_scoreAndMark (n : ℕ) :
    MeasurePreserving (Prod.map (@profileOfScores n) id)
      ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n)))
      ((StableMarriage.uniformProfile n).toMeasure.prod
        (uniformMarkLaw (StableMarriage.Matching n))) :=
  (measurePreserving_profileOfScores n).prod (MeasurePreserving.id _)

/-- The two marking events agree except on a null set of tied score profiles. -/
theorem score_mark_event_ae_eq (n : ℕ) :
    scoreMarkEvent n =ᵐ[((continuousScoreLaw n).prod
      (uniformMarkLaw (StableMarriage.Matching n)))]
      (Prod.map (@profileOfScores n) id) ⁻¹' stableMarkEvent n :=
  ((Measure.quasiMeasurePreserving_fst
    (μ := continuousScoreLaw n) (ν := uniformMarkLaw (StableMarriage.Matching n))).ae
      (ae_injective_rows n)).mono fun z hz ↦
    propext (isStable_profileOfScores_iff hz z.2).symm

/-- Stability has the same probability in the continuous and ordinal marking experiments. -/
theorem score_mark_event_mass_eq (n : ℕ) :
    ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n))) (scoreMarkEvent n) =
    ((StableMarriage.uniformProfile n).toMeasure.prod
      (uniformMarkLaw (StableMarriage.Matching n))) (stableMarkEvent n) :=
  (measure_congr (score_mark_event_ae_eq n)).trans
    ((measurePreserving_scoreAndMark n).measure_preimage
      (measurableSet_stableMarkEvent n).nullMeasurableSet)

/-- The law of the scores and the mark, conditioned on score stability. -/
noncomputable def scoreMarkedLaw (n : ℕ) :
    Measure (ScoreProfile n × StableMarriage.Matching n) :=
  markedLaw (continuousScoreLaw n) (scoreMarkEvent n)

instance (n : ℕ) : IsProbabilityMeasure (scoreMarkedLaw n) :=
  markedLaw_isProbabilityMeasure (continuousScoreLaw n)
    ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n))

/-- After conditioning, ranking the scores still gives the corresponding finite marked law. -/
theorem map_scoreMarkedLaw (n : ℕ) :
    (scoreMarkedLaw n).map (Prod.map (@profileOfScores n) id) =
      markedLaw (StableMarriage.uniformProfile n).toMeasure (stableMarkEvent n) := by
  rw [scoreMarkedLaw, markedLaw, markedLaw, ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul _ (measurePreserving_scoreAndMark n).measurable.aemeasurable,
    score_mark_event_mass_eq n, Measure.restrict_congr_set
      (score_mark_event_ae_eq n), ← Measure.restrict_map
      (measurePreserving_scoreAndMark n).measurable (measurableSet_stableMarkEvent n),
    (measurePreserving_scoreAndMark n).map_eq]

/-- The continuous count has the same expected value as the finite stable-matching count. -/
theorem markedNormalizer_scoreMarkEvent (n : ℕ) :
    markedNormalizer (continuousScoreLaw n) (scoreMarkEvent n) =
      ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n) := by
  have h := congrArg ((Fintype.card (StableMarriage.Matching n) : ℝ≥0∞) * ·)
    (score_mark_event_mass_eq n)
  simpa only [uniform_mark_event_mass _ (measurableSet_scoreMarkEvent n),
    uniform_mark_event_mass _ (measurableSet_stableMarkEvent n), ← mul_assoc,
    ENNReal.mul_inv_cancel (a := (Fintype.card (StableMarriage.Matching n) : ℝ≥0∞))
      (by simp [Fintype.card_ne_zero]) (by simp), one_mul,
    markedNormalizer_stableMarkEvent] using h

/-- Averaging the sum over all stable marks equals the conditional marked expectation times
the mean number of stable matchings. The test may depend on the actual scores. -/
theorem continuous_mark_counting_identity (n : ℕ)
    {f : ScoreProfile n × StableMarriage.Matching n → ℝ≥0∞} (hf : Measurable f) :
    ENNReal.ofReal (StableMarriage.expectedNumStableMatchings n) *
      (∫⁻ z, f z ∂scoreMarkedLaw n) =
      ∫⁻ x, ∑ m, (scoreMarkEvent n).indicator f (x, m) ∂continuousScoreLaw n := by
  simpa only [markedNormalizer_scoreMarkEvent, scoreMarkedLaw] using
    marked_counting_identity (continuousScoreLaw n) (measurableSet_scoreMarkEvent n)
      ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n)) hf

/-- The real-valued counting identity for tests integrable under the unconditioned joint law. -/
theorem continuous_mark_integral_counting_identity (n : ℕ)
    {f : ScoreProfile n × StableMarriage.Matching n → ℝ}
    (hf : Integrable f
      ((continuousScoreLaw n).prod (uniformMarkLaw (StableMarriage.Matching n)))) :
    StableMarriage.expectedNumStableMatchings n * (∫ z, f z ∂scoreMarkedLaw n) =
      ∫ x, ∑ m, (scoreMarkEvent n).indicator f (x, m) ∂continuousScoreLaw n := by
  have hn : 0 ≤ StableMarriage.expectedNumStableMatchings n :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  simpa only [markedNormalizer_scoreMarkEvent, ENNReal.toReal_ofReal hn, scoreMarkedLaw] using
    marked_integral_counting_identity (continuousScoreLaw n) (measurableSet_scoreMarkEvent n)
      ((score_mark_event_mass_eq n).trans_ne (uniform_profile_stable_mark_ne_zero n)) hf

end LennonPittelFormalization

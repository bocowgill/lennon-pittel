module

public import LennonPittel.PivotForwardForest
public import LennonPittel.SingletonRotationAnchor

/-!
# Counting rotations through their singleton anchors

A realized rotation is uniquely identified by the stable matching at which it is the
sole exposed rotation, together with its cycle at that matching. The correspondence
preserves the size of the cycle support.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal LennonPittelFormalization

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}

/-- A stable matching paired with its unique exposed forward cycle. -/
abbrev SingletonAnchorPair (p : Profile n) :=
  {a : Matching n × Matching n // IsStable p a.1 ∧ IsSoleForwardExposedRotation p a.1 a.2}

/-- Every realized rotation is represented by its singleton anchor and exposed cycle. -/
noncomputable def rotationEquivSingletonAnchorPair (hopt : IsManOptimal p μ₀) :
    Rotation p μ₀ ≃ SingletonAnchorPair p where
  toFun r :=
    ⟨((singletonRotationAnchor hopt r).val, r.val.cycle),
      (singletonRotationAnchor hopt r).property,
      (isExposedRotation_singletonRotationAnchor_iff hopt r _).mpr rfl,
      fun σ hσ ↦ (isExposedRotation_singletonRotationAnchor_iff hopt r σ).mp hσ⟩
  invFun a := rotationOfExposed hopt a.property.1 a.property.2.1
  left_inv r := by
    apply Subtype.ext
    exact (((eq_singletonRotationAnchor_iff hopt r _).mp rfl r).mpr rfl).2
  right_inv a := by
    let ν : {ν : Matching n // IsStable p ν} := ⟨a.val.1, a.property.1⟩
    let r := rotationOfExposed hopt ν.property a.property.2.1
    have hs (s : Rotation p μ₀) : s.IsExposedAt ν.val ↔ s = r := by
      constructor
      · intro he
        have hcycle := a.property.2.2 s.val.cycle he.1
        apply Subtype.ext
        change s.val = rotationLabel ν.val a.val.2
        rw [← he.2, hcycle]
      · rintro rfl
        exact ⟨a.property.2.1, rfl⟩
    have hν := (eq_singletonRotationAnchor_iff hopt r ν).mpr hs
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hν.symm) rfl)

/-- The cycle support size is unchanged by passage to the singleton anchor. -/
theorem rotationEquivSingletonAnchorPair_length (hopt : IsManOptimal p μ₀)
    (r : Rotation p μ₀) :
    ((rotationEquivSingletonAnchorPair hopt r).val.2.support.card) =
      r.val.cycle.support.card :=
  rfl

open scoped Classical in
/-- Weighted rotation counts can be evaluated by summing over all stable marks and
their sole exposed cycles. -/
theorem sum_rotation_lengthWeight_eq_sum_singletonAnchors {W : Type*} [AddCommMonoid W]
    [Fintype (Rotation p μ₀)] (hopt : IsManOptimal p μ₀) (g : ℕ → W) :
    (∑ r : Rotation p μ₀, g r.val.cycle.support.card) =
      ∑ ν : Matching n, ∑ σ : Matching n,
        if IsStable p ν ∧ IsSoleForwardExposedRotation p ν σ then g σ.support.card else 0 := by
  let f (a : Matching n × Matching n) := g a.2.support.card
  let q (a : Matching n × Matching n) :=
    IsStable p a.1 ∧ IsSoleForwardExposedRotation p a.1 a.2
  calc
    _ = ∑ a : SingletonAnchorPair p, f a.val :=
      Fintype.sum_equiv (rotationEquivSingletonAnchorPair hopt) _ _ fun _ ↦ rfl
    _ = ∑ a ∈ Finset.univ.filter q, f a :=
      (Finset.sum_subtype _ (by simp [q]) f).symm
    _ = ∑ a : Matching n × Matching n, if q a then f a else 0 :=
      Finset.sum_filter ..
    _ = _ := Fintype.sum_prod_type _

open scoped Classical in
/-- A length weight contributed by a sole exposed cycle, zero if the mark has no such cycle. -/
noncomputable def singletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (μ : Matching n) (g : ℕ → W) : W :=
  ∑ σ : Matching n, if IsSoleForwardExposedRotation p μ σ then g σ.support.card else 0

open scoped Classical in
/-- The total length weight of singleton anchors in a profile, counting only stable marks. -/
noncomputable def profileSingletonAnchorLengthWeight {W : Type*} [AddCommMonoid W]
    (p : Profile n) (g : ℕ → W) : W :=
  ∑ μ : Matching n, if IsStable p μ then singletonAnchorLengthWeight p μ g else 0

/-- The profile total computes the realized rotation length sum from any man-optimal start. -/
theorem sum_rotation_lengthWeight_eq_profileSingletonAnchorLengthWeight {W : Type*}
    [AddCommMonoid W] [Fintype (Rotation p μ₀)] (hopt : IsManOptimal p μ₀) (g : ℕ → W) :
    (∑ r : Rotation p μ₀, g r.val.cycle.support.card) =
      profileSingletonAnchorLengthWeight p g := by
  classical
  rw [sum_rotation_lengthWeight_eq_sum_singletonAnchors hopt]
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  exact Finset.sum_congr rfl fun μ _ ↦ by
    by_cases hμ : IsStable p μ <;> simp [hμ]

/-- The score array has a stable mark with the prescribed sole rank-exposed cycle. -/
def scoreStableSingletonAnchorEvent (μ σ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsSoleForwardExposedRotation (profileOfScores x) μ σ}

/-- The fixed-match, fixed-cycle singleton-anchor event is measurable. -/
theorem measurableSet_scoreStableSingletonAnchorEvent (μ σ : Matching n) :
    MeasurableSet (scoreStableSingletonAnchorEvent μ σ) :=
  (measurableSet_isScoreStable μ).inter
    ((measurable_profileOfScores n) (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsSoleForwardExposedRotation p μ σ}))

/-- The rotation length expectation in the finite model is the sum of the weighted
stable singleton-anchor events in the score model. -/
theorem lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent
    (n : ℕ) (g : ℕ → ℝ≥0∞) :
    (∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) =
      ∑ μ : Matching n, ∑ σ : Matching n,
        g σ.support.card * continuousScoreLaw n (scoreStableSingletonAnchorEvent μ σ) := by
  classical
  let f (μ σ : Matching n) := (scoreStableSingletonAnchorEvent μ σ).indicator
    (fun _ ↦ g σ.support.card)
  have hf (μ σ : Matching n) : Measurable (f μ σ) :=
    measurable_const.indicator (measurableSet_scoreStableSingletonAnchorEvent μ σ)
  have he : (fun x ↦ profileSingletonAnchorLengthWeight (profileOfScores x) g) =ᵐ[
      continuousScoreLaw n] fun x ↦ ∑ μ : Matching n, ∑ σ : Matching n, f μ σ x := by
    filter_upwards [ae_injective_rows n] with x hx
    unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    by_cases hμ : IsScoreStable x μ <;>
      simp [f, scoreStableSingletonAnchorEvent, Set.indicator,
        isStable_profileOfScores_iff hx μ, hμ]
  rw [← (measurePreserving_profileOfScores n).lintegral_comp Measurable.of_discrete,
    lintegral_congr_ae he, lintegral_finsetSum _ (fun μ _ ↦
      Finset.measurable_sum _ fun σ _ ↦ hf μ σ)]
  exact Finset.sum_congr rfl fun μ _ ↦ by
    rw [lintegral_finsetSum _ (fun σ _ ↦ hf μ σ)]
    exact Finset.sum_congr rfl fun σ _ ↦
      lintegral_indicator_const (measurableSet_scoreStableSingletonAnchorEvent μ σ) _

/-- The length expectation is the mean stable-matching count times the corresponding
length test under the conditioned score-mark law. -/
theorem lintegral_profileSingletonAnchorLengthWeight_eq_scoreMarkedLaw
    (n : ℕ) (g : ℕ → ℝ≥0∞) :
    (∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) =
      ENNReal.ofReal (expectedNumStableMatchings n) *
        ∫⁻ z, singletonAnchorLengthWeight (profileOfScores z.1) z.2 g ∂scoreMarkedLaw n := by
  classical
  let f (z : Profile n × Matching n) := singletonAnchorLengthWeight z.1 z.2 g
  have hf : Measurable f := Measurable.of_discrete
  have hpres : MeasurePreserving (Prod.map (@profileOfScores n) id) (scoreMarkedLaw n)
      (markedLaw (uniformProfile n).toMeasure (stableMarkEvent n)) :=
    ⟨(measurePreserving_scoreAndMark n).measurable, map_scoreMarkedLaw n⟩
  have h := stable_mark_counting_identity n hf
  rw [← hpres.lintegral_comp hf] at h
  exact h.symm

end LennonPittelFormalization

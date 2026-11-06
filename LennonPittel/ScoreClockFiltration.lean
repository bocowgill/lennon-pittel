module

public import LennonPittel.ScoreRotationHistory
public import Mathlib.Probability.Process.Adapted

/-!
# The natural filtration of the participation clock

The entire walk is measurable without dropping tied score profiles. Its
structural choices take countably many values and depend on finitely many
score comparisons at each checkpoint. The clock filtration records just
the real clock values through the current checkpoint.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

private abbrev DMeasurable {α β : Type*} [MeasurableSpace α] (f : α → β) : Prop :=
  @Measurable α β inferInstance ⊤ f

private theorem dmeasurable_postcomp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {f : α → β} (hf : DMeasurable f) (g : β → γ) : Measurable (g ∘ f) :=
  fun s _ ↦ hf (t := g ⁻¹' s) MeasurableSpace.measurableSet_top

private theorem dmeasurable_postcomp_discrete {α β γ : Type*} [MeasurableSpace α]
    {f : α → β} (hf : DMeasurable f) (g : β → γ) : DMeasurable (g ∘ f) :=
  @dmeasurable_postcomp _ _ _ _ ⊤ _ hf g

private theorem dmeasurable_pi {α ι β : Type*} [MeasurableSpace α] [Countable ι]
    [Countable (ι → β)] {f : α → ι → β}
    (h : ∀ i, DMeasurable fun x ↦ f x i) : DMeasurable f := by
  let : MeasurableSpace (ι → β) := ⊤
  apply measurable_to_countable'
  intro b
  have heq : f ⁻¹' {b} = ⋂ i, (fun x ↦ f x i) ⁻¹' {b i} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iInter, funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun i ↦ h i MeasurableSpace.measurableSet_top

private theorem dmeasurable_prod {α β γ : Type*} [MeasurableSpace α]
    [Countable β] [Countable γ] {f : α → β} {g : α → γ}
    (hf : DMeasurable f) (hg : DMeasurable g) :
    DMeasurable fun x ↦ (f x, g x) := by
  let : MeasurableSpace (β × γ) := ⊤
  apply measurable_to_countable'
  rintro ⟨b, c⟩
  rw [show (fun x ↦ (f x, g x)) ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} by
    ext x
    simp]
  exact (hf (t := {b}) MeasurableSpace.measurableSet_top).inter
    (hg (t := {c}) MeasurableSpace.measurableSet_top)

private theorem measurable_discrete_cases {α β γ : Type*} [MeasurableSpace α] [Countable β]
    [MeasurableSpace γ] {f : α → β} (hf : DMeasurable f) (g : β → α → γ)
    (hg : ∀ b, Measurable (g b)) : Measurable fun x ↦ g (f x) x := by
  intro s hs
  have heq : (fun x ↦ g (f x) x) ⁻¹' s = ⋃ b, (f ⁻¹' {b}) ∩ (g b ⁻¹' s) := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun b ↦ (hf MeasurableSpace.measurableSet_top).inter (hg b hs)

private theorem dmeasurable_discrete_cases {α β γ : Type*} [MeasurableSpace α] [Countable β]
    {f : α → β} (hf : DMeasurable f) (g : β → α → γ)
    (hg : ∀ b, DMeasurable (g b)) : DMeasurable fun x ↦ g (f x) x :=
  @measurable_discrete_cases _ _ _ _ _ ⊤ _ hf g hg

variable {n : ℕ}

private theorem measurable_scoreComparison (μ : Matching n) (m w : Fin n) :
    DMeasurable fun x : ScoreProfile n ↦
      successorScoreOracle (femaleSpouseScore x μ) (fun v ↦ x (.inr v)) m w := by
  let E : Set (ScoreProfile n) := {x | x (.inr w) m < femaleSpouseScore x μ w}
  have hE : MeasurableSet E := measurableSet_lt
    ((measurable_pi_apply m).comp (measurable_pi_apply (Sum.inr w : Fin n ⊕ Fin n)))
    (measurable_femaleSpouseScore μ w)
  let : MeasurableSpace Bool := ⊤
  apply measurable_to_countable'
  intro b
  cases b
  · convert hE.compl using 1
    ext x
    simp [successorScoreOracle, E]
  · convert hE using 1
    ext x
    simp [successorScoreOracle, E]

/-- The comparison-selected graph is measurable with the discrete target space. -/
theorem measurable_scoreRotationGraph (μ : Matching n) :
    @Measurable (ScoreProfile n) (Fin n → Option (Fin n)) inferInstance ⊤
      (fun x ↦ scoreRotationGraph x μ) := by
  have hp : DMeasurable (@profileOfScores n) := measurable_profileOfScores n
  have hor : DMeasurable fun x : ScoreProfile n ↦
      successorScoreOracle (femaleSpouseScore x μ) (fun w ↦ x (.inr w)) :=
    dmeasurable_pi fun m ↦ dmeasurable_pi fun w ↦ measurable_scoreComparison μ m w
  exact dmeasurable_postcomp_discrete (dmeasurable_prod hp hor) fun z ↦
    queriedSuccessorGraph z.1.manRank μ z.2

/-- The walk at a fixed start and horizon is measurable as a discrete structural record. -/
theorem measurable_scoreRotationWalk (k : ℕ) (μ : Matching n) :
    @Measurable (ScoreProfile n) (List (Equiv.Perm (Fin n)) × Matching n) inferInstance ⊤
      (fun x ↦ scoreRotationWalk x k μ) := by
  induction k generalizing μ with
  | zero => exact measurable_const
  | succ k ih =>
    have hnext : DMeasurable fun x : ScoreProfile n ↦
        chooseQueriedRotation (scoreRotationGraph x μ) :=
      dmeasurable_postcomp_discrete (measurable_scoreRotationGraph μ) chooseQueriedRotation
    simp only [scoreRotationWalk]
    refine dmeasurable_discrete_cases hnext (fun b x ↦ match b with
      | none => ([], μ)
      | some ρ =>
        let z := scoreRotationWalk x k (eliminateRotation μ ρ)
        (ρ :: z.1, z.2)) ?_
    intro b
    cases b with
    | none => exact measurable_const
    | some ρ => exact dmeasurable_postcomp_discrete (ih _) fun z ↦ (ρ :: z.1, z.2)

/-- Deferred acceptance uses the measurable finite rank profile. -/
theorem measurable_scoreWalkStart (n : ℕ) :
    @Measurable (ScoreProfile n) (Matching n) inferInstance ⊤
      (fun x ↦ DAState.matching (profileOfScores x)) := by
  have hp : DMeasurable (@profileOfScores n) := measurable_profileOfScores n
  exact dmeasurable_postcomp_discrete hp DAState.matching

/-- The structural record from the actual DA start is measurable. -/
theorem measurable_scoreWalkRecord (n k : ℕ) :
    @Measurable (ScoreProfile n) (List (Equiv.Perm (Fin n)) × Matching n) inferInstance ⊤
      (fun x ↦ scoreRotationWalk x k (DAState.matching (profileOfScores x))) :=
  dmeasurable_discrete_cases (measurable_scoreWalkStart n) (fun μ x ↦ scoreRotationWalk x k μ)
    (fun μ ↦ measurable_scoreRotationWalk k μ)

/-- The current matching is a measurable discrete function of the scores. -/
theorem measurable_scoreWalkCheckpoint (n k : ℕ) :
    @Measurable (ScoreProfile n) (Matching n) inferInstance ⊤
      (fun x ↦ (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2) :=
  dmeasurable_postcomp_discrete (measurable_scoreWalkRecord n k) Prod.snd

/-- The next choice is measurable, including the `none` case at termination. -/
theorem measurable_scoreWalkNext (n k : ℕ) :
    @Measurable (ScoreProfile n) (Option (Equiv.Perm (Fin n))) inferInstance ⊤
      (fun x ↦ chooseQueriedRotation (scoreRotationGraph x
        (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2)) :=
  dmeasurable_discrete_cases (measurable_scoreWalkCheckpoint n k) (fun μ x ↦
    chooseQueriedRotation (scoreRotationGraph x μ)) (fun μ ↦
      dmeasurable_postcomp_discrete (measurable_scoreRotationGraph μ) chooseQueriedRotation)

/-- The centered clock value is measurable on the full continuous score space. -/
theorem measurable_scoreWalkClock (n k : ℕ) :
    Measurable (fun x : ScoreProfile n ↦ scoreWalkClock x k) := by
  have hpot (μ : Matching n) : Measurable fun x : ScoreProfile n ↦ femaleLogPotential x μ :=
    Finset.measurable_sum _ fun i _ ↦ (measurable_femaleSpouseScore μ i).log.neg
  exact ((measurable_discrete_cases (measurable_scoreWalkRecord n k)
      (fun z x ↦ femaleLogPotential x z.2) (fun z ↦ hpot z.2)).sub
    (measurable_discrete_cases (measurable_scoreWalkStart n)
      (fun μ x ↦ femaleLogPotential x μ) hpot)).sub
    (dmeasurable_postcomp (measurable_scoreWalkRecord n k) fun z ↦
      (rotationParticipation z.1 : ℝ))

/-- The finite real-valued history through time `k`, including time zero. -/
noncomputable def scoreWalkClockHistory (x : ScoreProfile n) (k : ℕ) : Fin (k + 1) → ℝ :=
  fun i ↦ scoreWalkClock x i

theorem measurable_scoreWalkClockHistory (n k : ℕ) :
    Measurable (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k) :=
  Measurable.of_eval fun i ↦ measurable_scoreWalkClock n i

/-- The natural clock filtration, represented by the pullback of its finite history. -/
noncomputable def scoreWalkClockFiltration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ScoreProfile n)) where
  seq k :=
    MeasurableSpace.comap (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k) inferInstance
  mono' i j hij := by
    let trim : (Fin (j + 1) → ℝ) → Fin (i + 1) → ℝ :=
      fun z k ↦ z (k.castLE (Nat.succ_le_succ hij))
    have ht : Measurable trim := Measurable.of_eval fun k ↦ measurable_pi_apply _
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨trim ⁻¹' A, ht hA, rfl⟩
  le' k := (measurable_scoreWalkClockHistory n k).comap_le

/-- The finite-history presentation agrees with Mathlib's natural filtration. -/
theorem scoreWalkClockFiltration_eq_natural (n : ℕ) :
    scoreWalkClockFiltration n =
      Filtration.natural (fun k (x : ScoreProfile n) ↦ scoreWalkClock x k)
        (fun k ↦ (measurable_scoreWalkClock n k).stronglyMeasurable) := by
  apply Filtration.ext
  funext k
  change MeasurableSpace.comap (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k)
      (MeasurableSpace.pi : MeasurableSpace (Fin (k + 1) → ℝ)) =
    ⨆ j ≤ k, MeasurableSpace.comap (fun x : ScoreProfile n ↦ scoreWalkClock x j) inferInstance
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def, scoreWalkClockHistory]
  refine le_antisymm (iSup_le fun j ↦ ?_) (iSup₂_le fun j hj ↦ ?_)
  · exact le_iSup₂_of_le j (Nat.le_of_lt_succ j.isLt) le_rfl
  · exact le_iSup_of_le ⟨j, Nat.lt_succ_of_le hj⟩ le_rfl

theorem stronglyAdapted_scoreWalkClock (n : ℕ) :
    StronglyAdapted (scoreWalkClockFiltration n) (fun k x ↦ scoreWalkClock x k) := by
  intro k
  exact ((measurable_pi_apply (Fin.last k)).comp
    (comap_measurable (fun x : ScoreProfile n ↦ scoreWalkClockHistory x k))).stronglyMeasurable

/-- A test event from the past cannot distinguish two equal clock histories. -/
theorem mem_iff_of_scoreWalkClock_history_eq {A : Set (ScoreProfile n)} {x y : ScoreProfile n}
    {k : ℕ} (hA : MeasurableSet[scoreWalkClockFiltration n k] A)
    (hxy : ∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j) : x ∈ A ↔ y ∈ A := by
  obtain ⟨B, _, rfl⟩ := hA
  change scoreWalkClockHistory x k ∈ B ↔ scoreWalkClockHistory y k ∈ B
  rw [show scoreWalkClockHistory x k = scoreWalkClockHistory y k from
    funext fun j ↦ hxy j (Nat.le_of_lt_succ j.isLt)]

end LennonPittelFormalization

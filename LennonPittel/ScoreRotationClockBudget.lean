module

public import LennonPittel.ScoreRotationHistory

/-!
# The finite selection partition and pathwise clock budget

At each round the current matching and selected rotation index finitely
many disjoint branches. The complement contains the stopped states and the
null exceptional score arrays. The sum of active branch lengths is exactly
the participation of the padded walk.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators Classical Function

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The selected cycle at a padded checkpoint, if the walk can continue. -/
noncomputable def scoreWalkNextCycle (x : ScoreProfile n) (k : ℕ) :
    Option (Equiv.Perm (Fin n)) :=
  let start := DAState.matching (profileOfScores x)
  chooseQueriedRotation (scoreRotationGraph x (scoreRotationWalk x k start).2)

/-- The number of pairs moved in a round of the padded walk. -/
noncomputable def scoreWalkStepLength (x : ScoreProfile n) (k : ℕ) : ℕ :=
  (scoreWalkNextCycle x k).elim 0 fun ρ ↦ ρ.support.card

/-- The increment of the centered participation clock. -/
noncomputable def scoreWalkIncrement (x : ScoreProfile n) (k : ℕ) : ℝ :=
  scoreWalkClock x (k + 1) - scoreWalkClock x k

/-- Active branches record a matching and a cycle; the last branch is their complement. -/
def scoreWalkSelectionPartition (k : ℕ) :
    Option (Matching n × Equiv.Perm (Fin n)) → Set (ScoreProfile n)
  | none => (⋃ b : Matching n × Equiv.Perm (Fin n), scoreRotationBranch k b.1 b.2)ᶜ
  | some b => scoreRotationBranch k b.1 b.2

theorem measurableSet_scoreWalkSelectionPartition (k : ℕ)
    (b : Option (Matching n × Equiv.Perm (Fin n))) :
    MeasurableSet (scoreWalkSelectionPartition k b) := by
  cases b with
  | none => exact (MeasurableSet.iUnion fun b : Matching n × Equiv.Perm (Fin n) ↦
      measurableSet_scoreRotationBranch k b.1 b.2).compl
  | some b => exact measurableSet_scoreRotationBranch k b.1 b.2

theorem pairwise_disjoint_scoreWalkSelectionPartition (k : ℕ) :
    Pairwise (Disjoint on (@scoreWalkSelectionPartition n k)) := by
  intro a b hab
  change Disjoint (scoreWalkSelectionPartition k a) (scoreWalkSelectionPartition k b)
  rw [Set.disjoint_left]
  intro x ha hb
  cases a with
  | none =>
    cases b with
    | none => exact hab rfl
    | some b => exact ha (Set.mem_iUnion.mpr ⟨b, hb⟩)
  | some a =>
    cases b with
    | none => exact hb (Set.mem_iUnion.mpr ⟨a, ha⟩)
    | some b =>
      have ha' : x ∈ scoreRotationBranch k a.1 a.2 := ha
      have hb' : x ∈ scoreRotationBranch k b.1 b.2 := hb
      have he : a.1 = b.1 := ha'.2.1.symm.trans hb'.2.1
      have hsecond : a.2 = b.2 := Option.some.inj (ha'.2.2.symm.trans
        ((congrArg (fun ν ↦ chooseQueriedRotation (scoreRotationGraph x ν)) he).trans hb'.2.2))
      exact hab (congrArg some (Prod.ext he hsecond))

theorem iUnion_scoreWalkSelectionPartition (k : ℕ) :
    (⋃ b, @scoreWalkSelectionPartition n k b) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  by_cases h : x ∈ ⋃ b : Matching n × Equiv.Perm (Fin n), scoreRotationBranch k b.1 b.2
  · obtain ⟨b, hb⟩ := mem_iUnion.mp h
    exact ⟨some b, hb⟩
  · exact ⟨none, h⟩

theorem scoreWalkNextCycle_of_mem_branch {x : ScoreProfile n} {k : ℕ} {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hx : x ∈ scoreRotationBranch k μ ρ) :
    scoreWalkNextCycle x k = some ρ := by
  unfold scoreWalkNextCycle
  dsimp only
  rw [hx.2.1]
  exact hx.2.2

theorem scoreWalkNextCycle_eq_none_of_mem_stopped {x : ScoreProfile n} {k : ℕ}
    (hg : x ∈ goodClockInput n) (hx : x ∈ scoreWalkSelectionPartition k none) :
    scoreWalkNextCycle x k = none := by
  cases h : scoreWalkNextCycle x k with
  | none => rfl
  | some ρ =>
    exfalso
    apply hx
    let μ := (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
    exact mem_iUnion.mpr ⟨(μ, ρ), hg, rfl, h⟩

theorem scoreWalkIncrement_ae_eq_zero_on_stopped (k : ℕ) :
    (fun x ↦ scoreWalkIncrement x k) =ᵐ[(continuousScoreLaw n).restrict
      (scoreWalkSelectionPartition k none)] 0 := by
  filter_upwards [ae_restrict_mem (measurableSet_scoreWalkSelectionPartition (n := n) k none),
    ae_restrict_of_ae (ae_goodClockInput n)] with x hx hg
  have h := scoreWalkNextCycle_eq_none_of_mem_stopped hg hx
  have hs := scoreWalkClock_succ_sub x k (fun j i ↦ (hg.2 (.inr j) i).1)
  change scoreWalkIncrement x k = (match scoreWalkNextCycle x k with
    | none => 0
    | some ρ => _) at hs
  simpa only [h, Pi.zero_apply] using hs

/-- The branchwise constant length is measurable without exposing any selected magnitude. -/
noncomputable def scoreWalkMeasurableLength (x : ScoreProfile n) (k : ℕ) : ℝ :=
  ∑ b : Matching n × Equiv.Perm (Fin n),
    (scoreRotationBranch k b.1 b.2).indicator (fun _ ↦ (b.2.support.card : ℝ)) x

theorem measurable_scoreWalkMeasurableLength (k : ℕ) :
    Measurable (fun x : ScoreProfile n ↦ scoreWalkMeasurableLength x k) :=
  Finset.measurable_sum _ fun b _ ↦
    measurable_const.indicator (measurableSet_scoreRotationBranch k b.1 b.2)

theorem scoreWalkMeasurableLength_of_mem_branch {x : ScoreProfile n} {k : ℕ} {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hx : x ∈ scoreRotationBranch k μ ρ) :
    scoreWalkMeasurableLength x k = (ρ.support.card : ℝ) := by
  unfold scoreWalkMeasurableLength
  rw [Finset.sum_eq_single (μ, ρ)]
  · exact indicator_of_mem hx _
  · intro b _ hb
    apply indicator_of_notMem
    intro h
    exact Set.disjoint_left.mp
      (pairwise_disjoint_scoreWalkSelectionPartition (n := n) k
        (show some b ≠ some (μ, ρ) from fun e ↦ hb (Option.some.inj e))) h hx
  · simp

theorem scoreWalkMeasurableLength_of_mem_stopped {x : ScoreProfile n} {k : ℕ}
    (hx : x ∈ scoreWalkSelectionPartition k none) : scoreWalkMeasurableLength x k = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  exact indicator_of_notMem (fun hb ↦ hx (mem_iUnion.mpr ⟨b, hb⟩)) _

theorem scoreWalkMeasurableLength_eq_stepLength {x : ScoreProfile n} {k : ℕ}
    (hg : x ∈ goodClockInput n) :
    scoreWalkMeasurableLength x k = (scoreWalkStepLength x k : ℝ) := by
  obtain ⟨b, hb⟩ := mem_iUnion.mp
    (show x ∈ ⋃ b, @scoreWalkSelectionPartition n k b from by
      rw [iUnion_scoreWalkSelectionPartition]; exact mem_univ _)
  cases b with
  | none =>
    rw [scoreWalkMeasurableLength_of_mem_stopped hb, scoreWalkStepLength,
      scoreWalkNextCycle_eq_none_of_mem_stopped hg hb]
    exact Nat.cast_zero.symm
  | some b =>
    obtain ⟨μ, ρ⟩ := b
    have hb' : x ∈ scoreRotationBranch k μ ρ := hb
    rw [scoreWalkMeasurableLength_of_mem_branch hb', scoreWalkStepLength,
      scoreWalkNextCycle_of_mem_branch hb']
    rfl

/-- The participation of a prefix equals the sum of its padded step lengths. -/
theorem sum_scoreWalkStepLength_eq_rotationParticipation (x : ScoreProfile n) (N : ℕ) :
    (∑ k ∈ Finset.range N, scoreWalkStepLength x k) =
      rotationParticipation (scoreRotationWalk x N (DAState.matching (profileOfScores x))).1 := by
  let start := DAState.matching (profileOfScores x)
  induction N with
  | zero => simp [scoreRotationWalk, rotationParticipation]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, scoreRotationWalk_add x k 1 start]
    let out := scoreRotationWalk x k start
    change rotationParticipation out.1 + scoreWalkStepLength x k =
      rotationParticipation (out.1 ++ (scoreRotationWalk x 1 out.2).1)
    rw [scoreRotationWalk]
    cases h : scoreWalkNextCycle x k with
    | none =>
      have h' : chooseQueriedRotation (scoreRotationGraph x out.2) = none := h
      simp [scoreWalkStepLength, h, h']
    | some ρ =>
      have h' : chooseQueriedRotation (scoreRotationGraph x out.2) = some ρ := h
      simp [scoreWalkStepLength, h, h', scoreRotationWalk, rotationParticipation]

/-- The total expected-energy budget comes from a deterministic rank bound. -/
theorem ae_sum_scoreWalkMeasurableLength_le (n N : ℕ) :
    ∀ᵐ x ∂continuousScoreLaw n, ∑ k ∈ Finset.range N, scoreWalkMeasurableLength x k ≤
      (n * (n - 1) : ℕ) := by
  filter_upwards [ae_goodClockInput n] with x hg
  have h := (scoreRotationWalk_legal x hg.1 N
    (DAState.isManOptimal_matching (profileOfScores x)).1).participation_le
  simp_rw [scoreWalkMeasurableLength_eq_stepLength hg]
  rw [← Nat.cast_sum, sum_scoreWalkStepLength_eq_rotationParticipation]
  exact_mod_cast h

end LennonPittelFormalization

module

public import LennonPittel.ScoreRotationBranchLaw

/-!
# The clock history is constant on each passing fiber

At a given selection checkpoint, the whole preceding clock history is
unchanged if the selected coordinates are replaced below their current
thresholds. This is the deterministic condition needed for test events
in the natural filtration of the centered clock.
-/

@[expose] public section

open StableMarriage
open scoped Classical

namespace LennonPittelFormalization

variable {n : ℕ}

private theorem scoreRotationWalk_eq_nil_of_acyclic (x : ScoreProfile n) (μ : Matching n)
    (h : chooseQueriedRotation (scoreRotationGraph x μ) = none) (k : ℕ) :
    scoreRotationWalk x k μ = ([], μ) := by
  cases k with
  | zero => rfl
  | succ k => rw [scoreRotationWalk, h]

/-- Concatenating two runs is the run with their combined fuel. -/
theorem scoreRotationWalk_add (x : ScoreProfile n) (j k : ℕ) (ν : Matching n) :
    scoreRotationWalk x (j + k) ν =
      let a := scoreRotationWalk x j ν
      let b := scoreRotationWalk x k a.2
      (a.1 ++ b.1, b.2) := by
  induction j generalizing ν with
  | zero => simp only [Nat.zero_add, scoreRotationWalk, List.nil_append, Prod.eta]
  | succ j ih =>
    rw [Nat.succ_add, scoreRotationWalk, scoreRotationWalk]
    cases hc : chooseQueriedRotation (scoreRotationGraph x ν) with
    | none => simp only [scoreRotationWalk_eq_nil_of_acyclic x ν hc, List.nil_append]
    | some ρ =>
      change (ρ :: (scoreRotationWalk x (j + k) (eliminateRotation ν ρ)).1,
        (scoreRotationWalk x (j + k) (eliminateRotation ν ρ)).2) = _
      rw [ih]
      rfl

/-- The centered clock value at a padded checkpoint. -/
noncomputable def scoreWalkClock (x : ScoreProfile n) (k : ℕ) : ℝ :=
  let start := DAState.matching (profileOfScores x)
  let out := scoreRotationWalk x k start
  femaleLogPotential x out.2 - femaleLogPotential x start - (rotationParticipation out.1 : ℝ)

/-- The actual clock increment is the selected-cell sum, or zero after the walk stops. -/
theorem scoreWalkClock_succ_sub (x : ScoreProfile n) (k : ℕ)
    (hx : ∀ j i, 0 < x (.inr j) i) :
    let μ := (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
    scoreWalkClock x (k + 1) - scoreWalkClock x k =
      match chooseQueriedRotation (scoreRotationGraph x μ) with
      | none => 0
      | some ρ => centeredCacheLogIncrement (rotationClockUpper μ ρ)
          (splitRotationClockCells μ ρ x) := by
  let start := DAState.matching (profileOfScores x)
  let out := scoreRotationWalk x k start
  let μ := out.2
  change scoreWalkClock x (k + 1) - scoreWalkClock x k = _
  unfold scoreWalkClock
  change femaleLogPotential x (scoreRotationWalk x (k + 1) start).2 -
      femaleLogPotential x start - (rotationParticipation (scoreRotationWalk x (k + 1) start).1 :
      ℝ) - (femaleLogPotential x μ - femaleLogPotential x start -
      (rotationParticipation out.1 : ℝ)) = _
  rw [scoreRotationWalk_add x k 1 start]
  change (let b := scoreRotationWalk x 1 μ
    femaleLogPotential x b.2 - femaleLogPotential x start -
      (rotationParticipation (out.1 ++ b.1) : ℝ)) -
      (femaleLogPotential x μ - femaleLogPotential x start -
        (rotationParticipation out.1 : ℝ)) =
    match chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => 0
    | some ρ => centeredCacheLogIncrement (rotationClockUpper μ ρ)
        (splitRotationClockCells μ ρ x)
  rw [scoreRotationWalk]
  cases h : chooseQueriedRotation (scoreRotationGraph x μ) with
  | none => simp only [List.append_nil, sub_self]
  | some ρ =>
    have hpart : rotationParticipation (out.1 ++ [ρ]) =
        rotationParticipation out.1 + ρ.support.card := by
      simp [rotationParticipation]
    change femaleLogPotential x (eliminateRotation μ ρ) - femaleLogPotential x start -
      (rotationParticipation (out.1 ++ [ρ]) : ℝ) -
        (femaleLogPotential x μ - femaleLogPotential x start -
          (rotationParticipation out.1 : ℝ)) =
      centeredCacheLogIncrement (rotationClockUpper μ ρ) (splitRotationClockCells μ ρ x)
    rw [hpart, Nat.cast_add, centeredCacheLogIncrement_splitRotationClockCells x μ ρ hx]
    ring

/-- Replacing the next selected scores within the passing box leaves all past
centered clock values fixed. -/
theorem scoreWalkClock_history_eq_of_replace_selected {x y : ScoreProfile n} (k : ℕ)
    (hx : ∀ j, Function.Injective (x (.inr j))) (hy : ∀ j, Function.Injective (y (.inr j)))
    {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation (profileOfScores x)
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 ρ (r, i) →
      y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support,
      let μ := (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2
      y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    ∀ j ≤ k, scoreWalkClock y j = scoreWalkClock x j := by
  let start := DAState.matching (profileOfScores x)
  have hstart : IsStable (profileOfScores x) start :=
    (DAState.isManOptimal_matching (profileOfScores x)).1
  have hp := scoreRotationWalk_legal x hx k hstart
  have hda := da_matching_eq_of_replace_selected hp hρ hx hy hfixed
  have hpaths := scoreRotationWalk_eq_at_every_prefix k hx hstart hρ hfixed hbelow
  have hpotential (j : ℕ) (hj : j ≤ k) :
      femaleLogPotential y (scoreRotationWalk x j start).2 =
        femaleLogPotential x (scoreRotationWalk x j start).2 := by
    let prev := (scoreRotationWalk x j start).2
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    have heq : (scoreRotationWalk x k start).2 = (scoreRotationWalk x d prev).2 := by
      rw [hd, scoreRotationWalk_add]
    have hseg : RotationSequence (profileOfScores x) prev (scoreRotationWalk x d prev).1
        (scoreRotationWalk x k start).2 :=
      heq ▸ scoreRotationWalk_legal x hx d (scoreRotationWalk_legal x hx j hstart).isStable_end
    unfold femaleLogPotential
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg (fun z : ℝ ↦ -Real.log z)
    apply hfixed
    intro ⟨m, hm, he⟩
    apply hseg.rotationClockCell_ne_old_spouse hρ hm (prev.symm w)
    rw [Equiv.apply_symm_apply]
    exact he
  intro j hj
  unfold scoreWalkClock
  rw [hda]
  change femaleLogPotential y (scoreRotationWalk y j start).2 - femaleLogPotential y start -
      (rotationParticipation (scoreRotationWalk y j start).1 : ℝ) =
    femaleLogPotential x (scoreRotationWalk x j start).2 - femaleLogPotential x start -
      (rotationParticipation (scoreRotationWalk x j start).1 : ℝ)
  have hzero := hpotential 0 (Nat.zero_le k)
  change femaleLogPotential y start = femaleLogPotential x start at hzero
  rw [hpaths j hj, hpotential j hj, hzero]

end LennonPittelFormalization

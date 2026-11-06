module

public import LennonPittel.PivotForwardRevealRectangle

/-!
# Reading the forward pivot increments from the reveal

When a fixed cycle is exposed, its successor cells are active. Their male
scores, and hence the increments used in the compatibility rectangles,
are functions of the revealed male observations and the spouse scores.
-/

@[expose] public section

open MeasureTheory Set StableMarriage

namespace LennonPittelFormalization

/-- The male increment of a fixed forward arc, read from the active score
if the candidate is both off-diagonal and active. -/
noncomputable def forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n)
    (a : ForwardRevealedMaleScores flag) (m : Fin n) : ℝ :=
  if hm : ρ m ≠ m then
    let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    if hq : flag q = true then a ⟨q, hq⟩ - (diagonalPairAt d m).1 else 0
  else 0

theorem measurable_forwardPivotIncrement {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (m : Fin n) :
    Measurable (fun a ↦ forwardPivotIncrement d flag ρ a m) := by
  by_cases hm : ρ m ≠ m
  · let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    by_cases hq : flag q = true
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
      have he : Measurable (fun a : ForwardRevealedMaleScores flag ↦ a ⟨q, hq⟩) :=
        measurable_pi_apply _
      simpa only [forwardPivotIncrement, dite_eq_left hm, dite_eq_left hq'] using
        he.sub_const (diagonalPairAt d m).1
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) ≠ true := hq
      simp only [forwardPivotIncrement, dite_eq_left hm, dite_eq_right hq']
      exact measurable_const
  · simp only [forwardPivotIncrement, dite_eq_right hm]
    exact measurable_const

/-- On the actual fixed mask and an exposed pivot, the readout is exactly
the difference between the old and new male spouse scores. -/
theorem forwardPivotIncrement_eq_of_exposed {n : ℕ} (μ ρ : Matching n)
    (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ) {m : Fin n} (hm : ρ m ≠ m) :
    forwardPivotIncrement (splitScorePairs μ x).1 flag ρ
      (forwardRevealWithColumns flag (splitScorePairs μ x).2).1 m =
      x (.inl m) (μ (ρ m)) - x (.inl m) (μ m) := by
  let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
  have hmale : x (.inl m) (μ m) < x (.inl m) (μ (ρ m)) :=
    (rankPermutation_lt_iff (ht (.inl m)) _ _).mp (hρ.successor m hm).eligible.1
  have hfemale : x (.inr (μ (ρ m))) m < x (.inr (μ (ρ m))) (ρ m) :=
    (rankPermutation_lt_iff (ht (.inr (μ (ρ m)))) _ _).mp
      (by simpa only [profileOfScores, Equiv.symm_apply_apply] using (hρ.successor m hm).eligible.2)
  have hq : flag q = true := by
    by_contra h
    have hh := mem_pi.mp hmask q (mem_univ _)
    change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ x).1 m).1
      (diagonalPairAt (splitScorePairs μ x).1 (ρ m)).2 (flag q) at hh
    rw [forwardScoreCellFlagEvent, ite_eq_right h, mem_compl_iff, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs] at hh
    exact hh ⟨hmale, hfemale⟩
  have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
  simp only [forwardPivotIncrement, dite_eq_left hm, dite_eq_left hq']
  change ((splitScorePairs μ x).2 q).1 - (diagonalPairAt (splitScorePairs μ x).1 m).1 = _
  rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs]

end LennonPittelFormalization

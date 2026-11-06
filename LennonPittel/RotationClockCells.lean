module

public import LennonPittel.RotationParticipationClock

/-!
# Which score coordinates the participation clock reads

Each moved man contributes one distinct newly matched female score. Before
elimination, this score could have passed earlier comparisons, but could not
have been read as a previous spouse score or failed an earlier comparison.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ ν : Matching n}
variable {ρ : Equiv.Perm (Fin n)}

/-- The female score coordinate to be revealed for a moved man. -/
def rotationClockCell (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    (Fin n ⊕ Fin n) × Fin n :=
  (.inr (eliminateRotation μ ρ m), m)

/-- Different men in a rotation reveal different coordinates. -/
theorem rotationClockCell_injective (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    Function.Injective (rotationClockCell μ ρ) :=
  fun _ _ h ↦ congrArg Prod.snd h

/-- The new score of the wife assigned to a man is exactly the selected coordinate. -/
theorem femaleSpouseScore_eliminate_apply (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    femaleSpouseScore x (eliminateRotation μ ρ) (eliminateRotation μ ρ m) =
      x (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 := by
  simp only [femaleSpouseScore, Equiv.symm_apply_apply, rotationClockCell]

/-- Any score already read from a partner or an earlier proposal is excluded:
the new partner is strictly later in the moved man's list. -/
theorem IsExposedRotation.new_partner_ne_of_rank_le (hρ : IsExposedRotation p μ ρ)
    {m w : Fin n} (hm : m ∈ ρ.support)
    (hw : p.manRank m w ≤ p.manRank m (μ m)) :
    eliminateRotation μ ρ m ≠ w :=
  fun h ↦ (not_lt_of_ge hw)
    (h ▸ hρ.manRank_lt_eliminate_of_moved (Equiv.Perm.mem_support.mp hm))

/-- A selected score does not repeat a spouse score already read along the path. -/
theorem RotationSequence.rotationClockCell_ne_old_spouse {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p ν rs μ) (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : m ∈ ρ.support) (a : Fin n) :
    rotationClockCell μ ρ m ≠ (.inr (ν a), a) := by
  intro heq
  have ha : m = a := congrArg Prod.snd heq
  subst a
  exact hρ.new_partner_ne_of_rank_le hm (h.menWeaklyPrefer m)
    (Sum.inr.inj (congrArg Prod.fst heq))

/-- A woman's spouse score weakly decreases along a path in the score model. -/
theorem RotationSequence.femaleSpouseScore_end_le_start
    {x : ScoreProfile n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence (profileOfScores x) ν rs μ)
    (ht : ∀ j, Function.Injective (x (.inr j))) (j : Fin n) :
    femaleSpouseScore x μ j ≤ femaleSpouseScore x ν j := by
  induction h with
  | nil => exact le_rfl
  | cons _ hρ _ ih => exact ih.trans (femaleSpouseScore_eliminate_le x hρ ht j)

/-- A moved woman's new score passes its current threshold strictly. -/
theorem IsExposedRotation.rotationClockCell_score_lt {x : ScoreProfile n}
    (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {m : Fin n} (hm : m ∈ ρ.support) :
    x (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
      femaleSpouseScore x μ (eliminateRotation μ ρ m) := by
  have h := (hρ.successor m (Equiv.Perm.mem_support.mp hm)).eligible.2
  exact (rankPermutation_lt_iff (ht _) _ _).mp h

/-- The current passing comparison entails every previous comparison at the
same coordinate: older spouse thresholds are at least the current one. -/
theorem RotationSequence.rotationClockCell_score_lt_old_threshold
    {x : ScoreProfile n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence (profileOfScores x) ν rs μ)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {m : Fin n} (hm : m ∈ ρ.support) :
    x (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
      femaleSpouseScore x ν (eliminateRotation μ ρ m) :=
  (hρ.rotationClockCell_score_lt ht hm).trans_le
    (h.femaleSpouseScore_end_le_start ht (eliminateRotation μ ρ m))

end LennonPittelFormalization

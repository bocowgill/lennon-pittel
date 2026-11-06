module

public import LennonPittel.CoexposedRotations

/-!
# Co-exposed rotations give a lower bound on the stable-matching tail

The co-exposure event is contained in the event that the stable-matching
count reaches the corresponding power-of-two threshold.
-/

@[expose] public section

open StableMarriage MeasureTheory

namespace LennonPittelFormalization

/-- Some stable matching for `p) has at least `k` distinct exposed rotations. -/
def HasCoexposedRotations {n : ℕ} (p : Profile n) (k : ℕ) : Prop :=
  ∃ μ : Matching n, IsStable p μ ∧
    ∃ A : Finset (Equiv.Perm (Fin n)), k ≤ A.card ∧ ∀ ρ ∈ A, IsExposedRotation p μ ρ

/-- A co-exposure witness implies the power-of-two lower bound for its profile. -/
theorem HasCoexposedRotations.pow_le_numStableMatchings {n k : ℕ} {p : Profile n}
    (hp : HasCoexposedRotations p k) : 2 ^ k ≤ numStableMatchings p :=
  let ⟨_, hμ, A, hk, hA⟩ := hp
  (Nat.pow_le_pow_right (by decide) hk).trans
    (pow_card_exposedRotations_le_numStableMatchings hμ A hA)

/-- The co-exposure event is contained in the stable-matching upper-tail event. -/
theorem setOf_hasCoexposedRotations_subset_setOf_numStableMatchings (n k : ℕ) :
    {p : Profile n | HasCoexposedRotations p k} ⊆ {p | 2 ^ k ≤ numStableMatchings p} :=
  fun _ hp ↦ HasCoexposedRotations.pow_le_numStableMatchings hp

/-- The tail comparison holds for any measure on preference profiles. -/
theorem measure_hasCoexposedRotations_le_measure_numStableMatchings {n : ℕ}
    (ν : Measure (Profile n)) (k : ℕ) :
    ν {p | HasCoexposedRotations p k} ≤ ν {p | 2 ^ k ≤ numStableMatchings p} :=
  measure_mono (setOf_hasCoexposedRotations_subset_setOf_numStableMatchings n k)

/-- Under the uniform profile law, the co-exposure probability bounds the stable-matching tail
from below. -/
theorem uniformProfile_hasCoexposedRotations_le_numStableMatchings_tail (n k : ℕ) :
    (uniformProfile n).toMeasure {p | HasCoexposedRotations p k} ≤
      (uniformProfile n).toMeasure {p | 2 ^ k ≤ numStableMatchings p} :=
  measure_hasCoexposedRotations_le_measure_numStableMatchings (uniformProfile n).toMeasure k

end LennonPittelFormalization

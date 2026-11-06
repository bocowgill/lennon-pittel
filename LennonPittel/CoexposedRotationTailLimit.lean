module

public import LennonPittel.CoexposedRotationProbability
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A co-exposure criterion for the Lennon–Pittel tail limit

If co-exposure of `k n` rotations has probability tending to one and the
power-of-two lower bound eventually reaches the desired threshold, then the
Lennon–Pittel tail probability tends to one.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped Topology

namespace LennonPittelFormalization

/-- A power-of-two threshold that dominates a real threshold transfers the co-exposure bound. -/
theorem uniformProfile_hasCoexposedRotations_le_realTail {n k : ℕ} {t : ℝ}
    (ht : t ≤ (2 : ℝ) ^ k) :
    (uniformProfile n).toMeasure {p | HasCoexposedRotations p k} ≤
      (uniformProfile n).toMeasure {p | t ≤ (numStableMatchings p : ℝ)} := by
  refine (uniformProfile_hasCoexposedRotations_le_numStableMatchings_tail n k).trans
    (measure_mono fun p hp ↦ ?_)
  have hcount : 2 ^ k ≤ numStableMatchings p := hp
  exact ht.trans (by exact_mod_cast hcount)

/-- High-probability co-exposure and eventual threshold domination imply the
Lennon–Pittel tail limit. -/
theorem tendsto_lennonPittelTail_of_coexposedRotations (ε : ℕ → ℝ) (k : ℕ → ℕ)
    (hcoexposed : Tendsto
      (fun n ↦ (uniformProfile n).toMeasure {p | HasCoexposedRotations p (k n)})
      atTop (𝓝 1))
    (hthreshold : ∀ᶠ n in atTop,
      ε n * expectedNumStableMatchings n ≤ (2 : ℝ) ^ (k n)) :
    Tendsto
      (fun n ↦ (uniformProfile n).toMeasure
        {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) :=
  hcoexposed.squeeze' tendsto_const_nhds
    (hthreshold.mono fun _ hn ↦ uniformProfile_hasCoexposedRotations_le_realTail hn)
    (Eventually.of_forall fun _ ↦ prob_le_one)

end LennonPittelFormalization

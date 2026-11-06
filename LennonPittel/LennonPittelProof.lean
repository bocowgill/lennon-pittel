module

public import LennonPittel.PivotPairEnvelopeBounds

/-!
# The Lennon–Pittel lower tail

We keep the abundance parameters fixed while tuning the short-cycle
cutoff. This keeps the positive lower scale independent of the requested
variance error.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- The stable-count tail tends to one at every threshold vanishing relative
to the mean. The threshold need not be positive or monotone. -/
theorem lennonPittel_lowerTail (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n}) atTop (𝓝 1) := by
  apply lennonPittel_of_tunable_pivot_pair_bounds _ ε hε
  intro b A B κ hb _ _ _ hκ hκb _ _ e he
  obtain ⟨α, hα, hα', henv⟩ := eventually_pairEnvelopes_le (Real.exp_pos 72) hb he
  refine ⟨pivotShortCycleCutoff α, tendsto_pivotShortCycleCutoff hα, ?_⟩
  filter_upwards [henv, eventually_pivotPairIntegrals_le_envelopes
    (A := A) (B := B) hb hκ hκb hα hα'] with n htarget hpairs
  exact ⟨hpairs.1.trans htarget.1, hpairs.2.trans htarget.2⟩

/-- The exact statement in the Formal Conjectures repository. -/
theorem lennon_pittel_conjecture_verified
    (ε : ℕ → ℝ) (_hε_pos : ∀ n, 0 < ε n) (_hε_antitone : Antitone ε)
    (hε_tendsto : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ (StableMarriage.uniformProfile n).toMeasure
      {p | (StableMarriage.numStableMatchings p : ℝ) ≥
        ε n * StableMarriage.expectedNumStableMatchings n}) atTop (𝓝 1) :=
  lennonPittel_lowerTail ε hε_tendsto

end LennonPittelFormalization

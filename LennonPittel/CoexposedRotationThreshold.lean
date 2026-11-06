module

public import LennonPittel.CoexposedRotationTailLimit
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Nat.Find

/-!
# The least co-exposure threshold for the Lennon–Pittel reduction

The least exponent whose power of two reaches the target removes the
threshold hypothesis from the conditional tail theorem. Among exponents
that meet the threshold, it asks for the fewest co-exposed rotations.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped Topology

namespace LennonPittelFormalization

/-- Powers of two eventually reach any real threshold. -/
theorem exists_le_two_pow (t : ℝ) : ∃ k : ℕ, t ≤ (2 : ℝ) ^ k :=
  (pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 2)).imp fun _ h ↦ h.le

open Classical in
/-- The least natural exponent whose power of two is at least `t`. -/
noncomputable def leastTwoPowExponent (t : ℝ) : ℕ :=
  Nat.find (exists_le_two_pow t)

/-- The least exponent reaches the target. -/
theorem le_two_pow_leastTwoPowExponent (t : ℝ) :
    t ≤ (2 : ℝ) ^ leastTwoPowExponent t :=
  Nat.find_spec (exists_le_two_pow t)

/-- No exponent that reaches the target is smaller than the least one. -/
theorem leastTwoPowExponent_le {t : ℝ} {k : ℕ} (hk : t ≤ (2 : ℝ) ^ k) :
    leastTwoPowExponent t ≤ k :=
  Nat.find_min' (exists_le_two_pow t) hk

/-- An exponent is at least the least one exactly when its power reaches the target. -/
theorem leastTwoPowExponent_le_iff {t : ℝ} {k : ℕ} :
    leastTwoPowExponent t ≤ k ↔ t ≤ (2 : ℝ) ^ k :=
  ⟨fun h ↦ (le_two_pow_leastTwoPowExponent t).trans
    (pow_le_pow_right₀ (by norm_num) h), leastTwoPowExponent_le⟩

/-- The least exponent is zero exactly for targets at most one. -/
theorem leastTwoPowExponent_eq_zero_iff {t : ℝ} :
    leastTwoPowExponent t = 0 ↔ t ≤ 1 := by
  rw [← Nat.le_zero, leastTwoPowExponent_le_iff, pow_zero]

/-- A positive least exponent brackets the target between successive powers of two. -/
theorem leastTwoPowExponent_eq_succ_iff {t : ℝ} {k : ℕ} :
    leastTwoPowExponent t = k + 1 ↔ (2 : ℝ) ^ k < t ∧ t ≤ (2 : ℝ) ^ (k + 1) := by
  rw [le_antisymm_iff, leastTwoPowExponent_le_iff, ← Nat.lt_iff_add_one_le, lt_iff_not_ge,
    leastTwoPowExponent_le_iff, not_le, and_comm]

/-- The least rotation count for which the power-of-two bound reaches the target at size `n`. -/
noncomputable def coexposedRotationThreshold (ε : ℕ → ℝ) (n : ℕ) : ℕ :=
  leastTwoPowExponent (ε n * expectedNumStableMatchings n)

/-- The canonical exponent meets the threshold at every index. -/
theorem coexposedRotationThreshold_spec (ε : ℕ → ℝ) (n : ℕ) :
    ε n * expectedNumStableMatchings n ≤ (2 : ℝ) ^ coexposedRotationThreshold ε n :=
  le_two_pow_leastTwoPowExponent _

/-- The canonical exponent is at most any exponent that meets the threshold. -/
theorem coexposedRotationThreshold_le (ε : ℕ → ℝ) (n : ℕ) {k : ℕ}
    (hk : ε n * expectedNumStableMatchings n ≤ (2 : ℝ) ^ k) :
    coexposedRotationThreshold ε n ≤ k :=
  leastTwoPowExponent_le hk

/-- A witness for a larger rotation count is also a witness for a smaller count. -/
theorem HasCoexposedRotations.of_le {n k l : ℕ} {p : Profile n}
    (hp : HasCoexposedRotations p l) (hkl : k ≤ l) : HasCoexposedRotations p k :=
  let ⟨μ, hμ, A, hl, hA⟩ := hp
  ⟨μ, hμ, A, hkl.trans hl, hA⟩

/-- The least exponent succeeds with high probability exactly when some exponent
sequence succeeds with high probability and eventually meets the threshold. -/
theorem tendsto_coexposedRotationThreshold_iff_exists (ε : ℕ → ℝ) :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | HasCoexposedRotations p (coexposedRotationThreshold ε n)}) atTop (𝓝 1) ↔
    ∃ k : ℕ → ℕ,
      Tendsto (fun n ↦ (uniformProfile n).toMeasure {p | HasCoexposedRotations p (k n)})
        atTop (𝓝 1) ∧
      ∀ᶠ n in atTop, ε n * expectedNumStableMatchings n ≤ (2 : ℝ) ^ (k n) := by
  constructor
  · intro h
    exact ⟨coexposedRotationThreshold ε, h, Eventually.of_forall
      (coexposedRotationThreshold_spec ε)⟩
  · rintro ⟨k, hk, hthreshold⟩
    refine hk.squeeze' tendsto_const_nhds ?_ (Eventually.of_forall fun _ ↦ prob_le_one)
    exact hthreshold.mono fun n hn ↦ measure_mono fun _ hp ↦
      HasCoexposedRotations.of_le hp (coexposedRotationThreshold_le ε n hn)

/-- For the least exponent, high-probability co-exposure alone implies the
Lennon–Pittel tail limit. -/
theorem tendsto_lennonPittelTail_of_coexposedRotationThreshold (ε : ℕ → ℝ)
    (hcoexposed : Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | HasCoexposedRotations p (coexposedRotationThreshold ε n)}) atTop (𝓝 1)) :
    Tendsto
      (fun n ↦ (uniformProfile n).toMeasure
        {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) :=
  tendsto_lennonPittelTail_of_coexposedRotations ε (coexposedRotationThreshold ε) hcoexposed
    (Eventually.of_forall (coexposedRotationThreshold_spec ε))

end LennonPittelFormalization

module

public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.NormNum

/-!
# Scalar lower bounds for the reverse cycle count

The ordered-label encoding ranges over derangements. Their uniform one-third
fraction combines with Bernoulli's inequality for a per-arc perturbation.
-/

@[expose] public section

open scoped ENNReal

namespace LennonPittelFormalization

private theorem factorial_le_three_mul_numDerangements (k : ℕ) :
    2 ≤ k → k.factorial ≤ 3 * numDerangements k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hsmall : k < 4
    · rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl <;> decide
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hn : 2 ≤ n := by omega
      have h₀ := ih n (by omega) hn
      have h₁ := ih (n + 1) (by omega) (by omega)
      rw [Nat.add_comm 2 n, numDerangements_add_two, Nat.factorial_succ, Nat.factorial_succ n]
      calc
        (n + 2) * ((n + 1) * n.factorial) =
            (n + 1) * (n.factorial + (n + 1) * n.factorial) := by ring
        _ ≤ (n + 1) * (3 * numDerangements n + 3 * numDerangements (n + 1)) :=
          Nat.mul_le_mul_left _ (add_le_add h₀ (Nat.factorial_succ n ▸ h₁))
        _ = 3 * ((n + 1) * (numDerangements n + numDerangements (n + 1))) := by ring

/-- At least one third of the permutations of two or more positions are derangements. -/
theorem factorial_le_three_mul_card_derangements {k : ℕ} (hk : 2 ≤ k) :
    k.factorial ≤ 3 * Fintype.card (derangements (Fin k)) := by
  rw [card_derangements_fin_eq_numDerangements]
  exact factorial_le_three_mul_numDerangements k hk

/-- The one-third derangement bound in extended nonnegative reals. -/
theorem factorial_div_three_le_card_derangements {k : ℕ} (hk : 2 ≤ k) :
    (k.factorial : ℝ≥0∞) / 3 ≤ Fintype.card (derangements (Fin k)) := by
  rw [ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm _ 3]
  exact_mod_cast factorial_le_three_mul_card_derangements hk

/-- A lower bound per position derangement retains one third after dividing by the
number of presentations of a labeled permutation. -/
theorem div_three_le_of_derangement_mul_le_factorial_mul {k : ℕ} (hk : 2 ≤ k)
    {L W : ℝ≥0∞}
    (hm : (Fintype.card (derangements (Fin k)) : ℝ≥0∞) * L ≤
      (k.factorial : ℝ≥0∞) * W) :
    L / 3 ≤ W := by
  have hfac : (k.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  apply (ENNReal.mul_le_mul_iff_right hfac (ENNReal.natCast_ne_top _)).mp
  calc
    (k.factorial : ℝ≥0∞) * (L / 3) = ((k.factorial : ℝ≥0∞) / 3) * L := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ (Fintype.card (derangements (Fin k)) : ℝ≥0∞) * L :=
      mul_le_mul_left (factorial_div_three_le_card_derangements hk) L
    _ ≤ (k.factorial : ℝ≥0∞) * W := hm

/-- Replacing each arc weight by a factor of `1 - δ` loses at most `k * δ` over `k` arcs. -/
theorem ofReal_one_sub_nat_mul_le_pow_one_sub (k : ℕ) {δ : ℝ} (hδ : δ ≤ 1) :
    ENNReal.ofReal (1 - (k : ℝ) * δ) ≤ ENNReal.ofReal (1 - δ) ^ k := by
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr hδ)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [sub_eq_add_neg, mul_neg] using
    one_add_mul_le_pow (a := -δ) (neg_le_neg (hδ.trans (by norm_num))) k

end LennonPittelFormalization

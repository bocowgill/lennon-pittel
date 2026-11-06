module

public import LennonPittel.PivotReverseMaskLowerMoment
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.ENNReal.Inv

/-!
# Upper bound for reverse collections of one support size

Ordering each support gives exactly one labeling for each order. The total
weight of the admissible labelings is at most the weight of all independent
draws, which is one for each position derangement.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The sum of label products over all permutations of one support size is
at most one when the label weights sum to one. -/
theorem sum_supportPermutation_weights_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (r : α → ℝ≥0∞) (hr : ∑ i, r i = 1) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm α)).filter (fun σ ↦ σ.support.card = k),
      ∏ i ∈ σ.support, r i) ≤ 1 := by
  classical
  have hfac : (k.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  apply (ENNReal.mul_le_mul_iff_right hfac (ENNReal.natCast_ne_top _)).mp
  rw [mul_one]
  calc
    _ = ∑ e : derangements (Fin k),
        ∑ x ∈ Finset.univ.filter
          (fun x ↦ x ∈ iidLabelGood (∅ : Set α) (fun _ ↦ ∅) e.val), ∏ i, r (x i) := by
      simpa using (sum_iidLabelGood_eq_factorial_mul_sum_support k r ∅ (fun _ ↦ ∅)).symm
    _ ≤ ∑ _e : derangements (Fin k), (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun e _ ↦ calc
        _ ≤ ∑ x : Fin k → α, ∏ i, r (x i) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 1 := by rw [← Fintype.prod_sum]; simp [hr]
    _ = (Fintype.card (derangements (Fin k)) : ℝ≥0∞) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
      have h := Fintype.card_subtype_le (fun e : Equiv.Perm (Fin k) ↦ e ∈ derangements (Fin k))
      rw [Fintype.card_perm, Fintype.card_fin] at h
      exact_mod_cast h

/-- Excluding pivot labels and masked-out arcs can only decrease the sum
of normalized support weights. -/
theorem goodReverseSupportPermutations_weight_le_one {n : ℕ}
    (k : ℕ) (r : Fin n → ℝ≥0∞) (hr : ∑ i, r i = 1)
    (A : Finset (Fin n)) (F : Fin n → Finset (Fin n)) :
    (∑ σ ∈ goodReverseSupportPermutations k A F, ∏ i ∈ σ.support, r i) ≤ 1 := by
  classical
  refine (Finset.sum_le_sum_of_subset ?_).trans (sum_supportPermutation_weights_le_one k r hr)
  intro σ hσ
  exact (Finset.mem_filter_univ σ).mpr (mem_goodReverseSupportPermutations.mp hσ).1

end LennonPittelFormalization

module

public import LennonPittel.ForestDeterministic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Forest probabilities for independent successor rows

The determinant is linear in each row separately. Averaging against a
finite product law therefore amounts to replacing each row by its mean.
Together with the pointwise determinant identity, this computes the
probability of having no directed cycle.
-/

@[expose] public section

open scoped BigOperators Classical

namespace LennonPittelFormalization

/-- Averaging independent rows commutes with taking the determinant. The weights
need not be nonnegative or normalized for this algebraic identity. -/
theorem sum_prod_mul_det_eq_det_rowSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (w : ∀ i, κ i → ℝ)
    (a : ∀ i, κ i → ι → ℝ) :
    (∑ x : ∀ i, κ i, (∏ i, w i (x i)) * (Matrix.of (fun i j ↦ a i (x i) j)).det) =
      (Matrix.of (fun i j ↦ ∑ k, w i k * a i k j)).det := by
  let sign (σ : Equiv.Perm ι) : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)
  calc
    _ = ∑ x : ∀ i, κ i, ∑ σ : Equiv.Perm ι,
        sign σ * ∏ i, w i (x i) * a i (x i) (σ i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.prod_mul_distrib]
      simp only [Matrix.transpose_apply, Matrix.of_apply, sign]
      ac_rfl
    _ = ∑ σ : Equiv.Perm ι, sign σ * ∏ i, ∑ k, w i k * a i k (σ i) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      exact congrArg (sign σ * ·) (Fintype.prod_sum (fun i k ↦ w i k * a i k (σ i))).symm
    _ = _ := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl

/-- The mean determinant of identity minus adjacency is the determinant formed
from the individual arc probabilities. -/
theorem sum_prod_mul_det_one_sub_successorAdjacency {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (hw : ∀ i, ∑ o, w i o = 1) :
    (∑ f : ι → Option ι, (∏ i, w i (f i)) * (1 - successorAdjacency f).det) =
      (1 - Matrix.of (fun i j ↦ w i (some j))).det := by
  let a (i : ι) (o : Option ι) (j : ι) : ℝ :=
    (1 : Matrix ι ι ℝ) i j - (if o = some j then 1 else 0)
  have hmatrix (f : ι → Option ι) :
      Matrix.of (fun i j ↦ a i (f i) j) = 1 - successorAdjacency f := by
    ext i j
    rfl
  have hmean :
      Matrix.of (fun i j ↦ ∑ o, w i o * a i o j) =
        1 - Matrix.of (fun i j ↦ w i (some j)) := by
    ext i j
    simp only [a, Matrix.sub_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw i, one_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  simpa only [hmatrix, hmean] using sum_prod_mul_det_eq_det_rowSum w a

/-- The mass of acyclic partial successor maps under independent row weights. -/
noncomputable def forestProductMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) : ℝ :=
  ∑ f : ι → Option ι, (∏ i, w i (f i)) * (if IsAcyclicSuccessor f then 1 else 0)

/-- The probability of acyclicity under normalized loopless independent row weights
is the determinant of identity minus the arc-probability matrix. -/
theorem forestProductMass_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (hw : ∀ i, ∑ o, w i o = 1)
    (hloop : ∀ i, w i (some i) = 0) :
    forestProductMass w = (1 - Matrix.of (fun i j ↦ w i (some j))).det := by
  unfold forestProductMass
  calc
    _ = ∑ f : ι → Option ι, (∏ i, w i (f i)) * (1 - successorAdjacency f).det := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : ∀ i, f i ≠ some i
      · rw [det_one_sub_successorAdjacency f hf]
      · push Not at hf
        obtain ⟨i, hi⟩ := hf
        have hz : ∏ i, w i (f i) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, hloop])
        simp only [hz, zero_mul]
    _ = _ := sum_prod_mul_det_one_sub_successorAdjacency w hw

end LennonPittelFormalization

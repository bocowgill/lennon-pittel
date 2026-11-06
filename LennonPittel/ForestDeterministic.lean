module

public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a loopless partial successor map

A realized directed cycle is a nontrivial cyclic permutation whose
successor arcs are present. For a loopless graph with at most one outgoing
arc per vertex, the determinant of identity minus adjacency detects
whether any such cycle is present.
-/

@[expose] public section

open scoped BigOperators Classical

namespace LennonPittelFormalization

/-- The permutation is a directed cycle realized by the partial successor map. -/
def RealizesDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  σ.IsCycle ∧ ∀ i ∈ σ.support, f i = some (σ i)

/-- No nontrivial directed cycle is realized by the partial successor map. -/
def IsAcyclicSuccessor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) : Prop :=
  ∀ σ : Equiv.Perm ι, ¬ RealizesDirectedCycle f σ

/-- The zero-one matrix of the present successor arcs, in row-to-column orientation. -/
noncomputable def successorAdjacency {ι : Type*} [DecidableEq ι]
    (f : ι → Option ι) : Matrix ι ι ℝ :=
  fun i j ↦ if f i = some j then 1 else 0

private theorem det_one_sub_successorAdjacency_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : ι → Option ι} {σ : Equiv.Perm ι}
    (h : RealizesDirectedCycle f σ) : (1 - successorAdjacency f).det = 0 := by
  refine Matrix.det_eq_zero_of_not_linearIndependent_rows fun hlin ↦ ?_
  obtain ⟨i, hi⟩ := h.1.nonempty_support
  have hsum (j : ι) : (∑ k ∈ σ.support, (1 - successorAdjacency f) k j) = 0 :=
    calc
      _ = ∑ k ∈ σ.support, ((if k = j then (1 : ℝ) else 0) - (if σ k = j then 1 else 0)) :=
        Finset.sum_congr rfl fun k hk ↦ by
          simp [Matrix.sub_apply, Matrix.one_apply, successorAdjacency, h.2 k hk]
      _ = 0 := by
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        exact (Finset.sum_equiv σ (fun k ↦ Equiv.Perm.apply_mem_support.symm)
          (fun _ _ ↦ rfl)).symm
  have hcomb : (∑ k ∈ σ.support, (1 : ℝ) • (1 - successorAdjacency f) k) = 0 :=
    funext fun j ↦ by
      simp only [one_smul, Pi.zero_apply]
      exact (Finset.sum_apply j σ.support (fun k ↦ (1 - successorAdjacency f) k)).trans (hsum j)
  exact one_ne_zero ((linearIndependent_iff'.mp hlin) σ.support (fun _ ↦ 1) hcomb i hi)

private theorem det_one_sub_successorAdjacency_eq_one {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : ι → Option ι}
    (hf : ∀ i, f i ≠ some i) (h : IsAcyclicSuccessor f) :
    (1 - successorAdjacency f).det = 1 := by
  classical
  let A := 1 - successorAdjacency f
  have hprod (σ : Equiv.Perm ι) (hne : σ ≠ 1) : (∏ i, A i (σ i)) = 0 := by
    obtain ⟨τ, hτ⟩ := Finset.nonempty_iff_ne_empty.mpr
      (fun he ↦ hne (Equiv.Perm.cycleFactorsFinset_eq_empty_iff.mp he))
    obtain ⟨hcyc, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hτ
    have hbad : ¬ ∀ i ∈ τ.support, f i = some (τ i) :=
      fun ha ↦ h τ ⟨hcyc, ha⟩
    obtain ⟨i, hi, hfi⟩ := (not_forall.mp hbad).imp fun _ ↦ Classical.not_imp.mp
    have hit : i ≠ τ i := (Equiv.Perm.mem_support.mp hi).symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      simp [A, Matrix.sub_apply, successorAdjacency, hit, ← heq i hi, hfi])
  calc
    A.det = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A i (σ i) := by
      simpa only [Matrix.transpose_apply] using
        (Matrix.det_transpose A).symm.trans (Matrix.det_apply A.transpose)
    _ = Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, A i i := by
      simpa only [Equiv.Perm.one_apply] using
        (Finset.sum_eq_single (1 : Equiv.Perm ι)
          (fun σ _ hne ↦ by rw [hprod σ hne, smul_zero])
          (fun hn ↦ (hn (Finset.mem_univ _)).elim) :
          (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A i (σ i)) = _)
    _ = 1 := by simp [A, Matrix.sub_apply, successorAdjacency, hf]

/-- The determinant of identity minus successor adjacency is the no-cycle indicator. -/
theorem det_one_sub_successorAdjacency {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (hf : ∀ i, f i ≠ some i) :
    (1 - successorAdjacency f).det = if IsAcyclicSuccessor f then 1 else 0 := by
  classical
  by_cases h : IsAcyclicSuccessor f
  · simpa only [ite_eq_left h] using det_one_sub_successorAdjacency_eq_one hf h
  · obtain ⟨σ, hσ⟩ := not_forall.mp h
    simpa only [ite_eq_right h] using det_one_sub_successorAdjacency_eq_zero (not_not.mp hσ)

end LennonPittelFormalization

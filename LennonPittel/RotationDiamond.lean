module

public import LennonPittel.ExposedRotations

/-!
# Local commutation of exposed rotations

Distinct rotations exposed at the same matching move disjoint sets of men. They stay exposed
after one another is eliminated, and the two orders of elimination give the same matching.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ σ : Equiv.Perm (Fin n)}

private theorem moved_image {f : Equiv.Perm (Fin n)} {i : Fin n} (hi : f i ≠ i) :
    f (f i) ≠ f i :=
  f.injective.ne hi

private theorem eq_of_common_moved (hρ : IsExposedRotation p μ ρ) (hσ : IsExposedRotation p μ σ)
    {m : Fin n} (hmρ : ρ m ≠ m) (hmσ : σ m ≠ m) : ρ = σ := by
  have hagree (i : Fin n) (hiρ : ρ i ≠ i) (hiσ : σ i ≠ i) : ρ i = σ i :=
    μ.injective ((hρ.successor i hiρ).unique (hσ.successor i hiσ))
  have horbit (k : ℕ) :
      (ρ ^ k) m = (σ ^ k) m ∧ ρ ((ρ ^ k) m) ≠ (ρ ^ k) m ∧ σ ((σ ^ k) m) ≠ (σ ^ k) m := by
    induction k with
    | zero => simpa using And.intro (rfl : m = m) (And.intro hmρ hmσ)
    | succ k ih =>
      obtain ⟨heq, hmoveρ, hmoveσ⟩ := ih
      have hmoveσ' : σ ((ρ ^ k) m) ≠ (ρ ^ k) m := heq ▸ hmoveσ
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hagree _ hmoveρ hmoveσ').trans (congrArg σ heq),
        moved_image hmoveρ, moved_image hmoveσ⟩
  apply Equiv.ext
  intro i
  by_cases hi : ρ i ≠ i
  · obtain ⟨k, hk⟩ := hρ.isCycle.exists_pow_eq hmρ hi
    have his : σ i ≠ i := by
      rw [← hk, (horbit k).1]
      exact (horbit k).2.2
    exact hagree i hi his
  · have his : σ i = i := by
      by_contra hsi
      obtain ⟨k, hk⟩ := hσ.isCycle.exists_pow_eq hmσ hsi
      apply hi
      rw [← hk, ← (horbit k).1]
      exact (horbit k).2.1
    exact (not_ne_iff.mp hi).trans his.symm

/-- Distinct exposed rotations move disjoint sets of men. -/
theorem IsExposedRotation.disjoint_moved (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) (m : Fin n) (hm : ρ m ≠ m) : σ m = m := by
  by_contra hs
  exact hne (eq_of_common_moved hρ hσ hm hs)

/-- Eliminating a distinct exposed rotation leaves this rotation exposed. -/
theorem IsExposedRotation.persist_eliminate (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    IsExposedRotation p (eliminateRotation μ σ) ρ := by
  refine ⟨hρ.isCycle, fun m hm ↦ ?_⟩
  let μ' := eliminateRotation μ σ
  have hold : μ' m = μ m := congrArg μ (hρ.disjoint_moved hσ hne m hm)
  have hnext : μ' (ρ m) = μ (ρ m) :=
    congrArg μ (hρ.disjoint_moved hσ hne (ρ m) (moved_image hm))
  have hs := hρ.successor m hm
  have helig : IsEligibleSuccessor p μ' m (μ' (ρ m)) := by
    refine ⟨?_, ?_⟩
    · simpa only [hold, hnext] using hs.eligible.1
    · rw [Equiv.symm_apply_apply, hnext]
      simpa only [Equiv.symm_apply_apply] using hs.eligible.2
  refine ⟨helig, fun w hw ↦ ?_⟩
  have hman : p.manRank m (μ' m) < p.manRank m w := hw.1
  rw [hold] at hman
  have hbefore : IsEligibleSuccessor p μ m w :=
    ⟨hman, hw.2.trans_le (hσ.womanRank_eliminate_le w)⟩
  change p.manRank m (μ' (ρ m)) ≤ p.manRank m w
  rw [hnext]
  exact hs.min_rank w hbefore

/-- Eliminating two distinct rotations exposed at the same matching commutes. -/
theorem IsExposedRotation.eliminate_comm (hρ : IsExposedRotation p μ ρ)
    (hσ : IsExposedRotation p μ σ) (hne : ρ ≠ σ) :
    eliminateRotation (eliminateRotation μ ρ) σ = eliminateRotation (eliminateRotation μ σ) ρ := by
  apply Equiv.ext
  intro m
  simp only [eliminateRotation_apply]
  by_cases hr : ρ m = m
  · by_cases hs : σ m = m
    · simp only [hr, hs]
    · have hfix := hσ.disjoint_moved hρ hne.symm (σ m) (moved_image hs)
      simp only [hr, hfix]
  · have hfix := hρ.disjoint_moved hσ hne m hr
    have hfix' := hρ.disjoint_moved hσ hne (ρ m) (moved_image hr)
    simp only [hfix, hfix']

end LennonPittelFormalization

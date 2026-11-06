module

public import LennonPittel.CoexposedRotationProbability
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The weighted count supplied by co-exposed rotations

Eliminating a subset of initially exposed rotations gives distinct stable matchings
on which the unchosen rotations remain exposed. Weighting each resulting matching
by two to the number of its exposed rotations gives a lower bound of three to the
number of initially chosen rotations.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ : Matching n}

/-- The number of exposed rotations at a matching. -/
noncomputable def numExposedRotations (p : Profile n) (μ : Matching n) : ℕ :=
  Nat.card {ρ : Equiv.Perm (Fin n) // IsExposedRotation p μ ρ}

/-- Sum of two to the number of exposed rotations over all stable matchings. -/
noncomputable def coexposureWeight (p : Profile n) : ℕ := by
  classical
  exact ∑ ν : {ν : Matching n // IsStable p ν}, 2 ^ numExposedRotations p ν.val

private theorem exists_coexposed_cube_vertex (hμ : IsStable p μ)
    (A : Finset (Equiv.Perm (Fin n))) (hA : ∀ ρ ∈ A, IsExposedRotation p μ ρ)
    (S : Finset (Equiv.Perm (Fin n))) (hS : S ⊆ A) :
    ∃ ν, IsStable p ν ∧
      (∀ ρ ∈ A, ρ ∉ S → IsExposedRotation p ν ρ) ∧
      (∀ m, (∀ ρ ∈ S, ρ m = m) → ν m = μ m) ∧
      (∀ ρ ∈ S, ∀ m, ρ m ≠ m → ν m = μ (ρ m)) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨μ, hμ, fun ρ hρ _ ↦ hA ρ hρ, fun _ _ ↦ rfl,
      fun _ hρ ↦ (Finset.notMem_empty _ hρ).elim⟩
  | @insert a S ha ih =>
    have haA := hS (Finset.mem_insert_self a S)
    have hSA : S ⊆ A := fun _ hρ ↦ hS (Finset.mem_insert_of_mem hρ)
    obtain ⟨ν, hν, hremain, hfixed, hmoved⟩ := ih hSA
    have he := hremain a haA ha
    refine ⟨eliminateRotation ν a, he.isStable_eliminate hν, ?_, ?_, ?_⟩
    · intro ρ hρ hn
      exact (hremain ρ hρ (fun h ↦ hn (Finset.mem_insert_of_mem h))).persist_eliminate he
        (fun h ↦ hn (h.symm ▸ Finset.mem_insert_self a S))
    · intro m hm
      rw [eliminateRotation_apply, hm a (Finset.mem_insert_self a S)]
      exact hfixed m (fun ρ hρ ↦ hm ρ (Finset.mem_insert_of_mem hρ))
    · intro ρ hρ m hm
      rw [eliminateRotation_apply]
      rcases Finset.mem_insert.mp hρ with rfl | hρ'
      · apply hfixed
        exact fun σ hσ ↦ (hA ρ haA).disjoint_moved (hA σ (hSA hσ))
          (fun h ↦ ha (h.symm ▸ hσ)) (ρ m) (ρ.injective.ne hm)
      · rw [(hA ρ (hSA hρ')).disjoint_moved (hA a haA)
          (fun h ↦ ha (h ▸ hρ')) m hm]
        exact hmoved ρ hρ' m hm

/-- Subsets of an exposed family embed into stable matchings, retaining at least
the number of exposed rotations left unchosen. -/
theorem exists_coexposed_cube_embedding (hμ : IsStable p μ)
    (A : Finset (Equiv.Perm (Fin n))) (hA : ∀ ρ ∈ A, IsExposedRotation p μ ρ) :
    ∃ e : ↥A.powerset ↪ {ν : Matching n // IsStable p ν},
      ∀ S, A.card - S.val.card ≤ numExposedRotations p (e S).val := by
  classical
  choose ν hν hremain hfixed hmoved using fun S : ↥A.powerset ↦
    exists_coexposed_cube_vertex hμ A hA S.val (Finset.mem_powerset.mp S.property)
  let f : ↥A.powerset → {ν : Matching n // IsStable p ν} := fun S ↦ ⟨ν S, hν S⟩
  have hsubset (S T : ↥A.powerset) (heq : f S = f T) : S.val ⊆ T.val := by
    intro ρ hρS
    by_contra hρT
    have he := hA ρ (Finset.mem_powerset.mp S.property hρS)
    obtain ⟨m, hm, _⟩ := he.isCycle
    have hfix (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ T.val) : σ m = m :=
      he.disjoint_moved (hA σ (Finset.mem_powerset.mp T.property hσ))
        (fun h ↦ hρT (h.symm ▸ hσ)) m hm
    have hp : ν S m = ν T m := congrArg (fun τ : {τ : Matching n // IsStable p τ} ↦ τ.val m) heq
    rw [hmoved S ρ hρS m hm, hfixed T m hfix] at hp
    exact hm (μ.injective hp)
  refine ⟨⟨f, fun S T he ↦ Subtype.ext (Finset.Subset.antisymm
    (hsubset S T he) (hsubset T S he.symm))⟩, fun S ↦ ?_⟩
  let g : ↥(A \ S.val) → {ρ : Equiv.Perm (Fin n) // IsExposedRotation p (ν S) ρ} :=
    fun ρ ↦ ⟨ρ.val, hremain S ρ.val (Finset.mem_sdiff.mp ρ.property).1
      (Finset.mem_sdiff.mp ρ.property).2⟩
  have hg : Function.Injective g := fun _ _ he ↦
    Subtype.ext (congrArg (Subtype.val :
      {ρ : Equiv.Perm (Fin n) // IsExposedRotation p (ν S) ρ} → _) he)
  change A.card - S.val.card ≤ Nat.card {ρ // IsExposedRotation p (ν S) ρ}
  simpa only [Nat.card_eq_finsetCard,
    Finset.card_sdiff_of_subset (Finset.mem_powerset.mp S.property)] using
    Nat.card_le_card_of_injective g hg

/-- The weighted stable-matching count of a profile dominates three to the
size of any family of co-exposed rotations. -/
theorem pow_card_le_coexposureWeight (hμ : IsStable p μ)
    (A : Finset (Equiv.Perm (Fin n))) (hA : ∀ ρ ∈ A, IsExposedRotation p μ ρ) :
    3 ^ A.card ≤ coexposureWeight p := by
  classical
  obtain ⟨e, he⟩ := exists_coexposed_cube_embedding hμ A hA
  let w (ν : {ν : Matching n // IsStable p ν}) := (2 : ℕ) ^ numExposedRotations p ν.val
  calc
    3 ^ A.card = ∑ S ∈ A.powerset, 2 ^ (A.card - S.card) := by
      simpa only [one_pow, one_mul] using (Finset.sum_pow_mul_eq_add_pow (1 : ℕ) 2 A).symm
    _ = ∑ S : ↥A.powerset, 2 ^ (A.card - S.val.card) :=
      (Finset.sum_attach A.powerset (fun S ↦ 2 ^ (A.card - S.card))).symm
    _ ≤ ∑ S : ↥A.powerset, w (e S) :=
      Finset.sum_le_sum fun S _ ↦ Nat.pow_le_pow_right (by decide) (he S)
    _ = ∑ ν ∈ Finset.univ.map e, w ν := (Finset.sum_map _ _ _).symm
    _ ≤ coexposureWeight p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ Nat.zero_le _

/-- Co-exposure of at least `k` rotations forces the weighted count to reach `3 ^ k`. -/
theorem HasCoexposedRotations.pow_le_coexposureWeight {k : ℕ}
    (hp : HasCoexposedRotations p k) : 3 ^ k ≤ coexposureWeight p :=
  let ⟨_, hμ, A, hk, hA⟩ := hp
  (Nat.pow_le_pow_right (by decide) hk).trans (pow_card_le_coexposureWeight hμ A hA)

end LennonPittelFormalization

module

public import LennonPittel.ExposedRotations

/-!
# Reversing an exposed rotation

Exchange the two sides of the preference profile and take the inverse matching.
The rotation that restores the old matching is then exposed in the ordinary
successor graph of the exchanged profile.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}

/-- Exchange the two sides of a preference profile. -/
def swapProfile (p : Profile n) : Profile n :=
  ⟨p.womanRank, p.manRank⟩

@[simp]
theorem swapProfile_swapProfile (p : Profile n) : swapProfile (swapProfile p) = p := rfl

/-- Exchanging the sides preserves stability after inverting the matching. -/
theorem isStable_swapProfile_iff : IsStable (swapProfile p) μ.symm ↔ IsStable p μ := by
  constructor
  · intro h m w hb
    exact h w m
      ⟨fun he ↦ hb.1 ((congrArg μ he).symm.trans (μ.apply_symm_apply w)), hb.2.2, hb.2.1⟩
  · intro h w m hb
    refine h m w ⟨fun he ↦ hb.1 ?_, hb.2.2, hb.2.1⟩
    simpa only [Equiv.symm_apply_apply] using (congrArg μ.symm he).symm

/-- Relabel a men's cycle by their partners in the matching before elimination. -/
def reverseRotationCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  μ.symm.trans (ρ.trans μ)

/-- Eliminating the relabeled cycle in the exchanged profile recovers the old matching. -/
theorem eliminateRotation_swap_reverseCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    eliminateRotation (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ) = μ.symm := by
  ext w
  simp [reverseRotationCycle, eliminateRotation]

/-- Reversing the undoing cycle returns the original cycle of men. -/
theorem reverseRotationCycle_swap_reverseCycle (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    reverseRotationCycle (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ) = ρ := by
  ext m
  simp [reverseRotationCycle, eliminateRotation]

/-- After a forward elimination, the swapped successor graph exposes its undoing cycle. -/
theorem IsExposedRotation.isExposedRotation_swap_eliminate
    (hρ : IsExposedRotation p μ ρ) (hμ : IsStable p μ) :
    IsExposedRotation (swapProfile p) (eliminateRotation μ ρ).symm
      (reverseRotationCycle μ ρ) := by
  refine ⟨?_, ?_⟩
  · change (μ * ρ * μ⁻¹).IsCycle
    exact hρ.isCycle.conj
  · intro w hw
    obtain ⟨m, rfl⟩ := μ.surjective w
    have hm : ρ m ≠ m := by
      intro he
      apply hw
      simp [reverseRotationCycle, he]
    have hback : ρ (ρ.symm m) ≠ ρ.symm m := by
      intro he
      have he' : m = ρ.symm m := by simpa only [Equiv.apply_symm_apply] using he
      exact hm ((congrArg ρ he').trans (ρ.apply_symm_apply m))
    have hnew : (eliminateRotation μ ρ).symm (reverseRotationCycle μ ρ (μ m)) = m := by
      simp [reverseRotationCycle, eliminateRotation]
    have hcurrent : (eliminateRotation μ ρ).symm (μ m) = ρ.symm m := by
      simp [eliminateRotation]
    constructor
    · have hprev := (hρ.successor (ρ.symm m) hback).eligible.2
      have hwlt : p.womanRank (μ m) (ρ.symm m) < p.womanRank (μ m) m := by
        simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hprev
      simp only [IsEligibleSuccessor, swapProfile, hnew, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply]
      exact ⟨hwlt, (hρ.successor m hm).eligible.1⟩
    · intro t ht
      simp only [IsEligibleSuccessor, swapProfile, hcurrent, Equiv.symm_symm,
        eliminateRotation_apply] at ht
      change p.womanRank (μ m) ((eliminateRotation μ ρ).symm
        (reverseRotationCycle μ ρ (μ m))) ≤ p.womanRank (μ m) t
      rw [hnew]
      by_contra hbad
      -- A better reverse candidate would have been eligible in the old forward row.
      have hwbad := lt_of_not_ge hbad
      have hne : μ t ≠ μ m := fun he ↦
        (ne_of_lt hwbad) (congrArg (p.womanRank (μ m)) (μ.injective he))
      have hnot : ¬ p.manRank t (μ m) < p.manRank t (μ t) := fun ht' ↦
        hμ t (μ m) ⟨hne, ht', by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      have hf : IsEligibleSuccessor p μ t (μ m) :=
        ⟨lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank t).injective he)),
          by simpa only [Equiv.symm_apply_apply] using hwbad⟩
      by_cases htfix : ρ t = t
      · exact (not_lt_of_ge hf.1.le) (by simpa only [htfix] using ht.2)
      · exact (not_lt_of_ge ((hρ.successor t htfix).min_rank _ hf)) ht.2

end LennonPittelFormalization

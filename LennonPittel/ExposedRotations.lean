module

public import LennonPittel.Model
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Exposed rotations in a stable marriage

An exposed rotation follows a single cycle in the successor relation of a matching.
Eliminating the cycle gives each moved man the current partner of the next man.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ}

/-- A woman is eligible as a successor if she is below the man's current partner
in his list and strictly prefers him to her current partner. -/
def IsEligibleSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  p.manRank m (μ m) < p.manRank m w ∧ p.womanRank w m < p.womanRank w (μ.symm w)

/-- The successor is the eligible woman with the smallest rank in the man's list. -/
structure IsSuccessor (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop where
  eligible : IsEligibleSuccessor p μ m w
  min_rank : ∀ w', IsEligibleSuccessor p μ m w' → p.manRank m w ≤ p.manRank m w'

/-- An exposed rotation is a single nontrivial cycle of men in which each moved man's
successor is the old partner of the next man. -/
structure IsExposedRotation (p : Profile n) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Prop where
  isCycle : ρ.IsCycle
  successor : ∀ m, ρ m ≠ m → IsSuccessor p μ m (μ (ρ m))

/-- Eliminating a rotation reassigns man `m` to the old partner of `ρ m`. -/
def eliminateRotation (μ : Matching n) (ρ : Equiv.Perm (Fin n)) : Matching n :=
  ρ.trans μ

@[simp]
theorem eliminateRotation_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (m : Fin n) :
    eliminateRotation μ ρ m = μ (ρ m) := rfl

variable {p : Profile n} {μ : Matching n} {ρ : Equiv.Perm (Fin n)}

/-- There is at most one successor, since every woman's rank in a man's list is distinct. -/
theorem IsSuccessor.unique {m w w' : Fin n}
    (h : IsSuccessor p μ m w) (h' : IsSuccessor p μ m w') : w = w' :=
  (p.manRank m).injective <| le_antisymm (h.min_rank w' h'.eligible) (h'.min_rank w h.eligible)

/-- Each moved man strictly prefers his old partner to his new partner. -/
theorem IsExposedRotation.manRank_lt_eliminate_of_moved (hρ : IsExposedRotation p μ ρ)
    {m : Fin n} (hm : ρ m ≠ m) :
    p.manRank m (μ m) < p.manRank m (eliminateRotation μ ρ m) :=
  (hρ.successor m hm).eligible.1

/-- No woman is worse off after the rotation is eliminated. -/
theorem IsExposedRotation.womanRank_eliminate_le (hρ : IsExposedRotation p μ ρ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ ρ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ ρ).surjective w
  have hle : p.womanRank (μ (ρ m)) m ≤ p.womanRank (μ (ρ m)) (ρ m) :=
    if h : ρ m = m then
      (congrArg (p.womanRank (μ (ρ m))) h.symm).le
    else by
      simpa only [Equiv.symm_apply_apply] using (hρ.successor m h).eligible.2.le
  have htarget : p.womanRank (eliminateRotation μ ρ m)
        ((eliminateRotation μ ρ).symm (eliminateRotation μ ρ m)) ≤
      p.womanRank (eliminateRotation μ ρ m) (μ.symm (eliminateRotation μ ρ m)) := by
    have hinv : (eliminateRotation μ ρ).symm (μ (ρ m)) = m :=
      (eliminateRotation μ ρ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget

/-- Eliminating an exposed rotation from a stable matching gives a stable matching. -/
theorem IsExposedRotation.isStable_eliminate (hρ : IsExposedRotation p μ ρ)
    (hμ : IsStable p μ) : IsStable p (eliminateRotation μ ρ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hρ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : ρ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((hρ.successor m hm).min_rank w ⟨hbelow, hwOld⟩)) hb.2.1

/-- An exposed rotation changes the matching. -/
theorem IsExposedRotation.eliminate_ne (hρ : IsExposedRotation p μ ρ) :
    eliminateRotation μ ρ ≠ μ :=
  fun h ↦ hρ.isCycle.ne_one <| Equiv.ext fun m ↦
    μ.injective (congrArg (fun f : Matching n ↦ f m) h)

end LennonPittelFormalization

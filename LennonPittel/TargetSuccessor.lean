module

public import LennonPittel.ExposedRotations
public import Mathlib.Data.Finset.Max

/-!
# Successors toward a stable target

If every man weakly prefers the current matching to a stable target, then each man with
a different partner has a successor no worse than his target partner. The successor's
current husband also has a different target partner.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ ν : Matching n}

private theorem target_partner_eligible (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i))
    {m : Fin n} (hm : μ m ≠ ν m) : IsEligibleSuccessor p μ m (ν m) :=
  let j := μ.symm (ν m)
  have hjμ : μ j = ν m := μ.apply_symm_apply _
  have hjm : j ≠ m := fun h ↦ hm ((congrArg μ h).symm.trans hjμ)
  have hjν : ν j ≠ ν m := ν.injective.ne hjm
  have hjmove : μ j ≠ ν j := fun h ↦ hjν (h.symm.trans hjμ)
  have hjrank : p.manRank j (μ j) < p.manRank j (ν j) :=
    lt_of_le_of_ne (hle j) ((p.manRank j).injective.ne hjmove)
  have hw : ¬ p.womanRank (ν m) j < p.womanRank (ν m) m := fun h ↦
    hν j (ν m) ⟨hjν, by simpa only [hjμ] using hjrank,
      by simpa only [Equiv.symm_apply_apply] using h⟩
  ⟨lt_of_le_of_ne (hle m) ((p.manRank m).injective.ne hm),
    lt_of_le_of_ne (le_of_not_gt hw) ((p.womanRank (ν m)).injective.ne hjm.symm)⟩

private theorem successor_husband_moves (hν : IsStable p ν) {m w : Fin n}
    (hw : IsEligibleSuccessor p μ m w) (hbound : p.manRank m w ≤ p.manRank m (ν m)) :
    μ (μ.symm w) ≠ ν (μ.symm w) :=
  let j := μ.symm w
  have hjμ : μ j = w := μ.apply_symm_apply w
  have hjm : j ≠ m := fun h ↦
    (ne_of_lt hw.1) (congrArg (p.manRank m) ((congrArg μ h).symm.trans hjμ))
  fun heq ↦
    have hjν : ν j = w := heq.symm.trans hjμ
    have hwm : w ≠ ν m := fun h ↦ hjm (ν.injective (hjν.trans h))
    have hlt : p.manRank m w < p.manRank m (ν m) :=
      lt_of_le_of_ne hbound ((p.manRank m).injective.ne hwm)
    have hjνsymm : ν.symm w = j := by
      simpa only [Equiv.symm_apply_apply] using (congrArg ν.symm hjν).symm
    hν m w ⟨hwm.symm, hlt, by simpa only [hjνsymm] using hw.2⟩

/-- A man who has not reached his stable target partner has a successor no worse than
that partner, and the successor's current husband has not reached his target either. -/
theorem exists_successor_towards_target (_hμ : IsStable p μ) (hν : IsStable p ν)
    (hle : ∀ i, p.manRank i (μ i) ≤ p.manRank i (ν i)) {m : Fin n} (hm : μ m ≠ ν m) :
    ∃ j : Fin n, IsSuccessor p μ m (μ j) ∧ μ j ≠ ν j ∧
      p.manRank m (μ j) ≤ p.manRank m (ν m) := by
  classical
  let candidates := Finset.univ.filter (IsEligibleSuccessor p μ m)
  have htarget : ν m ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, target_partner_eligible hν hle hm⟩
  obtain ⟨w, hw, hmin⟩ := candidates.exists_min_image (p.manRank m) ⟨ν m, htarget⟩
  have heligible : IsEligibleSuccessor p μ m w := (Finset.mem_filter.mp hw).2
  have hsuccessor : IsSuccessor p μ m w :=
    ⟨heligible, fun v hv ↦ hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)⟩
  have hbound : p.manRank m w ≤ p.manRank m (ν m) := hmin (ν m) htarget
  have hj : μ (μ.symm w) = w := μ.apply_symm_apply w
  exact ⟨μ.symm w, by simpa only [hj] using hsuccessor,
    successor_husband_moves hν heligible hbound,
    by simpa only [hj] using hbound⟩

end LennonPittelFormalization

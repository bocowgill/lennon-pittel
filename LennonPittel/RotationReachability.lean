module

public import LennonPittel.ManOptimal
public import LennonPittel.RotationCycle
public import LennonPittel.TargetSuccessor

/-!
# Reaching stable matchings by exposed rotations

A target stable matching reachable in the men's preference order can be attained by
successive exposed rotations. A decreasing natural-valued rank gap proves termination.
-/

@[expose] public section

open scoped BigOperators
open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n}

/-- A finite list of rotations that are exposed at their respective elimination steps. -/
inductive RotationSequence (p : Profile n) :
    Matching n → List (Equiv.Perm (Fin n)) → Matching n → Prop where
  | nil {μ : Matching n} (hμ : IsStable p μ) : RotationSequence p μ [] μ
  | cons {μ ν : Matching n} {ρ : Equiv.Perm (Fin n)} {rs : List (Equiv.Perm (Fin n))}
      (hμ : IsStable p μ) (hρ : IsExposedRotation p μ ρ)
      (rest : RotationSequence p (eliminateRotation μ ρ) rs ν) :
      RotationSequence p μ (ρ :: rs) ν

private def totalManRank (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m : Fin n, (p.manRank m (μ m) : ℕ)

private theorem totalManRank_le {μ ν : Matching n}
    (hle : ∀ m, p.manRank m (μ m) ≤ p.manRank m (ν m)) :
    totalManRank p μ ≤ totalManRank p ν :=
  Finset.sum_le_sum fun m _ ↦ hle m

private theorem totalManRank_lt_eliminate {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation p μ ρ) :
    totalManRank p μ < totalManRank p (eliminateRotation μ ρ) :=
  have hle (m : Fin n) : p.manRank m (μ m) ≤ p.manRank m (eliminateRotation μ ρ m) :=
    if hm : ρ m = m then
      le_of_eq (by simp only [eliminateRotation_apply, hm])
    else (hρ.manRank_lt_eliminate_of_moved hm).le
  let ⟨m, hm, _⟩ := hρ.isCycle
  Finset.sum_lt_sum (fun i _ ↦ hle i)
    ⟨m, Finset.mem_univ m, hρ.manRank_lt_eliminate_of_moved hm⟩

/-- If men weakly prefer the current matching to a distinct stable target, an exposed
rotation can be eliminated without going below any man's target partner. -/
theorem exists_exposedRotation_towards_target {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) (hne : μ ≠ ν) :
    ∃ ρ, IsExposedRotation p μ ρ ∧ MenWeaklyPrefer p (eliminateRotation μ ρ) ν := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, μ m ≠ ν m := by
    simpa only [not_forall] using mt (fun h : ∀ i, μ i = ν i ↦ Equiv.ext h) hne
  let changed : Set (Fin n) := {i | μ i ≠ ν i}
  let : Nonempty changed := ⟨⟨m, hm⟩⟩
  -- A changed man's successor is currently matched to another changed man.
  choose next hsucc hchanged hbound using fun i : changed ↦
    exists_successor_towards_target hμ hν hle i.property
  let f : changed → changed := fun i ↦ ⟨next i, hchanged i⟩
  have hnf (i : changed) : f i ≠ i := fun h ↦
    have he : next i = i.val := congrArg Subtype.val h
    (lt_irrefl _) (by simpa only [he] using (hsucc i).eligible.1)
  obtain ⟨ρ, hcycle, hedge⟩ := exists_cycle_permutation f hnf
  refine ⟨ρ, ⟨hcycle, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨ha, hρ⟩ := hedge i hi
    simpa only [hρ] using hsucc ⟨i, ha⟩
  · intro i
    by_cases hi : ρ i = i
    · simpa only [eliminateRotation_apply, hi] using hle i
    · obtain ⟨ha, hρ⟩ := hedge i hi
      simpa only [eliminateRotation_apply, hρ] using hbound ⟨i, ha⟩

/-- Every stable target weakly below a stable start in the men's preference order is
reachable by a finite sequence of exposed rotations. -/
theorem exists_rotationSequence_of_menWeaklyPrefer {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) (hle : MenWeaklyPrefer p μ ν) :
    ∃ rs, RotationSequence p μ rs ν := by
  classical
  let gap := fun σ : Matching n ↦ totalManRank p ν - totalManRank p σ
  refine (measure gap).wf.induction
    (C := fun σ ↦ IsStable p σ →
      MenWeaklyPrefer p σ ν →
      ∃ rs, RotationSequence p σ rs ν) μ ?_ hμ hle
  intro σ ih hσ hσν
  by_cases h : σ = ν
  · exact ⟨[], h ▸ RotationSequence.nil hσ⟩
  · obtain ⟨ρ, hρ, hnext⟩ := exists_exposedRotation_towards_target hσ hν hσν h
    have hinc := totalManRank_lt_eliminate hρ
    have hbound := totalManRank_le hnext
    have hdrop : gap (eliminateRotation σ ρ) < gap σ := by
      dsimp only [gap]
      omega
    obtain ⟨rs, hrs⟩ := ih _ hdrop (hρ.isStable_eliminate hσ) hnext
    exact ⟨ρ :: rs, .cons hσ hρ hrs⟩

/-- Every stable matching can be reached from a man-optimal matching. -/
theorem exists_rotationSequence_of_manOptimal {μ ν : Matching n}
    (hopt : IsManOptimal p μ) (hν : IsStable p ν) :
    ∃ rs, RotationSequence p μ rs ν :=
  exists_rotationSequence_of_menWeaklyPrefer hopt.1 hν (hopt.2 ν hν)

/-- The man-optimal matching is unique: each man must receive the same rank in both. -/
theorem IsManOptimal.eq {μ ν : Matching n} (hμ : IsManOptimal p μ) (hν : IsManOptimal p ν) :
    μ = ν :=
  Equiv.ext fun m ↦ (p.manRank m).injective ((hμ.2 ν hν.1 m).antisymm (hν.2 μ hμ.1 m))

/-- When a stable matching exists, one man-optimal start reaches all stable targets. -/
theorem exists_manOptimal_reaches_every_stable (h : ∃ μ, IsStable p μ) :
    ∃ μ, IsManOptimal p μ ∧ ∀ ν, IsStable p ν → ∃ rs, RotationSequence p μ rs ν :=
  let ⟨μ, hopt⟩ := exists_manOptimal_of_exists_stable h
  ⟨μ, hopt, fun _ hν ↦ exists_rotationSequence_of_manOptimal hopt hν⟩

/-- Given any stable target, there is a man-optimal start and a sequence reaching the target. -/
theorem exists_manOptimal_rotationSequence {ν : Matching n} (hν : IsStable p ν) :
    ∃ μ rs, IsManOptimal p μ ∧ RotationSequence p μ rs ν :=
  let ⟨μ, hopt⟩ := exists_manOptimal_of_exists_stable ⟨ν, hν⟩
  let ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hν
  ⟨μ, rs, hopt, hrs⟩

end LennonPittelFormalization

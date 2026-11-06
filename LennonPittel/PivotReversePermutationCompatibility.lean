module

public import LennonPittel.CoexposureCycleMoment
public import LennonPittel.PivotCrossBlocker

/-!
# Crossed blockers for a reverse successor permutation

A realized permutation can undo several reverse cycles at once. The resulting
matching is stable. If its moved support avoids the forward pivot, loss of
exposure is witnessed by a crossed rectangle involving the two supports.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ ρ σ : Matching n}

/-- Following all realized successor arcs does not worsen any woman's rank. -/
theorem RealizesSuccessorPermutation.womanRank_eliminate_le
    (hσ : RealizesSuccessorPermutation p μ σ) (w : Fin n) :
    p.womanRank w ((eliminateRotation μ σ).symm w) ≤ p.womanRank w (μ.symm w) :=
  let ⟨m, hm⟩ := (eliminateRotation μ σ).surjective w
  have hle : p.womanRank (μ (σ m)) m ≤ p.womanRank (μ (σ m)) (σ m) :=
    if he : σ m = m then (congrArg (p.womanRank (μ (σ m))) he.symm).le
    else by simpa only [Equiv.symm_apply_apply] using
      (hσ m (Equiv.Perm.mem_support.mpr he)).eligible.2.le
  have htarget : p.womanRank (eliminateRotation μ σ m)
      ((eliminateRotation μ σ).symm (eliminateRotation μ σ m)) ≤
        p.womanRank (eliminateRotation μ σ m) (μ.symm (eliminateRotation μ σ m)) := by
    have hinv : (eliminateRotation μ σ).symm (μ (σ m)) = m :=
      (eliminateRotation μ σ).symm_apply_apply m
    simpa only [eliminateRotation_apply, hinv, Equiv.symm_apply_apply] using hle
  hm ▸ htarget

/-- Following a realized successor permutation preserves stability, whether or
not the permutation consists of a single cycle. -/
theorem RealizesSuccessorPermutation.isStable_eliminate
    (hσ : RealizesSuccessorPermutation p μ σ) (hμ : IsStable p μ) :
    IsStable p (eliminateRotation μ σ) :=
  fun m w hb ↦
    have hwOld : p.womanRank w m < p.womanRank w (μ.symm w) :=
      hb.2.2.trans_le (hσ.womanRank_eliminate_le w)
    have hne : μ m ≠ w := fun h ↦ (ne_of_lt hwOld)
      (congrArg (p.womanRank w) ((μ.symm_apply_apply m).symm.trans (congrArg μ.symm h)))
    have hnot : ¬ p.manRank m w < p.manRank m (μ m) := fun h ↦
      hμ m w ⟨hne, h, hwOld⟩
    if hm : σ m = m then
      hnot (by simpa only [eliminateRotation_apply, hm] using hb.2.1)
    else
      have hbelow : p.manRank m (μ m) < p.manRank m w :=
        lt_of_le_of_ne (le_of_not_gt hnot) (fun he ↦ hne ((p.manRank m).injective he))
      (not_lt_of_ge ((hσ m (Equiv.Perm.mem_support.mpr hm)).min_rank w ⟨hbelow, hwOld⟩)) hb.2.1

/-- The simultaneous undo of any realized reverse successor permutation is stable. -/
theorem RealizesSuccessorPermutation.undo_stable
    (hσ : RealizesSuccessorPermutation (swapProfile p) μ.symm σ) (hμ : IsStable p μ) :
    IsStable p (undoReverseRotation μ σ) :=
  isStable_swapProfile_iff.mp (hσ.isStable_eliminate (isStable_swapProfile_iff.mpr hμ))

/-- A woman receives the old husband of her image under the reverse permutation. -/
theorem undoReverseRotation_symm_apply (μ σ : Matching n) (w : Fin n) :
    (undoReverseRotation μ σ).symm w = μ.symm (σ w) :=
  rfl

/-- A man whose old partner is outside the reverse support keeps that partner. -/
theorem undoReverseRotation_apply_of_not_mem_support {m : Fin n} (hm : μ m ∉ σ.support) :
    undoReverseRotation μ σ m = μ m :=
  (undoReverseRotation μ σ).symm.injective <| calc
    (undoReverseRotation μ σ).symm (undoReverseRotation μ σ m) = m :=
      (undoReverseRotation μ σ).symm_apply_apply m
    _ = μ.symm (μ m) := (μ.symm_apply_apply m).symm
    _ = (undoReverseRotation μ σ).symm (μ m) := by
      rw [undoReverseRotation_symm_apply, Equiv.Perm.notMem_support.mp hm]

/-- If the forward pivot ceases to be exposed after undoing a disjoint
realized reverse permutation, one crossed pair lies in the open rectangle
between the old and proposed spouse scores on both sides. -/
theorem exists_crossed_scores_of_not_exposed_after_reversePermutation {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i)) (hμ : IsStable (profileOfScores x) μ)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
    (hdisj : ∀ m ∈ ρ.support, μ m ∉ σ.support)
    (hfail : ¬ IsExposedRotation (profileOfScores x) (undoReverseRotation μ σ) ρ) :
    ∃ m ∈ ρ.support, ∃ w ∈ σ.support,
      x (.inl m) (μ m) < x (.inl m) w ∧
      x (.inl m) w < x (.inl m) (μ (ρ m)) ∧
      x (.inr w) (μ.symm w) < x (.inr w) m ∧
      x (.inr w) m < x (.inr w) (μ.symm (σ w)) :=
  have hfixed (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation μ σ m = μ m :=
    undoReverseRotation_apply_of_not_mem_support (hdisj m (Equiv.Perm.mem_support.mpr hm))
  have hN := (isStable_profileOfScores_iff hx _).mp (hσ.undo_stable hμ)
  Classical.byContradiction fun hnone ↦ hfail
    ((isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hx hρ hN hfixed).mpr
      fun m w hr ↦ hnone
        ⟨m, Equiv.Perm.mem_support.mpr hr.1, w,
          Equiv.Perm.mem_support.mpr fun he ↦ hr.2.1
            ((undoReverseRotation_symm_apply μ σ w).trans (congrArg μ.symm he)),
          by simpa only [undoReverseRotation_symm_apply] using hr.2.2⟩)

end LennonPittelFormalization

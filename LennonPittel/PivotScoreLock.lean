module

public import LennonPittel.CoexposureGoodScores
public import LennonPittel.SingletonRotationAnchor

/-!
# Participant scores at singleton rotation anchors

An exposed label fixes the spouses on the support of its cycle. Moving from an
exposure to the singleton anchor preserves those scores, while the total women's
spouse score can decrease. A lower bound on one locked score then transfers a
lower bound on the total, provided the corresponding anchor share is bounded.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ μ ν : Matching n} {r : Rotation p μ₀}

/-- An exposure's eliminated ideal is contained in the pivot's singleton ideal. -/
theorem Rotation.IsExposedAt.eliminatedRotations_subset_singletonAnchor
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) :
    eliminatedRotations p μ₀ μ ⊆
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val := by
  rw [eliminatedRotations_singletonRotationAnchor]
  intro s hs hrs
  exact ((r.isExposedAt_iff_minimal hopt hμ).mp he).prop (hrs μ hs)

/-- A pivot remains exposed in a larger stable ideal that still omits it. -/
theorem Rotation.IsExposedAt.of_eliminatedRotations_subset
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) (hν : IsStable p ν)
    (hsub : eliminatedRotations p μ₀ μ ⊆ eliminatedRotations p μ₀ ν)
    (hr : r ∉ eliminatedRotations p μ₀ ν) :
    r.IsExposedAt ν := by
  rw [r.isExposedAt_iff_minimal hopt hν, minimal_iff_forall_lt]
  refine ⟨hr, fun _ hlt hnot ↦ hnot (hsub ?_)⟩
  exact (Rotation.lt_iff_before_exposure hopt hlt.ne).mp hlt μ hμ he.1 he.2

/-- Two exposures of the same realized label agree on every moved man's spouse. -/
theorem Rotation.IsExposedAt.partner_eq_of_moved
    (hμ : r.IsExposedAt μ) (hν : r.IsExposedAt ν) {m : Fin n} (hm : r.val.cycle m ≠ m) :
    μ m = ν m := by
  have he := congrArg (fun l : RotationLabel n ↦ l.oldPartner m) (hμ.2.trans hν.2.symm)
  simpa only [rotationLabel, ite_eq_right hm, Option.some.injEq] using he

/-- The woman married to a moved man has the same spouse in both exposures. -/
theorem Rotation.IsExposedAt.husband_eq_of_moved
    (hμ : r.IsExposedAt μ) (hν : r.IsExposedAt ν) {m : Fin n} (hm : r.val.cycle m ≠ m) :
    ν.symm (μ m) = m :=
  (Equiv.symm_apply_eq ν).2 (hμ.partner_eq_of_moved hν hm)

/-- Both scores of a participating couple are locked at the singleton anchor. -/
theorem Rotation.IsExposedAt.singletonAnchor_spouseScores_eq
    (he : r.IsExposedAt μ) (hopt : IsManOptimal p μ₀) (x : ScoreProfile n)
    {m : Fin n} (hm : r.val.cycle m ≠ m) :
    maleSpouseScore x μ m = maleSpouseScore x (singletonRotationAnchor hopt r).val m ∧
      femaleSpouseScore x μ (μ m) =
        femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) := by
  have ha : r.IsExposedAt (singletonRotationAnchor hopt r).val :=
    ((eq_singletonRotationAnchor_iff hopt r _).mp rfl r).mpr rfl
  exact ⟨congrArg (x (.inl m)) (he.partner_eq_of_moved ha hm),
    congrArg (x (.inr (μ m))) ((μ.symm_apply_apply m).trans
      (he.husband_eq_of_moved ha hm).symm)⟩

/-- In an increasing rotation path, every woman weakly improves her rank. -/
theorem RotationSequence.womanRank_end_le {rs : List (Equiv.Perm (Fin n))}
    (hpath : RotationSequence p μ rs ν) (j : Fin n) :
    p.womanRank j (ν.symm j) ≤ p.womanRank j (μ.symm j) := by
  induction hpath with
  | nil => exact le_rfl
  | cons _ hρ _ ih => exact ih.trans (hρ.womanRank_eliminate_le j)

/-- Women's total spouse score is nonincreasing under inclusion of stable ideals. -/
theorem femaleSpouseTotal_le_of_eliminatedRotations_subset {x : ScoreProfile n}
    {μ₀ μ ν : Matching n} (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hμ : IsStable (profileOfScores x) μ) (hν : IsStable (profileOfScores x) ν)
    (hsub : eliminatedRotations (profileOfScores x) μ₀ μ ⊆
      eliminatedRotations (profileOfScores x) μ₀ ν) :
    femaleSpouseTotal x ν ≤ femaleSpouseTotal x μ := by
  obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hμ hν
    ((eliminatedRotations_subset_iff hopt hμ hν).mp hsub)
  refine Finset.sum_le_sum fun j _ ↦ le_of_not_gt fun hgt ↦ ?_
  exact (not_lt_of_ge (hpath.womanRank_end_le j))
    ((rankPermutation_lt_iff (ht (.inr j)) (μ.symm j) (ν.symm j)).mpr hgt)

/-- A lower share at one locked coordinate and an upper share at that coordinate
at the anchor bound the anchor's total from below. Ideal inclusion bounds it above. -/
theorem Rotation.IsExposedAt.singletonAnchor_femaleSpouseTotal_bounds {x : ScoreProfile n}
    {μ₀ μ : Matching n} {r : Rotation (profileOfScores x) μ₀}
    (he : r.IsExposedAt μ) (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀) (hμ : IsStable (profileOfScores x) μ)
    {m : Fin n} (hm : r.val.cycle m ≠ m) {a b : ℝ} (hb : 0 < b)
    (hlo : femaleSpouseTotal x μ * a ≤ femaleSpouseScore x μ (μ m))
    (hhi : femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) ≤
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val * b) :
    femaleSpouseTotal x μ * a / b ≤ femaleSpouseTotal x (singletonRotationAnchor hopt r).val ∧
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val ≤ femaleSpouseTotal x μ := by
  refine ⟨(div_le_iff₀ hb).2 ?_, femaleSpouseTotal_le_of_eliminatedRotations_subset ht hopt hμ
    (singletonRotationAnchor hopt r).property (he.eliminatedRotations_subset_singletonAnchor
      hopt hμ)⟩
  calc
    femaleSpouseTotal x μ * a ≤ femaleSpouseScore x μ (μ m) := hlo
    _ = femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) :=
      (he.singletonAnchor_spouseScores_eq hopt x hm).2
    _ ≤ femaleSpouseTotal x (singletonRotationAnchor hopt r).val * b := hhi

/-- The locked-coordinate bound stated in terms of normalized spouse shares. -/
theorem Rotation.IsExposedAt.singletonAnchor_femaleSpouseTotal_bounds_of_shares
    {x : ScoreProfile n} {μ₀ μ : Matching n} {r : Rotation (profileOfScores x) μ₀}
    (he : r.IsExposedAt μ) (ht : ∀ row, Function.Injective (x row))
    (hopt : IsManOptimal (profileOfScores x) μ₀) (hμ : IsStable (profileOfScores x) μ)
    {m : Fin n} (hm : r.val.cycle m ≠ m) {a b : ℝ} (hb : 0 < b)
    (hμpos : 0 < femaleSpouseTotal x μ)
    (hApos : 0 < femaleSpouseTotal x (singletonRotationAnchor hopt r).val)
    (hlo : a ≤ femaleSpouseScore x μ (μ m) / femaleSpouseTotal x μ)
    (hhi : femaleSpouseScore x (singletonRotationAnchor hopt r).val (μ m) /
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val ≤ b) :
    femaleSpouseTotal x μ * a / b ≤ femaleSpouseTotal x (singletonRotationAnchor hopt r).val ∧
      femaleSpouseTotal x (singletonRotationAnchor hopt r).val ≤ femaleSpouseTotal x μ :=
  he.singletonAnchor_femaleSpouseTotal_bounds ht hopt hμ hm hb
    (by simpa only [mul_comm] using (le_div_iff₀ hμpos).mp hlo)
    (by simpa only [mul_comm] using (div_le_iff₀ hApos).mp hhi)

end LennonPittelFormalization

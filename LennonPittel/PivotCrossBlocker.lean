module

public import LennonPittel.ReverseRotationIdeals
public import LennonPittel.ScoreRanks

/-!
# Local compatibility of a forward pivot with an undo endpoint

Only a woman whose partner changed in the undo can become a new, earlier
successor of a pivot man. Stability of the undo endpoint places such a pair
between the two spouse scores on each side.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {A N : Matching n} {ρ : Equiv.Perm (Fin n)}

/-- An undo-changed woman who would block a pivot man's move to his original successor. -/
def IsPivotCrossBlocker (p : Profile n) (A N : Matching n) (ρ : Equiv.Perm (Fin n))
    (m w : Fin n) : Prop :=
  ρ m ≠ m ∧ N.symm w ≠ A.symm w ∧
    p.manRank m w < p.manRank m (A (ρ m)) ∧ p.womanRank w m < p.womanRank w (N.symm w)

/-- A pivot's label is unchanged when its moved men keep their old partners. -/
theorem rotationLabel_eq_of_fixed_on_cycle
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    rotationLabel N ρ = rotationLabel A ρ := by
  unfold rotationLabel
  congr 1
  funext m
  by_cases hm : ρ m = m
  · simp [hm]
  · simp [hm, hfixed m hm]

private theorem IsPivotCrossBlocker.old_partner_ne {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    A m ≠ w := by
  rintro rfl
  apply h.2.1
  rw [← hfixed m h.1, N.symm_apply_apply, hfixed m h.1, A.symm_apply_apply]

/-- At a stable undo endpoint a crossed blocker is below the pivot man's old spouse. -/
theorem IsPivotCrossBlocker.manRank_old_lt {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    p.manRank m (A m) < p.manRank m w := by
  have hne := h.old_partner_ne hfixed
  have hnot : ¬ p.manRank m w < p.manRank m (A m) := fun hlt ↦
    hN m w ⟨(hfixed m h.1).trans_ne hne, (hfixed m h.1).symm ▸ hlt, h.2.2.2⟩
  exact lt_of_le_of_ne (le_of_not_gt hnot) (fun heq ↦ hne ((p.manRank m).injective heq))

/-- A crossed blocker did not already prefer the pivot man to her old spouse. -/
theorem IsPivotCrossBlocker.womanRank_old_lt {m w : Fin n}
    (h : IsPivotCrossBlocker p A N ρ m w) (hρ : IsExposedRotation p A ρ)
    (hN : IsStable p N) (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    p.womanRank w (A.symm w) < p.womanRank w m := by
  have hnot : ¬ p.womanRank w m < p.womanRank w (A.symm w) := fun hlt ↦
    (not_lt_of_ge ((hρ.successor m h.1).min_rank w ⟨h.manRank_old_lt hN hfixed, hlt⟩)) h.2.2.1
  apply lt_of_le_of_ne (le_of_not_gt hnot)
  intro heq
  have hh := (p.womanRank w).injective heq
  exact h.old_partner_ne hfixed ((congrArg A hh).symm.trans (A.apply_symm_apply w))

/-- When the pivot men retain their partners, the original cycle stays exposed
exactly when no undo-changed woman gives a crossed blocker. -/
theorem isExposedRotation_iff_no_pivotCrossBlocker
    (hρ : IsExposedRotation p A ρ) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation p N ρ ↔ ∀ m w, ¬ IsPivotCrossBlocker p A N ρ m w := by
  constructor
  · intro he m w h
    have ht := hfixed (ρ m) (ρ.injective.ne h.1)
    have hman : p.manRank m (N m) < p.manRank m w := by
      rw [hfixed m h.1]
      exact h.manRank_old_lt hN hfixed
    have hle := (he.successor m h.1).min_rank w ⟨hman, h.2.2.2⟩
    rw [ht] at hle
    exact (not_lt_of_ge hle) h.2.2.1
  · intro h
    refine ⟨hρ.isCycle, fun m hm ↦ ?_⟩
    have hold := hfixed m hm
    have ht := hfixed (ρ m) (ρ.injective.ne hm)
    have hs := hρ.successor m hm
    constructor
    · constructor
      · simpa only [hold, ht] using hs.eligible.1
      · have hinv := N.symm_apply_apply (ρ m)
        rw [ht] at hinv
        simpa only [ht, hinv, Equiv.symm_apply_apply] using hs.eligible.2
    · intro w hw
      by_cases hw' : N.symm w = A.symm w
      · have hwA : IsEligibleSuccessor p A m w :=
          ⟨by simpa only [hold] using hw.1, by simpa only [hw'] using hw.2⟩
        simpa only [ht] using hs.min_rank w hwA
      · apply le_of_not_gt
        intro hlt
        exact h m w ⟨hm, hw', by simpa only [ht] using hlt, hw.2⟩

/-- With the pivot participants fixed by the undo, exposure is equivalent to
stability after applying the pivot cycle. -/
theorem isExposedRotation_iff_stable_eliminate_of_fixed_on_cycle
    (hρ : IsExposedRotation p A ρ) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation p N ρ ↔ IsStable p (eliminateRotation N ρ) := by
  refine ⟨fun h ↦ h.isStable_eliminate hN, fun h ↦ ?_⟩
  apply (isExposedRotation_iff_no_pivotCrossBlocker hρ hN hfixed).mpr
  intro m w hc
  have hwfix : ρ (N.symm w) = N.symm w := by
    by_contra hm
    apply hc.2.1
    apply A.injective
    rw [← hfixed (N.symm w) hm, N.apply_symm_apply, A.apply_symm_apply]
  have hinv : (eliminateRotation N ρ).symm w = N.symm w := by
    apply (eliminateRotation N ρ).injective
    rw [Equiv.apply_symm_apply, eliminateRotation_apply, hwfix, N.apply_symm_apply]
  have hman : p.manRank m w < p.manRank m (eliminateRotation N ρ m) := by
    simpa only [eliminateRotation_apply, hfixed (ρ m) (ρ.injective.ne hc.1)] using hc.2.2.1
  exact h m w ⟨fun he ↦ hman.ne (congrArg (p.manRank m) he).symm, hman,
    by simpa only [hinv] using hc.2.2.2⟩

/-- Compatible endpoints can be combined when every changed woman's final
partner is accounted for by one of them and all leave the pivot men fixed. -/
theorem isExposedRotation_of_covering_compatible_endpoints
    (hρ : IsExposedRotation p A ρ) (hN : IsStable p N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m)
    (hcover : ∀ w, N.symm w ≠ A.symm w → ∃ B : Matching n,
      B.symm w = N.symm w ∧ (∀ m, ρ m ≠ m → B m = A m) ∧ IsExposedRotation p B ρ) :
    IsExposedRotation p N ρ := by
  apply (isExposedRotation_iff_no_pivotCrossBlocker hρ hN hfixed).mpr
  intro m w hc
  obtain ⟨B, hw, hBfix, hB⟩ := hcover w hc.2.1
  have hman : p.manRank m (B m) < p.manRank m w := by
    rw [hBfix m hc.1]
    exact hc.manRank_old_lt hN hfixed
  have hwoman : p.womanRank w m < p.womanRank w (B.symm w) := by
    rw [hw]
    exact hc.2.2.2
  have hle := (hB.successor m hc.1).min_rank w ⟨hman, hwoman⟩
  rw [hBfix (ρ m) (ρ.injective.ne hc.1)] at hle
  exact (not_lt_of_ge hle) hc.2.2.1

private theorem RotationSequence.apply_eq_start_of_fixed_all {rs : List (Equiv.Perm (Fin n))}
    (hs : RotationSequence p A rs N) {w : Fin n}
    (hfixed : ∀ σ ∈ rs, σ w = w) : N w = A w := by
  induction hs with
  | nil => rfl
  | @cons _ _ σ rs _ _ _ ih =>
    rw [ih (fun τ hτ ↦ hfixed τ (List.mem_cons_of_mem σ hτ)),
      eliminateRotation_apply, hfixed σ List.mem_cons_self]

private theorem RotationSequence.apply_eq_start_or_one_cycle {rs : List (Equiv.Perm (Fin n))}
    (hs : RotationSequence p A rs N) (hnd : rs.Nodup)
    (hd : ∀ σ ∈ rs, ∀ τ ∈ rs, σ ≠ τ → ∀ w, σ w ≠ w → τ w = w) (w : Fin n) :
    N w = A w ∨ ∃ σ ∈ rs, σ w ≠ w ∧ N w = A (σ w) := by
  induction hs with
  | nil => exact Or.inl rfl
  | @cons A _ σ rs _ _ htail ih =>
    have hhead := (List.nodup_cons.mp hnd).1
    have hmem (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ rs) : τ ∈ σ :: rs :=
      List.mem_cons_of_mem σ hτ
    by_cases hw : σ w = w
    · rcases ih (List.nodup_cons.mp hnd).2
          (fun τ hτ ζ hζ ↦ hd τ (hmem τ hτ) ζ (hmem ζ hζ)) with
        heq | ⟨τ, hτ, hm, heq⟩
      · exact Or.inl (by simpa only [eliminateRotation_apply, hw] using heq)
      · have hne : τ ≠ σ := fun he ↦ hhead (he ▸ hτ)
        have hfix := hd τ (hmem τ hτ) σ List.mem_cons_self hne (τ w) (τ.injective.ne hm)
        exact Or.inr ⟨τ, hmem τ hτ, hm, by
          simpa only [eliminateRotation_apply, hfix] using heq⟩
    · have hfix (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ rs) : τ w = w :=
        hd σ List.mem_cons_self τ (hmem τ hτ) (fun he ↦ hhead (he.symm ▸ hτ)) w hw
      exact Or.inr ⟨σ, List.mem_cons_self, hw, htail.apply_eq_start_of_fixed_all hfix⟩

/-- Each woman changed by a sequence of initially exposed reverse cycles has
the husband she would get by undoing just her own cycle. -/
theorem reverse_rotationSequence_woman_provenance {rs : List (Equiv.Perm (Fin n))}
    (hseq : RotationSequence (swapProfile p) A.symm rs N.symm) (hnd : rs.Nodup)
    (he : ∀ σ ∈ rs, IsReverseExposedRotation p A σ)
    {w : Fin n} (hw : N.symm w ≠ A.symm w) :
    ∃ σ ∈ rs, σ w ≠ w ∧ (undoReverseRotation A σ).symm w = N.symm w := by
  have hd (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ rs) (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ rs)
      (hne : σ ≠ τ) (v : Fin n) (hm : σ v ≠ v) : τ v = v :=
    (show IsExposedRotation (swapProfile p) A.symm σ from he σ hσ).disjoint_moved
      (he τ hτ) hne v hm
  obtain ⟨σ, hσ, hmove, heq⟩ := (hseq.apply_eq_start_or_one_cycle hnd hd w).resolve_left hw
  exact ⟨σ, hσ, hmove, by simpa only [undoReverseRotation, Equiv.symm_symm,
    eliminateRotation_apply] using heq.symm⟩

/-- Compatibility with each individual undo implies compatibility with their
sequence when the pivot men keep their partners throughout the tested endpoints. -/
theorem isExposedRotation_of_compatible_reverse_sequence {rs : List (Equiv.Perm (Fin n))}
    (hseq : RotationSequence (swapProfile p) A.symm rs N.symm) (hnd : rs.Nodup)
    (he : ∀ σ ∈ rs, IsReverseExposedRotation p A σ) (hρ : IsExposedRotation p A ρ)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m)
    (hindfix : ∀ σ ∈ rs, ∀ m, ρ m ≠ m → undoReverseRotation A σ m = A m)
    (hcompat : ∀ σ ∈ rs, IsExposedRotation p (undoReverseRotation A σ) ρ) :
    IsExposedRotation p N ρ := by
  apply isExposedRotation_of_covering_compatible_endpoints hρ
    (isStable_swapProfile_iff.mp hseq.isStable_end) hfixed
  intro w hw
  obtain ⟨σ, hσ, _, heq⟩ := reverse_rotationSequence_woman_provenance hseq hnd he hw
  exact ⟨undoReverseRotation A σ, heq, hindfix σ hσ, hcompat σ hσ⟩

/-- The open score rectangle for a crossed blocker, including its participant conditions. -/
def IsPivotCrossRectangle (x : ScoreProfile n) (A N : Matching n)
    (ρ : Equiv.Perm (Fin n)) (m w : Fin n) : Prop :=
  ρ m ≠ m ∧ N.symm w ≠ A.symm w ∧
    x (.inl m) (A m) < x (.inl m) w ∧ x (.inl m) w < x (.inl m) (A (ρ m)) ∧
    x (.inr w) (A.symm w) < x (.inr w) m ∧ x (.inr w) m < x (.inr w) (N.symm w)

/-- For distinct scores in each row the local compatibility test is exactly
membership in the open rectangle of original and new spouse scores. -/
theorem isPivotCrossBlocker_iff_score_rectangle {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i))
    (hρ : IsExposedRotation (profileOfScores x) A ρ) (hN : IsStable (profileOfScores x) N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) (m w : Fin n) :
    IsPivotCrossBlocker (profileOfScores x) A N ρ m w ↔ IsPivotCrossRectangle x A N ρ m w := by
  let hm := rankPermutation_lt_iff (hx (.inl m))
  let hw := rankPermutation_lt_iff (hx (.inr w))
  exact ⟨fun h ↦ ⟨h.1, h.2.1, (hm _ _).mp (h.manRank_old_lt hN hfixed),
    (hm _ _).mp h.2.2.1, (hw _ _).mp (h.womanRank_old_lt hρ hN hfixed), (hw _ _).mp h.2.2.2⟩,
    fun ⟨ha, hb, _, hc, _, hd⟩ ↦ ⟨ha, hb, (hm _ _).mpr hc, (hw _ _).mpr hd⟩⟩

/-- For tie-free scores, avoiding the crossed rectangles is exactly the
condition for the pivot to remain exposed at a stable undo endpoint. -/
theorem isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle {x : ScoreProfile n}
    (hx : ∀ i, Function.Injective (x i))
    (hρ : IsExposedRotation (profileOfScores x) A ρ) (hN : IsScoreStable x N)
    (hfixed : ∀ m, ρ m ≠ m → N m = A m) :
    IsExposedRotation (profileOfScores x) N ρ ↔
      ∀ m w, ¬ IsPivotCrossRectangle x A N ρ m w := by
  have hstable := (isStable_profileOfScores_iff hx N).mpr hN
  simpa only [isPivotCrossBlocker_iff_score_rectangle hx hρ hstable hfixed] using
    isExposedRotation_iff_no_pivotCrossBlocker hρ hstable hfixed

end LennonPittelFormalization

module

public import LennonPittel.PivotScoreLock
public import LennonPittel.PivotReverseFilteredCount
public import LennonPittel.PivotLocalEligibility
public import LennonPittel.PivotFullRevealLaw

/-!
# Replay above a stable anchor from its full forward reveal

The full forward reveal consists of the spouse scores, the eligibility flags,
and both scores at each eligible off-spouse pair. If a second stable matching
is weakly worse for the men, its new spouse pairs and all its forward-eligible
pairs were already revealed at the anchor.

The same reveal determines reverse searches for women whose husbands changed,
as well as the compatibility and increment tests of collections on those women.
A measurable completion of the observed data supplies a representative for
applying these pointwise statements to reveal-measurable events.
-/

@[expose] public section

open MeasureTheory Set StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The score test for a forward-eligible pair at a fixed matching. -/
def ScoreForwardEligible (x : ScoreProfile n) (A : Matching n) (m w : Fin n) : Prop :=
  x (.inl m) (A m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (A.symm w)

/-- Agreement of both observed scores at a given pair. -/
def ScorePairAgrees (x y : ScoreProfile n) (m w : Fin n) : Prop :=
  x (.inl m) w = y (.inl m) w ∧ x (.inr w) m = y (.inr w) m

/-- Two arrays have the same spouse scores, forward flags, and active scores. -/
structure FullForwardRevealAgrees (x y : ScoreProfile n) (A : Matching n) : Prop where
  spouse : ∀ m, ScorePairAgrees x y m (A m)
  eligible_iff : ∀ m w, ScoreForwardEligible x A m w ↔ ScoreForwardEligible y A m w
  cell : ∀ m w, ScoreForwardEligible x A m w → ScorePairAgrees x y m w

variable {x y : ScoreProfile n} {A B : Matching n}

theorem FullForwardRevealAgrees.symm (h : FullForwardRevealAgrees x y A) :
    FullForwardRevealAgrees y x A where
  spouse m := ⟨(h.spouse m).1.symm, (h.spouse m).2.symm⟩
  eligible_iff m w := (h.eligible_iff m w).symm
  cell m w hw :=
    let hc := h.cell m w ((h.eligible_iff m w).mpr hw)
    ⟨hc.1.symm, hc.2.symm⟩

/-- Spouse agreement indexed by women rather than by men. -/
theorem FullForwardRevealAgrees.womanSpouse (h : FullForwardRevealAgrees x y A) (w : Fin n) :
    x (.inr w) (A.symm w) = y (.inr w) (A.symm w) := by
  simpa only [A.apply_symm_apply] using (h.spouse (A.symm w)).2

private theorem rankPermutation_le_iff_of_injective {u : Fin n → ℝ}
    (hu : Function.Injective u) (i j : Fin n) :
    rankPermutation u i ≤ rankPermutation u j ↔ u i ≤ u j := by
  rw [← not_lt, ← not_lt, rankPermutation_lt_iff hu]

theorem isEligibleSuccessor_profileOfScores_iff (hx : ∀ row, Function.Injective (x row))
    (A : Matching n) (m w : Fin n) :
    IsEligibleSuccessor (profileOfScores x) A m w ↔ ScoreForwardEligible x A m w := by
  simp only [IsEligibleSuccessor, profileOfScores, ScoreForwardEligible,
    rankPermutation_lt_iff (hx (.inl m)), rankPermutation_lt_iff (hx (.inr w))]

/-- A woman who strictly prefers a man to her anchor spouse identifies a
forward-eligible cell there, since anchor stability rules out blocking. -/
theorem scoreForwardEligible_of_woman_lt (hA : IsScoreStable x A)
    {m w : Fin n} (hm : Function.Injective (x (.inl m)))
    (hw : x (.inr w) m < x (.inr w) (A.symm w)) :
    ScoreForwardEligible x A m w := by
  have hne : A m ≠ w := by
    rintro rfl
    rw [A.symm_apply_apply] at hw
    exact lt_irrefl _ hw
  have hle : x (.inl m) (A m) ≤ x (.inl m) w :=
    le_of_not_gt fun hlt ↦ hA m w ⟨hne, hlt, hw⟩
  exact ⟨lt_of_le_of_ne hle (fun he ↦ hne (hm he)), hw⟩

private theorem FullForwardRevealAgrees.replay_spouses (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row))
    (hA : IsScoreStable x A) (hB : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B) :
    (∀ m, ScorePairAgrees x y m (B m)) ∧
      (∀ w, x (.inr w) (B.symm w) ≤ x (.inr w) (A.symm w)) := by
  obtain ⟨_, hpath⟩ :=
    exists_rotationSequence_of_menWeaklyPrefer ((isStable_profileOfScores_iff hx A).mpr hA) hB hAB
  have hw (w : Fin n) : x (.inr w) (B.symm w) ≤ x (.inr w) (A.symm w) :=
    (rankPermutation_le_iff_of_injective (hx (.inr w)) _ _).mp (hpath.womanRank_end_le w)
  refine ⟨fun m ↦ ?_, hw⟩
  by_cases he : A m = B m
  · rw [← he]
    exact h.spouse m
  · have hne : m ≠ A.symm (B m) := fun hh ↦ he ((A.symm_apply_eq).mp hh.symm).symm
    have hle : x (.inr (B m)) m ≤ x (.inr (B m)) (A.symm (B m)) := by
      simpa only [B.symm_apply_apply] using hw (B m)
    exact h.cell m (B m) (scoreForwardEligible_of_woman_lt hA (hx (.inl m))
      (lt_of_le_of_ne hle (fun heq ↦ hne (hx (.inr (B m)) heq))))

/-- If two tie-free arrays agree on the full forward reveal at a common
stable anchor, then every stable matching above that anchor replays in the
second array, including the complete forward reveal at that later matching. -/
theorem FullForwardRevealAgrees.later (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B) :
    IsStable (profileOfScores y) B ∧ MenWeaklyPrefer (profileOfScores y) A B ∧
      FullForwardRevealAgrees x y B := by
  have hAx' := (isStable_profileOfScores_iff hx A).mp hAx
  have hAy' := (isStable_profileOfScores_iff hy A).mp hAy
  obtain ⟨hsp, hwx⟩ := h.replay_spouses hx hAx' hBx hAB
  have hwsp (w : Fin n) : x (.inr w) (B.symm w) = y (.inr w) (B.symm w) := by
    simpa only [B.apply_symm_apply] using (hsp (B.symm w)).2
  have hmx (m : Fin n) : x (.inl m) (A m) ≤ x (.inl m) (B m) :=
    (rankPermutation_le_iff_of_injective (hx (.inl m)) _ _).mp (hAB m)
  have hmy (m : Fin n) : y (.inl m) (A m) ≤ y (.inl m) (B m) := by
    rw [← (h.spouse m).1, ← (hsp m).1]
    exact hmx m
  have hwy (w : Fin n) : y (.inr w) (B.symm w) ≤ y (.inr w) (A.symm w) := by
    rw [← hwsp w, ← h.womanSpouse w]
    exact hwx w
  have hstable : IsScoreStable y B := by
    intro m w hb
    have he := scoreForwardEligible_of_woman_lt hAy' (hy (.inl m)) (hb.2.2.trans_le (hwy w))
    have hc := h.cell m w ((h.eligible_iff m w).mpr he)
    apply (isStable_profileOfScores_iff hx B).mp hBx m w
    exact ⟨hb.1, hc.1.symm ▸ (hsp m).1.symm ▸ hb.2.1, hc.2.symm ▸ (hwsp w).symm ▸ hb.2.2⟩
  refine ⟨(isStable_profileOfScores_iff hy B).mpr hstable,
    fun m ↦ (rankPermutation_le_iff_of_injective (hy (.inl m)) _ _).mpr (hmy m),
    ⟨hsp, ?_, ?_⟩⟩
  · intro m w
    constructor
    · intro he
      have hc := h.cell m w ⟨(hmx m).trans_lt he.1, he.2.trans_le (hwx w)⟩
      exact ⟨(hsp m).1 ▸ hc.1 ▸ he.1, hwsp w ▸ hc.2 ▸ he.2⟩
    · intro he
      have hc := h.symm.cell m w ⟨(hmy m).trans_lt he.1, he.2.trans_le (hwy w)⟩
      exact ⟨(hsp m).1.symm ▸ hc.1 ▸ he.1, (hwsp w).symm ▸ hc.2 ▸ he.2⟩
  · intro m w he
    exact h.cell m w ⟨(hmx m).trans_lt he.1, he.2.trans_le (hwx w)⟩

/-- Agreement of the full reveal implies agreement of the forward successors. -/
theorem FullForwardRevealAgrees.successor_iff (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (m w : Fin n) :
    IsSuccessor (profileOfScores x) A m w ↔ IsSuccessor (profileOfScores y) A m w := by
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hs : IsSuccessor (profileOfScores u) A m w) : IsSuccessor (profileOfScores v) A m w := by
    let ex := isEligibleSuccessor_profileOfScores_iff hu A m
    let ey := isEligibleSuccessor_profileOfScores_iff hv A m
    have hw := (ex w).mp hs.eligible
    refine ⟨(ey w).mpr ((huv.eligible_iff m w).mp hw), fun w' hw' ↦ ?_⟩
    have hw' := (huv.eligible_iff m w').mpr ((ey w').mp hw')
    have hle := (rankPermutation_le_iff_of_injective (hu (.inl m)) w w').mp
      (hs.min_rank w' ((ex w').mpr hw'))
    apply (rankPermutation_le_iff_of_injective (hv (.inl m)) w w').mpr
    rw [← (huv.cell m w hw).1, ← (huv.cell m w' hw').1]
    exact hle
  exact ⟨transport h hx hy, transport h.symm hy hx⟩

/-- Agreement of the full reveal preserves all exposed forward cycles. -/
theorem FullForwardRevealAgrees.exposedRotation_iff (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (ρ : Matching n) :
    IsExposedRotation (profileOfScores x) A ρ ↔ IsExposedRotation (profileOfScores y) A ρ :=
  ⟨fun hρ ↦ ⟨hρ.isCycle, fun m hm ↦
      (h.successor_iff hx hy m _).mp (hρ.successor m hm)⟩,
    fun hρ ↦ ⟨hρ.isCycle, fun m hm ↦ (h.successor_iff hx hy m _).mpr (hρ.successor m hm)⟩⟩

/-- Every pair at or above a woman's anchor spouse in her preferences is
fully revealed: it is the spouse cell or a forward-eligible cell. -/
theorem FullForwardRevealAgrees.pair_agrees_of_woman_le (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hA : IsScoreStable x A) {m w : Fin n}
    (hw : x (.inr w) m ≤ x (.inr w) (A.symm w)) : ScorePairAgrees x y m w := by
  rcases lt_or_eq_of_le hw with hlt | he
  · exact h.cell m w (scoreForwardEligible_of_woman_lt hA (hx (.inl m)) hlt)
  · have hm : m = A.symm w := hx (.inr w) he
    have hw' : A m = w := ((Equiv.symm_apply_eq A).mp hm.symm).symm
    rw [← hw']
    exact h.spouse m

private theorem reverseEligible_profileOfScores_iff
    (hx : ∀ row, Function.Injective (x row)) (B : Matching n) (w m : Fin n) :
    IsEligibleSuccessor (swapProfile (profileOfScores x)) B.symm w m ↔
      x (.inr w) (B.symm w) < x (.inr w) m ∧ x (.inl m) w < x (.inl m) (B m) := by
  simp only [IsEligibleSuccessor, swapProfile, profileOfScores, Equiv.symm_symm,
    rankPermutation_lt_iff (hx (.inr w)), rankPermutation_lt_iff (hx (.inl m))]

private theorem reverseEligible_anchorHusband_of_changed
    (hx : ∀ row, Function.Injective (x row)) (hA : IsStable (profileOfScores x) A)
    (hB : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {w : Fin n} (hw : B.symm w ≠ A.symm w) :
    IsEligibleSuccessor (swapProfile (profileOfScores x)) B.symm w (A.symm w) := by
  obtain ⟨_, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer hA hB hAB
  apply (reverseEligible_profileOfScores_iff hx B w _).mpr
  constructor
  · apply (rankPermutation_lt_iff (hx (.inr w)) _ _).mp
    exact lt_of_le_of_ne (hpath.womanRank_end_le w)
      (fun he ↦ hw ((rankPermutation (x (.inr w))).injective he))
  · have hne : w ≠ B (A.symm w) := fun he ↦ hw ((Equiv.symm_apply_eq B).mpr he)
    have hle : x (.inl (A.symm w)) w ≤ x (.inl (A.symm w)) (B (A.symm w)) := by
      simpa only [A.apply_symm_apply] using
        (rankPermutation_le_iff_of_injective (hx (.inl (A.symm w))) _ _).mp (hAB (A.symm w))
    exact lt_of_le_of_ne hle (fun he ↦ hne (hx (.inl (A.symm w)) he))

private theorem FullForwardRevealAgrees.reverseSearchPrefix_iff (h : FullForwardRevealAgrees x y A)
    (hB : FullForwardRevealAgrees x y B)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsScoreStable x A) (hAy : IsScoreStable y A) (w m : Fin n) :
    (IsEligibleSuccessor (swapProfile (profileOfScores x)) B.symm w m ∧
      x (.inr w) m ≤ x (.inr w) (A.symm w)) ↔
    (IsEligibleSuccessor (swapProfile (profileOfScores y)) B.symm w m ∧
      y (.inr w) m ≤ y (.inr w) (A.symm w)) := by
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hBuv : FullForwardRevealAgrees u v B)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hAu : IsScoreStable u A) :
      (IsEligibleSuccessor (swapProfile (profileOfScores u)) B.symm w m ∧
        u (.inr w) m ≤ u (.inr w) (A.symm w)) →
      (IsEligibleSuccessor (swapProfile (profileOfScores v)) B.symm w m ∧
        v (.inr w) m ≤ v (.inr w) (A.symm w)) := by
    rintro ⟨he, hl⟩
    have hc := huv.pair_agrees_of_woman_le hu hAu hl
    refine ⟨(reverseEligible_profileOfScores_iff hv B w m).mpr ?_, ?_⟩
    · rw [← (hBuv.spouse m).1, ← hBuv.womanSpouse w, ← hc.1, ← hc.2]
      exact (reverseEligible_profileOfScores_iff hu B w m).mp he
    · rwa [← hc.2, ← huv.womanSpouse w]
  exact ⟨transport h hB hx hy hAx, transport h.symm hB.symm hy hx hAy⟩

/-- The reverse successor of a changed woman is already determined by
the earlier full forward reveal. Her former husband is a reverse-eligible
fallback, so only pairs at least as attractive to her need to be tested. -/
theorem FullForwardRevealAgrees.reverseSuccessor_iff_of_changed (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {w : Fin n} (hw : B.symm w ≠ A.symm w) (m : Fin n) :
    IsSuccessor (swapProfile (profileOfScores x)) B.symm w m ↔
      IsSuccessor (swapProfile (profileOfScores y)) B.symm w m := by
  obtain ⟨hBy, hABy, hB⟩ := h.later hx hy hAx hAy hBx hAB
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hBuv : FullForwardRevealAgrees u v B)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hAu : IsStable (profileOfScores u) A) (hAv : IsStable (profileOfScores v) A)
      (hBu : IsStable (profileOfScores u) B)
      (hABu : MenWeaklyPrefer (profileOfScores u) A B)
      (hs : IsSuccessor (swapProfile (profileOfScores u)) B.symm w m) :
      IsSuccessor (swapProfile (profileOfScores v)) B.symm w m := by
    have hAu' := (isStable_profileOfScores_iff hu A).mp hAu
    have hAv' := (isStable_profileOfScores_iff hv A).mp hAv
    let eqPrefix := huv.reverseSearchPrefix_iff hBuv hu hv hAu' hAv' w
    have hb := (rankPermutation_le_iff_of_injective (hu (.inr w)) _ _).mp
      (hs.min_rank _ (reverseEligible_anchorHusband_of_changed hu hAu hBu hABu hw))
    obtain ⟨he, hm⟩ := (eqPrefix m).mp ⟨hs.eligible, hb⟩
    refine ⟨he, fun m' hm' ↦ ?_⟩
    apply (rankPermutation_le_iff_of_injective (hv (.inr w)) _ _).mpr
    by_cases hl : v (.inr w) m' ≤ v (.inr w) (A.symm w)
    · obtain ⟨he', hb'⟩ := (eqPrefix m').mpr ⟨hm', hl⟩
      have hscore := (rankPermutation_le_iff_of_injective (hu (.inr w)) _ _).mp
        (hs.min_rank m' he')
      rw [← (huv.pair_agrees_of_woman_le hu hAu' hb).2,
        ← (huv.pair_agrees_of_woman_le hu hAu' hb').2]
      exact hscore
    · exact hm.trans (le_of_not_ge hl)
  exact ⟨transport h hB hx hy hAx hAy hBx hAB,
    transport h.symm hB.symm hy hx hAy hAx hBy hABy⟩

/-- The score pair of the reverse successor of a changed woman was already
fully observed at the earlier anchor. -/
theorem FullForwardRevealAgrees.reverseSuccessor_pair_agrees_of_changed
    (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row))
    (hAx : IsStable (profileOfScores x) A) (hBx : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {w m : Fin n} (hw : B.symm w ≠ A.symm w)
    (hs : IsSuccessor (swapProfile (profileOfScores x)) B.symm w m) :
    ScorePairAgrees x y m w :=
  h.pair_agrees_of_woman_le hx ((isStable_profileOfScores_iff hx A).mp hAx) <|
    (rankPermutation_le_iff_of_injective (hx (.inr w)) _ _).mp
      (hs.min_rank _ (reverseEligible_anchorHusband_of_changed hx hAx hBx hAB hw))

/-- A reverse permutation supported on changed women is realized in one
array exactly when it is realized in the other. -/
theorem FullForwardRevealAgrees.reversePermutation_iff_of_changed (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    (σ : Matching n) (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w) :
    RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ ↔
      RealizesSuccessorPermutation (swapProfile (profileOfScores y)) B.symm σ := by
  constructor
  · intro hs w hw
    exact (h.reverseSuccessor_iff_of_changed hx hy hAx hAy hBx hAB
      (hchanged w hw) _).mp (hs w hw)
  · intro hs w hw
    exact (h.reverseSuccessor_iff_of_changed hx hy hAx hAy hBx hAB
      (hchanged w hw) _).mpr (hs w hw)

/-- The women's undo-endpoint spouse scores agree for a reverse permutation
supported on women who changed since the earlier anchor. -/
theorem FullForwardRevealAgrees.undo_femaleSpouse_agrees_of_changed
    (h : FullForwardRevealAgrees x y A) (hB : FullForwardRevealAgrees x y B)
    (hx : ∀ row, Function.Injective (x row))
    (hAx : IsStable (profileOfScores x) A) (hBx : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B) {σ : Matching n}
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w) (w : Fin n) :
    femaleSpouseScore x (undoReverseRotation B σ) w =
      femaleSpouseScore y (undoReverseRotation B σ) w := by
  simp only [femaleSpouseScore, undoReverseRotation_symm_apply]
  by_cases hw : w ∈ σ.support
  · exact (h.reverseSuccessor_pair_agrees_of_changed hx hAx hBx hAB
      (hchanged w hw) (hσ w hw)).2
  · rw [Equiv.Perm.notMem_support.mp hw]
    exact hB.womanSpouse w

private theorem FullForwardRevealAgrees.crossRectangle_of_changed
    (h : FullForwardRevealAgrees x y A) (hB : FullForwardRevealAgrees x y B)
    (hx : ∀ row, Function.Injective (x row))
    (hAx : IsStable (profileOfScores x) A) (hBx : IsStable (profileOfScores x) B)
    (hAB : MenWeaklyPrefer (profileOfScores x) A B) {ρ σ : Matching n}
    (hρ : IsExposedRotation (profileOfScores x) B ρ)
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w) {m w : Fin n}
    (hc : IsPivotCrossRectangle x B (undoReverseRotation B σ) ρ m w) :
    IsPivotCrossRectangle y B (undoReverseRotation B σ) ρ m w := by
  have hw : w ∈ σ.support := Equiv.Perm.mem_support.mpr fun he ↦
    hc.2.1 (by rw [undoReverseRotation_symm_apply, he])
  have hf : x (.inr w) ((undoReverseRotation B σ).symm w) ≤ x (.inr w) (A.symm w) := by
    rw [undoReverseRotation_symm_apply]
    exact (rankPermutation_le_iff_of_injective (hx (.inr w)) _ _).mp
      ((hσ w hw).min_rank _
        (reverseEligible_anchorHusband_of_changed hx hAx hBx hAB (hchanged w hw)))
  have hp := h.pair_agrees_of_woman_le hx ((isStable_profileOfScores_iff hx A).mp hAx)
    (hc.2.2.2.2.2.le.trans hf)
  have ht := hB.cell m (B (ρ m)) <|
    (isEligibleSuccessor_profileOfScores_iff hx B m _).mp (hρ.successor m hc.1).eligible
  have hN := h.undo_femaleSpouse_agrees_of_changed hB hx hAx hBx hAB hσ hchanged w
  simp only [femaleSpouseScore] at hN
  simpa only [IsPivotCrossRectangle, (hB.spouse m).1, hp.1, ht.1, hB.womanSpouse w,
    hp.2, hN] using hc

/-- Compatibility with the later forward pivot is replayable for a reverse
collection supported on changed women and disjoint from that pivot. -/
theorem FullForwardRevealAgrees.undo_compatible_iff_of_changed
    (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {ρ σ : Matching n} (hρ : IsExposedRotation (profileOfScores x) B ρ)
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) B.symm σ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w)
    (hdisj : ∀ m ∈ ρ.support, B m ∉ σ.support) :
    IsExposedRotation (profileOfScores x) (undoReverseRotation B σ) ρ ↔
      IsExposedRotation (profileOfScores y) (undoReverseRotation B σ) ρ := by
  obtain ⟨hBy, hABy, hB⟩ := h.later hx hy hAx hAy hBx hAB
  have hρy := (hB.exposedRotation_iff hx hy ρ).mp hρ
  have hσy := (h.reversePermutation_iff_of_changed hx hy hAx hAy hBx hAB σ hchanged).mp hσ
  have hfixed (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation B σ m = B m :=
    undoReverseRotation_apply_of_not_mem_support (hdisj m (Equiv.Perm.mem_support.mpr hm))
  rw [isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hx hρ
    ((isStable_profileOfScores_iff hx _).mp (hσ.undo_stable hBx)) hfixed,
    isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hy hρy
      ((isStable_profileOfScores_iff hy _).mp (hσy.undo_stable hBy)) hfixed]
  exact ⟨fun he m w hc ↦ he m w
      (h.symm.crossRectangle_of_changed hB.symm hy hAy hBy hABy hρy hσy hchanged hc),
    fun he m w hc ↦ he m w (h.crossRectangle_of_changed hB hx hAx hBx hAB hρ hσ hchanged hc)⟩

/-- Replaying the later reveal determines membership of a candidate supported
entirely on changed women in the later filtered decoration family. -/
theorem FullForwardRevealAgrees.mem_filteredReverseSupportFamily_iff_of_changed
    (h : FullForwardRevealAgrees x y A)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B)
    {ρ σ : Matching n} (hρ : IsExposedRotation (profileOfScores x) B ρ)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w)
    (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) :
    σ ∈ filteredReverseSupportFamily B ρ flag k L t x ↔
      σ ∈ filteredReverseSupportFamily B ρ flag k L t y := by
  obtain ⟨hBy, hABy, hB⟩ := h.later hx hy hAx hAy hBx hAB
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (hBuv : FullForwardRevealAgrees u v B)
      (hu : ∀ row, Function.Injective (u row)) (hv : ∀ row, Function.Injective (v row))
      (hAu : IsStable (profileOfScores u) A) (hAv : IsStable (profileOfScores v) A)
      (hBu : IsStable (profileOfScores u) B) (hABu : MenWeaklyPrefer (profileOfScores u) A B)
      (hρu : IsExposedRotation (profileOfScores u) B ρ)
      (hmem : σ ∈ filteredReverseSupportFamily B ρ flag k L t u) :
      σ ∈ filteredReverseSupportFamily B ρ flag k L t v := by
    simp only [filteredReverseSupportFamily, Finset.mem_filter, compatibleReverseSupportFamily,
      mem_compatibleReversePermutations] at hmem ⊢
    rcases hmem with ⟨⟨hcand, hreal, hcompat⟩, hcap, hinc⟩
    have hdisj (m : Fin n) (hm : m ∈ ρ.support) : B m ∉ σ.support := fun hw ↦
      ((mem_goodReverseSupportPermutations.mp hcand).2 _ hw).1
        (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
    refine ⟨⟨hcand, (huv.reversePermutation_iff_of_changed hu hv hAu hAv hBu hABu
      σ hchanged).mp hreal, (huv.undo_compatible_iff_of_changed hu hv hAu hAv hBu hABu
      hρu hreal hchanged hdisj).mp hcompat⟩, hcap, ?_⟩
    intro w hw
    have hp := huv.reverseSuccessor_pair_agrees_of_changed hu hAu hBu hABu
      (hchanged w hw) (hreal w hw)
    simpa only [reverseScoreIncrement, hp.2, hBuv.womanSpouse w] using hinc w hw
  exact ⟨transport h hB hx hy hAx hAy hBx hAB hρ,
    transport h.symm hB.symm hy hx hAy hAx hBy hABy
      ((hB.exposedRotation_iff hx hy ρ).mp hρ)⟩

/-- Equality of the spouse diagonal follows from agreement of spouse pairs. -/
theorem FullForwardRevealAgrees.diagonal_eq (h : FullForwardRevealAgrees x y A) :
    (splitScorePairs A x).1 = (splitScorePairs A y).1 := by
  funext q
  have he : q = ⟨(q.val.1, q.val.1), rfl⟩ :=
    Subtype.ext (Prod.ext rfl q.property.symm)
  rw [he]
  change diagonalPairAt (splitScorePairs A x).1 q.val.1 =
    diagonalPairAt (splitScorePairs A y).1 q.val.1
  rw [diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs]
  exact Prod.ext (h.spouse _).1 (h.spouse _).2

/-- The forward flag for an off-diagonal coordinate is its score eligibility test. -/
theorem forwardMaskOfScores_eq_true_iff (x : ScoreProfile n) (A : Matching n)
    (q : OffDiagonalCellIndex n) :
    forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true ↔
      ScoreForwardEligible x A q.val.1 (A q.val.2) := by
  rw [forwardMaskOfScores, forwardCellFlag_eq_true, splitScorePairs_offDiagonal_apply,
    diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs]
  simp only [forwardEligibleScoreCell, Set.mem_prod, Set.mem_Ioi, Set.mem_Iio,
    ScoreForwardEligible, Equiv.symm_apply_apply]

/-- Equality of the full forward reveal gives the same active mask. -/
theorem FullForwardRevealAgrees.mask_eq (h : FullForwardRevealAgrees x y A) :
    forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 =
      forwardMaskOfScores (splitScorePairs A y).1 (splitScorePairs A y).2 := by
  funext q
  apply Bool.eq_iff_iff.mpr
  exact (forwardMaskOfScores_eq_true_iff x A q).trans
    ((h.eligible_iff q.val.1 (A q.val.2)).trans (forwardMaskOfScores_eq_true_iff y A q).symm)

/-- On the common mask, both scores are equal at each active coordinate. -/
theorem FullForwardRevealAgrees.active_pair_eq (h : FullForwardRevealAgrees x y A)
    (flag : OffDiagonalCellIndex n → Bool)
    (hflag : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 = flag)
    (q : ForwardActiveCellIndex flag) :
    (splitScorePairs A x).2 q.val = (splitScorePairs A y).2 q.val := by
  have he : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q.val = true := by
    rw [hflag]
    exact q.property
  have hp := h.cell _ _ ((forwardMaskOfScores_eq_true_iff x A q.val).mp he)
  rw [splitScorePairs_offDiagonal_apply, splitScorePairs_offDiagonal_apply]
  exact Prod.ext hp.1 hp.2

/-- Agreement at a mark preserves the local singleton-eligibility test. -/
theorem FullForwardRevealAgrees.locallyEligible_iff (h : FullForwardRevealAgrees x y A)
    (b a c : ℝ) (ρ : Matching n) :
    IsLocallyEligiblePivot b a c x A ρ ↔ IsLocallyEligiblePivot b a c y A ρ := by
  let flag := forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2
  let Test (d : DiagonalScorePairs n) (v : ForwardRevealedMaleScores flag) : Prop :=
    LocalPivotGeometry b a c A ρ d flag ∧
      v ∈ eligiblePivotRevealSet d flag ρ (localPivotIncrementCap c d)
  have hm : (forwardRevealWithColumns flag (splitScorePairs A x).2).1 =
      (forwardRevealWithColumns flag (splitScorePairs A y).2).1 :=
    funext fun q ↦ congrArg Prod.fst (h.active_pair_eq flag rfl q)
  have hx : IsLocallyEligiblePivot b a c x A ρ ↔
      Test (splitScorePairs A x).1 (forwardRevealWithColumns flag (splitScorePairs A x).2).1 :=
    Iff.rfl
  have hy : IsLocallyEligiblePivot b a c y A ρ ↔
      Test (splitScorePairs A y).1 (forwardRevealWithColumns flag (splitScorePairs A y).2).1 := by
    unfold IsLocallyEligiblePivot
    dsimp only
    rw [← h.mask_eq]
  rw [hx, hy, hm, h.diagonal_eq]

/-- Coordinatewise agreement is exactly equality of the enlarged reveal. -/
theorem fullForwardRevealAgrees_iff_pivotFullReveal_eq
    {x y : ScoreProfile n} {A : Matching n} :
    FullForwardRevealAgrees x y A ↔ pivotFullReveal A x = pivotFullReveal A y := by
  constructor
  · intro h
    unfold pivotFullReveal pivotFullRevealFromScores pivotMaleRevealFromScores
    dsimp only
    refine Prod.ext (Prod.ext h.diagonal_eq (Prod.ext h.mask_eq ?_)) ?_
    · funext q
      rw [← h.mask_eq]
      dsimp only
      split
      · rename_i hq
        exact congrArg Prod.fst (h.active_pair_eq _ rfl ⟨q, hq⟩)
      · rfl
    · funext q
      rw [← h.mask_eq]
      dsimp only
      split
      · rename_i hq
        exact congrArg Prod.snd (h.active_pair_eq _ rfl ⟨q, hq⟩)
      · rfl
  · intro h
    have hd : (splitScorePairs A x).1 = (splitScorePairs A y).1 :=
      congrArg (fun z : PivotFullRevealData n ↦ z.1.1) h
    have hm : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 =
        forwardMaskOfScores (splitScorePairs A y).1 (splitScorePairs A y).2 :=
      congrArg (fun z : PivotFullRevealData n ↦ z.1.2.1) h
    have hp (q : OffDiagonalCellIndex n)
        (hq : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true) :
        (splitScorePairs A x).2 q = (splitScorePairs A y).2 q := by
      have hqy : forwardMaskOfScores (splitScorePairs A y).1 (splitScorePairs A y).2 q = true := by
        rwa [← hm]
      apply Prod.ext
      · have he := congrArg (fun z : PivotFullRevealData n ↦ z.1.2.2 q) h
        simpa only [pivotFullReveal, pivotFullRevealFromScores, pivotMaleRevealFromScores,
          hq, hqy, ite_true] using he
      · have he := congrArg (fun z : PivotFullRevealData n ↦ z.2 q) h
        simpa only [pivotFullReveal, pivotFullRevealFromScores, hq, hqy, ite_true] using he
    have hindex (m w : Fin n) (hne : A m ≠ w) : m ≠ A.symm w := fun he ↦
      hne (((Equiv.symm_apply_eq A).mp he.symm).symm)
    refine ⟨fun m ↦ ?_, fun m w ↦ ?_, fun m w he ↦ ?_⟩
    · have he := congrArg (fun d ↦ diagonalPairAt d m) hd
      rw [diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs] at he
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
    · by_cases he : A m = w
      · subst w
        simp only [ScoreForwardEligible, lt_self_iff_false, false_and]
      · let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), hindex m w he⟩
        have hq : A q.val.2 = w := A.apply_symm_apply w
        have hx := forwardMaskOfScores_eq_true_iff x A q
        have hy := forwardMaskOfScores_eq_true_iff y A q
        rw [hq] at hx hy
        rw [← hx, ← hy, hm]
    · have hne : A m ≠ w := fun hmw ↦ he.1.ne (congrArg (x (.inl m)) hmw)
      let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), hindex m w hne⟩
      have hq : A q.val.2 = w := A.apply_symm_apply w
      have hx := forwardMaskOfScores_eq_true_iff x A q
      rw [hq] at hx
      have hpair := hp q (hx.mpr he)
      rw [splitScorePairs_offDiagonal_apply, splitScorePairs_offDiagonal_apply, hq] at hpair
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- Equality of the enlarged reveal at a common stable anchor transfers
later stability, the order from the anchor, and the enlarged reveal there. -/
theorem pivotFullReveal_replay_later {x y : ScoreProfile n} {A B : Matching n}
    (h : pivotFullReveal A x = pivotFullReveal A y)
    (hx : ∀ row, Function.Injective (x row)) (hy : ∀ row, Function.Injective (y row))
    (hAx : IsStable (profileOfScores x) A) (hAy : IsStable (profileOfScores y) A)
    (hBx : IsStable (profileOfScores x) B) (hAB : MenWeaklyPrefer (profileOfScores x) A B) :
    IsStable (profileOfScores y) B ∧ MenWeaklyPrefer (profileOfScores y) A B ∧
      pivotFullReveal B x = pivotFullReveal B y := by
  obtain ⟨hBy, hABy, hB⟩ :=
    (fullForwardRevealAgrees_iff_pivotFullReveal_eq.mpr h).later hx hy hAx hAy hBx hAB
  exact ⟨hBy, hABy, fullForwardRevealAgrees_iff_pivotFullReveal_eq.mp hB⟩

private theorem ne_inverse_of_ne_partner {A : Matching n} {m w : Fin n} (h : A m ≠ w) :
    m ≠ A.symm w :=
  fun he ↦ h (((Equiv.symm_apply_eq A).mp he.symm).symm)

private def fullRevealCompletionPair (A : Matching n) (R : PivotFullRevealData n) (m w : Fin n) :
    ℝ × ℝ :=
  if h : A m = w then diagonalPairAt R.1.1 m
  else
    let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner h⟩
    if R.1.2.1 q = true then (R.1.2.2 q, R.2 q) else (2 + (A.symm w).val, 2 + m.val)

/-- Reconstruct a score array from the enlarged reveal, filling inactive cells
with distinct large scores. The completion is not meant to have the original law. -/
@[no_expose]
def pivotFullRevealCompletion (A : Matching n) (R : PivotFullRevealData n) : ScoreProfile n :=
  fun row i ↦ match row with
    | .inl m => (fullRevealCompletionPair A R m i).1
    | .inr w => (fullRevealCompletionPair A R i w).2

private theorem measurable_fullRevealCompletionPair (A : Matching n) (m w : Fin n) :
    Measurable (fun R : PivotFullRevealData n ↦ fullRevealCompletionPair A R m w) := by
  by_cases h : A m = w
  · simp only [fullRevealCompletionPair, dite_eq_left h]
    exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)
  · let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner h⟩
    simp only [fullRevealCompletionPair, dite_eq_right h]
    have hflag : Measurable (fun R : PivotFullRevealData n ↦ R.1.2.1 q) :=
      (measurable_pi_apply q).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
    have hmale : Measurable (fun R : PivotFullRevealData n ↦ R.1.2.2 q) :=
      (measurable_pi_apply q).comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hfemale : Measurable (fun R : PivotFullRevealData n ↦ R.2 q) :=
      (measurable_pi_apply q).comp measurable_snd
    exact Measurable.ite (measurableSet_eq_fun hflag measurable_const)
      (hmale.prodMk hfemale) measurable_const

theorem measurable_pivotFullRevealCompletion (A : Matching n) :
    Measurable (pivotFullRevealCompletion A) := by
  refine Measurable.of_eval fun r ↦ Measurable.of_eval fun i ↦ ?_
  cases r with
  | inl m => exact (measurable_fullRevealCompletionPair A m i).fst
  | inr w => exact (measurable_fullRevealCompletionPair A i w).snd

/-- Evaluating the completion on the actual reveal is measurable with
respect to the enlarged reveal sigma algebra. -/
theorem measurable_pivotFullRevealCompletion_from_reveal (A : Matching n) :
    Measurable[pivotFullRevealSpace A]
      (fun x ↦ pivotFullRevealCompletion A (pivotFullReveal A x)) :=
  (measurable_pivotFullRevealCompletion A).comp
    (comap_measurable (pivotFullReveal A))

private theorem fullRevealCompletionPair_of_observed (A : Matching n) (x : ScoreProfile n)
    (m w : Fin n) (h : A m = w ∨ ScoreForwardEligible x A m w) :
    fullRevealCompletionPair A (pivotFullReveal A x) m w =
      (x (.inl m) w, x (.inr w) m) := by
  by_cases hmw : A m = w
  · subst w
    rw [fullRevealCompletionPair, dite_eq_left rfl]
    exact diagonalPairAt_splitScorePairs A x m
  · let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner hmw⟩
    have hq : A q.val.2 = w := A.apply_symm_apply w
    have hflag : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true :=
      (forwardMaskOfScores_eq_true_iff x A q).mpr (hq.symm ▸ h.resolve_left hmw)
    have hp := splitScorePairs_offDiagonal_apply A x q
    rw [hq] at hp
    rw [fullRevealCompletionPair, dite_eq_right hmw]
    change (if forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true
      then ((pivotFullReveal A x).1.2.2 q, (pivotFullReveal A x).2 q) else _) = _
    simp only [pivotFullReveal, pivotFullRevealFromScores, pivotMaleRevealFromScores,
      hflag, ite_true]
    exact hp

private theorem fullRevealCompletionPair_of_inactive (A : Matching n) (x : ScoreProfile n)
    (m w : Fin n) (h : ¬ (A m = w ∨ ScoreForwardEligible x A m w)) :
    fullRevealCompletionPair A (pivotFullReveal A x) m w =
      ((2 : ℝ) + (A.symm w).val, (2 : ℝ) + m.val) := by
  have hmw : A m ≠ w := fun he ↦ h (Or.inl he)
  let q : OffDiagonalCellIndex n := ⟨(m, A.symm w), ne_inverse_of_ne_partner hmw⟩
  have hq : A q.val.2 = w := A.apply_symm_apply w
  have hflag : forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q ≠ true :=
    fun he ↦ h (Or.inr (hq ▸ (forwardMaskOfScores_eq_true_iff x A q).mp he))
  rw [fullRevealCompletionPair, dite_eq_right hmw]
  change (if forwardMaskOfScores (splitScorePairs A x).1 (splitScorePairs A x).2 q = true
    then ((pivotFullReveal A x).1.2.2 q, (pivotFullReveal A x).2 q) else _) = _
  rw [ite_eq_right hflag]

private theorem injective_row_of_filling {u v : Fin n → ℝ} {P : Fin n → Prop}
    (f : Fin n → Fin n) (hf : Function.Injective f) (hu : Function.Injective u)
    (hsmall : ∀ i, u i < 1) (hseen : ∀ i, P i → v i = u i)
    (hfill : ∀ i, ¬ P i → v i = 2 + (f i).val) : Function.Injective v := by
  intro i j he
  by_cases hi : P i <;> by_cases hj : P j
  · exact hu ((hseen i hi).symm.trans (he.trans (hseen j hj)))
  · have hlt := hsmall i
    rw [hseen i hi, hfill j hj] at he
    have hnon : 0 ≤ ((f j).val : ℝ) := Nat.cast_nonneg _
    linarith
  · have hlt := hsmall j
    rw [hfill i hi, hseen j hj] at he
    have hnon : 0 ≤ ((f i).val : ℝ) := Nat.cast_nonneg _
    linarith
  · rw [hfill i hi, hfill j hj] at he
    exact hf (Fin.ext (by exact_mod_cast (add_left_cancel he)))

/-- A genuine tie-free reveal from scores below one has a stable, tie-free
representative with exactly the same enlarged reveal. -/
theorem pivotFullRevealCompletion_spec {x : ScoreProfile n} {A : Matching n}
    (hx : ∀ row, Function.Injective (x row)) (hu : ∀ r i, x r i < 1) :
    let y := pivotFullRevealCompletion A (pivotFullReveal A x)
    (∀ row, Function.Injective (y row)) ∧ IsStable (profileOfScores y) A ∧
      FullForwardRevealAgrees x y A := by
  dsimp only
  let R := pivotFullReveal A x
  let y := pivotFullRevealCompletion A R
  let P (m w : Fin n) := A m = w ∨ ScoreForwardEligible x A m w
  have hseen (m w : Fin n) (h : P m w) : ScorePairAgrees x y m w := by
    have h' := fullRevealCompletionPair_of_observed A x m w h
    exact ⟨(congrArg Prod.fst h').symm, (congrArg Prod.snd h').symm⟩
  have hfill (m w : Fin n) (h : ¬ P m w) :
      y (.inl m) w = 2 + (A.symm w).val ∧ y (.inr w) m = 2 + m.val := by
    have h' := fullRevealCompletionPair_of_inactive A x m w h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hsp (m : Fin n) := hseen m (A m) (Or.inl rfl)
  have hwsp (w : Fin n) : x (.inr w) (A.symm w) = y (.inr w) (A.symm w) := by
    simpa only [A.apply_symm_apply] using (hsp (A.symm w)).2
  have hytie (r : Fin n ⊕ Fin n) : Function.Injective (y r) := by
    cases r with
    | inl m =>
      exact injective_row_of_filling (P := P m) A.symm A.symm.injective (hx (.inl m))
        (hu (.inl m)) (fun w hw ↦ (hseen m w hw).1.symm) (fun w hw ↦ (hfill m w hw).1)
    | inr w =>
      exact injective_row_of_filling (P := fun m ↦ P m w) id Function.injective_id (hx (.inr w))
        (hu (.inr w)) (fun m hm ↦ (hseen m w hm).2.symm) (fun m hm ↦ (hfill m w hm).2)
  have hinactive (m w : Fin n) (hn : ¬ P m w) :
      ¬ y (.inr w) m < y (.inr w) (A.symm w) := by
    rw [(hfill m w hn).2, ← hwsp w]
    have hnon : 0 ≤ (m.val : ℝ) := Nat.cast_nonneg _
    linarith [hu (.inr w) (A.symm w)]
  have helig (m w : Fin n) (he : ScoreForwardEligible x A m w) :
      ScoreForwardEligible y A m w := by
    have hp := hseen m w (Or.inr he)
    constructor
    · rw [← (hsp m).1, ← hp.1]
      exact he.1
    · rw [← hwsp w, ← hp.2]
      exact he.2
  refine ⟨hytie, (isStable_profileOfScores_iff hytie A).mpr ?_,
    ⟨hsp, ?_, fun m w he ↦ hseen m w (Or.inr he)⟩⟩
  · intro m w hb
    by_cases he : ScoreForwardEligible x A m w
    · exact (helig m w he).1.not_gt hb.2.1
    · exact hinactive m w (fun h ↦ h.elim hb.1 he) hb.2.2
  · intro m w
    refine ⟨helig m w, fun he ↦ ?_⟩
    have hne : A m ≠ w := fun hh ↦ he.1.ne (congrArg (y (.inl m)) hh)
    by_contra hn
    exact hinactive m w (fun h ↦ h.elim hne hn) he.2

/-- At a stable anchor, the enlarged reveal decides the later eligibility
and moved-women filtered-candidate test by evaluation on its completion. -/
theorem pivotFullRevealCompletion_later_filtered_iff
    {x : ScoreProfile n} {A B ρ σ : Matching n}
    (hx : ∀ row, Function.Injective (x row)) (hu : ∀ r i, x r i < 1)
    (hA : IsStable (profileOfScores x) A)
    (hchanged : ∀ w ∈ σ.support, B.symm w ≠ A.symm w)
    (b a c : ℝ) (flag : OffDiagonalCellIndex n → Bool) (k L : ℕ) (t : ℝ) :
    let y := pivotFullRevealCompletion A (pivotFullReveal A x)
    (IsStable (profileOfScores x) B ∧ MenWeaklyPrefer (profileOfScores x) A B ∧
      IsLocallyEligiblePivot b a c x B ρ ∧
      σ ∈ filteredReverseSupportFamily B ρ flag k L t x) ↔
    (IsStable (profileOfScores y) B ∧ MenWeaklyPrefer (profileOfScores y) A B ∧
      IsLocallyEligiblePivot b a c y B ρ ∧
      σ ∈ filteredReverseSupportFamily B ρ flag k L t y) := by
  dsimp only
  obtain ⟨hy, hAy, h⟩ := pivotFullRevealCompletion_spec (A := A) hx hu
  have transport {u v : ScoreProfile n} (huv : FullForwardRevealAgrees u v A)
      (htu : ∀ row, Function.Injective (u row)) (htv : ∀ row, Function.Injective (v row))
      (hAu : IsStable (profileOfScores u) A) (hAv : IsStable (profileOfScores v) A) :
      (IsStable (profileOfScores u) B ∧ MenWeaklyPrefer (profileOfScores u) A B ∧
        IsLocallyEligiblePivot b a c u B ρ ∧
        σ ∈ filteredReverseSupportFamily B ρ flag k L t u) →
      (IsStable (profileOfScores v) B ∧ MenWeaklyPrefer (profileOfScores v) A B ∧
        IsLocallyEligiblePivot b a c v B ρ ∧
        σ ∈ filteredReverseSupportFamily B ρ flag k L t v) := by
    rintro ⟨hBu, hAB, hloc, hmem⟩
    obtain ⟨hBv, hABv, hB⟩ := huv.later htu htv hAu hAv hBu hAB
    exact ⟨hBv, hABv, (hB.locallyEligible_iff b a c ρ).mp hloc,
      (huv.mem_filteredReverseSupportFamily_iff_of_changed htu htv hAu hAv hBu hAB
        (hloc.isSoleForwardExposed htu).1 hchanged flag k L t).mp hmem⟩
  exact ⟨transport h hx hy hA hAy, transport h.symm hy hx hAy hA⟩

/-- The test evaluated on the canonical completion is measurable in the
enlarged reveal. The replay theorem identifies it with the actual test
on stable, tie-free score arrays whenever the support uses changed women. -/
theorem measurableSet_pivotFullRevealCompletion_later_filtered
    (A B ρ σ : Matching n) (b a c : ℝ) (flag : OffDiagonalCellIndex n → Bool)
    (k L : ℕ) (t : ℝ) :
    MeasurableSet[pivotFullRevealSpace A] {x : ScoreProfile n |
      let y := pivotFullRevealCompletion A (pivotFullReveal A x)
      IsStable (profileOfScores y) B ∧ MenWeaklyPrefer (profileOfScores y) A B ∧
        IsLocallyEligiblePivot b a c y B ρ ∧
        σ ∈ filteredReverseSupportFamily B ρ flag k L t y} := by
  have hstable : MeasurableSet {y : ScoreProfile n | IsStable (profileOfScores y) B} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsStable p B})
  have horder : MeasurableSet {y : ScoreProfile n | MenWeaklyPrefer (profileOfScores y) A B} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | MenWeaklyPrefer p A B})
  have hfamily : MeasurableSet {y : ScoreProfile n |
      σ ∈ filteredReverseSupportFamily B ρ flag k L t y} := by
    simp only [filteredReverseSupportFamily, Finset.mem_filter, ofPred_and]
    exact ((measurable_profileOfScores n) (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | σ ∈ compatibleReverseSupportFamily B ρ flag k p})).inter
        ((MeasurableSet.const _).inter (measurableSet_reverseCollectionIncrementGood B σ t))
  exact measurable_pivotFullRevealCompletion_from_reveal A
    (hstable.inter (horder.inter ((measurableSet_isLocallyEligiblePivot b a c B ρ).inter hfamily)))

end LennonPittelFormalization

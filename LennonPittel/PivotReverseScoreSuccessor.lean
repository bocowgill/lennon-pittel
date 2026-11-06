module

public import LennonPittel.PivotReverseRowLaw
public import LennonPittel.ReverseSuccessorRotation

/-!
# Reverse successor tests in the actual score array

Index each woman by her current husband. At a stable tie-free score array,
a reverse successor must lie in the inactive part of that woman's column.
Its rank minimality implies the corresponding inactive-column score test.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The reverse successor rank test implies the inactive-column event,
with original men as the target indices. -/
theorem exists_reverseSuccessorColumnEvent_of_isSuccessor {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (hs : IsScoreStable x μ) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hji : j ≠ i)
    (hj : IsSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) j) :
    ∃ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j ∧
      (forwardInactiveColumnsEquiv flag (fun q ↦ (splitScorePairs μ x).2 q.val)) i ∈
        reverseSuccessorColumnEvent (diagonalPairAt (splitScorePairs μ x).1 i).2
          (fun k ↦ (diagonalPairAt (splitScorePairs μ x).1 k.val.val.val.1).1) q := by
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  let a : OffDiagonalCellIndex n := ⟨(j, i), hji⟩
  have hmale (m : Fin n) (w w' : Fin n) :
      (profileOfScores x).manRank m w < (profileOfScores x).manRank m w' ↔
        x (.inl m) w < x (.inl m) w' := rankPermutation_lt_iff (ht (.inl m)) w w'
  have hfemale (m m' : Fin n) :
      (profileOfScores x).womanRank (μ i) m < (profileOfScores x).womanRank (μ i) m' ↔
        x (.inr (μ i)) m < x (.inr (μ i)) m' := rankPermutation_lt_iff (ht (.inr (μ i))) m m'
  have hmalej : x (.inl j) (μ i) < x (.inl j) (μ j) :=
    (hmale _ _ _).mp (by simpa only [swapProfile, Equiv.symm_symm] using hj.eligible.2)
  have hfemalej : x (.inr (μ i)) i < x (.inr (μ i)) j :=
    (hfemale _ _).mp (by simpa only [swapProfile, Equiv.symm_apply_apply] using hj.eligible.1)
  have ha : flag a ≠ true := by
    intro h
    have hh := mem_pi.mp hmask a (mem_univ _)
    change z a ∈ forwardScoreCellFlagEvent (diagonalPairAt d j).1
      (diagonalPairAt d i).2 (flag a) at hh
    dsimp only [z, d] at hh
    rw [h, forwardScoreCellFlagEvent, ite_eq_left rfl, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hh
    exact hmalej.not_gt (mem_prod.mp hh).1
  let q : ForwardInactiveColumnIndex flag i := ⟨⟨a, ha⟩, rfl⟩
  let col := (forwardInactiveColumnsEquiv flag (fun k ↦ z k.val)) i
  have hcell (k : ForwardInactiveColumnIndex flag i) :
      col k = (x (.inl k.val.val.val.1) (μ i), x (.inr (μ i)) k.val.val.val.1) := by
    change (splitScorePairs μ x).2 k.val.val = _
    rw [splitScorePairs_offDiagonal_apply, k.property]
  refine ⟨q, rfl, ?_⟩
  change col ∈ reverseSuccessorColumnEvent (diagonalPairAt d i).2
    (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q
  change (diagonalPairAt d i).2 < (col q).2 ∧
    (col q).1 < (diagonalPairAt d j).1 ∧
    ∀ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      ¬ ((col k.val).2 < (col q).2 ∧
        (col k.val).1 < (diagonalPairAt d k.val.val.val.val.1).1)
  simp only [hcell, d, diagonalPairAt_splitScorePairs, q, a]
  refine ⟨hfemalej, hmalej, fun k h ↦ ?_⟩
  let m := k.val.val.val.val.1
  have hne : m ≠ i := fun hm ↦ k.val.val.val.property (hm.trans k.val.property.symm)
  have hbetter : x (.inl m) (μ i) < x (.inl m) (μ m) := h.2
  have hnotbetter : ¬ x (.inr (μ i)) m < x (.inr (μ i)) i :=
    fun hh ↦ hs m (μ i) ⟨μ.injective.ne hne, hbetter,
      by simpa only [Equiv.symm_apply_apply] using hh⟩
  have hww : x (.inr (μ i)) i < x (.inr (μ i)) m :=
    lt_of_le_of_ne (le_of_not_gt hnotbetter) ((ht (.inr (μ i))).ne hne.symm)
  have hel : IsEligibleSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) m := by
    simpa only [IsEligibleSuccessor, swapProfile, Equiv.symm_apply_apply, Equiv.symm_symm] using
      And.intro ((hfemale _ _).mpr hww) ((hmale _ _ _).mpr hbetter)
  exact (not_lt_of_ge (hj.min_rank m hel)) ((hfemale _ _).mpr h.1)

/-- The column test for the arc from woman `i` to man `j`, with `i` indexed
by her husband. If the target is masked out, the event is empty. -/
def forwardInactiveReverseArcEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
  ⋃ q : {q : ForwardInactiveColumnIndex flag i // q.val.val.val.1 = j},
    reverseSuccessorColumnEvent (diagonalPairAt d i).2
      (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q.val

theorem measurableSet_forwardInactiveReverseArcEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) :
    MeasurableSet (forwardInactiveReverseArcEvent d flag i j) :=
  MeasurableSet.iUnion fun q ↦ measurableSet_reverseSuccessorColumnEvent _ _ q.val

/-- A stable tie-free score array has a given reverse rank successor exactly
when its inactive column passes the corresponding arc test. -/
theorem isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (hs : IsScoreStable x μ) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hji : j ≠ i) :
    IsSuccessor (swapProfile (profileOfScores x)) μ.symm (μ i) j ↔
      (forwardInactiveColumnsEquiv flag (fun q ↦ (splitScorePairs μ x).2 q.val)) i ∈
        forwardInactiveReverseArcEvent (splitScorePairs μ x).1 flag i j := by
  constructor
  · intro hj
    obtain ⟨q, hq, htest⟩ := exists_reverseSuccessorColumnEvent_of_isSuccessor
      μ x flag hs ht hmask i j hji hj
    exact mem_iUnion.mpr ⟨⟨q, hq⟩, htest⟩
  · intro h
    obtain ⟨q, hq⟩ := mem_iUnion.mp h
    let d := (splitScorePairs μ x).1
    let z := (splitScorePairs μ x).2
    let col := (forwardInactiveColumnsEquiv flag (fun k ↦ z k.val)) i
    have hcell (k : ForwardInactiveColumnIndex flag i) :
        col k = (x (.inl k.val.val.val.1) (μ i), x (.inr (μ i)) k.val.val.val.1) := by
      change (splitScorePairs μ x).2 k.val.val = _
      rw [splitScorePairs_offDiagonal_apply, k.property]
    change (diagonalPairAt d i).2 < (col q.val).2 ∧
      (col q.val).1 < (diagonalPairAt d q.val.val.val.val.1).1 ∧
      ∀ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q.val},
        ¬ ((col k.val).2 < (col q.val).2 ∧
          (col k.val).1 < (diagonalPairAt d k.val.val.val.val.1).1) at hq
    simp only [hcell, d, diagonalPairAt_splitScorePairs, q.property] at hq
    have hf (a b : Fin n) : (profileOfScores x).womanRank (μ i) a <
        (profileOfScores x).womanRank (μ i) b ↔ x (.inr (μ i)) a < x (.inr (μ i)) b :=
      rankPermutation_lt_iff (ht (.inr (μ i))) a b
    have hm (a : Fin n) : (profileOfScores x).manRank a (μ i) <
        (profileOfScores x).manRank a (μ a) ↔ x (.inl a) (μ i) < x (.inl a) (μ a) :=
      rankPermutation_lt_iff (ht (.inl a)) _ _
    refine ⟨?_, ?_⟩
    · simpa only [IsEligibleSuccessor, swapProfile, Equiv.symm_symm, Equiv.symm_apply_apply] using
        And.intro ((hf i j).mpr hq.1) ((hm j).mpr hq.2.1)
    · intro m hel
      change (profileOfScores x).womanRank (μ i) j ≤ (profileOfScores x).womanRank (μ i) m
      apply le_of_not_gt
      intro hlt
      have hsmall := (hf m j).mp hlt
      have hmale : x (.inl m) (μ i) < x (.inl m) (μ m) :=
        (hm m).mp (by simpa only [swapProfile, Equiv.symm_symm] using hel.2)
      have hmi : m ≠ i := fun e ↦ (lt_irrefl _ (e ▸ hmale))
      let a : OffDiagonalCellIndex n := ⟨(m, i), hmi⟩
      have ha : flag a ≠ true := by
        intro he
        have hh := mem_pi.mp hmask a (mem_univ _)
        change (splitScorePairs μ x).2 a ∈ forwardScoreCellFlagEvent
          (diagonalPairAt (splitScorePairs μ x).1 m).1
          (diagonalPairAt (splitScorePairs μ x).1 i).2 (flag a) at hh
        rw [he, forwardScoreCellFlagEvent, ite_eq_left rfl, forwardEligibleScoreCell,
          splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs] at hh
        exact hmale.not_gt (mem_prod.mp hh).1
      let k : ForwardInactiveColumnIndex flag i := ⟨⟨a, ha⟩, rfl⟩
      have hk : k ≠ q.val := fun he ↦ hsmall.ne
        (congrArg (fun b : ForwardInactiveColumnIndex flag i ↦
          x (.inr (μ i)) b.val.val.val.1) he |>.trans (congrArg (x (.inr (μ i))) q.property))
      exact hq.2.2 ⟨k, hk⟩ ⟨hsmall, hmale⟩

/-- A bound on the total competing mass yields the normalized upper bound
even when the designated target is unavailable. -/
theorem normalizedForwardInactiveColumnLaw_reverseArc_le {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n) {X a : ℝ}
    (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1)
    (hx : ∀ k, (diagonalPairAt d k).1 ∈ Icc 0 1) (hX : 0 < X) (ha : 0 < a)
    (hcomp : ∀ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j →
      X / a ≤ ∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
        (diagonalPairAt d k.val.val.val.val.1).1) :
    normalizedForwardInactiveColumnLaw d flag i (forwardInactiveReverseArcEvent d flag i j) ≤
      ENNReal.ofReal a * ENNReal.ofReal ((diagonalPairAt d j).1 / X) := by
  by_cases h : ∃ q : ForwardInactiveColumnIndex flag i, q.val.val.val.1 = j
  · obtain ⟨q, hq⟩ := h
    have he : forwardInactiveReverseArcEvent d flag i j =
        reverseSuccessorColumnEvent (diagonalPairAt d i).2
          (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q := by
      ext z
      change (z ∈ ⋃ q' : {q' : ForwardInactiveColumnIndex flag i // q'.val.val.val.1 = j},
        reverseSuccessorColumnEvent (diagonalPairAt d i).2
          (fun k ↦ (diagonalPairAt d k.val.val.val.1).1) q'.val) ↔ _
      rw [mem_iUnion]
      refine ⟨?_, fun hz ↦ ⟨⟨q, hq⟩, hz⟩⟩
      rintro ⟨q', hz⟩
      have hq' : q'.val = q := Subtype.ext (Subtype.ext (Subtype.ext
        (Prod.ext (q'.property.trans hq.symm) (q'.val.property.trans q.property.symm))))
      simpa only [hq'] using hz
    rw [he, ← hq]
    exact reverseSuccessorColumnEvent_mass_le q hy0 hy1 (fun k ↦ hx k.val.val.val.1)
      hX ha (hcomp q hq)
  · have he : forwardInactiveReverseArcEvent d flag i j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨q, _⟩ := mem_iUnion.mp hz
      exact h ⟨q.val, q.property⟩
    simp only [he, measure_empty, zero_le]

end LennonPittelFormalization

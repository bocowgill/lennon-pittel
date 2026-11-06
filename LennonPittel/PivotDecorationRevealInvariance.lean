module

public import LennonPittel.PivotMarkedDecorationCount

/-!
# Reverse decorations ignore active female scores

The diagonal, active male scores, and entire inactive cells determine the
filtered reverse family at a stable anchor. A reverse successor's female
score and each possible crossed-blocker female score lie above their
original spouse score, so neither can be in an active cell.
-/

@[expose] public section

open MeasureTheory Set StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {μ ρ σ : Matching n} {x y : ScoreProfile n}
  {flag : OffDiagonalCellIndex n → Bool}

/-- Two score arrays have the same diagonal and the same opened male
observations and inactive score columns at the mark. -/
structure SameReverseReveal (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x y : ScoreProfile n) : Prop where
  diagonal : (splitScorePairs μ x).1 = (splitScorePairs μ y).1
  observed : forwardRevealWithColumns flag (splitScorePairs μ x).2 =
    forwardRevealWithColumns flag (splitScorePairs μ y).2

theorem SameReverseReveal.symm (h : SameReverseReveal μ flag x y) :
    SameReverseReveal μ flag y x := ⟨h.diagonal.symm, h.observed.symm⟩

theorem SameReverseReveal.inactiveCell_eq (h : SameReverseReveal μ flag x y)
    (q : ForwardInactiveCellIndex flag) :
    (splitScorePairs μ x).2 q.val = (splitScorePairs μ y).2 q.val :=
  congrFun (congrFun (congrArg Prod.snd h.observed) q.val.val.2)
    (⟨q, rfl⟩ : ForwardInactiveColumnIndex flag q.val.val.2)

theorem SameReverseReveal.male_eq (h : SameReverseReveal μ flag x y) (m w : Fin n) :
    x (.inl m) w = y (.inl m) w := by
  by_cases hw : w = μ m
  · subst w
    simpa only [diagonalPairAt_splitScorePairs] using
      congrArg (fun d ↦ (diagonalPairAt d m).1) h.diagonal
  · let q : OffDiagonalCellIndex n :=
      ⟨(m, μ.symm w), fun he ↦ hw ((congrArg μ he).trans (μ.apply_symm_apply w)).symm⟩
    have hcell : ((splitScorePairs μ x).2 q).1 = ((splitScorePairs μ y).2 q).1 := by
      by_cases hq : flag q = true
      · exact congrFun (congrArg Prod.fst h.observed) (⟨q, hq⟩ : ForwardActiveCellIndex flag)
      · exact congrArg Prod.fst (h.inactiveCell_eq ⟨q, hq⟩)
    simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using hcell

theorem SameReverseReveal.female_spouse_eq (h : SameReverseReveal μ flag x y) (w : Fin n) :
    x (.inr w) (μ.symm w) = y (.inr w) (μ.symm w) := by
  simpa only [diagonalPairAt_splitScorePairs, Equiv.apply_symm_apply] using
    congrArg (fun d ↦ (diagonalPairAt d (μ.symm w)).2) h.diagonal

private theorem SameReverseReveal.female_eq_of_spouse_lt
    (h : SameReverseReveal μ flag x y)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (hw : x (.inr w) (μ.symm w) < x (.inr w) m) :
    x (.inr w) m = y (.inr w) m := by
  have hne : m ≠ μ.symm w := fun e ↦ hw.ne (congrArg (x (.inr w)) e.symm)
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q ≠ true := by
    intro he
    have hc := mem_pi.mp hmask q (mem_univ _)
    change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ x).1 m).1
      (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
    rw [he, forwardScoreCellFlagEvent, ite_eq_left rfl, forwardEligibleScoreCell,
      splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs] at hc
    exact hw.not_gt (by simpa only [q, Equiv.apply_symm_apply, mem_Iio] using (mem_prod.mp hc).2)
  simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using
    congrArg Prod.snd (h.inactiveCell_eq ⟨q, hq⟩)

private theorem SameReverseReveal.reverseSuccessor_iff (h : SameReverseReveal μ flag x y)
    (hsx : IsScoreStable x μ) (hsy : IsScoreStable y μ)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (w j : Fin n) (hj : j ≠ μ.symm w) :
    IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j ↔
      IsSuccessor (swapProfile (profileOfScores y)) μ.symm w j := by
  let i := μ.symm w
  have hcol := congrFun (congrArg Prod.snd h.observed) i
  have hx := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ x flag hsx htx hmx i j hj
  have hy := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent μ y flag hsy hty hmy i j hj
  change _ ↔ (forwardRevealWithColumns flag (splitScorePairs μ x).2).2 i ∈
    forwardInactiveReverseArcEvent (splitScorePairs μ x).1 flag i j at hx
  rw [hcol, h.diagonal] at hx
  simpa only [i, Equiv.apply_symm_apply] using hx.trans hy.symm

private theorem SameReverseReveal.forwardExposed_iff (h : SameReverseReveal μ flag x y)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔ IsExposedRotation (profileOfScores y) μ ρ := by
  rw [isExposedRotation_iff_forwardRevealExposureEvent μ ρ x flag htx hmx,
    isExposedRotation_iff_forwardRevealExposureEvent μ ρ y flag hty hmy, h.observed]

private theorem reverseScore_spouse_lt
    (ht : ∀ r, Function.Injective (x r))
    {w j : Fin n} (h : IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j) :
    x (.inr w) (μ.symm w) < x (.inr w) j :=
  (rankPermutation_lt_iff (ht (.inr w)) _ _).mp h.eligible.1

private theorem SameReverseReveal.crossRectangle
    (h : SameReverseReveal μ flag x y)
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (htx : ∀ r, Function.Injective (x r))
    (hσ : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
    {m w : Fin n}
    (hR : IsPivotCrossRectangle x μ (undoReverseRotation μ σ) ρ m w) :
    IsPivotCrossRectangle y μ (undoReverseRotation μ σ) ρ m w := by
  have hw : w ∈ σ.support := Equiv.Perm.mem_support.mpr fun he ↦
    hR.2.1 (by rw [undoReverseRotation_symm_apply, he])
  have hf := h.female_eq_of_spouse_lt hmx hR.2.2.2.2.1
  have hj := h.female_eq_of_spouse_lt hmx (reverseScore_spouse_lt htx (hσ w hw))
  unfold IsPivotCrossRectangle
  rw [← h.male_eq, ← h.male_eq, ← h.male_eq, ← h.female_spouse_eq, ← hf,
    undoReverseRotation_symm_apply, ← hj, ← undoReverseRotation_symm_apply]
  exact hR

/-- Filtered reverse support families are constant on the smaller reveal
and inactive columns, on stable, tie-free score profiles. -/
theorem filteredReverseSupportFamily_eq_of_same_forwardReveal
    (h : SameReverseReveal μ flag x y)
    (hsx : IsScoreStable x μ) (hsy : IsScoreStable y μ)
    (htx : ∀ r, Function.Injective (x r)) (hty : ∀ r, Function.Injective (y r))
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (hρx : IsExposedRotation (profileOfScores x) μ ρ) (k L : ℕ) (t : ℝ) :
    filteredReverseSupportFamily μ ρ flag k L t x =
      filteredReverseSupportFamily μ ρ flag k L t y := by
  classical
  have hρy := h.forwardExposed_iff htx hty hmx hmy |>.mp hρx
  ext σ
  simp only [filteredReverseSupportFamily, Finset.mem_filter, compatibleReverseSupportFamily,
    mem_compatibleReversePermutations]
  have hreal : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ ↔
      RealizesSuccessorPermutation (swapProfile (profileOfScores y)) μ.symm σ := by
    have hiff (w : Fin n) (hw : w ∈ σ.support) := h.reverseSuccessor_iff hsx hsy htx hty hmx hmy
      w (μ.symm (σ w)) (μ.symm.injective.ne (Equiv.Perm.mem_support.mp hw))
    exact ⟨fun hr w hw ↦ (hiff w hw).mp (hr w hw), fun hr w hw ↦ (hiff w hw).mpr (hr w hw)⟩
  have hcompat (hc : σ ∈ goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag))
      (hrx : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ)
      (hry : RealizesSuccessorPermutation (swapProfile (profileOfScores y)) μ.symm σ) :
      IsExposedRotation (profileOfScores x) (undoReverseRotation μ σ) ρ ↔
        IsExposedRotation (profileOfScores y) (undoReverseRotation μ σ) ρ := by
    have hdisj : ∀ m ∈ ρ.support, μ m ∉ σ.support := by
      exact fun m hm hms ↦ (mem_goodReverseSupportPermutations.mp hc).2 _ hms |>.1
        (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
    have hfixed (m : Fin n) (hm : ρ m ≠ m) : undoReverseRotation μ σ m = μ m :=
      undoReverseRotation_apply_of_not_mem_support (hdisj m (Equiv.Perm.mem_support.mpr hm))
    have hxN := (isStable_profileOfScores_iff htx _).mp
      (hrx.undo_stable ((isStable_profileOfScores_iff htx μ).mpr hsx))
    have hyN := (isStable_profileOfScores_iff hty _).mp
      (hry.undo_stable ((isStable_profileOfScores_iff hty μ).mpr hsy))
    rw [isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle htx hρx hxN hfixed,
      isExposedRotation_profileOfScores_iff_no_pivotCrossRectangle hty hρy hyN hfixed]
    exact ⟨fun hn m w hr ↦ hn m w (h.symm.crossRectangle hmy hty hry hr),
      fun hn m w hr ↦ hn m w (h.crossRectangle hmx htx hrx hr)⟩
  have hinc (hrx : RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ) :
      reverseCollectionIncrementGood x μ σ t ↔ reverseCollectionIncrementGood y μ σ t := by
    have he (w : Fin n) (hw : w ∈ σ.support) :
        reverseScoreIncrement x μ w (μ.symm (σ w)) =
          reverseScoreIncrement y μ w (μ.symm (σ w)) := by
      unfold reverseScoreIncrement
      rw [h.female_eq_of_spouse_lt hmx (reverseScore_spouse_lt htx (hrx w hw)),
        h.female_spouse_eq]
    exact ⟨fun hi w hw ↦ he w hw ▸ hi w hw, fun hi w hw ↦ (he w hw).symm ▸ hi w hw⟩
  constructor
  · rintro ⟨⟨hc, hrx, hex⟩, hs, hi⟩
    have hry := hreal.mp hrx
    exact ⟨⟨hc, hry, (hcompat hc hrx hry).mp hex⟩, hs, (hinc hrx).mp hi⟩
  · rintro ⟨⟨hc, hry, hey⟩, hs, hi⟩
    have hrx := hreal.mpr hry
    exact ⟨⟨hc, hrx, (hcompat hc hrx hry).mpr hey⟩, hs, (hinc hrx).mpr hi⟩

/-- Fill the omitted active female coordinates by distinct ordered fractions
of the woman's old spouse score. All retained coordinates are read as given. -/
noncomputable def reverseRevealFillOffDiagonal (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    OffDiagonalScorePairs n :=
  fun q ↦ if h : flag q = true then
    (r.1 ⟨q, h⟩, (diagonalPairAt d q.val.2).2 * (((q.val.1.val : ℝ) + 1) / (n + 1)))
  else r.2 q.val.2 ⟨⟨q, h⟩, rfl⟩

theorem measurable_reverseRevealFillOffDiagonal (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun a : DiagonalScorePairs n ×
      (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
      reverseRevealFillOffDiagonal a.1 flag a.2) := by
  refine Measurable.of_eval fun q ↦ ?_
  by_cases h : flag q = true
  · have hm : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦ a.2.1 ⟨q, h⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
    have hf : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
        (diagonalPairAt a.1 q.val.2).2) :=
      measurable_snd.comp ((measurable_pi_apply _).comp measurable_fst)
    simpa only [reverseRevealFillOffDiagonal, dite_eq_left h] using hm.prodMk (hf.mul_const _)
  · have hI : Measurable (fun a : DiagonalScorePairs n ×
        (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
        a.2.2 q.val.2 ⟨⟨q, h⟩, rfl⟩) :=
      (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (measurable_snd.comp measurable_snd))
    simpa only [reverseRevealFillOffDiagonal, dite_eq_right h] using hI

/-- Reconstruct a full score array measurably from only the diagonal,
active male scores, and the inactive columns. -/
noncomputable def reverseRevealFill (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) : ScoreProfile n :=
  (splitScorePairs μ).symm (d, reverseRevealFillOffDiagonal d flag r)

theorem measurable_reverseRevealFill (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool) :
    Measurable (fun a : DiagonalScorePairs n ×
      (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) ↦
      reverseRevealFill μ a.1 flag a.2) :=
  (splitScorePairs μ).symm.measurable.comp
    (measurable_fst.prodMk (measurable_reverseRevealFillOffDiagonal flag))

@[simp]
theorem splitScorePairs_reverseRevealFill (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    splitScorePairs μ (reverseRevealFill μ d flag r) =
      (d, reverseRevealFillOffDiagonal d flag r) :=
  (splitScorePairs μ).apply_symm_apply _

@[simp]
theorem forwardRevealWithColumns_reverseRevealFillOffDiagonal (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool)
    (r : ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :
    forwardRevealWithColumns flag (reverseRevealFillOffDiagonal d flag r) = r := by
  apply Prod.ext
  · funext q
    change ((reverseRevealFillOffDiagonal d flag r) q.val).1 = _
    simp only [reverseRevealFillOffDiagonal, dite_eq_left q.property]
  · funext i q
    obtain ⟨q, rfl⟩ := q
    change (reverseRevealFillOffDiagonal d flag r) q.val = _
    simp only [reverseRevealFillOffDiagonal, dite_eq_right q.property]

/-- Replace just the active female scores of a given marked array. -/
noncomputable def discardActiveFemale (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (x : ScoreProfile n) : ScoreProfile n :=
  reverseRevealFill μ (splitScorePairs μ x).1 flag
    (forwardRevealWithColumns flag (splitScorePairs μ x).2)

theorem sameReverseReveal_discardActiveFemale (μ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (x : ScoreProfile n) :
    SameReverseReveal μ flag x (discardActiveFemale μ flag x) := by
  constructor <;> simp only [discardActiveFemale, splitScorePairs_reverseRevealFill,
    forwardRevealWithColumns_reverseRevealFillOffDiagonal]

private def markedCellActive (μ : Matching n) (flag : OffDiagonalCellIndex n → Bool)
    (m w : Fin n) : Prop :=
  ∃ h : m ≠ μ.symm w, flag ⟨(m, μ.symm w), h⟩ = true

private theorem activeCell_scores
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : markedCellActive μ flag m w) :
    x (.inl m) (μ m) < x (.inl m) w ∧ x (.inr w) m < x (.inr w) (μ.symm w) := by
  obtain ⟨hne, hf⟩ := ha
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hc := mem_pi.mp hmask q (mem_univ _)
  change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
    (diagonalPairAt (splitScorePairs μ x).1 m).1
    (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
  rw [show flag q = true from hf, forwardScoreCellFlagEvent, ite_eq_left rfl,
    forwardEligibleScoreCell, splitScorePairs_offDiagonal_apply,
    diagonalPairAt_splitScorePairs, diagonalPairAt_splitScorePairs] at hc
  simpa only [q, Equiv.apply_symm_apply, mem_prod, mem_Ioi, mem_Iio] using hc

private theorem spouse_le_female_of_not_active (hs : IsScoreStable x μ)
    (ht : ∀ row, Function.Injective (x row))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
    x (.inr w) (μ.symm w) ≤ x (.inr w) m := by
  apply le_of_not_gt
  intro hf
  have hne : m ≠ μ.symm w := fun he ↦ hf.ne (congrArg (x (.inr w)) he)
  have hw : μ m ≠ w := fun he ↦ hne (μ.symm_apply_eq.mpr he.symm).symm
  have hm : x (.inl m) (μ m) < x (.inl m) w :=
    lt_of_le_of_ne (le_of_not_gt fun hlt ↦ hs m w ⟨hw, hlt, hf⟩)
      (fun he ↦ hw (ht (.inl m) he))
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q ≠ true := fun he ↦ ha ⟨hne, he⟩
  have hc := mem_pi.mp hmask q (mem_univ _)
  change (splitScorePairs μ x).2 q ∈ forwardScoreCellFlagEvent
    (diagonalPairAt (splitScorePairs μ x).1 m).1
    (diagonalPairAt (splitScorePairs μ x).1 (μ.symm w)).2 (flag q) at hc
  rw [forwardScoreCellFlagEvent, ite_eq_right hq, forwardEligibleScoreCell,
    splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
    diagonalPairAt_splitScorePairs] at hc
  apply hc
  simpa only [q, Equiv.apply_symm_apply, mem_prod, mem_Ioi, mem_Iio] using And.intro hm hf

private theorem female_discardActiveFemale_of_active {m w : Fin n}
    (ha : markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m =
      x (.inr w) (μ.symm w) * (((m.val : ℝ) + 1) / (n + 1)) := by
  obtain ⟨hne, hf⟩ := ha
  let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hne⟩
  have hq : flag q = true := hf
  have h := congrArg (fun a ↦ (a.2 q).2)
    (splitScorePairs_reverseRevealFill μ (splitScorePairs μ x).1 flag
      (forwardRevealWithColumns flag (splitScorePairs μ x).2))
  simpa only [discardActiveFemale, splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply,
    reverseRevealFillOffDiagonal, dite_eq_left hq, diagonalPairAt_splitScorePairs] using h

private theorem female_discardActiveFemale_of_not_active {m w : Fin n}
    (ha : ¬ markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m = x (.inr w) m := by
  have h := sameReverseReveal_discardActiveFemale μ flag x
  by_cases hm : m = μ.symm w
  · subst m
    exact (h.female_spouse_eq w).symm
  · let q : OffDiagonalCellIndex n := ⟨(m, μ.symm w), hm⟩
    have hq : flag q ≠ true := fun he ↦ ha ⟨hm, he⟩
    simpa only [splitScorePairs_offDiagonal_apply, q, Equiv.apply_symm_apply] using
      (congrArg Prod.snd (h.inactiveCell_eq ⟨q, hq⟩)).symm

private theorem fraction_lt_one (m : Fin n) : ((m.val : ℝ) + 1) / (n + 1) < 1 := by
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  rw [one_mul]
  have hm : (m.val : ℝ) < n := by exact_mod_cast m.isLt
  linarith

private theorem female_discardActiveFemale_lt_of_active
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    {m w : Fin n} (ha : markedCellActive μ flag m w) :
    discardActiveFemale μ flag x (.inr w) m < x (.inr w) (μ.symm w) := by
  have hpos := (h0 (.inr w) m).trans_lt (activeCell_scores hmask ha).2
  rw [female_discardActiveFemale_of_active ha]
  simpa only [mul_one] using mul_lt_mul_of_pos_left (fraction_lt_one m) hpos

/-- On a stable, tie-free marked array with nonnegative scores, the
measurable replacement stays stable, tie-free, and on the same mask. -/
theorem discardActiveFemale_valid (hs : IsScoreStable x μ)
    (ht : ∀ row, Function.Injective (x row)) (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    let y := discardActiveFemale μ flag x
    IsScoreStable y μ ∧ (∀ row, Function.Injective (y row)) ∧
      (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag := by
  intro y
  let h := sameReverseReveal_discardActiveFemale μ flag x
  change SameReverseReveal μ flag x y at h
  have hlt {m w : Fin n} (ha : markedCellActive μ flag m w) :
      y (.inr w) m < x (.inr w) (μ.symm w) :=
    female_discardActiveFemale_lt_of_active h0 hmask ha
  have hunchanged {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
      y (.inr w) m = x (.inr w) m := female_discardActiveFemale_of_not_active ha
  have hnot {m w : Fin n} (ha : ¬ markedCellActive μ flag m w) :
      x (.inr w) (μ.symm w) ≤ y (.inr w) m :=
    (spouse_le_female_of_not_active hs ht hmask ha).trans_eq (hunchanged ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro m w hb
    by_cases ha : markedCellActive μ flag m w
    · have hm := (activeCell_scores hmask ha).1
      rw [h.male_eq, h.male_eq] at hm
      exact hm.not_gt hb.2.1
    · exact (hnot ha).not_gt (by rw [h.female_spouse_eq]; exact hb.2.2)
  · intro r
    cases r with
    | inl m =>
      intro a b he
      exact ht (.inl m) (by simpa only [h.male_eq] using he)
    | inr w =>
      intro a b he
      by_cases ha : markedCellActive μ flag a w <;> by_cases hb : markedCellActive μ flag b w
      · have hpos := (h0 (.inr w) a).trans_lt (activeCell_scores hmask ha).2
        change discardActiveFemale μ flag x (.inr w) a =
          discardActiveFemale μ flag x (.inr w) b at he
        rw [female_discardActiveFemale_of_active ha, female_discardActiveFemale_of_active hb] at he
        have hdiv := mul_left_cancel₀ hpos.ne' he
        have hcast : (a.val : ℝ) = (b.val : ℝ) := by
          have hh := (div_left_inj' (by positivity : (n : ℝ) + 1 ≠ 0)).mp hdiv
          linarith
        exact Fin.ext (by exact_mod_cast hcast)
      · exact ((he ▸ hlt ha).not_ge (hnot hb)).elim
      · exact ((he.symm ▸ hlt hb).not_ge (hnot ha)).elim
      · exact ht (.inr w) ((hunchanged ha).symm.trans (he.trans (hunchanged hb)))
  · apply mem_pi.mpr
    intro q _
    let m := q.val.1
    let i := q.val.2
    change (splitScorePairs μ y).2 q ∈ forwardScoreCellFlagEvent
      (diagonalPairAt (splitScorePairs μ y).1 m).1
      (diagonalPairAt (splitScorePairs μ y).1 i).2 (flag q)
    by_cases hf : flag q = true
    · have hq : markedCellActive μ flag m (μ i) := by
        have hne : m ≠ μ.symm (μ i) := by
          simpa only [Equiv.symm_apply_apply] using q.property
        refine ⟨hne, ?_⟩
        convert hf using 2
        exact Subtype.ext (by simp only [m, i, Equiv.symm_apply_apply])
      have hm := (activeCell_scores hmask hq).1
      rw [h.male_eq, h.male_eq] at hm
      have hY := hlt hq
      rw [h.female_spouse_eq] at hY
      rw [hf, forwardScoreCellFlagEvent, ite_eq_left rfl, forwardEligibleScoreCell,
        splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
        diagonalPairAt_splitScorePairs]
      exact ⟨hm, by simpa only [Equiv.symm_apply_apply, mem_Iio, m, i] using hY⟩
    · rw [← h.diagonal, ← h.inactiveCell_eq ⟨q, hf⟩]
      exact mem_pi.mp hmask q (mem_univ _)

/-- The filtered family can be read from the measurable reduced-score
reconstruction on every stable, tie-free array in the unit-score support. -/
theorem filteredReverseSupportFamily_eq_discardActiveFemale
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hρ : IsExposedRotation (profileOfScores x) μ ρ) (k L : ℕ) (t : ℝ) :
    filteredReverseSupportFamily μ ρ flag k L t x =
      filteredReverseSupportFamily μ ρ flag k L t (discardActiveFemale μ flag x) := by
  obtain ⟨hs', ht', hmask'⟩ := discardActiveFemale_valid hs ht h0 hmask
  exact filteredReverseSupportFamily_eq_of_same_forwardReveal
    (sameReverseReveal_discardActiveFemale μ flag x) hs hs' ht ht' hmask hmask' hρ k L t

@[simp]
theorem discardActiveFemale_reconstruct (μ : Matching n) (d : DiagonalScorePairs n)
    (z : OffDiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) :
    discardActiveFemale μ flag ((splitScorePairs μ).symm (d, z)) =
      reverseRevealFill μ d flag (forwardRevealWithColumns flag z) := by
  simp only [discardActiveFemale, MeasurableEquiv.apply_symm_apply]

/-- Eligibility uses only the smaller reveal, so it is invariant under any
change that preserves that reveal and the mask. -/
theorem SameReverseReveal.localEligibility_iff (h : SameReverseReveal μ flag x y)
    (hmx : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (hmy : (splitScorePairs μ y).2 ∈ forwardScoreMaskEvent (splitScorePairs μ y).1 flag)
    (b A B : ℝ) :
    IsLocallyEligiblePivot b A B x μ ρ ↔ IsLocallyEligiblePivot b A B y μ ρ := by
  have ex := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ
    (splitScorePairs μ x).1 (splitScorePairs μ x).2 flag hmx
  have ey := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ
    (splitScorePairs μ y).1 (splitScorePairs μ y).2 flag hmy
  rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply, h.diagonal,
    congrArg Prod.fst h.observed] at ex
  rw [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] at ey
  exact ex.trans ey.symm

/-- The eligible count itself is a measurable function of the smaller
reveal and the inactive columns, via the canonical score reconstruction. -/
theorem localFilteredDecorationCount_eq_discardActiveFemale
    (hs : IsScoreStable x μ) (ht : ∀ row, Function.Injective (x row))
    (h0 : ∀ i j, 0 ≤ x i j)
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (b A B : ℝ) (K L : ℕ) (ρ : Matching n) :
    localFilteredDecorationCount b A B K L μ ρ x =
      localFilteredDecorationCount b A B K L μ ρ (discardActiveFemale μ flag x) := by
  classical
  obtain ⟨_, _, hmask'⟩ := discardActiveFemale_valid hs ht h0 hmask
  have h := sameReverseReveal_discardActiveFemale μ flag x
  have he := h.localEligibility_iff (ρ := ρ) hmask hmask' b A B
  by_cases hE : IsLocallyEligiblePivot b A B x μ ρ
  · rw [localFilteredDecorationCount_of_eligible_of_fixedMask K L hE hmask,
      localFilteredDecorationCount_of_eligible_of_fixedMask K L (he.mp hE) hmask',
      ← h.diagonal]
    have hρ := (hE.isSoleForwardExposed ht).1
    congr 2
    ext σ
    simp only [mem_markedFilteredChoices]
    rw [filteredReverseSupportFamily_eq_discardActiveFemale hs ht h0 hmask hρ]
  · have hy := fun h' ↦ hE (he.mpr h')
    simp only [localFilteredDecorationCount, ite_eq_right hE, ite_eq_right hy]

/-- At almost every diagonal the factorization of the marked count holds
almost surely on every mask and every measurable reveal restriction. -/
theorem ae_diagonal_ae_localFilteredDecorationCount_eq_reverseRevealFill
    (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ (flag : OffDiagonalCellIndex n → Bool)
      (U : Set (ForwardRevealedMaleScores flag)), ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      localFilteredDecorationCount b A B K L μ ρ ((splitScorePairs μ).symm (d, z)) =
        localFilteredDecorationCount b A B K L μ ρ
          (reverseRevealFill μ d flag (forwardRevealWithColumns flag z)) := by
  have hu : ∀ᵐ a ∂(diagonalScoreLaw n).prod (offDiagonalScoreLaw n),
      ∀ r i, (splitScorePairs μ).symm a r i ∈ Ioo (0 : ℝ) 1 :=
    (measurePreserving_splitScorePairs μ).symm.quasiMeasurePreserving.ae (ae_unitOpen_scores n)
  filter_upwards [ae_diagonal_ae_injective_scoreRows μ, Measure.ae_ae_of_ae_prod hu]
    with d ht h0
  intro flag U
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae h0)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag))]
    with z hz hu hstable hmask
  let x := (splitScorePairs μ).symm (d, z)
  have hsplit : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  have hs : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).mpr
    (by simpa only [hsplit] using hstable)
  have hm : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag := by
    simpa only [hsplit] using hmask
  simpa only [x, discardActiveFemale_reconstruct] using
    localFilteredDecorationCount_eq_discardActiveFemale hs hz
      (fun r i ↦ (hu r i).1.le) hm b A B K L ρ

end LennonPittelFormalization

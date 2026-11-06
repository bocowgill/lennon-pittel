module

public import LennonPittel.PivotForwardRevealRectangle
public import LennonPittel.ReverseIncrementColumnTail

/-!
# The large reverse-increment event at a fixed forward reveal

A long finite reverse successor in the actual rank profile gives a long
successor in one inactive column. The event can be bounded without
selecting a reverse cycle or conditioning on its existence.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The score of a woman's proposed reverse partner minus her spouse score. -/
def reverseScoreIncrement {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (w j : Fin n) : ℝ := x (.inr w) j - x (.inr w) (μ.symm w)

theorem measurable_reverseScoreIncrement {n : ℕ} (μ : Matching n) (w j : Fin n) :
    Measurable (fun x : ScoreProfile n ↦ reverseScoreIncrement x μ w j) := by
  have hrow : Measurable (fun x : ScoreProfile n ↦ x (.inr w)) := measurable_pi_apply _
  exact ((measurable_pi_apply j).comp hrow).sub ((measurable_pi_apply (μ.symm w)).comp hrow)

/-- Some woman has an actual reverse successor with increment greater than `t`. -/
def scoreLongReverseSuccessorEvent {n : ℕ} (μ : Matching n) (t : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ w j, IsSuccessor (swapProfile (profileOfScores x)) μ.symm w j ∧
    t < reverseScoreIncrement x μ w j}

theorem measurableSet_scoreLongReverseSuccessorEvent {n : ℕ} (μ : Matching n) (t : ℝ) :
    MeasurableSet (scoreLongReverseSuccessorEvent μ t) := by
  unfold scoreLongReverseSuccessorEvent
  simp only [ofPred_exists, ofPred_and]
  refine MeasurableSet.iUnion fun w ↦ MeasurableSet.iUnion fun j ↦ ?_
  exact ((measurable_profileOfScores n) (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IsSuccessor (swapProfile p) μ.symm w j})).inter
      (measurableSet_lt measurable_const (measurable_reverseScoreIncrement μ w j))

/-- The corresponding event on the unreconstructed off-diagonal coordinates. -/
def fixedDiagonalLongReverseSuccessorEvent {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (t : ℝ) : Set (OffDiagonalScorePairs n) :=
  (fun z ↦ (splitScorePairs μ).symm (d, z)) ⁻¹' scoreLongReverseSuccessorEvent μ t

theorem measurable_fixedDiagonalReconstruction {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) :
    Measurable (fun z : OffDiagonalScorePairs n ↦ (splitScorePairs μ).symm (d, z)) :=
  (splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id)

theorem measurableSet_fixedDiagonalLongReverseSuccessorEvent {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (t : ℝ) :
    MeasurableSet (fixedDiagonalLongReverseSuccessorEvent μ d t) :=
  (measurableSet_scoreLongReverseSuccessorEvent μ t).preimage
    (measurable_fixedDiagonalReconstruction μ d)

/-- All columns whose finite reverse successor exceeds the increment cutoff. -/
def longReverseColumnCover {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (t : ℝ) : Set (ForwardInactiveColumns flag) :=
  ⋃ i : Fin n, (fun z : ForwardInactiveColumns flag ↦ z i) ⁻¹'
    reverseColumnLongSuccessorEvent (diagonalPairAt d i).2
      (fun q ↦ (diagonalPairAt d q.val.val.val.1).1) t

theorem measurableSet_longReverseColumnCover {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (t : ℝ) :
    MeasurableSet (longReverseColumnCover d flag t) :=
  MeasurableSet.iUnion fun i ↦ (measurableSet_reverseColumnLongSuccessorEvent _ _ _).preimage
    (measurable_pi_apply i)

/-- The long rank-successor event is contained almost surely in the
corresponding event of the unopened columns. -/
theorem fixedDiagonalLongReverseSuccessorEvent_ae_le_cover {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (t : ℝ)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    fixedDiagonalLongReverseSuccessorEvent μ d t ≤ᵐ[forwardMaskRevealLaw d flag U]
      (Prod.snd ∘ forwardRevealWithColumns flag) ⁻¹' longReverseColumnCover d flag t := by
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  unfold forwardMaskRevealLaw
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht))] with z hzmask hzstable hzt h
  let x := (splitScorePairs μ).symm (d, z)
  have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  obtain ⟨w, j, hj, hlong⟩ : x ∈ scoreLongReverseSuccessorEvent μ t := h
  let i := μ.symm w
  have hiw : μ i = w := μ.apply_symm_apply w
  have hne : j ≠ i := fun e ↦ by
    have hh := hj.eligible.1
    rw [e] at hh
    exact (lt_irrefl _) hh
  have hstable : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).2
    (by simpa only [he] using hzstable)
  have hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag :=
    by simpa only [he] using hzmask
  obtain ⟨q, hq, hcol⟩ := exists_reverseSuccessorColumnEvent_of_isSuccessor μ x flag
    hstable hzt hmask i j hne (hiw.symm ▸ hj)
  let b := (forwardRevealWithColumns flag z).2
  change b ∈ longReverseColumnCover d flag t
  refine mem_iUnion.mpr ⟨i, q, ?_, ?_⟩
  · simpa only [he, b, forwardRevealWithColumns, Function.comp_apply, Prod.map_snd,
      forwardScoreMaskRevealAndInactive] using hcol
  have hcell : b i q = (x (.inl j) w, x (.inr w) j) := by
    change z q.val.val = _
    simpa only [he, q.property, hiw, hq] using splitScorePairs_offDiagonal_apply μ x q.val.val
  have hdiag : diagonalPairAt d i = (x (.inl i) w, x (.inr w) i) := by
    simpa only [he, hiw] using diagonalPairAt_splitScorePairs μ x i
  change t < (b i q).2 - (diagonalPairAt d i).2
  rw [hcell, hdiag]
  exact hlong

/-- Bound the probability mass of any long finite reverse successor.
No conditioning on a selected collection is used. -/
theorem measure_fixedDiagonalLongReverseSuccessorEvent_le {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (hU : MeasurableSet U)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1) {S t : ℝ} (ht₀ : 0 ≤ t)
    (hS : ∀ i, S ≤ ∑ q : ForwardInactiveColumnIndex flag i, (diagonalPairAt d q.val.val.val.1).1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    (forwardMaskRevealLaw d flag U) (fixedDiagonalLongReverseSuccessorEvent μ d t) ≤
      (forwardMaskRevealLaw d flag U) univ *
        ((n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-t * S))) := by
  let V : Set (ForwardRevealedMaleScores flag × ForwardInactiveColumns flag) :=
    Prod.snd ⁻¹' longReverseColumnCover d flag t
  rw [forwardMaskRevealLaw_univ μ d flag U hU hy0 hy1 ht]
  refine forwardMaskRevealLaw_measure_le_of_column_sections d flag U hU hy0 hy1 V
    ((measurableSet_longReverseColumnCover d flag t).preimage measurable_snd)
    (fixedDiagonalLongReverseSuccessorEvent_ae_le_cover μ d flag U t ht) fun _ _ ↦ ?_
  let ν := normalizedForwardInactiveColumnLaw d flag
  have (i : Fin n) : IsProbabilityMeasure (ν i) :=
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  change (Measure.pi ν) (longReverseColumnCover d flag t) ≤ _
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (Real.exp (-t * S)) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [(measurePreserving_eval ν i).measure_preimage
        (measurableSet_reverseColumnLongSuccessorEvent _ _ _).nullMeasurableSet]
      refine (reverseColumnLongSuccessorEvent_mass_le (hy0 i) (hy1 i)
        (fun q : ForwardInactiveColumnIndex flag i ↦ hx q.val.val.val.1) ht₀).trans
          (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
      exact mul_le_mul_of_nonpos_left (hS i) (neg_nonpos.mpr ht₀)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The reverse score-increment cutoff used by the centered proof. -/
noncomputable def reverseIncrementCutoff (n : ℕ) (X : ℝ) : ℝ := 16 * Real.log (n : ℝ) / X

/-- At the logarithmic cutoff, a union over the women costs at most
`n⁻⁷` times the mass of the fixed revealed event. -/
theorem measure_fixedDiagonalLongReverseSuccessorEvent_cutoff_le {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (hU : MeasurableSet U) (hn : 0 < n)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Icc 0 1) {X : ℝ} (hX : 0 < X)
    (hS : ∀ i, X / 2 ≤ ∑ q : ForwardInactiveColumnIndex flag i, (diagonalPairAt d q.val.val.val.1).1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    (forwardMaskRevealLaw d flag U)
      (fixedDiagonalLongReverseSuccessorEvent μ d (reverseIncrementCutoff n X)) ≤
      (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal ((n : ℝ) ^ (-7 : ℤ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt hn)
  have ht₀ : 0 ≤ reverseIncrementCutoff n X := by unfold reverseIncrementCutoff; positivity
  have he : Real.exp (-reverseIncrementCutoff n X * (X / 2)) = (n : ℝ) ^ (-8 : ℤ) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hn']
    congr 1
    unfold reverseIncrementCutoff
    norm_num
    field_simp [hX.ne']; ring
  refine (measure_fixedDiagonalLongReverseSuccessorEvent_le μ d flag U hU hy0 hy1 hx ht₀ hS ht).trans_eq ?_
  rw [he, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul hn'.le]
  congr 2
  calc
    (n : ℝ) * (n : ℝ) ^ (-8 : ℤ) = (n : ℝ) ^ (1 : ℤ) * (n : ℝ) ^ (-8 : ℤ) := by rw [zpow_one]
    _ = (n : ℝ) ^ (-7 : ℤ) := by rw [← zpow_add₀ hn'.ne']; norm_num

end LennonPittelFormalization

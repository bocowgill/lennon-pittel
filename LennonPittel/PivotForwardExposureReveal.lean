module

public import LennonPittel.PivotForwardPivotReadout

/-!
# Forward exposure is decided by the revealed information

The mask tells which forward candidates are eligible. The revealed male
scores then determine each eligible row's minimum, with no use of the
unopened columns.
-/

@[expose] public section

open MeasureTheory Set StableMarriage

namespace LennonPittelFormalization

private theorem forwardEligible_iff_flag {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (flag : OffDiagonalCellIndex n → Bool) (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag)
    (i j : Fin n) (hij : i ≠ j) :
    IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔ flag ⟨(i, j), hij⟩ = true := by
  let q : OffDiagonalCellIndex n := ⟨(i, j), hij⟩
  let d := (splitScorePairs μ x).1
  let z := (splitScorePairs μ x).2
  have he : IsEligibleSuccessor (profileOfScores x) μ i (μ j) ↔
      z q ∈ forwardEligibleScoreCell (diagonalPairAt d i).1 (diagonalPairAt d j).2 := by
    dsimp only [z, d]
    rw [splitScorePairs_offDiagonal_apply, diagonalPairAt_splitScorePairs,
      diagonalPairAt_splitScorePairs]
    simp only [IsEligibleSuccessor, forwardEligibleScoreCell, mem_prod, mem_Ioi, mem_Iio,
      Equiv.symm_apply_apply, profileOfScores, rankPermutation_lt_iff (ht (.inl i)),
      rankPermutation_lt_iff (ht (.inr (μ j))), q]
  have hh : z q ∈ forwardScoreCellFlagEvent (diagonalPairAt d i).1 (diagonalPairAt d j).2
      (flag q) := mem_pi.mp hmask q (mem_univ _)
  change _ ↔ flag q = true
  rw [he]
  by_cases hq : flag q = true
  · simp only [hq, forwardScoreCellFlagEvent] at hh
    simp only [hq, iff_true]
    exact hh
  · simp only [forwardScoreCellFlagEvent, ite_eq_right hq, mem_compl_iff] at hh
    exact ⟨fun h ↦ (hh h).elim, fun h ↦ (hq h).elim⟩

/-- The event in the revealed information that a fixed forward cycle is exposed. -/
def forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : Set (ForwardRevealedMaleScores flag) :=
  {v | ρ.IsCycle ∧ ∀ m, ρ m ≠ m →
    ∃ q : ForwardActiveCellIndex flag, q.val.val = (m, ρ m) ∧
      ∀ t : ForwardActiveCellIndex flag, t.val.val.1 = m → v q ≤ v t}

/-- Forward exposure can be tested using only the mask and the revealed scores. -/
theorem isExposedRotation_iff_forwardRevealExposureEvent {n : ℕ} (μ ρ : Matching n)
    (x : ScoreProfile n) (flag : OffDiagonalCellIndex n → Bool)
    (ht : ∀ r, Function.Injective (x r))
    (hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag) :
    IsExposedRotation (profileOfScores x) μ ρ ↔
      (forwardRevealWithColumns flag (splitScorePairs μ x).2).1 ∈
        forwardRevealExposureEvent ρ flag := by
  let v := (forwardRevealWithColumns flag (splitScorePairs μ x).2).1
  let p := profileOfScores x
  have hscore (q : ForwardActiveCellIndex flag) :
      v q = x (.inl q.val.val.1) (μ q.val.val.2) :=
    congrArg Prod.fst (splitScorePairs_offDiagonal_apply μ x q.val)
  have hle (m j k : Fin n) :
      p.manRank m (μ j) ≤ p.manRank m (μ k) ↔ x (.inl m) (μ j) ≤ x (.inl m) (μ k) := by
    rw [← not_lt, ← not_lt]
    exact not_congr (rankPermutation_lt_iff (ht (.inl m)) _ _)
  constructor
  · intro h
    refine ⟨h.isCycle, fun m hm ↦ ?_⟩
    let q₀ : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    let q : ForwardActiveCellIndex flag := ⟨q₀,
      (forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mp (h.successor m hm).eligible⟩
    refine ⟨q, rfl, fun t htm ↦ ?_⟩
    have htne : m ≠ t.val.val.2 := htm.symm ▸ t.val.property
    have hteq : (⟨(m, t.val.val.2), htne⟩ : OffDiagonalCellIndex n) = t.val :=
      Subtype.ext (Prod.ext htm.symm rfl)
    have hflag : flag ⟨(m, t.val.val.2), htne⟩ = true := by rw [hteq]; exact t.property
    have htel := (forwardEligible_iff_flag μ x flag ht hmask m t.val.val.2 htne).mpr hflag
    change v q ≤ v t
    rw [hscore q, hscore t, htm]
    exact (hle m (ρ m) t.val.val.2).mp ((h.successor m hm).min_rank _ htel)
  · rintro ⟨hcyc, htest⟩
    refine ⟨hcyc, fun m hm ↦ ?_⟩
    obtain ⟨q, hq, hmin⟩ := htest m hm
    have hq' : (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = q.val := Subtype.ext hq.symm
    refine ⟨(forwardEligible_iff_flag μ x flag ht hmask m (ρ m) hm.symm).mpr
      (hq' ▸ q.property), ?_⟩
    intro w hwel
    let j := μ.symm w
    have hjw : μ j = w := μ.apply_symm_apply w
    have hj : m ≠ j := fun h ↦ (lt_irrefl _ (by simpa only [← hjw, ← h] using hwel.1))
    let t : ForwardActiveCellIndex flag := ⟨⟨(m, j), hj⟩,
      (forwardEligible_iff_flag μ x flag ht hmask m j hj).mp (hjw.symm ▸ hwel)⟩
    have h := hmin t rfl
    change v q ≤ v t at h
    rw [hscore q, hscore t, hq] at h
    exact hjw ▸ (hle m (ρ m) j).mpr h

theorem measurableSet_forwardRevealExposureEvent {n : ℕ} (ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) : MeasurableSet (forwardRevealExposureEvent ρ flag) := by
  unfold forwardRevealExposureEvent
  simp only [ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun (m : Fin n) ↦
    MeasurableSet.iInter fun (_ : ρ m ≠ m) ↦ MeasurableSet.iUnion
      fun (q : ForwardActiveCellIndex flag) ↦ (MeasurableSet.const _).inter
        (MeasurableSet.iInter fun (t : ForwardActiveCellIndex flag) ↦
          MeasurableSet.iInter fun (_ : t.val.val.1 = m) ↦ ?_))
  exact measurableSet_le (measurable_pi_apply q) (measurable_pi_apply t)

/-- A measurable restriction of the revealed data can enforce exposure
almost surely in the original fixed-mask law. -/
theorem ae_isExposedRotation_of_forwardReveal_subset {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (hU : MeasurableSet U)
    (hsub : U ⊆ forwardRevealExposureEvent ρ flag)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      IsExposedRotation (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ := by
  unfold forwardMaskRevealLaw
  filter_upwards [ae_restrict_mem (hU.preimage (measurable_fst.comp
      (measurable_forwardScoreMaskRevealAndInactive flag))),
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht))] with z hz hzmask hzt
  let x := (splitScorePairs μ).symm (d, z)
  have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  apply (isExposedRotation_iff_forwardRevealExposureEvent μ ρ x flag hzt
    (by simpa only [he] using hzmask)).mpr
  simpa only [he, Function.comp_apply, forwardRevealWithColumns, Prod.map_fst, id_eq] using
    hsub hz

end LennonPittelFormalization

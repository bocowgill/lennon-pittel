module

public import LennonPittel.CoexposureScoreProduct

/-!
# Forward successors under the normalized stable row law

The exact forward-arc probability is the eligibility probability of its
target times the integral for beating all eligible competitors.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The off-diagonal row law conditional on the absence of a blocking pair. -/
noncomputable def normalizedStableScoreRowLaw {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) :
    Measure ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  (stableScoreRowLaw d i univ)⁻¹ • stableScoreRowLaw d i

private theorem stableScoreRowLaw_univ_ne_zero {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    stableScoreRowLaw d i univ ≠ 0 := by
  rw [stableScoreRowLaw, Measure.pi_univ]
  refine Finset.prod_ne_zero_iff.mpr fun j _ ↦ ?_
  change rowNonblockingLaw (diagonalPairAt d i).1 (diagonalPairAt d j.val).2 univ ≠ 0
  rw [rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ (hy j.val)]
  apply ENNReal.ofReal_ne_zero_iff.mpr
  have h := mul_le_mul_of_nonneg_left (hy j.val).2 hx.1
  linarith only [h, hx.2]

/-- The stable row has positive finite mass and its normalization is a probability law. -/
theorem normalizedStableScoreRowLaw_isProbabilityMeasure {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    IsProbabilityMeasure (normalizedStableScoreRowLaw d i) := by
  constructor
  rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (stableScoreRowLaw_univ_ne_zero d i hx hy) (measure_ne_top _ _)]

/-- The unnormalized row is its mass times the conditional row law. -/
theorem stableScoreRowLaw_eq_smul_normalized {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    stableScoreRowLaw d i = stableScoreRowLaw d i univ • normalizedStableScoreRowLaw d i := by
  rw [normalizedStableScoreRowLaw, smul_smul,
    ENNReal.mul_inv_cancel (stableScoreRowLaw_univ_ne_zero d i hx hy) (measure_ne_top _ _),
    one_smul]

/-- The successor probability in a stable row is the exact eligibility integral. -/
theorem normalizedStableScoreRowLaw_successor_eq {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      ENNReal.ofReal (rowEligibilityProbability (diagonalPairAt d i).1
        (diagonalPairAt d j.val).2 *
        scoreRowMass Finset.univ
          (fun k : {k : {k : Fin n // i ≠ k} // k ≠ j} ↦
            rowEligibilityProbability (diagonalPairAt d i).1 (diagonalPairAt d k.val.val).2)
          0 1) := by
  let x := (diagonalPairAt d i).1
  let y (k : {k : Fin n // i ≠ k}) := (diagonalPairAt d k.val).2
  let a (k : {k : Fin n // i ≠ k}) := rowEligibilityProbability x (y k)
  let m (k : {k : Fin n // i ≠ k}) := rowNonblockingLaw x (y k)
  let E := scoreSuccessorPairEvent x (y j) (fun k : {k // k ≠ j} ↦ y k.val)
  let K := scoreRowKernel Finset.univ (fun k : {k // k ≠ j} ↦ y k.val) x
  let L := scoreRowMass Finset.univ (fun k : {k // k ≠ j} ↦ a k.val) 0 1
  change normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
    ENNReal.ofReal (a j * L)
  have hpres := measurePreserving_rowTargetAndCompetitors m j
  have hE : MeasurableSet E := measurableSet_scoreSuccessorPairEvent _ _ _
  have heq : stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) E :=
    hpres.measure_preimage hE.nullMeasurableSet
  have ht : stableScoreRowLaw d i univ =
      m j univ * ∏ k : {k // k ≠ j}, m k.val univ := by
    have h := hpres.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    calc
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) univ :=
        by
          change (Measure.pi m) univ = _
          simpa only [Set.preimage_univ] using h
      _ = ((m j).prod (Measure.pi fun k : {k // k ≠ j} ↦ m k.val)) (univ ×ˢ univ) :=
        by rw [Set.univ_prod_univ]
      _ = _ := by rw [Measure.prod_prod, Measure.pi_univ]
  have hden (k : {k : Fin n // i ≠ k}) : 0 < 1 - x * y k := by
    have h := mul_le_mul_of_nonneg_left (hy k.val).2 hx.1
    change x * y k ≤ x * 1 at h
    linarith only [h, hx.2]
  have hm (k : {k : Fin n // i ≠ k}) : m k univ = ENNReal.ofReal (1 - x * y k) :=
    rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ (hy k.val)
  have ht' : stableScoreRowLaw d i univ = ENNReal.ofReal ((1 - x * y j) * K) := by
    rw [ht]
    simp_rw [hm]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ ↦ (hden k.val).le),
      ← ENNReal.ofReal_mul (hden j).le]
    rfl
  have hK : 0 ≤ K := Finset.prod_nonneg fun k _ ↦ (hden k.val).le
  have heq' : stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) =
      stableScoreRowLaw d i univ * ENNReal.ofReal (a j * L) := by
    rw [heq, ht', ← ENNReal.ofReal_mul (mul_nonneg (hden j).le hK)]
    rw [scoreSuccessorPairEvent_mass ⟨hx.1, hx.2.le⟩ (hy j.val)
      (fun k : {k // k ≠ j} ↦ hy k.val.val)]
    congr 1
    rw [scoreRowMass_affine_eq hx (fun k _ ↦ hy k.val.val)]
    change y j * ((1 - x) * K * L) = (1 - x * y j) * K * (a j * L)
    unfold a rowEligibilityProbability
    have hden' : 1 - y j * x ≠ 0 := by simpa only [mul_comm] using (hden j).ne'
    field_simp [(hden j).ne', hden']
  rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul, heq', ← mul_assoc,
    ENNReal.inv_mul_cancel (stableScoreRowLaw_univ_ne_zero d i hx hy) (measure_ne_top _ _),
    one_mul]

/-- The row event yields a rank successor as soon as the score rows have no ties. -/
theorem isSuccessor_of_scoreRowSuccessorEvent {n : ℕ} (μ : Matching n) (x : ScoreProfile n)
    (ht : ∀ row, Function.Injective (x row))
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (h : offDiagonalRowsEquiv n (splitScorePairs μ x).2 i ∈
      scoreRowSuccessorEvent (splitScorePairs μ x).1 i j) :
    IsSuccessor (profileOfScores x) μ i (μ j.val) := by
  have hcell (a : {a : Fin n // i ≠ a}) :
      offDiagonalRowsEquiv n (splitScorePairs μ x).2 i a =
        (x (.inl i) (μ a.val), x (.inr (μ a.val)) i) :=
    splitScorePairs_offDiagonal_apply μ x ⟨(i, a.val), a.property⟩
  simp only [scoreRowSuccessorEvent, Set.mem_ofPred_eq, hcell, diagonalPairAt_splitScorePairs] at h
  have hman (w w' : Fin n) : (profileOfScores x).manRank i w < (profileOfScores x).manRank i w'
      ↔ x (.inl i) w < x (.inl i) w' :=
    rankPermutation_lt_iff (ht (.inl i)) w w'
  have hwoman (w m m' : Fin n) :
      (profileOfScores x).womanRank w m < (profileOfScores x).womanRank w m'
        ↔ x (.inr w) m < x (.inr w) m' :=
    rankPermutation_lt_iff (ht (.inr w)) m m'
  refine ⟨⟨(hman _ _).2 h.1, ?_⟩, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using (hwoman (μ j.val) i j.val).2 h.2.1
  · intro w hw
    apply le_of_not_gt
    intro hlt
    have hi : i ≠ μ.symm w := by
      intro hi
      have heq : μ i = w := by rw [hi, Equiv.apply_symm_apply]
      exact (ne_of_lt hw.1) (congrArg ((profileOfScores x).manRank i) heq)
    let k : {k : Fin n // i ≠ k} := ⟨μ.symm w, hi⟩
    have hk : k ≠ j := by
      intro heq
      have hwj : w = μ j.val := by
        have hval := congrArg (fun k : {k : Fin n // i ≠ k} ↦ μ k.val) heq
        simpa only [k, Equiv.apply_symm_apply] using hval
      exact (ne_of_lt hlt) (congrArg ((profileOfScores x).manRank i) hwj)
    have hlt' : x (.inl i) w < x (.inl i) (μ j.val) := (hman _ _).1 hlt
    have hel' : x (.inr w) i < x (.inr w) (μ.symm w) := (hwoman _ _ _).1 hw.2
    exact h.2.2 ⟨k, hk⟩ (by simpa only [k, Equiv.apply_symm_apply] using And.intro hlt' hel')

/-- On stable tie-free arrays, the row event is exactly the corresponding rank arc. -/
theorem scoreRowSuccessorEvent_iff_isSuccessor_reconstructed {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hs : IsScoreStable ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) row)) :
    r i ∈ scoreRowSuccessorEvent d i j ↔
      IsSuccessor
        (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)))
        μ i (μ j.val) := by
  refine ⟨fun h ↦ isSuccessor_of_scoreRowSuccessorEvent μ _ ht i j ?_, ?_⟩
  · simpa only [MeasurableEquiv.apply_symm_apply] using h
  · exact scoreRowSuccessorEvent_of_isSuccessor_reconstructed μ d r i j hs ht

end LennonPittelFormalization

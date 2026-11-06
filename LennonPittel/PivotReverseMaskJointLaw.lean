module

public import LennonPittel.CoexposureCycleMoment
public import LennonPittel.PivotReverseScoreSuccessor

/-!
# Joint reverse successor law at a fixed forward reveal

Any prescribed successor permutation tests at most one arc per column.
On a fixed mask those tests depend on disjoint inactive columns. The exact
factorization holds after restricting to a measurable revealed-score event.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The stable off-diagonal score law restricted to one mask and a
measurable event of the revealed male scores. -/
noncomputable def forwardMaskRevealLaw {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (A : Set (ForwardActiveCellIndex flag → ℝ)) :
    Measure (OffDiagonalScorePairs n) :=
  (((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)).restrict
      ((Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A)

/-- The reverse successor graph on the reconstructed score profile follows
the prescribed permutation with exactly the product of its column arc
probabilities times the mass of the fixed mask and revealed event. -/
theorem measure_realizesReverseSuccessorPermutation_fixedMask {n : ℕ}
    (μ σ : Matching n) (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (A : Set (ForwardActiveCellIndex flag → ℝ)) (hA : MeasurableSet A)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    forwardMaskRevealLaw d flag A {z | RealizesSuccessorPermutation
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm σ} =
      ((forwardScoreMaskActiveMaleLaw d flag) A *
        (forwardScoreMaskInactiveColumnLaw d flag) univ) *
      ∏ i ∈ σ.support,
        normalizedForwardInactiveColumnLaw d flag (μ.symm i)
          (forwardInactiveReverseArcEvent d flag (μ.symm i) (μ.symm (σ i))) := by
  let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)
  let G := (Prod.fst ∘ forwardScoreMaskRevealAndInactive flag) ⁻¹' A
  let P (z : OffDiagonalScorePairs n) :=
    swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))
  let f := Prod.map id (forwardInactiveColumnsEquiv flag) ∘ forwardScoreMaskRevealAndInactive flag
  let L := forwardScoreMaskInactiveColumnLaw d flag
  let R := forwardScoreMaskActiveMaleLaw d flag
  let L₀ := normalizedForwardInactiveColumnLaw d flag
  let : ∀ i : Fin n, IsProbabilityMeasure (L₀ i) := fun i ↦
    normalizedForwardInactiveColumnLaw_isProbabilityMeasure d flag i (hy0 i) (hy1 i)
  have hf : Measurable f :=
    (measurable_id.prodMap (forwardInactiveColumnsEquiv flag).measurable).comp
      (measurable_forwardScoreMaskRevealAndInactive flag)
  let B (i : Fin n) : Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
    if μ i ∈ σ.support then forwardInactiveReverseArcEvent d flag i (μ.symm (σ (μ i)))
    else univ
  have hB (i : Fin n) : MeasurableSet (B i) := by
    by_cases h : μ i ∈ σ.support
    · simpa only [B, ite_eq_left h] using measurableSet_forwardInactiveReverseArcEvent d flag i _
    · simp only [B, ite_eq_right h, MeasurableSet.univ]
  have hrect : MeasurableSet (A ×ˢ univ.pi B) := hA.prod (MeasurableSet.univ_pi hB)
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  have hevent : {z | RealizesSuccessorPermutation (P z) μ.symm σ} =ᵐ[ν.restrict G]
      f ⁻¹' (A ×ˢ univ.pi B) := by
    filter_upwards [ae_restrict_mem (hA.preimage (measurable_fst.comp
        (measurable_forwardScoreMaskRevealAndInactive flag))),
      ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
      ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
      ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht))]
      with z hzG hzmask hzstable hzt
    let x := (splitScorePairs μ).symm (d, z)
    have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
    have hxstable : IsScoreStable x μ := (isScoreStable_iff_splitScorePairs μ x).2
      (by simpa only [he] using hzstable)
    have hxmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag :=
      by simpa only [he] using hzmask
    have harc (i : Fin n) (hi : μ i ∈ σ.support) :
        IsSuccessor (P z) μ.symm (μ i) (μ.symm (σ (μ i))) ↔ (f z).2 i ∈ B i := by
      have hne : μ.symm (σ (μ i)) ≠ i := fun h ↦
        Equiv.Perm.mem_support.mp hi (by simpa only [Equiv.apply_symm_apply] using congrArg μ h)
      rw [show B i = forwardInactiveReverseArcEvent d flag i (μ.symm (σ (μ i))) by
        simp only [B, ite_eq_left hi]]
      have h := isSuccessor_swapProfile_iff_forwardInactiveReverseArcEvent
        μ x flag hxstable hzt hxmask i _ hne
      rw [he] at h
      exact h
    apply propext
    constructor
    · intro h
      refine ⟨hzG, mem_pi.mpr fun i _ ↦ ?_⟩
      by_cases hi : μ i ∈ σ.support
      · exact (harc i hi).mp (h (μ i) hi)
      · simp only [B, ite_eq_right hi, mem_univ]
    · intro h j hj
      have hi : μ (μ.symm j) ∈ σ.support := by simpa only [Equiv.apply_symm_apply] using hj
      have hB' := mem_pi.mp h.2 (μ.symm j) (mem_univ _)
      simpa only [Equiv.apply_symm_apply] using (harc _ hi).mpr hB'
  have hl : L (univ.pi B) = L univ * ∏ i, L₀ i (B i) := by
    change forwardScoreMaskInactiveColumnLaw d flag (univ.pi B) =
      forwardScoreMaskInactiveColumnLaw d flag univ * _
    rw [forwardScoreMaskInactiveColumnLaw_eq_smul d flag hy0 hy1, Measure.smul_apply,
      Measure.smul_apply, Measure.pi_pi, measure_univ, smul_eq_mul, smul_eq_mul, mul_one]
  have hp : (∏ i, L₀ i (B i)) =
      ∏ i ∈ σ.support, L₀ (μ.symm i) (forwardInactiveReverseArcEvent d flag
        (μ.symm i) (μ.symm (σ i))) := by
    let g (i : Fin n) := if i ∈ σ.support then
      L₀ (μ.symm i) (forwardInactiveReverseArcEvent d flag (μ.symm i) (μ.symm (σ i))) else 1
    calc
      _ = ∏ i, g (μ i) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        by_cases hi : μ i ∈ σ.support
        · simp only [B, g, ite_eq_left hi]
          exact congrArg (fun j ↦ L₀ j (forwardInactiveReverseArcEvent d flag j (μ.symm (σ (μ i)))))
            (μ.symm_apply_apply i).symm
        · simp only [B, g, ite_eq_right hi, measure_univ]
      _ = ∏ i, g i := Fintype.prod_equiv μ _ _ (fun _ ↦ rfl)
      _ = _ := by simp only [g, Finset.prod_ite_mem, Finset.univ_inter]
  calc
    _ = (ν.restrict G) (f ⁻¹' (A ×ˢ univ.pi B)) := measure_congr hevent
    _ = ν (f ⁻¹' (A ×ˢ univ.pi B)) := by
      rw [Measure.restrict_apply (hrect.preimage hf), inter_eq_left.mpr (fun _ hz ↦ hz.1)]
    _ = R A * L (univ.pi B) := by
      rw [← Measure.map_apply hf hrect, map_forwardScoreMaskRevealAndInactiveColumns d flag,
        Measure.prod_prod]
    _ = _ := by rw [hl, hp, mul_assoc]

/-- The common factor in the joint law is exactly the mass of the fixed
mask and revealed event, including the possibility of zero mass. -/
theorem forwardMaskRevealLaw_univ {n : ℕ} (μ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (A : Set (ForwardActiveCellIndex flag → ℝ))
    (hA : MeasurableSet A)
    (hy0 : ∀ i, 0 ≤ (diagonalPairAt d i).2) (hy1 : ∀ i, (diagonalPairAt d i).2 < 1)
    (ht : ∀ᵐ z ∂(offDiagonalScoreLaw n),
      ∀ r, Function.Injective ((splitScorePairs μ).symm (d, z) r)) :
    forwardMaskRevealLaw d flag A univ =
      (forwardScoreMaskActiveMaleLaw d flag) A * (forwardScoreMaskInactiveColumnLaw d flag) univ := by
  simpa only [realizesSuccessorPermutation_one, Set.ofPred_true, Equiv.Perm.support_one,
    Finset.prod_empty, mul_one] using
    measure_realizesReverseSuccessorPermutation_fixedMask μ 1 d flag A hA hy0 hy1 ht

end LennonPittelFormalization

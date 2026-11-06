module

public import LennonPittel.PivotCompatibilityLoss
public import LennonPittel.PivotReversePermutationDecoration

/-!
# A positive first moment after enforcing pivot compatibility

For each support size, the realized count splits into the compatible
count and the crossed-blocker loss. The linear-in-cutoff lower bound
survives if the blocker loss is smaller than the unfiltered margin.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The candidate permutations that are realized and retain the pivot. -/
noncomputable def compatibleReversePermutations {n : ℕ} (S : Finset (Matching n))
    (p : Profile n) (μ ρ : Matching n) : Finset (Matching n) := by
  classical
  exact S.filter fun σ ↦ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
    IsExposedRotation p (undoReverseRotation μ σ) ρ

theorem mem_compatibleReversePermutations {n : ℕ} {S : Finset (Matching n)}
    {p : Profile n} {μ ρ σ : Matching n} : σ ∈ compatibleReversePermutations S p μ ρ ↔
    σ ∈ S ∧ RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      IsExposedRotation p (undoReverseRotation μ σ) ρ := by
  classical
  simp [compatibleReversePermutations]

/-- A rank-level compatible test for a candidate on reconstructed scores. -/
def compatibleReversePermutationEvent {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) : Set (OffDiagonalScorePairs n) :=
  {z | let p := profileOfScores ((splitScorePairs μ).symm (d, z))
       RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
         IsExposedRotation p (undoReverseRotation μ σ) ρ}

private theorem measurable_reconstructedProfile {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) : Measurable (fun z : OffDiagonalScorePairs n ↦
      profileOfScores ((splitScorePairs μ).symm (d, z))) :=
  (measurable_profileOfScores n).comp
    ((splitScorePairs μ).symm.measurable.comp (measurable_const.prodMk measurable_id))

theorem measurableSet_compatibleReversePermutationEvent {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) : MeasurableSet (compatibleReversePermutationEvent μ ρ σ d) :=
  measurable_reconstructedProfile μ d (MeasurableSet.of_discrete : MeasurableSet
    {p : Profile n | RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      IsExposedRotation p (undoReverseRotation μ σ) ρ})

theorem measurableSet_incompatibleReversePermutationEvent {n : ℕ} (μ ρ σ : Matching n)
    (d : DiagonalScorePairs n) : MeasurableSet (incompatibleReversePermutationEvent μ ρ σ d) :=
  measurable_reconstructedProfile μ d (MeasurableSet.of_discrete : MeasurableSet
    {p : Profile n | RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧
      ¬ IsExposedRotation p (undoReverseRotation μ σ) ρ})

/-- The compatible count's first moment is the sum of compatible event masses. -/
theorem lintegral_card_compatibleReversePermutations {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (S : Finset (Matching n)) (ν : Measure (OffDiagonalScorePairs n)) :
    (∫⁻ z, ((compatibleReversePermutations S
      (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ).card : ℝ≥0∞) ∂ν) =
      ∑ σ ∈ S, ν (compatibleReversePermutationEvent μ ρ σ d) := by
  classical
  let E := fun σ ↦ compatibleReversePermutationEvent μ ρ σ d
  have hpoint (z : OffDiagonalScorePairs n) :
      ((compatibleReversePermutations S (profileOfScores ((splitScorePairs μ).symm (d, z)))
        μ ρ).card : ℝ≥0∞) = ∑ σ ∈ S, (E σ).indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
    calc
      _ = ∑ σ ∈ S.filter (fun σ ↦ z ∈ E σ), (1 : ℝ≥0∞) := by
        have he : compatibleReversePermutations S
            (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ =
            S.filter (fun σ ↦ z ∈ E σ) := by
          ext σ
          rw [mem_compatibleReversePermutations]
          exact (Finset.mem_filter (s := S) (a := σ) (p := fun τ ↦ z ∈ E τ)).symm
        rw [he, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = _ := by simp only [Finset.sum_filter, indicator_apply]
  simp_rw [hpoint]
  rw [lintegral_finsetSum _ (fun σ _ ↦ measurable_const.indicator
    (measurableSet_compatibleReversePermutationEvent μ ρ σ d))]
  exact Finset.sum_congr rfl fun σ _ ↦ lintegral_indicator_one
    (measurableSet_compatibleReversePermutationEvent μ ρ σ d)

/-- The unfiltered first moment is the compatible first moment plus the
mass of the incompatible realizations, counted with multiplicity one. -/
theorem lintegral_realizedReversePermutationCount_eq_compat_add_loss {n : ℕ}
    (μ ρ : Matching n) (d : DiagonalScorePairs n) (S : Finset (Matching n))
    (ν : Measure (OffDiagonalScorePairs n)) :
    (∫⁻ z, (realizedReversePermutationCount S
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞) ∂ν) =
      (∫⁻ z, ((compatibleReversePermutations S
        (profileOfScores ((splitScorePairs μ).symm (d, z))) μ ρ).card : ℝ≥0∞) ∂ν) +
      ∑ σ ∈ S, ν (incompatibleReversePermutationEvent μ ρ σ d) := by
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  have hP : Measurable P :=
    (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
      (measurable_reconstructedProfile μ d)
  change (∫⁻ z, (realizedReversePermutationCount S (P z) μ.symm : ℝ≥0∞) ∂ν) = _
  rw [lintegral_realizedReversePermutationCount ν P hP μ.symm S,
    lintegral_card_compatibleReversePermutations μ ρ d S ν, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  let A := compatibleReversePermutationEvent μ ρ σ d
  let B := incompatibleReversePermutationEvent μ ρ σ d
  have he : {z | RealizesSuccessorPermutation (P z) μ.symm σ} = A ∪ B := by
    ext z
    simp only [P, A, B, compatibleReversePermutationEvent, incompatibleReversePermutationEvent,
      mem_union, mem_ofPred_eq, ← and_or_left, em, and_true]
  have hd : Disjoint A B := Set.disjoint_left.mpr fun _ hA hB ↦ hB.2 hA.2
  rw [he, measure_union hd (measurableSet_incompatibleReversePermutationEvent μ ρ σ d)]

/-- The fixed score and mask bounds used by the unfiltered lower moment.
They are separate from the additional bounds for the compatibility loss. -/
structure ReverseUnfilteredControls {n : ℕ} (μ ρ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (K : ℕ) (η : ℝ≥0∞) (m δ : ℝ) : Prop where
  forbidden_weight : ∀ i,
    ∑ j ∈ forwardMaskForbiddenTargets μ flag i, reverseSpouseWeights μ d j ≤ η
  label_loss : ∀ k ∈ Finset.Icc 2 K,
    reverseGoodLabelLoss k (reverseSpouseWeights μ d) (ρ.support.map μ.toEmbedding) η ≤
      ENNReal.ofReal (1 / 4)
  male_total_ge_two : 2 ≤ ∑ i, (diagonalPairAt d i).1
  competitor_mass : ∀ i (q : ForwardInactiveColumnIndex flag i),
    (∑ j, (diagonalPairAt d j).1) / 2 ≤
      ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
        (diagonalPairAt d t.val.val.val.val.1).1
  male_max : ∀ i, (diagonalPairAt d i).1 ≤ m
  arc_error : 14 * m / (∑ i, (diagonalPairAt d i).1) +
    Real.exp (-(∑ i, (diagonalPairAt d i).1) / 4) ≤ δ
  error_nonneg : 0 ≤ δ
  error_le_one : δ ≤ 1
  cumulative_error : (K : ℝ) * δ ≤ 1 / 4

/-- The compatible realized collections at a prescribed support size. -/
noncomputable def compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) (p : Profile n) : Finset (Matching n) :=
  compatibleReversePermutations
    (goodReverseSupportPermutations k (ρ.support.map μ.toEmbedding)
      (forwardMaskForbiddenTargets μ flag)) p μ ρ

private theorem measurable_card_compatibleReverseSupportFamily {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (k : ℕ) :
    Measurable (fun z : OffDiagonalScorePairs n ↦ ((compatibleReverseSupportFamily μ ρ flag k
      (profileOfScores ((splitScorePairs μ).symm (d, z)))).card : ℝ≥0∞)) :=
  (show Measurable (fun p : Profile n ↦
    ((compatibleReverseSupportFamily μ ρ flag k p).card : ℝ≥0∞)) from
      fun _ _ ↦ MeasurableSet.of_discrete).comp (measurable_reconstructedProfile μ d)

/-- At a size between two and the cutoff, at least half of the unfiltered
lower-moment margin remains when the compatibility loss fits its budget. -/
theorem lintegral_card_compatibleReverseSupportFamily_ge {n K k : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) {a D m δ : ℝ} {η : ℝ≥0∞}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hlow : ReverseUnfilteredControls μ ρ d flag K η m δ) (hk : k ∈ Finset.Icc 2 K)
    (ha : 1 ≤ a)
    (hbudget : ENNReal.ofReal a ^ K * (K : ℝ≥0∞) *
      ENNReal.ofReal (a * D / ∑ i, (diagonalPairAt d i).1) ≤ ENNReal.ofReal (3 / 32)) :
    (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 32) ≤
      ∫⁻ z, ((compatibleReverseSupportFamily μ ρ flag k
        (profileOfScores ((splitScorePairs μ).symm (d, z)))).card : ℝ≥0∞)
        ∂forwardMaskRevealLaw d flag U := by
  let ν := forwardMaskRevealLaw d flag U
  let A := ρ.support.map μ.toEmbedding
  let S := goodReverseSupportPermutations k A (forwardMaskForbiddenTargets μ flag)
  let c := ν univ
  let G := ∫⁻ z, ((compatibleReverseSupportFamily μ ρ flag k
    (profileOfScores ((splitScorePairs μ).symm (d, z)))).card : ℝ≥0∞) ∂ν
  let B := ∑ σ ∈ S, ν (incompatibleReversePermutationEvent μ ρ σ d)
  have hk' := Finset.mem_Icc.mp hk
  have hkδ := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk'.2)
    hlow.error_nonneg).trans hlow.cumulative_error
  have hsurv := reverseSupportCoefficient_ge hlow.error_le_one hkδ (hlow.label_loss k hk)
  have hunf := lintegral_realizedReverseSupportCount_fixedMask_ge μ d flag U h.measurable_reveal
    A hk'.1 η hlow.forbidden_weight h.female_nonneg h.female_lt_one h.male_mem
    hlow.male_total_ge_two hlow.competitor_mass hlow.male_max hlow.arc_error hlow.error_le_one h.tie_free
  have hmass : c = (forwardScoreMaskActiveMaleLaw d flag) U *
      (forwardScoreMaskInactiveColumnLaw d flag) univ :=
    forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg h.female_lt_one h.tie_free
  have htotal : c * ENNReal.ofReal (3 / 16) ≤ G + B := by
    dsimp only at hunf
    rw [← hmass, mul_assoc, lintegral_realizedReversePermutationCount_eq_compat_add_loss] at hunf
    exact (mul_le_mul_right hsurv c).trans hunf
  have hbad : B ≤ c * ENNReal.ofReal (3 / 32) := by
    have hb := sum_measure_incompatibleReversePermutationEvent_le μ ρ d flag U k h
    have ha' : 1 ≤ ENNReal.ofReal a := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha
    refine hb.trans (mul_le_mul_right (?_ : _ ≤ ENNReal.ofReal (3 / 32)) c)
    exact (mul_le_mul_left (mul_le_mul' (pow_le_pow_right' ha' hk'.2)
      (Nat.cast_le.mpr hk'.2)) _).trans hbudget
  have hfinite : c * ENNReal.ofReal (3 / 32) ≠ ⊤ := by
    let : IsFiniteMeasure ν := by unfold ν forwardMaskRevealLaw; infer_instance
    exact ENNReal.mul_ne_top (measure_ne_top ν univ) ENNReal.ofReal_ne_top
  apply (ENNReal.add_le_add_iff_left hfinite).mp
  calc
    _ = c * ENNReal.ofReal (3 / 16) := by
      change c * ENNReal.ofReal (3 / 32) + c * ENNReal.ofReal (3 / 32) = _
      rw [← mul_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    _ ≤ G + B := htotal
    _ ≤ c * ENNReal.ofReal (3 / 32) + G :=
      (add_le_add le_rfl hbad).trans_eq (add_comm _ _)

/-- The compatible first moment grows linearly in the support cutoff. -/
theorem lintegral_sum_card_compatibleReverseSupportFamily_ge {n K : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) {a D m δ : ℝ} {η : ℝ≥0∞}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hlow : ReverseUnfilteredControls μ ρ d flag K η m δ) (ha : 1 ≤ a)
    (hbudget : ENNReal.ofReal a ^ K * (K : ℝ≥0∞) *
      ENNReal.ofReal (a * D / ∑ i, (diagonalPairAt d i).1) ≤ ENNReal.ofReal (3 / 32)) :
    (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 32) * ((K - 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ z, (∑ k ∈ Finset.Icc 2 K, ((compatibleReverseSupportFamily μ ρ flag k
        (profileOfScores ((splitScorePairs μ).symm (d, z)))).card : ℝ≥0∞))
        ∂forwardMaskRevealLaw d flag U := by
  let c := (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 32)
  rw [lintegral_finsetSum _ (fun k _ ↦ measurable_card_compatibleReverseSupportFamily μ ρ d flag k)]
  calc
    _ = ∑ _k ∈ Finset.Icc 2 K, c := by
      rw [Finset.sum_const, Nat.card_Icc, show K + 1 - 2 = K - 1 by omega, nsmul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun k hk ↦
      lintegral_card_compatibleReverseSupportFamily_ge μ ρ d flag U h hlow hk ha hbudget

/-- At the singleton anchor, the compatible families counted in the first
moment are actual truncated pivot decorations, with no double-counting. -/
theorem sum_card_compatibleReverseSupportFamily_le_card_pivotDecoration {n : ℕ}
    {p : Profile n} {μ₀ : Matching n} (hopt : IsManOptimal p μ₀)
    (r : Rotation p μ₀) (flag : OffDiagonalCellIndex n → Bool) (K : ℕ) :
    let μ := (singletonRotationAnchor hopt r).val
    (∑ k ∈ Finset.Icc 2 K,
      (compatibleReverseSupportFamily μ r.val.cycle flag k p).card) ≤
      Nat.card (PivotDecoration hopt K r) := by
  intro μ
  let ρ := r.val.cycle
  let S (k : ℕ) := compatibleReverseSupportFamily μ ρ flag k p
  refine sum_card_compatibleReversePermutationFamilies_le_card_pivotDecoration hopt K r
    (Finset.Icc 2 K) S ?_ ?_
  · intro k _ σ hσ
    exact (mem_goodReverseSupportPermutations.mp (mem_compatibleReversePermutations.mp hσ).1).1
  · intro k hk σ hσ
    have hc := mem_compatibleReversePermutations.mp hσ
    have hs := mem_goodReverseSupportPermutations.mp hc.1
    change RealizesSuccessorPermutation (swapProfile p) μ.symm σ ∧ σ.support.card ≤ K ∧
      (∀ m ∈ ρ.support, μ m ∉ σ.support) ∧ IsExposedRotation p (undoReverseRotation μ σ) ρ
    refine ⟨hc.2.1, hs.1.trans_le (Finset.mem_Icc.mp hk).2, ?_, hc.2.2⟩
    exact fun m hm hmem ↦ (hs.2 (μ m) hmem).1 (Finset.mem_map.mpr ⟨m, hm, rfl⟩)

end LennonPittelFormalization

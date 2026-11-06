module

public import LennonPittel.PivotConditionalMean
public import LennonPittel.PivotSingletonMarkedLength

/-!
# Upper moments of the filtered count at an eligible fixed mark

For the first moment we forget the filters, then group successor permutations
by support size. For the second moment we forget the support bound as well,
and use the fact that successor permutations encode subsets of exposed cycles.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

variable {n : ℕ}

private theorem measurable_localUpperReverseProfile (μ : Matching n)
    (d : DiagonalScorePairs n) : Measurable (fun z : OffDiagonalScorePairs n ↦
      swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) :=
  (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
    ((measurable_profileOfScores n).comp (measurable_fixedDiagonalReconstruction μ d))

private theorem markedFilteredChoice_realizes {μ ρ σ : Matching n}
    {flag : OffDiagonalCellIndex n → Bool} {K L : ℕ} {t : ℝ} {x : ScoreProfile n}
    (h : σ ∈ markedFilteredChoices μ ρ flag K L t x) :
    RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ := by
  classical
  exact (mem_compatibleReversePermutations.mp (Finset.mem_filter.mp
    (mem_markedFilteredChoices.mp h).2).1).2.1

/-- At a single support size the expected number of realized permutations
is at most the reveal mass times the per-arc inflation to that power. -/
theorem lintegral_realizedReverseSupportCard_le (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (k : ℕ) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, (realizedReversePermutationCount (Finset.univ.filter
      (fun σ : Matching n ↦ σ.support.card = k))
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞)
      ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (1 + δ) ^ k := by
  classical
  let ν := forwardMaskRevealLaw d flag U
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  let S := (Finset.univ : Finset (Matching n)).filter (fun σ ↦ σ.support.card = k)
  let r := reverseSpouseWeights μ d
  let c := ν univ
  let q := ENNReal.ofReal (1 + δ)
  change (∫⁻ z, (realizedReversePermutationCount S (P z) μ.symm : ℝ≥0∞) ∂ν) ≤ c * q ^ k
  rw [lintegral_realizedReversePermutationCount ν P (measurable_localUpperReverseProfile μ d) μ.symm S]
  calc
    _ ≤ ∑ σ ∈ S, (c * q ^ k) * ∏ i ∈ σ.support, r i := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
      have hk : σ.support.card = k := (Finset.mem_filter.mp hσ).2
      have he := measure_realizesReverseSuccessorPermutation_fixedMask μ σ d flag U
        h.measurable_reveal h.female_nonneg h.female_lt_one h.tie_free
      rw [← forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg
        h.female_lt_one h.tie_free] at he
      change ν {z | RealizesSuccessorPermutation (P z) μ.symm σ} ≤ _
      rw [he, mul_assoc]
      refine mul_le_mul_right ?_ c
      calc
        _ ≤ ∏ i ∈ σ.support, q * r (σ i) := by
          refine Finset.prod_le_prod fun i _ ↦ ?_
          exact normalizedForwardInactiveColumnLaw_reverseArc_le d flag (μ.symm i) (μ.symm (σ i))
            (h.female_nonneg _) (h.female_lt_one _) h.male_mem h.male_total_pos
            (by linarith [hu.perturbation_nonneg]) (fun j _ ↦ hu.competitor_mass _ j)
        _ = _ := by
          rw [σ.prod_comp σ.support (fun i ↦ q * r i) (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi),
            Finset.prod_mul_distrib, Finset.prod_const, hk]
    _ = (c * q ^ k) * ∑ σ ∈ S, ∏ i ∈ σ.support, r i := (Finset.mul_sum ..).symm
    _ ≤ (c * q ^ k) * 1 := mul_le_mul_right
      (sum_supportPermutation_weights_le_one k r
        (sum_reverseSpouseWeights μ d (fun i ↦ (h.male_mem i).1) h.male_total_pos)) _
    _ = _ := mul_one _

private theorem card_markedFilteredChoices_le_sum_supportSizes
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    (t : ℝ) (x : ScoreProfile n) :
    (markedFilteredChoices μ ρ flag K L t x).card ≤
      ∑ k ∈ Finset.range (K + 1), realizedReversePermutationCount (Finset.univ.filter
        (fun σ : Matching n ↦ σ.support.card = k)) (swapProfile (profileOfScores x)) μ.symm := by
  classical
  let S (k : ℕ) := (Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k)).filter
    (RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm)
  have hdisj : (↑(Finset.range (K + 1)) : Set ℕ).PairwiseDisjoint S := by
    intro k _ l _ hne
    exact Finset.disjoint_left.mpr fun σ hk hl ↦
      hne (((Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2).symm.trans
        ((Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2))
  change _ ≤ ∑ k ∈ Finset.range (K + 1), (S k).card
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro σ hσ
  exact Finset.mem_biUnion.mpr ⟨σ.support.card,
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_markedFilteredChoices.mp hσ).1),
    Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, markedFilteredChoice_realizes hσ⟩⟩

/-- Forgetting all three filters gives a linear first-moment bound, up to
the uniform inflation on the largest permitted support. -/
theorem lintegral_markedFilteredChoices_fixedMask_le (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (K L : ℕ) (t : ℝ) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, ((markedFilteredChoices μ ρ flag K L t
      ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ * (ENNReal.ofReal (1 + δ) ^ K * (↑(K + 1) : ℝ≥0∞)) := by
  classical
  let ν := forwardMaskRevealLaw d flag U
  let f (k : ℕ) (z : OffDiagonalScorePairs n) : ℝ≥0∞ :=
    realizedReversePermutationCount (Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k))
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm
  let q := ENNReal.ofReal (1 + δ)
  have hf (k : ℕ) : Measurable (f k) :=
    (show Measurable (fun p : Profile n ↦ (realizedReversePermutationCount
      (Finset.univ.filter (fun σ : Matching n ↦ σ.support.card = k)) p μ.symm : ℝ≥0∞)) from
        fun _ _ ↦ MeasurableSet.of_discrete).comp (measurable_localUpperReverseProfile μ d)
  have hq : 1 ≤ q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hu.perturbation_nonneg)
  calc
    _ ≤ ∫⁻ z, ∑ k ∈ Finset.range (K + 1), f k z ∂ν := by
      apply lintegral_mono
      intro z
      change _ ≤ ∑ k ∈ Finset.range (K + 1), f k z
      dsimp only [f]
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr (card_markedFilteredChoices_le_sum_supportSizes μ ρ flag K L t _)
    _ = ∑ k ∈ Finset.range (K + 1), ∫⁻ z, f k z ∂ν := lintegral_finsetSum _ (fun k _ ↦ hf k)
    _ ≤ ∑ _k ∈ Finset.range (K + 1), ν univ * q ^ K := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      exact (lintegral_realizedReverseSupportCard_le μ ρ d flag U k h hu).trans
        (mul_le_mul_right (pow_le_pow_right' hq (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) _)
    _ = ν univ * (q ^ K * (↑(K + 1) : ℝ≥0∞)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ac_rfl

private theorem card_markedFilteredChoices_le_two_pow
    (μ ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ)
    (t : ℝ) (x : ScoreProfile n) :
    (markedFilteredChoices μ ρ flag K L t x).card ≤
      2 ^ numExposedRotations (swapProfile (profileOfScores x)) μ.symm := by
  classical
  let P := fun σ : Matching n ↦
    RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ
  let S := Finset.univ.filter P
  have hc : S.card = Nat.card {σ : Matching n // P σ} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype S (by simp [S])]
  rw [← card_realizesSuccessorPermutation, ← hc]
  exact Finset.card_le_card fun σ hσ ↦ Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, markedFilteredChoice_realizes hσ⟩

/-- The raw marked count squared is dominated by the unrestricted
cycle-subset second moment. -/
theorem lintegral_sq_markedFilteredChoices_fixedMask_le (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (K L : ℕ) (t : ℝ) (hn : 0 < n) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, ((markedFilteredChoices μ ρ flag K L t
      ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ^ 2 ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ *
        ENNReal.ofReal (reverseFilterSecondMomentConstant C * (n : ℝ) * Real.sqrt n) := by
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  calc
    _ ≤ ∫⁻ z, (4 : ℝ≥0∞) ^ numExposedRotations (P z) μ.symm ∂forwardMaskRevealLaw d flag U := by
      apply lintegral_mono
      intro z
      have hc : ((markedFilteredChoices μ ρ flag K L t
          ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ≤
          (2 : ℝ≥0∞) ^ numExposedRotations (P z) μ.symm := by
        exact_mod_cast card_markedFilteredChoices_le_two_pow μ ρ flag K L t
          ((splitScorePairs μ).symm (d, z))
      refine (pow_le_pow_left' hc 2).trans_eq ?_
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    _ ≤ _ := by
      have hm := lintegral_four_pow_numReverseExposedRotations_fixedMask_le μ d flag U
        h.measurable_reveal hn h.female_nonneg h.female_lt_one h.male_mem h.male_total_pos
        hu.perturbation_nonneg hu.perturbation_le hu.competitor_mass h.tie_free
      dsimp only at hm
      rw [← forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg
        h.female_lt_one h.tie_free] at hm
      exact hm

/-- A real-valued moment bound supported on the local eligibility event. -/
noncomputable def localPivotMomentCeiling (b A B c : ℝ) (μ ρ : Matching n)
    (x : ScoreProfile n) : ℝ :=
  {x | IsLocallyEligiblePivot b A B x μ ρ}.indicator (fun _ ↦ c) x

theorem measurable_maleReveal_localPivotMomentCeiling (b A B c : ℝ) (μ ρ : Matching n) :
    Measurable[pivotMaleRevealSpace μ] (localPivotMomentCeiling b A B c μ ρ) :=
  measurable_const.indicator (measurableSet_isLocallyEligiblePivot_maleRevealSpace b A B μ ρ)

private theorem lintegral_fixedMask_localPivotMoment_le {b A B c : ℝ} (K L e : ℕ)
    (he : e ≠ 0) (μ ρ : Matching n) (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) {W : Set (PivotMaleRevealData n)}
    (hW : MeasurableSet W)
    (hfixed : ∀ U : Set (ForwardRevealedMaleScores flag), MeasurableSet U →
      U ⊆ eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) →
      LocalPivotGeometry b A B μ ρ d flag →
      (∫⁻ z, ((markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal d))
        ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ^ e ∂forwardMaskRevealLaw d flag U) ≤
        (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal c) :
    let R (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
    let S := pivotMaleReveal μ ⁻¹' W
    let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
      (forwardScoreMaskEvent d flag)
    (∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
      (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z) ∂ν) ≤
      ∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
        (localPivotMomentCeiling b A B c μ ρ x)) (R z) ∂ν := by
  classical
  dsimp only
  let R (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
  let S := pivotMaleReveal μ ⁻¹' W
  let ν := ((offDiagonalScoreLaw n).restrict (offDiagonalNonblocking d)).restrict
    (forwardScoreMaskEvent d flag)
  let U₀ := eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d)
  let U := U₀ ∩ (fun v ↦ pivotMaleRevealSection flag (d, v)) ⁻¹' W
  let V := (fun z ↦ (forwardRevealWithColumns flag z).1) ⁻¹' U
  let N (z : OffDiagonalScorePairs n) : ℝ≥0∞ := ((markedFilteredChoices μ ρ flag K L
    (reverseIncrementCutoff n (reverseDiagonalMaleTotal d)) (R z)).card : ℝ≥0∞) ^ e
  have hmask : ∀ᵐ z ∂ν, z ∈ forwardScoreMaskEvent d flag :=
    ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)
  change (∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
    (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z) ∂ν) ≤
    ∫⁻ z, S.indicator (fun x ↦ ENNReal.ofReal
      (localPivotMomentCeiling b A B c μ ρ x)) (R z) ∂ν
  by_cases hgeo : LocalPivotGeometry b A B μ ρ d flag
  · have hU : MeasurableSet U := (measurableSet_eligiblePivotRevealSet d flag ρ _).inter
      (hW.preimage ((measurable_pivotMaleRevealSection flag).comp
        (measurable_const.prodMk measurable_id)))
    have hV : MeasurableSet V := hU.preimage (measurable_forwardRevealWithColumns flag).fst
    have hV' (z : OffDiagonalScorePairs n) (hz : z ∈ forwardScoreMaskEvent d flag) :
        z ∈ V ↔ R z ∈ S ∧ IsLocallyEligiblePivot b A B (R z) μ ρ := by
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hR := pivotMaleReveal_reconstruct μ d z flag hz
      change ((forwardRevealWithColumns flag z).1 ∈ U₀ ∧
        pivotMaleRevealSection flag (d, (forwardRevealWithColumns flag z).1) ∈ W) ↔ _
      change _ ↔ pivotMaleReveal μ (R z) ∈ W ∧ _
      rw [show pivotMaleReveal μ (R z) = _ from hR, hE, and_iff_right hgeo, and_comm]
    have hceil : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localPivotMomentCeiling b A B c μ ρ x)) (R z)) =ᵐ[ν]
        V.indicator (fun _ ↦ ENNReal.ofReal c) := by
      filter_upwards [hmask] with z hz
      by_cases hs : R z ∈ S <;> by_cases hE : IsLocallyEligiblePivot b A B (R z) μ ρ <;>
        simp [localPivotMomentCeiling, indicator_apply, hV' z hz, hs, hE]
    have hN : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z)) =ᵐ[ν] V.indicator N := by
      filter_upwards [hmask] with z hz
      by_cases hs : R z ∈ S
      · by_cases hE : IsLocallyEligiblePivot b A B (R z) μ ρ
        · have hR : splitScorePairs μ (R z) = (d, z) := (splitScorePairs μ).apply_symm_apply _
          have hz' : (splitScorePairs μ (R z)).2 ∈
              forwardScoreMaskEvent (splitScorePairs μ (R z)).1 flag := by rw [hR]; exact hz
          rw [indicator_of_mem hs, indicator_of_mem ((hV' z hz).mpr ⟨hs, hE⟩),
            localFilteredDecorationCount_of_eligible_of_fixedMask K L hE hz', hR]
          simp [N]
        · simp [localFilteredDecorationCount, hV' z hz, hs, hE, zero_pow he]
      · simp [hV' z hz, hs]
    rw [lintegral_congr_ae hN, lintegral_congr_ae hceil, lintegral_indicator hV,
      lintegral_indicator hV, lintegral_const, mul_comm]
    exact hfixed U hU inter_subset_left hgeo
  · have hz : (fun z ↦ S.indicator (fun x ↦ ENNReal.ofReal
        (localFilteredDecorationCount b A B K L μ ρ x) ^ e) (R z)) =ᵐ[ν] (fun _ ↦ 0) := by
      filter_upwards [hmask] with z hz
      have hE := isLocallyEligiblePivot_reconstruct_iff (b := b) (A := A) (B := B) μ ρ d z flag hz
      have hnot : ¬ IsLocallyEligiblePivot b A B (R z) μ ρ := fun h ↦ hgeo (hE.mp h).1
      simp [localFilteredDecorationCount, indicator_apply, hnot, zero_pow he]
    rw [lintegral_congr_ae hz, lintegral_zero]
    exact zero_le

/-- Transport a fixed-mask moment upper bound to every smaller-reveal test. -/
theorem setLIntegral_localPivotMoment_le {b A B c : ℝ} (K L e : ℕ) (he : e ≠ 0)
    (μ ρ : Matching n)
    (hfixed : ∀ᵐ d ∂diagonalScoreLaw n, ∀ (flag : OffDiagonalCellIndex n → Bool)
      (U : Set (ForwardRevealedMaleScores flag)), MeasurableSet U →
      U ⊆ eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) →
      LocalPivotGeometry b A B μ ρ d flag →
      (∫⁻ z, ((markedFilteredChoices μ ρ flag K L
        (reverseIncrementCutoff n (reverseDiagonalMaleTotal d))
        ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞) ^ e ∂forwardMaskRevealLaw d flag U) ≤
        (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal c)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫⁻ x in S, ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x) ^ e
      ∂stableMarkScoreLaw μ) ≤
      ∫⁻ x in S, ENNReal.ofReal (localPivotMomentCeiling b A B c μ ρ x) ∂stableMarkScoreLaw μ := by
  have hSm := pivotMaleRevealSpace_le μ _ hS
  change ∃ W : Set (PivotMaleRevealData n), MeasurableSet W ∧ pivotMaleReveal μ ⁻¹' W = S at hS
  obtain ⟨W, hW, rfl⟩ := hS
  let S := pivotMaleReveal μ ⁻¹' W
  let f := fun x ↦ ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x) ^ e
  let g := fun x ↦ ENNReal.ofReal (localPivotMomentCeiling b A B c μ ρ x)
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp
    (measurable_localFilteredDecorationCount b A B K L μ ρ)).pow_const _
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((measurable_maleReveal_localPivotMomentCeiling b A B c μ ρ).mono
      (pivotMaleRevealSpace_le μ) le_rfl)
  change (∫⁻ x in S, f x ∂stableMarkScoreLaw μ) ≤ ∫⁻ x in S, g x ∂stableMarkScoreLaw μ
  calc
    _ = ∫⁻ x, S.indicator f x ∂stableMarkScoreLaw μ := (lintegral_indicator hSm f).symm
    _ ≤ ∫⁻ x, S.indicator g x ∂stableMarkScoreLaw μ := by
      rw [lintegral_stableMarkScoreLaw μ (hf.indicator hSm),
        lintegral_stableMarkScoreLaw μ (hg.indicator hSm)]
      apply lintegral_mono_ae
      filter_upwards [hfixed] with d hd
      rw [lintegral_offDiagonalNonblocking_eq_sum_masks d,
        lintegral_offDiagonalNonblocking_eq_sum_masks d]
      exact Finset.sum_le_sum fun flag _ ↦
        lintegral_fixedMask_localPivotMoment_le K L e he μ ρ d flag hW (hd flag)
    _ = _ := lintegral_indicator hSm g

theorem integrable_localFilteredDecorationCount_pow (b A B : ℝ) (K L e : ℕ)
    (μ ρ : Matching n) (ν : Measure (ScoreProfile n)) [IsFiniteMeasure ν] :
    Integrable (fun x ↦ localFilteredDecorationCount b A B K L μ ρ x ^ e) ν := by
  refine (integrable_const ((n.factorial : ℝ) ^ e)).mono'
    ((measurable_localFilteredDecorationCount b A B K L μ ρ).pow_const e).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  have hp : 0 ≤ localFilteredDecorationCount b A B K L μ ρ x ^ e :=
    pow_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x) _
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  exact pow_le_pow_left₀ (localFilteredDecorationCount_nonneg b A B K L μ ρ x)
    (localFilteredDecorationCount_le_factorial b A B K L μ ρ x) e

private theorem setIntegral_localPivotMoment_le_of_setLIntegral {b A B c : ℝ} (K L e : ℕ)
    (hc : 0 ≤ c) (μ ρ : Matching n) {S : Set (ScoreProfile n)}
    (hlin : (∫⁻ x in S, ENNReal.ofReal (localFilteredDecorationCount b A B K L μ ρ x) ^ e
      ∂stableMarkScoreLaw μ) ≤
      ∫⁻ x in S, ENNReal.ofReal (localPivotMomentCeiling b A B c μ ρ x) ∂stableMarkScoreLaw μ) :
    (∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ^ e ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localPivotMomentCeiling b A B c μ ρ x ∂stableMarkScoreLaw μ := by
  have hf := (integrable_localFilteredDecorationCount_pow b A B K L e μ ρ
    (stableMarkScoreLaw μ)).integrableOn (s := S)
  have hg := ((integrable_const c (μ := stableMarkScoreLaw μ)).indicator
    (measurableSet_isLocallyEligiblePivot b A B μ ρ)).integrableOn (s := S)
  have hnf : ∀ᵐ x ∂(stableMarkScoreLaw μ).restrict S,
      0 ≤ localFilteredDecorationCount b A B K L μ ρ x ^ e :=
    Eventually.of_forall fun x ↦ pow_nonneg (localFilteredDecorationCount_nonneg b A B K L μ ρ x) _
  have hng : ∀ᵐ x ∂(stableMarkScoreLaw μ).restrict S, 0 ≤ localPivotMomentCeiling b A B c μ ρ x :=
    Eventually.of_forall fun x ↦ Set.indicator_nonneg (fun _ _ ↦ hc) x
  rw [integral_eq_lintegral_of_nonneg_ae hnf hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hng hg.aestronglyMeasurable]
  apply ENNReal.toReal_mono ((hasFiniteIntegral_iff_ofReal hng).mp hg.2).ne
  simpa only [ENNReal.ofReal_pow (localFilteredDecorationCount_nonneg b A B K L μ ρ _)] using hlin

private theorem pow_arcInflation_le_of_support {K : ℕ} {δ κ : ℝ} (hn : 0 < n)
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 2 / Real.sqrt (n : ℝ))
    (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    ENNReal.ofReal (1 + δ) ^ K ≤ ENNReal.ofReal (Real.exp (2 * κ)) := by
  have hn' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  rw [← ENNReal.ofReal_pow (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (1 + δ) ^ K ≤ (Real.exp δ) ^ K := pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp δ) _
    _ = Real.exp ((K : ℝ) * δ) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr <| calc
      (K : ℝ) * δ ≤ (κ * Real.sqrt (n : ℝ)) * (2 / Real.sqrt (n : ℝ)) :=
        mul_le_mul hK hδ' hδ (by positivity)
      _ = 2 * κ := by field_simp

/-- Almost every diagonal has the local certificate at every eligible mask.
The certificate also carries lower-moment controls, which are not needed here. -/
abbrev LocalUpperMomentControls (b A B : ℝ) (K L : ℕ) (μ ρ : Matching n) : Prop :=
  ∀ᵐ d ∂diagonalScoreLaw n, ∀ flag,
    LocalPivotGeometry b A B μ ρ d flag →
    EligibleReverseMomentCertificate μ ρ d flag K L (localPivotIncrementCap B d)
      (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
      (B / Real.sqrt (n : ℝ))

/-- The real first-moment ceiling tested on all smaller-reveal events. -/
theorem setIntegral_localFilteredDecorationCount_le {b A B κ : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hκ : 0 ≤ κ) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hcert : LocalUpperMomentControls b A B K L μ ρ)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localPivotMomentCeiling b A B
        (Real.exp (2 * κ) * (↑(K + 1) : ℝ)) μ ρ x ∂stableMarkScoreLaw μ := by
  have hlin := setLIntegral_localPivotMoment_le (b := b) (A := A) (B := B)
    (c := Real.exp (2 * κ) * (↑(K + 1) : ℝ)) K L 1 one_ne_zero μ ρ ?_ hS
  · simpa only [pow_one] using
      setIntegral_localPivotMoment_le_of_setLIntegral K L 1 (by positivity) μ ρ hlin
  filter_upwards [hcert] with d hd flag U hU hsub hgeo
  have h := hd flag hgeo
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_natCast]
  simp only [pow_one]
  refine (lintegral_markedFilteredChoices_fixedMask_le μ ρ d flag U K L _
    (h.compatibility.restrict_reveal hU hsub) h.upper).trans ?_
  exact mul_le_mul_right (mul_le_mul_left (pow_arcInflation_le_of_support h.n_pos hκ
    h.upper.perturbation_nonneg h.upper.perturbation_le hK) _) _

/-- The real second-moment ceiling tested on all smaller-reveal events. -/
theorem setIntegral_sq_localFilteredDecorationCount_le {b A B : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hcert : LocalUpperMomentControls b A B K L μ ρ)
    {S : Set (ScoreProfile n)} (hS : MeasurableSet[pivotMaleRevealSpace μ] S) :
    (∫ x in S, localFilteredDecorationCount b A B K L μ ρ x ^ 2 ∂stableMarkScoreLaw μ) ≤
      ∫ x in S, localPivotMomentCeiling b A B
        (reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n) μ ρ x ∂stableMarkScoreLaw μ := by
  have hc : 0 ≤ reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n := by
    unfold reverseFilterSecondMomentConstant
    positivity
  apply setIntegral_localPivotMoment_le_of_setLIntegral K L 2 hc μ ρ
  apply setLIntegral_localPivotMoment_le K L 2 (by decide) μ ρ _ hS
  filter_upwards [hcert] with d hd flag U hU hsub hgeo
  have h := hd flag hgeo
  exact lintegral_sq_markedFilteredChoices_fixedMask_le μ ρ d flag U K L _ h.n_pos
    (h.compatibility.restrict_reveal hU hsub) h.upper

/-- On eligible marks the conditional mean is bounded by a constant times
the number of possible support sizes; off eligibility the ceiling is zero. -/
theorem localPivotConditionalMean_le_ceiling_ae {b A B κ : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hκ : 0 ≤ κ) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hcert : LocalUpperMomentControls b A B K L μ ρ) :
    localPivotConditionalMean b A B K L μ ρ ≤ᵐ[stableMarkScoreLaw μ]
      localPivotMomentCeiling b A B (Real.exp (2 * κ) * (↑(K + 1) : ℝ)) μ ρ := by
  let ν := stableMarkScoreLaw μ
  let m := pivotMaleRevealSpace μ
  let f := localFilteredDecorationCount b A B K L μ ρ
  let g := localPivotMomentCeiling b A B (Real.exp (2 * κ) * (↑(K + 1) : ℝ)) μ ρ
  have hm := pivotMaleRevealSpace_le μ
  have hf : Integrable f ν := integrable_localFilteredDecorationCount b A B K L μ ρ ν
  have hg : Integrable g ν := (integrable_const _).indicator
    (measurableSet_isLocallyEligiblePivot b A B μ ρ)
  have hgm : StronglyMeasurable[m] g :=
    (measurable_maleReveal_localPivotMomentCeiling b A B _ μ ρ).stronglyMeasurable
  have hcm : StronglyMeasurable[m] (ν[f|m]) := stronglyMeasurable_condExp
  change ν[f|m] ≤ᵐ[ν] g
  apply ae_of_ae_trim hm
  refine ae_le_of_forall_setIntegral_le
    ((integrable_condExp (f := f)).trim hm hcm) (hg.trim hm hgm) fun S hS _ ↦ ?_
  rw [← setIntegral_trim hm hgm hS, ← setIntegral_trim hm hcm hS, setIntegral_condExp hm hf hS]
  exact setIntegral_localFilteredDecorationCount_le K L μ ρ hκ hK hcert hS

/-- The linear first-moment ceiling holds eventually for the same support
and filter budgets used for the lower bound. -/
theorem eventually_localPivotConditionalMean_le_ceiling_ae (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ (μ ρ : Matching n) (b A : ℝ),
      localPivotConditionalMean b A B (K n) (L n) μ ρ ≤ᵐ[stableMarkScoreLaw μ]
        localPivotMomentCeiling b A B (Real.exp (2 * κ) * (↑(K n + 1) : ℝ)) μ ρ := by
  filter_upwards [eventually_ae_diagonal_localPivotGeometry_certificate K L hB hκ hK hL
    hsmallLabel hsmallCompat, hK] with n hn hcap μ ρ b A
  exact localPivotConditionalMean_le_ceiling_ae (K n) (L n) μ ρ hκ hcap.2 <|
    (hn μ).mono fun d hd flag hgeom ↦ hd ρ flag hgeom

private theorem stableMark_localEligibility_mass_le (b A B : ℝ) (μ ρ : Matching n) :
    stableMarkScoreLaw μ {x | IsLocallyEligiblePivot b A B x μ ρ} ≤
      continuousScoreLaw n (scoreStableSingletonAnchorEvent μ ρ) := by
  rw [stableMarkScoreLaw, Measure.restrict_apply (measurableSet_isLocallyEligiblePivot b A B μ ρ)]
  apply measure_mono_ae
  filter_upwards [ae_injective_rows n] with x hx he
  exact ⟨he.2, he.1.isSoleForwardExposed hx⟩

/-- The mass of all eligible marks is no larger than the mean number of
singleton anchors. This retains the saving from the exposure event. -/
theorem sum_stableMark_localEligibility_mass_le (b A B : ℝ) :
    (∑ μ : Matching n, ∑ ρ : Matching n,
      stableMarkScoreLaw μ {x | IsLocallyEligiblePivot b A B x μ ρ}) ≤
    ∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
      ∂(uniformProfile n).toMeasure := by
  rw [lintegral_profileSingletonAnchorLengthWeight_eq_sum_scoreStableSingletonAnchorEvent]
  simpa only [one_mul] using Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) ↦
    Finset.sum_le_sum fun ρ (_ : ρ ∈ Finset.univ) ↦ stableMark_localEligibility_mass_le b A B μ ρ

/-- The unconditional second moment at a fixed mark retains its eligibility
mass as a factor; no normalization of the fixed-mark law is needed. -/
theorem integral_sq_localFilteredDecorationCount_le_mass {b A B : ℝ} (K L : ℕ)
    (μ ρ : Matching n) (hcert : LocalUpperMomentControls b A B K L μ ρ) :
    (∫ x, localFilteredDecorationCount b A B K L μ ρ x ^ 2 ∂stableMarkScoreLaw μ) ≤
      (reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n) *
        (stableMarkScoreLaw μ).real {x | IsLocallyEligiblePivot b A B x μ ρ} := by
  have h := setIntegral_sq_localFilteredDecorationCount_le K L μ ρ hcert
    (S := univ) MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  unfold localPivotMomentCeiling at h
  rw [integral_indicator_const _ (measurableSet_isLocallyEligiblePivot b A B μ ρ), smul_eq_mul,
    mul_comm] at h
  exact h

/-- The sum of the raw local square moments has order n² log n, with
explicit constants and a lower-order remainder. -/
theorem eventually_sum_integral_sq_localFilteredDecorationCount_le (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ b A : ℝ,
      (∑ μ : Matching n, ∑ ρ : Matching n,
        ∫ x, localFilteredDecorationCount b A B (K n) (L n) μ ρ x ^ 2 ∂stableMarkScoreLaw μ) ≤
        reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n *
          ((Real.exp 5 * (108 + 48 * Real.exp 4)) * Real.sqrt n * Real.log n +
            (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_ae_diagonal_localPivotGeometry_certificate K L hB hκ hK hL
    hsmallLabel hsmallCompat, eventually_lintegral_profileSingletonAnchorCount_le,
    eventually_gt_atTop (0 : ℕ)] with n hn hmass hn' b A
  let E (μ ρ : Matching n) := {x | IsLocallyEligiblePivot b A B x μ ρ}
  let c := reverseFilterSecondMomentConstant 2 * (n : ℝ) * Real.sqrt n
  let M := (Real.exp 5 * (108 + 48 * Real.exp 4)) * Real.sqrt n * Real.log n +
    (n : ℝ) ^ (-3 : ℝ)
  have hc : 0 ≤ c := by unfold c reverseFilterSecondMomentConstant; positivity
  have hM : 0 ≤ M := by
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn')
    unfold M
    positivity
  have hmass' : (∑ μ : Matching n, ∑ ρ : Matching n, stableMarkScoreLaw μ (E μ ρ)) ≤
      ENNReal.ofReal M := (sum_stableMark_localEligibility_mass_le b A B).trans hmass
  have hreal : (∑ μ : Matching n, ∑ ρ : Matching n, (stableMarkScoreLaw μ).real (E μ ρ)) ≤ M := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass'
    rw [ENNReal.toReal_ofReal hM, ENNReal.toReal_sum (fun μ _ ↦
      ENNReal.sum_ne_top.mpr fun ρ _ ↦ measure_ne_top (stableMarkScoreLaw μ) (E μ ρ))] at h
    simp_rw [ENNReal.toReal_sum (fun ρ _ ↦ measure_ne_top (stableMarkScoreLaw _) (E _ ρ))] at h
    exact h
  calc
    _ ≤ ∑ μ : Matching n, ∑ ρ : Matching n, c * (stableMarkScoreLaw μ).real (E μ ρ) := by
      refine Finset.sum_le_sum fun μ _ ↦ Finset.sum_le_sum fun ρ _ ↦ ?_
      exact integral_sq_localFilteredDecorationCount_le_mass (K n) (L n) μ ρ <|
        (hn μ).mono fun d hd flag hgeom ↦ hd ρ flag hgeom
    _ = c * ∑ μ : Matching n, ∑ ρ : Matching n, (stableMarkScoreLaw μ).real (E μ ρ) := by
      simp_rw [Finset.mul_sum]
    _ ≤ c * M := mul_le_mul_of_nonneg_left hreal hc

end LennonPittelFormalization

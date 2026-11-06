module

public import LennonPittel.PivotReverseFilteredCount
public import LennonPittel.PivotReverseMaskMoment
public import LennonPittel.MeasureCountFilterLoss
public import LennonPittel.ReverseCycleTypeWeightTransfer
public import LennonPittel.ShortCycleChebyshev
public import LennonPittel.UniformShortCycleMoments

/-!
# Loss of first moment from the two reverse-decoration filters

The short-cycle count is controlled on permutations of positions, then
transferred to weighted collections. The large-increment count is
controlled by the total second moment on one rare event per anchor.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The upper-arc perturbation and inactive masses used to bound the two
filter losses. These concern the original columns, not the relaxed ones. -/
structure ReverseFilterUpperControls {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (δ C : ℝ) : Prop where
  perturbation_nonneg : 0 ≤ δ
  perturbation_le : δ ≤ C / Real.sqrt (n : ℝ)
  competitor_mass : ∀ (i : Fin n) (q : ForwardInactiveColumnIndex flag i),
    (∑ j, (diagonalPairAt d j).1) / (1 + δ) ≤
      ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
        (diagonalPairAt d t.val.val.val.val.1).1
  available_mass : ∀ i, (∑ j, (diagonalPairAt d j).1) / 2 ≤
    ∑ q : ForwardInactiveColumnIndex flag i, (diagonalPairAt d q.val.val.val.1).1

open scoped Classical in
/-- Uniformly in the number of positions, the short-cycle cap is violated
by at most a fraction `4 / log L` of permutations. -/
theorem shortCycleCapBad_uniformMass_le (k L : ℕ) (hL : 2 ≤ L) :
    (((Finset.univ : Finset (Equiv.Perm (Fin k))).filter
      (fun σ ↦ shortCycleCapBad L σ.cycleType)).card : ℝ≥0∞) /
      (k.factorial : ℝ≥0∞) ≤ ENNReal.ofReal (4 / Real.log (L : ℝ)) :=
  shortCycleChebyshev_ennreal hL (shortCycleCount L)
    (sum_shortCycleCount k L) (sum_shortCycleCount_mul_sub_one_le k L)

private theorem measurable_reconstructedReverseProfile {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) : Measurable (fun z : OffDiagonalScorePairs n ↦
      swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) :=
  (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp
    ((measurable_profileOfScores n).comp (measurable_fixedDiagonalReconstruction μ d))

/-- First-moment cost of the short-cycle cap at one support size, before
requiring compatibility. -/
theorem lintegral_shortCycleRejectedCandidates_le {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (k L : ℕ) (hL : 2 ≤ L) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, (realizedReversePermutationCount (shortCycleRejectedCandidates μ ρ flag k L)
      (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞)
      ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (1 + δ) ^ k *
        ENNReal.ofReal (4 / Real.log (L : ℝ)) := by
  classical
  let ν := forwardMaskRevealLaw d flag U
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  let S := shortCycleRejectedCandidates μ ρ flag k L
  let r := reverseSpouseWeights μ d
  let c := ν univ
  let q := ENNReal.ofReal (1 + δ)
  have hmem (σ : Matching n) (hσ : σ ∈ S) : σ.support.card = k ∧ shortCycleCapBad L σ.cycleType := by
    obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hσ
    exact ⟨(mem_goodReverseSupportPermutations.mp h₁).1, h₂⟩
  have hW : (∑ σ ∈ S, ∏ i ∈ σ.support, r i) ≤ ENNReal.ofReal (4 / Real.log (L : ℝ)) := by
    let T := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun σ ↦ σ.support.card = k ∧ shortCycleCapBad L σ.cycleType)
    have hST : S ⊆ T := fun σ hσ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem σ hσ⟩
    have hT := sum_supportPermutation_cycleType_weights_le k (shortCycleCapBad L) r
      (sum_reverseSpouseWeights μ d (fun i ↦ (h.male_mem i).1) h.male_total_pos)
    exact (Finset.sum_le_sum_of_subset hST).trans (hT.trans (shortCycleCapBad_uniformMass_le k L hL))
  change (∫⁻ z, (realizedReversePermutationCount S (P z) μ.symm : ℝ≥0∞) ∂ν) ≤ _
  rw [lintegral_realizedReversePermutationCount ν P (measurable_reconstructedReverseProfile μ d) μ.symm S]
  calc
    _ ≤ ∑ σ ∈ S, (c * q ^ k) * ∏ i ∈ σ.support, r i := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
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
            Finset.prod_mul_distrib, Finset.prod_const, (hmem σ hσ).1]
    _ = (c * q ^ k) * ∑ σ ∈ S, ∏ i ∈ σ.support, r i := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right hW _

/-- Sum the short-cycle loss through the total support cutoff. -/
theorem lintegral_sum_shortCycleRejectedCandidates_le {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (K L : ℕ) (hL : 2 ≤ L) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    (∫⁻ z, (∑ k ∈ Finset.Icc 2 K,
      (realizedReversePermutationCount (shortCycleRejectedCandidates μ ρ flag k L)
        (swapProfile (profileOfScores ((splitScorePairs μ).symm (d, z)))) μ.symm : ℝ≥0∞))
      ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (1 + δ) ^ K *
        ENNReal.ofReal (4 / Real.log (L : ℝ)) * ((K - 1 : ℕ) : ℝ≥0∞) := by
  let ν := forwardMaskRevealLaw d flag U
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  let f (k : ℕ) (z : OffDiagonalScorePairs n) : ℝ≥0∞ :=
    realizedReversePermutationCount (shortCycleRejectedCandidates μ ρ flag k L) (P z) μ.symm
  let q := ENNReal.ofReal (1 + δ)
  let c := ν univ
  let b := ENNReal.ofReal (4 / Real.log (L : ℝ))
  have hf (k : ℕ) : Measurable (f k) :=
    (show Measurable (fun p : Profile n ↦ (realizedReversePermutationCount
      (shortCycleRejectedCandidates μ ρ flag k L) p μ.symm : ℝ≥0∞)) from
        fun _ _ ↦ MeasurableSet.of_discrete).comp (measurable_reconstructedReverseProfile μ d)
  have hq : 1 ≤ q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hu.perturbation_nonneg)
  change (∫⁻ z, (∑ k ∈ Finset.Icc 2 K, f k z) ∂ν) ≤ _
  rw [lintegral_finsetSum _ (fun k _ ↦ hf k)]
  calc
    _ ≤ ∑ _k ∈ Finset.Icc 2 K, (c * q ^ K * b) := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      exact (lintegral_shortCycleRejectedCandidates_le μ ρ d flag U k L hL h hu).trans
        (mul_le_mul_left (mul_le_mul_right (pow_le_pow_right' hq (Finset.mem_Icc.mp hk).2) c) b)
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, show K + 1 - 2 = K - 1 by omega, nsmul_eq_mul, mul_comm]

/-- The constant in the fixed-mask upper cycle-subset second moment. -/
noncomputable def reverseFilterSecondMomentConstant (C : ℝ) : ℝ :=
  2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2)

/-- All sizes' large-increment losses together cost at most the reveal
mass times `√constant / n²`. The global rare event is charged only once. -/
theorem lintegral_sum_incrementRejectedReverseSupportFamily_le {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (I : Finset ℕ) (hn : 0 < n) {a D δ C : ℝ}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hu : ReverseFilterUpperControls d flag δ C) :
    let X := ∑ i, (diagonalPairAt d i).1
    let t := reverseIncrementCutoff n X
    (∫⁻ z, (∑ k ∈ I, ((incrementRejectedReverseSupportFamily μ ρ flag k t
      ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞)) ∂forwardMaskRevealLaw d flag U) ≤
      (forwardMaskRevealLaw d flag U) univ *
        ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) := by
  intro X t
  let ν := forwardMaskRevealLaw d flag U
  let E := fixedDiagonalLongReverseSuccessorEvent μ d t
  let P := fun z : OffDiagonalScorePairs n ↦ swapProfile (profileOfScores
    ((splitScorePairs μ).symm (d, z)))
  let f := fun z : OffDiagonalScorePairs n ↦ (2 : ℝ≥0∞) ^ numExposedRotations (P z) μ.symm
  have hf : Measurable f :=
    (show Measurable (fun p : Profile n ↦ (2 : ℝ≥0∞) ^ numExposedRotations p μ.symm) from
      fun _ _ ↦ MeasurableSet.of_discrete).comp (measurable_reconstructedReverseProfile μ d)
  have hE : MeasurableSet E := measurableSet_fixedDiagonalLongReverseSuccessorEvent μ d t
  have hrare : ν E ≤ ν univ * ENNReal.ofReal ((n : ℝ) ^ (-7 : ℝ)) := by
    rw [show (n : ℝ) ^ (-7 : ℝ) = (n : ℝ) ^ (-7 : ℤ) by simp]
    exact measure_fixedDiagonalLongReverseSuccessorEvent_cutoff_le μ d flag U h.measurable_reveal
      hn h.female_nonneg h.female_lt_one h.male_mem h.male_total_pos hu.available_mass h.tie_free
  have hM : (∫⁻ z, f z ^ (2 : ℕ) ∂ν) ≤ ν univ *
      ENNReal.ofReal (reverseFilterSecondMomentConstant C * (n : ℝ) * Real.sqrt n) := by
    have hpow (z : OffDiagonalScorePairs n) :
        f z ^ (2 : ℕ) = (4 : ℝ≥0∞) ^ numExposedRotations (P z) μ.symm := by
      dsimp only [f]
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    simp_rw [hpow]
    have hm := lintegral_four_pow_numReverseExposedRotations_fixedMask_le μ d flag U
      h.measurable_reveal hn h.female_nonneg h.female_lt_one h.male_mem h.male_total_pos
      hu.perturbation_nonneg hu.perturbation_le hu.competitor_mass h.tie_free
    dsimp only at hm
    rw [← forwardMaskRevealLaw_univ μ d flag U h.measurable_reveal h.female_nonneg
      h.female_lt_one h.tie_free] at hm
    exact hm
  calc
    _ ≤ ∫⁻ z, E.indicator f z ∂ν := by
      refine lintegral_mono fun z ↦ ?_
      let x := (splitScorePairs μ).symm (d, z)
      have hp := sum_card_incrementRejectedReverseSupportFamily_le_indicator μ ρ flag I t x
      by_cases hz : z ∈ E
      · rw [indicator_of_mem hz]
        simpa only [indicator_of_mem (show x ∈ scoreLongReverseSuccessorEvent μ t from hz)] using hp
      · rw [indicator_of_notMem hz]
        simpa only [indicator_of_notMem (show x ∉ scoreLongReverseSuccessorEvent μ t from hz)] using hp
    _ = ∫⁻ z in E, f z ∂ν := lintegral_indicator hE f
    _ ≤ _ := lintegral_restrict_le_mass_mul_sqrt_div_sq ν E hf
      (by exact_mod_cast Nat.succ_le_of_lt hn) (by unfold reverseFilterSecondMomentConstant; positivity)
      hrare hM

private theorem lower_after_two_filter_losses {c N g s b : ℝ≥0∞}
    (hc : c ≠ ⊤) (hN : N ≠ ⊤)
    (h : c * ENNReal.ofReal (3 / 32) * N ≤ g + s + b)
    (hs : s ≤ c * ENNReal.ofReal (3 / 128) * N)
    (hb : b ≤ c * ENNReal.ofReal (3 / 128) * N) :
    c * ENNReal.ofReal (3 / 64) * N ≤ g := by
  let T := c * ENNReal.ofReal (3 / 64) * N
  have hT : T ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top) hN
  have hsum : s + b ≤ T := by
    refine (add_le_add hs hb).trans_eq ?_
    dsimp only [T]
    rw [← add_mul, ← mul_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  apply (ENNReal.add_le_add_iff_left hT).mp
  calc
    T + T = c * ENNReal.ofReal (3 / 32) * N := by
      dsimp only [T]
      rw [← add_mul, ← mul_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    _ ≤ g + s + b := h
    _ = g + (s + b) := add_assoc ..
    _ ≤ g + T := add_le_add le_rfl hsum
    _ = T + g := add_comm ..

/-- The exact two filters leave a linear lower moment when each costs at
most one quarter of the compatible margin. -/
theorem lintegral_sum_card_filteredReverseSupportFamily_ge {n K : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (L : ℕ) (hL : 2 ≤ L) (hn : 0 < n)
    {a D m δlow δ C : ℝ} {η : ℝ≥0∞}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hlow : ReverseUnfilteredControls μ ρ d flag K η m δlow)
    (hu : ReverseFilterUpperControls d flag δ C) (ha : 1 ≤ a)
    (hbudget : ENNReal.ofReal a ^ K * (K : ℝ≥0∞) *
      ENNReal.ofReal (a * D / ∑ i, (diagonalPairAt d i).1) ≤ ENNReal.ofReal (3 / 32))
    (hshort : ENNReal.ofReal (1 + δ) ^ K * ENNReal.ofReal (4 / Real.log (L : ℝ)) ≤
      ENNReal.ofReal (3 / 128))
    (hinc : ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) ≤
      ENNReal.ofReal (3 / 128) * ((K - 1 : ℕ) : ℝ≥0∞)) :
    let X := ∑ i, (diagonalPairAt d i).1
    let t := reverseIncrementCutoff n X
    (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 64) * ((K - 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ z, (∑ k ∈ Finset.Icc 2 K, ((filteredReverseSupportFamily μ ρ flag k L t
        ((splitScorePairs μ).symm (d, z))).card : ℝ≥0∞)) ∂forwardMaskRevealLaw d flag U := by
  intro X t
  let ν := forwardMaskRevealLaw d flag U
  let c := ν univ
  let N : ℝ≥0∞ := ((K - 1 : ℕ) : ℝ≥0∞)
  let I := Finset.Icc 2 K
  let x (z : OffDiagonalScorePairs n) := (splitScorePairs μ).symm (d, z)
  let f (z : OffDiagonalScorePairs n) : ℝ≥0∞ := ∑ k ∈ I,
    ((compatibleReverseSupportFamily μ ρ flag k (profileOfScores (x z))).card : ℝ≥0∞)
  let g (z : OffDiagonalScorePairs n) : ℝ≥0∞ := ∑ k ∈ I,
    ((filteredReverseSupportFamily μ ρ flag k L t (x z)).card : ℝ≥0∞)
  let s (z : OffDiagonalScorePairs n) : ℝ≥0∞ := ∑ k ∈ I,
    (realizedReversePermutationCount (shortCycleRejectedCandidates μ ρ flag k L)
      (swapProfile (profileOfScores (x z))) μ.symm : ℝ≥0∞)
  let b (z : OffDiagonalScorePairs n) : ℝ≥0∞ := ∑ k ∈ I,
    ((incrementRejectedReverseSupportFamily μ ρ flag k t (x z)).card : ℝ≥0∞)
  have hg : Measurable g := Finset.measurable_sum _ fun k _ ↦
    (measurable_card_filteredReverseSupportFamily μ ρ flag k L t).comp
      (measurable_fixedDiagonalReconstruction μ d)
  have hs : Measurable s := Finset.measurable_sum _ fun k _ ↦
    (show Measurable (fun p : Profile n ↦ (realizedReversePermutationCount
      (shortCycleRejectedCandidates μ ρ flag k L) p μ.symm : ℝ≥0∞)) from
      fun _ _ ↦ MeasurableSet.of_discrete).comp (measurable_reconstructedReverseProfile μ d)
  have hpoint (z : OffDiagonalScorePairs n) : f z ≤ g z + s z + b z := by
    dsimp only [f, g, s, b]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    exact_mod_cast card_compatibleReverseSupportFamily_le_filtered_add_rejections μ ρ flag k L t (x z)
  have hraw : c * ENNReal.ofReal (3 / 32) * N ≤ ∫⁻ z, f z ∂ν :=
    lintegral_sum_card_compatibleReverseSupportFamily_ge μ ρ d flag U h hlow ha hbudget
  have hsum : c * ENNReal.ofReal (3 / 32) * N ≤
      (∫⁻ z, g z ∂ν) + (∫⁻ z, s z ∂ν) + (∫⁻ z, b z ∂ν) := by
    refine hraw.trans ((lintegral_mono hpoint).trans_eq ?_)
    calc
      _ = (∫⁻ z, (g + s) z ∂ν) + (∫⁻ z, b z ∂ν) := lintegral_add_left (hg.add hs) _
      _ = _ := by
        change (∫⁻ z, g z + s z ∂ν) + _ = _
        rw [lintegral_add_left hg]
  have hshort' : (∫⁻ z, s z ∂ν) ≤ c * ENNReal.ofReal (3 / 128) * N := by
    have hS := lintegral_sum_shortCycleRejectedCandidates_le μ ρ d flag U K L hL h hu
    rw [mul_assoc c] at hS
    exact hS.trans (mul_le_mul_left (mul_le_mul_right hshort c) N)
  have hinc' : (∫⁻ z, b z ∂ν) ≤ c * ENNReal.ofReal (3 / 128) * N := by
    have hB := lintegral_sum_incrementRejectedReverseSupportFamily_le μ ρ d flag U I hn h hu
    exact hB.trans ((mul_le_mul_right hinc c).trans_eq (mul_assoc ..).symm)
  have : IsFiniteMeasure ν := by unfold ν forwardMaskRevealLaw; infer_instance
  exact lower_after_two_filter_losses (measure_ne_top ν univ) (ENNReal.natCast_ne_top _) hsum
    hshort' hinc'

/-- A bounded cumulative perturbation makes the short-cycle loss small
once the logarithmic cap scale is large enough. -/
theorem shortCycleLoss_budget_of_log (K L : ℕ) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hKδ : (K : ℝ) * δ ≤ B)
    (hL : (512 / 3 : ℝ) * Real.exp B ≤ Real.log (L : ℝ)) :
    ENNReal.ofReal (1 + δ) ^ K * ENNReal.ofReal (4 / Real.log (L : ℝ)) ≤
      ENNReal.ofReal (3 / 128) := by
  have hbase : 0 ≤ 1 + δ := by linarith
  have hlog : 0 < Real.log (L : ℝ) := (by positivity : 0 < (512 / 3 : ℝ) * Real.exp B).trans_le hL
  have hp : (1 + δ) ^ K ≤ Real.exp B := by
    calc
      _ ≤ (Real.exp δ) ^ K := pow_le_pow_left₀ hbase
        (by linarith only [Real.add_one_le_exp δ]) _
      _ = Real.exp ((K : ℝ) * δ) := (Real.exp_nat_mul δ K).symm
      _ ≤ _ := Real.exp_le_exp.mpr hKδ
  rw [← ENNReal.ofReal_pow hbase, ← ENNReal.ofReal_mul (pow_nonneg hbase _)]
  apply ENNReal.ofReal_le_ofReal
  refine (mul_le_mul_of_nonneg_right hp (by positivity)).trans ?_
  rw [← mul_div_assoc, div_le_iff₀ hlog]
  linarith only [hL]

/-- A finite numerical sufficient condition for the increment budget. -/
theorem reverseIncrementLoss_budget_of {n K : ℕ} (C : ℝ) (hn : 0 < n) (hK : 2 ≤ K)
    (hlarge : (128 / 3 : ℝ) * Real.sqrt (reverseFilterSecondMomentConstant C) ≤ (n : ℝ) ^ 2) :
    ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) ≤
      ENNReal.ofReal (3 / 128) * ((K - 1 : ℕ) : ℝ≥0∞) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ ENNReal.ofReal (3 / 128) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ 2)]
      linarith only [hlarge]
    _ = ENNReal.ofReal (3 / 128) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_right (by exact_mod_cast (show 1 ≤ K - 1 by omega)) _

/-- Both filter budgets hold eventually whenever the short-cycle scale
tends to infinity and the accumulated upper-arc error stays bounded. -/
theorem eventually_reverseFilterLossBudgets (K L : ℕ → ℕ) (δ : ℕ → ℝ) (C B : ℝ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n) (hL : Tendsto L atTop atTop)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n ∧ (K n : ℝ) * δ n ≤ B) :
    ∀ᶠ n in atTop, 2 ≤ L n ∧
      ENNReal.ofReal (1 + δ n) ^ K n * ENNReal.ofReal (4 / Real.log (L n : ℝ)) ≤
        ENNReal.ofReal (3 / 128) ∧
      ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) ≤
        ENNReal.ofReal (3 / 128) * ((K n - 1 : ℕ) : ℝ≥0∞) := by
  have hlog : Tendsto (fun n ↦ Real.log (L n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hL)
  filter_upwards [hK, hL.eventually_ge_atTop 2, hδ, hlog.eventually_ge_atTop
      ((512 / 3 : ℝ) * Real.exp B), eventually_ge_atTop (1 : ℕ),
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
        ((128 / 3 : ℝ) * Real.sqrt (reverseFilterSecondMomentConstant C))]
    with n hKn hLn hδn hlogn hn hlarge
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  exact ⟨hLn, shortCycleLoss_budget_of_log (K n) (L n) hδn.1 hδn.2 hlogn,
    reverseIncrementLoss_budget_of C (Nat.zero_lt_of_lt hn) hKn (hlarge.trans hsq)⟩

/-- At a singleton anchor, the surviving families still count distinct
actual pivot decorations. The two tests only remove members. -/
theorem sum_card_filteredReverseSupportFamily_le_card_pivotDecoration {n : ℕ}
    {x : ScoreProfile n} {μ₀ : Matching n} (hopt : IsManOptimal (profileOfScores x) μ₀)
    (r : Rotation (profileOfScores x) μ₀) (flag : OffDiagonalCellIndex n → Bool)
    (K L : ℕ) (t : ℝ) :
    let μ := (singletonRotationAnchor hopt r).val
    (∑ k ∈ Finset.Icc 2 K,
      (filteredReverseSupportFamily μ r.val.cycle flag k L t x).card) ≤
      Nat.card (PivotDecoration hopt K r) := by
  classical
  intro μ
  refine (Finset.sum_le_sum fun _ _ ↦ Finset.card_filter_le _ _).trans
    (sum_card_compatibleReverseSupportFamily_le_card_pivotDecoration hopt r flag K)

end LennonPittelFormalization

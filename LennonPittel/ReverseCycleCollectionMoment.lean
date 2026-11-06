module

public import LennonPittel.CoexposureCycleMoment
public import LennonPittel.PivotReverseScoreSuccessor
public import LennonPittel.ReverseColoredPermutations
public import LennonPittel.ReverseQuadraticGaussian
public import LennonPittel.ReverseRotationIdeals

/-!
# Upper moment for reverse cycle collections

Each selected cycle has three colors in a pair of subsets. Bounds on joint
arrows thus reduce the fourth exponential moment to a quadratic-weighted
support sum. Applying the same result to the swapped profile handles reverse
cycles, with an explicit interface for the column tests.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Sorting three-colored permutations by their supports produces the
quadratic coefficient that is absorbed by the Gaussian cutoff. -/
theorem sum_three_colored_successorPermutation_product_le {n : ℕ}
    (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞) :
    (∑ σ : Matching n, (3 : ℝ≥0∞) ^ σ.cycleFactorsFinset.card *
      ∏ i ∈ σ.support, a * w (σ i)) ≤
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (s.card.factorial : ℝ≥0∞) * ((s.card : ℝ≥0∞) + 1) ^ 2 * a ^ s.card *
          ∏ i ∈ s, w i := by
  classical
  rw [sum_weighted_successorPermutation_product_by_support]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  have hs :
      (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support = s),
        (3 : ℝ≥0∞) ^ σ.cycleFactorsFinset.card) ≤
        (s.card.factorial : ℝ≥0∞) * ((s.card : ℝ≥0∞) + 1) ^ 2 := by
    exact_mod_cast sum_three_pow_cycleFactorsFinset_support_le s
  simpa only [mul_assoc] using
    (mul_le_mul_left hs (a ^ s.card * ∏ i ∈ s, w i))

/-- The joint arc bound gives an upper moment of order `n * √n` times
the common mass factor. -/
theorem lintegral_four_pow_numExposedRotations_le_mul {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (c : ℝ≥0∞)
    (hn : 0 < n) {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    {δ C : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ))
    (harc : ∀ σ : Matching n, ν {x | RealizesSuccessorPermutation (P x) M σ} ≤ c *
      ∏ i ∈ σ.support, ENNReal.ofReal (1 + δ) * ENNReal.ofReal (w (σ i))) :
    (∫⁻ x, (4 : ℝ≥0∞) ^ numExposedRotations (P x) M ∂ν) ≤
      c * ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) *
        (n : ℝ) * Real.sqrt n) := by
  have h := lintegral_cycleWeight_numExposedRotations_le ν P hP M 3 _ harc
  rw [show (3 : ℝ≥0∞) + 1 = 4 by norm_num] at h
  refine h.trans ?_
  simp_rw [← mul_assoc, mul_comm _ c, mul_assoc c]
  rw [← Finset.mul_sum]
  exact mul_le_mul_right ((sum_three_colored_successorPermutation_product_le _ _).trans
    (reverse_weighted_powerset_sum_le_n_mul_sqrt_ennreal hn hw₀ hw hδ₀ hδ)) c

/-- A joint arc bound with perturbation of order `1 / √n` bounds the second
moment of the number of cycle subsets by a constant times `n * √n`. -/
theorem lintegral_four_pow_numExposedRotations_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (hn : 0 < n) {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    {δ C : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ))
    (harc : ∀ σ : Matching n, ν {x | RealizesSuccessorPermutation (P x) M σ} ≤
      ∏ i ∈ σ.support, ENNReal.ofReal (1 + δ) * ENNReal.ofReal (w (σ i))) :
    (∫⁻ x, (4 : ℝ≥0∞) ^ numExposedRotations (P x) M ∂ν) ≤
      ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) *
        (n : ℝ) * Real.sqrt n) := by
  simpa only [one_mul] using lintegral_four_pow_numExposedRotations_le_mul
    ν P hP M 1 hn hw₀ hw hδ₀ hδ (by simpa only [one_mul])

/-- On a product of probability columns, marginal reverse arc bounds suffice.
The proposer index in the swapped profile is the original woman's index. -/
theorem lintegral_four_pow_numReverseExposedRotations_le_of_pi {n : ℕ}
    {β : Fin n → Type*} [∀ i, MeasurableSpace (β i)]
    (ν : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (ν i)]
    (P : (∀ i, β i) → Profile n) (hP : Measurable P) (M : Matching n)
    (T : (i : Fin n) → Fin n → Set (β i)) (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    {δ C : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ))
    (hvalid : ∀ᵐ x ∂Measure.pi ν, ∀ i j,
      IsSuccessor (swapProfile (P x)) M.symm i (M.symm j) → x i ∈ T i j)
    (hmarg : ∀ i j, i ≠ j → ν i (T i j) ≤ ENNReal.ofReal (1 + δ) * ENNReal.ofReal (w j)) :
    (∫⁻ x, (4 : ℝ≥0∞) ^ numExposedRotations (swapProfile (P x)) M.symm ∂(Measure.pi ν)) ≤
      ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) *
        (n : ℝ) * Real.sqrt n) := by
  have hswap : Measurable (fun x ↦ swapProfile (P x)) :=
    (show Measurable (swapProfile (n := n)) from fun _ _ ↦ MeasurableSet.of_discrete).comp hP
  refine lintegral_four_pow_numExposedRotations_le _ _ hswap _ hn hw₀ hw hδ₀ hδ fun σ ↦ ?_
  simpa only [measure_univ, one_mul, Finset.prod_const_one] using
    measure_realizesSuccessorPermutation_le_of_pi ν (fun x ↦ swapProfile (P x)) M.symm σ T
      (fun _ j ↦ ENNReal.ofReal (1 + δ) * ENNReal.ofReal (w j)) hvalid
      (fun i j hij ↦ by simpa only [measure_univ, one_mul] using hmarg i j hij)

/-- Any filtered count of subsets is bounded in second moment by the
fourth exponential moment of the cycle count. -/
theorem lintegral_sq_cycleSubsetCount_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (Z C : Ω → ℕ) (hZ : ∀ x, Z x ≤ 2 ^ C x) :
    (∫⁻ x, (Z x : ℝ≥0∞) ^ 2 ∂ν) ≤ ∫⁻ x, (4 : ℝ≥0∞) ^ C x ∂ν := by
  refine lintegral_mono fun x ↦ ?_
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ C x) ^ 2 := pow_le_pow_left' (by exact_mod_cast hZ x) _
    _ = _ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

end LennonPittelFormalization

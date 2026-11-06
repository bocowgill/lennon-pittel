module

public import LennonPittel.PivotComparableCentered

/-!
# Reduction of the centered second moment

Equal anchors contribute only one pivot, since eligibility tests sole
exposure. For different anchors the two ordered comparable cases are
disjoint. Incomparable terms are bounded by their nonnegative count-count
and mean-mean products.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The two orders on stable matchings are both absent. -/
def IncomparableAnchors (p : Profile n) (μ ν : Matching n) : Prop :=
  ¬ MenWeaklyPrefer p μ ν ∧ ¬ MenWeaklyPrefer p ν μ

theorem measurableSet_incomparableAnchors (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IncomparableAnchors (profileOfScores x) μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | IncomparableAnchors p μ ν})

private theorem menWeaklyPrefer_antisymm {p : Profile n} {μ ν : Matching n}
    (h : MenWeaklyPrefer p μ ν) (h' : MenWeaklyPrefer p ν μ) : μ = ν :=
  Equiv.ext fun m ↦ (p.manRank m).injective (le_antisymm (h m) (h' m))

namespace PivotCountParameters

noncomputable def incomparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    ScoreProfile n → ℝ :=
  {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.centered i * q.centered j)

/-- The mixed products can be dropped when upper-bounding an incomparable pair. -/
noncomputable def incomparableUpperTerm (q : PivotCountParameters) (i j : PivotMark n) :
    ScoreProfile n → ℝ :=
  {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
    (q.count i * q.count j + q.mean i * q.mean j)

noncomputable def comparableCenteredMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableCenteredTerm i j x

noncomputable def comparableResidualMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableResidualTerm i j x

noncomputable def incomparableCenteredMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.incomparableCenteredTerm i j x

noncomputable def incomparableUpperMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n, q.incomparableUpperTerm i j x

private theorem centered_eq_zero_of_not_stable (q : PivotCountParameters) (i : PivotMark n)
    {x : ScoreProfile n} (h : ¬ IsScoreStable x i.1) : q.centered i x = 0 :=
  indicator_of_notMem (show x ∉ {x | IsScoreStable x i.1} from h) _

private theorem centered_zero_on_ineligible_ae (q : PivotCountParameters) (i : PivotMark n) :
    ∀ᵐ x ∂continuousScoreLaw n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.centered i x = 0 := by
  filter_upwards [ae_scoreLaw_on_stableMark i (q.localMean_zero_on_ineligible_ae i)]
    with x hx hE
  by_cases h : x ∈ {x | IsScoreStable x i.1}
  · rw [centered, onStableMark, indicator_of_mem h, localCentered, Pi.sub_apply, hx h hE]
    exact sub_eq_zero.mpr (localFilteredDecorationCount_of_not_eligible _ _ hE)
  · exact q.centered_eq_zero_of_not_stable i h

private theorem centered_product_eq_zero_of_same_anchor (q : PivotCountParameters)
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row)) (i j : PivotMark n)
    (h : i.1 = j.1) (hne : i ≠ j)
    (hz : ∀ k : PivotMark n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x k.1 k.2 →
        q.centered k x = 0) :
    q.centered i x * q.centered j x = 0 := by
  by_cases hi : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2
  · by_cases hj : IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2
    · have hei := hi.isSoleForwardExposed ht
      have hej := hj.isSoleForwardExposed ht
      have he : j.2 = i.2 := hei.2 j.2 (h ▸ hej.1)
      exact (hne (Prod.ext h he.symm)).elim
    · rw [hz j hj, mul_zero]
  · rw [hz i hi, zero_mul]

private theorem centered_product_split (q : PivotCountParameters)
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row)) (i j : PivotMark n)
    (hz : ∀ k : PivotMark n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x k.1 k.2 →
        q.centered k x = 0) :
    q.centered i x * q.centered j x =
      (if i = j then (q.centered i x) ^ 2 else 0) +
        q.comparableCenteredTerm i j x + q.comparableCenteredTerm j i x +
        q.incomparableCenteredTerm i j x := by
  classical
  by_cases he : i = j
  · subst j
    have hle : MenWeaklyPrefer (profileOfScores x) i.1 i.1 := fun _ ↦ le_rfl
    simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
      IncomparableAnchors, hle, pow_two]
  · by_cases hi : IsScoreStable x i.1
    · by_cases hj : IsScoreStable x j.1
      · by_cases hsame : i.1 = j.1
        · have hle : MenWeaklyPrefer (profileOfScores x) j.1 j.1 := fun _ ↦ le_rfl
          simp [q.centered_product_eq_zero_of_same_anchor ht i j hsame he hz,
            comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
            IncomparableAnchors, he, hsame, hle]
        · by_cases hle : MenWeaklyPrefer (profileOfScores x) i.1 j.1
          · have hge : ¬ MenWeaklyPrefer (profileOfScores x) j.1 i.1 :=
              fun h ↦ hsame (menWeaklyPrefer_antisymm hle h)
            simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
              IncomparableAnchors, he, hi, hj, hsame, hle, hge]
          · by_cases hge : MenWeaklyPrefer (profileOfScores x) j.1 i.1
            · simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
                IncomparableAnchors, he, hi, hj, Ne.symm hsame, hle, hge, mul_comm]
            · simp [comparableCenteredTerm, IsStrictLaterStable, incomparableCenteredTerm,
                IncomparableAnchors, he, hi, hj, hle, hge]
      · simp [q.centered_eq_zero_of_not_stable j hj, comparableCenteredTerm,
          incomparableCenteredTerm, indicator_apply, he]
    · simp [q.centered_eq_zero_of_not_stable i hi, comparableCenteredTerm,
        incomparableCenteredTerm, indicator_apply, he]

private theorem totalCount_sub_totalMean_eq_sum_centered (q : PivotCountParameters) (x : ScoreProfile n) :
    totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
        q.supportCap q.shortCutoff x -
      totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
        q.supportCap q.shortCutoff x = ∑ i : PivotMark n, q.centered i x := by
  classical
  have he : totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
      q.supportCap q.shortCutoff x = ∑ i : PivotMark n, q.count i x := by
    rw [Fintype.sum_prod_type]
    unfold totalLocalFilteredDecorationCount
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ρ _
    simp [count, onStableMark, localCount, indicator_apply]
  rw [he, totalLocalPivotConditionalMean, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ (q.centered_eq_sub i x).symm

private theorem centered_secondMoment_integrand_ae (q : PivotCountParameters) :
    ∀ᵐ x ∂continuousScoreLaw n,
      (totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x -
        totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x) ^ 2 =
        (∑ i : PivotMark n, (q.centered i x) ^ 2) + 2 * q.comparableCenteredMass x +
          q.incomparableCenteredMass x := by
  classical
  have hz : ∀ᵐ x ∂continuousScoreLaw n, ∀ i : PivotMark n,
      ¬ IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.centered i x = 0 := ae_all_iff.2 q.centered_zero_on_ineligible_ae
  filter_upwards [ae_injective_rows n, hz] with x ht hz
  rw [q.totalCount_sub_totalMean_eq_sum_centered x, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, q.centered_product_split ht _ _ hz]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : PivotMark n, ∑ j : PivotMark n,
      if i = j then (q.centered i x) ^ 2 else 0) = ∑ i : PivotMark n, (q.centered i x) ^ 2 := by
    simp
  have hswap : (∑ i : PivotMark n, ∑ j : PivotMark n, q.comparableCenteredTerm j i x) =
      q.comparableCenteredMass x := Finset.sum_comm
  rw [hd, hswap]
  unfold comparableCenteredMass incomparableCenteredMass
  ring

private theorem integrable_centered_mul (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.centered i * q.centered j) (continuousScoreLaw n) :=
  integrable_mul_of_ae_abs_le_real (q.measurable_centered i) (q.measurable_centered j)
    (by positivity) (q.abs_centered_le_ae i) (q.abs_centered_le_ae j)

private theorem integrable_incomparableCenteredTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.incomparableCenteredTerm i j) (continuousScoreLaw n) :=
  (q.integrable_centered_mul i j).indicator (measurableSet_incomparableAnchors i.1 j.1)

private theorem integrable_incomparableUpperTerm (q : PivotCountParameters) (i j : PivotMark n) :
    Integrable (q.incomparableUpperTerm i j) (continuousScoreLaw n) := by
  have hc (k : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.count k x| ≤ (n.factorial : ℝ) :=
    Eventually.of_forall fun x ↦ (abs_of_nonneg (q.count_mem_Icc k x).1).symm ▸
      (q.count_mem_Icc k x).2
  have hm (k : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.mean k x| ≤ (n.factorial : ℝ) :=
    (q.mean_mem_Icc_ae k).mono fun x hx ↦ (abs_of_nonneg hx.1).symm ▸ hx.2
  exact ((integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_count j)
    (by positivity) (hc i) (hc j)).add
      (integrable_mul_of_ae_abs_le_real (q.measurable_mean i) (q.measurable_mean j)
        (by positivity) (hm i) (hm j))).indicator (measurableSet_incomparableAnchors i.1 j.1)

private theorem integral_incomparableCenteredMass_le (q : PivotCountParameters) :
    (∫ x, q.incomparableCenteredMass x ∂continuousScoreLaw n) ≤
      ∫ x, q.incomparableUpperMass x ∂continuousScoreLaw n := by
  apply integral_mono_ae
  · exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_incomparableCenteredTerm i j
  · exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_incomparableUpperTerm i j
  have hM := ae_all_iff.2 (q.mean_mem_Icc_ae (n := n))
  filter_upwards [hM] with x hx
  apply Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  classical
  by_cases h : x ∈ {x | IncomparableAnchors (profileOfScores x) i.1 j.1}
  · rw [incomparableCenteredTerm, incomparableUpperTerm, indicator_of_mem h, indicator_of_mem h]
    simp only [Pi.mul_apply, Pi.add_apply, q.centered_eq_sub]
    nlinarith [mul_nonneg (q.count_mem_Icc i x).1 (hx j).1,
      mul_nonneg (hx i).1 (q.count_mem_Icc j x).1]
  · rw [incomparableCenteredTerm, incomparableUpperTerm, indicator_of_notMem h, indicator_of_notMem h]

private theorem integral_comparableCenteredMass_le (q : PivotCountParameters) :
    (∫ x, q.comparableCenteredMass x ∂continuousScoreLaw n) ≤
      ∫ x, q.comparableResidualMass x ∂continuousScoreLaw n := by
  unfold comparableCenteredMass comparableResidualMass
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    q.integrable_comparableCenteredTerm i j),
    integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_comparableResidualTerm i j)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ q.integrable_comparableCenteredTerm i j),
    integral_finsetSum _ (fun j _ ↦ q.integrable_comparableResidualTerm i j)]
  exact Finset.sum_le_sum fun j _ ↦ q.integral_comparableCenteredTerm_le_residual i j

/-- The variance reduction with the actual comparable residual and two
nonnegative incomparable products. No estimate of the pair terms is used. -/
theorem integral_centered_sq_le_pair_terms (q : PivotCountParameters) :
    (∫ x, (totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x -
        totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
          q.supportCap q.shortCutoff x) ^ 2 ∂continuousScoreLaw n) ≤
      (∑ i : PivotMark n, ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1) +
        2 * (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) +
        ∫ x, q.incomparableUpperMass x ∂continuousScoreLaw n := by
  let ν := continuousScoreLaw n
  let D (x : ScoreProfile n) := ∑ i : PivotMark n, (q.centered i x) ^ 2
  have hD (i : PivotMark n) : Integrable (fun x ↦ (q.centered i x) ^ 2) ν := by
    simp only [pow_two]
    exact q.integrable_centered_mul i i
  have hd : Integrable D ν := integrable_finsetSum _ fun i _ ↦ hD i
  have hc : Integrable (q.comparableCenteredMass (n := n)) ν :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_comparableCenteredTerm i j
  have hi : Integrable (q.incomparableCenteredMass (n := n)) ν :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      q.integrable_incomparableCenteredTerm i j
  rw [integral_congr_ae q.centered_secondMoment_integrand_ae]
  have he : (∫ x, D x + 2 * q.comparableCenteredMass x + q.incomparableCenteredMass x ∂ν) =
      (∫ x, D x ∂ν) + 2 * (∫ x, q.comparableCenteredMass x ∂ν) +
        ∫ x, q.incomparableCenteredMass x ∂ν := by
    calc
      _ = (∫ x, D x + 2 * q.comparableCenteredMass x ∂ν) +
          ∫ x, q.incomparableCenteredMass x ∂ν := integral_add (hd.add (hc.const_mul 2)) hi
      _ = _ := by rw [integral_add hd (hc.const_mul 2), integral_const_mul]
  rw [he]
  refine add_le_add (add_le_add ?_ (mul_le_mul_of_nonneg_left
    q.integral_comparableCenteredMass_le (by norm_num))) q.integral_incomparableCenteredMass_le
  unfold D
  rw [integral_finsetSum _ (fun i _ ↦ hD i)]
  exact Finset.sum_le_sum fun i _ ↦ q.integral_sq_centered_le_localCount_sq i

end PivotCountParameters
end LennonPittelFormalization

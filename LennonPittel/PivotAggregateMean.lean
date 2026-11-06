module

public import LennonPittel.PivotConditionalMean
public import LennonPittel.PivotEligibleAbundance

/-!
# The aggregate conditional mean has the conjectured scale

The same long-pivot parameters both keep the counted stable endpoints
distinct and make the total conditional mean large. The lower estimate
is pointwise on the abundance event, apart from the almost-sure
versions of the conditional expectations.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

variable {n : ℕ}

/-- One summand of the aggregate mean, zero at a nonstable mark. -/
noncomputable def stablePivotMeanTerm (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) (i : Matching n × Matching n) : ℝ :=
  {y | IsScoreStable y i.1}.indicator (localPivotConditionalMean b A B K L i.1 i.2) x

/-- Sum the marked conditional means over possible labeled anchors and pivots. -/
noncomputable def totalLocalPivotConditionalMean (b A B : ℝ) (K L : ℕ)
    (x : ScoreProfile n) : ℝ :=
  ∑ i : Matching n × Matching n, stablePivotMeanTerm b A B K L x i

theorem measurable_totalLocalPivotConditionalMean (b A B : ℝ) (K L : ℕ) :
    Measurable (totalLocalPivotConditionalMean (n := n) b A B K L) := by
  unfold totalLocalPivotConditionalMean stablePivotMeanTerm
  exact Finset.measurable_sum _ fun i _ ↦
    ((stronglyMeasurable_condExp.mono (pivotMaleRevealSpace_le i.1)).measurable.indicator
      (measurableSet_isScoreStable i.1))

/-- At a point where all marked lower bounds hold, the abundant anchors
contribute once each to the aggregate mean. -/
theorem totalLocalPivotConditionalMean_ge_of_abundance {b A B : ℝ} {K L : ℕ}
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row))
    (h : ∀ μ ρ : Matching n, IsScoreStable x μ →
      localPivotMeanFloor b A B K μ ρ x ≤ localPivotConditionalMean b A B K L μ ρ x)
    (hE : x ∈ locallyEligiblePivotAbundance n b A B) :
    (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ) * (Real.sqrt n * Real.log n / (10 * A)) ≤
      totalLocalPivotConditionalMean b A B K L x := by
  classical
  obtain ⟨S, hS, hE⟩ := hE
  let p := profileOfScores x
  let hopt := DAState.isManOptimal_matching p
  let f (r : Rotation p (DAState.matching p)) : Matching n × Matching n :=
    ((singletonRotationAnchor hopt r).val, r.val.cycle)
  let c : ℝ := (3 / 64 : ℝ) * ((K - 1 : ℕ) : ℝ)
  let term := stablePivotMeanTerm b A B K L x
  have hf : Function.Injective f := by
    intro r s he
    exact singletonRotationAnchor_injective hopt (Subtype.ext (congrArg Prod.fst he))
  have hnonneg (i : Matching n × Matching n) : 0 ≤ term i := by
    by_cases hi : x ∈ {y | IsScoreStable y i.1}
    · unfold term stablePivotMeanTerm
      rw [indicator_of_mem hi]
      exact (localPivotMeanFloor_nonneg b A B K i.1 i.2 x).trans (h i.1 i.2 hi)
    · unfold term stablePivotMeanTerm
      rw [indicator_of_notMem hi]
  have hterm (r : Rotation p (DAState.matching p)) (hr : r ∈ S) : c ≤ term (f r) := by
    have hs := (isStable_profileOfScores_iff ht (f r).1).mp (singletonRotationAnchor hopt r).property
    have he : IsLocallyEligiblePivot b A B x (f r).1 (f r).2 := hE r hr
    have hh := h (f r).1 (f r).2 hs
    unfold localPivotMeanFloor at hh
    rw [indicator_of_mem (show x ∈ {y | IsLocallyEligiblePivot b A B y (f r).1 (f r).2}
      from he)] at hh
    unfold term stablePivotMeanTerm
    rw [indicator_of_mem (show x ∈ {y | IsScoreStable y (f r).1} from hs)]
    exact hh
  change c * _ ≤ ∑ i, term i
  calc
    _ ≤ c * (S.card : ℝ) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ∑ _r ∈ S, c := by simp only [Finset.sum_const, nsmul_eq_mul]; exact mul_comm _ _
    _ ≤ ∑ r ∈ S, term (f r) := Finset.sum_le_sum hterm
    _ = ∑ i ∈ S.image f, term i := (Finset.sum_image fun _ _ _ _ he ↦ hf he).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hnonneg i)

/-- The integer support cap used for the reverse decorations. -/
noncomputable def pivotDecorationSupportCap (κ : ℝ) (n : ℕ) : ℕ :=
  ⌊κ * Real.sqrt (n : ℝ)⌋₊

theorem eventually_pivotDecorationSupportCap_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ pivotDecorationSupportCap κ n ∧
      (pivotDecorationSupportCap κ n : ℝ) ≤ κ * Real.sqrt (n : ℝ) ∧
      κ * Real.sqrt (n : ℝ) / 2 ≤ ((pivotDecorationSupportCap κ n - 1 : ℕ) : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ κ * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop 4] with n hn
  let t := κ * Real.sqrt (n : ℝ)
  let K := pivotDecorationSupportCap κ n
  change 4 ≤ t at hn
  have hK : t < (K : ℝ) + 1 := Nat.lt_floor_add_one t
  have hK' : (K : ℝ) ≤ t := Nat.floor_le (by positivity)
  have h₂ : 2 ≤ K := by
    exact_mod_cast (show (2 : ℝ) ≤ K by linarith)
  refine ⟨h₂, hK', ?_⟩
  rw [Nat.cast_sub (by omega : 1 ≤ K)]
  push_cast
  linarith

/-- The actual count is dominated almost surely by the number of stable matchings. -/
theorem ae_totalLocalFilteredDecorationCount_le {b A B κ : ℝ} {K L : ℕ}
    (hn : 0 < n) (hκ : κ < b) (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    ∀ᵐ x ∂continuousScoreLaw n, totalLocalFilteredDecorationCount b A B K L x ≤
      (numStableMatchings (profileOfScores x) : ℝ) := by
  filter_upwards [ae_injective_rows n] with x ht
  exact totalLocalFilteredDecorationCount_le_numStableMatchings ht fun _ _ _ he ↦
    he.supportCap_lt hn hκ hK

/-- With arbitrarily small probability loss, the aggregate conditional mean
has order n log n, using the same count that is dominated by stable matchings.
The short-cycle cutoff is allowed to be any divergent sequence. -/
theorem exists_eventually_pivotAggregateMean_lower {η : ℝ} (hη : 0 < η) :
    ∃ b A B κ c : ℝ, 0 < c ∧ 0 < κ ∧ κ < b ∧ 0 < B ∧ 1 ≤ A ∧
      ∀ (L : ℕ → ℕ), Tendsto L atTop atTop → ∀ᶠ n : ℕ in atTop,
        (∀ᵐ x ∂continuousScoreLaw n,
          totalLocalFilteredDecorationCount b A B (pivotDecorationSupportCap κ n) (L n) x ≤
            (numStableMatchings (profileOfScores x) : ℝ)) ∧
        continuousScoreLaw n {x | c * ((n : ℝ) * Real.log n) >
          totalLocalPivotConditionalMean b A B (pivotDecorationSupportCap κ n) (L n) x} ≤
            ENNReal.ofReal η := by
  obtain ⟨b, A, B, κ, _, _, hA, hB, hκ, hκb, hlabel, hcompat, hab⟩ :=
    exists_eligiblePivotAbundance_and_supportCoefficient hη
  let K := pivotDecorationSupportCap κ
  let c := 3 * κ / (1280 * A)
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨b, A, B, κ, c, hc, hκ, hκb, hB, hA, fun L hL ↦ ?_⟩
  have hK := eventually_pivotDecorationSupportCap_bounds hκ
  have hmean := eventually_localPivotMeanFloor_le_conditionalMean_ae K L hB.le hκ.le
    (hK.mono fun _ h ↦ ⟨h.1, h.2.1⟩) hL hlabel hcompat
  filter_upwards [hK, hmean, hab, eventually_gt_atTop (0 : ℕ)] with n hnK hnMean hnAb hn
  refine ⟨ae_totalLocalFilteredDecorationCount_le hn hκb hnK.2.1, ?_⟩
  have hAll : ∀ᵐ x ∂continuousScoreLaw n, ∀ μ ρ : Matching n, IsScoreStable x μ →
      localPivotMeanFloor b A B (K n) μ ρ x ≤ localPivotConditionalMean b A B (K n) (L n) μ ρ x := by
    rw [ae_all_iff]
    intro μ
    rw [ae_all_iff]
    intro ρ
    exact (ae_restrict_iff' (measurableSet_isScoreStable μ)).mp (hnMean μ ρ b A)
  have hnum : c * ((n : ℝ) * Real.log n) ≤ (3 / 64 : ℝ) * ((K n - 1 : ℕ) : ℝ) *
      (Real.sqrt n * Real.log n / (10 * A)) := by
    have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    calc
      _ = (3 / 64 : ℝ) * (κ * Real.sqrt n / 2) * (Real.sqrt n * Real.log n / (10 * A)) := by
        calc
          _ = (3 / 64 : ℝ) * (κ / 2) * ((n : ℝ) * Real.log n / (10 * A)) := by
            dsimp [c]
            ring
          _ = (3 / 64 : ℝ) * (κ / 2) * ((Real.sqrt n) ^ 2 * Real.log n / (10 * A)) := by
            rw [Real.sq_sqrt hn']
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnK.2.2 (by norm_num)) (by positivity)
  refine (measure_mono_ae ?_).trans hnAb
  filter_upwards [ae_injective_rows n, hAll] with x ht hall hx
  exact fun h ↦ (not_lt_of_ge (hnum.trans
    (totalLocalPivotConditionalMean_ge_of_abundance ht hall h))) hx

end LennonPittelFormalization

module

public import LennonPittel.PivotCenteredReduction
public import LennonPittel.PivotIncomparableAnchors
public import LennonPittel.PivotLocalMomentUpper
public import LennonPittel.LennonPittelLowerTailCriterion

/-!
# The diagonal and incomparable mean contributions to the variance

Both contributions have order at most n² log n. The incomparable mean
bound uses the number of bare eligible marks, not the much larger count
of all incomparable stable matching pairs.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

namespace PivotCountParameters

variable {n : ℕ}

/-- The ordered incomparable product of the two actual conditional means. -/
noncomputable def incomparableMeanProductMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n,
    {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.mean i * q.mean j) x

/-- The ordered incomparable product of the two actual decoration counts. -/
noncomputable def incomparableCountProductMass (q : PivotCountParameters) (x : ScoreProfile n) : ℝ :=
  ∑ i : PivotMark n, ∑ j : PivotMark n,
    {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.count i * q.count j) x

theorem integrable_incomparableMeanProductMass (q : PivotCountParameters) :
    Integrable (q.incomparableMeanProductMass (n := n)) (continuousScoreLaw n) := by
  have h (i : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.mean i x| ≤ (n.factorial : ℝ) :=
    (q.mean_mem_Icc_ae i).mono fun x hx ↦ (abs_of_nonneg hx.1).symm ▸ hx.2
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_mul_of_ae_abs_le_real (q.measurable_mean i) (q.measurable_mean j)
      (by positivity) (h i) (h j)).indicator (measurableSet_incomparableAnchors i.1 j.1)

theorem integrable_incomparableCountProductMass (q : PivotCountParameters) :
    Integrable (q.incomparableCountProductMass (n := n)) (continuousScoreLaw n) := by
  have h (i : PivotMark n) : ∀ᵐ x ∂continuousScoreLaw n, |q.count i x| ≤ (n.factorial : ℝ) :=
    Eventually.of_forall fun x ↦ (abs_of_nonneg (q.count_mem_Icc i x).1).symm ▸
      (q.count_mem_Icc i x).2
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_count j)
      (by positivity) (h i) (h j)).indicator (measurableSet_incomparableAnchors i.1 j.1)

theorem integral_incomparableUpperMass_eq (q : PivotCountParameters) :
    (∫ x, q.incomparableUpperMass x ∂continuousScoreLaw n) =
      (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) +
        ∫ x, q.incomparableMeanProductMass x ∂continuousScoreLaw n := by
  have h (x : ScoreProfile n) : q.incomparableUpperMass x =
      q.incomparableCountProductMass x + q.incomparableMeanProductMass x := by
    have hterm (i j : PivotMark n) :
        q.incomparableUpperTerm i j x =
          {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.count i * q.count j) x +
          {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator (q.mean i * q.mean j) x := by
      classical
      by_cases hmem : x ∈ {y | IncomparableAnchors (profileOfScores y) i.1 j.1}
      · simp only [incomparableUpperTerm, indicator_of_mem hmem, Pi.add_apply]
      · simp only [incomparableUpperTerm, indicator_of_notMem hmem, add_zero]
    simp only [incomparableUpperMass, incomparableCountProductMass,
      incomparableMeanProductMass, hterm, Finset.sum_add_distrib]
  simp_rw [h]
  exact integral_add q.integrable_incomparableCountProductMass q.integrable_incomparableMeanProductMass

theorem integral_incomparableMeanProductMass_nonneg (q : PivotCountParameters) :
    0 ≤ ∫ x, q.incomparableMeanProductMass x ∂continuousScoreLaw n := by
  apply integral_nonneg_of_ae
  have h := ae_all_iff.2 (q.mean_mem_Icc_ae (n := n))
  filter_upwards [h] with x hx
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    Set.indicator_nonneg (fun _ _ ↦ mul_nonneg (hx i).1 (hx j).1) _

private theorem mean_le_eligibleCeiling_ae (q : PivotCountParameters) (i : PivotMark n)
    {c : ℝ}
    (h : q.localMean i ≤ᵐ[stableMarkScoreLaw i.1]
      localPivotMomentCeiling q.lowerLength q.upperLength q.geometryBudget c i.1 i.2) :
    ∀ᵐ x ∂continuousScoreLaw n,
      q.mean i x ≤ {y | IsScoreStable y i.1 ∧
        IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget y i.1 i.2}.indicator
        (fun _ ↦ c) x := by
  filter_upwards [ae_scoreLaw_on_stableMark i h] with x hx
  by_cases hs : IsScoreStable x i.1
  · have he : {y | IsScoreStable y i.1 ∧
          IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget y i.1 i.2}.indicator
          (fun _ ↦ c) x = localPivotMomentCeiling q.lowerLength q.upperLength
            q.geometryBudget c i.1 i.2 x := by
      classical
      simp only [localPivotMomentCeiling, indicator_apply, mem_ofPred_eq, hs, true_and]
    rw [he, mean, onStableMark, indicator_of_mem (show x ∈ {y | IsScoreStable y i.1} from hs)]
    exact hx hs
  · simp [mean, onStableMark, hs]

private theorem incomparableMeanProductMass_le_ae (q : PivotCountParameters)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : PivotMark n, q.localMean i ≤ᵐ[stableMarkScoreLaw i.1]
      localPivotMomentCeiling q.lowerLength q.upperLength q.geometryBudget c i.1 i.2) :
    ∀ᵐ x ∂continuousScoreLaw n, q.incomparableMeanProductMass x ≤
      c ^ 2 * (Nat.card (IncomparableEligibleAnchorMarks
        q.lowerLength q.upperLength q.geometryBudget x) : ℝ) := by
  classical
  have hμ := ae_all_iff.2 (q.mean_mem_Icc_ae (n := n))
  have hcμ := ae_all_iff.2 (fun i : PivotMark n ↦ q.mean_le_eligibleCeiling_ae i (h i))
  filter_upwards [hμ, hcμ] with x hμ hx
  rw [natCard_incomparableEligibleAnchorMarks_eq_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
  let E (k : PivotMark n) := IsScoreStable x k.1 ∧
    IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x k.1 k.2
  by_cases hinc : IncomparableAnchors (profileOfScores x) i.1 j.1
  · have hmem : x ∈ incomparableEligibleAnchorMarksEvent
        q.lowerLength q.upperLength q.geometryBudget i j ↔ E i ∧ E j := by
      change (IsScoreStable x i.1 ∧ IsScoreStable x j.1 ∧
        IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 ∧
        IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x j.1 j.2 ∧
        IncomparableAnchors (profileOfScores x) i.1 j.1) ↔ _
      simp [E, hinc, and_assoc, and_left_comm]
    have hprod : q.mean i x * q.mean j x ≤
        (if E i then c else 0) * (if E j then c else 0) := by
      have hk (k : PivotMark n) : q.mean k x ≤ if E k then c else 0 := by
        simpa only [indicator_apply, E, mem_ofPred_eq] using hx k
      exact mul_le_mul (hk i) (hk j) (hμ j).1 (by split <;> positivity)
    change {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
      (q.mean i * q.mean j) x ≤ _
    rw [indicator_of_mem (show x ∈ {y | IncomparableAnchors (profileOfScores y) i.1 j.1}
      from hinc), Pi.mul_apply, indicator_apply, hmem]
    by_cases hi : E i <;> by_cases hj : E j <;> simpa [hi, hj, pow_two] using hprod
  · have he : x ∉ incomparableEligibleAnchorMarksEvent
        q.lowerLength q.upperLength q.geometryBudget i j :=
      fun hm ↦ hinc hm.2.2.2.2
    simp [hinc, he]

private theorem integrable_bareIncomparableAnchorCount (b A B : ℝ) :
    Integrable (fun x : ScoreProfile n ↦
      (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ)) (continuousScoreLaw n) := by
  simp_rw [natCard_incomparableEligibleAnchorMarks_eq_sum]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrable_const _).indicator (measurableSet_incomparableEligibleAnchorMarksEvent b A B i j)

/-- The actual incomparable mean–mean product is bounded by the squared
local ceiling times the expected bare number of eligible marks. -/
theorem integral_incomparableMeanProductMass_le (q : PivotCountParameters) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i : PivotMark n, q.localMean i ≤ᵐ[stableMarkScoreLaw i.1]
      localPivotMomentCeiling q.lowerLength q.upperLength q.geometryBudget c i.1 i.2) :
    (∫ x, q.incomparableMeanProductMass x ∂continuousScoreLaw n) ≤
      c ^ 2 * ∫ x, (Nat.card (IncomparableEligibleAnchorMarks
        q.lowerLength q.upperLength q.geometryBudget x) : ℝ) ∂continuousScoreLaw n := by
  rw [← integral_const_mul]
  exact integral_mono_ae q.integrable_incomparableMeanProductMass
    ((integrable_bareIncomparableAnchorCount _ _ _).const_mul _)
    (q.incomparableMeanProductMass_le_ae hc h)

end PivotCountParameters

private theorem eventually_log_natCast_atLeast (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, a ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop a

private theorem eventually_pivotMomentEnvelope_le {C D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ n : ℕ in atTop, D * (n : ℝ) * Real.sqrt n *
      (C * Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)) ≤
      (D * (C + 1)) * ((n : ℝ) ^ 2 * Real.log n) := by
  filter_upwards [eventually_log_natCast_atLeast 1, eventually_ge_atTop (1 : ℕ)] with n hlog hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hremainder : (n : ℝ) ^ (-3 : ℝ) ≤ Real.sqrt n * Real.log n :=
    (Real.rpow_le_one_of_one_le_of_nonpos hn' (by norm_num)).trans
      (one_le_mul_of_one_le_of_one_le hs hlog)
  calc
    _ ≤ D * (n : ℝ) * Real.sqrt n * (C * Real.sqrt n * Real.log n + Real.sqrt n * Real.log n) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hremainder _) (by positivity)
    _ = _ := by
      rw [show C * Real.sqrt n * Real.log n + Real.sqrt n * Real.log n =
        (C + 1) * Real.sqrt n * Real.log n by ring]
      calc
        _ = D * (C + 1) * ((n : ℝ) * (Real.sqrt n) ^ 2 * Real.log n) := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]; ring

private theorem isLittleO_of_eventually_nonneg_le_pivotMomentEnvelope {f : ℕ → ℝ} {D : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧
      f n ≤ D * ((n : ℝ) ^ 2 * Real.log n)) :
    f =o[atTop] (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2) := by
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [h, eventually_log_natCast_atLeast (D / c)] with n hf hn
  have hlog := Real.log_natCast_nonneg n
  have hDc : D ≤ c * Real.log n := by
    have := (div_le_iff₀ hc).mp hn
    rwa [mul_comm] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf.1, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ D * ((n : ℝ) ^ 2 * Real.log n) := hf.2
    _ ≤ (c * Real.log n) * ((n : ℝ) ^ 2 * Real.log n) :=
      mul_le_mul_of_nonneg_right hDc (by positivity)
    _ = _ := by ring

variable {n : ℕ}

/-- The actual diagonal contribution to the variance reduction. -/
noncomputable def pivotRawDiagonalMass (q : PivotCountParameters) (n : ℕ) : ℝ :=
  ∑ i : PivotMark n, ∫ x, (q.localCount i x) ^ 2 ∂stableMarkScoreLaw i.1

/-- The diagonal term, normalized by the square of the target scale, vanishes. -/
theorem isLittleO_pivotRawDiagonalMass (b A B κ : ℝ) (K L : ℕ → ℕ)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    (fun n : ℕ ↦ pivotRawDiagonalMass ⟨b, A, B, K n, L n⟩ n) =o[atTop]
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2) := by
  let D := reverseFilterSecondMomentConstant 2
  let C := Real.exp 5 * (108 + 48 * Real.exp 4)
  have hD : 0 ≤ D := by unfold D reverseFilterSecondMomentConstant; positivity
  refine isLittleO_of_eventually_nonneg_le_pivotMomentEnvelope
    (D := D * (C + 1)) ?_
  filter_upwards [eventually_sum_integral_sq_localFilteredDecorationCount_le K L
    hB hκ hK hL hsmallLabel hsmallCompat, eventually_pivotMomentEnvelope_le (C := C) hD]
    with n h₁ h₂
  unfold pivotRawDiagonalMass
  refine ⟨Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ sq_nonneg _, ?_⟩
  rw [Fintype.sum_prod_type]
  exact (h₁ b A).trans h₂

private theorem integral_bareIncomparableAnchorCount_le {b A B : ℝ} {m : ℝ} (hm : 0 ≤ m)
    (h : (∫⁻ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞)
        ∂continuousScoreLaw n) ≤ 2 * ENNReal.ofReal m) :
    (∫ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ) ∂continuousScoreLaw n) ≤
      2 * m := by
  have hI := PivotCountParameters.integrable_bareIncomparableAnchorCount (n := n) b A B
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦ Nat.cast_nonneg (Nat.card (IncomparableEligibleAnchorMarks b A B x)))
    hI.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]
  have hfin : (2 : ℝ≥0∞) * ENNReal.ofReal m ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm, ENNReal.toReal_ofNat] at hh

/-- The actual incomparable mean–mean contribution, normalized by the
square of the target scale, vanishes. -/
theorem isLittleO_incomparableMeanProductMass (b A B κ : ℝ) (K L : ℕ → ℕ)
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    (fun n : ℕ ↦ ∫ x, (PivotCountParameters.mk b A B (K n) (L n)).incomparableMeanProductMass x
      ∂continuousScoreLaw n) =o[atTop] (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2) := by
  let C := twoForwardWindowConstant b A
  let a := Real.exp (2 * κ) * (κ + 1)
  let D := 2 * a ^ 2
  have hC : 0 ≤ C := by unfold C twoForwardWindowConstant; positivity
  have ha : 0 ≤ a := by unfold a; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  refine isLittleO_of_eventually_nonneg_le_pivotMomentEnvelope
    (D := D * (C + 1)) ?_
  filter_upwards [eventually_localPivotConditionalMean_le_ceiling_ae K L hB hκ hK hL
    hsmallLabel hsmallCompat, eventually_lintegral_card_incomparableEligibleAnchorMarks_le hb hA,
    eventually_pivotMomentEnvelope_le (C := C) hD, hK, eventually_ge_atTop (1 : ℕ)]
    with n hmean hbare henvelope hcap hn
  let q := PivotCountParameters.mk b A B (K n) (L n)
  let c := Real.exp (2 * κ) * (↑(K n + 1) : ℝ)
  let m := C * Real.sqrt n * Real.log n + (n : ℝ) ^ (-3 : ℝ)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn'
  have hc : 0 ≤ c := by unfold c; positivity
  have hm : 0 ≤ m := by unfold m; positivity
  have hc' : c ≤ a * Real.sqrt n := by
    unfold c a
    rw [mul_assoc, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add hcap.2 hs) (by positivity)
  have hsq : c ^ 2 ≤ a ^ 2 * (n : ℝ) * Real.sqrt n := by
    calc
      c ^ 2 ≤ (a * Real.sqrt n) ^ 2 := pow_le_pow_left₀ hc hc' _
      _ = a ^ 2 * (n : ℝ) := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hs
  refine ⟨q.integral_incomparableMeanProductMass_nonneg, ?_⟩
  calc
    _ ≤ c ^ 2 * ∫ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ)
        ∂continuousScoreLaw n :=
      q.integral_incomparableMeanProductMass_le hc fun i ↦ hmean i.1 i.2 b A
    _ ≤ c ^ 2 * (2 * m) :=
      mul_le_mul_of_nonneg_left (integral_bareIncomparableAnchorCount_le hm (hbare B)) (sq_nonneg _)
    _ ≤ (a ^ 2 * (n : ℝ) * Real.sqrt n) * (2 * m) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = D * (n : ℝ) * Real.sqrt n * m := by unfold D; ring
    _ ≤ _ := henvelope

/-- An almost-sure domination by the stable count suffices. Clipping on the
exceptional null set does not change the centered moment. -/
theorem lennonPittel_of_score_centered_counts_ae
    (hcert : ∀ η : ℝ, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ e : ℝ, 0 < e →
      ∃ T M : ∀ n : ℕ, ScoreProfile n → ℝ,
        (∀ n, Measurable (T n)) ∧ (∀ n, Measurable (M n)) ∧
        ∀ᶠ n : ℕ in atTop,
          (∀ᵐ x ∂continuousScoreLaw n, T n x ≤ (numStableMatchings (profileOfScores x) : ℝ)) ∧
          ENNReal.ofReal (1 - η) ≤ (continuousScoreLaw n)
            {x | d * ((n : ℝ) * Real.log n) ≤ M n x} ∧
          scaledCenteredCountMoment (continuousScoreLaw n)
            ((n : ℝ) * Real.log n) (T n) (M n) ≤ ENNReal.ofReal e)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  apply lennonPittel_of_score_centered_counts _ ε hε
  intro η hη
  obtain ⟨d, hd, hd'⟩ := hcert η hη
  refine ⟨d, hd, fun e he ↦ ?_⟩
  obtain ⟨T, M, hT, hM, hgood⟩ := hd' e he
  let S (n : ℕ) (x : ScoreProfile n) := (numStableMatchings (profileOfScores x) : ℝ)
  let T' (n : ℕ) (x : ScoreProfile n) := min (T n x) (S n x)
  have hS (n : ℕ) : Measurable (S n) :=
    (show Measurable (fun p : Profile n ↦ (numStableMatchings p : ℝ)) from
      Measurable.of_discrete).comp (measurable_profileOfScores n)
  refine ⟨T', M, fun n ↦ (hT n).min (hS n), hM, fun n x ↦ min_le_right _ _, ?_⟩
  filter_upwards [hgood] with n hn
  refine ⟨hn.2.1, ?_⟩
  have ha : T' n =ᵐ[continuousScoreLaw n] T n :=
    hn.1.mono fun x hx ↦ min_eq_left hx
  unfold scaledCenteredCountMoment
  rw [lintegral_congr_ae (ha.mono fun x hx ↦ by rw [hx])]
  exact hn.2.2

namespace PivotCountParameters

/-- The aggregate decoration count for a common choice of filter parameters. -/
noncomputable def aggregateCount (q : PivotCountParameters) (n : ℕ) : ScoreProfile n → ℝ :=
  totalLocalFilteredDecorationCount q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff

/-- The aggregate of the actual smaller-reveal conditional means. -/
noncomputable def aggregateMean (q : PivotCountParameters) (n : ℕ) : ScoreProfile n → ℝ :=
  totalLocalPivotConditionalMean q.lowerLength q.upperLength q.geometryBudget
    q.supportCap q.shortCutoff

private theorem aggregateCount_sub_mean_eq_sum (q : PivotCountParameters) (x : ScoreProfile n) :
    q.aggregateCount n x - q.aggregateMean n x = ∑ i : PivotMark n, q.centered i x := by
  classical
  have hcount : q.aggregateCount n x = ∑ i : PivotMark n, q.count i x := by
    rw [Fintype.sum_prod_type]
    unfold aggregateCount totalLocalFilteredDecorationCount
    refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ρ _ ↦ ?_
    simp [count, onStableMark, localCount, indicator_apply]
  rw [hcount, aggregateMean, totalLocalPivotConditionalMean, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ (q.centered_eq_sub i x).symm

private theorem integrable_sq_aggregateCount_sub_mean (q : PivotCountParameters) :
    Integrable (fun x ↦ (q.aggregateCount n x - q.aggregateMean n x) ^ 2)
      (continuousScoreLaw n) := by
  simp_rw [aggregateCount_sub_mean_eq_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_mul_of_ae_abs_le_real (q.measurable_centered i) (q.measurable_centered j)
      (by positivity) (q.abs_centered_le_ae i) (q.abs_centered_le_ae j)

private theorem scaledCenteredCountMoment_aggregate_eq (q : PivotCountParameters) (a : ℝ) :
    scaledCenteredCountMoment (continuousScoreLaw n) a (q.aggregateCount n) (q.aggregateMean n) =
      ENNReal.ofReal ((∫ x, (q.aggregateCount n x - q.aggregateMean n x) ^ 2
        ∂continuousScoreLaw n) / a ^ 2) := by
  unfold scaledCenteredCountMoment
  simp_rw [div_pow]
  have hi := (q.integrable_sq_aggregateCount_sub_mean (n := n)).div_const (a ^ 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x ↦ by positivity),
    integral_div]

end PivotCountParameters

/-- For fixed admissible budgets, smallness of the two remaining pair
terms suffices for the scaled centered second moment. -/
theorem eventually_scaledCenteredCountMoment_le_of_pair_terms (b A B κ : ℝ) (K L : ℕ → ℕ)
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32)
    (hR : (fun n : ℕ ↦ ∫ x, (PivotCountParameters.mk b A B (K n) (L n)).comparableResidualMass x
        ∂continuousScoreLaw n) =o[atTop] (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2))
    (hC : (fun n : ℕ ↦ ∫ x, PivotCountParameters.incomparableCountProductMass
        ⟨b, A, B, K n, L n⟩ x ∂continuousScoreLaw n) =o[atTop]
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2))
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop,
      scaledCenteredCountMoment (continuousScoreLaw n) ((n : ℝ) * Real.log n)
        ((PivotCountParameters.mk b A B (K n) (L n)).aggregateCount n)
        ((PivotCountParameters.mk b A B (K n) (L n)).aggregateMean n) ≤ ENNReal.ofReal e := by
  let q (n : ℕ) := PivotCountParameters.mk b A B (K n) (L n)
  have hD := isLittleO_pivotRawDiagonalMass b A B κ K L hB hκ hK hL hsmallLabel hsmallCompat
  have hM := isLittleO_incomparableMeanProductMass b A B κ K L hb hA hB hκ hK hL
    hsmallLabel hsmallCompat
  have h := isLittleO_iff.mp ((hD.add (hR.const_mul_left (2 : ℝ))).add (hC.add hM)) he
  filter_upwards [h, eventually_gt_atTop (1 : ℕ)] with n hn hn'
  have ha : 0 < (n : ℝ) * Real.log n :=
    mul_pos (by positivity) (Real.log_pos (by exact_mod_cast hn'))
  have hq := (q n).integral_centered_sq_le_pair_terms (n := n)
  rw [(q n).integral_incomparableUpperMass_eq] at hq
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.log n))] at hn
  rw [(q n).scaledCenteredCountMoment_aggregate_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  exact hq.trans ((le_abs_self _).trans hn)

/-- At a prescribed accuracy the two open pair terms only need eventual
upper bounds. The short-cycle cutoff may be selected for this accuracy. -/
theorem eventually_scaledCenteredCountMoment_le_of_pair_bounds (b A B κ : ℝ) (K L : ℕ → ℕ)
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32)
    {e : ℝ} (he : 0 < e)
    (hPair : ∀ᶠ n : ℕ in atTop,
      (∫ x, PivotCountParameters.comparableResidualMass ⟨b, A, B, K n, L n⟩ x
        ∂continuousScoreLaw n) ≤ (e / 8) * ((n : ℝ) * Real.log n) ^ 2 ∧
      (∫ x, PivotCountParameters.incomparableCountProductMass ⟨b, A, B, K n, L n⟩ x
        ∂continuousScoreLaw n) ≤ (e / 4) * ((n : ℝ) * Real.log n) ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      scaledCenteredCountMoment (continuousScoreLaw n) ((n : ℝ) * Real.log n)
        ((PivotCountParameters.mk b A B (K n) (L n)).aggregateCount n)
        ((PivotCountParameters.mk b A B (K n) (L n)).aggregateMean n) ≤ ENNReal.ofReal e := by
  let q (n : ℕ) := PivotCountParameters.mk b A B (K n) (L n)
  have hD := isLittleO_pivotRawDiagonalMass b A B κ K L hB hκ hK hL hsmallLabel hsmallCompat
  have hM := isLittleO_incomparableMeanProductMass b A B κ K L hb hA hB hκ hK hL
    hsmallLabel hsmallCompat
  have hd := isLittleO_iff.mp hD (show 0 < e / 4 by positivity)
  have hm := isLittleO_iff.mp hM (show 0 < e / 4 by positivity)
  filter_upwards [hd, hm, hPair, eventually_gt_atTop (1 : ℕ)] with n hnd hnm hpair hn
  have ha : 0 < (n : ℝ) * Real.log n :=
    mul_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  have hq := (q n).integral_centered_sq_le_pair_terms (n := n)
  rw [(q n).integral_incomparableUpperMass_eq] at hq
  have hs := abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.log n))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hs] at hnd hnm
  have hd' := (le_abs_self _).trans hnd
  have hm' := (le_abs_self _).trans hnm
  rw [(q n).scaledCenteredCountMoment_aggregate_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  refine hq.trans ?_
  change pivotRawDiagonalMass (q n) n + 2 * (∫ x, (q n).comparableResidualMass x ∂continuousScoreLaw n) +
    ((∫ x, (q n).incomparableCountProductMass x ∂continuousScoreLaw n) +
      ∫ x, (q n).incomparableMeanProductMass x ∂continuousScoreLaw n) ≤ _
  linarith only [hd', hm', hpair.1, hpair.2]

private theorem eventually_pivotMean_large_of_abundance {b A B κ η : ℝ} (L : ℕ → ℕ)
    (hη : 0 ≤ η) (hA : 0 < A) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32)
    (hab : ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤ ENNReal.ofReal η) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (1 - η) ≤ (continuousScoreLaw n)
      {x | (3 * κ / (1280 * A)) * ((n : ℝ) * Real.log n) ≤
        (PivotCountParameters.mk b A B (pivotDecorationSupportCap κ n) (L n)).aggregateMean n x} := by
  let K := pivotDecorationSupportCap κ
  let d := 3 * κ / (1280 * A)
  have hK := eventually_pivotDecorationSupportCap_bounds hκ
  have hmean := eventually_localPivotMeanFloor_le_conditionalMean_ae K L hB hκ.le
    (hK.mono fun _ h ↦ ⟨h.1, h.2.1⟩) hL hsmallLabel hsmallCompat
  filter_upwards [hK, hmean, hab] with n hnK hnMean hnAb
  have hAll : ∀ᵐ x ∂continuousScoreLaw n, ∀ μ ρ : Matching n, IsScoreStable x μ →
      localPivotMeanFloor b A B (K n) μ ρ x ≤
        localPivotConditionalMean b A B (K n) (L n) μ ρ x := by
    rw [ae_all_iff]
    intro μ
    rw [ae_all_iff]
    intro ρ
    exact (ae_restrict_iff' (measurableSet_isScoreStable μ)).mp (hnMean μ ρ b A)
  have hnum : d * ((n : ℝ) * Real.log n) ≤ (3 / 64 : ℝ) * ((K n - 1 : ℕ) : ℝ) *
      (Real.sqrt n * Real.log n / (10 * A)) := by
    calc
      _ = (3 / 64 : ℝ) * (κ * Real.sqrt n / 2) * (Real.sqrt n * Real.log n / (10 * A)) := by
        calc
          _ = (3 * κ / (1280 * A)) * ((Real.sqrt n) ^ 2 * Real.log n) := by
            rw [Real.sq_sqrt (Nat.cast_nonneg n)]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnK.2.2 (by norm_num)) (by positivity)
  let E := locallyEligiblePivotAbundance n b A B
  have hE : ENNReal.ofReal (1 - η) ≤ continuousScoreLaw n E := by
    have he := measure_compl (μ := continuousScoreLaw n)
      (measurableSet_locallyEligiblePivotAbundance n b A B).compl
      (measure_ne_top (continuousScoreLaw n) Eᶜ)
    rw [show (locallyEligiblePivotAbundance n b A B)ᶜᶜ = E by simp [E], measure_univ] at he
    rw [ENNReal.ofReal_sub _ hη, ENNReal.ofReal_one, he]
    exact tsub_le_tsub_left hnAb _
  refine hE.trans (measure_mono_ae ?_)
  filter_upwards [ae_injective_rows n, hAll] with x ht hall hx
  exact hnum.trans (totalLocalPivotConditionalMean_ge_of_abundance ht hall hx)

/-- The two open pair integrals need only be eventually small at each
accuracy, possibly for a different divergent short-cycle cutoff. The
abundance parameters, and thus the lower-bound constant, are fixed first. -/
theorem lennonPittel_of_tunable_pivot_pair_bounds
    (hPair : ∀ b A B κ : ℝ, 0 < b → b ≤ 1 → 1 ≤ A → 0 < B → 0 < κ → κ < b →
      24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 →
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 →
      ∀ e : ℝ, 0 < e → ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
        ∀ᶠ n : ℕ in atTop,
          (∫ x, PivotCountParameters.comparableResidualMass
              ⟨b, A, B, pivotDecorationSupportCap κ n, L n⟩ x ∂continuousScoreLaw n) ≤
            (e / 8) * ((n : ℝ) * Real.log n) ^ 2 ∧
          (∫ x, PivotCountParameters.incomparableCountProductMass
              ⟨b, A, B, pivotDecorationSupportCap κ n, L n⟩ x ∂continuousScoreLaw n) ≤
            (e / 4) * ((n : ℝ) * Real.log n) ^ 2)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  apply lennonPittel_of_score_centered_counts_ae _ ε hε
  intro η hη
  obtain ⟨b, A, B, κ, hb, hb₁, hA, hB, hκ, hκb, hlabel, hcompat, hab⟩ :=
    exists_eligiblePivotAbundance_and_supportCoefficient hη
  let K := pivotDecorationSupportCap κ
  let d := 3 * κ / (1280 * A)
  have hA' := zero_lt_one.trans_le hA
  have hd : 0 < d := by unfold d; positivity
  have hK : ∀ᶠ n : ℕ in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ) :=
    (eventually_pivotDecorationSupportCap_bounds hκ).mono fun _ h ↦ ⟨h.1, h.2.1⟩
  refine ⟨d, hd, fun e he ↦ ?_⟩
  obtain ⟨L, hL, hbounds⟩ := hPair b A B κ hb hb₁ hA hB hκ hκb hlabel hcompat e he
  let q (n : ℕ) := PivotCountParameters.mk b A B (K n) (L n)
  refine ⟨fun n ↦ (q n).aggregateCount n, fun n ↦ (q n).aggregateMean n,
    fun _ ↦ measurable_totalLocalFilteredDecorationCount _ _ _ _ _,
    fun _ ↦ measurable_totalLocalPivotConditionalMean _ _ _ _ _, ?_⟩
  filter_upwards [hK, eventually_gt_atTop (0 : ℕ),
    eventually_pivotMean_large_of_abundance L hη.le hA' hB.le hκ hL hlabel hcompat hab,
    eventually_scaledCenteredCountMoment_le_of_pair_bounds b A B κ K L hb hA'.le hB.le hκ.le hK hL
      hlabel hcompat he hbounds] with n hnK hn hmean hvar
  exact ⟨ae_totalLocalFilteredDecorationCount_le hn hκb hnK.2, hmean, hvar⟩

/-- The two remaining analytic pair estimates imply the Lennon–Pittel tail.
The other parts of the variance decomposition and the abundance lower
bound are discharged by the actual marked score counts. -/
theorem lennonPittel_of_remaining_pivot_pair_estimates
    (hPair : ∀ b A B κ : ℝ, 0 < b → b ≤ 1 → 1 ≤ A → 0 < B → 0 < κ → κ < b →
      24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 →
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 →
      ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧
        ((fun n : ℕ ↦ ∫ x, PivotCountParameters.comparableResidualMass
            ⟨b, A, B, pivotDecorationSupportCap κ n, L n⟩ x ∂continuousScoreLaw n) =o[atTop]
          (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2)) ∧
        ((fun n : ℕ ↦ ∫ x, PivotCountParameters.incomparableCountProductMass
            ⟨b, A, B, pivotDecorationSupportCap κ n, L n⟩ x ∂continuousScoreLaw n) =o[atTop]
          (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  apply lennonPittel_of_tunable_pivot_pair_bounds _ ε hε
  intro b A B κ hb hb₁ hA hB hκ hκb hlabel hcompat e he
  obtain ⟨L, hL, hR, hC⟩ := hPair b A B κ hb hb₁ hA hB hκ hκb hlabel hcompat
  refine ⟨L, hL, ?_⟩
  filter_upwards [isLittleO_iff.mp hR (show 0 < e / 8 by positivity),
    isLittleO_iff.mp hC (show 0 < e / 4 by positivity)] with n hnR hnC
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.log n))] at hnR hnC
  exact ⟨(le_abs_self _).trans hnR, (le_abs_self _).trans hnC⟩

end LennonPittelFormalization

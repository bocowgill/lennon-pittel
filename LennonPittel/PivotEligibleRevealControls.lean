module

public import LennonPittel.PivotFilteredDecoration
public import LennonPittel.PivotReverseCompetitorMass
public import LennonPittel.PivotEligibilityScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Local eligibility controls for the filtered reverse moment

The reveal restricts only active observations. The arc budgets are consequences
of bounds on score weights removed from the original reverse columns.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Total male spouse score on the marked matching's diagonal. -/
def reverseDiagonalMaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).1

/-- Relative score losses available before the reverse columns are exposed:
one maximum entry, one active column, and the entire forward pivot. -/
structure ReverseMaskGeometry {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (s u p : ℝ) : Prop where
  score_mem : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1
  total_ge_two : 2 ≤ reverseDiagonalMaleTotal d
  max_nonneg : 0 ≤ s
  omitted_nonneg : 0 ≤ u
  pivot_nonneg : 0 ≤ p
  max_score : ∀ i, (diagonalPairAt d i).1 ≤ s * reverseDiagonalMaleTotal d
  omitted_score : ∀ i, forwardMaskOmittedMass d flag i ≤ u * reverseDiagonalMaleTotal d
  pivot_score : (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤ p * reverseDiagonalMaleTotal d

/-- The unrelaxed arc only loses the active column, diagonal, and target. -/
def reverseRawArcError (s u : ℝ) : ℝ := 2 * (2 * s + u)

/-- In a relaxed arc the pivot participants may also be omitted. -/
def reverseRelaxedArcInflation (s u p : ℝ) : ℝ := 1 + 2 * (2 * s + u + p)

/-- The lower arc error depends on the maximum normalized male score
and on the exponential truncation of the reverse competitor integral. -/
noncomputable def reverseLowerArcError (X s : ℝ) : ℝ := 14 * s + Real.exp (-X / 4)

/-- Forward information exposing precisely the pivot and bounding the
total of its nonnegative male score increments. -/
def eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    Set (ForwardRevealedMaleScores flag) :=
  {v | (∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ) ∧
    (∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m) ∧
    (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D}

theorem measurableSet_eligiblePivotRevealSet {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (D : ℝ) :
    MeasurableSet (eligiblePivotRevealSet d flag ρ D) := by
  have hs : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun τ ↦ ?_
    by_cases ht : τ = ρ
    · simpa only [ht, iff_true, ofPred_mem_eq] using
        measurableSet_forwardRevealExposureEvent ρ flag
    · simpa only [ht, iff_false, ← mem_compl_iff, ofPred_mem_eq] using
        (measurableSet_forwardRevealExposureEvent τ flag).compl
  have hnonneg : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement d flag ρ v m} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun m ↦ ?_
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun _ ↦
      measurableSet_le measurable_const (measurable_forwardPivotIncrement d flag ρ m)
  have hsum : MeasurableSet {v : ForwardRevealedMaleScores flag |
      (∑ m ∈ ρ.support, forwardPivotIncrement d flag ρ v m) ≤ D} :=
    measurableSet_le (Finset.measurable_sum _ (fun m _ ↦
      measurable_forwardPivotIncrement d flag ρ m)) measurable_const
  exact hs.inter (hnonneg.inter hsum)

/-- If a fraction at most `q ≤ 1/2` is removed, inflating by `1 + 2*q`
is enough to recover the original mass. -/
theorem total_div_one_add_two_mul_le_remaining {X q : ℝ} (hX : 0 ≤ X) (hq : 0 ≤ q)
    (hq' : q ≤ 1 / 2) : X / (1 + 2 * q) ≤ X * (1 - q) := by
  have hp : 0 < 1 + 2 * q := by linarith
  apply (div_le_iff₀ hp).mpr
  calc
    X = X * 1 := (mul_one _).symm
    _ ≤ X * ((1 - q) * (1 + 2 * q)) := by
      apply mul_le_mul_of_nonneg_left _ hX
      nlinarith only [mul_nonneg hq (show 0 ≤ 1 - 2 * q by linarith)]
    _ = _ := (mul_assoc ..).symm

namespace ReverseMaskGeometry

variable {n : ℕ} {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
  {μ ρ : Matching n} {s u p : ℝ}

/-- Absolute inactive mass before removing the designated reverse target. -/
theorem available_ge (h : ReverseMaskGeometry d flag ρ s u p) (i : Fin n) :
    reverseDiagonalMaleTotal d * (1 - (s + u)) ≤
      ∑ q : ForwardInactiveColumnIndex flag i, forwardInactiveColumnThreshold d q := by
  rw [sum_forwardInactiveColumn_eq]
  have hi := h.max_score i
  have hm := h.omitted_score i
  unfold reverseDiagonalMaleTotal at *
  nlinarith only [hi, hm]

/-- Absolute original competitor mass after removing the designated target. -/
theorem competitor_ge (h : ReverseMaskGeometry d flag ρ s u p) {i : Fin n}
    (q : ForwardInactiveColumnIndex flag i) :
    reverseDiagonalMaleTotal d * (1 - (2 * s + u)) ≤
      ∑ t : {t : ForwardInactiveColumnIndex flag i // t ≠ q},
        forwardInactiveColumnThreshold d t.val := by
  rw [sum_forwardInactiveCompetitor_eq]
  have hi := h.max_score i
  have hm := h.omitted_score i
  have hq := h.max_score (forwardInactiveColumnMan q)
  unfold reverseDiagonalMaleTotal at *
  change _ ≤ _ - _ - _ - (diagonalPairAt d (forwardInactiveColumnMan q)).1
  nlinarith only [hi, hm, hq]

/-- Absolute competitor mass when the pivot men are additionally omitted. -/
theorem kept_competitor_ge (h : ReverseMaskGeometry d flag ρ s u p) {i : Fin n}
    (q : ForwardKeptColumnIndex flag ρ.support i) :
    reverseDiagonalMaleTotal d * (1 - (2 * s + u + p)) ≤ forwardKeptCompetitorMass d q := by
  refine le_trans ?_ (forwardKeptCompetitorMass_ge d q (fun j ↦ (h.score_mem j).1.1))
  have hi := h.max_score i
  have hm := h.omitted_score i
  have hq := h.max_score (forwardInactiveColumnMan q.val)
  have hp := h.pivot_score
  unfold reverseDiagonalMaleTotal at *
  change _ ≤ _ - _ - _ - _ - (diagonalPairAt d (forwardInactiveColumnMan q.val)).1
  nlinarith only [hi, hm, hq, hp]

/-- The forbidden reverse target weight only includes the diagonal and the mask. -/
theorem forbidden_weight_le (h : ReverseMaskGeometry d flag ρ s u p) (i : Fin n) :
    (∑ j ∈ forwardMaskForbiddenTargets μ flag i, reverseSpouseWeights μ d j) ≤
      ENNReal.ofReal (s + u) := by
  have hX : 0 < reverseDiagonalMaleTotal d := by linarith [h.total_ge_two]
  rw [sum_forwardMaskForbiddenTargets_reverseSpouseWeights μ d flag i
    (fun j ↦ (h.score_mem j).1.1) hX]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hX).mpr
  linarith only [h.max_score (μ.symm i), h.omitted_score (μ.symm i)]

/-- The pivot support weight is unchanged by indexing the men by their spouses. -/
theorem pivot_weight_le (h : ReverseMaskGeometry d flag ρ s u p) :
    (∑ j ∈ ρ.support.map μ.toEmbedding, reverseSpouseWeights μ d j) ≤ ENNReal.ofReal p := by
  have hX : 0 < reverseDiagonalMaleTotal d := by linarith [h.total_ge_two]
  simp only [Finset.sum_map, reverseSpouseWeights, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
  change (∑ i ∈ ρ.support, ENNReal.ofReal ((diagonalPairAt d i).1 /
    reverseDiagonalMaleTotal d)) ≤ _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (h.score_mem i).1.1 hX.le),
    ← Finset.sum_div]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hX).mpr h.pivot_score)

/-- Compile local score bounds and numerical budgets into the three
interfaces consumed by the filtered fixed-reveal first moment. -/
theorem momentControls (h : ReverseMaskGeometry d flag ρ s u p) (K : ℕ) (D C : ℝ)
    (hq : 2 * s + u + p ≤ 1 / 2)
    (hlabel : ∀ k ∈ Finset.Icc 2 K,
      reverseGoodLabelLoss k (reverseSpouseWeights μ d) (ρ.support.map μ.toEmbedding)
        (ENNReal.ofReal (s + u)) ≤ ENNReal.ofReal (1 / 4))
    (hδ : let δ := reverseLowerArcError (reverseDiagonalMaleTotal d) s
      0 ≤ δ ∧ δ ≤ 1 ∧ (K : ℝ) * δ ≤ 1 / 4)
    (hu : reverseRawArcError s u ≤ C / Real.sqrt (n : ℝ))
    (ht : ∀ᵐ z ∂offDiagonalScoreLaw n,
      ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) :
    ReverseCompatibilityControls μ ρ d flag (eligiblePivotRevealSet d flag ρ D)
        (reverseRelaxedArcInflation s u p) D ∧
      ReverseUnfilteredControls μ ρ d flag K (ENNReal.ofReal (s + u))
        (s * reverseDiagonalMaleTotal d) (reverseLowerArcError (reverseDiagonalMaleTotal d) s) ∧
      ReverseFilterUpperControls d flag (reverseRawArcError s u) C := by
  let X := reverseDiagonalMaleTotal d
  let U := eligiblePivotRevealSet d flag ρ D
  have hX : 0 < X := by linarith [h.total_ge_two]
  have hm (i : Fin n) : (diagonalPairAt d i).1 ∈ Icc 0 1 :=
    ⟨(h.score_mem i).1.1, (h.score_mem i).1.2.le⟩
  have hU : MeasurableSet U := measurableSet_eligiblePivotRevealSet d flag ρ D
  have hrel : 0 ≤ 2 * s + u + p := by
    linarith [h.max_nonneg, h.omitted_nonneg, h.pivot_nonneg]
  have hraw : 0 ≤ 2 * s + u := by linarith [h.max_nonneg, h.omitted_nonneg]
  have hraw' : 2 * s + u ≤ 1 / 2 := by linarith [h.pivot_nonneg]
  have hhalf (q : ℝ) (hq : q ≤ 1 / 2) : X / 2 ≤ X * (1 - q) := calc
    _ = X * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hX.le
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hU, fun i ↦ (h.score_mem i).2.1, fun i ↦ (h.score_mem i).2.2, hm, hX,
      show 0 < reverseRelaxedArcInflation s u p from by
        unfold reverseRelaxedArcInflation
        linarith,
      fun i q ↦ (total_div_one_add_two_mul_le_remaining hX.le hrel hq).trans
        (h.kept_competitor_ge q),
      fun _ hv ↦ hv.2.1, fun _ hv ↦ hv.2.2, ht, ?_⟩
    exact ae_isExposedRotation_of_forwardReveal_subset μ ρ d flag U hU
      (fun _ hv ↦ (hv.1 ρ).mpr rfl) ht
  · refine ⟨h.forbidden_weight_le, hlabel, h.total_ge_two, fun i q ↦
      (hhalf _ hraw').trans (h.competitor_ge q), h.max_score, ?_, hδ.1, hδ.2.1, hδ.2.2⟩
    change 14 * (s * X) / X + Real.exp (-X / 4) ≤ 14 * s + Real.exp (-X / 4)
    rw [mul_div_assoc, mul_div_cancel_right₀ _ hX.ne']
  · refine ⟨show 0 ≤ reverseRawArcError s u from mul_nonneg (by norm_num) hraw, hu,
      fun i q ↦ (total_div_one_add_two_mul_le_remaining hX.le hraw hraw').trans
        (h.competitor_ge q), fun i ↦ (hhalf _ (by linarith [h.max_nonneg])).trans
          (h.available_ge i)⟩

end ReverseMaskGeometry

/-- The compatibility loss is small at the square-root support cutoff
when the inflation and the relative pivot-increment budget are of order
`1 / √n`. -/
theorem reverseCompatibilityBudget_of_squareRoot {n K : ℕ} {a X D κ Q V : ℝ}
    (hn : 0 < n) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hK : (K : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (ha : 1 ≤ a) (ha₂ : a ≤ 2) (haQ : a ≤ 1 + Q / Real.sqrt (n : ℝ))
    (hD : D / X ≤ V / Real.sqrt (n : ℝ))
    (hsmall : Real.exp (κ * Q) * (2 * κ * V) ≤ 3 / 32) :
    ENNReal.ofReal a ^ K * (K : ℝ≥0∞) * ENNReal.ofReal (a * D / X) ≤
      ENNReal.ofReal (3 / 32) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ha₀ : 0 ≤ a := by linarith
  have hpow : a ^ K ≤ Real.exp (κ * Q) := by
    calc
      _ ≤ (Real.exp (Q / Real.sqrt (n : ℝ))) ^ K := pow_le_pow_left₀ ha₀
        (haQ.trans (by linarith only [Real.add_one_le_exp (Q / Real.sqrt (n : ℝ))])) _
      _ = Real.exp ((K : ℝ) * (Q / Real.sqrt (n : ℝ))) := (Real.exp_nat_mul ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (calc
        _ ≤ (κ * Real.sqrt (n : ℝ)) * (Q / Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hK (div_nonneg hQ hs.le)
        _ = _ := by field_simp)
  have hfac : a * D / X ≤ 2 * (V / Real.sqrt (n : ℝ)) := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hD ha₀).trans
      (mul_le_mul_of_nonneg_right ha₂ (div_nonneg hV hs.le))
  have hfac' : ENNReal.ofReal (a * D / X) ≤
      ENNReal.ofReal (2 * (V / Real.sqrt (n : ℝ))) := ENNReal.ofReal_le_ofReal hfac
  calc
    _ ≤ ENNReal.ofReal (Real.exp (κ * Q)) * (K : ℝ≥0∞) *
        ENNReal.ofReal (2 * (V / Real.sqrt (n : ℝ))) := by
      rw [← ENNReal.ofReal_pow ha₀]
      exact mul_le_mul' (mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _) hfac'
    _ = ENNReal.ofReal (Real.exp (κ * Q) * ((K : ℝ) *
        (2 * (V / Real.sqrt (n : ℝ))))) := by
      rw [mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      refine (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hK (by positivity)) (Real.exp_nonneg _)).trans ?_
      convert hsmall using 1
      field_simp

/-- The diagonal, designated target, and active-mask losses together are
eventually at most one inverse square root of the total male score. -/
theorem eventually_reverseRawMaskBudget (Cx : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      2 * (Cx * Real.log n / n) + (n : ℝ) ^ (-11 / 20 : ℝ) ≤ 1 / Real.sqrt (n : ℝ) := by
  have hlog := (((isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).const_mul_left
    (4 * Cx)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop (1 : ℕ), hlog, hpow.eventually_ge_atTop 2]
    with n hn hln hpn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let R := Real.sqrt (n : ℝ)
  have hR : 0 < R := Real.sqrt_pos.mpr hn₀
  have hR2 : R ^ 2 = (n : ℝ) := Real.sq_sqrt hn₀.le
  have hln' : 4 * Cx * Real.log n ≤ R := by
    have hh : |4 * Cx * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := hln
    rw [← Real.sqrt_eq_rpow, abs_of_nonneg hR.le] at hh
    exact (le_abs_self _).trans hh
  have hA : 2 * (Cx * Real.log n / n) ≤ 1 / (2 * R) := by
    calc
      _ = (4 * Cx * Real.log n) / (2 * (n : ℝ)) := by ring
      _ ≤ R / (2 * (n : ℝ)) := div_le_div_of_nonneg_right hln' (by positivity)
      _ = _ := by rw [← hR2]; field_simp
  have hB : (n : ℝ) ^ (-11 / 20 : ℝ) ≤ 1 / (2 * R) := by
    rw [show (-11 / 20 : ℝ) = -(1 / 2 + 1 / 20) by norm_num, Real.rpow_neg hn₀.le,
      Real.rpow_add hn₀, ← Real.sqrt_eq_rpow, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    rw [mul_comm 2]
    exact mul_le_mul_of_nonneg_left hpn hR.le
  exact ⟨hn, (add_le_add hA hB).trans_eq (by ring)⟩

/-- A single positive support coefficient can meet both the label loss
and the compatibility loss budgets while staying strictly below the
lower pivot-length coefficient. -/
theorem exists_eligibleSupportCoefficient {b H B V : ℝ} (hb : 0 < b)
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hV : 0 ≤ V) :
    ∃ κ, 0 < κ ∧ κ < b ∧ H * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * V) ≤ 3 / 32 := by
  let Q := 2 * (1 + B)
  let d₁ := 1 / (Q + 1)
  let d₂ := 3 / (64 * (V + 1) * Real.exp 1)
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have h₁ : 0 < d₁ := by dsimp [d₁]; positivity
  have h₂ : 0 < d₂ := by dsimp [d₂]; positivity
  obtain ⟨κ, hκ, hκ', hbudget⟩ := exists_squareRootLabelBudget
    (lt_min hb (lt_min h₁ h₂)) hH hB (by norm_num : 0 ≤ (1 : ℝ))
  have hκQ : κ * Q ≤ 1 := calc
    _ ≤ κ * (Q + 1) := mul_le_mul_of_nonneg_left (by linarith) hκ.le
    _ ≤ _ := (le_div_iff₀ (by positivity : 0 < Q + 1)).mp
      (hκ'.le.trans (min_le_right ..) |>.trans (min_le_left ..))
  have hκV : κ * (64 * (V + 1) * Real.exp 1) ≤ 3 :=
    (le_div_iff₀ (by positivity : 0 < 64 * (V + 1) * Real.exp 1)).mp
      (hκ'.le.trans (min_le_right ..) |>.trans (min_le_right ..))
  refine ⟨κ, hκ, hκ'.trans_le (min_le_left ..), hbudget, ?_⟩
  calc
    _ ≤ Real.exp 1 * (2 * κ * V) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hκQ) (by positivity)
    _ ≤ Real.exp 1 * (2 * κ * (V + 1)) := by gcongr; linarith
    _ ≤ _ := by linarith only [hκV]

/-- The spouse-score product and the upper band edge supply the male
total growth used in the lower-arc approximation. -/
theorem reverseMaleTotal_ge_of_scoreBand {n : ℕ} {X Y c : ℝ}
    (hn : 0 < n) (hc : 0 ≤ c) (hY : 0 < Y)
    (hY' : Y ≤ (n : ℝ) ^ (2 / 5 : ℝ)) (hXY : c * n ≤ X * Y) :
    c * (n : ℝ) ^ (3 / 5 : ℝ) ≤ X := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ((le_div_iff₀ hY).mpr ?_).trans ((div_le_iff₀ hY).mpr hXY)
  calc
    _ ≤ (c * (n : ℝ) ^ (3 / 5 : ℝ)) * (n : ℝ) ^ (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hY' (by positivity)
    _ = c * (n : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hn₀, show (3 / 5 : ℝ) + 2 / 5 = 1 by norm_num,
        Real.rpow_one]

/-- The bound on the forward increment total, divided by the male total,
has inverse-square-root size on a regular spouse-score product. -/
theorem reversePivotIncrementRatio_le_of_scoreProduct {n : ℕ} {X Y c B D : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y) (hB : 0 ≤ B)
    (hXY : c * n ≤ X * Y) (hD : Y * D ≤ B * Real.sqrt (n : ℝ)) :
    D / X ≤ (B / c) / Real.sqrt (n : ℝ) := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hR : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  calc
    _ ≤ ((B * Real.sqrt (n : ℝ)) / Y) / X :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hY).mpr (by linarith)) hX.le
    _ = (B * Real.sqrt (n : ℝ)) / (X * Y) := by ring
    _ ≤ (B * Real.sqrt (n : ℝ)) / (c * n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hXY
    _ = (B * Real.sqrt (n : ℝ)) / (c * (Real.sqrt (n : ℝ)) ^ 2) := by
      rw [Real.sq_sqrt hn₀.le]
    _ = _ := by field_simp

/-- The local inputs of the filtered first moment, with the numerical
arc factors determined by the score losses rather than chosen afresh. -/
structure EligibleReverseMomentCertificate {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (K L : ℕ) (D s u p : ℝ) : Prop where
  n_pos : 0 < n
  short_scale : 2 ≤ L
  compatibility : ReverseCompatibilityControls μ ρ d flag (eligiblePivotRevealSet d flag ρ D)
    (reverseRelaxedArcInflation s u p) D
  unfiltered : ReverseUnfilteredControls μ ρ d flag K (ENNReal.ofReal (s + u))
    (s * reverseDiagonalMaleTotal d) (reverseLowerArcError (reverseDiagonalMaleTotal d) s)
  upper : ReverseFilterUpperControls d flag (reverseRawArcError s u) 2
  relaxed_inflation_ge_one : 1 ≤ reverseRelaxedArcInflation s u p
  compatibility_budget : ENNReal.ofReal (reverseRelaxedArcInflation s u p) ^ K *
    (K : ℝ≥0∞) * ENNReal.ofReal
      (reverseRelaxedArcInflation s u p * D / reverseDiagonalMaleTotal d) ≤
    ENNReal.ofReal (3 / 32)
  short_budget : ENNReal.ofReal (1 + reverseRawArcError s u) ^ K *
    ENNReal.ofReal (4 / Real.log (L : ℝ)) ≤ ENNReal.ofReal (3 / 128)
  increment_budget : ENNReal.ofReal
    (Real.sqrt (reverseFilterSecondMomentConstant 2) / (n : ℝ) ^ 2) ≤
    ENNReal.ofReal (3 / 128) * ((K - 1 : ℕ) : ℝ≥0∞)

/-- All fixed-reveal moment controls hold eventually, uniformly in the
eligible score vectors and masks. The two fixed coefficient budgets can
be obtained from `exists_eligibleSupportCoefficient`. -/
theorem eventually_eligibleReverseMomentCertificate (K L : ℕ → ℕ)
    {Cx H B V κ c : ℝ} (hCx : 0 ≤ Cx) (hH : 0 ≤ H) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hκ : 0 ≤ κ) (hc : 0 < c)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : H * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * V) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop,
      let s := Cx * Real.log (n : ℝ) / n
      let u := (n : ℝ) ^ (-11 / 20 : ℝ)
      let p := B / Real.sqrt (n : ℝ)
      ∀ (μ ρ : Matching n) (d : DiagonalScorePairs n)
        (flag : OffDiagonalCellIndex n → Bool) (D : ℝ),
        ReverseMaskGeometry d flag ρ s u p →
        c * (n : ℝ) ^ (3 / 5 : ℝ) ≤ reverseDiagonalMaleTotal d →
        (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤ ENNReal.ofReal (H / n) →
        D / reverseDiagonalMaleTotal d ≤ V / Real.sqrt (n : ℝ) →
        (∀ᵐ z ∂offDiagonalScoreLaw n,
          ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) →
        EligibleReverseMomentCertificate μ ρ d flag (K n) (L n) D s u p := by
  let s (n : ℕ) := Cx * Real.log (n : ℝ) / n
  let u (n : ℕ) := (n : ℝ) ^ (-11 / 20 : ℝ)
  let δ (n : ℕ) := reverseRawArcError (s n) (u n)
  let R (n : ℕ) := Real.sqrt (n : ℝ)
  have hraw := eventually_reverseRawMaskBudget Cx
  have hδ : ∀ᶠ n in atTop, 0 ≤ δ n ∧ (K n : ℝ) * δ n ≤ 2 * κ := by
    filter_upwards [hraw, hK] with n hn hk
    have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn.1.le)
    have hR : 0 < R n := Real.sqrt_pos.2 hn₀
    have hs : 0 ≤ s n := div_nonneg (mul_nonneg hCx hlog) hn₀.le
    have hu : 0 ≤ u n := Real.rpow_nonneg hn₀.le _
    have hn' : 2 * s n + u n ≤ 1 / R n := hn.2
    have hδn : δ n ≤ 2 / R n := by
      change 2 * (2 * s n + u n) ≤ 2 / R n
      calc
        _ ≤ 2 * (1 / R n) := mul_le_mul_of_nonneg_left hn' (by norm_num)
        _ = _ := by ring
    refine ⟨show 0 ≤ 2 * (2 * s n + u n) by positivity, ?_⟩
    calc
      _ ≤ (K n : ℝ) * (2 / R n) := mul_le_mul_of_nonneg_left hδn (Nat.cast_nonneg _)
      _ ≤ (κ * R n) * (2 / R n) :=
        mul_le_mul_of_nonneg_right hk.2 (div_nonneg (by norm_num) hR.le)
      _ = _ := by field_simp
  have hfilter := eventually_reverseFilterLossBudgets K L δ 2 (2 * κ)
    (hK.mono fun _ h ↦ h.1) hL hδ
  have hlarge : ∀ᶠ n in atTop, 2 * (1 + B) ≤ R n :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [hraw, hK, hfilter, hlarge,
    eventually_reverseArcLowerBudget_uniform (C := Cx) hκ hc]
    with n hraw_n hKn hf hlarge_n hlow
  dsimp only
  intro μ ρ d flag D hgeom hXrate hweights hD ht
  let X := reverseDiagonalMaleTotal d
  let p := B / R n
  let a := reverseRelaxedArcInflation (s n) (u n) p
  have hn : 0 < n := by omega
  have hR : 0 < R n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hX : 0 < X := by linarith [hgeom.total_ge_two]
  have hraw' : 2 * s n + u n ≤ 1 / R n := hraw_n.2
  have hq₁ : 2 * s n + u n + p ≤ (1 + B) / R n := by
    rw [add_div]
    exact add_le_add_left hraw' p
  have hq : 2 * s n + u n + p ≤ 1 / 2 := hq₁.trans
    ((div_le_iff₀ hR).mpr (by linarith))
  have ha : 1 ≤ a := by
    change 1 ≤ 1 + 2 * (2 * s n + u n + p)
    have hs : 0 ≤ s n := hgeom.max_nonneg
    have hu : 0 ≤ u n := hgeom.omitted_nonneg
    have hp : 0 ≤ p := hgeom.pivot_nonneg
    exact le_add_of_nonneg_right (by positivity)
  have ha₂ : a ≤ 2 := by
    change 1 + 2 * (2 * s n + u n + p) ≤ 2
    linarith
  have haQ : a ≤ 1 + (2 * (1 + B)) / R n := by
    change 1 + 2 * (2 * s n + u n + p) ≤ _
    rw [mul_div_assoc]
    linarith
  have hη : ENNReal.ofReal (s n + u n) ≤ ENNReal.ofReal (1 / R n) :=
    ENNReal.ofReal_le_ofReal (by linarith [hgeom.max_nonneg])
  have hlabel : ∀ k ∈ Finset.Icc 2 (K n),
      reverseGoodLabelLoss k (reverseSpouseWeights μ d) (ρ.support.map μ.toEmbedding)
        (ENNReal.ofReal (s n + u n)) ≤ ENNReal.ofReal (1 / 4) := by
    intro k hk
    have hk' : (k : ℝ) ≤ (K n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact (reverseGoodLabelLoss_le_of_squareRoot hn hH hB (by norm_num : 0 ≤ (1 : ℝ))
      (hk'.trans hKn.2) _ _ _ hweights hgeom.pivot_weight_le hη).trans
      (ENNReal.ofReal_le_ofReal hsmallLabel)
  have hδlo : let δlo := reverseLowerArcError X (s n)
      0 ≤ δlo ∧ δlo ≤ 1 ∧ (K n : ℝ) * δlo ≤ 1 / 4 := by
    have hratio : s n * X / X = s n := mul_div_cancel_right₀ _ hX.ne'
    have h := hlow (K n) X (s n * X) hXrate
      (mul_nonneg hgeom.max_nonneg hX.le) (hratio.le) hKn.2
    simpa only [reverseLowerArcError, mul_div_assoc, hratio] using h
  have hupper : δ n ≤ 2 / R n := by
    change 2 * (2 * s n + u n) ≤ 2 / R n
    calc
      _ ≤ 2 * (1 / R n) := mul_le_mul_of_nonneg_left hraw' (by norm_num)
      _ = _ := by ring
  obtain ⟨hcomp, hunf, hup⟩ := hgeom.momentControls (μ := μ) (K n) D 2 hq hlabel hδlo hupper ht
  refine ⟨hn, hf.1, hcomp, hunf, hup, ha, ?_, hf.2.1, hf.2.2⟩
  exact reverseCompatibilityBudget_of_squareRoot hn (by linarith) hV hKn.2 ha ha₂ haQ
    hD hsmallCompat

/-- The lower moment of actual filtered decorations on an eligible reveal. -/
theorem EligibleReverseMomentCertificate.lowerMoment {n K L : ℕ} {μ ρ : Matching n}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool} {D s u p : ℝ}
    (h : EligibleReverseMomentCertificate μ ρ d flag K L D s u p)
    (F : OffDiagonalScorePairs n → ℝ≥0∞)
    (hF : ∀ z,
      let pr := profileOfScores ((splitScorePairs μ).symm (d, z))
      ∀ (μ₀ : Matching n) (hopt : IsManOptimal pr μ₀) (r : Rotation pr μ₀),
        (singletonRotationAnchor hopt r).val = μ → r.val.cycle = ρ →
        (Nat.card (FilteredPivotDecoration hopt K r L
          (reverseIncrementCutoff n (reverseDiagonalMaleTotal d))) : ℝ≥0∞) ≤ F z) :
    let U := eligiblePivotRevealSet d flag ρ D
    (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 64) * ((K - 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ z, F z ∂forwardMaskRevealLaw d flag U :=
  lintegral_filteredDecorationCount_ge μ ρ d flag _ L h.short_scale h.n_pos h.compatibility
    h.unfiltered h.upper h.relaxed_inflation_ge_one h.compatibility_budget h.short_budget
    h.increment_budget (fun _ hv ↦ hv.1) F hF

end LennonPittelFormalization

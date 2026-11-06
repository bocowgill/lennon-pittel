module

public import LennonPittel.PivotEligibleMask
public import LennonPittel.PivotEligibleRevealControls

/-!
# Forward masks on the base pivot score band

The lower bound on the spouse-score product and the male score cutoff
give a uniform bound on each normalized male score.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- Total female spouse score on the marked matching's diagonal. -/
def pivotDiagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ i, (diagonalPairAt d i).2

/-- The base pivot band used for forward mask concentration. -/
def pivotBaseDiagonalBand (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | let X := reverseDiagonalMaleTotal d
       let Y := pivotDiagonalFemaleTotal d
       (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1 ∧ (diagonalPairAt d i).2 ∈ Ico 0 1) ∧
       2 ≤ Y ∧ Y ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧ (n : ℝ) / 128 ≤ X * Y ∧
       (∀ i, (diagonalPairAt d i).2 / Y ≤ 12 * Real.log n / n) ∧
       ∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (Y - 1)}

theorem measurableSet_pivotBaseDiagonalBand (n : ℕ) :
    MeasurableSet (pivotBaseDiagonalBand n) := by
  have hx (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hy (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hX : Measurable (@reverseDiagonalMaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hx i
  have hY : Measurable (@pivotDiagonalFemaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hy i
  unfold pivotBaseDiagonalBand
  simp only [ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun i ↦
    (measurableSet_Ico.preimage (hx i)).inter (measurableSet_Ico.preimage (hy i))).inter ?_
  exact (measurableSet_le measurable_const hY).inter
    ((measurableSet_le hY measurable_const).inter
      ((measurableSet_le measurable_const (hX.mul hY)).inter
        ((MeasurableSet.iInter fun i ↦ measurableSet_le ((hy i).div hY) measurable_const).inter
          (MeasurableSet.iInter fun i ↦ measurableSet_le (hx i)
            (measurable_const.div (hY.sub measurable_const))))))

/-- The product and absolute-score bounds give a normalized male score cutoff. -/
theorem normalizedMaleScore_le_of_spouseProduct {n : ℕ} {X Y x : ℝ}
    (hn : 0 < n) (hY : 2 ≤ Y) (hXY : (n : ℝ) / 128 ≤ X * Y)
    (hx : x ≤ 8 * Real.log n / (Y - 1)) :
    x / X ≤ 2048 * Real.log n / n := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog := Real.log_nonneg (show 1 ≤ (n : ℝ) by exact_mod_cast hn)
  have hY₀ : 0 < Y := by linarith
  have hY₁ : 0 < Y - 1 := by linarith
  have hXY₀ : 0 < X * Y := (div_pos hn₀ (by norm_num)).trans_le hXY
  have hX₀ : 0 < X := pos_of_mul_pos_left hXY₀ hY₀.le
  have hquot : Y / (Y - 1) ≤ 2 := (div_le_iff₀ hY₁).2 (by linarith)
  calc
    x / X ≤ (8 * Real.log n / (Y - 1)) / X := div_le_div_of_nonneg_right hx hX₀.le
    _ = (8 * Real.log n * (Y / (Y - 1))) / (X * Y) := by
      field_simp
    _ ≤ (8 * Real.log n * 2) / (X * Y) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hquot (mul_nonneg (by norm_num) hlog)) hXY₀.le
    _ ≤ (8 * Real.log n * 2) / ((n : ℝ) / 128) := div_le_div_of_nonneg_left
      (by positivity) (div_pos hn₀ (by norm_num)) hXY
    _ = _ := by ring

/-- Heavy forward masks on the base pivot band have negligible expected mark count. -/
theorem eventually_sum_measure_badForwardMaskAnchorEvent_on_pivotBaseDiagonalBand_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ μ : Matching n, continuousScoreLaw n
      (badForwardMaskAnchorEvent μ (pivotBaseDiagonalBand n) ((n : ℝ) ^ (-11 / 20 : ℝ)))) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_sum_measure_badForwardMaskAnchorEvent_le 2048 12 p (by norm_num),
    eventually_gt_atTop (0 : ℕ)] with n h hn
  apply h _ (measurableSet_pivotBaseDiagonalBand n)
  intro d hd
  obtain ⟨hscore, hY, hY', hXY, hy, hx⟩ := hd
  have hY₀ : 0 < pivotDiagonalFemaleTotal d := by linarith
  have hX₀ : 0 < reverseDiagonalMaleTotal d :=
    pos_of_mul_pos_left ((div_pos (Nat.cast_pos.mpr hn) (by norm_num)).trans_le hXY) hY₀.le
  refine ⟨hscore, hX₀, ?_, ?_⟩
  · exact fun i ↦ normalizedMaleScore_le_of_spouseProduct hn hY hXY (hx i)
  · exact fun i ↦ femaleScore_le_of_share_of_band hn (by norm_num) hY₀ hY' (hy i)

end LennonPittelFormalization

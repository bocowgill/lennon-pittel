module

public import LennonPittel.CoexposureScoreMomentBound
public import LennonPittel.CoexposureSpouseShells
public import LennonPittel.MarkedForwardRowDeficit
public import LennonPittel.PivotSpouseSquareRegularity
public import LennonPittel.SmallSpouseTotalLog

/-!
# Regular diagonals for the singleton-rotation length estimate

The cutoffs defining the good diagonal depend only on spouse scores. Their
complement has a small expected count among all score-stable marks.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The local diagonal conditions for the forward forest and length estimates. -/
def singletonLengthGoodDiagonal (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | d ∈ goodDiagonalScores n ∧
    (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) ∧
    (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) ∧
    (9 / 10 : ℝ) * Real.log n ≤ pivotDiagonalFemaleTotal d ∧
    (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) ∧
    (∑ i, forwardSpouseWeight d i *
      Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤
      (n : ℝ) ^ (-3 / 4 : ℝ)}

theorem measurableSet_singletonLengthGoodDiagonal (n : ℕ) :
    MeasurableSet (singletonLengthGoodDiagonal n) := by
  have hx (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hy (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hY : Measurable (@pivotDiagonalFemaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hy i
  have hw (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ forwardSpouseWeight d i) :=
    (hy i).div hY
  have hsq : Measurable (fun d : DiagonalScorePairs n ↦ ∑ i, (forwardSpouseWeight d i) ^ 2) :=
    Finset.measurable_sum _ fun i _ ↦ (hw i).pow_const _
  have hend : Measurable (fun d : DiagonalScorePairs n ↦ ∑ i, forwardSpouseWeight d i *
      Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) :=
    Finset.measurable_sum _ fun i _ ↦ (hw i).mul
      (Real.measurable_exp.comp (((measurable_const.sub (hx i)).mul hY).neg))
  unfold singletonLengthGoodDiagonal
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_goodDiagonalScores n).inter
    ((MeasurableSet.iInter fun i ↦ measurableSet_Ico.preimage (hx i)).inter
      ((MeasurableSet.iInter fun i ↦ measurableSet_Icc.preimage (hy i)).inter
        ((measurableSet_le measurable_const hY).inter
          ((measurableSet_le hsq measurable_const).inter
            (measurableSet_le hend measurable_const)))))

/-- The local good diagonal supplies the forward reference deficit budget. -/
theorem eventually_hasForwardReferenceDeficit_of_singletonLengthGoodDiagonal :
    ∀ᶠ n : ℕ in atTop, ∀ d ∈ singletonLengthGoodDiagonal n,
      HasForwardReferenceDeficit d (3 * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
  filter_upwards [eventually_hasForwardReferenceDeficit] with n h d hd
  exact h d hd.2.1 hd.2.2.1 hd.1.1 hd.1.2.1 hd.1.2.2 hd.2.2.2.2.1 hd.2.2.2.2.2

private def badSingletonSmallTotal {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}

private def badSingletonRelativeShare {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n}

private theorem measure_badSingletonLengthDiagonal_le {n : ℕ} (hn : 0 < n)
    (hlog : 2 ≤ (9 / 10 : ℝ) * Real.log n) (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧
        (splitScorePairs μ x).1 ∉ singletonLengthGoodDiagonal n} ≤
      continuousScoreLaw n (badSingletonSmallTotal μ) +
        continuousScoreLaw n (badSingletonRelativeShare μ) +
        continuousScoreLaw n (badMaleSpouseScores μ) +
        continuousScoreLaw n (badFemaleSpouseSquareMark μ) +
        continuousScoreLaw n (badForwardEndpointMark μ) := by
  let exceptions : Set (ScoreProfile n) :=
    (((badSingletonSmallTotal μ ∪ badSingletonRelativeShare μ) ∪ badMaleSpouseScores μ) ∪
      badFemaleSpouseSquareMark μ) ∪ badForwardEndpointMark μ
  have hsub : {x | IsScoreStable x μ ∧
        (splitScorePairs μ x).1 ∉ singletonLengthGoodDiagonal n} ≤ᵐ[continuousScoreLaw n]
      exceptions := by
    filter_upwards [ae_unitOpen_scores n] with x hx hbad
    let d := (splitScorePairs μ x).1
    let xm (i : Fin n) := maleSpouseScore x μ i
    let yf := femaleSpouseByHusband μ x
    have hm (i : Fin n) : (diagonalPairAt d i).1 = xm i :=
      congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)
    have hf (i : Fin n) : (diagonalPairAt d i).2 = yf i := by
      simp only [d, diagonalPairAt_splitScorePairs, yf, femaleSpouseByHusband, femaleSpouseScore,
        Equiv.symm_apply_apply]
    have hY : pivotDiagonalFemaleTotal d = spouseVectorTotal yf :=
      Finset.sum_congr rfl fun i _ ↦ hf i
    have hY' : spouseVectorTotal yf = femaleSpouseTotal x μ :=
      (femaleSpouseTotal_eq_sum_byHusband μ x).symm
    have hw (i : Fin n) : forwardSpouseWeight d i = spouseAngle yf i := by
      change (diagonalPairAt d i).2 / pivotDiagonalFemaleTotal d = yf i / spouseVectorTotal yf
      rw [hf i, hY]
    have hy (i : Fin n) : yf i ∈ Ioo (0 : ℝ) 1 :=
      hx (.inr (μ i)) (μ.symm (μ i))
    by_cases hsmall : femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hbad.1, hsmall⟩)))
    have hlarge : 2 ≤ femaleSpouseTotal x μ := hlog.trans (le_of_not_gt hsmall)
    by_cases hshare : ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤
        12 * Real.log n / n
    · by_cases hmale : ∀ i, maleSpouseScore x μ i ≤
          8 * Real.log n / (femaleSpouseTotal x μ - 1)
      · by_cases hsquare : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ)
        · by_cases hend : forwardWeightedEndpointError xm yf ≤ (n : ℝ) ^ (-3 / 4 : ℝ)
          · exfalso
            apply hbad.2
            refine ⟨(mem_goodDiagonalScores_iff x μ).mpr ⟨hlarge, hshare, hmale⟩,
              ?_, ?_, ?_, hsquare, ?_⟩
            · intro i
              rw [hm i]
              exact ⟨(hx (.inl i) (μ i)).1.le, (hx (.inl i) (μ i)).2⟩
            · intro i
              rw [hf i]
              exact ⟨(hy i).1.le, (hy i).2.le⟩
            · rw [hY, hY']
              exact le_of_not_gt hsmall
            · change (∑ i, forwardSpouseWeight d i *
                  Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤ _
              simp_rw [hw, hm, hY]
              simpa only [forwardWeightedEndpointError, spouseAngle, spouseVectorTotal, neg_mul] using hend
          · exact Or.inr ⟨hbad.1, ⟨hY'.symm ▸ hlarge, hY'.symm ▸ le_of_not_gt hsmall,
              fun i ↦ by rw [hY']; exact hshare (μ i)⟩, lt_of_not_ge hend⟩
        · apply Or.inl
          apply Or.inr
          refine ⟨hbad.1, ?_⟩
          have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
          have h := (div_lt_iff₀ hn₀).mp (lt_of_not_ge hsquare)
          simpa only [largeSpouseAngularSquareSet, mem_ofPred_eq, pittelAngularSquareScore, hw,
            mul_comm] using h
      · obtain ⟨i, hi⟩ := not_forall.mp hmale
        exact Or.inl (Or.inl (Or.inr ⟨hbad.1, hlarge, i, lt_of_not_ge hi⟩))
    · obtain ⟨j, hj⟩ := not_forall.mp hshare
      have htotal : spouseVectorTotal yf ≤ (n : ℝ) := by
        calc
          _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (hy i).2.le
          _ = _ := by simp
      refine Or.inl (Or.inl (Or.inl (Or.inr ⟨hbad.1, fun i ↦ (hy i).1.le, hY'.symm ▸ hlarge,
        htotal, μ.symm j, ?_⟩)))
      change 12 * Real.log n / n < yf (μ.symm j) / spouseVectorTotal yf
      rw [hY']
      simpa only [yf, femaleSpouseByHusband, Equiv.apply_symm_apply] using lt_of_not_ge hj
  calc
    _ ≤ continuousScoreLaw n exceptions := measure_mono_ae hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)) le_rfl)

private theorem neg_four_rpow_eq_inv {z : ℝ} (hz : 0 ≤ z) :
    z ^ (-4 : ℝ) = (z ^ (4 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hz, Real.rpow_ofNat]

private theorem eventually_sum_badSingletonRelativeShare_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badSingletonRelativeShare μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-4 : ℝ)) := by
  have hexp : ∀ᶠ n : ℕ in atTop, Real.exp (5 / 2 : ℝ) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds, hexp,
    eventually_ge_atTop (2 : ℕ)] with n h he hn
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr h.1
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith only [hn₂])
  have hcut : 12 * Real.log n / (n : ℝ) ≤ 1 := by
    linarith only [h.2.2.2.2.1, div_nonneg hnlog hn₀.le,
      show 24 * Real.log n / (n : ℝ) = 2 * (12 * Real.log n / (n : ℝ)) by ring]
  refine (sum_stable_largeRelativeSpouseScore_le h.1 hcut).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [neg_four_rpow_eq_inv hn₀.le]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ (12 : ℕ))).mpr
  have hcube : (n : ℝ) ^ 2 + 1 ≤ (n : ℝ) ^ 3 := by
    nlinarith only [hn₂, mul_nonneg (sub_nonneg.mpr hn₂) (sq_nonneg (n : ℝ))]
  calc
    _ ≤ ((n : ℝ) ^ 3 * n) * n := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcube hn₀.le) he
        (Real.exp_nonneg _) (by positivity)
    _ = (n : ℝ) ^ 5 := by ring
    _ ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith only [hn₂]) (by norm_num)
    _ = _ := by field_simp

private theorem eventually_sum_badSingletonMaleScore_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ)) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-4 : ℝ)) := by
  filter_upwards [eventually_expectedNumStableMatchings_le_sizeLog,
    eventually_ge_atTop (8 : ℕ)] with n hmean hn
  have hn₈ : 8 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₈]
  have hlog : Real.log (n : ℝ) ≤ n :=
    (Real.log_le_sub_one_of_pos hn₀).trans (by linarith only)
  have hmean' : expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
    simpa only [sq] using hmean.trans (mul_le_mul_of_nonneg_left hlog hn₀.le)
  calc
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 7) * ENNReal.ofReal (expectedNumStableMatchings n) :=
      sum_measure_badMaleSpouseScores_le (Nat.cast_pos.mp hn₀)
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 7) * ENNReal.ofReal ((n : ℝ) ^ 2) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hmean')
    _ = ENNReal.ofReal ((8 / (n : ℝ) ^ 7) * (n : ℝ) ^ 2) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      rw [neg_four_rpow_eq_inv hn₀.le, div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) ^ (7 : ℕ))).mpr
      calc
        _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hn₈ (sq_nonneg _)
        _ = _ := by field_simp)

/-- The expected number of stable marks with a bad local diagonal is at most
the inverse cube of market size for all sufficiently large markets. -/
theorem eventually_sum_measure_badSingletonLengthDiagonal_le :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ ∧
        (splitScorePairs μ x).1 ∉ singletonLengthGoodDiagonal n}) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le 4,
    eventually_sum_badSingletonRelativeShare_le, eventually_sum_badSingletonMaleScore_le,
    eventually_sum_measure_badFemaleSpouseSquareMark_le 4 (by norm_num),
    eventually_sum_measure_badForwardEndpointMark_le 4, hlog, eventually_ge_atTop (5 : ℕ)]
    with n hsmall hshare hmale hsq hend hlog hn
  have hn₅ : 5 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₅]
  let a := (n : ℝ) ^ (-4 : ℝ)
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (badSingletonSmallTotal μ) +
          continuousScoreLaw n (badSingletonRelativeShare μ) +
          continuousScoreLaw n (badMaleSpouseScores μ) +
          continuousScoreLaw n (badFemaleSpouseSquareMark μ) +
          continuousScoreLaw n (badForwardEndpointMark μ)) :=
      Finset.sum_le_sum fun μ _ ↦ measure_badSingletonLengthDiagonal_le
        (Nat.cast_pos.mp hn₀) hlog μ
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a + ENNReal.ofReal a +
        ENNReal.ofReal a + ENNReal.ofReal a := by
      simp only [Finset.sum_add_distrib]
      exact add_le_add (add_le_add (add_le_add (add_le_add hsmall hshare) hmale) hsq) hend
    _ = ENNReal.ofReal (5 * a) := by
      repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (calc
      5 * a ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₅ ha
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -4 = -3 by norm_num])

end LennonPittelFormalization

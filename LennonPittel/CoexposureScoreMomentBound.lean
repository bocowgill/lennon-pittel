module

public import LennonPittel.CoexposureGoodScores
public import LennonPittel.CoexposureScoreProduct
public import LennonPittel.CoexposureScoreRow
public import LennonPittel.CoexposureCycleMoment
public import LennonPittel.CoexposureGaussianSum
public import LennonPittel.CoexposureScoreEstimates

/-!
# The weighted moment for good stable score profiles

The stable cells of a fixed matching form independent unnormalized rows.
The diagonal cutoffs bound the successor marginals in these rows.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The male spouse score at a diagonal entry. -/
def diagonalMale {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).1

/-- The female spouse score at a diagonal entry. -/
def diagonalFemale {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2

/-- The sum of the female spouse scores. -/
def diagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ j, diagonalFemale d j

/-- The spouse-score cutoffs expressed on diagonal data indexed by husbands. -/
def goodDiagonalScores (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | 2 ≤ diagonalFemaleTotal d ∧
    (∀ j, diagonalFemale d j / diagonalFemaleTotal d ≤ 12 * Real.log n / n) ∧
    (∀ i, diagonalMale d i ≤ 8 * Real.log n / (diagonalFemaleTotal d - 1))}

/-- Reindexing by husbands preserves each of the three spouse cutoffs. -/
theorem mem_goodDiagonalScores_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    (splitScorePairs μ x).1 ∈ goodDiagonalScores n ↔ GoodSpouseScores x μ := by
  have hy (j : Fin n) : diagonalFemale (splitScorePairs μ x).1 j =
      femaleSpouseScore x μ (μ j) := by
    simp [diagonalFemale, diagonalPairAt_splitScorePairs, femaleSpouseScore]
  have hs : diagonalFemaleTotal (splitScorePairs μ x).1 = femaleSpouseTotal x μ := by
    simp only [diagonalFemaleTotal, hy, femaleSpouseTotal]
    exact Equiv.sum_comp μ (fun j ↦ x (.inr j) (μ.symm j))
  have hall : (∀ j, femaleSpouseScore x μ (μ j) / femaleSpouseTotal x μ ≤
      12 * Real.log n / n) ↔
      ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 12 * Real.log n / n :=
    ⟨fun h j ↦ by simpa only [Equiv.apply_symm_apply] using h (μ.symm j),
      fun h j ↦ h (μ j)⟩
  simp only [goodDiagonalScores, mem_ofPred_eq, GoodSpouseScores, hs, hy, diagonalMale,
    diagonalPairAt_splitScorePairs, maleSpouseScore, hall]

/-- The diagonal score cutoffs are measurable. -/
theorem measurableSet_goodDiagonalScores (n : ℕ) : MeasurableSet (goodDiagonalScores n) := by
  have hm (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ diagonalMale d i) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hf (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ diagonalFemale d i) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hs : Measurable (fun d : DiagonalScorePairs n ↦ diagonalFemaleTotal d) :=
    Finset.measurable_sum _ fun i _ ↦ hf i
  unfold goodDiagonalScores
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const hs).inter
    ((MeasurableSet.iInter fun j ↦ measurableSet_le ((hf j).div hs) measurable_const).inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le (hm i)
        (measurable_const.div (hs.sub measurable_const))))

private theorem diagonal_good_product_le {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n) (hx : ∀ i, 0 ≤ diagonalMale d i)
    (hy : ∀ j, 0 ≤ diagonalFemale d j) (i j : Fin n) :
    diagonalMale d i * diagonalFemale d j ≤ 192 * (Real.log n) ^ 2 / n := by
  let s := diagonalFemaleTotal d
  have hs : 2 ≤ s := hg.1
  have hspos : 0 < s := by linarith
  have hsone : 0 < s - 1 := by linarith
  have hscale : s / (s - 1) ≤ 2 := (div_le_iff₀ hsone).2 (by linarith)
  calc
    diagonalMale d i * diagonalFemale d j =
        (diagonalMale d i * (diagonalFemale d j / s)) * s := by
          rw [mul_assoc, div_mul_cancel₀ _ hspos.ne']
    _ ≤ (8 * Real.log n / (s - 1) * (12 * Real.log n / n)) * s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hg.2.2 i) (hg.2.1 j) (div_nonneg (hy j) hspos.le)
          ((hx i).trans (hg.2.2 i))) hspos.le
    _ = (96 * (Real.log n) ^ 2 / n) * (s / (s - 1)) := by ring
    _ ≤ (96 * (Real.log n) ^ 2 / n) * 2 := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

private theorem diagonal_competitor_sum {n : ℕ} (y : Fin n → ℝ)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val) =
      (∑ k, y k) - y i - y j.val := by
  classical
  have houter : (∑ k : {k : Fin n // i ≠ k}, y k.val) = (∑ k, y k) - y i := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp [ne_comm]) y]
    linarith [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]
  let f := fun k : {k : Fin n // i ≠ k} ↦ y k.val
  change (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, f k.val) =
    (∑ k, y k) - y i - f j
  rw [← Finset.sum_subtype (Finset.univ.erase j) (by simp) f]
  linarith [Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)]

private theorem diagonal_arc_bound {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n) (hx : ∀ i, 0 ≤ diagonalMale d i)
    (hy : ∀ j, 0 ≤ diagonalFemale d j)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i j : Fin n) :
    0 < diagonalFemaleTotal d - diagonalFemale d i - diagonalFemale d j ∧
      diagonalFemale d j / ((1 - diagonalMale d i * diagonalFemale d j) *
        (diagonalFemaleTotal d - diagonalFemale d i - diagonalFemale d j)) ≤
      (1 + coexposureSuccessorPerturbation n) * (diagonalFemale d j / diagonalFemaleTotal d) := by
  let s := diagonalFemaleTotal d
  let v := diagonalFemale d j
  let a := 1 - diagonalMale d i * v
  let b := s - diagonalFemale d i - v
  have hs : 0 < s := by linarith [show 2 ≤ s from hg.1]
  have ha : 1 - 192 * (Real.log n) ^ 2 / n ≤ a := by
    linarith only [diagonal_good_product_le hg hx hy i j]
  have hapos := hA.trans_le ha
  have hb : 1 - 24 * Real.log n / n ≤ b / s := by
    dsimp only [b, v]
    rw [sub_div, sub_div, div_self hs.ne']
    have hi := hg.2.1 i
    have hj := hg.2.1 j
    change diagonalFemale d i / s ≤ 12 * Real.log n / n at hi
    change diagonalFemale d j / s ≤ 12 * Real.log n / n at hj
    linarith only [hi, hj, show (24 : ℝ) * Real.log n / n =
      12 * Real.log n / n + 12 * Real.log n / n by ring]
  have hbpos : 0 < b := (div_pos_iff_of_pos_right hs).mp (hB.trans_le hb)
  refine ⟨hbpos, ?_⟩
  change v / (a * b) ≤ (1 + coexposureSuccessorPerturbation n) * (v / s)
  calc
    _ = (a⁻¹ * (b / s)⁻¹) * (v / s) := by
      field_simp [hapos.ne', hbpos.ne', hs.ne']
    _ ≤ ((1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹) * (v / s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (inv_anti₀ hA ha) (inv_anti₀ hB hb)
          (inv_nonneg.mpr (div_nonneg hbpos.le hs.le)) (inv_nonneg.mpr hA.le))
        (div_nonneg (hy j) hs.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hδ (div_nonneg (hy j) hs.le)

/-- The good diagonal bounds each arc by its female share times the
forward perturbation, with the unnormalized row mass kept explicit. -/
theorem stableScoreRowLaw_successor_le_of_goodDiagonalScores {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ j, (diagonalPairAt d j).2 ∈ Icc 0 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) ≤ stableScoreRowLaw d i univ *
      ENNReal.ofReal ((1 + coexposureSuccessorPerturbation n) *
        ((diagonalPairAt d j.val).2 / ∑ k, (diagonalPairAt d k).2)) := by
  have hsum := diagonal_competitor_sum (diagonalFemale d) i j
  have harc := diagonal_arc_bound hg (fun k ↦ (hx k).1) (fun k ↦ (hy k).1) hA hB hδ i j.val
  have hsum_pos : 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
      (diagonalPairAt d k.val.val).2 := by
    change 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, diagonalFemale d k.val.val
    rw [hsum]
    exact harc.1
  refine (stableScoreRowLaw_successor_le d i j (hx i) hy hsum_pos).trans ?_
  gcongr
  change diagonalFemale d j.val / ((1 - diagonalMale d i * diagonalFemale d j.val) *
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, diagonalFemale d k.val.val)) ≤ _
  rw [hsum]
  exact harc.2

private theorem ae_diagonalMale_mem_Ico (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, diagonalMale d i ∈ Ico (0 : ℝ) 1 := by
  have hne : ∀ᵐ t ∂unitScoreLaw, t ≠ (1 : ℝ) := by
    rw [ae_iff]
    simp
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1)), hne] with t ht hne
    exact ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Ico (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i,i), rfl⟩)).eventually hp

private theorem lintegral_diagonal_exposure_le {n : ℕ} (hn : 0 < n) (μ : Matching n)
    {d : DiagonalScorePairs n} (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, diagonalMale d i ∈ Ico (0 : ℝ) 1)
    (hy : ∀ j, diagonalFemale d j ∈ Icc (0 : ℝ) 1)
    (hδ₀ : 0 ≤ coexposureSuccessorPerturbation n)
    (hδsmall : coexposureSuccessorPerturbation n ≤ 1 / Real.sqrt (n : ℝ))
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n)
    (hrow : ∀ᵐ r ∂Measure.pi (stableScoreRowLaw d),
      let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ) :
    (∫⁻ r, (2 : ℝ≥0∞) ^ numExposedRotations
      (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ
        ∂(Measure.pi (stableScoreRowLaw d))) ≤
      (∏ i, stableScoreRowLaw d i univ) *
        ENNReal.ofReal (2 * Real.exp ((1 + 3 / 2) ^ 2 / 2) * Real.sqrt (n : ℝ)) := by
  classical
  let P := fun r : OffDiagonalScoreRows n ↦
    profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))
  let T := fun (i j : Fin n) ↦ if hij : i ≠ j then scoreRowSuccessorEvent d i ⟨j, hij⟩ else ∅
  let w := fun j ↦ diagonalFemale d j / diagonalFemaleTotal d
  have hs : 0 < diagonalFemaleTotal d := by linarith [hg.1]
  have hw₀ (j : Fin n) : 0 ≤ w j := div_nonneg (hy j).1 hs.le
  have hw : ∑ j, w j = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self hs.ne'
  have hP : Measurable P :=
    (measurable_profileOfScores n).comp ((splitScorePairs μ).symm.measurable.comp
      (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
  have hvalid : ∀ᵐ r ∂Measure.pi (stableScoreRowLaw d), ∀ i j,
      IsSuccessor (P r) μ i (μ j) → r i ∈ T i j := by
    filter_upwards [hrow] with r hr i j hj
    have hij : i ≠ j := fun h ↦ (lt_irrefl _) (h ▸ hj.eligible.1)
    simpa only [T, dite_eq_left hij] using
      scoreRowSuccessorEvent_of_isSuccessor_reconstructed μ d r i ⟨j, hij⟩ hr.2 hr.1 hj
  have hmarg (i j : Fin n) (hij : i ≠ j) :
      stableScoreRowLaw d i (T i j) ≤ stableScoreRowLaw d i univ *
        (ENNReal.ofReal (1 + coexposureSuccessorPerturbation n) * ENNReal.ofReal (w j)) := by
    rw [show T i j = scoreRowSuccessorEvent d i ⟨j, hij⟩ by simp only [T, dite_eq_left hij],
      ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + coexposureSuccessorPerturbation n)]
    exact stableScoreRowLaw_successor_le_of_goodDiagonalScores hg hx hy hA hB hδ i ⟨j, hij⟩
  refine (lintegral_pow_numExposedRotations_le_of_pi (stableScoreRowLaw d) P hP μ T _ _
    hvalid hmarg).trans ?_
  gcongr
  exact coexposure_weighted_powerset_sum_le_sqrt_ennreal hn hw₀ hw hδ₀ hδsmall

private theorem stableMass_eq_lintegral_rowMass {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ} =
      ∫⁻ d, (∏ i, stableScoreRowLaw d i univ) ∂diagonalScoreLaw n := by
  have h := continuousScoreLaw_lintegral_stable_and_diagonal_rows μ
    (C := univ) MeasurableSet.univ (f := fun _ ↦ 1) measurable_const
  simpa only [mem_univ, and_true, Measure.restrict_univ, lintegral_one,
    Measure.restrict_apply_univ, Measure.pi_univ] using h

/-- The weighted stable-matching moment has the sharp square-root factor for
the concrete all-good score event. -/
theorem eventually_lintegral_goodScoreCoexposureWeight_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫⁻ x, scoreCoexposureWeight n (goodCoexposureScores n) x ∂(continuousScoreLaw n)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (1 / 2 : ℝ) * expectedNumStableMatchings n) := by
  let C : ℝ := 2 * Real.exp ((1 + 3 / 2) ^ 2 / 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds] with n hn
  rcases hn with ⟨hn, hδ₀, hδsmall, hA, hB, hδ⟩
  rw [← Real.sqrt_eq_rpow, ENNReal.ofReal_mul (show 0 ≤ C * Real.sqrt (n : ℝ) by
    dsimp [C]; positivity)]
  let L := ENNReal.ofReal (C * Real.sqrt (n : ℝ))
  refine lintegral_goodScoreCoexposureWeight_le_of_fixed_moment (L := L) ?_
  intro μ
  have hweight : Measurable
      (fun x : ScoreProfile n ↦ (2 : ℝ≥0∞) ^ numExposedRotations (profileOfScores x) μ) :=
    (show Measurable (fun p : Profile n ↦ (2 : ℝ≥0∞) ^ numExposedRotations p μ) from
      fun _ _ ↦ MeasurableSpace.measurableSet_top).comp (measurable_profileOfScores n)
  rw [show {x : ScoreProfile n | IsScoreStable x μ ∧ GoodSpouseScores x μ} =
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ goodDiagonalScores n} by
        ext x; exact and_congr_right fun _ ↦ (mem_goodDiagonalScores_iff x μ).symm,
    continuousScoreLaw_lintegral_stable_and_diagonal_rows μ
      (measurableSet_goodDiagonalScores n) hweight, stableMass_eq_lintegral_rowMass μ]
  calc
    _ ≤ ∫⁻ d in goodDiagonalScores n, (∏ i, stableScoreRowLaw d i univ) * L
        ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_goodDiagonalScores n),
        ae_restrict_of_ae (ae_diagonalMale_mem_Ico n),
        ae_restrict_of_ae (ae_diagonalPairAt_mem_Icc n),
        ae_restrict_of_ae (ae_diagonal_ae_stableRows μ)] with d hd hx hy hr
      exact lintegral_diagonal_exposure_le hn μ hd hx (fun j ↦ (hy j).2)
        hδ₀ hδsmall hA hB hδ hr
    _ = (∫⁻ d in goodDiagonalScores n, ∏ i, stableScoreRowLaw d i univ ∂diagonalScoreLaw n) *
        L := lintegral_mul_const' L _ ENNReal.ofReal_ne_top
    _ ≤ (∫⁻ d, ∏ i, stableScoreRowLaw d i univ ∂diagonalScoreLaw n) * L := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := mul_comm _ _

end LennonPittelFormalization

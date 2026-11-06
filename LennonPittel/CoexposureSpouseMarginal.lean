module

public import LennonPittel.CoexposureScoreProduct
public import LennonPittel.CoexposureScoreRow
public import LennonPittel.CoexposureGoodScores
public import Mathlib.Probability.Independence.Integration

/-!
# Spouse-score marginals of a fixed stable matching

Integrating over the male spouse scores turns the off-diagonal stability
product into a product of one-dimensional row integrals.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The common product law of a vector of spouse scores. -/
noncomputable def spouseVectorLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ unitScoreLaw

instance (n : ℕ) : IsProbabilityMeasure (spouseVectorLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ unitScoreLaw))

/-- The independent unit scores have Lebesgue measure restricted to the unit cube. -/
theorem spouseVectorLaw_eq_restrict_volume (n : ℕ) :
    spouseVectorLaw n =
      (volume : Measure (Fin n → ℝ)).restrict (univ.pi fun _ ↦ Icc (0 : ℝ) 1) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

/-- The independent unit-score law is bounded by Lebesgue measure. -/
theorem spouseVectorLaw_le_volume (n : ℕ) :
    spouseVectorLaw n ≤ (volume : Measure (Fin n → ℝ)) := by
  rw [spouseVectorLaw_eq_restrict_volume]
  exact Measure.restrict_le_self

/-- The woman's spouse score, indexed by her husband in the fixed matching. -/
def femaleSpouseByHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) : Fin n → ℝ :=
  fun j ↦ femaleSpouseScore x μ (μ j)

/-- The product of the integrated stability factors at a female spouse-score vector. -/
noncomputable def femaleSpouseStabilityDensity {n : ℕ} (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1)

theorem measurable_femaleSpouseStabilityDensity (n : ℕ) :
    Measurable (@femaleSpouseStabilityDensity n) := by
  unfold femaleSpouseStabilityDensity
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  have h : Measurable (fun z : (Fin n → ℝ) × ℝ ↦
      scoreRowKernel (Finset.univ.erase i) z.1 z.2) := by
    unfold scoreRowKernel
    refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
    exact measurable_snd.mul ((measurable_pi_apply j).comp measurable_fst)
  convert (h.stronglyMeasurable.integral_prod_right' (ν := unitScoreLaw)).measurable using 1
  funext y
  rw [unitScoreLaw, scoreRowMass, intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc.symm

private def spouseVectors {n : ℕ} (d : DiagonalScorePairs n) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i ↦ (diagonalPairAt d i).1, fun i ↦ (diagonalPairAt d i).2)

/-- The pointwise product of all stability rows, before integrating the male scores. -/
noncomputable def spouseStabilityKernel {n : ℕ}
    (x y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i : Fin n, ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y (x i))

private theorem measurable_spouseStabilityKernel (n : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ spouseStabilityKernel z.1 z.2) := by
  unfold spouseStabilityKernel scoreRowKernel
  refine Finset.measurable_prod _ fun i _ ↦ Measurable.ennreal_ofReal ?_
  refine Finset.measurable_prod _ fun j _ ↦ measurable_const.sub ?_
  exact ((measurable_pi_apply i).comp measurable_fst).mul
    ((measurable_pi_apply j).comp measurable_snd)

private theorem ae_spouseVectorLaw_mem_Icc (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ j, y j ∈ Icc (0 : ℝ) 1 :=
  ae_all_iff.2 fun j ↦
    let h := measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) j
    h.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)

private def offDiagonalSigmaEquiv (n : ℕ) :
    {q : ScorePairIndex n // q.1 ≠ q.2} ≃ (i : Fin n) × {j : Fin n // i ≠ j} where
  toFun q := ⟨q.val.1, ⟨q.val.2, q.property⟩⟩
  invFun q := ⟨(q.1,q.2.val),q.2.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

private theorem spouseStabilityKernel_eq {n : ℕ} {x y : Fin n → ℝ}
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    spouseStabilityKernel x y = ∏ q : {q : ScorePairIndex n // q.1 ≠ q.2},
      ENNReal.ofReal (1 - x q.val.1 * y q.val.2) := by
  classical
  unfold spouseStabilityKernel scoreRowKernel
  trans ∏ i : Fin n, ∏ j : {j : Fin n // i ≠ j}, ENNReal.ofReal (1 - x i * y j.val)
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [ENNReal.ofReal_prod_of_nonneg]
    · exact Finset.prod_subtype _ (by simp [ne_comm])
        (fun j ↦ ENNReal.ofReal (1 - x i * y j))
    · intro j _
      exact sub_nonneg.mpr
        ((mul_le_mul_of_nonneg_right (hx i).2 (hy j).1).trans (by simpa using (hy j).2))
  · rw [← Fintype.prod_sigma']
    exact Fintype.prod_equiv (offDiagonalSigmaEquiv n).symm _ _ fun _ ↦ rfl

/-- Integrating a stability row over its uniform male spouse score gives its row mass. -/
theorem lintegral_scoreRowKernel_unitScoreLaw {n : ℕ} (J : Finset (Fin n))
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, ENNReal.ofReal (scoreRowKernel J y x) ∂unitScoreLaw) =
      ENNReal.ofReal (scoreRowMass J y 0 1) := by
  have hint : Integrable (scoreRowKernel J y) unitScoreLaw :=
    (continuous_scoreRowKernel J y).integrableOn_Icc
  have hnn : 0 ≤ᵐ[unitScoreLaw] scoreRowKernel J y := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1))] with x hx
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right hx.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [unitScoreLaw, scoreRowMass, intervalIntegral.integral_of_le (by norm_num)]
  exact integral_Icc_eq_integral_Ioc

private theorem lintegral_spouseStabilityKernel {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x, spouseStabilityKernel x y ∂spouseVectorLaw n) = femaleSpouseStabilityDensity y := by
  let f (i : Fin n) (x : ℝ) := ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y x)
  have hf (i : Fin n) : Measurable (f i) :=
    (continuous_scoreRowKernel _ _).measurable.ennreal_ofReal
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ unitScoreLaw)
    (X := f) (fun i ↦ (hf i).aemeasurable)
  calc
    _ = ∏ i : Fin n, ∫⁻ x, f i (x i) ∂spouseVectorLaw n :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hi
        (fun i ↦ (hf i).comp (measurable_pi_apply i))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      exact ((measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).lintegral_comp
        (hf i)).trans (lintegral_scoreRowKernel_unitScoreLaw _ y hy)

/-- The female stability density is at most one on the unit cube. -/
theorem femaleSpouseStabilityDensity_le_one {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    femaleSpouseStabilityDensity y ≤ 1 := by
  rw [← lintegral_spouseStabilityKernel y hy]
  have hone : (∫⁻ _x, 1 ∂spouseVectorLaw n) = 1 := by simp
  rw [← hone]
  apply lintegral_mono_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with x hx
  rw [spouseStabilityKernel_eq hx hy]
  calc
    _ ≤ ∏ _q : {q : ScorePairIndex n // q.1 ≠ q.2}, (1 : ℝ≥0∞) := by
      refine Finset.prod_le_prod fun q _ ↦ ?_
      rw [ENNReal.ofReal_le_one]
      exact sub_le_self _ (mul_nonneg (hx q.val.1).1 (hy q.val.2).1)
    _ = _ := Finset.prod_const_one

/-- The joint spouse-score marginal of fixed-matching stability, in row-product form. -/
theorem continuousScoreLaw_stable_and_spouseVectors {n : ℕ} (μ : Matching n)
    {B : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hB : MeasurableSet B) :
    continuousScoreLaw n
        {x | IsScoreStable x μ ∧
          ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} =
      ∫⁻ z, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) z
        ∂((spouseVectorLaw n).prod (spouseVectorLaw n)) := by
  have hv : MeasurePreserving (@spouseVectors n) (diagonalScoreLaw n)
      ((spouseVectorLaw n).prod (spouseVectorLaw n)) :=
    measurePreserving_diagonalScoreVectors n
  have hvec (x : ScoreProfile n) : spouseVectors (splitScorePairs μ x).1 =
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) := by
    apply Prod.ext <;> funext i
    · simp only [spouseVectors, diagonalPairAt_splitScorePairs, maleSpouseScore]
    · simp only [spouseVectors, diagonalPairAt_splitScorePairs, femaleSpouseByHusband,
        femaleSpouseScore, Equiv.symm_apply_apply]
  have hcut : MeasurableSet (spouseVectors ⁻¹' B) := hB.preimage hv.measurable
  have he : {x | IsScoreStable x μ ∧
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ B} =
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ spouseVectors ⁻¹' B} := by
    ext x
    simp [hvec]
  rw [he, continuousScoreLaw_stable_and_diagonal_prod μ hcut,
    ← hv.lintegral_comp ((measurable_spouseStabilityKernel n).indicator hB)]
  apply lintegral_congr_ae
  filter_upwards [ae_diagonalPairAt_mem_Icc n] with d hd
  by_cases h : spouseVectors d ∈ B
  · rw [indicator_of_mem (show d ∈ spouseVectors ⁻¹' B from h), indicator_of_mem h]
    exact (spouseStabilityKernel_eq (fun i ↦ (hd i).1) (fun i ↦ (hd i).2)).symm
  · rw [indicator_of_notMem (show d ∉ spouseVectors ⁻¹' B from h), indicator_of_notMem h]

/-- A female-spouse cutoff at a fixed stable matching integrates the female stability density. -/
theorem continuousScoreLaw_stable_and_femaleSpouse {n : ℕ} (μ : Matching n)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} =
      ∫⁻ y in B, femaleSpouseStabilityDensity y ∂spouseVectorLaw n := by
  rw [show {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B} =
    {x | IsScoreStable x μ ∧
      ((fun i ↦ maleSpouseScore x μ i), femaleSpouseByHusband μ x) ∈ Prod.snd ⁻¹' B} from rfl,
    continuousScoreLaw_stable_and_spouseVectors μ (hB.preimage measurable_snd),
    lintegral_prod_symm' _ ((measurable_spouseStabilityKernel n).indicator
      (hB.preimage measurable_snd)), ← lintegral_indicator hB]
  apply lintegral_congr_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with y hy
  by_cases h : y ∈ B
  · rw [indicator_of_mem h, ← lintegral_spouseStabilityKernel y hy]
    exact lintegral_congr fun x ↦ indicator_of_mem h _
  · rw [indicator_of_notMem h, ← lintegral_zero]
    exact lintegral_congr fun x ↦ indicator_of_notMem h _

private theorem lintegral_prod_spouseVectorLaw {n : ℕ} (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i : Fin n, f i (x i) ∂spouseVectorLaw n) =
      ∏ i : Fin n, ∫⁻ t, f i t ∂unitScoreLaw := by
  have hi := iIndepFun_pi (μ := fun _ : Fin n ↦ unitScoreLaw)
    (X := f) (fun i ↦ (hf i).aemeasurable)
  calc
    _ = ∏ i : Fin n, ∫⁻ x, f i (x i) ∂spouseVectorLaw n :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hi
        (fun i ↦ (hf i).comp (measurable_pi_apply i))
    _ = _ := Finset.prod_congr rfl fun i _ ↦
      (measurePreserving_eval (fun _ : Fin n ↦ unitScoreLaw) i).lintegral_comp (hf i)

private theorem lintegral_scoreRowKernel_tail {n : ℕ} (J : Finset (Fin n))
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (scoreRowKernel J y t) ∂unitScoreLaw) =
      ENNReal.ofReal (scoreRowMass J y a 1) := by
  rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi,
    show Ioi a ∩ Icc (0 : ℝ) 1 = Ioc a 1 by
      ext t
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ha.trans h.1.le, h.2⟩⟩]
  have hint : IntegrableOn (scoreRowKernel J y) (Ioc a 1) :=
    ((continuous_scoreRowKernel J y).intervalIntegrable a 1).1
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a 1)] scoreRowKernel J y := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc :
      MeasurableSet (Ioc a 1))] with t ht
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right ht.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [scoreRowMass, intervalIntegral.integral_of_le ha']

private theorem lintegral_scoreRowKernel_tail_le {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j)
    (i : Fin n) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (scoreRowKernel (Finset.univ.erase i) y t)
        ∂unitScoreLaw) ≤ ENNReal.ofReal (8 * Real.exp (-((∑ j, y j) - 1) * a)) *
      ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1) := by
  by_cases ha' : a ≤ 1
  · rw [lintegral_scoreRowKernel_tail _ y hy ha ha', ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ?_).mp (scoreRowMass_erase_div_le_exp_tail y i hy hs ha ha')
    have hsum : ∑ j ∈ Finset.univ.erase i, y j ≤ ∑ j, y j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ ↦ (hy j).1
    exact (by positivity : 0 < 1 / (4 * ∑ j, y j)).trans_le
      (scoreRowMass_lower (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
        ((by norm_num : (1 : ℝ) ≤ 2).trans hs) hsum)
  · have hz : unitScoreLaw.restrict (Ioi a) = 0 := by
      rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
      suffices Ioi a ∩ Icc (0 : ℝ) 1 = ∅ by rw [this, Measure.restrict_empty]
      refine Set.eq_empty_iff_forall_notMem.mpr fun t ht ↦ ha' ?_
      exact ht.1.le.trans ht.2.2
    rw [hz, lintegral_zero_measure]
    exact zero_le

private theorem lintegral_spouseStabilityKernel_tail_le {n : ℕ}
    (y : Fin n → ℝ) (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1)
    (hs : 2 ≤ ∑ j, y j) (i : Fin n) {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ x, {x : Fin n → ℝ | a < x i}.indicator
        (fun x ↦ spouseStabilityKernel x y) x ∂spouseVectorLaw n) ≤
      ENNReal.ofReal (8 * Real.exp (-((∑ j, y j) - 1) * a)) * femaleSpouseStabilityDensity y := by
  classical
  let f (j : Fin n) (t : ℝ) : ℝ≥0∞ :=
    if j = i then (Ioi a).indicator
      (fun t ↦ ENNReal.ofReal (scoreRowKernel (Finset.univ.erase j) y t)) t
    else ENNReal.ofReal (scoreRowKernel (Finset.univ.erase j) y t)
  have hf (j : Fin n) : Measurable (f j) := by
    by_cases h : j = i
    · simpa only [f, ite_eq_left h] using
        (continuous_scoreRowKernel (Finset.univ.erase j) y).measurable.ennreal_ofReal.indicator
          (measurableSet_Ioi (a := a))
    · simpa only [f, ite_eq_right h] using
        (continuous_scoreRowKernel (Finset.univ.erase j) y).measurable.ennreal_ofReal
  have heq (x : Fin n → ℝ) :
      {x : Fin n → ℝ | a < x i}.indicator (fun x ↦ spouseStabilityKernel x y) x =
        ∏ j : Fin n, f j (x j) := by
    by_cases hx : a < x i
    · rw [indicator_of_mem (show x ∈ {x : Fin n → ℝ | a < x i} from hx)]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      by_cases h : j = i
      · subst j
        simp [f, hx]
      · simp [f, h]
    · rw [indicator_of_notMem (show x ∉ {x : Fin n → ℝ | a < x i} from hx)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hx])).symm
  rw [lintegral_congr heq, lintegral_prod_spouseVectorLaw f hf,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hother : (∏ j ∈ Finset.univ.erase i, ∫⁻ t, f j t ∂unitScoreLaw) =
      ∏ j ∈ Finset.univ.erase i, ENNReal.ofReal
        (scoreRowMass (Finset.univ.erase j) y 0 1) := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    simpa only [f, ite_eq_right (Finset.mem_erase.mp hj).1] using
      lintegral_scoreRowKernel_unitScoreLaw (Finset.univ.erase j) y hy
  rw [hother]
  calc
    _ ≤ (∏ j ∈ Finset.univ.erase i, ENNReal.ofReal (scoreRowMass (Finset.univ.erase j) y 0 1)) *
        (ENNReal.ofReal (8 * Real.exp (-((∑ j, y j) - 1) * a)) *
          ENNReal.ofReal (scoreRowMass (Finset.univ.erase i) y 0 1)) := by
      gcongr
      simpa only [f, ite_eq_left rfl, lintegral_indicator measurableSet_Ioi] using
        lintegral_scoreRowKernel_tail_le y hy hs i ha
    _ = _ := by
      unfold femaleSpouseStabilityDensity
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      ac_rfl

/-- The total female spouse score is invariant under indexing by husbands. -/
theorem femaleSpouseTotal_eq_sum_byHusband {n : ℕ} (μ : Matching n) (x : ScoreProfile n) :
    femaleSpouseTotal x μ = ∑ j, femaleSpouseByHusband μ x j :=
  (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm

/-- One large male spouse score costs an exponentially small fraction of the stability mass. -/
theorem continuousScoreLaw_stable_and_maleSpouse_gt_le {n : ℕ} (μ : Matching n) (i : Fin n) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i} ≤
      ENNReal.ofReal (8 * Real.exp (-(8 * Real.log n))) *
        continuousScoreLaw n {x | IsScoreStable x μ} := by
  let a (y : Fin n → ℝ) := 8 * Real.log n / ((∑ j, y j) - 1)
  let B : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {z | 2 ≤ ∑ j, z.2 j ∧ a z.2 < z.1 i}
  have hB : MeasurableSet B := by
    have hsum : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ ∑ j, z.2 j) :=
      Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp measurable_snd
    have ha : Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ a z.2) :=
      measurable_const.div (hsum.sub measurable_const)
    exact (measurableSet_le measurable_const hsum).inter
      (measurableSet_lt ha ((measurable_pi_apply i).comp measurable_fst))
  have hcut : {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i} =
      {x | IsScoreStable x μ ∧
        ((fun j ↦ maleSpouseScore x μ j), femaleSpouseByHusband μ x) ∈ B} := by
    ext x
    simp [B, a, femaleSpouseTotal_eq_sum_byHusband]
  have hstable : continuousScoreLaw n {x | IsScoreStable x μ} =
      ∫⁻ y, femaleSpouseStabilityDensity y ∂spouseVectorLaw n := by
    simpa using continuousScoreLaw_stable_and_femaleSpouse μ (B := univ) MeasurableSet.univ
  rw [hcut, continuousScoreLaw_stable_and_spouseVectors μ hB,
    lintegral_prod_symm' _ ((measurable_spouseStabilityKernel n).indicator hB), hstable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_spouseVectorLaw_mem_Icc n] with y hy
  by_cases hs : 2 ≤ ∑ j, y j
  · have ha : 0 ≤ a y := div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n))
      (by linarith)
    have heq (x : Fin n → ℝ) :
        B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y) =
          {x : Fin n → ℝ | a y < x i}.indicator (fun x ↦ spouseStabilityKernel x y) x := by
      by_cases hx : a y < x i <;> simp [B, hs, hx]
    rw [lintegral_congr heq]
    have he : -((∑ j, y j) - 1) * a y = -(8 * Real.log n) := by
      dsimp [a]
      field_simp [show (∑ j, y j) - 1 ≠ 0 by linarith]
    simpa only [he] using lintegral_spouseStabilityKernel_tail_le y hy hs i ha
  · have hz : (∫⁻ x, B.indicator (fun z ↦ spouseStabilityKernel z.1 z.2) (x, y)
        ∂spouseVectorLaw n) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      exact Filter.Eventually.of_forall fun x ↦ indicator_of_notMem (fun h ↦ hs h.1) _
    rw [hz]
    exact zero_le

/-- A fixed matching is stable, has female total at least two, and fails the male cutoff. -/
def badMaleSpouseScores {n : ℕ} (μ : Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
    ∃ i, 8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i}

private theorem maleSpouseTailCoefficient_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) * ENNReal.ofReal (8 * Real.exp (-(8 * Real.log n))) =
      ENNReal.ofReal (8 / (n : ℝ) ^ 7) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), Real.exp_neg,
    show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hpos]
  congr 1
  rw [Nat.cast_ofNat, pow_succ]
  field_simp

/-- A union over the male rows costs at most `8 / n^7` of the stability mass. -/
theorem measure_badMaleSpouseScores_le {n : ℕ} (hn : 0 < n) (μ : Matching n) :
    continuousScoreLaw n (badMaleSpouseScores μ) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 7) * continuousScoreLaw n {x | IsScoreStable x μ} := by
  have he : badMaleSpouseScores μ = ⋃ i : Fin n,
      {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
        8 * Real.log n / (femaleSpouseTotal x μ - 1) < maleSpouseScore x μ i} := by
    ext x
    simp only [badMaleSpouseScores, mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨hst, hs, i, hi⟩ ↦ ⟨i, hst, hs, hi⟩,
      fun ⟨i, hst, hs, hi⟩ ↦ ⟨hst, hs, i, hi⟩⟩
  rw [he]
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (8 * Real.exp (-(8 * Real.log n))) *
        continuousScoreLaw n {x | IsScoreStable x μ} :=
      Finset.sum_le_sum fun i _ ↦ continuousScoreLaw_stable_and_maleSpouse_gt_le μ i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
      rw [maleSpouseTailCoefficient_eq hn]

/-- The sum of all fixed-matching stability probabilities is the expected stable count. -/
theorem sum_measure_scoreStable_eq_expected (n : ℕ) :
    (∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ}) =
      ENNReal.ofReal (expectedNumStableMatchings n) := by
  have hf (μ : Matching n) :
      Measurable ({x | IsScoreStable x μ}.indicator (1 : ScoreProfile n → ℝ≥0∞)) :=
    measurable_const.indicator (measurableSet_isScoreStable μ)
  calc
    _ = ∑ μ : Matching n, ∫⁻ x, {x | IsScoreStable x μ}.indicator 1 x ∂continuousScoreLaw n := by
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [lintegral_indicator_one (measurableSet_isScoreStable μ)]
    _ = ∫⁻ x, ∑ μ : Matching n, {x | IsScoreStable x μ}.indicator 1 x ∂continuousScoreLaw n :=
      (lintegral_finsetSum _ fun μ _ ↦ hf μ).symm
    _ = ∫⁻ x, ∑ μ : Matching n, (scoreMarkEvent n).indicator 1 (x, μ)
        ∂continuousScoreLaw n := by
      refine lintegral_congr fun x ↦ Finset.sum_congr rfl fun μ _ ↦ ?_
      by_cases h : IsScoreStable x μ <;> simp [scoreMarkEvent, h]
    _ = _ := by
      have hm : Measurable (1 : ScoreProfile n × Matching n → ℝ≥0∞) :=
        measurable_const
      simpa using (continuous_mark_counting_identity n hm).symm

/-- The expected count of male-cutoff failures is bounded by the mean count times `8/n^7`. -/
theorem sum_measure_badMaleSpouseScores_le {n : ℕ} (hn : 0 < n) :
    (∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 7) * ENNReal.ofReal (expectedNumStableMatchings n) := by
  calc
    _ ≤ ∑ μ : Matching n, ENNReal.ofReal (8 / (n : ℝ) ^ 7) *
        continuousScoreLaw n {x | IsScoreStable x μ} :=
      Finset.sum_le_sum fun μ _ ↦ measure_badMaleSpouseScores_le hn μ
    _ = _ := by rw [← Finset.mul_sum, sum_measure_scoreStable_eq_expected]

/-- A mean upper bound of order `n log n` makes the male-cutoff contribution vanish. -/
theorem tendsto_sum_measure_badMaleSpouseScores_zero_of_mean_upper {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ᶠ n : ℕ in atTop,
      expectedNumStableMatchings n ≤ C * ((n : ℝ) * Real.log n)) :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n (badMaleSpouseScores μ))
      atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (8 * C / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply, ← div_eq_mul_inv, mul_zero] using
      ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero.comp hcast).const_mul (8 * C))
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hmean] with n hn hm
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn'
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hp).trans (by linarith)
  have hm' : expectedNumStableMatchings n ≤ C * (n : ℝ) ^ 2 := by
    refine hm.trans ?_
    rw [sq]
    gcongr
  refine (sum_measure_badMaleSpouseScores_le (zero_lt_one.trans_le hn)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (8 / (n : ℝ) ^ 7) * (C * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hm' (by positivity)
    _ = (8 * C / (n : ℝ)) / ((n : ℝ) ^ 4) := by field_simp
    _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hn')

end LennonPittelFormalization

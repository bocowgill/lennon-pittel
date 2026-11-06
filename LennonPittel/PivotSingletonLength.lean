module

public import LennonPittel.CycleSupportCount
public import LennonPittel.PivotForwardForest
public import LennonPittel.PointedSymmetricSums
public import LennonPittel.SingletonGaussianLength

/-!
# Length of the sole forward rotation

The conditional sole-cycle bound is summed over cyclic permutations of a
given length. It then transfers to the original score law by retaining the
unnormalized off-diagonal stability mass.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- There is one exposed forward rotation at this matching, and it has length k. -/
def HasSoleForwardExposedLength {n : ℕ} (p : Profile n) (μ : Matching n) (k : ℕ) : Prop :=
  ∃ σ : Matching n, IsSoleForwardExposedRotation p μ σ ∧ σ.support.card = k

open scoped Classical in
/-- Summing the prescribed sole-cycle probabilities gives the length-event bound. -/
theorem measureReal_soleForwardExposedLength_le_sum {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (μ : Matching n) (k : ℕ) :
    ν.real {x | HasSoleForwardExposedLength (P x) μ k} ≤
      ∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.IsCycle ∧ σ.support.card = k),
        ν.real {x | IsSoleForwardExposedRotation (P x) μ σ} := by
  let S := Finset.univ.filter (fun σ : Matching n ↦ σ.IsCycle ∧ σ.support.card = k)
  have heq : {x | HasSoleForwardExposedLength (P x) μ k} =
      ⋃ σ ∈ S, {x | IsSoleForwardExposedRotation (P x) μ σ} := by
    ext x
    simp only [mem_ofPred_eq, HasSoleForwardExposedLength, mem_iUnion,
      S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨σ, hσ, hk⟩ ↦ ⟨σ, ⟨hσ.1.isCycle, hk⟩, hσ⟩,
      fun ⟨σ, hk, hσ⟩ ↦ ⟨σ, hσ, hk.2⟩⟩
  rw [heq]
  exact measureReal_biUnion_finset_le _ _

/-- The exact normalized row bound can be integrated over a measurable
diagonal cutoff without changing the stability normalizer. -/
theorem measure_scoreStable_diagonal_rankEvent_le {n : ℕ} (μ : Matching n)
    {C : Set (DiagonalScorePairs n)} (hC : MeasurableSet C)
    (hvalid : ∀ d ∈ C, (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) ∧
      ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    (B : Set (Profile n)) {a : ℝ}
    (hrow : ∀ᵐ d ∂diagonalScoreLaw n, d ∈ C →
      (Measure.pi (normalizedStableScoreRowLaw d)).real
        {r | profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) ∈ B}
        ≤ a) :
    continuousScoreLaw n
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ profileOfScores x ∈ B} ≤
      continuousScoreLaw n {x | IsScoreStable x μ} * ENNReal.ofReal a := by
  let G : Set (ScoreProfile n) := profileOfScores ⁻¹' B
  let D : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let f : ScoreProfile n → ℝ≥0∞ := G.indicator fun _ ↦ 1
  have hG : MeasurableSet G := measurable_profileOfScores n MeasurableSet.of_discrete
  have hf : Measurable f := measurable_const.indicator hG
  have hleft : continuousScoreLaw n
      {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ profileOfScores x ∈ B} =
      ∫⁻ x in D, f x ∂continuousScoreLaw n := by
    rw [show f = G.indicator (fun _ ↦ (1 : ℝ≥0∞)) from rfl, lintegral_indicator hG,
      lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hG]
    congr 1
    ext x
    change (IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧ profileOfScores x ∈ B) ↔
      (profileOfScores x ∈ B ∧ IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C)
    tauto
  rw [hleft, continuousScoreLaw_lintegral_stable_and_diagonal_rows μ hC hf]
  let m (d : DiagonalScorePairs n) := offDiagonalScoreLaw n (offDiagonalNonblocking d)
  have hM : (∫⁻ d, m d ∂diagonalScoreLaw n) = continuousScoreLaw n {x | IsScoreStable x μ} := by
    simpa only [mem_univ, and_true, indicator_univ, m] using
      (continuousScoreLaw_stable_and_diagonal μ (C := univ) MeasurableSet.univ).symm
  calc
    _ ≤ ∫⁻ d in C, m d * ENNReal.ofReal a ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae hrow] with d hd hr
      obtain ⟨hx, hy⟩ := hvalid d hd
      let ν := Measure.pi (normalizedStableScoreRowLaw d)
      let : ∀ i : Fin n, IsProbabilityMeasure (normalizedStableScoreRowLaw d i) :=
        fun i ↦ normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
      let R := (splitScorePairs μ).symm ∘ fun r : OffDiagonalScoreRows n ↦
        (d, (offDiagonalRowsEquiv n).symm r)
      let E := R ⁻¹' G
      have hE : MeasurableSet E := hG.preimage
        ((splitScorePairs μ).symm.measurable.comp
          (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
      have hb : ν E ≤ ENNReal.ofReal a := by
        have h := ENNReal.ofReal_le_ofReal (hr hd)
        change ENNReal.ofReal ((ν E).toReal) ≤ _ at h
        rwa [ENNReal.ofReal_toReal (measure_ne_top ν E)] at h
      have hfun : (fun r ↦ f ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) =
          E.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
        funext r
        change G.indicator (fun _ ↦ (1 : ℝ≥0∞)) (R r) = _
        by_cases he : r ∈ E
        · rw [indicator_of_mem (show R r ∈ G from he), indicator_of_mem he]
        · rw [indicator_of_notMem (show R r ∉ G from he), indicator_of_notMem he]
      rw [pi_stableScoreRowLaw_eq_smul_normalized d hx hy, hfun, lintegral_smul_measure,
        lintegral_indicator hE, lintegral_one, Measure.restrict_apply_univ, smul_eq_mul]
      exact mul_le_mul_right hb _
    _ ≤ ∫⁻ d, m d * ENNReal.ofReal a ∂diagonalScoreLaw n := lintegral_mono' Measure.restrict_le_self
      le_rfl
    _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hM]

open scoped Classical in
/-- A bound on each sole cycle gives a finite length bound, with one
inverse-length factor from the number of cyclic orders on each support. -/
theorem measureReal_soleForwardExposedLength_le_fallingFactorials {n k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (P : Ω → Profile n) (μ : Matching n)
    (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) {τ η : ℝ}
    (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hcycle : ∀ σ : Matching n, ν.real {x | IsSoleForwardExposedRotation (P x) μ σ} ≤
      ((1 + η) ^ σ.support.card * ∏ i ∈ σ.support, p i) *
        (Real.exp 1 * (τ + ∑ i ∈ σ.support, p i))) :
    ν.real {x | HasSoleForwardExposedLength (P x) μ k} ≤
      Real.exp 1 * ((1 + η) ^ k *
        ((τ / (k : ℝ)) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) +
          (∑ i, p i ^ 2) * ((n.descFactorial (k - 1) : ℝ) / (n : ℝ) ^ (k - 1)))) := by
  let S := Finset.univ.filter (fun σ : Matching n ↦ σ.IsCycle ∧ σ.support.card = k)
  let F (A : Finset (Fin n)) := (∏ i ∈ A, p i) * (τ + ∑ i ∈ A, p i)
  have hc : 0 ≤ (1 + η) ^ k := pow_nonneg (by linarith only [hη]) _
  calc
    _ ≤ ∑ σ ∈ S, ν.real {x | IsSoleForwardExposedRotation (P x) μ σ} :=
      measureReal_soleForwardExposedLength_le_sum ν P μ k
    _ ≤ ∑ σ ∈ S, (((1 + η) ^ σ.support.card * ∏ i ∈ σ.support, p i) *
        (Real.exp 1 * (τ + ∑ i ∈ σ.support, p i))) :=
      Finset.sum_le_sum fun σ _ ↦ hcycle σ
    _ = Real.exp 1 * ((1 + η) ^ k * ∑ σ ∈ S, F σ.support) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      have hkσ : σ.support.card = k := (Finset.mem_filter.mp hσ).2.2
      rw [hkσ]
      unfold F
      ring
    _ = Real.exp 1 * ((1 + η) ^ k * (((k - 1).factorial : ℝ) *
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, F A)) := by
      rw [show (∑ σ ∈ S, F σ.support) = _ from sum_cyclesWithLength_by_support k hk F]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weightedSupportLengthSum_le hn hk hkn hp hp₁ hτ) hc)
      (Real.exp_pos _).le

/-- The sole exposed forward rotation has a Gaussian length envelope
under the exact conditional score law. -/
theorem ae_diagonal_measureReal_soleForwardExposedLength_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (hn : 0 < n) (μ : Matching n)
    (hη₀ : 0 ≤ coexposureSuccessorPerturbation n)
    (hη : coexposureSuccessorPerturbation n ≤ 1 / Real.sqrt (n : ℝ))
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b →
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
        (Measure.pi (normalizedStableScoreRowLaw d)).real
          {r | HasSoleForwardExposedLength
            (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ k}
          ≤ Real.exp 5 * Real.exp (-(k : ℝ)^2 / (16 * (n : ℝ))) *
            ((b + ∑ i, (forwardSpouseWeight d i) ^ 2) / (k : ℝ) +
              ∑ i, (forwardSpouseWeight d i) ^ 2) := by
  filter_upwards [ae_diagonal_measureReal_soleForwardExposed_le_of_goodDiagonalScores μ hA hB hδ]
    with d hd
  intro hg hx hy b hb k hk hkn
  let p := forwardSpouseWeight d
  let s := ∑ i, p i ^ 2
  let τ := b + s
  let ν := Measure.pi (normalizedStableScoreRowLaw d)
  let P := fun r : OffDiagonalScoreRows n ↦
    profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have hp₁ : ∑ i, p i = 1 := by unfold p forwardSpouseWeight; rw [← Finset.sum_div, div_self hY.ne']
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ sq_nonneg (p i)
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hd, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hd
  have hτ : 0 ≤ τ := add_nonneg hb₀ hs
  have hcycle (σ : Matching n) :=
    hd hg hx hy b hb σ
  have hfinite := measureReal_soleForwardExposedLength_le_fallingFactorials
    ν P μ hn hk hkn hp hp₁ hτ hη₀ hcycle
  have hexp := mul_le_mul_of_nonneg_left
    (perturbedCycleLength_bound hn hk hkn hη₀ hη hτ hs) (Real.exp_pos 1).le
  refine hfinite.trans (hexp.trans_eq ?_)
  have h14 : Real.exp 1 * Real.exp 4 = Real.exp 5 := by rw [← Real.exp_add]; norm_num
  rw [← mul_assoc, ← mul_assoc, h14]

end LennonPittelFormalization

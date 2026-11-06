module

public import LennonPittel.ScoreRotationBandCrossing

/-!
# Probability bounds for the participation discarded by length cutoffs

The profile law is the pushforward of the continuous score law. Markov's
inequality therefore transfers the singleton-anchor length moment bounds
to the score arrays on which the adaptive walk is defined.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology

namespace LennonPittelFormalization

private theorem ofReal_profileSingletonAnchorLengthWeight {n : ℕ} (p : Profile n)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    ENNReal.ofReal (profileSingletonAnchorLengthWeight p g) =
      profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k)) := by
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro μ _
    by_cases hμ : IsStable p μ
    · simp only [hμ, ite_true]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro σ _
        split <;> simp
      · intro σ _
        split
        · exact hg _
        · exact le_rfl
    · simp [hμ]
  · intro μ _
    split
    · exact Finset.sum_nonneg fun σ _ ↦ by
        split
        · exact hg _
        · exact le_rfl
    · exact le_rfl

private theorem measure_score_lengthWeight_tail_le {n : ℕ} (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) {t b : ℝ} (ht : 0 < t)
    (hm : (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
      ∂(uniformProfile n).toMeasure) ≤ ENNReal.ofReal b) :
    continuousScoreLaw n {x | t < profileSingletonAnchorLengthWeight (profileOfScores x) g}
      ≤ ENNReal.ofReal (b / t) := by
  let E : Set (Profile n) := {p | t < profileSingletonAnchorLengthWeight p g}
  let f (p : Profile n) := profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
  let μ := (uniformProfile n).toMeasure
  change continuousScoreLaw n (profileOfScores ⁻¹' E) ≤ _
  rw [← Measure.map_apply (measurePreserving_profileOfScores n).measurable
    (show MeasurableSet E from MeasurableSet.of_discrete),
    (measurePreserving_profileOfScores n).map_eq]
  change μ E ≤ _
  have hsub : E ⊆ {p | ENNReal.ofReal t ≤ f p} := by
    intro p hp
    change ENNReal.ofReal t ≤ f p
    exact (ENNReal.ofReal_le_ofReal (le_of_lt hp)).trans_eq
      (ofReal_profileSingletonAnchorLengthWeight p g hg)
  have hmarkov : ENNReal.ofReal t * μ E ≤ ENNReal.ofReal b :=
    (mul_le_mul_right (measure_mono hsub) (ENNReal.ofReal t)).trans
      ((mul_meas_ge_le_lintegral (μ := μ) (f := f) Measurable.of_discrete _).trans hm)
  rw [ENNReal.ofReal_div_of_pos ht]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr ht))
    (Or.inl ENNReal.ofReal_ne_top)).mpr (by simpa only [mul_comm] using hmarkov)

private theorem eventually_log_size_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1

private theorem tendsto_size_quarter_neg :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop

/-- A fixed multiple of the square-root cutoff makes the contribution of
long rotations exceed any positive participation fraction with arbitrarily
small probability, eventually. -/
theorem exists_eventually_measure_longRotationLengthBudget_bad {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n {x | ε * ((n : ℝ) * Real.log n) <
        profileSingletonAnchorLengthWeight (profileOfScores x)
          (longRotationLengthWeight (A * Real.sqrt n))} ≤ ENNReal.ofReal η := by
  let C₁ := Real.exp 5 * (54 * Real.exp 4)
  let C₂ := Real.exp 5 * (144 * Real.exp 16)
  let δ := ε * η / 3
  have hδ : 0 < δ := by positivity
  have hA_lim : Tendsto (fun A : ℝ ↦ C₂ * Real.exp (-A)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have hA_ev : ∀ᶠ A : ℝ in atTop, 1 ≤ A ∧ C₂ * Real.exp (-A) ≤ δ :=
    (eventually_ge_atTop (1 : ℝ)).and (hA_lim.eventually_le_const hδ)
  obtain ⟨A, hA, hA_tail⟩ := hA_ev.exists
  refine ⟨A, hA, ?_⟩
  have hsize_lim :
      Tendsto (fun n : ℕ ↦ C₁ * (n : ℝ) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_size_quarter_neg
  have hrem_lim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_lintegral_profileSingletonAnchorLongLength_le,
    hsize_lim.eventually_le_const hδ, hrem_lim.eventually_le_const hδ,
    eventually_ge_atTop (1 : ℕ), eventually_log_size_ge_one]
    with n hm hs hr hn hlog
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  let b := (n : ℝ) * Real.log n
  have hb₁ : 1 ≤ b := by dsimp [b]; nlinarith
  have hb : 0 < b := zero_lt_one.trans_le hb₁
  have hsqrt : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn₀.le]
    norm_num
  have hc : Real.exp 5 * ((54 * Real.exp 4) / Real.sqrt (Real.sqrt (n : ℝ)) +
        144 * Real.exp 16 * Real.exp (-A)) ≤ 2 * δ := by
    rw [hsqrt]
    have hsplit : Real.exp 5 * ((54 * Real.exp 4) / ((n : ℝ) ^ (1 / 4 : ℝ)) +
        144 * Real.exp 16 * Real.exp (-A)) =
        C₁ * (n : ℝ) ^ (-(1 / 4) : ℝ) + C₂ * Real.exp (-A) := by
      rw [Real.rpow_neg hn₀.le]
      dsimp [C₁, C₂]
      ring
    rw [hsplit]
    linarith
  let g := longRotationLengthWeight (A * Real.sqrt (n : ℝ))
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g, longRotationLengthWeight]; split <;> positivity
  apply (measure_score_lengthWeight_tail_le g hg (b := b * (ε * η)) (mul_pos hε hb) ?_).trans
  · apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (mul_pos hε hb)).mpr (by ring_nf; exact le_rfl)
  · refine (hm A).trans ?_
    rw [← ENNReal.ofReal_mul hb.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ b * (2 * δ) + δ := add_le_add (mul_le_mul_of_nonneg_left hc hb.le) hr
      _ ≤ b * (2 * δ) + b * δ :=
        add_le_add le_rfl (le_mul_of_one_le_left hδ.le hb₁)
      _ = _ := by dsimp [δ]; ring

private theorem profileSingletonAnchorLengthWeight_le_mul_count {n : ℕ} (p : Profile n)
    (g : ℕ → ℝ≥0∞) (K : ℝ≥0∞) (hg : ∀ k, g k ≤ K) :
    profileSingletonAnchorLengthWeight p g ≤
      K * profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞)) := by
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro μ _
  by_cases hμ : IsStable p μ
  · simp only [hμ, ite_true, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    by_cases hσ : IsSoleForwardExposedRotation p μ σ
    · simpa only [hσ, ite_true, mul_one] using hg σ.support.card
    · simp [hσ]
  · simp [hμ]

/-- Rotations shorter than the fourth-root cutoff contribute a vanishing
fraction of `n * log n` participation in probability. -/
theorem tendsto_measure_shortRotationLengthBudget_bad {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ continuousScoreLaw n {x | ε * ((n : ℝ) * Real.log n) <
      profileSingletonAnchorLengthWeight (profileOfScores x)
        (shortRotationLengthWeight ((n : ℝ) ^ (1 / 4 : ℝ)))}) atTop (𝓝 0) := by
  let C := Real.exp 5 * (108 + 48 * Real.exp 4)
  have hlimit : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((C + 1) / ε * (n : ℝ) ^ (-(1 / 4) : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_const_nhds.mul tendsto_size_quarter_neg)
  refine tendsto_const_nhds.squeeze' hlimit (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_lintegral_profileSingletonAnchorCount_le,
    eventually_ge_atTop (1 : ℕ), eventually_log_size_ge_one] with n hm hn hlog
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  have hl₀ : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  let K := (n : ℝ) ^ (1 / 4 : ℝ)
  let g := shortRotationLengthWeight K
  have hK : 0 < K := Real.rpow_pos_of_pos hn₀ _
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g, shortRotationLengthWeight]; split <;> positivity
  have hle (k : ℕ) : ENNReal.ofReal (g k) ≤ ENNReal.ofReal K := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [g, shortRotationLengthWeight]
    split
    · exact le_of_lt ‹_›
    · exact hK.le
  have hcount : (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
        ∂(uniformProfile n).toMeasure) ≤
      ENNReal.ofReal ((C + 1) * Real.sqrt n * Real.log n) := by
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsmall : (n : ℝ) ^ (-3 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn₁ (by norm_num)
    have hbase : 1 ≤ Real.sqrt (n : ℝ) * Real.log n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hn₁) hlog
    change C * Real.sqrt n * Real.log n + _ ≤ _
    nlinarith only [hsmall, hbase]
  have hmoment : (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤ ENNReal.ofReal
      (K * ((C + 1) * Real.sqrt n * Real.log n)) := by
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal K *
          profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
          ∂(uniformProfile n).toMeasure :=
        lintegral_mono fun p ↦ profileSingletonAnchorLengthWeight_le_mul_count p _ _ hle
      _ = ENNReal.ofReal K *
          (∫⁻ p, profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
            ∂(uniformProfile n).toMeasure) := lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((C + 1) * Real.sqrt n * Real.log n) :=
        mul_le_mul_right hcount _
      _ = _ := (ENNReal.ofReal_mul hK.le).symm
  refine (measure_score_lengthWeight_tail_le g hg
    (mul_pos hε (mul_pos hn₀ hl₀)) hmoment).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hp : K * Real.sqrt n = (n : ℝ) * (n : ℝ) ^ (-(1 / 4) : ℝ) := by
    calc
      _ = (n : ℝ) ^ (3 / 4 : ℝ) := by
        unfold K
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn₀]
        norm_num
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 4) : ℝ) := by
        rw [← Real.rpow_add hn₀]
        norm_num
      _ = _ := by rw [Real.rpow_one]
  rw [show K * ((C + 1) * Real.sqrt n * Real.log n) =
    (C + 1) * (K * Real.sqrt n) * Real.log n by ring, hp]
  apply le_of_eq
  field_simp [hε.ne', hn₀.ne', hl₀.ne']

/-- A sufficiently small positive multiple of the square-root cutoff makes
the short-rotation participation exceed a fixed fraction with arbitrarily
small probability, eventually. -/
theorem exists_eventually_measure_shortRotationLengthBudget_bad {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n {x | ε * ((n : ℝ) * Real.log n) <
        profileSingletonAnchorLengthWeight (profileOfScores x)
          (shortRotationLengthWeight (b * Real.sqrt n))} ≤ ENNReal.ofReal η := by
  let C := Real.exp 5 * (108 + 48 * Real.exp 4)
  have hC : 0 < C + 1 := by dsimp [C]; positivity
  let b := min 1 (ε * η / (C + 1))
  have hb : 0 < b := lt_min zero_lt_one (div_pos (mul_pos hε hη) hC)
  have hbudget : b * (C + 1) ≤ ε * η := (le_div_iff₀ hC).mp (min_le_right _ _)
  refine ⟨b, hb, min_le_left _ _, ?_⟩
  filter_upwards [eventually_lintegral_profileSingletonAnchorCount_le,
    eventually_ge_atTop (1 : ℕ), eventually_log_size_ge_one] with n hm hn hlog
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁
  let L := (n : ℝ) * Real.log n
  have hL : 0 < L := mul_pos hn₀ (zero_lt_one.trans_le hlog)
  let K := b * Real.sqrt (n : ℝ)
  let g := shortRotationLengthWeight K
  have hK : 0 < K := mul_pos hb (Real.sqrt_pos_of_pos hn₀)
  have hg (k : ℕ) : 0 ≤ g k := by dsimp [g, shortRotationLengthWeight]; split <;> positivity
  have hle (k : ℕ) : ENNReal.ofReal (g k) ≤ ENNReal.ofReal K := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [g, shortRotationLengthWeight]
    split
    · exact le_of_lt ‹_›
    · exact hK.le
  let f (p : Profile n) := profileSingletonAnchorLengthWeight p (fun _ ↦ (1 : ℝ≥0∞))
  have hcount : (∫⁻ p, f p ∂(uniformProfile n).toMeasure) ≤
      ENNReal.ofReal ((C + 1) * Real.sqrt n * Real.log n) := by
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsmall : (n : ℝ) ^ (-3 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn₁ (by norm_num)
    have hbase : 1 ≤ Real.sqrt (n : ℝ) * Real.log n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hn₁) hlog
    change C * Real.sqrt n * Real.log n + _ ≤ _
    nlinarith only [hsmall, hbase]
  have hmoment : (∫⁻ p, profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k))
        ∂(uniformProfile n).toMeasure) ≤ ENNReal.ofReal (L * (ε * η)) := by
    calc
      _ ≤ ∫⁻ p, ENNReal.ofReal K * f p ∂(uniformProfile n).toMeasure :=
        lintegral_mono fun p ↦ profileSingletonAnchorLengthWeight_le_mul_count p _ _ hle
      _ = ENNReal.ofReal K * (∫⁻ p, f p ∂(uniformProfile n).toMeasure) :=
        lintegral_const_mul _ Measurable.of_discrete
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((C + 1) * Real.sqrt n * Real.log n) :=
        mul_le_mul_right hcount _
      _ = ENNReal.ofReal (L * (b * (C + 1))) := by
        rw [← ENNReal.ofReal_mul hK.le]
        congr 1
        have hs := Real.sq_sqrt hn₀.le
        dsimp [K, L]
        calc
          _ = b * (C + 1) * (Real.sqrt n)^2 * Real.log n := by ring
          _ = _ := by rw [hs]; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbudget hL.le)
  apply (measure_score_lengthWeight_tail_le g hg (mul_pos hε hL) hmoment).trans
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_iff₀ (mul_pos hε hL)).mpr (by ring_nf; exact le_rfl)

end LennonPittelFormalization

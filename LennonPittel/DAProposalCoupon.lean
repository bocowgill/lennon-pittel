module

public import LennonPittel.DAStreamSimulation

/-!
# Coupon-collector bound for deferred acceptance

The raw stream transcript is iid uniform even though its row is selected adaptively.
If every receiver has appeared by the horizon, the ordinary run has completed with
at most that many proposals. The failure probability is at most the coupon tail.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology LennonPittelFormalization

namespace LennonPittelFormalization

variable {n T : ℕ}

private def missesReceiver (w : Fin n) : Set (Fin T → Fin n) :=
  {y | ∀ t, y t ≠ w}

private def notCovered (n T : ℕ) : Set (Fin T → Fin n) :=
  {y | ¬ ∀ w, ∃ t, y t = w}

private theorem measure_missesReceiver_le [Nonempty (Fin n)] (hn : 0 < n)
    (w : Fin n) :
    (Measure.pi fun _ : Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure)
      (missesReceiver w) ≤ ENNReal.ofReal (Real.exp (-(T : ℝ) / n)) := by
  classical
  let μ := (PMF.fintypeUniform (Fin n)).toMeasure
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : μ ({w} : Set (Fin n)) = (n : ℝ≥0∞)⁻¹ := by
    simp [μ, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w)]
  have hwc : μ ({w}ᶜ : Set (Fin n)) = 1 - (n : ℝ≥0∞)⁻¹ := by
    rw [measure_compl (measurableSet_singleton w) (measure_ne_top _ _), measure_univ, hw]
  have hbase : 1 - (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)⁻¹)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnR, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (inv_nonneg.mpr hnR.le)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(n : ℝ)⁻¹)
  have he : missesReceiver (T := T) w = Set.pi univ (fun _ ↦ ({w}ᶜ : Set (Fin n))) := by
    ext y
    simp [missesReceiver]
  rw [he, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change μ ({w}ᶜ : Set (Fin n)) ^ T ≤ _
  rw [hwc]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)⁻¹)) ^ T := pow_le_pow_left' hbase T
    _ = _ := by
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) _, ← Real.exp_nat_mul]
      congr 2
      rw [div_eq_mul_inv, mul_neg, neg_mul]

private theorem measure_notCovered_le [Nonempty (Fin n)] (hn : 0 < n) :
    (Measure.pi fun _ : Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure)
      (notCovered n T) ≤ ENNReal.ofReal ((n : ℝ) * Real.exp (-(T : ℝ) / n)) := by
  classical
  let μ := Measure.pi fun _ : Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure
  have he : notCovered n T = ⋃ w : Fin n, missesReceiver w := by
    ext y
    simp [notCovered, missesReceiver]
  rw [he]
  calc
    μ (⋃ w : Fin n, missesReceiver w) ≤ ∑ w : Fin n, μ (missesReceiver w) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin n, ENNReal.ofReal (Real.exp (-(T : ℝ) / n)) :=
      Finset.sum_le_sum fun w _ ↦ measure_missesReceiver_le hn w
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- A proposal cap fails with probability at most the uniform receiver coverage bound. -/
theorem measure_daProposalCount_gt_le (hn : 0 < n) (hT : 0 < T) :
    (uniformProfile n).toMeasure {p | T < (DAState.run p (n * n)).proposalCount} ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp (-(T : ℝ) / n)) := by
  classical
  let seed : Fin n := ⟨0, hn⟩
  have : Nonempty (Fin n) := ⟨seed⟩
  let rawLaw : Measure (Fin n × Fin T → Fin n) :=
    Measure.pi fun _ ↦ (PMF.fintypeUniform (Fin n)).toMeasure
  let rankLaw : Measure (Fin n → Equiv.Perm (Fin n)) :=
    Measure.pi fun _ ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure rankLaw := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let f := fun z : (Fin n × Fin T → Fin n) × (Fin n → Equiv.Perm (Fin n)) ×
      (Fin n → Equiv.Perm (Fin n)) ↦ DAStreamState.streamProfile z.1 z.2.1 z.2.2
  let E : Set (Profile n) := {p | T < (DAState.run p (n * n)).proposalCount}
  have hf : MeasurePreserving f (rawLaw.prod (rankLaw.prod rankLaw))
      (uniformProfile n).toMeasure := measurePreserving_streamProfile
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  change (uniformProfile n).toMeasure E ≤ _
  rw [← hf.map_eq, Measure.map_apply hf.measurable hE,
    Measure.prod_apply_symm (hf.measurable hE)]
  calc
    _ ≤ (∫⁻ _, ENNReal.ofReal ((n : ℝ) * Real.exp (-(T : ℝ) / n))
        ∂(rankLaw.prod rankLaw)) := by
      apply lintegral_mono
      intro z
      let next := DAStreamState.query seed z.2 hT
      let draw := fun raw ↦ adaptiveTranscriptFn next raw T
      have hfiber : (fun raw ↦ (raw, z)) ⁻¹' (f ⁻¹' E) ⊆ draw ⁻¹' notCovered n T := by
        intro raw hbad
        change T < (DAState.run (DAStreamState.streamProfile raw z.1 z.2)
          (n * n)).proposalCount at hbad
        exact fun hc ↦ (Nat.not_lt_of_ge
          (DAStreamState.proposalCount_le_of_adaptiveTranscript_covers
            seed hT raw z.1 z.2 hc)) hbad
      refine (measure_mono hfiber).trans ?_
      rw [← Measure.map_apply (f := draw) Measurable.of_discrete MeasurableSet.of_discrete,
        show Measure.map draw rawLaw = _ from
          map_adaptiveTranscriptFn_eq_pi (PMF.fintypeUniform (Fin n)).toMeasure next T
            (DAStreamState.query_injective seed z.2 hT)]
      exact measure_notCovered_le hn
    _ = _ := by simp

/-- A common deterministic cap for proposals in either direction. -/
noncomputable def daProposalCap (n : ℕ) : ℕ := ⌈(3 : ℝ) * n * Real.log n⌉₊

theorem eventually_daProposalCap_le :
    ∀ᶠ n : ℕ in atTop, (daProposalCap n : ℝ) ≤ 4 * n * Real.log n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with n hl hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : 1 ≤ (n : ℝ) * Real.log n := by nlinarith
  have hp : 0 ≤ (3 : ℝ) * n * Real.log n := by positivity
  exact (Nat.ceil_lt_add_one hp).le.trans (by linarith)

/-- The ordinary proposal count exceeds the rounded cap with vanishing probability. -/
theorem tendsto_measure_daProposalCount_gt_daProposalCap :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | daProposalCap n < (DAState.run p (n * n)).proposalCount}) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall fun _ ↦ zero_le)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc : (3 : ℝ) * n * Real.log n ≤ daProposalCap n := Nat.le_ceil _
  have hT : 0 < daProposalCap n := by
    exact_mod_cast (show 0 < (daProposalCap n : ℝ) from (by positivity : 0 < (3 : ℝ) * n *
      Real.log n).trans_le hc)
  refine (measure_daProposalCount_gt_le hn' hT).trans (ENNReal.ofReal_le_ofReal ?_)
  have he : -(daProposalCap n : ℝ) / n ≤ Real.log n * (-3) := by
    apply (div_le_iff₀ hnR).mpr
    linarith [show Real.log n * (-3) * n = -((3 : ℝ) * n * Real.log n) by ring]
  calc
    _ ≤ (n : ℝ) * Real.exp (Real.log n * (-3)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hnR.le
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by
      rw [Real.rpow_one, Real.rpow_def_of_pos hnR]
    _ = (n : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hnR]
      norm_num

end LennonPittelFormalization

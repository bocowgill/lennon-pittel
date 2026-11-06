module

public import LennonPittel.CoexposureScoreRefutation
public import LennonPittel.MarkedSpouseLogGeometry
public import LennonPittel.RotationLengthCutoff

/-!
# Score-band crossings along rotation paths

Uniform length and share bounds control the one-step overshoot. Once a legal
path reaches both edges, the uniform log geometry converts a centered-clock
error bound into a lower bound on participation inside the band.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- Uniform upper bound on the relative drop of the female total in one step. -/
noncomputable def rotationStepRelativeCap (n : ℕ) : ℝ :=
  rotationLengthCutoff n * (12 * Real.log n / n)

theorem tendsto_rotationStepRelativeCap :
    Tendsto rotationStepRelativeCap atTop (𝓝 0) := by
  have ho := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)
  have h := (ho.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 12
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  change 12 * (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 8 : ℝ)) =
    (n : ℝ) ^ (7 / 8 : ℝ) * (12 * Real.log (n : ℝ) / (n : ℝ))
  rw [show (7 / 8 : ℝ) = 1 - 1 / 8 by norm_num, Real.rpow_sub hn', Real.rpow_one]
  field_simp

/-- With high probability the uniform share and rotation-length cutoffs both hold. -/
theorem tendsto_measure_badRotationStepGeometry_zero :
    Tendsto (fun n ↦ continuousScoreLaw n
      ((goodCoexposureScores n)ᶜ ∪
        profileOfScores ⁻¹' longStableExposedRotationEvent n (rotationLengthCutoff n)))
      atTop (𝓝 0) := by
  have hgood := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    (C := 1) zero_le_one
    (by simpa only [one_mul] using eventually_expectedNumStableMatchings_le_sizeLog)
  have h := hgood.add tendsto_measure_score_longStableExposedRotationEvent
  rw [add_zero] at h
  exact tendsto_const_nhds.squeeze' h (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall fun _ ↦ measure_union_le _ _)

/-- On the simultaneous score and length event the relative cap applies to
every legal rotation, irrespective of how it was selected. -/
theorem femaleSpouseTotal_drop_le_rotationStepRelativeCap {n : ℕ} {x : ScoreProfile n}
    (hx : x ∈ goodCoexposureScores n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    {μ : Matching n} (hμ : IsStable (profileOfScores x) μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ) :
    femaleSpouseTotal x μ - femaleSpouseTotal x (eliminateRotation μ ρ) ≤
      rotationStepRelativeCap n * femaleSpouseTotal x μ := by
  have hs := hx.2.2 μ hμ
  have hY : 0 < femaleSpouseTotal x μ := by linarith only [hs.1]
  have hn : 0 < n := by
    by_contra! hn
    obtain rfl := Nat.eq_zero_of_le_zero hn
    simp [femaleSpouseTotal] at hY
  have hcap : (ρ.support.card : ℝ) ≤ rotationLengthCutoff n :=
    le_of_not_gt fun h ↦ hlen ⟨μ, ρ, hμ, hρ, h⟩
  have hshare : 0 ≤ 12 * Real.log (n : ℝ) / (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact (femaleSpouseTotal_drop_le_support_mul_share x μ ρ hY hs.2.1
    (fun _ ↦ (hx.2.1 _ _).1.le)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcap hshare) hY.le)

/-- At the first crossing of a positive threshold, the new total retains at
least the same fraction of the threshold as the bound for a single step. -/
theorem lower_of_relative_drop_at_crossing {old new threshold cap : ℝ}
    (hbefore : threshold ≤ old) (hcap : cap ≤ 1) (hdrop : old - new ≤ cap * old) :
    (1 - cap) * threshold ≤ new := by
  calc
    _ ≤ (1 - cap) * old := mul_le_mul_of_nonneg_left hbefore (sub_nonneg.mpr hcap)
    _ = old - cap * old := by ring
    _ ≤ new := by linarith only [hdrop]

/-- The two score-band endpoints in the multi-pivot argument force a
logarithmic-scale amount of participation when the centered error is small. -/
theorem rotationParticipation_ge_of_pivot_band {n : ℕ} (hn : 0 < n)
    (x : ScoreProfile n) (μ ν : Matching n) (rs : List (Equiv.Perm (Fin n)))
    (hμ : HasFemaleLogGeometry x μ) (hν : HasFemaleLogGeometry x ν)
    (hstart : (n : ℝ) ^ (2 / 5 : ℝ) / 2 ≤ femaleSpouseTotal x μ)
    (hfinish : femaleSpouseTotal x ν ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hYν : 0 < femaleSpouseTotal x ν) {E : ℝ}
    (hclock : |femaleLogPotential x ν - femaleLogPotential x μ -
      (rotationParticipation rs : ℝ)| ≤ E) :
    (n : ℝ) * (Real.log n / 5 - Real.log 2 - 6) - E ≤ (rotationParticipation rs : ℝ) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hstart' : 0 < (n : ℝ) ^ (2 / 5 : ℝ) / 2 := by positivity
  have hYμ : 0 < femaleSpouseTotal x μ := hstart'.trans_le hstart
  have hlog : Real.log n / 5 - Real.log 2 ≤
      Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) := by
    have hstartLog := Real.strictMonoOn_log.monotoneOn hstart' hYμ hstart
    have hfinishLog :=
      Real.strictMonoOn_log.monotoneOn hYν (Real.rpow_pos_of_pos hn' _) hfinish
    rw [Real.log_div (Real.rpow_pos_of_pos hn' _).ne' (by norm_num),
      Real.log_rpow hn'] at hstartLog
    rw [Real.log_rpow hn'] at hfinishLog
    rw [Real.log_div hYμ.ne' hYν.ne']
    linarith only [hstartLog, hfinishLog]
  calc
    _ = (n : ℝ) * (Real.log n / 5 - Real.log 2) - 6 * n - E := by ring
    _ ≤ (n : ℝ) * Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) - 6 * n - E :=
      sub_le_sub_right (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog hn'.le) _) _
    _ ≤ _ := rotationParticipation_ge_log_drop x μ ν rs hμ hν hYμ hYν hclock

end LennonPittelFormalization

module

public import LennonPittel.PivotSingletonMarkedLength
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A uniform cutoff on realized rotation lengths

A stable mark with a sole long exposed cycle contributes at least the cutoff
to the singleton-anchor length weight. Every exposed cycle has such an anchor,
possibly at a different stable matching.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal LennonPittelFormalization Topology

namespace LennonPittelFormalization

/-- A stable matching at which the only exposed rotation exceeds the cutoff. -/
def longSingletonRotationEvent (n : ℕ) (c : ℝ) : Set (Profile n) :=
  {p | ∃ μ σ : Matching n, IsStable p μ ∧ IsSoleForwardExposedRotation p μ σ ∧
    c < (σ.support.card : ℝ)}

/-- A rotation exceeds the cutoff at some stable matching. -/
def longStableExposedRotationEvent (n : ℕ) (c : ℝ) : Set (Profile n) :=
  {p | ∃ μ σ : Matching n, IsStable p μ ∧ IsExposedRotation p μ σ ∧
    c < (σ.support.card : ℝ)}

theorem measurableSet_longStableExposedRotationEvent (n : ℕ) (c : ℝ) :
    MeasurableSet (longStableExposedRotationEvent n c) :=
  MeasurableSet.of_discrete

/-- The singleton-anchor representation detects every long rotation exposed at a
stable matching, with no change to its length. -/
theorem longStableExposedRotationEvent_eq_longSingletonRotationEvent (n : ℕ) (c : ℝ) :
    longStableExposedRotationEvent n c = longSingletonRotationEvent n c := by
  ext p
  constructor
  · rintro ⟨μ, σ, hμ, hσ, hc⟩
    obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨μ, hμ⟩
    let r := rotationOfExposed hopt hμ hσ
    let a := rotationEquivSingletonAnchorPair hopt r
    refine ⟨a.val.1, a.val.2, a.property.1, a.property.2, ?_⟩
    rw [rotationEquivSingletonAnchorPair_length hopt r]
    exact hc
  · rintro ⟨μ, σ, hμ, hσ, hc⟩
    exact ⟨μ, σ, hμ, hσ.1, hc⟩

/-- Off the long-cycle event, every realized rotation has length at most the cutoff. -/
theorem rotation_length_le_of_not_mem_longStableExposedRotationEvent
    {n : ℕ} {p : Profile n} {μ₀ : Matching n} {c : ℝ}
    (hopt : IsManOptimal p μ₀) (hp : p ∉ longStableExposedRotationEvent n c)
    (r : Rotation p μ₀) : (r.val.cycle.support.card : ℝ) ≤ c := by
  apply le_of_not_gt
  intro hr
  let a := rotationEquivSingletonAnchorPair hopt r
  apply hp
  rw [longStableExposedRotationEvent_eq_longSingletonRotationEvent]
  refine ⟨a.val.1, a.val.2, a.property.1, a.property.2, ?_⟩
  rw [rotationEquivSingletonAnchorPair_length hopt r]
  exact hr

private theorem cutoff_mul_measure_longSingletonRotationEvent_le {n : ℕ} (c : ℝ) :
    ENNReal.ofReal c * (uniformProfile n).toMeasure (longSingletonRotationEvent n c) ≤
      ∫⁻ p, profileSingletonAnchorLengthWeight p
        (fun k ↦ ENNReal.ofReal (if c < (k : ℝ) then k else 0))
        ∂(uniformProfile n).toMeasure := by
  classical
  let E := longSingletonRotationEvent n c
  let g (k : ℕ) := ENNReal.ofReal (if c < (k : ℝ) then k else 0)
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  change ENNReal.ofReal c * (uniformProfile n).toMeasure E ≤
    ∫⁻ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure
  rw [← lintegral_indicator_const hE]
  apply lintegral_mono
  intro p
  by_cases hp : p ∈ E
  · rw [indicator_of_mem hp]
    obtain ⟨μ, σ, hμ, hσ, hc⟩ := hp
    calc
      ENNReal.ofReal c ≤ g σ.support.card := by
        simpa only [g, ite_eq_left hc] using ENNReal.ofReal_le_ofReal hc.le
      _ ≤ singletonAnchorLengthWeight p μ g := by
        simpa only [singletonAnchorLengthWeight, ite_eq_left hσ] using
          (Finset.single_le_sum
            (f := fun τ : Matching n ↦
              if IsSoleForwardExposedRotation p μ τ then g τ.support.card else 0)
            (fun _ _ ↦ zero_le) (Finset.mem_univ σ))
      _ ≤ profileSingletonAnchorLengthWeight p g := by
        simpa only [profileSingletonAnchorLengthWeight, ite_eq_left hμ] using
          (Finset.single_le_sum
            (f := fun ν : Matching n ↦ if IsStable p ν then singletonAnchorLengthWeight p ν g else 0)
            (fun _ _ ↦ zero_le) (Finset.mem_univ μ))
  · rw [indicator_of_notMem hp]
    exact zero_le

/-- A sublinear cutoff for the maximum realized rotation length. -/
noncomputable def rotationLengthCutoff (n : ℕ) : ℝ := (n : ℝ) ^ (7 / 8 : ℝ)

/-- The maximum-length cutoff is negligible on the linear scale. -/
theorem tendsto_rotationLengthCutoff_div_size :
    Tendsto (fun n : ℕ ↦ rotationLengthCutoff n / (n : ℝ)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
    tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  change (n : ℝ) ^ (-(1 / 8) : ℝ) = (n : ℝ) ^ (7 / 8 : ℝ) / (n : ℝ)
  rw [show (-(1 / 8) : ℝ) = 7 / 8 - 1 by norm_num, Real.rpow_sub hn', Real.rpow_one]

private theorem real_longRotationBound_le {x : ℝ} (hx : 1 ≤ x) :
    (x * Real.log x * (Real.exp 5 *
      ((54 * Real.exp 4) / Real.sqrt (Real.sqrt x) +
        144 * Real.exp 16 * Real.exp (-(x ^ (3 / 8 : ℝ))))) + x ^ (-2 : ℝ)) /
      (x ^ (7 / 8 : ℝ)) ≤
    (Real.exp 5 * (54 * Real.exp 4 + 144 * Real.exp 16)) *
      (Real.log x / x ^ (1 / 8 : ℝ)) + x ^ (-2 : ℝ) := by
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hsqrt : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx'.le]
    norm_num
  have hexp : Real.exp (-(x ^ (3 / 8 : ℝ))) ≤ 1 / x ^ (1 / 4 : ℝ) := by
    have hxpow : x ^ (1 / 4 : ℝ) ≤ x ^ (3 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hle : x ^ (1 / 4 : ℝ) ≤ Real.exp (x ^ (3 / 8 : ℝ)) :=
      hxpow.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hle
  have hpowers : x ^ (1 / 4 : ℝ) * x ^ (7 / 8 : ℝ) = x * x ^ (1 / 8 : ℝ) := by
    calc
      _ = x ^ (1 / 4 + 7 / 8 : ℝ) := (Real.rpow_add hx' _ _).symm
      _ = x ^ (1 + 1 / 8 : ℝ) := by norm_num
      _ = _ := by rw [Real.rpow_add hx', Real.rpow_one]
  have hden : 1 ≤ x ^ (7 / 8 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [add_div]
  refine add_le_add ?_ ?_
  · calc
      _ ≤ (x * Real.log x * (Real.exp 5 *
          ((54 * Real.exp 4) / x ^ (1 / 4 : ℝ) +
            144 * Real.exp 16 * (1 / x ^ (1 / 4 : ℝ))))) /
          x ^ (7 / 8 : ℝ) := by
        rw [hsqrt]
        gcongr
      _ = _ := by
        have heq :
            54 * Real.exp 4 / x ^ (1 / 4 : ℝ) +
                144 * Real.exp 16 * (1 / x ^ (1 / 4 : ℝ)) =
              (54 * Real.exp 4 + 144 * Real.exp 16) / x ^ (1 / 4 : ℝ) := by ring
        rw [heq, ← mul_div_assoc, ← mul_div_assoc, div_div, hpowers]
        field_simp
  · exact (div_le_iff₀ (by positivity)).mpr
      (le_mul_of_one_le_right (by positivity) hden)

/-- The chance that some stable matching exposes a rotation longer than
`rotationLengthCutoff n` tends to zero. -/
theorem tendsto_measure_longStableExposedRotationEvent :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure
      (longStableExposedRotationEvent n (rotationLengthCutoff n))) atTop (𝓝 0) := by
  let C := Real.exp 5 * (54 * Real.exp 4 + 144 * Real.exp 16)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 / 8 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (C * (Real.log n / (n : ℝ) ^ (1 / 8 : ℝ)) + (n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds.mul hlog).add hsmall)
  refine tendsto_const_nhds.squeeze' hupper (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_lintegral_profileSingletonAnchorLongLength_le,
    eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn₁'
  let a := (n : ℝ) ^ (3 / 8 : ℝ)
  let c := rotationLengthCutoff n
  have hc : 0 < c := Real.rpow_pos_of_pos hnpos _
  have heq : a * Real.sqrt (n : ℝ) = c := by
    dsimp [a, c, rotationLengthCutoff]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
    norm_num
  have hweighted := hn a
  rw [heq] at hweighted
  have hm := (cutoff_mul_measure_longSingletonRotationEvent_le (n := n) c).trans hweighted
  rw [mul_comm] at hm
  have hnl : 0 ≤ (n : ℝ) * Real.log n := mul_nonneg (by positivity) (Real.log_nonneg hn₁')
  rw [longStableExposedRotationEvent_eq_longSingletonRotationEvent]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hc))
    (Or.inl ENNReal.ofReal_ne_top)).mpr hm |>.trans ?_
  rw [← ENNReal.ofReal_mul hnl, ← ENNReal.ofReal_add (mul_nonneg hnl (by positivity))
    (by positivity), ← ENNReal.ofReal_div_of_pos hc]
  exact ENNReal.ofReal_le_ofReal (real_longRotationBound_le hn₁')

/-- The same cutoff holds for the preference profile drawn from continuous scores. -/
theorem tendsto_measure_score_longStableExposedRotationEvent :
    Tendsto (fun n ↦ continuousScoreLaw n
      (profileOfScores ⁻¹' longStableExposedRotationEvent n (rotationLengthCutoff n)))
      atTop (𝓝 0) := by
  convert tendsto_measure_longStableExposedRotationEvent using 1
  funext n
  rw [← (measurePreserving_profileOfScores n).map_eq,
    Measure.map_apply (measurePreserving_profileOfScores n).measurable
      (measurableSet_longStableExposedRotationEvent n _)]

end LennonPittelFormalization

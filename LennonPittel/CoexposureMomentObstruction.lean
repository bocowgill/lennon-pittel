module

public import LennonPittel.CoexposedRotationThreshold
public import LennonPittel.CoexposedRotationMultiplicity
public import LennonPittel.ContinuousScoreBridge
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Algebra.Order.Field

/-!
# A moment obstruction to high-probability co-exposure

The score calculation can bound a truncated weight on a larger sample
space than the space of preference profiles. The probability transfer
below keeps the score-space measure and the profile law distinct.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- If an event forces a large weight outside an exceptional set, its mass is
bounded by the exceptional mass plus a Markov bound. -/
theorem measure_le_exception_add_lintegral_div_of_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E G : Set Ω)
    {w : Ω → ℝ≥0∞} (hw : Measurable w) {b : ℝ≥0∞} (hb₀ : b ≠ 0) (hbtop : b ≠ ⊤)
    (hcert : ∀ x ∈ E, x ∈ G → b ≤ w x) :
    μ E ≤ μ Gᶜ + (∫⁻ x, w x ∂μ) / b := by
  have hE : E ⊆ Gᶜ ∪ {x | b ≤ w x} := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inr (hcert x hx hg)
    · exact Or.inl hg
  have hmarkov : μ {x | b ≤ w x} ≤ (∫⁻ x, w x ∂μ) / b :=
    (ENNReal.le_div_iff_mul_le (Or.inl hb₀) (Or.inl hbtop)).2
      (by simpa only [mul_comm] using mul_meas_ge_le_lintegral (μ := μ) hw b)
  exact (measure_mono hE).trans ((measure_union_le _ _).trans (add_le_add_right hmarkov _))

/-- Vanishing exceptional mass and normalized weight force the co-exposure
probability to vanish under the uniform profile law. The score law, the
weight certificate, and its asymptotic estimate are explicit inputs. -/
theorem tendsto_uniformProfile_coexposure_zero_of_lintegral
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (profile : ∀ n, Ω n → Profile n)
    (hprofile : ∀ n, Measurable (profile n))
    (hlaw : ∀ n, Measure.map (profile n) (μ n) = (uniformProfile n).toMeasure)
    (k : ℕ → ℕ) (G : ∀ n, Set (Ω n)) (w : ∀ n, Ω n → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hcert : ∀ n x, HasCoexposedRotations (profile n x) (k n) → x ∈ G n →
      (3 : ℝ≥0∞) ^ (k n) ≤ w n x)
    (hbad : Tendsto (fun n ↦ μ n (G n)ᶜ) atTop (𝓝 0))
    (hsmall : Tendsto (fun n ↦ (∫⁻ x, w n x ∂(μ n)) / (3 : ℝ≥0∞) ^ (k n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure {p | HasCoexposedRotations p (k n)})
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n ↦ μ n (G n)ᶜ + (∫⁻ x, w n x ∂(μ n)) / (3 : ℝ≥0∞) ^ (k n)) atTop (𝓝 0) := by
    simpa only [add_zero] using hbad.add hsmall
  refine tendsto_const_nhds.squeeze' hupper
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun n ↦ ?_)
  rw [← hlaw n, Measure.map_apply (hprofile n) MeasurableSpace.measurableSet_top]
  exact measure_le_exception_add_lintegral_div_of_lower_bound (μ n) _ (G n) (hw n)
    (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num)) (hcert n)

/-- The weighted count on a good score event, and zero outside it. -/
noncomputable def scoreCoexposureWeight (n : ℕ) (G : Set (ScoreProfile n)) :
    ScoreProfile n → ℝ≥0∞ :=
  G.indicator fun x ↦ (coexposureWeight (profileOfScores x) : ℝ≥0∞)

/-- A measurable good-score event gives a measurable truncated weight. -/
theorem measurable_scoreCoexposureWeight {n : ℕ} {G : Set (ScoreProfile n)}
    (hG : MeasurableSet G) : Measurable (scoreCoexposureWeight n G) :=
  have hcount : Measurable (fun p : Profile n ↦ (coexposureWeight p : ℝ≥0∞)) :=
    fun _ _ ↦ MeasurableSpace.measurableSet_top
  (hcount.comp (measurePreserving_profileOfScores n).measurable).indicator hG

/-- In the existing iid score model, the surviving-subset bound and the ranking
bridge give a zero limit once the two analytic bounds are supplied. -/
theorem tendsto_uniformProfile_coexposure_zero_of_score_moment
    (k : ℕ → ℕ) (G : ∀ n, Set (ScoreProfile n)) (hG : ∀ n, MeasurableSet (G n))
    (hbad : Tendsto (fun n ↦ continuousScoreLaw n (G n)ᶜ) atTop (𝓝 0))
    (hsmall : Tendsto (fun n ↦
      (∫⁻ x, scoreCoexposureWeight n (G n) x ∂(continuousScoreLaw n)) / (3 : ℝ≥0∞) ^ (k n))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ (uniformProfile n).toMeasure {p | HasCoexposedRotations p (k n)})
      atTop (𝓝 0) :=
  tendsto_uniformProfile_coexposure_zero_of_lintegral continuousScoreLaw
    (fun _ ↦ profileOfScores) (fun n ↦ (measurePreserving_profileOfScores n).measurable)
    (fun n ↦ (measurePreserving_profileOfScores n).map_eq) k G
    (fun n ↦ scoreCoexposureWeight n (G n))
    (fun n ↦ measurable_scoreCoexposureWeight (hG n))
    (fun n x hp hg ↦ by
      have hpow : (3 : ℝ≥0∞) ^ (k n) ≤ (coexposureWeight (profileOfScores x) : ℝ≥0∞) := by
        exact_mod_cast hp.pow_le_coexposureWeight
      simpa only [scoreCoexposureWeight, Set.indicator_of_mem hg] using hpow)
    hbad hsmall

/-- A positive vanishing tolerance with target asymptotic to \(n/e\) by Pittel's first moment. -/
noncomputable def reciprocalLogTolerance (n : ℕ) : ℝ :=
  (Real.log ((n : ℝ) + 2))⁻¹

/-- The reciprocal-log tolerance meets all three hypotheses of the conjecture. -/
theorem reciprocalLogTolerance_admissible :
    (∀ n, 0 < reciprocalLogTolerance n) ∧ Antitone reciprocalLogTolerance ∧
      Tendsto reciprocalLogTolerance atTop (𝓝 0) := by
  have hlog (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
  refine ⟨fun n ↦ inv_pos.mpr (hlog n), ?_, ?_⟩
  · intro m n hmn
    exact inv_anti₀ (hlog m) (Real.log_le_log (by positivity) (by gcongr))
  · have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right (by norm_num))
        tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hcast).inv_tendsto_atTop

/-- For the reciprocal-log tolerance, the score-moment bounds rule out convergence
of the co-exposure probability to one. The two analytic bounds remain hypotheses. -/
theorem not_tendsto_one_coexposure_reciprocalLog_of_score_moment
    (G : ∀ n, Set (ScoreProfile n)) (hG : ∀ n, MeasurableSet (G n))
    (hbad : Tendsto (fun n ↦ continuousScoreLaw n (G n)ᶜ) atTop (𝓝 0))
    (hsmall : Tendsto (fun n ↦
      (∫⁻ x, scoreCoexposureWeight n (G n) x ∂(continuousScoreLaw n)) /
        (3 : ℝ≥0∞) ^ coexposedRotationThreshold reciprocalLogTolerance n) atTop (𝓝 0)) :
    ¬ Tendsto (fun n ↦ (uniformProfile n).toMeasure
      {p | HasCoexposedRotations p (coexposedRotationThreshold reciprocalLogTolerance n)})
      atTop (𝓝 1) :=
  fun h ↦ zero_ne_one (tendsto_nhds_unique
    (tendsto_uniformProfile_coexposure_zero_of_score_moment _ G hG hbad hsmall) h)

end LennonPittelFormalization

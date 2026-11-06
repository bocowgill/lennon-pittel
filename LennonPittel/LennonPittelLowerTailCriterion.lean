module

public import LennonPittel.PittelFirstMoment

/-!
# Lower-count criterion for the Lennon–Pittel tail

Once the stable-matching count is bounded away from zero in probability on
the `n log n` scale, Pittel's first moment transfers the bound to every
threshold that vanishes relative to the mean.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- The stable-count tail at a real threshold in the uniform preference model. -/
noncomputable def stableMatchingCountTail (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  (uniformProfile n).toMeasure {p | t ≤ (numStableMatchings p : ℝ)}

/-- Raising a threshold can only decrease the stable-count tail. -/
theorem stableMatchingCountTail_antitone (n : ℕ) :
    Antitone (stableMatchingCountTail n) :=
  fun _ _ hab ↦ measure_mono fun _ hp ↦ hab.trans hp

/-- A lower bound away from zero in probability at the `n log n` scale
implies the Lennon–Pittel tail, using the verified mean asymptotic. -/
theorem lennonPittel_of_uniform_lower_scale
    (hlower : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (1 - δ) ≤ stableMatchingCountTail n (c * ((n : ℝ) * Real.log n)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  have hsmall : Tendsto (fun n : ℕ ↦
      ε n * (expectedNumStableMatchings n / ((n : ℝ) * Real.log n))) atTop (𝓝 0) := by
    simpa only [zero_mul] using hε.mul tendsto_expectedNumStableMatchings_div_size_log
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hat : a ≠ ⊤ := ha.ne_top
    have haR : a.toReal < 1 := by
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_strict_mono (by simp) ha
    let δ : ℝ := (1 - a.toReal) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨c, hc, hlarge⟩ := hlower δ hδ
    have haδ : a < ENNReal.ofReal (1 - δ) := by
      rw [← ENNReal.ofReal_toReal hat]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.2 (by
        dsimp [δ]
        linarith)
    filter_upwards [(tendsto_order.mp hsmall).2 c hc, hlarge, eventually_gt_atTop (1 : ℕ)]
      with n hs hl hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hnorm : 0 < (n : ℝ) * Real.log n :=
      mul_pos ((zero_lt_one : (0 : ℝ) < 1).trans hn') (Real.log_pos hn')
    have hthreshold : ε n * expectedNumStableMatchings n ≤ c * ((n : ℝ) * Real.log n) :=
      (div_le_iff₀ hnorm).mp (by simpa only [mul_div_assoc] using hs.le)
    exact haδ.trans_le (hl.trans (stableMatchingCountTail_antitone n hthreshold))
  · intro a ha
    exact Eventually.of_forall fun n ↦
      (prob_le_one (μ := (uniformProfile n).toMeasure)).trans_lt ha

/-- The second moment of a count minus its proposed center, divided by the
square of the chosen positive scale. -/
noncomputable def scaledCenteredCountMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a : ℝ) (T M : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (((T x - M x) / a) ^ 2) ∂μ

/-- A high-probability lower bound on the center transfers to the count
when its normalized squared deviation is small. -/
theorem measure_tail_ge_of_centeredMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {S T M : Ω → ℝ}
    (hTS : ∀ x, T x ≤ S x) (hT : Measurable T) (hM : Measurable M)
    {a d δ : ℝ} (ha : 0 < a) (hd : 0 < d) (hδ : 0 < δ) (hδ' : δ < 1)
    (hcenter : ENNReal.ofReal (1 - δ / 2) ≤ μ {x | d * a ≤ M x})
    (hmoment : scaledCenteredCountMoment μ a T M ≤ ENNReal.ofReal ((δ / 2) * (d / 2) ^ 2)) :
    ENNReal.ofReal (1 - δ) ≤ μ {x | (d / 2) * a ≤ S x} := by
  let f (x : Ω) := ENNReal.ofReal (((T x - M x) / a) ^ 2)
  let G := {x | (d / 2) * a ≤ S x}
  let E := {x | ENNReal.ofReal ((d / 2) ^ 2) ≤ f x}
  have hf : Measurable f := by unfold f; fun_prop
  have hpos : 0 < (d / 2) ^ 2 := by positivity
  have hE : μ E ≤ ENNReal.ofReal (δ / 2) := by
    calc
      _ ≤ scaledCenteredCountMoment μ a T M / ENNReal.ofReal ((d / 2) ^ 2) :=
        meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_pos.mpr hpos).ne'
          ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((δ / 2) * (d / 2) ^ 2) / ENNReal.ofReal ((d / 2) ^ 2) :=
        ENNReal.div_le_div_right hmoment _
      _ = _ := by
        rw [← ENNReal.ofReal_div_of_pos hpos, mul_div_cancel_right₀ _ hpos.ne']
  have hcover : {x | d * a ≤ M x} ⊆ G ∪ E := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl hg
    · right
      have hs : S x < (d / 2) * a := lt_of_not_ge hg
      have hdif : (T x - M x) / a ≤ -(d / 2) := by
        apply (div_le_iff₀ ha).2
        linarith [hTS x, (show d * a ≤ M x from hx)]
      apply ENNReal.ofReal_le_ofReal
      calc
        (d / 2) ^ 2 ≤ (-((T x - M x) / a)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = _ := by ring
  have hbound : ENNReal.ofReal (1 - δ / 2) ≤ μ G + ENNReal.ofReal (δ / 2) :=
    hcenter.trans ((measure_mono hcover).trans
      ((measure_union_le G E).trans (add_le_add le_rfl hE)))
  have hfin := measure_ne_top μ G
  have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) hbound
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - δ / 2),
    ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ δ / 2)] at hR
  change ENNReal.ofReal (1 - δ) ≤ μ G
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- A family of centered incidence counts in the continuous score model
implies the original conjecture tail. The center's lower scale can depend on
the allowed probability loss, but not on the desired moment error. -/
theorem lennonPittel_of_score_centered_counts
    (hcert : ∀ η : ℝ, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ e : ℝ, 0 < e →
      ∃ T M : ∀ n : ℕ, ScoreProfile n → ℝ,
        (∀ n, Measurable (T n)) ∧ (∀ n, Measurable (M n)) ∧
        (∀ n x, T n x ≤ (numStableMatchings (profileOfScores x) : ℝ)) ∧
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal (1 - η) ≤ (continuousScoreLaw n)
            {x | d * ((n : ℝ) * Real.log n) ≤ M n x} ∧
          scaledCenteredCountMoment (continuousScoreLaw n)
            ((n : ℝ) * Real.log n) (T n) (M n) ≤ ENNReal.ofReal e)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  refine lennonPittel_of_uniform_lower_scale (fun δ hδ ↦ ?_) ε hε
  by_cases hδ' : δ < 1
  · obtain ⟨d, hd, hclose⟩ := hcert (δ / 2) (by positivity)
    obtain ⟨T, M, hT, hM, hTS, hclose⟩ :=
      hclose ((δ / 2) * (d / 2) ^ 2) (by positivity)
    refine ⟨d / 2, by positivity, ?_⟩
    filter_upwards [hclose, eventually_gt_atTop (1 : ℕ)] with n hn hn'
    have hpos : (1 : ℝ) < n := by exact_mod_cast hn'
    have ha : 0 < (n : ℝ) * Real.log n :=
      mul_pos ((zero_lt_one : (0 : ℝ) < 1).trans hpos) (Real.log_pos hpos)
    have htail := measure_tail_ge_of_centeredMoment (continuousScoreLaw n)
      (hTS n) (hT n) (hM n) ha hd hδ hδ' hn.1 hn.2
    let G : Set (Profile n) :=
      {p | (d / 2) * ((n : ℝ) * Real.log n) ≤ (numStableMatchings p : ℝ)}
    have hG : MeasurableSet G := MeasurableSet.of_discrete
    change _ ≤ (uniformProfile n).toMeasure G
    rw [← (measurePreserving_profileOfScores n).map_eq,
      Measure.map_apply (measurePreserving_profileOfScores n).measurable hG]
    exact htail
  · refine ⟨1, one_pos, Eventually.of_forall fun n ↦ ?_⟩
    rw [ENNReal.ofReal_eq_zero.mpr (by linarith : 1 - δ ≤ 0)]
    exact zero_le

end LennonPittelFormalization

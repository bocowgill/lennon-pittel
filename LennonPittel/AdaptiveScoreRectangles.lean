module

public import LennonPittel.ContinuousScoreBridge
public import LennonPittel.FiniteProductDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Exact score rectangle updates

An observed comparison against an already known threshold restricts only the selected score
coordinate. A fixed finite transcript accumulates these restrictions coordinatewise. No assertion
is made here that the transcript of a particular matching algorithm has this form.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*}

/-- The measure on independent real scores, restricted separately in each coordinate. -/
noncomputable def scoreBoxLaw [Fintype ι] (box : ι → Set ℝ) : Measure (ι → ℝ) :=
  Measure.pi fun i ↦ volume.restrict (box i)

/-- Passing means that the score is strictly below the known threshold. -/
def scoreComparisonCut (threshold : ℝ) (passes : Bool) : Set ℝ :=
  if passes then Iio threshold else Ici threshold

theorem measurableSet_scoreComparisonCut (threshold : ℝ) (passes : Bool) :
    MeasurableSet (scoreComparisonCut threshold passes) := by
  cases passes <;> simp [scoreComparisonCut]

/-- One observed comparison at a selected score coordinate. -/
structure ScoreComparison (ι : Type*) where
  coord : ι
  threshold : ℝ
  passes : Bool

variable [DecidableEq ι]

/-- The allowed values for each coordinate after one comparison, without any prior restrictions. -/
def ScoreComparison.box (test : ScoreComparison ι) (i : ι) : Set ℝ :=
  if i = test.coord then scoreComparisonCut test.threshold test.passes else univ

/-- The observed outcome as an event in the score space. -/
def ScoreComparison.event (test : ScoreComparison ι) : Set (ι → ℝ) :=
  (fun x ↦ x test.coord) ⁻¹' scoreComparisonCut test.threshold test.passes

theorem ScoreComparison.measurableSet_box (test : ScoreComparison ι) (i : ι) :
    MeasurableSet (test.box i) := by
  by_cases hi : i = test.coord
  · simp [ScoreComparison.box, hi, measurableSet_scoreComparisonCut]
  · simp [ScoreComparison.box, hi]

theorem ScoreComparison.event_eq_pi (test : ScoreComparison ι) :
    test.event = univ.pi test.box := by
  ext x
  simp only [ScoreComparison.event, mem_preimage, mem_univ_pi]
  constructor
  · intro hx i
    by_cases hi : i = test.coord
    · simpa [ScoreComparison.box, hi] using hx
    · simp [ScoreComparison.box, hi]
  · intro hx
    simpa [ScoreComparison.box] using hx test.coord

/-- The restrictions from a fixed list of outcomes, intersected in each coordinate. -/
def scoreTranscriptBox : List (ScoreComparison ι) → ι → Set ℝ
  | [] => fun _ ↦ univ
  | test :: rest => fun i ↦ test.box i ∩ scoreTranscriptBox rest i

/-- The event that every comparison in a fixed transcript has the recorded outcome. -/
def scoreTranscriptEvent : List (ScoreComparison ι) → Set (ι → ℝ)
  | [] => univ
  | test :: rest => test.event ∩ scoreTranscriptEvent rest

theorem measurableSet_scoreTranscriptBox (trace : List (ScoreComparison ι)) (i : ι) :
    MeasurableSet (scoreTranscriptBox trace i) := by
  induction trace with
  | nil => exact MeasurableSet.univ
  | cons test _ ih => exact (test.measurableSet_box i).inter ih

theorem scoreTranscriptEvent_eq_pi (trace : List (ScoreComparison ι)) :
    scoreTranscriptEvent trace = univ.pi (scoreTranscriptBox trace) := by
  induction trace with
  | nil => simp [scoreTranscriptEvent, scoreTranscriptBox]
  | cons test rest ih =>
    simp only [scoreTranscriptEvent, scoreTranscriptBox, test.event_eq_pi, ih, Set.pi_inter_distrib]

variable [Fintype ι]

theorem measurableSet_scoreTranscriptEvent (trace : List (ScoreComparison ι)) :
    MeasurableSet (scoreTranscriptEvent trace) := by
  rw [scoreTranscriptEvent_eq_pi]
  exact MeasurableSet.univ_pi (measurableSet_scoreTranscriptBox trace)

/-- An exact restriction of the product measure after the outcomes of a fixed transcript. -/
theorem scoreBoxLaw_restrict_transcript (box : ι → Set ℝ)
    (trace : List (ScoreComparison ι)) :
    (scoreBoxLaw box).restrict (scoreTranscriptEvent trace) =
      scoreBoxLaw (fun i ↦ scoreTranscriptBox trace i ∩ box i) := by
  rw [scoreTranscriptEvent_eq_pi]
  unfold scoreBoxLaw
  rw [Measure.restrict_pi_pi]
  congr 1
  funext i
  exact Measure.restrict_restrict (measurableSet_scoreTranscriptBox trace i)

/-- One passing or failing comparison changes only the selected factor. -/
theorem scoreBoxLaw_restrict_comparison (box : ι → Set ℝ) (test : ScoreComparison ι) :
    (scoreBoxLaw box).restrict test.event =
      scoreBoxLaw (fun i ↦ if i = test.coord
        then scoreComparisonCut test.threshold test.passes ∩ box i else box i) := by
  rw [show test.event = scoreTranscriptEvent [test] by simp [scoreTranscriptEvent],
    scoreBoxLaw_restrict_transcript]
  congr 1
  funext i
  by_cases hi : i = test.coord <;> simp [scoreTranscriptBox, ScoreComparison.box, hi]

omit [DecidableEq ι] in
/-- Conditioning on a positive-mass rectangle normalizes the factors separately. -/
theorem cond_pi_scoreBox (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (box : ι → Set ℝ) (hbox : ∀ i, ν i (box i) ≠ 0) :
    ProbabilityTheory.cond (Measure.pi ν) (univ.pi box) =
      Measure.pi (fun i ↦ ProbabilityTheory.cond (ν i) (box i)) := by
  let ν' (i : ι) := (ν i).restrict (box i)
  have hν' (i : ι) : ν' i univ ≠ 0 := by simpa [ν'] using hbox i
  have hprod : (∏ i, ν i (box i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ hbox i
  have hprodTop : (∏ i, ν i (box i)) ≠ ⊤ := by
    rw [← Measure.pi_pi]
    exact measure_ne_top _ _
  change ((Measure.pi ν) (univ.pi box))⁻¹ •
    (Measure.pi ν).restrict (univ.pi box) = _
  rw [Measure.pi_pi, Measure.restrict_pi_pi]
  change (∏ i, ν i (box i))⁻¹ • Measure.pi ν' = _
  rw [pi_eq_prod_smul_pi_normalized ν' hν']
  simp only [ν', Measure.restrict_apply_univ, smul_smul,
    ENNReal.inv_mul_cancel hprod hprodTop, one_smul, ProbabilityTheory.cond]

/-- The normalized posterior of a fixed comparison transcript is a product of coordinate laws. -/
theorem cond_pi_scoreTranscript (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (trace : List (ScoreComparison ι)) (htrace : ∀ i, ν i (scoreTranscriptBox trace i) ≠ 0) :
    ProbabilityTheory.cond (Measure.pi ν) (scoreTranscriptEvent trace) =
      Measure.pi (fun i ↦ ProbabilityTheory.cond (ν i) (scoreTranscriptBox trace i)) := by
  rw [scoreTranscriptEvent_eq_pi]
  exact cond_pi_scoreBox ν _ htrace

/-- A measurable observation of a selected coordinate restricts that factor alone. -/
theorem scoreBoxLaw_restrict_observation {α : Type*} [MeasurableSpace α]
    (box : ι → Set ℝ) (i : ι) (observe : ℝ → α) (hobserve : Measurable observe)
    (seen : Set α) (hseen : MeasurableSet seen) :
    (scoreBoxLaw box).restrict ((fun x ↦ observe (x i)) ⁻¹' seen) =
      scoreBoxLaw (fun j ↦ if j = i then (observe ⁻¹' seen) ∩ box j else box j) := by
  have hset : (fun x : ι → ℝ ↦ observe (x i)) ⁻¹' seen =
      univ.pi (Function.update (fun _ ↦ univ) i (observe ⁻¹' seen)) := by
    rw [Set.univ_pi_update_univ]
    rfl
  rw [hset]
  unfold scoreBoxLaw
  rw [Measure.restrict_pi_pi]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simpa [Function.update_self] using
      (Measure.restrict_restrict (μ := (volume : Measure ℝ)) (t := box i)
        (hobserve hseen))
  · simp [hj]

/-- The comparisons selected by a policy along a prescribed future outcome sequence.
The policy receives the past outcomes with the newest one first. -/
def scorePolicyTranscript (next : List Bool → ι × ℝ) (past : List Bool) :
    List Bool → List (ScoreComparison ι)
  | [] => []
  | b :: future =>
    ⟨(next past).1, (next past).2, b⟩ :: scorePolicyTranscript next (b :: past) future

/-- The event that a prescribed sequence is generated by a score-comparison policy. -/
def scorePolicyHistoryEvent (next : List Bool → ι × ℝ) (past : List Bool) :
    List Bool → Set (ι → ℝ)
  | [] => univ
  | b :: future =>
    {x | (if x (next past).1 < (next past).2 then true else false) = b} ∩
      scorePolicyHistoryEvent next (b :: past) future

omit [DecidableEq ι] [Fintype ι] in
theorem scorePolicyHistoryEvent_eq_transcript (next : List Bool → ι × ℝ)
    (past future : List Bool) :
    scorePolicyHistoryEvent next past future =
      scoreTranscriptEvent (scorePolicyTranscript next past future) := by
  induction future generalizing past with
  | nil => rfl
  | cons b future ih =>
    simp only [scorePolicyHistoryEvent, scorePolicyTranscript, scoreTranscriptEvent, ih]
    congr 1
    ext x
    by_cases h : x (next past).1 < (next past).2 <;> cases b <;>
      simp [ScoreComparison.event, scoreComparisonCut, h, not_lt.mp]

/-- A fixed branch of an adaptive comparison policy gives coordinatewise restrictions. -/
theorem scoreBoxLaw_restrict_policyHistory (box : ι → Set ℝ) (next : List Bool → ι × ℝ)
    (past future : List Bool) :
    (scoreBoxLaw box).restrict (scorePolicyHistoryEvent next past future) =
      scoreBoxLaw (fun i ↦ scoreTranscriptBox (scorePolicyTranscript next past future) i ∩
        box i) := by
  rw [scorePolicyHistoryEvent_eq_transcript, scoreBoxLaw_restrict_transcript]

/-- The positive-mass posterior of an adaptive branch remains a product of conditional laws. -/
theorem cond_pi_scorePolicyHistory (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (next : List Bool → ι × ℝ) (past future : List Bool)
    (h : ∀ i, ν i (scoreTranscriptBox (scorePolicyTranscript next past future) i) ≠ 0) :
    ProbabilityTheory.cond (Measure.pi ν) (scorePolicyHistoryEvent next past future) =
      Measure.pi (fun i ↦ ProbabilityTheory.cond (ν i)
        (scoreTranscriptBox (scorePolicyTranscript next past future) i)) := by
  rw [scorePolicyHistoryEvent_eq_transcript]
  exact cond_pi_scoreTranscript ν _ h

omit [DecidableEq ι] in
/-- The selected score marginal of a positive-mass rectangular posterior is its own conditional
law. -/
theorem map_eval_cond_pi_scoreBox (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (box : ι → Set ℝ) (hbox : ∀ i, ν i (box i) ≠ 0) (i : ι) :
    Measure.map (fun x ↦ x i) (ProbabilityTheory.cond (Measure.pi ν) (univ.pi box)) =
      ProbabilityTheory.cond (ν i) (box i) := by
  rw [cond_pi_scoreBox ν box hbox]
  have (j : ι) : IsProbabilityMeasure (ProbabilityTheory.cond (ν j) (box j)) :=
    ProbabilityTheory.cond_isProbabilityMeasure (hbox j)
  exact (measurePreserving_eval (fun j ↦ ProbabilityTheory.cond (ν j) (box j)) i).map_eq

/-- The cached uniform score on `(0,u)`, represented as normalized restricted volume. -/
noncomputable def cachedUniformScoreLaw (u : ℝ) : Measure ℝ :=
  (ENNReal.ofReal u)⁻¹ • volume.restrict (Ioo 0 u)

theorem isProbabilityMeasure_cachedUniformScoreLaw {u : ℝ} (hu : 0 < u) :
    IsProbabilityMeasure (cachedUniformScoreLaw u) := by
  constructor
  rw [cachedUniformScoreLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Real.volume_Ioo, sub_zero, ENNReal.inv_mul_cancel (by simpa using hu) ENNReal.ofReal_ne_top]

theorem cachedUniformScoreLaw_restrict_pass {u v : ℝ} (hvu : v ≤ u) :
    (cachedUniformScoreLaw u).restrict (Iio v) =
      (ENNReal.ofReal u)⁻¹ • volume.restrict (Ioo 0 v) := by
  have hcut : Iio v ∩ Ioo 0 u = Ioo (0 : ℝ) v := by
    ext x
    exact ⟨fun hx ↦ ⟨hx.2.1, hx.1⟩, fun hx ↦ ⟨hx.2, hx.1, hx.2.trans_le hvu⟩⟩
  rw [cachedUniformScoreLaw, Measure.restrict_smul, Measure.restrict_restrict measurableSet_Iio,
    hcut]

/-- Under a cached uniform score on `(0,u)`, tightening to `0 < v ≤ u` passes with mass `v/u`. -/
theorem cachedUniformScoreLaw_pass {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    cachedUniformScoreLaw u (Iio v) = ENNReal.ofReal (v / u) := by
  rw [← Measure.restrict_apply_univ, cachedUniformScoreLaw_restrict_pass hvu,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_div_of_pos (hv.trans_le hvu), div_eq_mul_inv, mul_comm]

/-- Given a pass, the cached score is uniform on the tightened interval `(0,v)`. -/
theorem cond_cachedUniformScoreLaw_pass {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    ProbabilityTheory.cond (cachedUniformScoreLaw u) (Iio v) = cachedUniformScoreLaw v := by
  have hnv : ENNReal.ofReal v ≠ 0 := by simpa using hv
  have hmass : cachedUniformScoreLaw u (Iio v) ≠ 0 := by
    rw [cachedUniformScoreLaw_pass hv hvu]
    simpa using div_pos hv (hv.trans_le hvu)
  have hmassTop : cachedUniformScoreLaw u (Iio v) ≠ ⊤ := by
    rw [cachedUniformScoreLaw_pass hv hvu]
    exact ENNReal.ofReal_ne_top
  have hscale : (cachedUniformScoreLaw u).restrict (Iio v) =
      cachedUniformScoreLaw u (Iio v) • cachedUniformScoreLaw v := by
    rw [cachedUniformScoreLaw_restrict_pass hvu, cachedUniformScoreLaw_pass hv hvu,
      cachedUniformScoreLaw, ENNReal.ofReal_div_of_pos (hv.trans_le hvu), div_eq_mul_inv,
      smul_smul, mul_comm (ENNReal.ofReal v) ((ENNReal.ofReal u)⁻¹), mul_assoc,
      ENNReal.mul_inv_cancel hnv ENNReal.ofReal_ne_top, mul_one]
  change (cachedUniformScoreLaw u (Iio v))⁻¹ •
      (cachedUniformScoreLaw u).restrict (Iio v) = _
  rw [hscale, smul_smul, ENNReal.inv_mul_cancel hmass hmassTop, one_smul]

/-- Dividing a cached score by its positive endpoint gives the unit score law. -/
theorem map_cachedUniformScoreLaw_div {v : ℝ} (hv : 0 < v) :
    Measure.map (fun x ↦ x / v) (cachedUniformScoreLaw v) = unitScoreLaw := by
  have hmeas : Measurable (fun x : ℝ ↦ x / v) := measurable_id.div_const v
  have hpre : (fun x : ℝ ↦ x / v) ⁻¹' Ioo (0 : ℝ) 1 = Ioo 0 v := by
    ext x
    simp only [mem_preimage, mem_Ioo, div_pos_iff_of_pos_right hv, div_lt_iff₀ hv, one_mul]
  have hmap : Measure.map (fun x ↦ x / v) volume = ENNReal.ofReal v • volume := by
    simp only [div_eq_mul_inv]
    rw [Real.map_volume_mul_right (inv_ne_zero hv.ne'), inv_inv, abs_of_pos hv]
  rw [cachedUniformScoreLaw, Measure.map_smul _ hmeas.aemeasurable, ← hpre,
    ← Measure.restrict_map hmeas measurableSet_Ioo, hmap, Measure.restrict_smul, smul_smul,
    ENNReal.inv_mul_cancel (by simpa using hv) ENNReal.ofReal_ne_top, one_smul, unitScoreLaw,
    Measure.restrict_congr_set Ioo_ae_eq_Icc]

omit [DecidableEq ι] in
/-- Normalizing all cached scores coordinatewise gives the joint independent unit score law. -/
theorem measurePreserving_normalize_cachedUniformScoreLaw (upper : ι → ℝ)
    (hupper : ∀ i, 0 < upper i) :
    MeasurePreserving (fun (x : ι → ℝ) i ↦ x i / upper i)
      (Measure.pi fun i ↦ cachedUniformScoreLaw (upper i))
      (Measure.pi fun _ : ι ↦ unitScoreLaw) := by
  have hmeas (i : ι) : Measurable (fun x : ℝ ↦ x / upper i) := measurable_id.div_const _
  have (i : ι) : SigmaFinite
      (Measure.map (fun x : ℝ ↦ x / upper i) (cachedUniformScoreLaw (upper i))) := by
    rw [map_cachedUniformScoreLaw_div (hupper i)]
    infer_instance
  refine ⟨Measurable.of_eval (fun i ↦ (hmeas i).comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.pi_map_pi (fun i ↦ (hmeas i).aemeasurable)]
  simp only [map_cachedUniformScoreLaw_div (hupper _)]

omit [DecidableEq ι] in
/-- Normalized ratios on a chosen support have the independent unit score law, jointly and
independently of any measurable observation of the complementary scores. -/
theorem measurePreserving_normalize_cachedUniformScoreLaw_support_and_observe
    {α : Type*} [MeasurableSpace α] (upper : ι → ℝ) (hupper : ∀ i, 0 < upper i)
    (p : ι → Prop) [DecidablePred p] (observe : ({i // ¬ p i} → ℝ) → α)
    (hobs : Measurable observe) :
    MeasurePreserving
      (fun x : ι → ℝ ↦ (fun i : Subtype p ↦ x i / upper i, observe fun i ↦ x i))
      (Measure.pi fun i ↦ cachedUniformScoreLaw (upper i))
      ((Measure.pi fun _ : Subtype p ↦ unitScoreLaw).prod
        (Measure.map observe (Measure.pi fun i : {i // ¬ p i} ↦
          cachedUniformScoreLaw (upper i)))) := by
  let ν (i : ι) := cachedUniformScoreLaw (upper i)
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    isProbabilityMeasure_cachedUniformScoreLaw (hupper i)
  exact ((measurePreserving_normalize_cachedUniformScoreLaw
      (fun i : Subtype p ↦ upper i) (fun i ↦ hupper i)).prod
    (show MeasurePreserving observe _ _ from ⟨hobs, rfl⟩)).comp
    (measurePreserving_piEquivPiSubtypeProd ν p)

omit [DecidableEq ι] in
/-- Normalized ratios on a chosen support have the independent unit score law. -/
theorem measurePreserving_normalize_cachedUniformScoreLaw_support
    (upper : ι → ℝ) (hupper : ∀ i, 0 < upper i) (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun (x : ι → ℝ) (i : Subtype p) ↦ x i / upper i)
      (Measure.pi fun i ↦ cachedUniformScoreLaw (upper i))
      (Measure.pi fun _ : Subtype p ↦ unitScoreLaw) := by
  let ν (i : ι) := cachedUniformScoreLaw (upper i)
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    isProbabilityMeasure_cachedUniformScoreLaw (hupper i)
  exact (measurePreserving_normalize_cachedUniformScoreLaw
      (fun i : Subtype p ↦ upper i) (fun i ↦ hupper i)).comp
    (measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd ν p))

/-- After a passing comparison, the revealed score divided by the new endpoint is uniform. -/
theorem map_cond_cachedUniformScoreLaw_pass_div {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    Measure.map (fun x ↦ x / v) (ProbabilityTheory.cond (cachedUniformScoreLaw u) (Iio v)) =
      unitScoreLaw := by
  rw [cond_cachedUniformScoreLaw_pass hv hvu, map_cachedUniformScoreLaw_div hv]

/-- A pass in one coordinate of a cached product tightens exactly that coordinate's endpoint. -/
theorem cond_pi_cachedUniformScoreLaw_pass (upper : ι → ℝ) (hupper : ∀ i, 0 < upper i)
    (i : ι) {v : ℝ} (hv : 0 < v) (hvu : v ≤ upper i) :
    ProbabilityTheory.cond (Measure.pi fun j ↦ cachedUniformScoreLaw (upper j))
      ((fun x : ι → ℝ ↦ x i) ⁻¹' Iio v) =
        Measure.pi (fun j ↦ cachedUniformScoreLaw (if j = i then v else upper j)) := by
  let test : ScoreComparison ι := ⟨i, v, true⟩
  have (j : ι) : IsProbabilityMeasure (cachedUniformScoreLaw (upper j)) :=
    isProbabilityMeasure_cachedUniformScoreLaw (hupper j)
  have hbox (j : ι) : cachedUniformScoreLaw (upper j) (test.box j) ≠ 0 := by
    by_cases hj : j = i
    · subst j
      simp [test, ScoreComparison.box, scoreComparisonCut, cachedUniformScoreLaw_pass hv hvu,
        div_pos hv (hupper i)]
    · simp [test, ScoreComparison.box, hj]
  change ProbabilityTheory.cond (Measure.pi fun j ↦ cachedUniformScoreLaw (upper j))
    test.event = _
  rw [test.event_eq_pi, cond_pi_scoreBox _ _ hbox]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simpa [test, ScoreComparison.box, scoreComparisonCut] using
      cond_cachedUniformScoreLaw_pass hv hvu
  · simp [test, ScoreComparison.box, hj]

/-- Under the passing product posterior, the normalized selected score has the unit score law. -/
theorem map_div_cond_pi_cachedUniformScoreLaw_pass (upper : ι → ℝ)
    (hupper : ∀ i, 0 < upper i) (i : ι) {v : ℝ} (hv : 0 < v) (hvu : v ≤ upper i) :
    Measure.map (fun x : ι → ℝ ↦ x i / v)
      (ProbabilityTheory.cond (Measure.pi fun j ↦ cachedUniformScoreLaw (upper j))
        ((fun x : ι → ℝ ↦ x i) ⁻¹' Iio v)) = unitScoreLaw := by
  rw [cond_pi_cachedUniformScoreLaw_pass upper hupper i hv hvu]
  let ν (j : ι) := cachedUniformScoreLaw (if j = i then v else upper j)
  have (j : ι) : IsProbabilityMeasure (ν j) :=
    isProbabilityMeasure_cachedUniformScoreLaw (by by_cases hj : j = i <;> simp [hj, hv, hupper])
  have hmeas : Measurable (fun x : ℝ ↦ x / v) := measurable_id.div_const v
  change Measure.map ((fun x : ℝ ↦ x / v) ∘ Function.eval i) (Measure.pi ν) = _
  rw [← Measure.map_map hmeas (measurable_pi_apply i), (measurePreserving_eval ν i).map_eq]
  simpa [ν] using map_cachedUniformScoreLaw_div hv

end LennonPittelFormalization

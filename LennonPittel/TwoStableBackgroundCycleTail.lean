module

public import LennonPittel.CommonForwardCycleMoments
public import LennonPittel.TwoStableCommonRows
public import LennonPittel.PivotResidualEstimate

/-!
# Too few background cycles at a fixed jointly stable pair

The cycle count is evaluated at the second matching, using only men
whose partners agree. The bound conditions on the two spouse arrays
and joint stability, not on either matching being a toggle endpoint.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {n : ℕ} {μ ν : Matching n}

/-- Labels with a common partner in the two matchings. -/
def jointBackgroundLabels (μ ν : Matching n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ μ i = ν i

@[simp]
theorem mem_jointBackgroundLabels {i : Fin n} :
    i ∈ jointBackgroundLabels μ ν ↔ μ i = ν i := by
  simp [jointBackgroundLabels]

/-- The total of the female spouse scores in the second matching. -/
def jointBackgroundFemaleTotal (d : JointSpouseScores μ ν) : ℝ :=
  ∑ j : Fin n, jointWomanSpouseScoreRight d (ν j)

/-- Normalized female spouse scores, indexed by their husbands in the second matching. -/
noncomputable def jointBackgroundWeight (d : JointSpouseScores μ ν) (j : Fin n) : ℝ :=
  jointWomanSpouseScoreRight d (ν j) / jointBackgroundFemaleTotal d

/-- The uniform relative error used for the independent common forward rows. -/
noncomputable def jointBackgroundArcError (d : JointSpouseScores μ ν) (X P : ℝ) : ℝ :=
  2 * X + 4 * P + Real.exp (-jointBackgroundFemaleTotal d / 2)

@[simp]
theorem jointBackgroundFemaleTotal_split (μ ν : Matching n) (x : ScoreProfile n) :
    jointBackgroundFemaleTotal (splitTwoMatchingScores μ ν x).1 = femaleSpouseTotal x ν := by
  rw [femaleSpouseTotal_eq_sum_byHusband]
  unfold jointBackgroundFemaleTotal
  exact Finset.sum_congr rfl fun j _ ↦ jointWomanSpouseScoreRight_split μ ν x (ν j)

@[simp]
theorem jointBackgroundWeight_split (μ ν : Matching n) (x : ScoreProfile n) (j : Fin n) :
    jointBackgroundWeight (splitTwoMatchingScores μ ν x).1 j =
      femaleSpouseScore x ν (ν j) / femaleSpouseTotal x ν := by
  rw [jointBackgroundWeight, jointBackgroundFemaleTotal_split,
    jointWomanSpouseScoreRight_split, femaleSpouseScore]

theorem measurable_jointBackgroundFemaleTotal (μ ν : Matching n) :
    Measurable (jointBackgroundFemaleTotal (μ := μ) (ν := ν)) :=
  Finset.measurable_sum _ fun _ _ ↦ measurable_snd.comp (measurable_pi_apply _)

theorem measurable_jointBackgroundWeight (μ ν : Matching n) (j : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointBackgroundWeight d j) :=
  (measurable_snd.comp (measurable_pi_apply _)).div (measurable_jointBackgroundFemaleTotal μ ν)

/-- The quantitative geometric hypotheses needed on a marked score sector. -/
structure HasJointBackgroundGeometry (d : JointSpouseScores μ ν) (L : ℕ) (X P : ℝ) : Prop where
  total_pos : 0 < jointBackgroundFemaleTotal d
  male_le : ∀ i, jointManSpouseScoreRight d i ≤ X
  weight_le : ∀ i, jointBackgroundWeight d i ≤ P
  arc_loss : (L : ℝ) * jointBackgroundArcError d X P ≤ 1 / 100
  label_loss : commonForwardLabelLoss (jointBackgroundLabels μ ν) (jointBackgroundWeight d) L ≤
    1 / 100

/-- The normalized weights are nonnegative on the unit-score domain. -/
theorem jointBackgroundWeight_nonneg (d : JointSpouseScores μ ν)
    (hR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1)
    (hY : 0 < jointBackgroundFemaleTotal d) (i : Fin n) :
    0 ≤ jointBackgroundWeight d i := div_nonneg (hR _).1 hY.le

/-- A positive total normalizes the weights to a probability vector. -/
theorem sum_jointBackgroundWeight (d : JointSpouseScores μ ν)
    (hY : 0 < jointBackgroundFemaleTotal d) : ∑ i, jointBackgroundWeight d i = 1 := by
  unfold jointBackgroundWeight
  rw [← Finset.sum_div]
  exact div_self hY.ne'

/-- On the spouse-score sector, the conditional finite successor graph has
few common-label short cycles with probability at most `1200 / log L`. -/
theorem jointOffSpouseProbabilityLaw_fewCommonSuccessorCycles_le
    (d : JointSpouseScores μ ν) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X P : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hsmall : X + 2 * P ≤ 1 / 2)
    (hgeo : HasJointBackgroundGeometry d L X P)
    (hmL : ∀ i, jointManSpouseScoreLeft d i ∈ Ico 0 1)
    (hmR : ∀ i, jointManSpouseScoreRight d i ∈ Ico 0 1)
    (hfL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hfR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointOffSpouseProbabilityLaw d {v |
      (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) : ℝ) <
        (9 / 10 : ℝ) * Real.log (L : ℝ)} ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  classical
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  let C := jointBackgroundLabels μ ν
  let p := jointBackgroundWeight d
  let δ := jointBackgroundArcError d X P
  let r := jointCommonSuccessorLaw d
  have hpos := (jointOffSpouseScoreLaw_nonblocking_pos d hmL hmR).ne'
  let (i : Fin n) : IsProbabilityMeasure (r i) :=
    jointCommonSuccessorLaw_isProbabilityMeasure d hpos i
  have hp : ∀ i, 0 ≤ p i := jointBackgroundWeight_nonneg d hfR hgeo.total_pos
  have hδ0 : 0 ≤ δ := by
    unfold δ jointBackgroundArcError
    positivity
  have hδ : δ ∈ Icc 0 1 := by
    have hL' : 1 ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
    have hh : δ ≤ (L : ℝ) * δ := le_mul_of_one_le_left hδ0 hL'
    exact ⟨hδ0, hh.trans (hgeo.arc_loss.trans (by norm_num))⟩
  have harc : CommonForwardArcBounds r C p δ := by
    intro i hi j _ hij
    let ic : CommonMan μ ν := ⟨i, mem_jointBackgroundLabels.mp hi⟩
    let jc : CommonRowCandidate ic := ⟨j, hij⟩
    have h := jointCommonSuccessorLaw_some_uniform d ic jc (hmR i) hfL hfR
      (hgeo.male_le i) hsmall hgeo.total_pos hgeo.weight_le
    change ENNReal.ofReal ((1 - δ) * p j) ≤ (r i) {some j} ∧
      (r i) {some j} ≤ ENNReal.ofReal ((1 + δ) * p j) at h
    have hlo : 0 ≤ (1 - δ) * p j := mul_nonneg (sub_nonneg.mpr hδ.2) (hp j)
    have hhi : 0 ≤ (1 + δ) * p j := mul_nonneg (by linarith only [hδ0]) (hp j)
    exact ⟨by simpa only [ENNReal.toReal_ofReal hlo, measureReal_def] using
      ENNReal.toReal_mono (measure_ne_top (r i) {some j}) h.1,
      by simpa only [ENNReal.toReal_ofReal hhi, measureReal_def] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2⟩
  let E : Set (Fin n → Option (Fin n)) := {f | (commonForwardCycleCount C L f : ℝ) <
    (9 / 10 : ℝ) * Real.log (L : ℝ)}
  change jointOffSpouseProbabilityLaw d (jointCommonSuccessors d ⁻¹' E) ≤ _
  rw [(measurePreserving_jointCommonSuccessors d hpos).measure_preimage
    (MeasurableSet.of_discrete : MeasurableSet E).nullMeasurableSet]
  exact measure_lt_commonForwardCycleCount_le r C hL p hp
    (sum_jointBackgroundWeight d hgeo.total_pos) hδ harc hgeo.arc_loss hgeo.label_loss hlog

/-- The common-row count agrees almost surely with the exposed rotation count
computed in the reconstructed preference profile. -/
theorem ae_jointSpouse_ae_commonForwardCycleCount_eq (μ ν : Matching n) (L : ℕ) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, ∀ᵐ v ∂jointOffSpouseProbabilityLaw d,
      d ∈ jointMarkedNonblocking μ ν →
        commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) =
          (backgroundShortCycles (profileOfScores ((splitTwoMatchingScores μ ν).symm
            (d, v))) μ ν L).card := by
  classical
  filter_upwards [ae_jointSpouse_ae_commonCycle_iff_exposed μ ν] with d hd
  filter_upwards [hd] with v hv
  intro hmark
  unfold commonForwardCycleCount realizedForwardCycleCount backgroundShortCycles exposedShortCycles
  congr 1
  ext σ
  simp only [Finset.mem_filter, mem_commonForwardCycles, Finset.mem_Icc, Finset.mem_univ, true_and]
  have hC : σ.support ⊆ jointBackgroundLabels μ ν ↔
      Disjoint σ.support (relativeMenPermutation μ ν).support := by
    rw [Finset.disjoint_left]
    refine ⟨fun h i hi hrel ↦ Equiv.Perm.mem_support.mp hrel ?_, fun h i hi ↦ ?_⟩
    · simpa only [relativeMenPermutation, Equiv.trans_apply, ν.symm_apply_eq] using
        mem_jointBackgroundLabels.mp (h hi)
    · simpa only [mem_jointBackgroundLabels, relativeMenPermutation, Equiv.trans_apply,
        ν.symm_apply_eq] using Equiv.Perm.notMem_support.mp (h hi)
  constructor
  · rintro ⟨⟨hcyc, hsub, -, hlen⟩, hreal⟩
    exact ⟨⟨(hv hmark σ hcyc (fun i hi ↦ mem_jointBackgroundLabels.mp (hsub hi))).mp hreal.2,
      hlen⟩, hC.mp hsub⟩
  · rintro ⟨⟨hexp, hlen⟩, hdis⟩
    have hsub := hC.mpr hdis
    exact ⟨⟨hexp.1, hsub, hexp.1.two_le_card_support, hlen⟩, hexp.1,
      (hv hmark σ hexp.1 (fun i hi ↦ mem_jointBackgroundLabels.mp (hsub hi))).mpr hexp⟩

/-- Almost-everywhere conditional estimate for too few actual exposed common cycles. -/
theorem ae_jointOffSpouseProbabilityLaw_backgroundShortCycleException_le
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X P : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hsmall : X + 2 * P ≤ 1 / 2) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ jointMarkedNonblocking μ ν →
      HasJointBackgroundGeometry d L X P →
      jointOffSpouseProbabilityLaw d ((fun v ↦ (splitTwoMatchingScores μ ν).symm (d, v)) ⁻¹'
        backgroundShortCycleException μ ν L) ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  filter_upwards [ae_jointSpouse_thresholds μ ν,
    ae_jointSpouse_ae_commonForwardCycleCount_eq μ ν L] with d hd hcount
  intro hmark hgeo
  have heq : ((fun v ↦ (splitTwoMatchingScores μ ν).symm (d, v)) ⁻¹'
        backgroundShortCycleException μ ν L) =ᵐ[jointOffSpouseProbabilityLaw d]
      {v | (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) :
        ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)} := by
    filter_upwards [hcount] with v hv
    apply propext
    change ((backgroundShortCycles (profileOfScores ((splitTwoMatchingScores μ ν).symm
      (d, v))) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ) ↔
        (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) :
          ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)
    rw [hv hmark]
  rw [measure_congr heq]
  exact jointOffSpouseProbabilityLaw_fewCommonSuccessorCycles_le d hL hlog hX hP hsmall hgeo
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

/-- A fixed pair's background exception costs at most `1200 / log L` times
its joint-stability mass on the marked score sector. The sector may include a
fixed orientation test, but it does not constrain the unmarked cells. -/
theorem continuousScoreLaw_inter_backgroundShortCycleException_le
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X P : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hsmall : X + 2 * P ≤ 1 / 2)
    {D : Set (JointSpouseScores μ ν)} (hD : MeasurableSet D)
    (hgeo : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ D → HasJointBackgroundGeometry d L X P) :
    let A := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ D}
    continuousScoreLaw n (A ∩ backgroundShortCycleException μ ν L) ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) * continuousScoreLaw n A := by
  let e := splitTwoMatchingScores μ ν
  let A := {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (e x).1 ∈ D}
  let E := backgroundShortCycleException μ ν L
  let g := E.indicator (1 : ScoreProfile n → ℝ≥0∞)
  let c := ENNReal.ofReal (1200 / Real.log (L : ℝ))
  let W (d : JointSpouseScores μ ν) := jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d)
  have hE : MeasurableSet E := measurableSet_backgroundShortCycleException μ ν L
  have hg : Measurable g := measurable_const.indicator hE
  have hW (d : JointSpouseScores μ ν) :
      (∫⁻ _v, (1 : ℝ≥0∞) ∂(Measure.pi (jointOffSpouseCellLaw d))) = W d := by
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking, lintegral_const, one_mul,
      Measure.restrict_apply_univ]
  have hA : continuousScoreLaw n A =
      ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, W d ∂jointSpouseScoreLaw μ ν := by
    calc
      _ = ∫⁻ _x in A, (1 : ℝ≥0∞) ∂continuousScoreLaw n := by
        rw [lintegral_const, one_mul, Measure.restrict_apply_univ]
      _ = ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, ∫⁻ _v, (1 : ℝ≥0∞)
          ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν :=
        continuousScoreLaw_lintegral_twoStable μ ν hD measurable_const
      _ = _ := lintegral_congr hW
  have hb : ∀ᵐ d ∂(jointSpouseScoreLaw μ ν).restrict (D ∩ jointMarkedNonblocking μ ν),
      (∫⁻ v, g (e.symm (d, v)) ∂(Measure.pi (jointOffSpouseCellLaw d))) ≤ c * W d := by
    rw [ae_restrict_iff' (hD.inter (measurableSet_jointMarkedNonblocking μ ν))]
    filter_upwards [ae_jointOffSpouseProbabilityLaw_backgroundShortCycleException_le μ ν
      hL hlog hX hP hsmall, ae_jointSpouse_thresholds μ ν, hgeo] with d hd hu hgd hmem
    have hpos := (jointOffSpouseScoreLaw_nonblocking_pos d hu.1 hu.2.1).ne'
    let F := (fun v ↦ e.symm (d, v)) ⁻¹' E
    have hF : MeasurableSet F := hE.preimage
      (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
    have hsec :
        (fun v ↦ g (e.symm (d, v))) =
          F.indicator (1 : JointOffSpouseScores μ ν → ℝ≥0∞) := by
      funext v
      change E.indicator (1 : ScoreProfile n → ℝ≥0∞) (e.symm (d, v)) =
        F.indicator (1 : JointOffSpouseScores μ ν → ℝ≥0∞) v
      by_cases h : v ∈ F
      · rw [Set.indicator_of_mem (show e.symm (d, v) ∈ E from h) _, Set.indicator_of_mem h]
        rfl
      · rw [Set.indicator_of_notMem (show e.symm (d, v) ∉ E from h) _, Set.indicator_of_notMem h]
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking,
      jointOffSpouseScoreLaw_restrict_eq_smul_probabilityLaw d hpos,
      lintegral_smul_measure, smul_eq_mul, hsec, lintegral_indicator_one hF, mul_comm]
    exact mul_le_mul_left (hd hmem.2 (hgd hmem.1)) _
  change continuousScoreLaw n (A ∩ E) ≤ c * continuousScoreLaw n A
  calc
    _ = ∫⁻ x in A, g x ∂continuousScoreLaw n := by
      change continuousScoreLaw n (A ∩ E) =
        ∫⁻ x in A, E.indicator (1 : ScoreProfile n → ℝ≥0∞) x ∂continuousScoreLaw n
      rw [lintegral_indicator_one hE, Measure.restrict_apply hE, inter_comm]
    _ = ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, ∫⁻ v, g (e.symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d)) ∂jointSpouseScoreLaw μ ν :=
      continuousScoreLaw_lintegral_twoStable μ ν hD hg
    _ ≤ ∫⁻ d in D ∩ jointMarkedNonblocking μ ν, c * W d ∂jointSpouseScoreLaw μ ν :=
      lintegral_mono_ae hb
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hA]

/-- Drop any extra requirements defining the residual image and apply the
fixed-pair background bound on the retained marked score sector. -/
theorem measure_scoreIncomparablePairEvent_inter_backgroundShortCycleException_le
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X P : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hsmall : X + 2 * P ≤ 1 / 2)
    {D : Set (JointSpouseScores μ ν)} (hD : MeasurableSet D)
    (hgeo : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ D → HasJointBackgroundGeometry d L X P)
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ x ∈ scoreIncomparablePairEvent Q μ ν, (splitTwoMatchingScores μ ν x).1 ∈ D) :
    continuousScoreLaw n (scoreIncomparablePairEvent Q μ ν ∩ backgroundShortCycleException μ ν L) ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) * continuousScoreLaw n
        {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ D} := by
  refine (measure_mono ?_).trans
    (continuousScoreLaw_inter_backgroundShortCycleException_le μ ν hL hlog hX hP hsmall hD hgeo)
  exact fun x hx ↦ ⟨⟨hx.1.1, hx.1.2.1, hQ x hx.1⟩, hx.2⟩

/-- Real-valued form of the marked estimate, for summing fixed-pair masses. -/
theorem measureReal_scoreIncomparablePairEvent_inter_backgroundShortCycleException_le
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X P : ℝ} (hX : 0 ≤ X) (hP : 0 ≤ P) (hsmall : X + 2 * P ≤ 1 / 2)
    {D : Set (JointSpouseScores μ ν)} (hD : MeasurableSet D)
    (hgeo : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ D → HasJointBackgroundGeometry d L X P)
    {Q : ScoreProfile n → Matching n → Matching n → Prop}
    (hQ : ∀ x ∈ scoreIncomparablePairEvent Q μ ν, (splitTwoMatchingScores μ ν x).1 ∈ D) :
    (continuousScoreLaw n).real
      (scoreIncomparablePairEvent Q μ ν ∩ backgroundShortCycleException μ ν L) ≤
        (1200 / Real.log (L : ℝ)) * (continuousScoreLaw n).real
          {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ D} := by
  have hc : 0 ≤ (1200 : ℝ) / Real.log (L : ℝ) :=
    div_nonneg (by norm_num) (by linarith only [hlog])
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (measure_scoreIncomparablePairEvent_inter_backgroundShortCycleException_le
        μ ν hL hlog hX hP hsmall hD hgeo hQ)

end LennonPittelFormalization

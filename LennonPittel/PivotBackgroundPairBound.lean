module

public import LennonPittel.PivotBackgroundGeometry
public import LennonPittel.TwoStableBackgroundCycleTail
public import LennonPittel.TwoStableFixedPairBound

/-!
# A fixed regular pair with unusually few background cycles

The conditioning sector uses only the spouse scores. Its probability is
bounded by the same labeled-pair bound used without the cycle restriction.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal

namespace LennonPittelFormalization

variable {n : ℕ} {μ ν : Matching n}

private def rightBackgroundSector (U : Finset (Fin n)) :
    Set (JointSpouseScores μ ν) :=
  {d | (∀ i, if i ∈ U then jointManSpouseScoreRight d i ≤ jointManSpouseScoreLeft d i
      else jointManSpouseScoreLeft d i ≤ jointManSpouseScoreRight d i) ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ jointBackgroundFemaleTotal d ∧
    (∀ i, jointBackgroundWeight d i ≤ backgroundWeightCeiling n) ∧
    ∀ i, jointManSpouseScoreRight d i ≤ backgroundMaleCeiling n}

private theorem measurableSet_rightBackgroundSector (U : Finset (Fin n)) :
    MeasurableSet (rightBackgroundSector (μ := μ) (ν := ν) U) := by
  have hR (i : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦
      jointManSpouseScoreRight d i) := by unfold jointManSpouseScoreRight; fun_prop
  have hL (i : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦
      jointManSpouseScoreLeft d i) := by unfold jointManSpouseScoreLeft; fun_prop
  have hOrder : MeasurableSet {d : JointSpouseScores μ ν | ∀ i,
      if i ∈ U then jointManSpouseScoreRight d i ≤ jointManSpouseScoreLeft d i
      else jointManSpouseScoreLeft d i ≤ jointManSpouseScoreRight d i} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ U
    · simpa only [hi, ite_true] using measurableSet_le (hR i) (hL i)
    · simpa only [hi, ite_false] using measurableSet_le (hL i) (hR i)
  have hWeight : MeasurableSet {d : JointSpouseScores μ ν |
      ∀ i, jointBackgroundWeight d i ≤ backgroundWeightCeiling n} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le (measurable_jointBackgroundWeight μ ν i) measurable_const
  have hMale : MeasurableSet {d : JointSpouseScores μ ν |
      ∀ i, jointManSpouseScoreRight d i ≤ backgroundMaleCeiling n} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (hR i) measurable_const
  exact hOrder.inter ((measurableSet_le measurable_const
    (measurable_jointBackgroundFemaleTotal μ ν)).inter (hWeight.inter hMale))

private theorem split_mem_rightBackgroundSector {x : ScoreProfile n} {U : Finset (Fin n)}
    (ht : ∀ row, Function.Injective (x row))
    (hU : U = worsePartnerMen (profileOfScores x) μ ν)
    (hs : InResidualEndpointScoreDomain x ν) :
    (splitTwoMatchingScores μ ν x).1 ∈ rightBackgroundSector U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hi := mem_worsePartnerMen_iff_score_lt ht μ ν i
    rw [← hU] at hi
    by_cases hm : i ∈ U
    · simp only [hm, ite_true, jointManSpouseScoreRight_split, jointManSpouseScoreLeft_split]
      exact (hi.mp hm).le
    · simp only [hm, ite_false, jointManSpouseScoreRight_split, jointManSpouseScoreLeft_split]
      exact le_of_not_gt (fun he ↦ hm (hi.mpr he))
  · rw [jointBackgroundFemaleTotal_split]
    exact hs.1
  · intro i
    rw [jointBackgroundWeight_split]
    exact hs.2.2.1 (ν i)
  · intro i
    rw [jointManSpouseScoreRight_split]
    exact hs.2.2.2 i

private theorem eq_worsePartnerMen_of_mem_rightBackgroundSector {x : ScoreProfile n}
    {U V : Finset (Fin n)} (hUV : LabeledPairOrientation μ ν U V)
    (ht : ∀ row, Function.Injective (x row))
    (hs : (splitTwoMatchingScores μ ν x).1 ∈ rightBackgroundSector U) :
    U = worsePartnerMen (profileOfScores x) μ ν := by
  ext i
  rw [mem_worsePartnerMen_iff_score_lt ht μ ν i]
  have hi := hs.1 i
  simp only [jointManSpouseScoreRight_split, jointManSpouseScoreLeft_split] at hi
  by_cases hm : i ∈ U
  · have hne : ν i ≠ μ i := by
      have hh := Equiv.Perm.mem_support.mp
        (hUV.union_support ▸ Finset.mem_union.mpr (Or.inl hm))
      exact Ne.symm ((not_congr ν.symm_apply_eq).mp (show ν.symm (μ i) ≠ i from hh))
    rw [ite_eq_left hm] at hi
    exact iff_of_true hm (lt_of_le_of_ne hi fun he ↦ hne (ht (.inl i) he))
  · rw [ite_eq_right hm] at hi
    exact iff_of_false hm (not_lt_of_ge hi)

/-- On a regular size sector, the background exception costs a factor
`1200 / log L` in the uniform labeled-pair mass bound. The further event
`E` need not be measurable with respect to the spouse scores. -/
theorem eventually_measure_backgroundException_le_labeledStablePairMassBound
    {α : ℝ} (hα : 0 < α) (hα' : α < 1 / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ {μ ν : Matching n} {U V : Finset (Fin n)},
      LabeledPairOrientation μ ν U V →
      ValidPairSizes n (U.card, V.card) → RegularPairSizes n α (U.card, V.card) →
      ∀ {E : Set (ScoreProfile n)},
        (∀ᵐ x ∂continuousScoreLaw n, x ∈ E → IsScoreStable x μ ∧ IsScoreStable x ν ∧
          U = worsePartnerMen (profileOfScores x) μ ν ∧ InResidualEndpointScoreDomain x ν) →
        continuousScoreLaw n (E ∩ backgroundShortCycleException μ ν (pivotShortCycleCutoff α n)) ≤
          ENNReal.ofReal (1200 / Real.log (pivotShortCycleCutoff α n : ℝ)) *
            ENNReal.ofReal (labeledStablePairMassBound n U.card V.card) := by
  filter_upwards [eventually_backgroundShortCutoff_large hα,
    eventually_backgroundArcError_small hα hα', eventually_backgroundLabelLoss_small hα hα',
    eventually_gt_atTop (0 : ℕ)] with n hL hArc hLabel hn
  intro μ ν U V hUV hValid hreg E hE
  let D := rightBackgroundSector (μ := μ) (ν := ν) U
  let A : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧ (splitTwoMatchingScores μ ν x).1 ∈ D}
  have hC : ((jointBackgroundLabels μ ν)ᶜ.card : ℝ) ≤
      6 * (n : ℝ) ^ (1 - α) * Real.log n := by
    rw [jointBackgroundLabels, commonLabels_compl_eq_relative_support, ← hUV.union_support,
      Finset.card_union_of_disjoint hUV.disjoint, Nat.cast_add]
    exact add_le_of_regularPairSizes hn hreg
  have hGeom : ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ D →
      HasJointBackgroundGeometry d (pivotShortCycleCutoff α n)
        (backgroundMaleCeiling n) (backgroundWeightCeiling n) := by
    filter_upwards [ae_jointSpouse_thresholds μ ν] with d hd hD
    have hY := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (1 / 10 : ℝ)).trans_le hD.2.1
    exact ⟨hY, hD.2.2.2, hD.2.2.1, (hArc.2 _ hD.2.1).2,
      hLabel _ _ hC (jointBackgroundWeight_nonneg d hd.2.2.2 hY)
        (sum_jointBackgroundWeight d hY) hD.2.2.1⟩
  have hX : 0 ≤ backgroundMaleCeiling n := by unfold backgroundMaleCeiling; positivity
  have hP : 0 ≤ backgroundWeightCeiling n := by unfold backgroundWeightCeiling; positivity
  have hA : continuousScoreLaw n A ≤ ENNReal.ofReal (labeledStablePairMassBound n U.card V.card) := by
    apply measure_stablePairSector_le_labeledStablePairMassBound hValid hUV rfl rfl
    filter_upwards [ae_injective_rows n] with x ht hx
    exact ⟨hx.1, hx.2.1, eq_worsePartnerMen_of_mem_rightBackgroundSector hUV ht hx.2.2⟩
  calc
    _ ≤ continuousScoreLaw n (A ∩ backgroundShortCycleException μ ν (pivotShortCycleCutoff α n)) := by
      apply measure_mono_ae
      filter_upwards [ae_injective_rows n, hE] with x ht hEx hx
      obtain ⟨hμ, hν, hU, hs⟩ := hEx hx.1
      exact ⟨⟨hμ, hν, split_mem_rightBackgroundSector ht hU hs⟩, hx.2⟩
    _ ≤ ENNReal.ofReal (1200 / Real.log (pivotShortCycleCutoff α n : ℝ)) *
          continuousScoreLaw n A :=
      continuousScoreLaw_inter_backgroundShortCycleException_le μ ν hL.1 hL.2 hX hP
        hArc.1 (measurableSet_rightBackgroundSector U) hGeom
    _ ≤ _ := mul_le_mul_right hA _

end LennonPittelFormalization

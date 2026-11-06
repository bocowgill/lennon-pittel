module

public import LennonPittel.PivotReverseRowLaw

/-!
# The tail of a finite reverse successor increment

A long finite successor in a normalized inactive column implies that all
available cells missed an initial interval of eligible female scores.
The independent cell laws give the exponential bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*}

/-- Some reverse successor exists and its female score increment is larger than `t`. -/
def reverseColumnLongSuccessorEvent [DecidableEq ι] (y : ℝ) (v : ι → ℝ) (t : ℝ) :
    Set (ι → ℝ × ℝ) :=
  {z | ∃ i, z ∈ reverseSuccessorColumnEvent y v i ∧ t < (z i).2 - y}

theorem measurableSet_reverseColumnLongSuccessorEvent [Fintype ι] [DecidableEq ι]
    (y : ℝ) (v : ι → ℝ) (t : ℝ) : MeasurableSet (reverseColumnLongSuccessorEvent y v t) := by
  unfold reverseColumnLongSuccessorEvent
  simp only [ofPred_exists, ofPred_and]
  exact MeasurableSet.iUnion fun i ↦
    (measurableSet_reverseSuccessorColumnEvent y v i).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply i).snd.sub_const y))

private theorem inactiveFemaleScoreLaw_ae_le_one (y : ℝ) :
    ∀ᵐ s ∂inactiveFemaleScoreLaw y, s ≤ 1 := by
  have hzero : inactiveFemaleScoreLaw y (Ioi (1 : ℝ)) = 0 := by
    rw [inactiveFemaleScoreLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi,
      unitScoreLaw, Measure.restrict_apply (measurableSet_Ioi.inter measurableSet_Ici)]
    have hempty : Ioi (1 : ℝ) ∩ Ici y ∩ Icc 0 1 = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun _ h ↦ (not_lt_of_ge h.2.2) h.1.1
    rw [hempty, measure_empty, smul_zero]
  simpa only [mem_Ioi, not_lt] using measure_eq_zero_iff_ae_notMem.mp hzero

/-- An inactive column has a finite successor of increment greater than `t` with probability
at most `exp (-t * ∑ i, v i)`. The event is null beyond the end of the score interval. -/
theorem reverseColumnLongSuccessorEvent_mass_le [Fintype ι] [DecidableEq ι] {y t : ℝ}
    {v : ι → ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hv : ∀ i, v i ∈ Icc 0 1) (ht : 0 ≤ t) :
    (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      (reverseColumnLongSuccessorEvent y v t) ≤
      ENNReal.ofReal (Real.exp (-t * ∑ i, v i)) := by
  let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  have := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  change (Measure.pi fun _ : ι ↦ ν) _ ≤ _
  by_cases hfit : t ≤ 1 - y
  · let A (j : ι) : Set (ℝ × ℝ) :=
      {q | q.1 < v j ∧ y < q.2 ∧ q.2 < y + (1 - y) * t}
    have hsub : reverseColumnLongSuccessorEvent y v t ⊆ Set.univ.pi (fun j ↦ (A j)ᶜ) := by
      rintro z ⟨i, hi, hlong⟩
      apply mem_pi.mpr
      intro j _
      change ¬ ((z j).1 < v j ∧ y < (z j).2 ∧ (z j).2 < y + (1 - y) * t)
      intro hj
      have hcut : y + (1 - y) * t ≤ y + t := by nlinarith [mul_nonneg hy0 ht]
      have hlt : (z j).2 < (z i).2 := hj.2.2.trans_le (hcut.trans (by linarith))
      have hne : j ≠ i := fun he ↦ (lt_irrefl _ (he ▸ hlt))
      exact hi.2.2 ⟨j, hne⟩ ⟨hlt, hj.1⟩
    have ht1 : t ≤ 1 := hfit.trans (sub_le_self _ hy0)
    have hmeas (j : ι) : MeasurableSet (A j) :=
      (measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const))
    have hmass (j : ι) : ν (A j)ᶜ = ENNReal.ofReal (1 - v j * t) := by
      rw [measure_compl (hmeas j) (measure_ne_top _ _), measure_univ]
      have hshort : ν (A j) = ENNReal.ofReal (v j) * ENNReal.ofReal t :=
        inactiveCell_reverseEligible_increment_mass (hv j) hy0 hy1 ⟨ht, ht1⟩
      rw [hshort, ← ENNReal.ofReal_mul (hv j).1, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (mul_nonneg (hv j).1 ht)]
    calc
      _ ≤ (Measure.pi fun _ : ι ↦ ν) (Set.univ.pi (fun j ↦ (A j)ᶜ)) := measure_mono hsub
      _ = ∏ j, ENNReal.ofReal (1 - v j * t) := by rw [Measure.pi_pi]; simp only [hmass]
      _ ≤ ∏ j, ENNReal.ofReal (Real.exp (-t * v j)) := by
        refine Finset.prod_le_prod fun j _ ↦ ENNReal.ofReal_le_ofReal ?_
        simpa only [sub_eq_add_neg, neg_mul, add_comm, mul_comm t] using
          Real.add_one_le_exp (-t * v j)
      _ = _ := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ (Real.exp_pos (-t * v j)).le),
          ← Real.exp_sum, Finset.mul_sum]
  · have hcell : ∀ᵐ q ∂ν, q.2 ≤ 1 :=
      Measure.quasiMeasurePreserving_snd.ae (inactiveFemaleScoreLaw_ae_le_one y)
    have hcol : ∀ᵐ z ∂(Measure.pi fun _ : ι ↦ ν), ∀ j, (z j).2 ≤ 1 :=
      Filter.eventually_all.2 fun j ↦
        (Measure.tendsto_eval_ae_ae (μ := fun _ : ι ↦ ν) (i := j)).eventually hcell
    have hzero : (Measure.pi fun _ : ι ↦ ν) (reverseColumnLongSuccessorEvent y v t) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hcol] with z hz
      rintro ⟨i, _, hi⟩
      exact hfit (hi.le.trans (sub_le_sub_right (hz i) y))
    rw [hzero]
    exact zero_le

end LennonPittelFormalization

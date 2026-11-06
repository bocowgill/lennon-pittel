module

public import LennonPittel.ScoreRotationHistory

/-!
# Testing a selected rotation increment against the past

The past clock values are fixed by the complementary scores once the
selected rotation is fixed. Hence a test based on the past only refines
the complementary event in the branch's product law.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped Classical

namespace LennonPittelFormalization

variable {n : ℕ}

/-- On a branch, the actual increment is the log increment of its selected scores. -/
theorem scoreWalkClock_increment_eq_on_branch (k : ℕ) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {x : ScoreProfile n} (hx : x ∈ scoreRotationBranch k μ ρ) :
    scoreWalkClock x (k + 1) - scoreWalkClock x k =
      centeredCacheLogIncrement (rotationClockUpper μ ρ) (splitRotationClockCells μ ρ x) := by
  have h := scoreWalkClock_succ_sub x k (fun j i ↦ (hx.1.2 (.inr j) i).1)
  dsimp only at h
  rw [hx.2.1, hx.2.2] at h
  exact h

/-- On a selected branch, the whole past clock is determined by the complement. -/
theorem scoreWalkClock_history_eq_on_branch_fst_eq (k : ℕ) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {x y : ScoreProfile n}
    (hx : x ∈ scoreRotationBranch k μ ρ) (hy : y ∈ scoreRotationBranch k μ ρ)
    (hfst : (splitRotationClockCells μ ρ x).1 = (splitRotationClockCells μ ρ y).1) :
    ∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j := by
  have hxrot : IsExposedRotation (profileOfScores x) μ ρ :=
    (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx.1.1 μ ρ).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hx.2.2)
  have hyrot : IsExposedRotation (profileOfScores y) μ ρ :=
    (realizesDirectedCycle_queriedSuccessorGraph_scores_iff y hy.1.1 μ ρ).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hy.2.2)
  have hfixed (r i) (hr : ¬ IsRotationClockCell μ ρ (r, i)) : y r i = x r i :=
    (congrFun hfst ⟨(r, i), hr⟩).symm
  have hbelow (i : Fin n) (hi : i ∈ ρ.support) :
      y (rotationClockCell μ ρ i).1 (rotationClockCell μ ρ i).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ i) := by
    rw [femaleSpouseScore_eq_of_splitRotationClockCells_fst_eq μ ρ hfst]
    exact hyrot.rotationClockCell_score_lt hy.1.1 hi
  intro j hj
  refine (scoreWalkClock_history_eq_of_replace_selected k hx.1.1 hy.1.1
    (ρ := ρ) ?_ ?_ ?_ j hj).symm
  · rw [hx.2.1]
    exact hxrot
  · rw [hx.2.1]
    exact hfixed
  · simpa only [hx.2.1] using hbelow

private theorem scoreWalkClock_moments_on_branch_inter (k : ℕ) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {A : Set (ScoreProfile n)} (hA : MeasurableSet A)
    (hInv : ∀ {x y}, x ∈ scoreRotationBranch k μ ρ → y ∈ scoreRotationBranch k μ ρ →
      (∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j) → (x ∈ A ↔ y ∈ A)) :
    let D := scoreRotationBranch k μ ρ ∩ A
    let Δ := fun x ↦ scoreWalkClock x (k + 1) - scoreWalkClock x k
    MemLp Δ 2 ((continuousScoreLaw n).restrict D) ∧
      (∫ x in D, Δ x ∂continuousScoreLaw n) = 0 ∧
      (∫ x in D, (Δ x)^2 ∂continuousScoreLaw n) =
        (ρ.support.card : ℝ) * (continuousScoreLaw n).real D := by
  let D := scoreRotationBranch k μ ρ ∩ A
  let Δ := fun x : ScoreProfile n ↦ scoreWalkClock x (k + 1) - scoreWalkClock x k
  let e := splitRotationClockCells μ ρ
  let P := (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
    (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)
  let E := e.symm ⁻¹' D
  let ν := P.restrict E
  let L := centeredCacheLogIncrement (rotationClockUpper μ ρ)
  have hm : MeasurableSpace.comap (Prod.fst :
      (ClockComplement μ ρ → ℝ) × (ClockSelected μ ρ → ℝ) →
        (ClockComplement μ ρ → ℝ))
      inferInstance ≤ MeasurableSpace.prod
      (inferInstance : MeasurableSpace (ClockComplement μ ρ → ℝ))
      (inferInstance : MeasurableSpace (ClockSelected μ ρ → ℝ)) :=
    measurable_fst.comap_le
  have hD : MeasurableSet D := (measurableSet_scoreRotationBranch k μ ρ).inter hA
  have hE : MeasurableSet E := e.symm.measurable hD
  have hsplit : MeasurePreserving e ((continuousScoreLaw n).restrict D) ν := by
    have hpre : e ⁻¹' E = D := by
      ext x
      simp [E]
    have hp : MeasurePreserving e (continuousScoreLaw n) P :=
      measurePreserving_splitRotationClockCells μ ρ
    rw [← hpre]
    exact hp.restrict_preimage hE
  have hΔ : (fun x ↦ L (e x)) =ᵐ[(continuousScoreLaw n).restrict D] Δ := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact (scoreWalkClock_increment_eq_on_branch k μ ρ hx.1).symm
  have h := scoreRotationBranch_inter_condExp_logMoments k μ ρ hA
    (fun hx hy hfst ↦ hInv hx hy (scoreWalkClock_history_eq_on_branch_fst_eq k μ ρ hx hy hfst))
  have hmean : (∫ z, L z ∂ν) = 0 := by
    rw [← integral_condExp hm, integral_congr_ae h.2.1, integral_zero]
  have henergy : (∫ z, (L z)^2 ∂ν) = ∫ _ : ScoreProfile n,
      (ρ.support.card : ℝ) ∂(continuousScoreLaw n).restrict D := by
    rw [← integral_condExp hm, integral_congr_ae h.2.2]
    exact (hsplit.integral_comp' (fun _ ↦ (ρ.support.card : ℝ))).symm
  refine ⟨(memLp_congr_ae hΔ).mp (h.1.comp_measurePreserving hsplit), ?_, ?_⟩
  · exact (integral_congr_ae hΔ).symm.trans ((hsplit.integral_comp' L).trans hmean)
  · calc
      _ = ∫ x in D, (L (e x))^2 ∂continuousScoreLaw n :=
        integral_congr_ae (hΔ.symm.mono fun _ hx ↦ congrArg (fun r : ℝ ↦ r^2) hx)
      _ = ∫ z, (L z)^2 ∂ν := hsplit.integral_comp' (fun z ↦ (L z)^2)
      _ = (ρ.support.card : ℝ) * (continuousScoreLaw n).real D := by
        rw [henergy, integral_const, smul_eq_mul, mul_comm]
        simp only [measureReal_def, Measure.restrict_apply_univ]

/-- The actual increment is square-integrable on each rotation branch. -/
theorem memLp_scoreWalkClock_increment_on_branch
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    MemLp (fun x ↦ scoreWalkClock x (k + 1) - scoreWalkClock x k) 2
      ((continuousScoreLaw n).restrict (scoreRotationBranch k μ ρ)) := by
  simpa only [inter_univ] using
    (scoreWalkClock_moments_on_branch_inter k μ ρ MeasurableSet.univ (fun _ _ _ ↦ Iff.rfl)).1

/-- The squared increment integrates to the rotation size times the branch mass. -/
theorem setIntegral_sq_scoreWalkClock_increment_on_branch
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    (∫ x in scoreRotationBranch k μ ρ, (scoreWalkClock x (k + 1) - scoreWalkClock x k)^2
      ∂continuousScoreLaw n) = (ρ.support.card : ℝ) *
        (continuousScoreLaw n).real (scoreRotationBranch k μ ρ) := by
  simpa only [inter_univ] using
    (scoreWalkClock_moments_on_branch_inter k μ ρ MeasurableSet.univ
      (fun _ _ _ ↦ Iff.rfl)).2.2

/-- Every measurable test based on the past has zero increment integral on the branch. -/
theorem setIntegral_scoreWalkClock_increment_on_branch_inter
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    {A : Set (ScoreProfile n)} (hA : MeasurableSet A)
    (hInv : ∀ {x y}, x ∈ scoreRotationBranch k μ ρ → y ∈ scoreRotationBranch k μ ρ →
      (∀ j ≤ k, scoreWalkClock x j = scoreWalkClock y j) → (x ∈ A ↔ y ∈ A)) :
    (∫ x in scoreRotationBranch k μ ρ ∩ A, (scoreWalkClock x (k + 1) - scoreWalkClock x k)
      ∂continuousScoreLaw n) = 0 :=
  (scoreWalkClock_moments_on_branch_inter k μ ρ hA hInv).2.1

end LennonPittelFormalization

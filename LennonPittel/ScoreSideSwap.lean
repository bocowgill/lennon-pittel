module

public import LennonPittel.CoexposureSpouseMarginal
public import LennonPittel.PittelSimplexMoments

/-!
# Swapping the sides of the continuous score model

The swap only permutes the independent score rows. A stable matching
becomes its inverse, and its male and female score statistics exchange
roles up to the corresponding permutation of labels.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

/-- Exchange the two sides, retaining the candidate labels within each row. -/
def swapScoreSides {n : ℕ} (x : ScoreProfile n) : ScoreProfile n :=
  fun row ↦ x row.swap

/-- Exchanging the sides leaves the independent score law unchanged. -/
theorem measurePreserving_swapScoreSides (n : ℕ) :
    MeasurePreserving (@swapScoreSides n) (continuousScoreLaw n) (continuousScoreLaw n) := by
  let e := Equiv.sumComm (Fin n) (Fin n)
  have h := measurePreserving_piCongrLeft
    (fun _ : Fin n ⊕ Fin n ↦ Measure.pi fun _ : Fin n ↦ unitScoreLaw) e
  have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n ↦ Fin n → ℝ) e) =
      @swapScoreSides n := by
    funext x row
    cases row <;> rfl
  simpa only [hfun, continuousScoreLaw] using h

/-- A blocking pair becomes the same pair with the roles exchanged. -/
theorem isScoreBlockingPair_swapScoreSides_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (m w : Fin n) :
    IsScoreBlockingPair (swapScoreSides x) μ.symm w m ↔ IsScoreBlockingPair x μ m w := by
  have hne : μ.symm w ≠ m ↔ μ m ≠ w := by
    constructor
    · intro h hmw
      exact h (by rw [← hmw, μ.symm_apply_apply])
    · intro h hwm
      exact h (by rw [← hwm, μ.apply_symm_apply])
  simp only [IsScoreBlockingPair, swapScoreSides, Sum.swap_inl, Sum.swap_inr,
    Equiv.symm_symm, hne, and_comm (a := x (.inr w) m < x (.inr w) (μ.symm w))]

/-- Score stability is unchanged when both the sides and matching are exchanged. -/
theorem isScoreStable_swapScoreSides_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    IsScoreStable (swapScoreSides x) μ.symm ↔ IsScoreStable x μ := by
  constructor
  · intro h m w
    exact mt (isScoreBlockingPair_swapScoreSides_iff x μ m w).mpr (h w m)
  · intro h w m
    exact mt (isScoreBlockingPair_swapScoreSides_iff x μ m w).mp (h m w)

/-- After the swap, the old male spouse scores are indexed by their partners. -/
theorem femaleSpouseByHusband_swapScoreSides {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    femaleSpouseByHusband μ.symm (swapScoreSides x) =
      (fun i ↦ maleSpouseScore x μ i) ∘ μ.symm := by
  funext i
  rfl

/-- The law of a permutation-invariant spouse statistic on the stable event
is the same on the two sides, with the matching inverted. -/
theorem scoreStable_maleSpouseStatistic_measure_eq_female {n : ℕ} (μ : Matching n)
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)), v ∘ e ∈ S ↔ v ∈ S) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ (fun i ↦ maleSpouseScore x μ i) ∈ S} =
      continuousScoreLaw n {x | IsScoreStable x μ.symm ∧ femaleSpouseByHusband μ.symm x ∈ S} := by
  let T : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ.symm ∧ femaleSpouseByHusband μ.symm x ∈ S}
  have hT : MeasurableSet T := (measurableSet_isScoreStable μ.symm).inter
    (hS.preimage (Measurable.of_eval fun i ↦ measurable_femaleSpouseScore μ.symm (μ.symm i)))
  have hpre : swapScoreSides ⁻¹' T =
      {x | IsScoreStable x μ ∧ (fun i ↦ maleSpouseScore x μ i) ∈ S} := by
    ext x
    change IsScoreStable (swapScoreSides x) μ.symm ∧
      femaleSpouseByHusband μ.symm (swapScoreSides x) ∈ S ↔ _
    rw [isScoreStable_swapScoreSides_iff, femaleSpouseByHusband_swapScoreSides, hinv]
    rfl
  rw [← hpre]
  exact (measurePreserving_swapScoreSides n).measure_preimage hT.nullMeasurableSet

/-- Normalized shares are permuted when their vector is permuted. -/
theorem spouseAngle_comp_equiv {n : ℕ} (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    spouseAngle (v ∘ e) = spouseAngle v ∘ e := by
  funext i
  change v (e i) / (∑ j, v (e j)) = v (e i) / (∑ j, v j)
  rw [Equiv.sum_comp e v]

/-- The scaled sum of squared shares is invariant under label permutations. -/
theorem pittelAngularSquareScore_spouseAngle_comp_equiv {n : ℕ} (v : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) :
    pittelAngularSquareScore (spouseAngle (v ∘ e)) = pittelAngularSquareScore (spouseAngle v) := by
  rw [spouseAngle_comp_equiv]
  unfold pittelAngularSquareScore
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e (fun i ↦ spouseAngle v i ^ 2)]

/-- Transfer a cutoff on the spouse total and the scaled squared shares
from women to men by exchanging the roles and inverting the matching. -/
theorem scoreStable_maleSpouseAngleSquare_measure_eq_female {n : ℕ}
    (μ : Matching n) (L c : ℝ) :
    continuousScoreLaw n {x | IsScoreStable x μ ∧ L ≤ ∑ i, maleSpouseScore x μ i ∧
      c < pittelAngularSquareScore (spouseAngle (fun i ↦ maleSpouseScore x μ i))} =
      continuousScoreLaw n {x | IsScoreStable x μ.symm ∧ L ≤ femaleSpouseTotal x μ.symm ∧
        c < pittelAngularSquareScore (spouseAngle (femaleSpouseByHusband μ.symm x))} := by
  let S : Set (Fin n → ℝ) :=
    {v | L ≤ ∑ i, v i ∧ c < pittelAngularSquareScore (spouseAngle v)}
  have hsq : Measurable (pittelAngularSquareScore : (Fin n → ℝ) → ℝ) := by
    unfold pittelAngularSquareScore
    fun_prop
  have hS : MeasurableSet S := (measurableSet_le measurable_const
    (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)).inter
    (measurableSet_lt measurable_const (hsq.comp (measurable_spouseAngle n)))
  have hInv (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)) : v ∘ e ∈ S ↔ v ∈ S := by
    change (L ≤ ∑ i, v (e i)) ∧ c < pittelAngularSquareScore (spouseAngle (v ∘ e)) ↔ _
    rw [Equiv.sum_comp e v, pittelAngularSquareScore_spouseAngle_comp_equiv]
    rfl
  simpa only [S, mem_ofPred_eq, ← femaleSpouseTotal_eq_sum_byHusband] using
    scoreStable_maleSpouseStatistic_measure_eq_female μ hS hInv

end LennonPittelFormalization

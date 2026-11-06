module

public import LennonPittel.AdaptiveScoreFiberAssembly
public import LennonPittel.ScoreRotationWalk

/-!
# Exact clock moments on a concrete rotation branch

Fix the checkpoint matching and the next selected cycle. Rearrange the iid
array into the selected female cells and the remaining scores. The replay
theorem makes this measurable branch a passing box in the selected scores.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators Classical

namespace LennonPittelFormalization

variable {n : ℕ}

abbrev ClockCell (n : ℕ) := (Fin n ⊕ Fin n) × Fin n

abbrev ClockSelected (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :=
  {c : ClockCell n // IsRotationClockCell μ ρ c}

abbrev ClockComplement (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :=
  {c : ClockCell n // ¬IsRotationClockCell μ ρ c}

/-- Split the full score array into the complementary and selected entries. -/
noncomputable def splitRotationClockCells (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    ScoreProfile n ≃ᵐ (ClockComplement μ ρ → ℝ) × (ClockSelected μ ρ → ℝ) :=
  (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ClockCell n ↦ ℝ)
      (IsRotationClockCell μ ρ)).trans MeasurableEquiv.prodComm)

private theorem measurePreserving_clockUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm
      (continuousScoreLaw n) (Measure.pi fun _ : ClockCell n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi fun j ↦ s (i, j)) by
    ext x
    simp [mem_pi, Prod.forall]]
  simp_rw [continuousScoreLaw, Measure.pi_pi]
  rw [← Finset.prod_product']
  simp

/-- Both factors of the split have the independent unit score law. -/
theorem measurePreserving_splitRotationClockCells (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    MeasurePreserving (splitRotationClockCells μ ρ) (continuousScoreLaw n)
      ((Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
        (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)) :=
  (Measure.measurePreserving_swap.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ClockCell n ↦ unitScoreLaw)
      (IsRotationClockCell μ ρ))).comp (measurePreserving_clockUncurry n)

private theorem split_fst_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (x : ScoreProfile n) (c : ClockComplement μ ρ) :
    (splitRotationClockCells μ ρ x).1 c = x c.val.1 c.val.2 := rfl

private theorem split_snd_apply (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (x : ScoreProfile n) (c : ClockSelected μ ρ) :
    (splitRotationClockCells μ ρ x).2 c = x c.val.1 c.val.2 := rfl

/-- A current spouse score is never among the cells selected by the rotation. -/
theorem old_spouse_not_selected (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (w : Fin n) : ¬IsRotationClockCell μ ρ (.inr w, μ.symm w) := by
  rintro ⟨m, hm, heq⟩
  have ha : m = μ.symm w := congrArg Prod.snd heq
  have hw : μ (ρ m) = w := Sum.inr.inj (congrArg Prod.fst heq)
  have hm' : μ m = w := (congrArg μ ha).trans (μ.apply_symm_apply w)
  have hr : ρ m = m := μ.injective (hw.trans hm'.symm)
  exact (Equiv.Perm.mem_support.mp hm) hr

/-- The complementary coordinates include every current spouse score. -/
theorem femaleSpouseScore_eq_of_splitRotationClockCells_fst_eq (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {x y : ScoreProfile n}
    (h : (splitRotationClockCells μ ρ x).1 = (splitRotationClockCells μ ρ y).1) (w : Fin n) :
    femaleSpouseScore x μ w = femaleSpouseScore y μ w :=
  congrFun h ⟨(.inr w, μ.symm w), old_spouse_not_selected μ ρ w⟩

/-- The current cutoff for a selected cell is an old spouse score in the complement. -/
def rotationClockUpper (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (a : ClockComplement μ ρ → ℝ) (c : ClockSelected μ ρ) : ℝ :=
  let w := eliminateRotation μ ρ c.val.2
  a ⟨(.inr w, μ.symm w), old_spouse_not_selected μ ρ w⟩

private theorem rotationClockUpper_split (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (x : ScoreProfile n) (c : ClockSelected μ ρ) :
    rotationClockUpper μ ρ (splitRotationClockCells μ ρ x).1 c =
      femaleSpouseScore x μ (eliminateRotation μ ρ c.val.2) := rfl

private theorem symm_mem_support {ρ : Equiv.Perm (Fin n)} {i : Fin n} (hi : i ∈ ρ.support) :
    ρ.symm i ∈ ρ.support :=
  Equiv.Perm.apply_mem_support.mp (by simpa only [Equiv.apply_symm_apply] using hi)

private noncomputable def oldHusbandEquivSelected (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    {i : Fin n // i ∈ ρ.support} ≃ ClockSelected μ ρ := by
  let f (i : {i : Fin n // i ∈ ρ.support}) : ClockSelected μ ρ :=
    ⟨rotationClockCell μ ρ (ρ.symm i.val), ⟨_, symm_mem_support i.property, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    exact Subtype.ext (ρ.symm.injective
      (rotationClockCell_injective μ ρ (congrArg Subtype.val h)))
  · intro c
    obtain ⟨m, hm, heq⟩ := c.property
    refine ⟨⟨ρ m, Equiv.Perm.apply_mem_support.mpr hm⟩, Subtype.ext ?_⟩
    exact (congrArg (rotationClockCell μ ρ) (ρ.symm_apply_apply m)).trans heq

/-- There is one selected cell per participating pair. -/
theorem card_clockSelected (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    Fintype.card (ClockSelected μ ρ) = ρ.support.card :=
  (Fintype.card_congr (oldHusbandEquivSelected μ ρ).symm).trans (Fintype.card_coe _)

/-- The split-score log sum is the actual centered log progress at a rotation. -/
theorem centeredCacheLogIncrement_splitRotationClockCells (x : ScoreProfile n)
    (μ : Matching n) (ρ : Equiv.Perm (Fin n)) (hx : ∀ j i, 0 < x (.inr j) i) :
    centeredCacheLogIncrement (rotationClockUpper μ ρ) (splitRotationClockCells μ ρ x) =
      femaleLogPotential x (eliminateRotation μ ρ) - femaleLogPotential x μ -
        (ρ.support.card : ℝ) := by
  rw [femaleLogPotential_eliminate_sub x μ ρ hx, sum_negLog_sub_card_eq_sum_centeredNegLog]
  unfold centeredCacheLogIncrement
  let e := oldHusbandEquivSelected μ ρ
  rw [← Equiv.sum_comp e]
  rw [← Finset.sum_coe_sort ρ.support]
  apply Finset.sum_congr rfl
  intro i _
  have he : (e i).val = rotationClockCell μ ρ (ρ.symm i.val) := rfl
  have hnew : eliminateRotation μ ρ (ρ.symm i.val) = μ i.val := by
    rw [eliminateRotation_apply, Equiv.apply_symm_apply]
  have hval := femaleSpouseScore_eliminate_apply x μ ρ (ρ.symm i.val)
  rw [hnew] at hval
  rw [split_snd_apply, rotationClockUpper_split]
  simp only [he, rotationClockCell, hnew, femaleRotationRatio] at hval ⊢
  rw [hval]

private def ordinalClockGraph (p : Profile n) (μ : Matching n) : Fin n → Option (Fin n) :=
  queriedSuccessorGraph p.manRank μ
    (fun m w ↦ decide (p.womanRank w m < p.womanRank w (μ.symm w)))

private noncomputable def ordinalClockEnd (p : Profile n) : ℕ → Matching n → Matching n
  | 0, μ => μ
  | k + 1, μ =>
    match chooseQueriedRotation (ordinalClockGraph p μ) with
    | none => μ
    | some ρ => ordinalClockEnd p k (eliminateRotation μ ρ)

private theorem ordinalClockGraph_eq_score (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (μ : Matching n) :
    ordinalClockGraph (profileOfScores x) μ = scoreRotationGraph x μ := by
  unfold ordinalClockGraph scoreRotationGraph
  congr 1
  funext m w
  simp only [profileOfScores, successorScoreOracle, femaleSpouseScore]
  exact decide_eq_decide.mpr (rankPermutation_lt_iff (hx w) m (μ.symm w))

private theorem ordinalClockEnd_eq_score (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (k : ℕ) (μ : Matching n) :
    ordinalClockEnd (profileOfScores x) k μ = (scoreRotationWalk x k μ).2 := by
  induction k generalizing μ with
  | zero => rfl
  | succ k ih =>
    rw [ordinalClockEnd, scoreRotationWalk, ordinalClockGraph_eq_score x hx]
    cases chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => rfl
    | some ρ => exact ih _

/-- Only the almost-sure open-unit and female no-ties conditions are imposed. -/
def goodClockInput (n : ℕ) : Set (ScoreProfile n) :=
  {x | (∀ w, Function.Injective (x (.inr w))) ∧ ∀ r i, x r i ∈ Ioo (0 : ℝ) 1}

theorem measurableSet_goodClockInput (n : ℕ) : MeasurableSet (goodClockInput n) := by
  have hc (r : Fin n ⊕ Fin n) (i : Fin n) :
      Measurable fun x : ScoreProfile n ↦ x r i :=
    (measurable_pi_apply i).comp (measurable_pi_apply r)
  unfold goodClockInput
  simp only [ofPred_and, Function.Injective, ofPred_forall]
  refine (MeasurableSet.iInter fun w ↦ MeasurableSet.iInter fun i ↦
    MeasurableSet.iInter fun j ↦ ?_).inter
    (MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun i ↦
      (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)).preimage (hc r i))
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, imp_false]
    exact (measurableSet_eq_fun (hc (.inr w) i) (hc (.inr w) j)).compl

theorem ae_goodClockInput (n : ℕ) : ∀ᵐ x ∂continuousScoreLaw n, x ∈ goodClockInput n := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x ht hu
  exact ⟨fun w ↦ ht (.inr w), hu⟩

/-- The branch of the score walk having the specified current matching and cycle. -/
def scoreRotationBranch (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    Set (ScoreProfile n) :=
  {x | x ∈ goodClockInput n ∧
    (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 = μ ∧
    chooseQueriedRotation (scoreRotationGraph x μ) = some ρ}

theorem measurableSet_scoreRotationBranch (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    MeasurableSet (scoreRotationBranch k μ ρ) := by
  let B : Set (Profile n) := {p | ordinalClockEnd p k (DAState.matching p) = μ ∧
    chooseQueriedRotation (ordinalClockGraph p μ) = some ρ}
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have h : scoreRotationBranch k μ ρ = goodClockInput n ∩ profileOfScores ⁻¹' B := by
    ext x
    change (x ∈ goodClockInput n ∧ _) ↔ (x ∈ goodClockInput n ∧ _)
    refine and_congr_right fun hx ↦ ?_
    change (_ = μ ∧ _) ↔ (ordinalClockEnd _ k _ = μ ∧ _)
    rw [ordinalClockEnd_eq_score x hx.1, ordinalClockGraph_eq_score x hx.1]
  rw [h]
  exact (measurableSet_goodClockInput n).inter ((measurable_profileOfScores n) hB)

/-- Restricting a rotation branch by a measurable event that is constant on
its passing fibers preserves its conditional log moments. -/
theorem scoreRotationBranch_inter_condExp_logMoments
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) {A : Set (ScoreProfile n)}
    (hA : MeasurableSet A)
    (hconst : ∀ {x y}, x ∈ scoreRotationBranch k μ ρ → y ∈ scoreRotationBranch k μ ρ →
      (splitRotationClockCells μ ρ x).1 = (splitRotationClockCells μ ρ y).1 →
      (x ∈ A ↔ y ∈ A)) :
    let e := splitRotationClockCells μ ρ
    let P := (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
      (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)
    let ν := P.restrict (e.symm ⁻¹' (scoreRotationBranch k μ ρ ∩ A))
    let L := centeredCacheLogIncrement (rotationClockUpper μ ρ)
    let m := MeasurableSpace.comap Prod.fst (inferInstance :
      MeasurableSpace (ClockComplement μ ρ → ℝ))
    MemLp L 2 ν ∧ ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (ρ.support.card : ℝ)) := by
  let e := splitRotationClockCells μ ρ
  let E := e.symm ⁻¹' (scoreRotationBranch k μ ρ ∩ A)
  let G := e.symm ⁻¹' goodClockInput n
  have hE := e.symm.measurable ((measurableSet_scoreRotationBranch k μ ρ).inter hA)
  have hG := e.symm.measurable (measurableSet_goodClockInput n)
  have hgood := (measurePreserving_splitRotationClockCells μ ρ).symm.quasiMeasurePreserving.ae
    (ae_goodClockInput n)
  have hupper (i : ClockSelected μ ρ) :
      Measurable (fun a ↦ rotationClockUpper μ ρ a i) := measurable_pi_apply _
  rw [← card_clockSelected μ ρ]
  refine scoreBranch_condExp_logMoments_of_replay
    (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw)
    (E := E) (G := G) hE hG hgood (rotationClockUpper μ ρ) hupper ?_ ?_
  · intro a v hv i
    let x := e.symm (a, v)
    have hg : x ∈ goodClockInput n := hv.1.1
    have hs := hg.2 (.inr (eliminateRotation μ ρ i.val.2))
      (μ.symm (eliminateRotation μ ρ i.val.2))
    have he : e x = (a, v) := e.apply_symm_apply _
    have hc := rotationClockUpper_split μ ρ x i
    change rotationClockUpper μ ρ (e x).1 i = _ at hc
    rw [he] at hc
    exact ⟨hc ▸ hs.1, hc ▸ hs.2.le⟩
  · intro a u hu v hv
    let x := e.symm (a, u)
    let y := e.symm (a, v)
    have ex : e x = (a, u) := e.apply_symm_apply _
    have ey : e y = (a, v) := e.apply_symm_apply _
    have hx : x ∈ scoreRotationBranch k μ ρ := hu.1
    have hy : y ∈ goodClockInput n := hv
    have hfixed (r : Fin n ⊕ Fin n) (i : Fin n) (hc : ¬ IsRotationClockCell μ ρ (r, i)) :
        y r i = x r i := by
      let c : ClockComplement μ ρ := ⟨(r, i), hc⟩
      change (e y).1 c = (e x).1 c
      rw [ey, ex]
    have hchoose := hx.2.2
    rw [← hx.2.1] at hchoose
    have hpass := scoreRotationWalk_same_prefix_and_choice_iff k hx.1.1 hy.1 hchoose
      (by rw [hx.2.1]; exact hfixed)
    constructor
    · intro hbranch i
      have hb : y ∈ scoreRotationBranch k μ ρ := hbranch.1
      have hρ := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff y hy.1 μ ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation hb.2.2)
      obtain ⟨m, hm, heq⟩ := i.property
      have ha : m = i.val.2 := congrArg Prod.snd heq
      subst m
      have hlt := hρ.rotationClockCell_score_lt hy.1 hm
      rw [heq, femaleSpouseScore, hfixed _ _ (old_spouse_not_selected μ ρ _)] at hlt
      have hc := rotationClockUpper_split μ ρ x i
      change rotationClockUpper μ ρ (e x).1 i = _ at hc
      rw [ex] at hc
      have hval := split_snd_apply μ ρ y i
      change (e y).2 i = _ at hval
      rw [ey] at hval
      change v i = _ at hval
      change rotationClockUpper μ ρ a i = _ at hc
      refine ⟨?_, ?_⟩
      · rw [hval]
        exact (hy.2 i.val.1 i.val.2).1
      · rw [hval, hc]
        exact hlt
    · intro hall
      have hbelow (m : Fin n) (hm : m ∈ ρ.support) :
          y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
            femaleSpouseScore x μ (eliminateRotation μ ρ m) := by
        let c : ClockSelected μ ρ := ⟨rotationClockCell μ ρ m, ⟨m, hm, rfl⟩⟩
        have hval := split_snd_apply μ ρ y c
        change (e y).2 c = _ at hval
        rw [ey] at hval
        have hc := rotationClockUpper_split μ ρ x c
        change rotationClockUpper μ ρ (e x).1 c = _ at hc
        rw [ex] at hc
        exact hval ▸ hc ▸ (hall c).2
      have hp := hpass.mpr (by rw [hx.2.1]; exact hbelow)
      have hyμ := (congrArg Prod.snd hp.1).trans hx.2.1
      have hsame := congrArg
        (fun τ : Matching n ↦ chooseQueriedRotation (scoreRotationGraph y τ)) hyμ
      have hb : y ∈ scoreRotationBranch k μ ρ := ⟨hy, hyμ, hsame.symm.trans hp.2⟩
      refine ⟨hb, (hconst hx hb ?_).mp hu.2⟩
      exact (congrArg Prod.fst ex).trans (congrArg Prod.fst ey).symm

/-- The measurable concrete branch has the exact conditional log moments
given all scores outside the selected cells. -/
theorem scoreRotationBranch_condExp_logMoments
    (k : ℕ) (μ : Matching n) (ρ : Equiv.Perm (Fin n)) :
    let e := splitRotationClockCells μ ρ
    let P := (Measure.pi fun _ : ClockComplement μ ρ ↦ unitScoreLaw).prod
      (Measure.pi fun _ : ClockSelected μ ρ ↦ unitScoreLaw)
    let ν := P.restrict (e.symm ⁻¹' scoreRotationBranch k μ ρ)
    let L := centeredCacheLogIncrement (rotationClockUpper μ ρ)
    let m := MeasurableSpace.comap Prod.fst (inferInstance :
      MeasurableSpace (ClockComplement μ ρ → ℝ))
    MemLp L 2 ν ∧ ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (ρ.support.card : ℝ)) := by
  simpa only [inter_univ] using
    scoreRotationBranch_inter_condExp_logMoments k μ ρ (A := univ) MeasurableSet.univ
      (fun _ _ _ ↦ Iff.rfl)

end LennonPittelFormalization

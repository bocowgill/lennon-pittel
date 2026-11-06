module

public import LennonPittel.DeferredAcceptanceTranscript
public import LennonPittel.RotationClockCells
public import LennonPittel.RotationSuccessorQueries

/-!
# A score-comparison walk between the two extreme stable matchings

At each checkpoint the walk scans the known men's lists using Boolean
comparisons against current spouse scores. The cycle is chosen from that
graph, before the new spouse scores are read. The participation cap gives
a deterministic horizon at which the graph has no remaining cycle.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The successor graph at the current matching uses only comparisons
against the known spouse scores. -/
noncomputable def scoreRotationGraph (x : ScoreProfile n) (μ : Matching n) :
    Fin n → Option (Fin n) :=
  queriedSuccessorGraph (profileOfScores x).manRank μ
    (successorScoreOracle (femaleSpouseScore x μ) (fun w ↦ x (.inr w)))

/-- Run at most the specified number of comparison-selected rotations.
Once no cycle is found, the matching stays fixed. -/
noncomputable def scoreRotationWalk (x : ScoreProfile n) :
    ℕ → Matching n → List (Equiv.Perm (Fin n)) × Matching n
  | 0, μ => ([], μ)
  | k + 1, μ =>
    match chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => ([], μ)
    | some ρ =>
      let out := scoreRotationWalk x k (eliminateRotation μ ρ)
      (ρ :: out.1, out.2)

/-- The finite walk is a legal rotation sequence in the rank profile. -/
theorem scoreRotationWalk_legal (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) (k : ℕ)
    {μ : Matching n} (hμ : IsStable (profileOfScores x) μ) :
    RotationSequence (profileOfScores x) μ (scoreRotationWalk x k μ).1
      (scoreRotationWalk x k μ).2 := by
  induction k generalizing μ with
  | zero => exact .nil hμ
  | succ k ih =>
    rw [scoreRotationWalk]
    split
    · exact .nil hμ
    · rename_i ρ hselect
      have hρ : IsExposedRotation (profileOfScores x) μ ρ :=
        (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht μ ρ).mp
          (realizesDirectedCycle_of_chooseQueriedRotation hselect)
      exact .cons hμ hρ (ih (hρ.isStable_eliminate hμ))

private theorem scoreRotationWalk_length_of_endpoint_cycle (x : ScoreProfile n)
    (k : ℕ) (μ : Matching n)
    (h : chooseQueriedRotation (scoreRotationGraph x (scoreRotationWalk x k μ).2) ≠ none) :
    (scoreRotationWalk x k μ).1.length = k := by
  induction k generalizing μ with
  | zero => rfl
  | succ k ih =>
    cases hc : chooseQueriedRotation (scoreRotationGraph x μ) with
    | none =>
      rw [scoreRotationWalk, hc] at h
      exact (h hc).elim
    | some ρ =>
      rw [scoreRotationWalk, hc] at h ⊢
      exact congrArg Nat.succ (ih _ h)

/-- Each legal nontrivial step accounts for at least one participating pair. -/
theorem RotationSequence.length_le_participation {p : Profile n} {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    rs.length ≤ rotationParticipation rs := by
  induction h with
  | nil => simp [rotationParticipation]
  | @cons μ ν ρ rs _ hρ _ ih =>
    obtain ⟨m, hm, _⟩ := hρ.isCycle
    have hpos := Finset.card_pos.mpr ⟨m, Equiv.Perm.mem_support.mpr hm⟩
    simp only [List.length_cons, rotationParticipation, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- A walk at the deterministic participation horizon has no next rotation. -/
theorem scoreRotationWalk_horizon_acyclic (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) {μ : Matching n}
    (hμ : IsStable (profileOfScores x) μ) :
    IsAcyclicSuccessor (scoreRotationGraph x (scoreRotationWalk x (n * (n - 1)) μ).2) := by
  let N := n * (n - 1)
  let out := scoreRotationWalk x N μ
  have hp := scoreRotationWalk_legal x ht N hμ
  apply (chooseQueriedRotation_eq_none_iff _).mp
  change chooseQueriedRotation (scoreRotationGraph x out.2) = none
  cases hchoose : chooseQueriedRotation (scoreRotationGraph x out.2) with
  | none => rfl
  | some ρ =>
    have hρ : IsExposedRotation (profileOfScores x) out.2 ρ :=
      (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht _ ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation hchoose)
    have hstep : RotationSequence (profileOfScores x) out.2 [ρ] (eliminateRotation out.2 ρ) :=
      .cons hp.isStable_end hρ (.nil (hρ.isStable_eliminate hp.isStable_end))
    have hext := hp.append hstep
    have hl := scoreRotationWalk_length_of_endpoint_cycle x N μ (by
      change chooseQueriedRotation (scoreRotationGraph x out.2) ≠ none
      rw [hchoose]
      exact Option.some_ne_none _)
    have hbad := hext.length_le_participation.trans hext.participation_le
    change (out.1 ++ [ρ]).length ≤ N at hbad
    change out.1.length = N at hl
    simp only [List.length_append, List.length_singleton, hl] at hbad
    omega

/-- The comparison-selected walk starts at the DA matching and ends at the
woman-optimal matching. This is a deterministic result, not a conditional law. -/
theorem scoreRotationWalk_da_optimal_endpoints (x : ScoreProfile n)
    (ht : ∀ j, Function.Injective (x (.inr j))) :
    let p := profileOfScores x
    let μ := DAState.matching p
    let out := scoreRotationWalk x (n * (n - 1)) μ
    IsManOptimal p μ ∧ RotationSequence p μ out.1 out.2 ∧
      IsManOptimal (swapProfile p) out.2.symm := by
  dsimp only
  have hs := DAState.isManOptimal_matching (profileOfScores x)
  have hp := scoreRotationWalk_legal x ht (n * (n - 1)) hs.1
  exact ⟨hs, hp, isWomanOptimal_of_acyclic_queriedSuccessorGraph_scores x ht _
    hp.isStable_end (scoreRotationWalk_horizon_acyclic x ht hs.1)⟩

/-- The scores selected by an upcoming rotation are distinct female coordinates. -/
def IsRotationClockCell (μ : Matching n) (ρ : Equiv.Perm (Fin n))
    (c : (Fin n ⊕ Fin n) × Fin n) : Prop :=
  ∃ m ∈ ρ.support, rotationClockCell μ ρ m = c

private theorem manRank_eq_of_fix_rotationClockCells {x y : ScoreProfile n}
    {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    (hfixed : ∀ r i, ¬IsRotationClockCell μ ρ (r, i) → y r i = x r i) :
    (profileOfScores y).manRank = (profileOfScores x).manRank := by
  have hrow (m : Fin n) : y (.inl m) = x (.inl m) := funext fun i ↦
    hfixed (.inl m) i fun ⟨a, _, ha⟩ ↦ Sum.inr_ne_inl (congrArg Prod.fst ha)
  funext m
  simp only [profileOfScores, hrow m]

/-- Resampling the selected scores below the current cutoffs preserves every
earlier successor graph, including the graph used to select the rotation. -/
theorem scoreRotationGraph_eq_of_replace_selected {x y : ScoreProfile n} {ν μ : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (hp : RotationSequence (profileOfScores x) ν rs μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j)))
    (hfixed : ∀ r i, ¬IsRotationClockCell μ ρ (r, i) → y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support, y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
      femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    scoreRotationGraph y ν = scoreRotationGraph x ν := by
  have hmen := manRank_eq_of_fix_rotationClockCells hfixed
  have hspouse (j : Fin n) : femaleSpouseScore y ν j = femaleSpouseScore x ν j := by
    apply hfixed
    intro ⟨a, ha, h⟩
    apply hp.rotationClockCell_ne_old_spouse hρ ha (ν.symm j)
    simpa only [Equiv.apply_symm_apply] using h
  have horacle : successorScoreOracle (femaleSpouseScore y ν) (fun w ↦ y (.inr w)) =
      successorScoreOracle (femaleSpouseScore x ν) (fun w ↦ x (.inr w)) := by
    funext m w
    unfold successorScoreOracle
    rw [hspouse]
    change decide (y (.inr w) m < _) = decide (x (.inr w) m < _)
    by_cases hc : IsRotationClockCell μ ρ (.inr w, m)
    · obtain ⟨a, ha, heq⟩ := hc
      have hy := (hbelow a ha).trans_le
        (hp.femaleSpouseScore_end_le_start ht (eliminateRotation μ ρ a))
      have hx := hp.rotationClockCell_score_lt_old_threshold hρ ht ha
      have hw : eliminateRotation μ ρ a = w := Sum.inr.inj (congrArg Prod.fst heq)
      rw [hw, heq] at hy hx
      simp only [hy, hx, decide_true]
    · rw [hfixed _ _ hc]
  rw [scoreRotationGraph, scoreRotationGraph, hmen, horacle]

/-- Altering only upcoming selected cells also preserves the DA starting
matching: every proposal was made at a rank no later than that man's DA wife. -/
theorem da_matching_eq_of_replace_selected {x y : ScoreProfile n} {μ : Matching n}
    {rs : List (Equiv.Perm (Fin n))}
    (hp : RotationSequence (profileOfScores x) (DAState.matching (profileOfScores x)) rs μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (hx : ∀ j, Function.Injective (x (.inr j))) (hy : ∀ j, Function.Injective (y (.inr j)))
    (hfixed : ∀ r i, ¬IsRotationClockCell μ ρ (r, i) → y r i = x r i) :
    DAState.matching (profileOfScores y) = DAState.matching (profileOfScores x) := by
  let p := profileOfScores x
  let q := profileOfScores y
  have hrun := DAState.run_eq_of_agree_on_proposed_scores (n * n) hx hy
    (manRank_eq_of_fix_rotationClockCells hfixed).symm fun w a ha ↦ by
      apply Eq.symm
      apply hfixed
      intro ⟨m, hm, heq⟩
      have hma : m = a := congrArg Prod.snd heq
      subst a
      exact hρ.new_partner_ne_of_rank_le hm
        (((DAState.proposed_run_sq_iff p m w).mp ha).trans (hp.menWeaklyPrefer m))
        (Sum.inr.inj (congrArg Prod.fst heq))
  apply Equiv.ext
  intro m
  have hm (a : Profile n) :
      (DAState.run a (n * n)).held (DAState.matching a m) = some m :=
    DAState.held_toMatching _ (DAState.complete_run_sq a) m
  exact (DAState.valid_run p (n * n)).held_unique (hrun ▸ hm q) (hm p)

/-- Below the current passing thresholds, modifying the next rotation's
selected scores does not change the walk at any earlier checkpoint. -/
theorem scoreRotationWalk_eq_at_every_prefix {x y : ScoreProfile n} (k : ℕ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {ν : Matching n}
    (hν : IsStable (profileOfScores x) ν) {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation (profileOfScores x) (scoreRotationWalk x k ν).2 ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell (scoreRotationWalk x k ν).2 ρ (r, i) →
      y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support,
      let μ := (scoreRotationWalk x k ν).2
      y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    ∀ j ≤ k, scoreRotationWalk y j ν = scoreRotationWalk x j ν := by
  induction k generalizing ν with
  | zero =>
    intro j hj
    obtain rfl := Nat.eq_zero_of_le_zero hj
    rfl
  | succ k ih =>
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      have hgraph := scoreRotationGraph_eq_of_replace_selected
        (scoreRotationWalk_legal x ht (k + 1) hν) hρ ht hfixed hbelow
      rw [scoreRotationWalk, scoreRotationWalk, hgraph]
      cases h : chooseQueriedRotation (scoreRotationGraph x ν) with
      | none => rfl
      | some σ =>
        have hσ : IsExposedRotation (profileOfScores x) ν σ :=
          (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht ν σ).mp
            (realizesDirectedCycle_of_chooseQueriedRotation h)
        rw [scoreRotationWalk, h] at hρ hfixed hbelow
        exact congrArg (fun z ↦ (σ :: z.1, z.2))
          (ih (hσ.isStable_eliminate hν) hρ hfixed hbelow j (Nat.le_of_succ_le_succ hj))

/-- Below the current passing thresholds, the entire recorded prefix stays fixed. -/
theorem scoreRotationWalk_eq_of_replace_selected {x y : ScoreProfile n} (k : ℕ)
    (ht : ∀ j, Function.Injective (x (.inr j))) {ν : Matching n}
    (hν : IsStable (profileOfScores x) ν) {ρ : Equiv.Perm (Fin n)}
    (hρ : IsExposedRotation (profileOfScores x) (scoreRotationWalk x k ν).2 ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell (scoreRotationWalk x k ν).2 ρ (r, i) →
      y r i = x r i)
    (hbelow : ∀ m ∈ ρ.support,
      let μ := (scoreRotationWalk x k ν).2
      y (rotationClockCell μ ρ m).1 (rotationClockCell μ ρ m).2 <
        femaleSpouseScore x μ (eliminateRotation μ ρ m)) :
    scoreRotationWalk y k ν = scoreRotationWalk x k ν :=
  scoreRotationWalk_eq_at_every_prefix k ht hν hρ hfixed hbelow k le_rfl

/-- For fixed complementary scores and a tie-free profile at which the next
cycle is selected, the same prefix and next cycle occur exactly below the
selected scores' current thresholds. -/
theorem scoreRotationWalk_same_prefix_and_choice_iff {x y : ScoreProfile n} (k : ℕ)
    (hx : ∀ j, Function.Injective (x (.inr j))) (hy : ∀ j, Function.Injective (y (.inr j)))
    {ρ : Equiv.Perm (Fin n)}
    (hchoose : chooseQueriedRotation (scoreRotationGraph x
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2) = some ρ)
    (hfixed : ∀ r i, ¬IsRotationClockCell
      (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2 ρ (r, i) →
      y r i = x r i) :
    let start := DAState.matching (profileOfScores x)
    let out := scoreRotationWalk x k start
    let out' := scoreRotationWalk y k (DAState.matching (profileOfScores y))
    (out' = out ∧ chooseQueriedRotation (scoreRotationGraph y out'.2) = some ρ) ↔
      ∀ m ∈ ρ.support,
        y (rotationClockCell out.2 ρ m).1 (rotationClockCell out.2 ρ m).2 <
          femaleSpouseScore x out.2 (eliminateRotation out.2 ρ m) := by
  let start := DAState.matching (profileOfScores x)
  let out := scoreRotationWalk x k start
  let out' := scoreRotationWalk y k (DAState.matching (profileOfScores y))
  change (out' = out ∧ chooseQueriedRotation (scoreRotationGraph y out'.2) = some ρ) ↔ _
  have hstart := (DAState.isManOptimal_matching (profileOfScores x)).1
  have hp := scoreRotationWalk_legal x hx k hstart
  have hρ := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx out.2 ρ).mp
    (realizesDirectedCycle_of_chooseQueriedRotation hchoose)
  have hspouse (j : Fin n) : femaleSpouseScore y out.2 j = femaleSpouseScore x out.2 j := by
    apply hfixed
    intro ⟨a, ha, heq⟩
    apply (RotationSequence.nil hp.isStable_end).rotationClockCell_ne_old_spouse hρ ha
      (out.2.symm j)
    change rotationClockCell out.2 ρ a = (.inr (out.2 (out.2.symm j)), out.2.symm j)
    rw [Equiv.apply_symm_apply]
    exact heq
  constructor
  · rintro ⟨heq, hc⟩ m hm
    rw [heq] at hc
    have hρ' := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff y hy out.2 ρ).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hc)
    rw [← hspouse]
    exact hρ'.rotationClockCell_score_lt hy hm
  · intro hbelow
    have hda := da_matching_eq_of_replace_selected hp hρ hx hy hfixed
    have heq : out' = out := by
      unfold out' out
      rw [hda]
      exact scoreRotationWalk_eq_of_replace_selected k hx hstart hρ hfixed hbelow
    have hgraph := scoreRotationGraph_eq_of_replace_selected
      (RotationSequence.nil hp.isStable_end) hρ hx hfixed hbelow
    exact ⟨heq, by rw [heq, hgraph]; exact hchoose⟩

end LennonPittelFormalization

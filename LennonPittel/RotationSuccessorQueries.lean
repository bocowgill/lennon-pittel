module

public import LennonPittel.ForestDeterministic
public import LennonPittel.ReverseSuccessorRotation
public import LennonPittel.RotationReachability
public import LennonPittel.ScoreRanks
public import Mathlib.Data.List.FinRange

/-!
# A comparison-only successor scan

The scan uses known men's ranks and a Boolean comparison oracle for each
woman's score against her current spouse score. It stops at the first
passing comparison, returning the tested prefix and its answers. The
resulting partial graph identifies exactly the exposed rotations.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

/-- Scan in list order, stopping at the first passing query and returning
only the queried coordinates and their Boolean outcomes. -/
def runSuccessorQuery {α : Type*} (passes : α → Bool) :
    List α → Option α × List (α × Bool)
  | [] => (none, [])
  | w :: ws =>
    match passes w with
    | true => (some w, [(w, true)])
    | false =>
      let rest := runSuccessorQuery passes ws
      (rest.1, (w, false) :: rest.2)

theorem runSuccessorQuery_fst {α : Type*} (passes : α → Bool) (candidates : List α) :
    (runSuccessorQuery passes candidates).1 = candidates.find? passes := by
  induction candidates with
  | nil => rfl
  | cons w ws ih =>
    cases h : passes w <;> simp [runSuccessorQuery, h, ih]

/-- The tested coordinates form a prefix of the candidate list. -/
theorem runSuccessorQuery_trace_prefix {α : Type*} (passes : α → Bool) (candidates : List α) :
    (runSuccessorQuery passes candidates).2.map Prod.fst <+: candidates := by
  induction candidates with
  | nil => exact List.nil_prefix
  | cons w ws ih =>
    cases h : passes w <;> simp [runSuccessorQuery, h, ih]

/-- Each recorded Boolean is the answer returned by the oracle. -/
theorem runSuccessorQuery_answer {α : Type*} (passes : α → Bool) (candidates : List α)
    {q : α × Bool} (hq : q ∈ (runSuccessorQuery passes candidates).2) : passes q.1 = q.2 := by
  induction candidates with
  | nil => simp [runSuccessorQuery] at hq
  | cons w ws ih =>
    cases h : passes w
    · simp only [runSuccessorQuery, h, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h
      · exact ih hq
    · have hq' : q = (w, true) := by simpa [runSuccessorQuery, h] using hq
      subst q
      exact h

/-- A returned successor is the subject of a recorded passing comparison. -/
theorem runSuccessorQuery_success_mem_trace {α : Type*} (passes : α → Bool)
    (candidates : List α) {w : α} (h : (runSuccessorQuery passes candidates).1 = some w) :
    (w, true) ∈ (runSuccessorQuery passes candidates).2 := by
  induction candidates with
  | nil => simp [runSuccessorQuery] at h
  | cons v vs ih =>
    cases hpass : passes v
    · simp only [runSuccessorQuery, hpass] at h ⊢
      exact List.mem_cons_of_mem _ (ih h)
    · simp only [runSuccessorQuery, hpass, Option.some.injEq] at h
      subst w
      simp [runSuccessorQuery, hpass]

/-- A fixed scan result is characterized by the comparisons on its realized
trace; answers at all later candidates are irrelevant. -/
theorem runSuccessorQuery_eq_iff_trace {α : Type*} (passes other : α → Bool)
    (candidates : List α) :
    runSuccessorQuery other candidates = runSuccessorQuery passes candidates ↔
      ∀ q ∈ (runSuccessorQuery passes candidates).2, other q.1 = q.2 := by
  refine ⟨fun he q hq ↦ runSuccessorQuery_answer other candidates (he ▸ hq), ?_⟩
  induction candidates with
  | nil => intro _; rfl
  | cons w ws ih =>
    intro hagree
    cases h : passes w
    · have hw : other w = false := hagree (w, false) (by simp [runSuccessorQuery, h])
      have ht (q : α × Bool) (hq : q ∈ (runSuccessorQuery passes ws).2) :
          other q.1 = q.2 :=
        hagree q (by simp [runSuccessorQuery, h, hq])
      simp [runSuccessorQuery, h, hw, ih ht]
    · have hw : other w = true := hagree (w, true) (by simp [runSuccessorQuery, h])
      simp [runSuccessorQuery, h, hw]

variable {n : ℕ}

/-- The women below the current wife, in increasing order of the man's rank. -/
def successorQueryCandidates (rank : Equiv.Perm (Fin n)) (wife : Fin n) : List (Fin n) :=
  ((List.finRange n).filter fun i ↦ decide (rank wife < i)).map rank.symm

theorem mem_successorQueryCandidates {rank : Equiv.Perm (Fin n)} {wife w : Fin n} :
    w ∈ successorQueryCandidates rank wife ↔ rank wife < rank w := by
  simp only [successorQueryCandidates, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq, Equiv.symm_apply_eq]
  exact ⟨fun ⟨i, hi, h⟩ ↦ h ▸ hi, fun h ↦ ⟨rank w, h, rfl⟩⟩

theorem successorQueryCandidates_pairwise (rank : Equiv.Perm (Fin n)) (wife : Fin n) :
    (successorQueryCandidates rank wife).Pairwise (fun a b ↦ rank a < rank b) := by
  have hs : (List.finRange n).Pairwise (fun a b : Fin n ↦ a < b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa using hij
  simpa [successorQueryCandidates, List.pairwise_map] using
    hs.filter (fun i ↦ decide (rank wife < i))

/-- A one-row successor scan needs only the known rank permutation and current wife. -/
def querySuccessorRow (rank : Equiv.Perm (Fin n)) (wife : Fin n) (passes : Fin n → Bool) :
    Option (Fin n) × List (Fin n × Bool) :=
  runSuccessorQuery passes (successorQueryCandidates rank wife)

/-- A row never queries any woman twice. -/
theorem querySuccessorRow_trace_nodup (rank : Equiv.Perm (Fin n)) (wife : Fin n)
    (passes : Fin n → Bool) : ((querySuccessorRow rank wife passes).2.map Prod.fst).Nodup :=
  List.Nodup.sublist (runSuccessorQuery_trace_prefix passes _).sublist
    ((successorQueryCandidates_pairwise rank wife).imp fun h ↦
      fun he ↦ (ne_of_lt h) (congrArg rank he))

variable {p : Profile n} {μ : Matching n} {m w : Fin n}

private theorem isSuccessor_of_querySuccessorRow (passes : Fin n → Bool)
    (hpasses : ∀ v, passes v = true ↔ p.womanRank v m < p.womanRank v (μ.symm v))
    (h : (querySuccessorRow (p.manRank m) (μ m) passes).1 = some w) :
    IsSuccessor p μ m w := by
  rw [querySuccessorRow, runSuccessorQuery_fst] at h
  have hw := List.mem_of_find?_eq_some h
  obtain ⟨hpass, before, after, heq, hfail⟩ := List.find?_eq_some_iff_append.mp h
  refine ⟨⟨mem_successorQueryCandidates.mp hw, (hpasses w).mp hpass⟩, ?_⟩
  intro v hv
  have hs := successorQueryCandidates_pairwise (p.manRank m) (μ m)
  have hmem := mem_successorQueryCandidates.mpr hv.1
  rw [heq, List.mem_append, List.mem_cons] at hmem
  rw [heq, List.pairwise_append, List.pairwise_cons] at hs
  rcases hmem with hbefore | rfl | hafter
  · have hfalse := hfail v hbefore
    simp [(hpasses v).mpr hv.2] at hfalse
  · exact le_rfl
  · exact (hs.2.1.1 v hafter).le

/-- A successful scan returns exactly the minimal-rank eligible successor. -/
theorem querySuccessorRow_eq_some_iff (passes : Fin n → Bool)
    (hpasses : ∀ v, passes v = true ↔ p.womanRank v m < p.womanRank v (μ.symm v)) :
    (querySuccessorRow (p.manRank m) (μ m) passes).1 = some w ↔ IsSuccessor p μ m w := by
  refine ⟨isSuccessor_of_querySuccessorRow passes hpasses, ?_⟩
  intro hw
  cases h : (querySuccessorRow (p.manRank m) (μ m) passes).1 with
  | none =>
    rw [querySuccessorRow, runSuccessorQuery_fst, List.find?_eq_none] at h
    exact (h w (mem_successorQueryCandidates.mpr hw.eligible.1)
      ((hpasses w).mpr hw.eligible.2)).elim
  | some v =>
    rw [(isSuccessor_of_querySuccessorRow passes hpasses h).unique hw]

/-- The arc points to the current husband of the successor found in the row. -/
def queriedSuccessorGraph (menRank : Fin n → Equiv.Perm (Fin n)) (μ : Matching n)
    (passes : Fin n → Fin n → Bool) (m : Fin n) : Option (Fin n) :=
  ((querySuccessorRow (menRank m) (μ m) (passes m)).1).map μ.symm

/-- The full graph is determined by the actual row query traces. -/
theorem queriedSuccessorGraph_eq_of_agrees
    (menRank : Fin n → Equiv.Perm (Fin n)) (μ : Matching n)
    (passes other : Fin n → Fin n → Bool)
    (h : ∀ i q, q ∈ (querySuccessorRow (menRank i) (μ i) (passes i)).2 → other i q.1 = q.2) :
    queriedSuccessorGraph menRank μ other = queriedSuccessorGraph menRank μ passes := by
  funext i
  exact congrArg (fun r : Option (Fin n) × List (Fin n × Bool) ↦ r.1.map μ.symm)
    ((runSuccessorQuery_eq_iff_trace (passes i) (other i) _).mpr (h i))

/-- Fix a cycle selection rule depending only on the observed graph. -/
noncomputable def chooseQueriedRotation (f : Fin n → Option (Fin n)) :
    Option (Equiv.Perm (Fin n)) := by
  classical
  exact if h : ∃ ρ, RealizesDirectedCycle f ρ then some (Classical.choose h) else none

theorem realizesDirectedCycle_of_chooseQueriedRotation {f : Fin n → Option (Fin n)}
    {ρ : Equiv.Perm (Fin n)} (h : chooseQueriedRotation f = some ρ) :
    RealizesDirectedCycle f ρ := by
  unfold chooseQueriedRotation at h
  split at h
  · rename_i hcycle
    exact (Option.some.inj h) ▸ Classical.choose_spec hcycle
  · cases h

theorem chooseQueriedRotation_eq_none_iff (f : Fin n → Option (Fin n)) :
    chooseQueriedRotation f = none ↔ IsAcyclicSuccessor f := by
  classical
  unfold chooseQueriedRotation IsAcyclicSuccessor
  split <;> simp_all [← not_exists]

/-- A graph arc is present exactly when the next man's wife is the successor. -/
theorem queriedSuccessorGraph_eq_some_iff (passes : Fin n → Fin n → Bool)
    (hpasses : ∀ i v, passes i v = true ↔ p.womanRank v i < p.womanRank v (μ.symm v))
    (m j : Fin n) :
    queriedSuccessorGraph p.manRank μ passes m = some j ↔ IsSuccessor p μ m (μ j) := by
  simp only [queriedSuccessorGraph, Option.map_eq_some_iff, Equiv.symm_apply_eq]
  exact ⟨fun ⟨v, hv, h⟩ ↦ h ▸ (querySuccessorRow_eq_some_iff _ (hpasses m)).mp hv,
    fun hs ↦ ⟨μ j, (querySuccessorRow_eq_some_iff _ (hpasses m)).mpr hs, rfl⟩⟩

/-- A cycle of the comparison-only graph is precisely an exposed rotation. -/
theorem realizesDirectedCycle_queriedSuccessorGraph_iff (passes : Fin n → Fin n → Bool)
    (hpasses : ∀ i v, passes i v = true ↔ p.womanRank v i < p.womanRank v (μ.symm v))
    (ρ : Equiv.Perm (Fin n)) :
    RealizesDirectedCycle (queriedSuccessorGraph p.manRank μ passes) ρ ↔
      IsExposedRotation p μ ρ :=
  ⟨fun h ↦ ⟨h.1, fun m hm ↦ (queriedSuccessorGraph_eq_some_iff passes hpasses m _).mp
      (h.2 m (Equiv.Perm.mem_support.mpr hm))⟩,
    fun h ↦ ⟨h.isCycle, fun m hm ↦ (queriedSuccessorGraph_eq_some_iff passes hpasses m _).mpr
      (h.successor m (Equiv.Perm.mem_support.mp hm))⟩⟩

/-- A Boolean comparison against a known threshold, indexed by man then woman.
The score array is indexed by woman then man. -/
noncomputable def successorScoreOracle (threshold : Fin n → ℝ)
    (score : Fin n → Fin n → ℝ) (m w : Fin n) : Bool :=
  decide (score w m < threshold w)

/-- An earlier rejection remains a rejection when the threshold decreases. -/
theorem successorScoreOracle_false_of_le_threshold {upper lower : Fin n → ℝ}
    {score : Fin n → Fin n → ℝ} (hle : lower w ≤ upper w)
    (h : successorScoreOracle upper score m w = false) :
    successorScoreOracle lower score m w = false := by
  simp only [successorScoreOracle, decide_eq_false_iff_not, not_lt] at h ⊢
  exact hle.trans h

/-- Each edge of a selected cycle was recorded as a pass before its score is read. -/
theorem queriedSuccessorGraph_cycle_edge_mem_trace
    (menRank : Fin n → Equiv.Perm (Fin n)) (μ : Matching n) (passes : Fin n → Fin n → Bool)
    {ρ : Equiv.Perm (Fin n)}
    (hρ : RealizesDirectedCycle (queriedSuccessorGraph menRank μ passes) ρ)
    {m : Fin n} (hm : m ∈ ρ.support) :
    (μ (ρ m), true) ∈ (querySuccessorRow (menRank m) (μ m) (passes m)).2 := by
  have hedge := hρ.2 m hm
  simp only [queriedSuccessorGraph, Option.map_eq_some_iff, Equiv.symm_apply_eq] at hedge
  obtain ⟨_, hv, rfl⟩ := hedge
  exact runSuccessorQuery_success_mem_trace _ _ hv

/-- With known spouse scores as thresholds, comparison-only scans recover the
exposed rotations of the full profile. Only the female rows need to be tie-free. -/
theorem realizesDirectedCycle_queriedSuccessorGraph_scores_iff (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) :
    RealizesDirectedCycle (queriedSuccessorGraph (profileOfScores x).manRank μ
      (successorScoreOracle (fun w ↦ x (.inr w) (μ.symm w)) (fun w ↦ x (.inr w)))) ρ ↔
      IsExposedRotation (profileOfScores x) μ ρ :=
  realizesDirectedCycle_queriedSuccessorGraph_iff _ (fun m w ↦ by
    simp only [successorScoreOracle, decide_eq_true_eq, profileOfScores,
      rankPermutation_lt_iff (hx w)]) ρ

/-- A cycle-free stable matching is woman-optimal. Woman-optimality is
man-optimality after exchanging the two sides. -/
theorem isWomanOptimal_of_no_exposedRotation (hμ : IsStable p μ)
    (hnone : ∀ ρ, ¬ IsExposedRotation p μ ρ) : IsManOptimal (swapProfile p) μ.symm := by
  refine ⟨isStable_swapProfile_iff.mpr hμ, ?_⟩
  intro η hη w
  let ν := η.symm
  have hν : IsStable p ν :=
    isStable_swapProfile_iff.mp (by simpa only [ν, Equiv.symm_symm] using hη)
  obtain ⟨ξ, hξ, hmax⟩ := exists_stable_manRank_max hμ hν
  have hμξ : MenWeaklyPrefer p μ ξ := fun i ↦ (le_max_left _ _).trans_eq (hmax i).symm
  have heq : ξ = μ := by
    by_contra h
    obtain ⟨ρ, hρ, -⟩ := exists_exposedRotation_towards_target hμ hξ hμξ (Ne.symm h)
    exact hnone ρ hρ
  let m := η w
  have hmν : ν m = w := η.symm_apply_apply w
  change p.womanRank w (μ.symm w) ≤ p.womanRank w m
  by_contra hw
  have hwoman := lt_of_not_ge hw
  have hm : μ m ≠ w := fun h ↦ (ne_of_lt hwoman)
    (congrArg (p.womanRank w) ((Equiv.symm_apply_eq μ).mpr h.symm).symm)
  have hman : p.manRank m w ≤ p.manRank m (μ m) := by
    rw [← hmν, ← heq, hmax]
    exact le_max_right _ _
  exact hμ m w ⟨hm, lt_of_le_of_ne hman ((p.manRank m).injective.ne hm.symm), hwoman⟩

/-- If the comparison-only graph has no directed cycle, the current stable
matching is woman-optimal. -/
theorem isWomanOptimal_of_acyclic_queriedSuccessorGraph (hμ : IsStable p μ)
    (passes : Fin n → Fin n → Bool)
    (hpasses : ∀ i v, passes i v = true ↔ p.womanRank v i < p.womanRank v (μ.symm v))
    (hgraph : IsAcyclicSuccessor (queriedSuccessorGraph p.manRank μ passes)) :
    IsManOptimal (swapProfile p) μ.symm :=
  isWomanOptimal_of_no_exposedRotation hμ fun ρ hρ ↦ hgraph ρ
    ((realizesDirectedCycle_queriedSuccessorGraph_iff passes hpasses ρ).mpr hρ)

/-- If the graph obtained from known spouse scores is acyclic, the current
stable matching is woman-optimal in the profile of all scores. -/
theorem isWomanOptimal_of_acyclic_queriedSuccessorGraph_scores (x : ScoreProfile n)
    (hx : ∀ w, Function.Injective (x (.inr w))) (μ : Matching n)
    (hμ : IsStable (profileOfScores x) μ)
    (hgraph : IsAcyclicSuccessor (queriedSuccessorGraph (profileOfScores x).manRank μ
      (successorScoreOracle (fun w ↦ x (.inr w) (μ.symm w)) (fun w ↦ x (.inr w))))) :
    IsManOptimal (swapProfile (profileOfScores x)) μ.symm :=
  isWomanOptimal_of_no_exposedRotation hμ fun ρ hρ ↦ hgraph ρ
    ((realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx μ ρ).mpr hρ)

end LennonPittelFormalization

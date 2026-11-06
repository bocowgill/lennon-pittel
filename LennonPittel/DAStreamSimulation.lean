module

public import LennonPittel.DeferredAcceptanceTranscript
public import LennonPittel.UniformStreamRanks
public import LennonPittel.AdaptiveFiniteQueries

/-!
# Deferred acceptance on receiver streams

The raw clock reads a receiver from the current proposer's stream. A repeat is
counted by the raw clock but leaves the ordinal state unchanged. After completion
we keep reading from a fixed row so the raw clock can run for a fixed horizon.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

/-- Ordinal state together with each proposer's list of raw receiver draws. -/
structure DAStreamState (n : ℕ) where
  da : DAState n
  observed : Fin n → List (Fin n)

namespace DAStreamState

variable {n T : ℕ}

def initial (n : ℕ) : DAStreamState n := ⟨DAState.initial n, fun _ ↦ []⟩

/-- Choose the same free proposer as ordinal DA, with a fixed row after stopping. -/
def proposer (seed : Fin n) (s : DAStreamState n) : Fin n :=
  if h : s.da.readyMen.Nonempty then s.da.readyMen.min' h else seed

/-- Process one raw receiver draw without consulting any future draws. -/
def step (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (s : DAStreamState n) (w : Fin n) : DAStreamState n :=
  let m := proposer seed s
  let q : Profile n := ⟨fun _ ↦ Equiv.refl _, women⟩
  ⟨if s.da.readyMen.Nonempty ∧ w ∉ s.observed m then
      s.da.applyDecision m w (DAState.proposalAccepted q s.da m w)
    else s.da,
    Function.update s.observed m (s.observed m ++ [w])⟩

/-- Replay a finite list of raw answers. -/
def replay (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) : DAStreamState n :=
  ys.foldl (step seed women) (initial n)

@[simp]
theorem replay_nil (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n)) :
    replay seed women [] = initial n := rfl

@[simp]
theorem replay_append_singleton (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) (w : Fin n) :
    replay seed women (ys ++ [w]) = step seed women (replay seed women ys) w := by
  simp [replay]

theorem length_observed_step (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (s : DAStreamState n) (w i : Fin n) :
    ((step seed women s w).observed i).length =
      (s.observed i).length + if i = s.proposer seed then 1 else 0 := by
  by_cases hi : i = s.proposer seed
  · subst i
    simp [step]
  · simp [step, hi]

theorem length_observed_replay_le (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) (i : Fin n) :
    ((replay seed women ys).observed i).length ≤ ys.length := by
  induction ys using List.reverseRecOn with
  | nil => simp [initial]
  | append_singleton ys w ih =>
    simp only [replay_append_singleton, length_observed_step, List.length_append,
      List.length_singleton]
    split <;> omega

/-- The next unused raw coordinate, with an arbitrary value beyond the horizon. -/
def query (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n)) (hT : 0 < T)
    (ys : List (Fin n)) : Fin n × Fin T :=
  let s := replay seed women ys
  let m := s.proposer seed
  (m, if h : (s.observed m).length < T then ⟨(s.observed m).length, h⟩ else ⟨0, hT⟩)

theorem query_index_val (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (hT : 0 < T) {ys : List (Fin n)} (hy : ys.length < T) :
    (query seed women hT ys).2.val =
      ((replay seed women ys).observed ((replay seed women ys).proposer seed)).length := by
  simp [query, (length_observed_replay_le seed women ys _).trans_lt hy]

private theorem observed_take_mono (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    (ys : List (Fin n)) (m : Fin n) :
    Monotone fun k ↦ ((replay seed women (ys.take k)).observed m).length := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < ys.length
  · rw [List.take_succ_eq_append_getElem hk, replay_append_singleton, length_observed_step]
    exact Nat.le_add_right _ _
  · rw [List.take_of_length_le (Nat.le_of_not_lt hk),
      List.take_of_length_le (by omega : ys.length ≤ k + 1)]

/-- The raw query never reuses a table coordinate on any transcript of length T. -/
theorem query_injective (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n)) (hT : 0 < T)
    (ys : Fin T → Fin n) :
    Function.Injective (fun t : Fin T ↦ query seed women hT ((List.ofFn ys).take t.val)) := by
  let l := List.ofFn ys
  let S := fun t : ℕ ↦ replay seed women (l.take t)
  have hlen (t : Fin T) : (l.take t.val).length < T :=
    (List.length_take_le _ _).trans_lt t.isLt
  have hne (i j : Fin T) (hij : i < j) :
      query seed women hT (l.take i.val) ≠ query seed women hT (l.take j.val) := by
    intro h
    let m := (S i.val).proposer seed
    have hm : m = (S j.val).proposer seed := congrArg Prod.fst h
    have hcount : ((S i.val).observed m).length = ((S j.val).observed m).length := by
      have he := congrArg (fun a : Fin n × Fin T ↦ a.2.val) h
      change (query seed women hT (l.take i.val)).2.val =
        (query seed women hT (l.take j.val)).2.val at he
      rw [query_index_val seed women hT (hlen i), query_index_val seed women hT (hlen j)] at he
      exact he.trans (congrArg (fun a ↦ ((S j.val).observed a).length) hm.symm)
    have hi : i.val < l.length := by simp [l]
    have hstep : ((S (i.val + 1)).observed m).length = ((S i.val).observed m).length + 1 := by
      change ((replay seed women (l.take (i.val + 1))).observed m).length = _
      rw [List.take_succ_eq_append_getElem hi, replay_append_singleton, length_observed_step,
        ite_eq_left (show m = (S i.val).proposer seed from rfl)]
    have hle := observed_take_mono seed women l m (show i.val + 1 ≤ j.val from hij)
    change ((S (i.val + 1)).observed m).length ≤ ((S j.val).observed m).length at hle
    omega
  intro i j h
  exact le_antisymm (le_of_not_gt (fun hji ↦ hne j i hji h.symm))
    (le_of_not_gt (fun hij ↦ hne i j hij h))

/-- The full profile attached to a finite table and independent fallback ranks. -/
noncomputable def streamProfile (raw : Fin n × Fin T → Fin n)
    (fallback women : Fin n → Equiv.Perm (Fin n)) : Profile n :=
  ⟨fun m ↦ streamRank (fun j ↦ raw (m, j)) (fallback m), women⟩

/-- Every observed row is a prefix of the specified table. -/
def ObservationsMatch (s : DAStreamState n) (raw : Fin n × Fin T → Fin n) : Prop :=
  ∀ m, s.observed m = (List.ofFn fun j : Fin T ↦ raw (m, j)).take (s.observed m).length

/-- While DA runs, the distinct observations are exactly the true proposals. -/
def Agrees (s : DAStreamState n) (p : Profile n) : Prop :=
  s.da.Valid p ∧ (s.da.readyMen.Nonempty → ∀ m w,
    w ∈ s.observed m ↔ (p.manRank m w).val < s.da.count m)

theorem initial_agrees (p : Profile n) : (initial n).Agrees p := by
  refine ⟨DAState.initial_valid p, ?_⟩
  simp [initial, DAState.initial]

theorem initial_observationsMatch (raw : Fin n × Fin T → Fin n) :
    (initial n).ObservationsMatch raw := by
  intro m
  simp [initial]

theorem observationsMatch_step (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    {s : DAStreamState n} {raw : Fin n × Fin T → Fin n} (hs : s.ObservationsMatch raw)
    (h : (s.observed (s.proposer seed)).length < T) :
    (s.step seed women (raw (s.proposer seed, ⟨_, h⟩))).ObservationsMatch raw := by
  intro m
  by_cases hm : m = s.proposer seed
  · subst m
    simp only [step, Function.update_self, List.length_append, List.length_singleton]
    rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using h),
      List.getElem_ofFn, ← hs]
  · simpa only [step, Function.update_of_ne hm] using hs m

private theorem rank_eq_count_of_lower_iff {rank : Equiv.Perm (Fin n)} {w : Fin n} {k : ℕ}
    (hk : k < n) (h : ∀ v, rank v < rank w ↔ (rank v).val < k) : (rank w).val = k := by
  apply le_antisymm
  · by_contra! hlt
    let v := rank.symm ⟨k, hk⟩
    have hv : rank v = ⟨k, hk⟩ := rank.apply_symm_apply _
    have hvlt : rank v < rank w := by
      rw [hv]
      exact hlt
    have hvk := (h v).mp hvlt
    rw [hv] at hvk
    exact (lt_irrefl k) hvk
  · by_contra! hlt
    exact (lt_irrefl (rank w)) ((h w).mpr hlt)

private theorem fresh_ordinal_rank (seed : Fin n) {s : DAStreamState n}
    {raw : Fin n × Fin T → Fin n} {fallback women : Fin n → Equiv.Perm (Fin n)}
    (hs : s.Agrees (streamProfile raw fallback women)) (hObs : s.ObservationsMatch raw)
    (hready : s.da.readyMen.Nonempty) (hidx : (s.observed (s.proposer seed)).length < T)
    (hfresh : raw (s.proposer seed, ⟨_, hidx⟩) ∉ s.observed (s.proposer seed)) :
    ((streamProfile raw fallback women).manRank (s.proposer seed)
      (raw (s.proposer seed, ⟨_, hidx⟩))).val = s.da.count (s.proposer seed) := by
  let m := s.proposer seed
  let i : Fin T := ⟨(s.observed m).length, hidx⟩
  let row := fun j : Fin T ↦ raw (m, j)
  have hmem (w : Fin n) : w ∈ s.observed m ↔ ∃ j : Fin T, j < i ∧ row j = w := by
    rw [hObs m]
    constructor
    · intro hw
      obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hw
      have hj' : j < i.val := hj.trans_le (List.length_take_le _ _)
      exact ⟨⟨j, hj'.trans i.isLt⟩, hj', by simpa only [List.getElem_take,
        List.getElem_ofFn] using he⟩
    · rintro ⟨j, hj, rfl⟩
      apply List.mem_iff_getElem.mpr
      have hj' : j.val < ((List.ofFn row).take i.val).length := by
        simp only [List.length_take, List.length_ofFn, lt_min_iff]
        exact ⟨hj, j.isLt⟩
      exact ⟨j.val, hj', by rw [List.getElem_take, List.getElem_ofFn]⟩
  have hf : ∀ j : Fin T, j < i → row j ≠ row i :=
    fun j hj he ↦ hfresh ((hmem _).mpr ⟨j, hj, he⟩)
  have hm : m ∈ s.da.readyMen := by
    simpa only [m, proposer, dite_eq_left hready] using Finset.min'_mem _ hready
  change (streamRank row (fallback m) (row i)).val = s.da.count m
  apply rank_eq_count_of_lower_iff (DAState.mem_readyMen.mp hm).2
  intro w
  exact (streamRank_lt_fresh_iff row (fallback m) i hf w).trans
    ((hmem w).symm.trans (hs.2 hready m w))

private theorem nextProposal_eq_of_fresh (seed : Fin n) {s : DAStreamState n}
    {p : Profile n} {w : Fin n} (hready : s.da.readyMen.Nonempty)
    (hrank : (p.manRank (s.proposer seed) w).val = s.da.count (s.proposer seed)) :
    s.da.nextProposal p.manRank = some (s.proposer seed, w) := by
  have hw : s.da.proposalTarget p.manRank (s.proposer seed)
      ((DAState.mem_readyMen.mp (by
        simpa only [proposer, dite_eq_left hready] using Finset.min'_mem _ hready)).2) = w := by
    unfold DAState.proposalTarget
    apply (p.manRank (s.proposer seed)).symm_apply_eq.mpr
    exact Fin.ext hrank.symm
  simpa only [DAState.nextProposal, proposer, dite_eq_left hready, Option.some.injEq,
    Prod.mk.injEq, true_and] using hw

private theorem fresh_step (seed : Fin n) {s : DAStreamState n}
    {p : Profile n} {w : Fin n} (hready : s.da.readyMen.Nonempty)
    (hf : w ∉ s.observed (s.proposer seed))
    (hrank : (p.manRank (s.proposer seed) w).val = s.da.count (s.proposer seed)) :
    (s.step seed p.womanRank w).da = s.da.advance p := by
  rw [DAState.advance, nextProposal_eq_of_fresh seed hready hrank]
  simp only [step, ite_eq_left (And.intro hready hf)]
  rfl

theorem agrees_step (seed : Fin n) {s : DAStreamState n}
    {raw : Fin n × Fin T → Fin n} {fallback women : Fin n → Equiv.Perm (Fin n)}
    (hs : s.Agrees (streamProfile raw fallback women)) (hObs : s.ObservationsMatch raw)
    (hidx : (s.observed (s.proposer seed)).length < T) :
    let w := raw (s.proposer seed, ⟨_, hidx⟩)
    (s.step seed women w).Agrees (streamProfile raw fallback women) ∧
    (s.step seed women w).da.proposalCount ≤ s.da.proposalCount + 1 := by
  let p := streamProfile raw fallback women
  let m := s.proposer seed
  let w := raw (m, ⟨_, hidx⟩)
  let t := s.step seed women w
  change t.Agrees p ∧ t.da.proposalCount ≤ s.da.proposalCount + 1
  have hobs : t.observed = Function.update s.observed m (s.observed m ++ [w]) := rfl
  by_cases hready : s.da.readyMen.Nonempty
  · by_cases hseen : w ∈ s.observed m
    · have hda : t.da = s.da := by simp [t, step, m, hseen]
      refine ⟨⟨hda ▸ hs.1, ?_⟩, by rw [hda]; exact Nat.le_succ _⟩
      intro _ i v
      rw [hda, hobs]
      by_cases hi : i = m
      · subst i
        rw [Function.update_self, List.mem_append, List.mem_singleton, ← hs.2 hready m v]
        exact ⟨fun hv ↦ hv.elim id (fun h ↦ h ▸ hseen), Or.inl⟩
      · simpa only [Function.update_of_ne hi] using hs.2 hready i v
    · have hrank := fresh_ordinal_rank seed hs hObs hready hidx hseen
      have hda : t.da = s.da.advance p := fresh_step seed hready hseen hrank
      have hnext : s.da.nextProposal p.manRank = some (m, w) :=
        nextProposal_eq_of_fresh seed hready hrank
      refine ⟨⟨hda ▸ hs.1.advance, ?_⟩, ?_⟩
      · intro _ i v
        rw [hda, DAState.advance, hnext, hobs]
        by_cases hi : i = m
        · subst i
          have he : v = w ↔ (p.manRank m v).val = s.da.count m :=
            ⟨fun h ↦ h ▸ hrank, fun h ↦ (p.manRank m).injective
              (Fin.ext (h.trans hrank.symm))⟩
          simp only [DAState.applyDecision, Function.update_self, List.mem_append,
            List.mem_singleton]
          have hprev : v ∈ s.observed m ↔ (p.manRank m v).val < s.da.count m :=
            hs.2 hready m v
          rw [hprev, he]
          omega
        · simpa only [DAState.applyDecision, Function.update_of_ne hi] using
            hs.2 hready i v
      · rw [hda, DAState.proposalCount_advance_of_some hnext]
  · have hda : t.da = s.da := by simp [t, step, hready]
    exact ⟨⟨hda ▸ hs.1, fun h ↦ (hready (hda ▸ h)).elim⟩,
      by rw [hda]; exact Nat.le_succ _⟩

private theorem step_preserves_observed (seed : Fin n)
    (women : Fin n → Equiv.Perm (Fin n)) (s : DAStreamState n) (v : Fin n)
    {m w : Fin n} (hw : w ∈ s.observed m) : w ∈ (s.step seed women v).observed m := by
  by_cases hm : m = s.proposer seed
  · subst m
    simpa only [step, Function.update_self, List.mem_append] using Or.inl hw
  · simpa only [step, Function.update_of_ne hm] using hw

/-- Each raw draw is recorded in some row of the replay. -/
theorem exists_mem_observed_of_mem (seed : Fin n) (women : Fin n → Equiv.Perm (Fin n))
    {ys : List (Fin n)} {w : Fin n} (hw : w ∈ ys) :
    ∃ m, w ∈ (replay seed women ys).observed m := by
  induction ys using List.reverseRecOn with
  | nil => simp at hw
  | append_singleton ys v ih =>
    rw [replay_append_singleton]
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨m, hm⟩ := ih h
      exact ⟨m, step_preserves_observed seed women _ v hm⟩
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨(replay seed women ys).proposer seed, by simp [step]⟩

/-- When the raw history includes every receiver, the ordinal part has finished. -/
theorem complete_of_covers (seed : Fin n) {p : Profile n} {ys : List (Fin n)}
    (hs : (replay seed p.womanRank ys).Agrees p) (hcover : ∀ w : Fin n, w ∈ ys) :
    (replay seed p.womanRank ys).da.Complete := by
  classical
  let s := replay seed p.womanRank ys
  have hnone : s.da.nextProposal p.manRank = none := by
    by_contra hnext
    have hr : s.da.readyMen.Nonempty := by
      by_contra h
      exact hnext (by simp [DAState.nextProposal, h])
    have hheld (w : Fin n) : ∃ a, s.da.held w = some a := by
      obtain ⟨m, hm⟩ := exists_mem_observed_of_mem seed p.womanRank (hcover w)
      obtain ⟨a, ha, _⟩ := hs.1.preferred_holder ((hs.2 hr m w).mp hm)
      exact ⟨a, ha⟩
    let holder (w : Fin n) := Classical.choose (hheld w)
    have hholder (w : Fin n) : s.da.held w = some (holder w) := Classical.choose_spec (hheld w)
    have hi : Function.Injective holder := fun u v huv ↦
      hs.1.held_unique (hholder u) (by rw [huv]; exact hholder v)
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hi (s.da.readyMen.min' hr)
    exact (DAState.mem_readyMen.mp (Finset.min'_mem _ hr)).1 w (hw ▸ hholder w)
  exact hs.1.complete_of_nextProposal_none hnone

private theorem proposalCount_eq_run_sq_of_complete {p : Profile n} {s : DAState n}
    (hs : s.Valid p) (hc : s.Complete) :
    s.proposalCount = (DAState.run p (n * n)).proposalCount := by
  let μ := s.toMatching hc
  let ν := DAState.matching p
  have hμ := hs.isManOptimal_toMatching hc
  have hν := DAState.isManOptimal_matching p
  have he (m : Fin n) : p.manRank m (μ m) = p.manRank m (ν m) :=
    le_antisymm (hμ.2 ν hν.1 m) (hν.2 μ hμ.1 m)
  unfold DAState.proposalCount
  apply Finset.sum_congr rfl
  intro m _
  rw [← hs.held_last (s.held_toMatching hc m),
    ← (DAState.valid_run p _).held_last ((DAState.run p _).held_toMatching
      (DAState.complete_run_sq p) m)]
  change (p.manRank m (μ m)).val + 1 = (p.manRank m (ν m)).val + 1
  rw [he]

/-- During a raw transcript the ordinary DA state is valid, and each tick costs at most
one true proposal. -/
theorem replay_adaptiveTranscript (seed : Fin n) (hT : 0 < T)
    (raw : Fin n × Fin T → Fin n) (fallback women : Fin n → Equiv.Perm (Fin n))
    (t : ℕ) (ht : t ≤ T) :
    let s := replay seed women (adaptiveTranscript (query seed women hT) raw t)
    s.ObservationsMatch raw ∧ s.Agrees (streamProfile raw fallback women) ∧
      s.da.proposalCount ≤ t := by
  induction t with
  | zero =>
    exact ⟨initial_observationsMatch raw, initial_agrees _, by
      simp [adaptiveTranscript, DAState.proposalCount, initial, DAState.initial]⟩
  | succ t ih =>
    let ys := adaptiveTranscript (query seed women hT) raw t
    let s := replay seed women ys
    let m := s.proposer seed
    have hy : ys.length = t := length_adaptiveTranscript _ _ _
    have hi : (s.observed m).length < T :=
      (length_observed_replay_le seed women ys m).trans_lt (hy ▸ Nat.lt_of_succ_le ht)
    have hq : query seed women hT ys = (m, ⟨(s.observed m).length, hi⟩) := by
      change (m, (if h : (s.observed m).length < T then
        (⟨(s.observed m).length, h⟩ : Fin T) else ⟨0, hT⟩)) = _
      rw [dite_eq_left hi]
    obtain ⟨ho, hv, hp⟩ := ih (Nat.le_of_succ_le ht)
    have hy' : adaptiveTranscript (query seed women hT) raw (t + 1) =
        ys ++ [raw (query seed women hT ys)] := rfl
    dsimp only
    rw [hy', hq, replay_append_singleton]
    obtain ⟨hv', hp'⟩ := agrees_step seed hv ho hi
    exact ⟨observationsMatch_step seed women ho hi, hv', hp'.trans (Nat.succ_le_succ hp)⟩

/-- Covering every receiver by the raw horizon bounds the number of ordinal proposals. -/
theorem proposalCount_le_of_adaptiveTranscript_covers (seed : Fin n) (hT : 0 < T)
    (raw : Fin n × Fin T → Fin n) (fallback women : Fin n → Equiv.Perm (Fin n))
    (hcover : ∀ w : Fin n, ∃ t : Fin T, adaptiveTranscriptFn (query seed women hT) raw T t = w) :
    (DAState.run (streamProfile raw fallback women) (n * n)).proposalCount ≤ T := by
  let ys := adaptiveTranscript (query seed women hT) raw T
  let s := replay seed women ys
  let p := streamProfile raw fallback women
  obtain ⟨_, hv, hcount⟩ := replay_adaptiveTranscript seed hT raw fallback women T le_rfl
  change s.Agrees p at hv
  change s.da.proposalCount ≤ T at hcount
  change (DAState.run p (n * n)).proposalCount ≤ T
  have hlist (w : Fin n) : w ∈ ys := by
    change w ∈ adaptiveTranscript (query seed women hT) raw T
    rw [← ofFn_adaptiveTranscriptFn (query seed women hT) raw T]
    exact List.mem_ofFn.mpr (hcover w)
  have hc : s.da.Complete := complete_of_covers (p := p) seed hv hlist
  rw [← proposalCount_eq_run_sq_of_complete hv.1 hc]
  exact hcount

end DAStreamState
end LennonPittelFormalization

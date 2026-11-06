module

public import LennonPittel.ManOptimal
public import LennonPittel.ScoreRanks
public import Mathlib.Data.Finset.Max

/-!
# An ordinal deferred-acceptance transcript

The proposal state keeps a count for each man and an optional tentative
husband for each woman. Choosing whom to ask uses men's ranks and the state.
Updating the state then requires at most one comparison in the receiving
woman's ranking.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

/-- The state of men-proposing deferred acceptance. -/
structure DAState (n : ℕ) where
  /-- How many of his first choices a man has proposed to. -/
  count : Fin n → ℕ
  /-- The tentative husband, if any, of each woman. -/
  held : Fin n → Option (Fin n)

namespace DAState

variable {n : ℕ}

/-- No woman is currently holding this man's proposal. -/
def Free (s : DAState n) (m : Fin n) : Prop := ∀ w, s.held w ≠ some m

/-- The state before any proposals have been made. -/
def initial (n : ℕ) : DAState n := ⟨fun _ ↦ 0, fun _ ↦ none⟩

/-- The next woman on a man's list, without consulting any women's ranks. -/
def proposalTarget (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n)
    (m : Fin n) (h : s.count m < n) : Fin n := (rank m).symm ⟨s.count m, h⟩

/-- The incumbent stays only when she exists and the new proposal loses. -/
def chosenHolder (s : DAState n) (m w : Fin n) (accept : Bool) : Fin n :=
  if accept then m else (s.held w).getD m

/-- Update the state using only the outcome of the new proposal. -/
def applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) : DAState n :=
  ⟨Function.update s.count m (s.count m + 1),
    Function.update s.held w (some (s.chosenHolder m w accept))⟩

/-- An empty slot accepts automatically; an occupied slot compares two men. -/
def proposalAccepted (p : Profile n) (s : DAState n) (m w : Fin n) : Bool :=
  (s.held w).elim true fun a ↦ decide (p.womanRank w m < p.womanRank w a)

/-- Invariants for an ordinal proposal state and its rejected pairs. -/
structure Valid (p : Profile n) (s : DAState n) : Prop where
  count_le : ∀ m, s.count m ≤ n
  held_unique : ∀ {u v m}, s.held u = some m → s.held v = some m → u = v
  held_last : ∀ {w m}, s.held w = some m → (p.manRank m w).val + 1 = s.count m
  preferred_holder : ∀ {m w}, (p.manRank m w).val < s.count m →
    ∃ a, s.held w = some a ∧ p.womanRank w a ≤ p.womanRank w m
  not_rejected : ∀ (ν : Matching n), IsStable p ν → ∀ m,
    (p.manRank m (ν m)).val < s.count m → s.held (ν m) = some m

/-- The empty proposal history satisfies the invariants. -/
theorem initial_valid (p : Profile n) : Valid p (initial n) := by
  constructor
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]

private theorem chosenHolder_spec (p : Profile n) (s : DAState n) (m w : Fin n) :
    let b := s.chosenHolder m w (proposalAccepted p s m w)
    (b = m ∨ s.held w = some b) ∧ p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a := by
  cases h : s.held w with
  | none => simp [chosenHolder, proposalAccepted, h]
  | some a =>
    by_cases ha : p.womanRank w m < p.womanRank w a
    · simp [chosenHolder, proposalAccepted, h, ha, ha.le]
    · simp [chosenHolder, proposalAccepted, h, ha, le_of_not_gt ha]

/-- One proposal by a free man preserves all rejection invariants. -/
theorem Valid.apply_proposal {p : Profile n} {s : DAState n}
    (hs : Valid p s) {m w : Fin n} (hm : s.Free m)
    (hnew : (p.manRank m w).val = s.count m) :
    Valid p (s.applyDecision m w (proposalAccepted p s m w)) := by
  let b := s.chosenHolder m w (proposalAccepted p s m w)
  let t := s.applyDecision m w (proposalAccepted p s m w)
  have hspec : (b = m ∨ s.held w = some b) ∧
      p.womanRank w b ≤ p.womanRank w m ∧
      ∀ a, s.held w = some a → p.womanRank w b ≤ p.womanRank w a :=
    chosenHolder_spec p s m w
  have htCount : t.count m = s.count m + 1 := by simp [t, applyDecision]
  have htCount' {i : Fin n} (hi : i ≠ m) : t.count i = s.count i := by
    simp [t, applyDecision, hi]
  have htHeld : t.held w = some b := by simp [t, b, applyDecision]
  have htHeld' {v : Fin n} (hv : v ≠ w) : t.held v = s.held v := by
    simp [t, applyDecision, hv]
  have hsHeld_ne {v i : Fin n} (hi : s.held v = some i) : i ≠ m := by
    rintro rfl
    exact hm v hi
  have no_other_hold {v : Fin n} (hv : v ≠ w) (h : s.held v = some b) : False := by
    rcases hspec.1 with hbm | hbw
    · exact hm v (hbm ▸ h)
    · exact hv (hs.held_unique h hbw)
  have old_proposal {i v : Fin n} (hv : v ≠ w)
      (hi : (p.manRank i v).val < t.count i) : (p.manRank i v).val < s.count i := by
    by_cases him : i = m
    · subst i
      rw [htCount, ← hnew] at hi
      have hne : (p.manRank m v).val ≠ (p.manRank m w).val :=
        fun h ↦ hv ((p.manRank m).injective (Fin.ext h))
      rw [← hnew]
      omega
    · exact htCount' him ▸ hi
  have winner_prefers {ν : Matching n} (hν : IsStable p ν) :
      p.manRank b w ≤ p.manRank b (ν b) := by
    by_contra! hlt
    have hlt' : (p.manRank b (ν b)).val < (p.manRank b w).val := hlt
    rcases hspec.1 with hbm | hbw
    · rw [hbm, hnew] at hlt'
      exact hm (ν m) (hs.not_rejected ν hν m hlt')
    · have hp : (p.manRank b (ν b)).val < s.count b := by
        have := hs.held_last hbw
        omega
      have heq := hs.held_unique (hs.not_rejected ν hν b hp) hbw
      exact (not_lt_of_ge (le_of_eq (congrArg (p.manRank b) heq.symm))) hlt
  have proposed_dominance {i : Fin n} (hi : (p.manRank i w).val < t.count i) :
      p.womanRank w b ≤ p.womanRank w i := by
    by_cases him : i = m
    · exact him ▸ hspec.2.1
    · have hprop : (p.manRank i w).val < s.count i := htCount' him ▸ hi
      obtain ⟨a, ha, hpref⟩ := hs.preferred_holder hprop
      exact (hspec.2.2 a ha).trans hpref
  change Valid p t
  constructor
  · intro i
    by_cases h : i = m
    · subst i
      rw [htCount, ← hnew]
      exact Nat.succ_le_of_lt (p.manRank m w).isLt
    · exact (htCount' h).trans_le (hs.count_le i)
  · intro u v i hu hv
    by_cases huw : u = w
    · subst u
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hu)
      subst i
      by_contra hvw
      exact no_other_hold (Ne.symm hvw) ((htHeld' (Ne.symm hvw)).symm.trans hv)
    · by_cases hvw : v = w
      · subst v
        have hbi : b = i := Option.some.inj (htHeld.symm.trans hv)
        subst i
        exact False.elim (no_other_hold huw ((htHeld' huw).symm.trans hu))
      · exact hs.held_unique ((htHeld' huw).symm.trans hu) ((htHeld' hvw).symm.trans hv)
  · intro v i hvi
    by_cases hv : v = w
    · subst v
      have hbi : b = i := Option.some.inj (htHeld.symm.trans hvi)
      subst i
      rcases hspec.1 with hbm | hbw
      · rw [hbm, htCount, hnew]
      · exact (hs.held_last hbw).trans (htCount' (hsHeld_ne hbw)).symm
    · have h := (htHeld' hv).symm.trans hvi
      exact (hs.held_last h).trans (htCount' (hsHeld_ne h)).symm
  · intro i v hi
    by_cases hv : v = w
    · subst v
      exact ⟨b, htHeld, proposed_dominance hi⟩
    · obtain ⟨a, ha, hle⟩ := hs.preferred_holder (old_proposal hv hi)
      exact ⟨a, (htHeld' hv).trans ha, hle⟩
  · intro ν hν i hi
    by_cases hw : ν i = w
    · rw [hw] at hi ⊢
      by_contra h
      have hbi : b ≠ i := fun e ↦ h (e ▸ htHeld)
      have hbν : ν b ≠ w := fun e ↦ hbi (ν.injective (e.trans hw.symm))
      have hbPref : p.manRank b w < p.manRank b (ν b) :=
        lt_of_le_of_ne (winner_prefers hν) fun e ↦ hbν ((p.manRank b).injective e).symm
      have hwPref : p.womanRank w b < p.womanRank w (ν.symm w) := by
        rw [← hw, ν.symm_apply_apply, hw]
        exact lt_of_le_of_ne (proposed_dominance hi) fun e ↦ hbi ((p.womanRank w).injective e)
      exact hν b w ⟨hbν, hbPref, hwPref⟩
    · exact (htHeld' hw).trans (hs.not_rejected ν hν i (old_proposal hw hi))

/-- A free man in a valid state has an untried woman. -/
theorem Valid.free_count_lt {p : Profile n} {s : DAState n} (hs : Valid p s)
    {m : Fin n} (hm : s.Free m) : s.count m < n := by
  classical
  by_contra! h
  have hheld (w : Fin n) : ∃ a, s.held w = some a := by
    obtain ⟨a, ha, _⟩ := hs.preferred_holder ((p.manRank m w).isLt.trans_le h)
    exact ⟨a, ha⟩
  let holder (w : Fin n) := Classical.choose (hheld w)
  have hholder (w : Fin n) : s.held w = some (holder w) := Classical.choose_spec (hheld w)
  have hi : Function.Injective holder := fun u v huv ↦
    hs.held_unique (hholder u) (by rw [huv]; exact hholder v)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hi m
  exact hm w (hw ▸ hholder w)

/-- Every man has a tentative wife. -/
def Complete (s : DAState n) : Prop := ∀ m, ∃ w, s.held w = some m

/-- A complete proposal state determines a matching. -/
noncomputable def toMatching (s : DAState n) (hc : s.Complete) : Matching n := by
  let wife (m : Fin n) := Classical.choose (hc m)
  have hw (m : Fin n) : s.held (wife m) = some m := Classical.choose_spec (hc m)
  have hi : Function.Injective wife := by
    intro m a h
    exact Option.some.inj ((hw m).symm.trans (h ▸ hw a))
  exact Equiv.ofBijective wife ⟨hi, Finite.surjective_of_injective hi⟩

/-- The matching from a complete state agrees with its tentative holdings. -/
theorem held_toMatching (s : DAState n) (hc : s.Complete) (m : Fin n) :
    s.held (s.toMatching hc m) = some m :=
  Classical.choose_spec (hc m)

/-- The matching from a valid complete state is man-optimal. -/
theorem Valid.isManOptimal_toMatching {p : Profile n} {s : DAState n} (hs : Valid p s)
    (hc : s.Complete) : IsManOptimal p (s.toMatching hc) := by
  let μ := s.toMatching hc
  have hh := s.held_toMatching hc
  change IsManOptimal p μ
  constructor
  · intro m w hb
    have hl := hs.held_last (hh m)
    have hrank : (p.manRank m w).val < s.count m := by
      exact (show (p.manRank m w).val < (p.manRank m (μ m)).val from hb.2.1).trans
        (hl ▸ Nat.lt_succ_self _)
    obtain ⟨a, ha, hpref⟩ := hs.preferred_holder hrank
    have ha' := hh (μ.symm w)
    change s.held (μ (μ.symm w)) = _ at ha'
    rw [μ.apply_symm_apply] at ha'
    have heq := Option.some.inj (ha.symm.trans ha')
    exact hb.2.2.not_ge (heq ▸ hpref)
  · intro ν hν m
    by_contra! h
    have hrank : (p.manRank m (ν m)).val < s.count m := by
      exact (show (p.manRank m (ν m)).val < (p.manRank m (μ m)).val from h).trans
        (hs.held_last (hh m) ▸ Nat.lt_succ_self _)
    have hmate := hs.held_unique (hs.not_rejected ν hν m hrank) (hh m)
    exact h.ne (congrArg (p.manRank m) hmate)

/-- Free men who still have a woman to propose to. -/
def readyMen (s : DAState n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ (∀ w, s.held w ≠ some m) ∧ s.count m < n

theorem mem_readyMen {s : DAState n} {m : Fin n} :
    m ∈ s.readyMen ↔ s.Free m ∧ s.count m < n := by
  simp [readyMen, Free]

/-- A deterministic proposal command. The first free man proposes to his next choice. -/
def nextProposal (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Option (Fin n × Fin n) :=
  if h : s.readyMen.Nonempty then
    let m := s.readyMen.min' h
    let hm := mem_readyMen.mp (Finset.min'_mem _ h)
    some (m, s.proposalTarget rank m hm.2)
  else none

/-- A proposal command chooses a free man and his next ranked woman. -/
theorem nextProposal_some {rank : Fin n → Equiv.Perm (Fin n)} {s : DAState n}
    {m w : Fin n} (h : s.nextProposal rank = some (m, w)) :
    s.Free m ∧ (rank m w).val = s.count m := by
  unfold nextProposal at h
  split at h
  · rename_i hne
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨(mem_readyMen.mp (Finset.min'_mem _ hne)).1, by simp [proposalTarget]⟩
  · contradiction

/-- If the proposal command stops in a valid state, every man has a tentative wife. -/
theorem Valid.complete_of_nextProposal_none {p : Profile n} {s : DAState n}
    (hs : Valid p s) (hd : s.nextProposal p.manRank = none) : s.Complete := by
  classical
  intro m
  by_contra! hm
  have hfree : s.Free m := hm
  have hne : s.readyMen.Nonempty := ⟨m, mem_readyMen.mpr ⟨hfree, hs.free_count_lt hfree⟩⟩
  simp [nextProposal, hne] at hd

/-- Execute one proposal if possible, with the comparison supplied by the profile. -/
def advance (p : Profile n) (s : DAState n) : DAState n :=
  match s.nextProposal p.manRank with
  | none => s
  | some (m, w) => s.applyDecision m w (proposalAccepted p s m w)

/-- A proposal step preserves validity. -/
theorem Valid.advance {p : Profile n} {s : DAState n} (hs : Valid p s) :
    Valid p (advance p s) := by
  cases h : s.nextProposal p.manRank with
  | none => simpa only [DAState.advance, h] using hs
  | some a =>
    obtain ⟨m, w⟩ := a
    have hp := nextProposal_some h
    simpa only [DAState.advance, h] using hs.apply_proposal hp.1 hp.2

/-- The sum of the men's proposal counts is the number of proposals made so far. -/
def proposalCount (s : DAState n) : ℕ := ∑ m, s.count m

private theorem proposalCount_applyDecision (s : DAState n) (m w : Fin n) (accept : Bool) :
    (s.applyDecision m w accept).proposalCount = s.proposalCount + 1 := by
  let t := s.applyDecision m w accept
  have hm : m ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have he :
      ∑ i ∈ Finset.univ.erase m, t.count i = ∑ i ∈ Finset.univ.erase m, s.count i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [t, applyDecision, (Finset.mem_erase.mp hi).1]
  change t.proposalCount = _
  unfold proposalCount
  rw [← Finset.sum_erase_add _ t.count hm, ← Finset.sum_erase_add _ s.count hm, he]
  simp [t, applyDecision, add_assoc]

/-- A nonterminal step increments the proposal count. -/
theorem proposalCount_advance_of_some {p : Profile n} {s : DAState n} {a : Fin n × Fin n}
    (h : s.nextProposal p.manRank = some a) :
    (advance p s).proposalCount = s.proposalCount + 1 := by
  obtain ⟨m, w⟩ := a
  rw [advance, h]
  exact proposalCount_applyDecision s m w _

/-- A valid state cannot have made more than `n²` proposals. -/
theorem Valid.proposalCount_le {p : Profile n} {s : DAState n} (hs : Valid p s) :
    s.proposalCount ≤ n * n := by
  calc
    _ ≤ ∑ _ : Fin n, n := Finset.sum_le_sum fun m _ ↦ hs.count_le m
    _ = _ := by simp

/-- The ordinal DA history, padded with a fixed state after termination. -/
def run (p : Profile n) : ℕ → DAState n
  | 0 => initial n
  | k + 1 => advance p (run p k)

/-- Every state in the history is valid. -/
theorem valid_run (p : Profile n) (k : ℕ) : Valid p (run p k) := by
  induction k with
  | zero => exact initial_valid p
  | succ k ih => exact ih.advance

private theorem le_proposalCount_run_of_next {p : Profile n} {k : ℕ}
    (h : (run p k).nextProposal p.manRank ≠ none) : k ≤ (run p k).proposalCount := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases hprev : (run p k).nextProposal p.manRank with
    | none =>
      have he : run p (k + 1) = run p k := by simp only [run, advance, hprev]
      exact False.elim (h (he ▸ hprev))
    | some a =>
      have hcount := proposalCount_advance_of_some hprev
      change k + 1 ≤ (advance p (run p k)).proposalCount
      rw [hcount]
      exact Nat.succ_le_succ (ih (by rw [hprev]; exact Option.some_ne_none _))

/-- The proposal history is terminal by the deterministic horizon `n²`. -/
theorem nextProposal_run_sq_eq_none (p : Profile n) :
    (run p (n * n)).nextProposal p.manRank = none := by
  cases h : (run p (n * n)).nextProposal p.manRank with
  | none => rfl
  | some a =>
    have hl := le_proposalCount_run_of_next (p := p) (k := n * n)
      (by rw [h]; exact Option.some_ne_none _)
    have hu := (valid_run p (n * n + 1)).proposalCount_le
    change (advance p (run p (n * n))).proposalCount ≤ n * n at hu
    rw [proposalCount_advance_of_some h] at hu
    omega

/-- The proposal history terminates in a complete state. -/
theorem complete_run_sq (p : Profile n) : (run p (n * n)).Complete :=
  (valid_run p (n * n)).complete_of_nextProposal_none (nextProposal_run_sq_eq_none p)

/-- Deferred acceptance yields the man-optimal stable matching. -/
noncomputable def matching (p : Profile n) : Matching n :=
  (run p (n * n)).toMatching (complete_run_sq p)

theorem isManOptimal_matching (p : Profile n) : IsManOptimal p (matching p) :=
  (valid_run p (n * n)).isManOptimal_toMatching (complete_run_sq p)

/-- A man proposed to exactly the prefix through his final wife, inclusive. -/
theorem proposed_run_sq_iff (p : Profile n) (m w : Fin n) :
    (p.manRank m w).val < (run p (n * n)).count m ↔
      p.manRank m w ≤ p.manRank m (matching p m) := by
  have hlast : (p.manRank m (matching p m)).val + 1 = (run p (n * n)).count m :=
    (valid_run p (n * n)).held_last
      ((run p (n * n)).held_toMatching (complete_run_sq p) m)
  rw [← hlast]
  exact Nat.lt_succ_iff

/-- A woman's final husband is weakly preferred to every man who proposed to her. -/
theorem womanRank_matching_le_of_proposed (p : Profile n) {m w : Fin n}
    (h : (p.manRank m w).val < (run p (n * n)).count m) :
    p.womanRank w ((matching p).symm w) ≤ p.womanRank w m := by
  obtain ⟨a, ha, hpref⟩ := (valid_run p (n * n)).preferred_holder h
  have hheld := (run p (n * n)).held_toMatching (complete_run_sq p) ((matching p).symm w)
  change (run p (n * n)).held (matching p ((matching p).symm w)) = _ at hheld
  rw [(matching p).apply_symm_apply] at hheld
  exact Option.some.inj (ha.symm.trans hheld) ▸ hpref

/-- A proposal changes no count except that of the proposer, which increases by one. -/
theorem count_le_advance (p : Profile n) (s : DAState n) (m : Fin n) :
    s.count m ≤ (advance p s).count m := by
  cases h : s.nextProposal p.manRank with
  | none => simp only [advance, h, le_rfl]
  | some a =>
    obtain ⟨i, w⟩ := a
    rw [advance, h]
    by_cases hm : m = i
    · subst m
      simp [applyDecision]
    · simp [applyDecision, hm]

/-- Once a pair has been proposed, it stays in the proposed prefix of the history. -/
theorem count_mono_run (p : Profile n) (m : Fin n) :
    Monotone fun k ↦ (run p k).count m :=
  monotone_nat_of_le_succ fun k ↦ count_le_advance p (run p k) m

/-- Replaying a history needs only men's ranks and comparisons between the
proposers in each woman's proposed prefix of that history. -/
theorem run_eq_of_agree_on_proposed {p q : Profile n} (k : ℕ)
    (hmen : p.manRank = q.manRank)
    (hwomen : ∀ w a b,
      (p.manRank a w).val < (run p k).count a →
      (p.manRank b w).val < (run p k).count b →
      (p.womanRank w a < p.womanRank w b ↔ q.womanRank w a < q.womanRank w b)) :
    run q k = run p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hprev := ih fun w a b ha hb ↦ hwomen w a b
      (ha.trans_le (count_le_advance p (run p k) a))
      (hb.trans_le (count_le_advance p (run p k) b))
    change advance q (run q k) = advance p (run p k)
    rw [hprev]
    unfold advance
    rw [← hmen]
    cases hn : (run p k).nextProposal p.manRank with
    | none => rfl
    | some pair =>
      obtain ⟨m, w⟩ := pair
      cases ha : (run p k).held w with
      | none => simp [proposalAccepted, ha]
      | some a =>
        have hnew : (p.manRank m w).val < (run p (k + 1)).count m := by
          change _ < (advance p (run p k)).count m
          rw [advance, hn, (nextProposal_some hn).2]
          simp [applyDecision]
        have hold : (p.manRank a w).val < (run p (k + 1)).count a := by
          have hlast := (valid_run p k).held_last ha
          have hpast : (p.manRank a w).val < (run p k).count a := by
            rw [← hlast]
            exact Nat.lt_succ_self _
          exact hpast.trans_le (count_le_advance p (run p k) a)
        simp only [proposalAccepted, ha, Option.elim_some]
        exact congrArg ((run p k).applyDecision m w)
          (decide_eq_decide.mpr (hwomen w m a hnew hold).symm)

/-- A score implementation first issues the ordinal proposal, then reads the
new score and compares with the already-held score if there is one. -/
noncomputable def advanceScores (x : ScoreProfile n) (s : DAState n) : DAState n :=
  match s.nextProposal (profileOfScores x).manRank with
  | none => s
  | some (m, w) =>
    s.applyDecision m w ((s.held w).elim true fun a ↦ decide (x (.inr w) m < x (.inr w) a))

/-- The score implementation is the ordinal proposal step on tie-free female rows. -/
theorem advanceScores_eq_advance (x : ScoreProfile n) (s : DAState n)
    (hx : ∀ w, Function.Injective (x (.inr w))) :
    advanceScores x s = advance (profileOfScores x) s := by
  unfold advanceScores advance
  cases hp : s.nextProposal (profileOfScores x).manRank with
  | none => rfl
  | some pair =>
    obtain ⟨m, w⟩ := pair
    cases hh : s.held w with
    | none => simp [proposalAccepted, hh]
    | some a =>
      simp only [proposalAccepted, hh, Option.elim_some]
      exact congrArg (s.applyDecision m w)
        (decide_eq_decide.mpr (rankPermutation_lt_iff (hx w) m a).symm)

/-- With men's ranks fixed, altering only unproposed female scores cannot
change a tie-free DA history. -/
theorem run_eq_of_agree_on_proposed_scores {x y : ScoreProfile n} (k : ℕ)
    (hx : ∀ w, Function.Injective (x (.inr w)))
    (hy : ∀ w, Function.Injective (y (.inr w)))
    (hmen : (profileOfScores x).manRank = (profileOfScores y).manRank)
    (hwomen : ∀ w a, ((profileOfScores x).manRank a w).val <
      (run (profileOfScores x) k).count a → x (.inr w) a = y (.inr w) a) :
    run (profileOfScores y) k = run (profileOfScores x) k := by
  apply run_eq_of_agree_on_proposed k hmen
  intro w a b ha hb
  change rankPermutation (x (.inr w)) a < rankPermutation (x (.inr w)) b ↔
    rankPermutation (y (.inr w)) a < rankPermutation (y (.inr w)) b
  rw [rankPermutation_lt_iff (hx w), rankPermutation_lt_iff (hy w),
    hwomen w a ha, hwomen w b hb]

/-- Female-score coordinates read in a history with the given proposal counts. -/
def proposedCells (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Set (Fin n × Fin n) := {c | (rank c.2 c.1).val < s.count c.2}

/-- Every final husband's score is among the observed proposal scores. -/
theorem matching_symm_mem_proposedCells (p : Profile n) (w : Fin n) :
    (w, (matching p).symm w) ∈ proposedCells p.manRank (run p (n * n)) := by
  apply (proposed_run_sq_iff p ((matching p).symm w) w).mpr
  rw [(matching p).apply_symm_apply]

/-- Complete the observed scores by distinct dummy scores outside the unit interval. -/
noncomputable def fillFromProposed (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n)
    (men : Fin n → Fin n → ℝ) (women : proposedCells rank s → ℝ) : ScoreProfile n
  | .inl m, w => men m w
  | .inr w, m =>
    if h : (rank m w).val < s.count m then women ⟨(w, m), h⟩ else 2 + (m.val : ℝ)

/-- Completion of the observed score coordinates is measurable. -/
theorem measurable_fillFromProposed (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) :
    Measurable (fun x : (Fin n → Fin n → ℝ) × (proposedCells rank s → ℝ) ↦
      fillFromProposed rank s x.1 x.2) := by
  apply Measurable.of_eval
  intro r
  apply Measurable.of_eval
  intro a
  cases r with
  | inl m =>
    exact (measurable_pi_apply a).comp ((measurable_pi_apply m).comp measurable_fst)
  | inr w =>
    by_cases h : (rank a w).val < s.count a
    · simp only [fillFromProposed, dite_eq_left h]
      exact (measurable_pi_apply (⟨(w, a), h⟩ : proposedCells rank s)).comp measurable_snd
    · simpa only [fillFromProposed, dite_eq_right h] using
        (measurable_const : Measurable fun _ :
          (Fin n → Fin n → ℝ) × (proposedCells rank s → ℝ) ↦ 2 + (a.val : ℝ))

/-- A fixed structural DA branch is measurable in the initial male scores
and the read female scores of that branch. -/
theorem measurableSet_rank_and_run_fillFromProposed
    (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) (k : ℕ) :
    MeasurableSet {x : (Fin n → Fin n → ℝ) × (proposedCells rank s → ℝ) |
      let p := profileOfScores (fillFromProposed rank s x.1 x.2)
      p.manRank = rank ∧ run p k = s} :=
  ((measurable_profileOfScores n).comp (measurable_fillFromProposed rank s))
    (MeasurableSpace.measurableSet_top :
      MeasurableSet {p : Profile n | p.manRank = rank ∧ run p k = s})

/-- On the tie-free unit score arrays, a fixed DA state is recognized from
only its proposed coordinates and the initial male score array. -/
theorem run_eq_iff_run_fillFromProposed {x : ScoreProfile n}
    (rank : Fin n → Equiv.Perm (Fin n)) (s : DAState n) (k : ℕ)
    (hmen : (profileOfScores x).manRank = rank)
    (hx : ∀ w, Function.Injective (x (.inr w))) (hu : ∀ w m, x (.inr w) m < 1) :
    run (profileOfScores x) k = s ↔
      run (profileOfScores (fillFromProposed rank s (fun m ↦ x (.inl m))
        (fun c ↦ x (.inr c.val.1) c.val.2))) k = s := by
  let y := fillFromProposed rank s (fun m ↦ x (.inl m)) (fun c ↦ x (.inr c.val.1) c.val.2)
  have hmen' : (profileOfScores y).manRank = (profileOfScores x).manRank := rfl
  have hread {w m} (h : (rank m w).val < s.count m) : y (.inr w) m = x (.inr w) m := by
    simp only [y, fillFromProposed, dite_eq_left h]
  have hunread {w m} (h : ¬ (rank m w).val < s.count m) :
      y (.inr w) m = 2 + (m.val : ℝ) := by
    simp only [y, fillFromProposed, dite_eq_right h]
  have hy (w : Fin n) : Function.Injective (y (.inr w)) := by
    intro a b heq
    by_cases ha : (rank a w).val < s.count a
    · by_cases hb : (rank b w).val < s.count b
      · exact hx w ((hread ha).symm.trans (heq.trans (hread hb)))
      · rw [hread ha, hunread hb] at heq
        linarith only [heq, hu w a, Nat.cast_nonneg (α := ℝ) b.val]
    · by_cases hb : (rank b w).val < s.count b
      · rw [hunread ha, hread hb] at heq
        linarith only [heq, hu w b, Nat.cast_nonneg (α := ℝ) a.val]
      · rw [hunread ha, hunread hb] at heq
        have hval : (a.val : ℝ) = b.val := add_left_cancel heq
        exact Fin.ext (by exact_mod_cast hval)
  change run (profileOfScores x) k = s ↔ run (profileOfScores y) k = s
  constructor
  · intro h
    refine (run_eq_of_agree_on_proposed_scores k hx hy hmen'.symm fun w m hm ↦ ?_).trans h
    rw [hmen, h] at hm
    exact (hread hm).symm
  · intro h
    refine (run_eq_of_agree_on_proposed_scores k hy hx hmen' fun w m hm ↦ ?_).trans h
    rw [hmen', hmen, h] at hm
    exact hread hm

end DAState
end LennonPittelFormalization

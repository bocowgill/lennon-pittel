module

public import LennonPittel.RotationClockBand
public import LennonPittel.ScoreRotationHistory

/-!
# Crossing the pivot score band on the comparison-selected walk

If the walk starts above the band and finishes below it, the two first
crossings delimit a legal segment whose clock drift forces participation.
The endpoint assumptions are deterministic; this file gives no probability
estimate for those assumptions.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The matching at a padded checkpoint of the walk started at deferred acceptance. -/
noncomputable def scoreWalkMatching (x : ScoreProfile n) (k : ℕ) : Matching n :=
  (scoreRotationWalk x k (DAState.matching (profileOfScores x))).2

/-- The sum of the women's spouse scores at that checkpoint. -/
noncomputable def scoreWalkFemaleTotal (x : ScoreProfile n) (k : ℕ) : ℝ :=
  femaleSpouseTotal x (scoreWalkMatching x k)

/-- The rotations of the actual walk between two checkpoints. -/
noncomputable def scoreWalkSegmentRotations (x : ScoreProfile n) (a b : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  (scoreRotationWalk x (b - a) (scoreWalkMatching x a)).1

/-- Every checkpoint of the score walk is stable. -/
theorem scoreWalkMatching_stable {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) (k : ℕ) :
    IsStable (profileOfScores x) (scoreWalkMatching x k) := by
  have hstart := (DAState.isManOptimal_matching (profileOfScores x)).1
  exact (scoreRotationWalk_legal x hx k hstart).isStable_end

/-- Every forward segment of the score walk is a legal rotation sequence. -/
theorem scoreWalkSegmentRotations_legal {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) {a b : ℕ} (hab : a ≤ b) :
    RotationSequence (profileOfScores x) (scoreWalkMatching x a)
      (scoreWalkSegmentRotations x a b) (scoreWalkMatching x b) := by
  have h := congrArg Prod.snd
    (scoreRotationWalk_add x a (b - a) (DAState.matching (profileOfScores x)))
  rw [Nat.add_sub_of_le hab] at h
  change scoreWalkMatching x b = (scoreRotationWalk x (b - a) (scoreWalkMatching x a)).2 at h
  rw [h]
  exact scoreRotationWalk_legal x hx _ (scoreWalkMatching_stable hx a)

/-- The next checkpoint either eliminates the selected rotation or stays put. -/
theorem scoreWalkMatching_succ (x : ScoreProfile n) (k : ℕ) :
    scoreWalkMatching x (k + 1) =
      match chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) with
      | none => scoreWalkMatching x k
      | some ρ => eliminateRotation (scoreWalkMatching x k) ρ := by
  have h := congrArg Prod.snd
    (scoreRotationWalk_add x k 1 (DAState.matching (profileOfScores x)))
  change scoreWalkMatching x (k + 1) = (scoreRotationWalk x 1 (scoreWalkMatching x k)).2 at h
  rw [h, scoreRotationWalk]
  cases chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) <;> rfl

/-- The female score total is antitone along the padded walk. -/
theorem antitone_scoreWalkFemaleTotal {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) :
    Antitone (scoreWalkFemaleTotal x) := by
  apply antitone_nat_of_succ_le
  intro k
  unfold scoreWalkFemaleTotal
  rw [scoreWalkMatching_succ]
  cases h : chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) with
  | none => rfl
  | some ρ =>
    have hρ :=
      (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx (scoreWalkMatching x k) ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation h)
    exact femaleSpouseTotal_eliminate_le x hρ hx

/-- On the score and length events, the relative cap also applies to padded steps. -/
theorem scoreWalkFemaleTotal_step_drop {x : ScoreProfile n} (hn : 0 < n)
    (hx : x ∈ goodCoexposureScores n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (k : ℕ) :
    scoreWalkFemaleTotal x k - scoreWalkFemaleTotal x (k + 1) ≤
      rotationStepRelativeCap n * scoreWalkFemaleTotal x k := by
  have ht : ∀ j, Function.Injective (x (.inr j)) := fun j ↦ hx.1 (.inr j)
  have hs := scoreWalkMatching_stable ht k
  unfold scoreWalkFemaleTotal
  rw [scoreWalkMatching_succ]
  cases h : chooseQueriedRotation (scoreRotationGraph x (scoreWalkMatching x k)) with
  | none =>
    change femaleSpouseTotal x (scoreWalkMatching x k) -
        femaleSpouseTotal x (scoreWalkMatching x k) ≤ _
    rw [sub_self]
    apply mul_nonneg _ (zero_le_two.trans (hx.2.2 _ hs).1)
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    unfold rotationStepRelativeCap rotationLengthCutoff
    positivity
  | some ρ =>
    have hρ :=
      (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x ht (scoreWalkMatching x k) ρ).mp
        (realizesDirectedCycle_of_chooseQueriedRotation h)
    exact femaleSpouseTotal_drop_le_rotationStepRelativeCap hx hlen hs hρ

/-- Clock drift between two checkpoints subtracts exactly the participation of their segment. -/
theorem scoreWalkClock_sub (x : ScoreProfile n) {a b : ℕ} (hab : a ≤ b) :
    scoreWalkClock x b - scoreWalkClock x a =
      femaleLogPotential x (scoreWalkMatching x b) - femaleLogPotential x (scoreWalkMatching x a) -
        (rotationParticipation (scoreWalkSegmentRotations x a b) : ℝ) := by
  let μ := DAState.matching (profileOfScores x)
  have h := scoreRotationWalk_add x a (b - a) μ
  rw [Nat.add_sub_of_le hab] at h
  have hp : (rotationParticipation (scoreRotationWalk x b μ).1 : ℝ) =
      (rotationParticipation (scoreRotationWalk x a μ).1 : ℝ) +
        (rotationParticipation (scoreWalkSegmentRotations x a b) : ℝ) := by
    rw [h]
    simp [rotationParticipation, scoreWalkSegmentRotations, scoreWalkMatching, μ]
  change (femaleLogPotential x (scoreWalkMatching x b) - femaleLogPotential x μ -
      (rotationParticipation (scoreRotationWalk x b μ).1 : ℝ)) -
      (femaleLogPotential x (scoreWalkMatching x a) - femaleLogPotential x μ -
        (rotationParticipation (scoreRotationWalk x a μ).1 : ℝ)) = _
  rw [hp]
  ring

private theorem first_score_crossing {Y : ℕ → ℝ} {N : ℕ} {u c : ℝ}
    (hstart : u < Y 0) (hfinish : Y N ≤ u) (hcap : c ≤ 1)
    (hstep : ∀ t, Y t - Y (t + 1) ≤ c * Y t) :
    ∃ t ≤ N, (∀ j < t, u < Y j) ∧ (1 - c) * u ≤ Y t ∧ Y t ≤ u := by
  have hex : ∃ t, Y t ≤ u := ⟨N, hfinish⟩
  let t := Nat.find hex
  have hsmall : ∀ j < t, u < Y j := fun j hj ↦ lt_of_not_ge (Nat.find_min hex hj)
  have ht : t ≤ N := Nat.find_min' hex hfinish
  have htop : Y t ≤ u := Nat.find_spec hex
  have ht' : t ≠ 0 := fun he ↦ (not_le_of_gt hstart) (he ▸ htop)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht'
  have hk' : k < t := by omega
  refine ⟨t, ht, hsmall, ?_, htop⟩
  rw [hk]
  exact lower_of_relative_drop_at_crossing (hsmall k hk').le hcap (hstep k)

/-- If the actual walk starts above and ends below the pivot band, it contains
a legal band segment with participation forced by the uniform clock bound. -/
theorem exists_scoreWalk_pivot_band_segment {x : ScoreProfile n} {N : ℕ} {E : ℝ}
    (hn : 0 < n) (hx : x ∈ goodCoexposureScores n) (hgeom : x ∈ goodFemaleLogGeometry n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (hcap : rotationStepRelativeCap n ≤ 1 / 2)
    (hsep : (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2)
    (hstart : (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0)
    (hfinish : scoreWalkFemaleTotal x N ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hclock : ∀ t ≤ N, |scoreWalkClock x t| ≤ E) :
    ∃ a b, a < b ∧ b ≤ N ∧
      (∀ t, a ≤ t → t < b → scoreWalkFemaleTotal x t ∈
        Set.Ioc ((n : ℝ) ^ (1 / 5 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))) ∧
      (1 - rotationStepRelativeCap n) * (n : ℝ) ^ (2 / 5 : ℝ) ≤ scoreWalkFemaleTotal x a ∧
      (1 - rotationStepRelativeCap n) * (n : ℝ) ^ (1 / 5 : ℝ) ≤ scoreWalkFemaleTotal x b ∧
      scoreWalkFemaleTotal x b ≤ (n : ℝ) ^ (1 / 5 : ℝ) ∧
      RotationSequence (profileOfScores x) (scoreWalkMatching x a)
        (scoreWalkSegmentRotations x a b) (scoreWalkMatching x b) ∧
      (n : ℝ) * (Real.log n / 5 - Real.log 2 - 6) - 2 * E ≤
        (rotationParticipation (scoreWalkSegmentRotations x a b) : ℝ) := by
  let Y := scoreWalkFemaleTotal x
  let U := (n : ℝ) ^ (2 / 5 : ℝ)
  let L := (n : ℝ) ^ (1 / 5 : ℝ)
  let c := rotationStepRelativeCap n
  have ht : ∀ j, Function.Injective (x (.inr j)) := fun j ↦ hx.1 (.inr j)
  have hY : Antitone Y := antitone_scoreWalkFemaleTotal ht
  have hc : c ≤ 1 := hcap.trans (by norm_num)
  have hU : 0 ≤ U := by unfold U; positivity
  have hLU : L < U := hsep.trans_le (by change U / 2 ≤ U; linarith)
  have hstep := scoreWalkFemaleTotal_step_drop hn hx hlen
  obtain ⟨a, haN, _, ha, hau⟩ := first_score_crossing hstart
    (hfinish.trans hLU.le) hc hstep
  obtain ⟨b, hbN, hbefore, hb, hbl⟩ := first_score_crossing (hLU.trans hstart) hfinish hc hstep
  have ha' : U / 2 ≤ Y a := calc
    U / 2 = (1 / 2) * U := by ring
    _ ≤ (1 - c) * U := mul_le_mul_of_nonneg_right (by
      change (1 / 2 : ℝ) ≤ 1 - rotationStepRelativeCap n
      linarith only [hcap]) hU
    _ ≤ Y a := ha
  have hab : a < b := by
    by_contra! hba
    exact (not_le_of_gt (hsep.trans_le ha')) ((hY hba).trans hbl)
  have hsa := scoreWalkMatching_stable ht a
  have hsb := scoreWalkMatching_stable ht b
  have hseg := scoreWalkSegmentRotations_legal ht hab.le
  refine ⟨a, b, hab, hbN, fun t hat htb ↦ ⟨hbefore t htb, (hY hat).trans hau⟩,
    ha, hb, hbl, hseg, ?_⟩
  have herr : |scoreWalkClock x b - scoreWalkClock x a| ≤ 2 * E := calc
    _ ≤ |scoreWalkClock x b| + |scoreWalkClock x a| := abs_sub _ _
    _ ≤ 2 * E := by linarith only [hclock a haN, hclock b hbN]
  rw [scoreWalkClock_sub x hab.le] at herr
  exact rotationParticipation_ge_of_pivot_band hn x _ _ _ (hgeom _ hsa) (hgeom _ hsb)
    ha' hbl (lt_of_lt_of_le (by norm_num) (hx.2.2 _ hsb).1) herr

/-- The same realized label cannot occur twice on a legal rotation sequence. -/
theorem RotationSequence.rotationLabels_nodup {p : Profile n} {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    (rotationLabels μ rs).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons μ ν ρ rs _ hρ htail ih =>
    rw [rotationLabels, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    obtain ⟨m, hm, _⟩ := hρ.isCycle
    obtain ⟨old, _, hold, _, hstart, _, _⟩ := htail.label_rank_bounds hmem
      (show (rotationLabel μ ρ).cycle m ≠ m from hm)
    have hold' : μ m = old := by simpa [rotationLabel, hm] using hold
    rw [← hold'] at hstart
    exact (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm)) hstart

private theorem rotationLabels_map_lengthWeight {W : Type*} (g : ℕ → W)
    (μ : Matching n) (rs : List (Equiv.Perm (Fin n))) :
    (rotationLabels μ rs).map (fun r ↦ g r.cycle.support.card) =
      rs.map (fun σ ↦ g σ.support.card) := by
  induction rs generalizing μ with
  | nil => rfl
  | cons σ rs ih =>
    simp only [rotationLabels, List.map_cons, rotationLabel, ih]

/-- The nonnegative length weight along a segment from a man-optimal walk is
bounded by the corresponding weight over all realized rotations. -/
theorem RotationSequence.lengthWeight_le_profileSingletonAnchorLengthWeight
    {p : Profile n} {μ₀ μ ν : Matching n} {rs ss : List (Equiv.Perm (Fin n))}
    (hopt : IsManOptimal p μ₀) (hprefix : RotationSequence p μ₀ ss μ)
    (hseg : RotationSequence p μ rs ν) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (rs.map (fun σ ↦ g σ.support.card)).sum ≤ profileSingletonAnchorLengthWeight p g := by
  classical
  let : Fintype (RotationLabel n) := Fintype.ofFinite _
  let : Fintype (Rotation p μ₀) := Fintype.ofFinite _
  let f (r : RotationLabel n) : ℝ := g r.cycle.support.card
  let P (r : RotationLabel n) : Prop :=
    ∃ ν' rs', RotationSequence p μ₀ rs' ν' ∧ r ∈ rotationLabels μ₀ rs'
  let V := Finset.univ.filter P
  have hsub : (rotationLabels μ rs).toFinset ⊆ V := by
    intro r hr
    have hr' := List.mem_toFinset.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ν, ss ++ rs, hprefix.append hseg,
      by rw [hprefix.rotationLabels_append]; exact List.mem_append_right _ hr'⟩
  calc
    _ = ((rotationLabels μ rs).map f).sum := by rw [rotationLabels_map_lengthWeight]
    _ = ∑ r ∈ (rotationLabels μ rs).toFinset, f r :=
      (List.sum_toFinset f hseg.rotationLabels_nodup).symm
    _ ≤ ∑ r ∈ V, f r := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ ↦ hg _)
    _ = ∑ r : Rotation p μ₀, g r.val.cycle.support.card :=
      Finset.sum_subtype (p := P) V (by intro r; simp [V]) f
    _ = _ := sum_rotation_lengthWeight_eq_profileSingletonAnchorLengthWeight hopt g

/-- Length contributed by a rotation shorter than the lower cutoff. -/
noncomputable def shortRotationLengthWeight (K : ℝ) (k : ℕ) : ℝ :=
  if (k : ℝ) < K then k else 0

/-- Length contributed by a rotation longer than the upper cutoff. -/
noncomputable def longRotationLengthWeight (A : ℝ) (k : ℕ) : ℝ :=
  if A < (k : ℝ) then k else 0

open scoped Classical in
/-- The number of occurrences of rotations whose support size is between the two cutoffs. -/
noncomputable def middleRotationCount (K A : ℝ) (rs : List (Equiv.Perm (Fin n))) : ℕ :=
  rs.countP (fun ρ ↦ decide (K ≤ (ρ.support.card : ℝ) ∧ (ρ.support.card : ℝ) ≤ A))

/-- Small and large length weights leave at most the upper cutoff times the number
of intermediate rotations to account for all remaining participation. -/
theorem rotationParticipation_le_lengthWeights_add_middleCount (K A : ℝ)
    (rs : List (Equiv.Perm (Fin n))) :
    (rotationParticipation rs : ℝ) ≤
      (rs.map (fun ρ ↦ shortRotationLengthWeight K ρ.support.card)).sum +
        (rs.map (fun ρ ↦ longRotationLengthWeight A ρ.support.card)).sum +
        A * (middleRotationCount K A rs : ℝ) := by
  classical
  induction rs with
  | nil => simp [rotationParticipation, middleRotationCount]
  | cons ρ rs ih =>
    let l : ℝ := ρ.support.card
    have h₁ : 0 ≤ shortRotationLengthWeight K ρ.support.card := by
      unfold shortRotationLengthWeight
      split <;> positivity
    have h₂ : 0 ≤ longRotationLengthWeight A ρ.support.card := by
      unfold longRotationLengthWeight
      split <;> positivity
    have hhead : l ≤ shortRotationLengthWeight K ρ.support.card +
        longRotationLengthWeight A ρ.support.card + (if K ≤ l ∧ l ≤ A then A else 0) := by
      by_cases hK : l < K
      · rw [ite_eq_right (fun h ↦ hK.not_ge h.1)]
        have hs : shortRotationLengthWeight K ρ.support.card = l := ite_eq_left hK
        linarith only [h₂, hs]
      · by_cases hA : A < l
        · rw [ite_eq_right (fun h ↦ hA.not_ge h.2)]
          have hl : longRotationLengthWeight A ρ.support.card = l := ite_eq_left hA
          linarith only [h₁, hl]
        · rw [ite_eq_left ⟨le_of_not_gt hK, le_of_not_gt hA⟩]
          linarith only [h₁, h₂, le_of_not_gt hA]
    have hpart : (rotationParticipation (ρ :: rs) : ℝ) =
        l + (rotationParticipation rs : ℝ) := by
      simp [l, rotationParticipation]
    rw [hpart]
    simp [middleRotationCount] at ih
    by_cases hm : K ≤ l ∧ l ≤ A
    · simp [middleRotationCount, l, hm, Nat.cast_add, mul_add] at hhead ⊢
      linarith only [ih, hhead]
    · simp [middleRotationCount, l, hm] at hhead ⊢
      linarith only [ih, hhead]

/-- The actual band segment contains enough intermediate rotations after charging the
short and long participation to the whole profile. -/
theorem exists_scoreWalk_pivot_band_middle_count {x : ScoreProfile n} {N : ℕ} {E : ℝ}
    (hn : 0 < n) (hx : x ∈ goodCoexposureScores n) (hgeom : x ∈ goodFemaleLogGeometry n)
    (hlen : profileOfScores x ∉ longStableExposedRotationEvent n (rotationLengthCutoff n))
    (hcap : rotationStepRelativeCap n ≤ 1 / 2)
    (hsep : (n : ℝ) ^ (1 / 5 : ℝ) < (n : ℝ) ^ (2 / 5 : ℝ) / 2)
    (hstart : (n : ℝ) ^ (2 / 5 : ℝ) < scoreWalkFemaleTotal x 0)
    (hfinish : scoreWalkFemaleTotal x N ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hclock : ∀ t ≤ N, |scoreWalkClock x t| ≤ E) (K A : ℝ) :
    ∃ a b, a < b ∧ b ≤ N ∧
      (∀ t, a ≤ t → t < b → scoreWalkFemaleTotal x t ∈
        Set.Ioc ((n : ℝ) ^ (1 / 5 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))) ∧
      RotationSequence (profileOfScores x) (scoreWalkMatching x a)
        (scoreWalkSegmentRotations x a b) (scoreWalkMatching x b) ∧
      (n : ℝ) * (Real.log n / 5 - Real.log 2 - 6) - 2 * E -
        profileSingletonAnchorLengthWeight (profileOfScores x) (shortRotationLengthWeight K) -
        profileSingletonAnchorLengthWeight (profileOfScores x) (longRotationLengthWeight A) ≤
        A * (middleRotationCount K A (scoreWalkSegmentRotations x a b) : ℝ) := by
  obtain ⟨a, b, hab, hbN, hband, _, _, _, hseg, hpart⟩ :=
    exists_scoreWalk_pivot_band_segment hn hx hgeom hlen hcap hsep hstart hfinish hclock
  let p := profileOfScores x
  have hopt := DAState.isManOptimal_matching p
  have hprefix := scoreRotationWalk_legal x (fun j ↦ hx.1 (.inr j)) a hopt.1
  have hs := RotationSequence.lengthWeight_le_profileSingletonAnchorLengthWeight hopt hprefix hseg
    (shortRotationLengthWeight K) (fun k ↦ by
      unfold shortRotationLengthWeight
      split <;> positivity)
  have hl := RotationSequence.lengthWeight_le_profileSingletonAnchorLengthWeight hopt hprefix hseg
    (longRotationLengthWeight A) (fun k ↦ by
      unfold longRotationLengthWeight
      split <;> positivity)
  have hmid := rotationParticipation_le_lengthWeights_add_middleCount K A
    (scoreWalkSegmentRotations x a b)
  exact ⟨a, b, hab, hbN, hband, hseg, by linarith only [hpart, hmid, hs, hl]⟩

private theorem rotationLabels_scoreRotationWalk_checkpoint (x : ScoreProfile n) (k : ℕ)
    {μ : Matching n} {r : RotationLabel n}
    (hr : r ∈ rotationLabels μ (scoreRotationWalk x k μ).1) :
    ∃ t < k, let ν := (scoreRotationWalk x t μ).2
      chooseQueriedRotation (scoreRotationGraph x ν) = some r.cycle ∧
        rotationLabel ν r.cycle = r := by
  induction k generalizing μ with
  | zero => simp [scoreRotationWalk, rotationLabels] at hr
  | succ k ih =>
    cases hρ : chooseQueriedRotation (scoreRotationGraph x μ) with
    | none => simp [scoreRotationWalk, hρ, rotationLabels] at hr
    | some ρ =>
      simp only [scoreRotationWalk, hρ, rotationLabels, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨0, Nat.zero_lt_succ k, hρ, rfl⟩
      · obtain ⟨t, ht, hw⟩ := ih hr
        exact ⟨t + 1, Nat.succ_lt_succ ht, by simpa only [scoreRotationWalk, hρ] using hw⟩

/-- The intermediate-length occurrences of a segment are distinct realized rotations.
Each of them is exposed at an actual checkpoint within the segment. -/
theorem exists_scoreWalkSegment_middle_realizedRotations {x : ScoreProfile n}
    (hx : ∀ j, Function.Injective (x (.inr j))) {a b : ℕ} (hab : a ≤ b) (K A : ℝ) :
    ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
      S.card = middleRotationCount K A (scoreWalkSegmentRotations x a b) ∧
      ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
        (r.val.cycle.support.card : ℝ) ≤ A ∧
          ∃ t, a ≤ t ∧ t < b ∧ r.IsExposedAt (scoreWalkMatching x t) := by
  classical
  let p := profileOfScores x
  let μ₀ := DAState.matching p
  let rs := scoreWalkSegmentRotations x a b
  let ss := (scoreRotationWalk x a μ₀).1
  let labels := rotationLabels (scoreWalkMatching x a) rs
  let middle (r : RotationLabel n) : Bool := decide
    (K ≤ (r.cycle.support.card : ℝ) ∧ (r.cycle.support.card : ℝ) ≤ A)
  let T := (labels.filter middle).toFinset
  let P (r : RotationLabel n) : Prop :=
    ∃ ν rs', RotationSequence p μ₀ rs' ν ∧ r ∈ rotationLabels μ₀ rs'
  have hprefix := scoreRotationWalk_legal x hx a (DAState.isManOptimal_matching p).1
  have hseg := scoreWalkSegmentRotations_legal hx hab
  have hsub : ∀ r ∈ T, P r := by
    intro r hr
    have hr' := (List.mem_filter.mp (List.mem_toFinset.mp hr)).1
    refine ⟨scoreWalkMatching x b, ss ++ rs, hprefix.append hseg, ?_⟩
    rw [hprefix.rotationLabels_append]
    exact List.mem_append_right _ hr'
  let S : Finset (Rotation p μ₀) := T.subtype P
  have hmap := rotationLabels_map_lengthWeight (fun k : ℕ ↦ k) (scoreWalkMatching x a) rs
  have hcnt : labels.countP middle = middleRotationCount K A rs := by
    let goodLength (k : ℕ) : Bool := decide (K ≤ (k : ℝ) ∧ (k : ℝ) ≤ A)
    have h := congrArg (List.countP goodLength) hmap
    simpa only [List.countP_map, Function.comp_def, labels, middle, middleRotationCount,
      goodLength] using h
  have hc : S.card = middleRotationCount K A rs := by
    change (T.subtype P).card = _
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr hsub]
    change (labels.filter middle).toFinset.card = _
    rw [List.toFinset_card_of_nodup (hseg.rotationLabels_nodup.filter _)]
    rw [← List.countP_eq_length_filter]
    exact hcnt
  refine ⟨S, hc, ?_⟩
  intro r hr
  have hr' : r.val ∈ T := Finset.mem_subtype.mp hr
  have hr'' := List.mem_filter.mp (List.mem_toFinset.mp hr')
  have hlength : K ≤ (r.val.cycle.support.card : ℝ) ∧
      (r.val.cycle.support.card : ℝ) ≤ A := decide_eq_true_eq.mp hr''.2
  obtain ⟨t, ht, hchoose, hlabel⟩ := rotationLabels_scoreRotationWalk_checkpoint
    x (b - a) (μ := scoreWalkMatching x a) hr''.1
  have heq := congrArg Prod.snd (scoreRotationWalk_add x a t μ₀)
  change scoreWalkMatching x (a + t) = (scoreRotationWalk x t (scoreWalkMatching x a)).2 at heq
  rw [← heq] at hchoose hlabel
  have hρ := (realizesDirectedCycle_queriedSuccessorGraph_scores_iff x hx
    (scoreWalkMatching x (a + t)) r.val.cycle).mp
      (realizesDirectedCycle_of_chooseQueriedRotation hchoose)
  exact ⟨hlength.1, hlength.2, a + t, by omega, by omega, hρ, hlabel⟩

end LennonPittelFormalization

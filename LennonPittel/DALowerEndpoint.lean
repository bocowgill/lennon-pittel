module

public import LennonPittel.ScoreRotationBranchLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Fresh female scores at deferred-acceptance proposals

The next ordinal proposal does not depend on the female score it is about
to read. This bounds the number of small female scores seen before a
deterministic proposal cap, and hence bounds the lower endpoint of the walk.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped Classical ENNReal Topology

namespace LennonPittelFormalization

variable {n : ℕ}

/-- At ordinal proposal time `k`, the deferred-acceptance command selects `c`. -/
def daProposalEvent (k : ℕ) (c : Fin n × Fin n) : Set (ScoreProfile n) :=
  {x | (DAState.run (profileOfScores x) k).nextProposal (profileOfScores x).manRank = some c}

theorem measurableSet_daProposalEvent (k : ℕ) (c : Fin n × Fin n) :
    MeasurableSet (daProposalEvent k c) := by
  change MeasurableSet (profileOfScores ⁻¹'
    {p : Profile n | (DAState.run p k).nextProposal p.manRank = some c})
  exact (measurable_profileOfScores n) MeasurableSet.of_discrete

/-- The female score coordinate at the proposed pair. -/
abbrev daFemaleCell (c : Fin n × Fin n) : ClockCell n :=
  (.inr c.2, c.1)

/-- Replacing the female score at the proposed pair does not change the command
that makes the proposal, provided both arrays have tie-free female rows. -/
theorem mem_daProposalEvent_of_agree_off_cell (k : ℕ) (c : Fin n × Fin n)
    {x y : ScoreProfile n} (hx : x ∈ daProposalEvent k c)
    (hxt : ∀ w, Function.Injective (x (.inr w)))
    (hyt : ∀ w, Function.Injective (y (.inr w)))
    (hoff : ∀ d : ClockCell n, d ≠ daFemaleCell c → x d.1 d.2 = y d.1 d.2) :
    y ∈ daProposalEvent k c := by
  have hmen : (profileOfScores x).manRank = (profileOfScores y).manRank := by
    funext m
    change rankPermutation (x (.inl m)) = rankPermutation (y (.inl m))
    congr 1
    funext w
    exact hoff (.inl m, w) (by simp)
  have hp := DAState.nextProposal_some hx
  have hrun := DAState.run_eq_of_agree_on_proposed_scores k hxt hyt hmen ?_
  · change (DAState.run (profileOfScores y) k).nextProposal (profileOfScores y).manRank =
      some c
    rw [hrun, ← hmen]
    exact hx
  · intro w m hread
    apply hoff (.inr w, m)
    intro h
    have hw : w = c.2 := Sum.inr.inj (congrArg Prod.fst h)
    have hm : m = c.1 := congrArg Prod.snd h
    subst w
    subst m
    exact (Nat.ne_of_lt hread) hp.2

private abbrev DAOtherCells (c : Fin n × Fin n) := {d : ClockCell n // d ≠ daFemaleCell c}
private abbrev DAChosenCell (c : Fin n × Fin n) := {d : ClockCell n // d = daFemaleCell c}

attribute [-instance] Fintype.subtypeEq in
private noncomputable def splitDAFemaleCell (c : Fin n × Fin n) :
    ScoreProfile n ≃ᵐ (DAOtherCells c → ℝ) × (DAChosenCell c → ℝ) :=
  (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ClockCell n ↦ ℝ)
      (fun d ↦ d = daFemaleCell c)).trans MeasurableEquiv.prodComm)

private theorem measurePreserving_daUncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm
      (continuousScoreLaw n) (Measure.pi fun _ : ClockCell n ↦ unitScoreLaw) := by
  refine ⟨(MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  rw [show (MeasurableEquiv.curry (Fin n ⊕ Fin n) (Fin n) ℝ).symm ⁻¹' (univ.pi s) =
      univ.pi (fun i ↦ univ.pi fun j ↦ s (i, j)) by
    ext x
    simp [Set.mem_pi, Prod.forall]]
  simp_rw [continuousScoreLaw, Measure.pi_pi]
  rw [← Finset.prod_product']
  simp

attribute [-instance] Fintype.subtypeEq in
private theorem measurePreserving_splitDAFemaleCell (c : Fin n × Fin n) :
    MeasurePreserving (splitDAFemaleCell c) (continuousScoreLaw n)
      ((Measure.pi fun _ : DAOtherCells c ↦ unitScoreLaw).prod
        (Measure.pi fun _ : DAChosenCell c ↦ unitScoreLaw)) :=
  (Measure.measurePreserving_swap.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ClockCell n ↦ unitScoreLaw)
      (fun d ↦ d = daFemaleCell c))).comp (measurePreserving_daUncurry n)

attribute [-instance] Fintype.subtypeEq in
/-- At a specified ordinal proposal time, selecting a pair is independent of the
female score at that pair. This includes histories that have already stopped:
their commands select no pair. -/
theorem measure_daProposalEvent_inter_score (k : ℕ) (c : Fin n × Fin n)
    {S : Set ℝ} (hS : MeasurableSet S) :
    continuousScoreLaw n (daProposalEvent k c ∩ {x | x (.inr c.2) c.1 ∈ S}) =
      continuousScoreLaw n (daProposalEvent k c) * unitScoreLaw S := by
  let e := splitDAFemaleCell c
  let Q := Measure.pi (fun _ : DAOtherCells c ↦ unitScoreLaw)
  let R := Measure.pi (fun _ : DAChosenCell c ↦ unitScoreLaw)
  let E := e.symm ⁻¹' (daProposalEvent k c ∩ goodClockInput n)
  let G := e.symm ⁻¹' goodClockInput n
  let Z : Set (DAChosenCell c → ℝ) := Function.eval ⟨daFemaleCell c, rfl⟩ ⁻¹' S
  have he : MeasurePreserving e (continuousScoreLaw n) (Q.prod R) :=
    measurePreserving_splitDAFemaleCell c
  have hE := e.symm.measurable ((measurableSet_daProposalEvent k c).inter
    (measurableSet_goodClockInput n))
  have hG := e.symm.measurable (measurableSet_goodClockInput n)
  have hgood := he.symm.quasiMeasurePreserving.ae (ae_goodClockInput n)
  have hZ : MeasurableSet Z := (measurable_pi_apply _) hS
  have hZR : R Z = unitScoreLaw S :=
    (measurePreserving_eval (μ := fun _ : DAChosenCell c ↦ unitScoreLaw) _).measure_preimage
      hS.nullMeasurableSet
  have hreplay : ∀ a u, (a, u) ∈ E → ∀ v, (a, v) ∈ G →
      ((a, v) ∈ E ↔ ∀ i : DAChosenCell c, v i ∈ Ioo (0 : ℝ) 1) := by
    intro a u hu v hv
    let x := e.symm (a, u)
    let y := e.symm (a, v)
    have hx : x ∈ daProposalEvent k c ∩ goodClockInput n := hu
    have hy : y ∈ goodClockInput n := hv
    have ex : e x = (a, u) := e.apply_symm_apply _
    have ey : e y = (a, v) := e.apply_symm_apply _
    have hfixed (d : ClockCell n) (hd : d ≠ daFemaleCell c) : x d.1 d.2 = y d.1 d.2 := by
      change (e x).1 ⟨d, hd⟩ = (e y).1 ⟨d, hd⟩
      rw [ex, ey]
    have hsel := mem_daProposalEvent_of_agree_off_cell k c hx.1 hx.2.1 hy.1 hfixed
    have hvunit (i : DAChosenCell c) : v i ∈ Ioo (0 : ℝ) 1 := by
      have h := hy.2 i.val.1 i.val.2
      change (e y).2 i ∈ Ioo (0 : ℝ) 1 at h
      simpa only [ey] using h
    exact ⟨fun _ ↦ hvunit, fun _ ↦ ⟨hsel, hy⟩⟩
  have hrep := ae_eq_scoreCacheFiberEvent_of_replay Q hE hG hgood (fun _ _ ↦ 1)
    (fun _ ↦ measurable_const) hreplay
  have hrect : E =ᵐ[Q.prod R] scoreBranchBase E ×ˢ (univ : Set (DAChosenCell c → ℝ)) := by
    apply hrep.trans
    apply Filter.Eventually.set_eq
    filter_upwards [hgood] with z hz
    change z.1 ∈ scoreBranchBase E ∧ (∀ i : DAChosenCell c, z.2 i ∈ Ioo (0 : ℝ) 1) ↔
      z.1 ∈ scoreBranchBase E ∧ z.2 ∈ univ
    have hunit (i : DAChosenCell c) : z.2 i ∈ Ioo (0 : ℝ) 1 := by
      have h : (e (e.symm z)).2 i ∈ Ioo (0 : ℝ) 1 := hz.2 i.val.1 i.val.2
      simpa only [e.apply_symm_apply] using h
    simp [hunit]
  have hE0 : (Q.prod R) E = Q (scoreBranchBase E) := by
    rw [measure_congr hrect, Measure.prod_prod, measure_univ, mul_one]
  have hEZ : (Q.prod R) (E ∩ Prod.snd ⁻¹' Z) = Q (scoreBranchBase E) * unitScoreLaw S := by
    have hrectZ : (E ∩ Prod.snd ⁻¹' Z : Set _) =ᵐ[Q.prod R] (scoreBranchBase E ×ˢ Z) := by
      apply Filter.Eventually.set_eq
      filter_upwards [hrect.mem_iff] with z hz
      change (z ∈ E ∧ z.2 ∈ Z) ↔ _
      rw [hz]
      simp
    rw [measure_congr hrectZ, Measure.prod_prod, hZR]
  have hpre : e ⁻¹' E = daProposalEvent k c ∩ goodClockInput n := by
    ext x
    simp [E]
  have hpreZ : e ⁻¹' (E ∩ Prod.snd ⁻¹' Z) =
      (daProposalEvent k c ∩ goodClockInput n) ∩ {x | x (.inr c.2) c.1 ∈ S} := by
    rw [preimage_inter, hpre]
    rfl
  have h0 := he.measure_preimage hE.nullMeasurableSet
  have h1 := he.measure_preimage (hE.inter (measurable_snd hZ)).nullMeasurableSet
  rw [hpre, hE0] at h0
  rw [hpreZ, hEZ, ← h0] at h1
  have hg (A : Set (ScoreProfile n)) :
      (A ∩ goodClockInput n : Set _) =ᵐ[continuousScoreLaw n] A := by
    apply Filter.Eventually.set_eq
    filter_upwards [ae_goodClockInput n] with x hx
    simp [hx]
  rw [measure_congr (hg (daProposalEvent k c))] at h1
  refine (measure_congr ?_).trans h1
  apply Filter.Eventually.set_eq
  filter_upwards [ae_goodClockInput n] with x hx
  simp [hx]

private theorem DAState.proposalCount_run_eq_of_active (p : Profile n) (k : ℕ)
    (h : (DAState.run p k).nextProposal p.manRank ≠ none) :
    (DAState.run p k).proposalCount = k := by
  induction k with
  | zero => simp [DAState.run, DAState.initial, DAState.proposalCount]
  | succ k ih =>
    cases hp : (DAState.run p k).nextProposal p.manRank with
    | none => exact False.elim (h (by simp only [DAState.run, DAState.advance, hp]))
    | some c =>
      change (DAState.advance p (DAState.run p k)).proposalCount = k + 1
      rw [DAState.proposalCount_advance_of_some hp, ih (by simp [hp])]

private theorem DAState.exists_proposal_before_of_rank_lt_count (p : Profile n) (K : ℕ)
    (m w : Fin n) (h : (p.manRank m w).val < (DAState.run p K).count m) :
    ∃ k < K, (DAState.run p k).nextProposal p.manRank = some (m, w) := by
  induction K with
  | zero => simp [DAState.run, DAState.initial] at h
  | succ K ih =>
    by_cases hprev : (p.manRank m w).val < (DAState.run p K).count m
    · obtain ⟨k, hk, hp⟩ := ih hprev
      exact ⟨k, hk.trans (Nat.lt_succ_self _), hp⟩
    · change _ < (DAState.advance p (DAState.run p K)).count m at h
      cases hp : (DAState.run p K).nextProposal p.manRank with
      | none => exact False.elim (hprev (by simpa only [DAState.advance, hp] using h))
      | some c =>
        obtain ⟨a, b⟩ := c
        rw [DAState.advance, hp] at h
        have ham : m = a := by
          by_contra hne
          exact hprev (by simpa [DAState.applyDecision, hne] using h)
        subst a
        have hcount : (p.manRank m w).val = (DAState.run p K).count m := by
          simp only [DAState.applyDecision, Function.update_self] at h
          omega
        have hwb := (p.manRank m).injective (Fin.ext (hcount.trans
          (DAState.nextProposal_some hp).2.symm))
        exact ⟨K, Nat.lt_succ_self _, hwb ▸ hp⟩

private theorem DAState.proposalCount_run_mono (p : Profile n) :
    Monotone fun k ↦ (DAState.run p k).proposalCount :=
  fun _ _ h ↦ Finset.sum_le_sum fun m _ ↦ DAState.count_mono_run p m h

/-- Every final spouse pair occurs at a tick strictly below the number of proposals. -/
theorem DAState.exists_nextProposal_final_pair (p : Profile n) (w : Fin n) :
    ∃ k < (DAState.run p (n * n)).proposalCount,
      (DAState.run p k).nextProposal p.manRank = some ((DAState.matching p).symm w, w) := by
  obtain ⟨k, hk, hp⟩ := DAState.exists_proposal_before_of_rank_lt_count p (n * n) _ _
    (DAState.matching_symm_mem_proposedCells p w)
  have hc := DAState.proposalCount_run_eq_of_active p k (by simp [hp])
  have hm := DAState.proposalCount_run_mono p (Nat.succ_le_of_lt hk)
  change (DAState.advance p (DAState.run p k)).proposalCount ≤ _ at hm
  rw [DAState.proposalCount_advance_of_some hp, hc] at hm
  exact ⟨k, Nat.lt_of_succ_le hm, hp⟩

/-- At time `k`, the proposal selects `c` and its female score is at most `u`. -/
def daLowProposalEvent (k : ℕ) (u : ℝ) (c : Fin n × Fin n) : Set (ScoreProfile n) :=
  daProposalEvent k c ∩ {x | x (.inr c.2) c.1 ≤ u}

private theorem measurableSet_daLowProposalEvent (k : ℕ) (u : ℝ) (c : Fin n × Fin n) :
    MeasurableSet (daLowProposalEvent k u c) :=
  (measurableSet_daProposalEvent k c).inter
    (measurableSet_le ((measurable_pi_apply c.1).comp
      (measurable_pi_apply (Sum.inr c.2 : Fin n ⊕ Fin n)))
      measurable_const)

private theorem unitScoreLaw_Iic_le_ofReal (u : ℝ) :
    unitScoreLaw (Iic u) ≤ ENNReal.ofReal u := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iic]
  have hsub : Iic u ∩ Icc (0 : ℝ) 1 ⊆ Icc 0 u := fun _ hx ↦ ⟨hx.2.1, hx.1⟩
  simpa only [Real.volume_Icc, sub_zero] using (measure_mono (μ := volume) hsub)

private theorem sum_measure_daProposalEvent_le_one (k : ℕ) :
    ∑ c : Fin n × Fin n, continuousScoreLaw n (daProposalEvent k c) ≤ 1 := by
  have hd : Pairwise (fun c d : Fin n × Fin n ↦
      Disjoint (daProposalEvent k c) (daProposalEvent k d)) := by
    intro c d hne
    refine Set.disjoint_left.mpr fun x hc hd ↦ hne ?_
    exact Option.some.inj (hc.symm.trans hd)
  rw [← tsum_fintype (L := SummationFilter.unconditional (Fin n × Fin n)),
    ← measure_iUnion hd (measurableSet_daProposalEvent k)]
  exact (measure_mono (subset_univ _)).trans_eq measure_univ

private theorem sum_measure_daLowProposalEvent_le (k : ℕ) (u : ℝ) :
    ∑ c : Fin n × Fin n, continuousScoreLaw n (daLowProposalEvent k u c) ≤
      ENNReal.ofReal u := by
  have h c : continuousScoreLaw n (daLowProposalEvent k u c) =
      continuousScoreLaw n (daProposalEvent k c) * unitScoreLaw (Iic u) :=
    measure_daProposalEvent_inter_score k c measurableSet_Iic
  simp_rw [h, ← Finset.sum_mul]
  exact (mul_le_mul' (sum_measure_daProposalEvent_le_one k) (unitScoreLaw_Iic_le_ofReal u)).trans
    (one_mul _).le

/-- The number of low-score female cells read in the first \`T\` ordinal ticks. -/
noncomputable def daLowProposalCount (T : ℕ) (u : ℝ) (x : ScoreProfile n) : ℝ≥0∞ :=
  (Finset.univ.filter fun a : Fin T × (Fin n × Fin n) ↦
    x ∈ daLowProposalEvent a.1.val u a.2).card

private theorem daLowProposalCount_eq_sum (T : ℕ) (u : ℝ) (x : ScoreProfile n) :
    daLowProposalCount T u x = ∑ a : Fin T × (Fin n × Fin n),
      (daLowProposalEvent a.1.val u a.2).indicator 1 x := by
  simp [daLowProposalCount, Set.indicator]

theorem measurable_daLowProposalCount (T : ℕ) (u : ℝ) :
    Measurable (daLowProposalCount (n := n) T u) := by
  simp_rw [show daLowProposalCount (n := n) T u = _ from funext (daLowProposalCount_eq_sum T u)]
  exact Finset.measurable_sum _ fun a _ ↦ measurable_const.indicator
    (measurableSet_daLowProposalEvent a.1.val u a.2)

/-- The expected number of low scores in \`T\` ticks is at most \`T * u\`. -/
theorem lintegral_daLowProposalCount_le (T : ℕ) (u : ℝ) :
    (∫⁻ x, daLowProposalCount T u x ∂continuousScoreLaw n) ≤
      (T : ℝ≥0∞) * ENNReal.ofReal u := by
  simp_rw [daLowProposalCount_eq_sum]
  rw [lintegral_finsetSum _ (f := fun a : Fin T × (Fin n × Fin n) ↦
    (daLowProposalEvent a.1.val u a.2).indicator 1) (fun a _ ↦ measurable_const.indicator
    (measurableSet_daLowProposalEvent a.1.val u a.2))]
  simp_rw [lintegral_indicator_one (measurableSet_daLowProposalEvent _ _ _)]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _ : Fin T, ENNReal.ofReal u :=
      Finset.sum_le_sum fun a _ ↦ sum_measure_daLowProposalEvent_le a.val u
    _ = _ := by simp [nsmul_eq_mul]

private theorem card_low_spouse_le_daLowProposalCount (T : ℕ) (u : ℝ) (x : ScoreProfile n)
    (hcap : (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T) :
    ((Finset.univ.filter fun w : Fin n ↦
      femaleSpouseScore x (DAState.matching (profileOfScores x)) w ≤ u).card : ℝ≥0∞) ≤
      daLowProposalCount T u x := by
  let p := profileOfScores x
  have hex (w : Fin n) : ∃ k : Fin T,
      (DAState.run p k.val).nextProposal p.manRank = some ((DAState.matching p).symm w, w) := by
    obtain ⟨k, hk, hp⟩ := DAState.exists_nextProposal_final_pair p w
    exact ⟨⟨k, hk.trans_le hcap⟩, hp⟩
  choose f hf using hex
  unfold daLowProposalCount
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun w ↦ (f w, (DAState.matching p).symm w, w))
  · intro w hw
    change w ∈ Finset.univ.filter (fun w ↦ femaleSpouseScore x (DAState.matching p) w ≤ u) at hw
    have hs := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf w, hs⟩
  · intro a _ b _ hab
    exact congrArg (fun v : Fin T × (Fin n × Fin n) ↦ v.2.2) hab

private theorem half_le_card_low_of_sum_le (a : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (u : ℝ) (hu : 0 < u) (hsmall : ∑ j, a j ≤ u * ((n : ℝ) / 2)) :
    (n : ℝ) / 2 ≤ ((Finset.univ.filter fun w ↦ a w ≤ u).card : ℝ) := by
  let lo := Finset.univ.filter fun w ↦ a w ≤ u
  let hi := Finset.univ.filter fun w ↦ ¬ a w ≤ u
  have hcard : lo.card + hi.card = n := by
    simpa only [lo, hi, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun w ↦ a w ≤ u)
  have hsum : (hi.card : ℝ) * u ≤ ∑ j, a j := by
    calc
      _ = ∑ _ ∈ hi, u := by simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ hi, a j := Finset.sum_le_sum fun j hj ↦
        le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hj).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ hi)
        (fun j _ _ ↦ ha j)
  have hhi : (hi.card : ℝ) ≤ (n : ℝ) / 2 :=
    (mul_le_mul_iff_left₀ hu).mp (by simpa only [mul_comm u ((n : ℝ) / 2)] using hsum.trans hsmall)
  have hcast : (lo.card : ℝ) + (hi.card : ℝ) = n := by exact_mod_cast hcard
  change (n : ℝ) / 2 ≤ (lo.card : ℝ)
  linarith

/-- A small spouse-score total with at most \`T\` proposals has a finite-time
Markov bound. There is no distributional assumption on the terminal spouse choices. -/
theorem measure_badManOptimalScore_inter_proposalCap_le {T : ℕ} {u : ℝ}
    (hn : 0 < n) (hu : 0 < u) :
    continuousScoreLaw n {x |
      femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ u * ((n : ℝ) / 2) ∧
      (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T} ≤
      (T : ℝ≥0∞) * ENNReal.ofReal u / ENNReal.ofReal ((n : ℝ) / 2) := by
  have hpos : 0 < (n : ℝ) / 2 := by positivity
  have hsub : ∀ᵐ x ∂continuousScoreLaw n,
      (femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ u * ((n : ℝ) / 2) ∧
      (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T) →
      ENNReal.ofReal ((n : ℝ) / 2) ≤ daLowProposalCount T u x := by
    filter_upwards [ae_unitOpen_scores n] with x hx hh
    have hhalf := half_le_card_low_of_sum_le
      (femaleSpouseScore x (DAState.matching (profileOfScores x)))
      (fun j ↦ (hx (.inr j) ((DAState.matching (profileOfScores x)).symm j)).1.le) u hu hh.1
    have hcast := ENNReal.ofReal_le_ofReal hhalf
    rw [ENNReal.ofReal_natCast] at hcast
    exact hcast.trans (card_low_spouse_le_daLowProposalCount T u x hh.2)
  refine (measure_mono_ae hsub).trans
    ((meas_ge_le_lintegral_div (measurable_daLowProposalCount T u).aemeasurable
      (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).trans ?_)
  exact ENNReal.div_le_div_right (lintegral_daLowProposalCount_le T u) _

/-- A high-probability logarithmic proposal cap makes the men-optimal
female spouse-score total exceed the upper end of the pivot band. -/
theorem tendsto_measure_badManOptimalScore_of_proposalCap {C : ℝ} (T : ℕ → ℕ)
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ C * n * Real.log n)
    (hcap : Tendsto (fun n ↦ continuousScoreLaw n {x |
      T n < (DAState.run (profileOfScores x) (n * n)).proposalCount}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ continuousScoreLaw n {x |
      femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ (n : ℝ) ^ (2 / 5 : ℝ)})
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (3 / 5 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (4 * C * (Real.log n / (n : ℝ) ^ (3 / 5 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hlog)
  have hsum : Tendsto (fun n ↦ continuousScoreLaw n {x |
      T n < (DAState.run (profileOfScores x) (n * n)).proposalCount} +
      ENNReal.ofReal (4 * C * (Real.log n / (n : ℝ) ^ (3 / 5 : ℝ)))) atTop (𝓝 0) := by
    simpa only [add_zero] using hcap.add hdecay
  refine tendsto_const_nhds.squeeze' hsum (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hT, eventually_gt_atTop (0 : ℕ)] with n hTn hn
  let u : ℝ := 2 * (n : ℝ) ^ (2 / 5 : ℝ) / n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu : 0 < u := by dsimp [u]; positivity
  have hscale : u * ((n : ℝ) / 2) = (n : ℝ) ^ (2 / 5 : ℝ) := by
    dsimp [u]
    field_simp
  have hmark := measure_badManOptimalScore_inter_proposalCap_le (T := T n) hn hu
  rw [hscale] at hmark
  let B : Set (ScoreProfile n) := {x |
    femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ (n : ℝ) ^ (2 / 5 : ℝ)}
  let E : Set (ScoreProfile n) :=
    {x | T n < (DAState.run (profileOfScores x) (n * n)).proposalCount}
  let G : Set (ScoreProfile n) := {x |
    femaleSpouseTotal x (DAState.matching (profileOfScores x)) ≤ (n : ℝ) ^ (2 / 5 : ℝ) ∧
    (DAState.run (profileOfScores x) (n * n)).proposalCount ≤ T n}
  have hsub : B ⊆ E ∪ G := by
    intro x hx
    by_cases h : x ∈ E
    · exact Or.inl h
    · exact Or.inr ⟨hx, le_of_not_gt h⟩
  change continuousScoreLaw n B ≤ continuousScoreLaw n E + _
  calc
    _ ≤ continuousScoreLaw n (E ∪ G) := measure_mono hsub
    _ ≤ continuousScoreLaw n E + continuousScoreLaw n G := measure_union_le E G
    _ ≤ continuousScoreLaw n E + ((T n : ℝ≥0∞) * ENNReal.ofReal u /
        ENNReal.ofReal ((n : ℝ) / 2)) := add_le_add_right hmark _
    _ ≤ _ := by
      apply add_le_add_right
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (T n)),
        ← ENNReal.ofReal_div_of_pos (by positivity : 0 < (n : ℝ) / 2)]
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hTn hu.le) (by positivity)).trans
      apply le_of_eq
      have hpow : (n : ℝ) ^ (3 / 5 : ℝ) = (n : ℝ) / (n : ℝ) ^ (2 / 5 : ℝ) := by
        rw [show (3 / 5 : ℝ) = 1 - 2 / 5 by norm_num, Real.rpow_sub hn', Real.rpow_one]
      rw [hpow]
      dsimp [u]
      field_simp
      norm_num

end LennonPittelFormalization

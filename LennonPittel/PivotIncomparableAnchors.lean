module

public import LennonPittel.PivotLocalEligibility
public import LennonPittel.PivotSingletonMarkedLength
public import LennonPittel.PivotTwoCycleForest
public import LennonPittel.SingletonRotationAnchor

/-!
# The intersection anchor for incomparable pivots

The intersection of two singleton anchor ideals omits the union of the
two principal upper sets. If the pivots are incomparable, they are exactly
the minimal omitted elements. The intersection matching and the ordered
pair of its exposed cycles recover the original realized pivots.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The minimal elements omitted by the meet of the two singleton ideals
are precisely the incomparable generators. -/
theorem minimal_compl_inf_singletonAnchorIdeal_iff {α : Type*} [PartialOrder α]
    {r s : α} (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) (t : α) :
    Minimal (· ∉ (singletonAnchorIdeal r ⊓ singletonAnchorIdeal s : LowerSet α)) t ↔
      t = r ∨ t = s := by
  classical
  simp only [minimal_iff_forall_lt, LowerSet.mem_inf_iff, mem_singletonAnchorIdeal, not_not]
  constructor
  · rintro ⟨ht, hpred⟩
    have ht' : r ≤ t ∨ s ≤ t := by
      by_cases hrt : r ≤ t
      · exact Or.inl hrt
      · exact Or.inr (not_not.mp fun hst ↦ ht ⟨hrt, hst⟩)
    rcases ht' with hrt | hst
    · rcases eq_or_lt_of_le hrt with he | hlt
      · exact Or.inl he.symm
      · exact ((hpred hlt).1 le_rfl).elim
    · rcases eq_or_lt_of_le hst with he | hlt
      · exact Or.inr he.symm
      · exact ((hpred hlt).2 le_rfl).elim
  · rintro (rfl | rfl)
    · exact ⟨fun h ↦ h.1 le_rfl, fun _ h ↦ ⟨h.not_ge, fun hs ↦ hsr (hs.trans h.le)⟩⟩
    · exact ⟨fun h ↦ h.2 le_rfl, fun _ h ↦ ⟨fun hr ↦ hrs (hr.trans h.le), h.not_ge⟩⟩

variable {n : ℕ} {p : Profile n} {μ₀ : Matching n}

/-- The stable matching corresponding to the intersection of the two anchor ideals. -/
noncomputable def twoRotationAnchor (hopt : IsManOptimal p μ₀) (r s : Rotation p μ₀) :
    {μ : Matching n // IsStable p μ} :=
  (stableMatchingEquivRotationIdeals hopt).symm (singletonAnchorIdeal r ⊓ singletonAnchorIdeal s)

/-- The intersection anchor eliminates exactly the rotations eliminated at both singleton anchors. -/
theorem eliminatedRotations_twoRotationAnchor (hopt : IsManOptimal p μ₀) (r s : Rotation p μ₀) :
    eliminatedRotations p μ₀ (twoRotationAnchor hopt r s).val =
      eliminatedRotations p μ₀ (singletonRotationAnchor hopt r).val ∩
        eliminatedRotations p μ₀ (singletonRotationAnchor hopt s).val := by
  let e := stableMatchingEquivRotationIdeals hopt
  rw [eliminatedRotations_singletonRotationAnchor, eliminatedRotations_singletonRotationAnchor]
  exact congrArg (fun I : LowerSet (Rotation p μ₀) ↦ (I : Set (Rotation p μ₀)))
    (e.apply_symm_apply (singletonAnchorIdeal r ⊓ singletonAnchorIdeal s))

/-- The order of the singleton anchors agrees with the prerequisite order. -/
private theorem singletonAnchor_pref_iff (hopt : IsManOptimal p μ₀)
    (r s : Rotation p μ₀) :
    MenWeaklyPrefer p (singletonRotationAnchor hopt r).val
        (singletonRotationAnchor hopt s).val ↔ r ≤ s := by
  rw [← eliminatedRotations_subset_iff hopt (singletonRotationAnchor hopt r).property
    (singletonRotationAnchor hopt s).property, eliminatedRotations_singletonRotationAnchor,
    eliminatedRotations_singletonRotationAnchor]
  constructor
  · intro h
    by_contra hrs
    exact h (show s ∈ (Set.Ici r)ᶜ from hrs) (Set.mem_Ici.mpr le_rfl)
  · exact fun hrs _ hx hs ↦ hx (hrs.trans hs)

/-- At the intersection anchor exactly the two incomparable labels are exposed. -/
theorem isExposedAt_twoRotationAnchor_iff (hopt : IsManOptimal p μ₀)
    {r s : Rotation p μ₀} (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) (t : Rotation p μ₀) :
    t.IsExposedAt (twoRotationAnchor hopt r s).val ↔ t = r ∨ t = s := by
  let μ := twoRotationAnchor hopt r s
  rw [Rotation.isExposedAt_iff_minimal hopt μ.property,
    eliminatedRotations_twoRotationAnchor, eliminatedRotations_singletonRotationAnchor,
    eliminatedRotations_singletonRotationAnchor]
  exact minimal_compl_inf_singletonAnchorIdeal_iff hrs hsr t

/-- At the intersection anchor exactly the two incomparable cycles are exposed. -/
theorem hasExactlyTwoForwardExposedRotations_twoRotationAnchor
    (hopt : IsManOptimal p μ₀) {r s : Rotation p μ₀} (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    HasExactlyTwoForwardExposedRotations p (twoRotationAnchor hopt r s).val
      r.val.cycle s.val.cycle := by
  let μ := twoRotationAnchor hopt r s
  have he (t : Rotation p μ₀) := isExposedAt_twoRotationAnchor_iff hopt hrs hsr t
  have hr := (he r).mpr (Or.inl rfl)
  have hs := (he s).mpr (Or.inr rfl)
  refine ⟨fun h ↦ hrs (le_of_eq ?_), hr.1, hs.1, fun τ hτ ↦ ?_⟩
  · exact Subtype.ext (hr.2.symm.trans ((congrArg (rotationLabel μ.val) h).trans hs.2))
  · let t := rotationOfExposed hopt μ.property hτ
    rcases (he t).mp ⟨hτ, rfl⟩ with h | h
    · exact Or.inl (congrArg (fun q : Rotation p μ₀ ↦ q.val.cycle) h)
    · exact Or.inr (congrArg (fun q : Rotation p μ₀ ↦ q.val.cycle) h)

/-- At a given matching an exposed cycle determines its realized rotation label. -/
theorem Rotation.IsExposedAt.eq_of_cycle_eq {μ : Matching n} {r s : Rotation p μ₀}
    (hr : r.IsExposedAt μ) (hs : s.IsExposedAt μ) (he : r.val.cycle = s.val.cycle) : r = s :=
  Subtype.ext (hr.2.symm.trans ((congrArg (rotationLabel μ) he).trans hs.2))

/-- Ordered pairs of incomparable pivots that pass the local test at their
respective singleton anchors. No decoration is selected. -/
abbrev IncomparableEligiblePivotPair {x : ScoreProfile n} {μ₀ : Matching n}
    (hopt : IsManOptimal (profileOfScores x) μ₀) (b A B : ℝ) :=
  {rs : Rotation (profileOfScores x) μ₀ × Rotation (profileOfScores x) μ₀ //
    (¬ rs.1 ≤ rs.2) ∧ (¬ rs.2 ≤ rs.1) ∧
      IsLocallyEligiblePivot b A B x (singletonRotationAnchor hopt rs.1).val rs.1.val.cycle ∧
      IsLocallyEligiblePivot b A B x (singletonRotationAnchor hopt rs.2).val rs.2.val.cycle}

/-- A stable matching marked by the ordered pair of its only exposed
rotations, both in the given length window. -/
abbrev MarkedTwoForwardExposedWindow (p : Profile n) (b A : ℝ) :=
  {M : Matching n × Matching n × Matching n //
    IsStable p M.1 ∧ HasExactlyTwoForwardExposedRotations p M.1 M.2.1 M.2.2 ∧
      M.2.1.support.card ∈ forwardLengthWindow n b A ∧
      M.2.2.support.card ∈ forwardLengthWindow n b A}

/-- A genuine cycle passing the local pivot test retains its length window
when exposed at another matching. -/
theorem IsLocallyEligiblePivot.mem_forwardLengthWindow {x : ScoreProfile n}
    {μ ρ : Matching n} {b A B : ℝ} (h : IsLocallyEligiblePivot b A B x μ ρ)
    (hρ : ρ.IsCycle) : ρ.support.card ∈ forwardLengthWindow n b A := by
  rw [forwardLengthWindow, Finset.mem_filter, Finset.mem_Icc]
  have hcard : ρ.support.card ≤ n := by simpa using ρ.support.card_le_univ
  exact ⟨⟨hρ.two_le_card_support, hcard⟩, h.1.length_lower, h.1.length_upper⟩

/-- The two exposed cycles at the intersection anchor recover both original
eligible pivots in their original order. -/
noncomputable def incomparableEligiblePivotPairEmbedding {x : ScoreProfile n}
    (hopt : IsManOptimal (profileOfScores x) μ₀) (b A B : ℝ) :
    IncomparableEligiblePivotPair hopt b A B ↪
      MarkedTwoForwardExposedWindow (profileOfScores x) b A where
  toFun z := by
    let μ := twoRotationAnchor hopt z.val.1 z.val.2
    have ht := hasExactlyTwoForwardExposedRotations_twoRotationAnchor hopt
      z.property.1 z.property.2.1
    exact ⟨(μ.val, z.val.1.val.cycle, z.val.2.val.cycle), μ.property, ht,
      z.property.2.2.1.mem_forwardLengthWindow ht.2.1.isCycle,
      z.property.2.2.2.mem_forwardLengthWindow ht.2.2.1.isCycle⟩
  inj' := by
    intro z w h
    let μ := twoRotationAnchor hopt z.val.1 z.val.2
    let ν := twoRotationAnchor hopt w.val.1 w.val.2
    have hμ : μ.val = ν.val := congrArg (fun M ↦ M.val.1) h
    have hc₁ : z.val.1.val.cycle = w.val.1.val.cycle := congrArg (fun M ↦ M.val.2.1) h
    have hc₂ : z.val.2.val.cycle = w.val.2.val.cycle := congrArg (fun M ↦ M.val.2.2) h
    have hz₁ : z.val.1.IsExposedAt μ.val :=
      (isExposedAt_twoRotationAnchor_iff hopt z.property.1 z.property.2.1 _).mpr (Or.inl rfl)
    have hz₂ : z.val.2.IsExposedAt μ.val :=
      (isExposedAt_twoRotationAnchor_iff hopt z.property.1 z.property.2.1 _).mpr (Or.inr rfl)
    have hw₁ : w.val.1.IsExposedAt ν.val :=
      (isExposedAt_twoRotationAnchor_iff hopt w.property.1 w.property.2.1 _).mpr (Or.inl rfl)
    have hw₂ : w.val.2.IsExposedAt ν.val :=
      (isExposedAt_twoRotationAnchor_iff hopt w.property.1 w.property.2.1 _).mpr (Or.inr rfl)
    rw [← hμ] at hw₁ hw₂
    exact Subtype.ext (Prod.ext (hz₁.eq_of_cycle_eq hw₁ hc₁) (hz₂.eq_of_cycle_eq hw₂ hc₂))

/-- Pointwise domination of the number of bare incomparable eligible pairs
by the number of ordered long exact-two marks. -/
theorem card_incomparableEligiblePivotPair_le {x : ScoreProfile n}
    (hopt : IsManOptimal (profileOfScores x) μ₀) (b A B : ℝ) :
    Nat.card (IncomparableEligiblePivotPair hopt b A B) ≤
      Nat.card (MarkedTwoForwardExposedWindow (profileOfScores x) b A) :=
  Nat.card_le_card_of_injective _ (incomparableEligiblePivotPairEmbedding hopt b A B).injective

/-- The bare count written on fixed labeled anchors, without reference to a
choice of man-optimal start. Each anchor carries its tested sole cycle. -/
abbrev IncomparableEligibleAnchorMarks (b A B : ℝ) (x : ScoreProfile n) :=
  {ij : (Matching n × Matching n) × (Matching n × Matching n) //
    IsScoreStable x ij.1.1 ∧ IsScoreStable x ij.2.1 ∧
      IsLocallyEligiblePivot b A B x ij.1.1 ij.1.2 ∧
      IsLocallyEligiblePivot b A B x ij.2.1 ij.2.2 ∧
      (¬ MenWeaklyPrefer (profileOfScores x) ij.1.1 ij.2.1) ∧
      (¬ MenWeaklyPrefer (profileOfScores x) ij.2.1 ij.1.1)}

/-- The score event contributing one to the ordered bare count for the
given fixed pair of labeled anchor marks. -/
def incomparableEligibleAnchorMarksEvent (b A B : ℝ)
    (i j : Matching n × Matching n) : Set (ScoreProfile n) :=
  {x | IsScoreStable x i.1 ∧ IsScoreStable x j.1 ∧
    IsLocallyEligiblePivot b A B x i.1 i.2 ∧ IsLocallyEligiblePivot b A B x j.1 j.2 ∧
    (¬ MenWeaklyPrefer (profileOfScores x) i.1 j.1) ∧
    (¬ MenWeaklyPrefer (profileOfScores x) j.1 i.1)}

theorem measurableSet_incomparableEligibleAnchorMarksEvent (b A B : ℝ)
    (i j : Matching n × Matching n) : MeasurableSet (incomparableEligibleAnchorMarksEvent b A B i j) :=
  (measurableSet_isScoreStable i.1).inter ((measurableSet_isScoreStable j.1).inter
    ((measurableSet_isLocallyEligiblePivot b A B i.1 i.2).inter
      ((measurableSet_isLocallyEligiblePivot b A B j.1 j.2).inter
        (measurable_profileOfScores n (MeasurableSet.of_discrete :
          MeasurableSet {p : Profile n | (¬ MenWeaklyPrefer p i.1 j.1) ∧
            (¬ MenWeaklyPrefer p j.1 i.1)})))))

/-- The subtype cardinality is exactly the indicator sum over the fixed
labeled anchor pairs used in the centered-moment decomposition. -/
theorem natCard_incomparableEligibleAnchorMarks_eq_sum {R : Type*} [AddCommMonoidWithOne R]
    (b A B : ℝ) (x : ScoreProfile n) :
    (Nat.card (IncomparableEligibleAnchorMarks b A B x) : R) =
      ∑ i : Matching n × Matching n, ∑ j : Matching n × Matching n,
        (incomparableEligibleAnchorMarksEvent b A B i j).indicator (fun _ ↦ (1 : R)) x := by
  classical
  let P (ij : (Matching n × Matching n) × (Matching n × Matching n)) :=
    x ∈ incomparableEligibleAnchorMarksEvent b A B ij.1 ij.2
  change (Nat.card {ij // P ij} : R) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype P, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : x ∈ incomparableEligibleAnchorMarksEvent b A B i j
  · rw [ite_eq_left (show P (i, j) from h), indicator_of_mem h, Nat.cast_one]
  · rw [ite_eq_right (show ¬ P (i, j) from h), indicator_of_notMem h]

/-- A stable mark with sole exposed cycle is the singleton anchor for the
label that it realizes. -/
private theorem eq_singletonRotationAnchor_of_isSoleForwardExposed
    (hopt : IsManOptimal p μ₀) {μ σ : Matching n} (hμ : IsStable p μ)
    (hσ : IsSoleForwardExposedRotation p μ σ) :
    (⟨μ, hμ⟩ : {μ : Matching n // IsStable p μ}) =
      singletonRotationAnchor hopt (rotationOfExposed hopt hμ hσ.1) := by
  let r := rotationOfExposed hopt hμ hσ.1
  apply (eq_singletonRotationAnchor_iff hopt r _).mpr
  intro s
  constructor
  · intro hs
    exact hs.eq_of_cycle_eq (show r.IsExposedAt μ from ⟨hσ.1, rfl⟩)
      (hσ.2 _ hs.1)
  · rintro rfl
    exact ⟨hσ.1, rfl⟩

/-- The fixed labeled-anchor count injects into the rotation-label count.
Tie-freeness is used only to read the local score test as actual exposure. -/
@[no_expose] noncomputable def incomparableEligibleAnchorMarksEmbedding {x : ScoreProfile n}
    (hopt : IsManOptimal (profileOfScores x) μ₀) (ht : ∀ row, Function.Injective (x row))
    (b A B : ℝ) : IncomparableEligibleAnchorMarks b A B x ↪
      IncomparableEligiblePivotPair hopt b A B := by
  let hs (z : IncomparableEligibleAnchorMarks b A B x) :
      IsStable (profileOfScores x) z.val.1.1 :=
    (isStable_profileOfScores_iff ht _).mpr z.property.1
  let ht' (z : IncomparableEligibleAnchorMarks b A B x) :
      IsStable (profileOfScores x) z.val.2.1 :=
    (isStable_profileOfScores_iff ht _).mpr z.property.2.1
  let he₁ (z : IncomparableEligibleAnchorMarks b A B x) :=
    z.property.2.2.1.isSoleForwardExposed ht
  let he₂ (z : IncomparableEligibleAnchorMarks b A B x) :=
    z.property.2.2.2.1.isSoleForwardExposed ht
  let r (z : IncomparableEligibleAnchorMarks b A B x) :=
    rotationOfExposed hopt (hs z) (he₁ z).1
  let s (z : IncomparableEligibleAnchorMarks b A B x) :=
    rotationOfExposed hopt (ht' z) (he₂ z).1
  have hr (z : IncomparableEligibleAnchorMarks b A B x) :
      z.val.1.1 = (singletonRotationAnchor hopt (r z)).val :=
    congrArg Subtype.val (eq_singletonRotationAnchor_of_isSoleForwardExposed hopt (hs z) (he₁ z))
  have hq (z : IncomparableEligibleAnchorMarks b A B x) :
      z.val.2.1 = (singletonRotationAnchor hopt (s z)).val :=
    congrArg Subtype.val (eq_singletonRotationAnchor_of_isSoleForwardExposed hopt (ht' z) (he₂ z))
  refine ⟨fun z ↦ ⟨(r z, s z), ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h
    apply z.property.2.2.2.2.1
    rw [hr z, hq z]
    exact (singletonAnchor_pref_iff hopt _ _).mpr h
  · intro h
    apply z.property.2.2.2.2.2
    rw [hr z, hq z]
    exact (singletonAnchor_pref_iff hopt _ _).mpr h
  · exact hr z ▸ z.property.2.2.1
  · exact hq z ▸ z.property.2.2.2.1
  · intro z w h
    have h₁ : r z = r w := congrArg (fun a ↦ a.val.1) h
    have h₂ : s z = s w := congrArg (fun a ↦ a.val.2) h
    apply Subtype.ext
    exact Prod.ext
      (Prod.ext ((hr z).trans ((congrArg (fun t ↦ (singletonRotationAnchor hopt t).val) h₁).trans
        (hr w).symm)) (congrArg (fun t : Rotation (profileOfScores x) μ₀ ↦ t.val.cycle) h₁))
      (Prod.ext ((hq z).trans ((congrArg (fun t ↦ (singletonRotationAnchor hopt t).val) h₂).trans
        (hq w).symm)) (congrArg (fun t : Rotation (profileOfScores x) μ₀ ↦ t.val.cycle) h₂))

/-- The actual bare score-mark count is bounded by the long exact-two count. -/
theorem card_incomparableEligibleAnchorMarks_le {x : ScoreProfile n}
    (ht : ∀ row, Function.Injective (x row)) (b A B : ℝ) :
    Nat.card (IncomparableEligibleAnchorMarks b A B x) ≤
      Nat.card (MarkedTwoForwardExposedWindow (profileOfScores x) b A) := by
  rcases isEmpty_or_nonempty (IncomparableEligibleAnchorMarks b A B x) with he | ⟨⟨z⟩⟩
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  · obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable
      ⟨z.val.1.1, (isStable_profileOfScores_iff ht _).mpr z.property.1⟩
    exact (Nat.card_le_card_of_injective _
      (incomparableEligibleAnchorMarksEmbedding hopt ht b A B).injective).trans
        (card_incomparableEligiblePivotPair_le hopt b A B)

/-- Existence of the two forward rotations in the length window at a fixed mark. -/
def HasTwoForwardExposedWindow (p : Profile n) (μ : Matching n) (b A : ℝ) : Prop :=
  ∃ σ τ : Matching n, HasExactlyTwoForwardExposedRotations p μ σ τ ∧
    σ.support.card ∈ forwardLengthWindow n b A ∧ τ.support.card ∈ forwardLengthWindow n b A

/-- The exact-two window event is bounded by the ordered-pair mass. -/
theorem measureReal_hasTwoForwardExposedWindow_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (μ : Matching n) (b A : ℝ) :
    ν.real {x | HasTwoForwardExposedWindow (P x) μ b A} ≤
      ∑ k ∈ forwardLengthWindow n b A, ∑ l ∈ forwardLengthWindow n b A,
        ∑ σ ∈ forwardCyclesOfLength n k, ∑ τ ∈ forwardCyclesOfLength n l,
          ν.real {x | HasExactlyTwoForwardExposedRotations (P x) μ σ τ} := by
  classical
  let L := forwardLengthWindow n b A
  have heq : {x | HasTwoForwardExposedWindow (P x) μ b A} =
      ⋃ k ∈ L, ⋃ l ∈ L, ⋃ σ ∈ forwardCyclesOfLength n k, ⋃ τ ∈ forwardCyclesOfLength n l,
        {x | HasExactlyTwoForwardExposedRotations (P x) μ σ τ} := by
    ext x
    simp only [HasTwoForwardExposedWindow, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨σ, τ, h, hk, hl⟩
      refine ⟨σ.support.card, hk, τ.support.card, hl, σ, ?_, τ, ?_, h⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.1.isCycle, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.2.1.isCycle, rfl⟩
    · rintro ⟨k, hk, l, hl, σ, hσ, τ, hτ, h⟩
      exact ⟨σ, τ, h, ((Finset.mem_filter.mp hσ).2.2).symm ▸ hk,
        ((Finset.mem_filter.mp hτ).2.2).symm ▸ hl⟩
  rw [heq]
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
  refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
  exact measureReal_biUnion_finset_le _ _

/-- The actual full-score event of a score-stable matching with two forward
rotations in the required length window. -/
def scoreStableTwoForwardWindowEvent (μ : Matching n) (b A : ℝ) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ HasTwoForwardExposedWindow (profileOfScores x) μ b A}

theorem measurableSet_scoreStableTwoForwardWindowEvent (μ : Matching n) (b A : ℝ) :
    MeasurableSet (scoreStableTwoForwardWindowEvent μ b A) :=
  (measurableSet_isScoreStable μ).inter
    (measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | HasTwoForwardExposedWindow p μ b A}))

/-- Constant for the normalized good-diagonal window estimate. -/
noncomputable def twoForwardWindowConstant (b A : ℝ) : ℝ :=
  Real.exp (1 + 2 * A) * ((A + 1) / b) ^ 2 * (27 + 48 * A)

/-- Summing the good-diagonal probability over all marks and charging each
exceptional mark once gives a bound in the original score law. -/
theorem eventually_sum_measure_scoreStableTwoForwardWindowEvent_le {b A : ℝ}
    (hb : 0 < b) (hA₀ : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n (scoreStableTwoForwardWindowEvent μ b A)) ≤
        ENNReal.ofReal (twoForwardWindowConstant b A * Real.sqrt n * Real.log n +
          (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds,
    eventually_hasForwardReferenceDeficit_of_singletonLengthGoodDiagonal,
    eventually_sum_measure_badSingletonLengthDiagonal_le,
    eventually_expectedNumStableMatchings_le_sizeLog] with n hp hdef hbad hmean
  obtain ⟨hn, hη₀, hη, hA, hB, hδ⟩ := hp
  let C := singletonLengthGoodDiagonal n
  let D := Real.exp (1 + 2 * A) * ((A + 1) / b) ^ 2
  let c := twoForwardWindowConstant b A
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn₀
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn₀.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hc : 0 ≤ c := by dsimp [c, twoForwardWindowConstant]; positivity
  have hpw : Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num)
  have hbud : singletonLengthBudget n ≤ 27 / Real.sqrt n :=
    (singletonLengthBudget_le hn).trans
      (div_le_div_of_nonneg_left (by norm_num) hs hpw)
  have hrest : (2 * A * Real.sqrt n) * (24 / (n : ℝ)) = (48 * A) / Real.sqrt n := by
    rw [show 24 / (n : ℝ) = 24 / (Real.sqrt (n : ℝ)) ^ 2 by rw [hsq]]
    field_simp
    ring
  have hg (μ : Matching n) :
      continuousScoreLaw n
        {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧
          HasTwoForwardExposedWindow (profileOfScores x) μ b A} ≤
        continuousScoreLaw n {x | IsScoreStable x μ} * ENNReal.ofReal (c / Real.sqrt n) := by
    let : MeasurableSpace (Option (Fin n)) := ⊤
    let : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
    refine measure_scoreStable_diagonal_rankEvent_le μ (measurableSet_singletonLengthGoodDiagonal n)
      (fun _ h ↦ ⟨h.2.1, h.2.2.1⟩) {p | HasTwoForwardExposedWindow p μ b A} ?_
    filter_upwards [ae_diagonal_sum_measureReal_exactlyTwoForwardExposedWindow_le
      hn μ hb hA₀ hη₀ hη hA hB hδ] with d hd
    intro h
    let P (r : OffDiagonalScoreRows n) :=
      profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))
    refine (measureReal_hasTwoForwardExposedWindow_le _ P μ b A).trans
      ((hd h.1 h.2.1 h.2.2.1 _ (hdef d h)).trans ?_)
    have hds : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) := h.2.2.2.2.1
    change D * (3 * (n : ℝ) ^ (-3 / 4 : ℝ) + (∑ i, (forwardSpouseWeight d i) ^ 2) +
        (2 * A * Real.sqrt n) * ∑ i, (forwardSpouseWeight d i) ^ 2) ≤ c / Real.sqrt n
    calc
      _ ≤ D * (singletonLengthBudget n + (2 * A * Real.sqrt n) * (24 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add_right hds _)
          (mul_le_mul_of_nonneg_left hds (by positivity))) hD
      _ ≤ D * (27 / Real.sqrt n + (48 * A) / Real.sqrt n) := by
        rw [hrest]
        exact mul_le_mul_of_nonneg_left (add_le_add_left hbud _) hD
      _ = _ := by unfold c twoForwardWindowConstant D; ring
  have hm (μ : Matching n) :
      continuousScoreLaw n (scoreStableTwoForwardWindowEvent μ b A) ≤
        continuousScoreLaw n {x | IsScoreStable x μ} * ENNReal.ofReal (c / Real.sqrt n) +
          continuousScoreLaw n (badSingletonLengthDiagonalEvent μ C) := by
    refine (measure_mono (t := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C ∧
      HasTwoForwardExposedWindow (profileOfScores x) μ b A} ∪
      badSingletonLengthDiagonalEvent μ C) ?_).trans ((measure_union_le _ _).trans
        (add_le_add (hg μ) le_rfl))
    intro x hx
    by_cases h : (splitScorePairs μ x).1 ∈ C
    · exact Or.inl ⟨hx.1, h, hx.2⟩
    · exact Or.inr ⟨hx.1, h⟩
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (c / Real.sqrt n) +
          continuousScoreLaw n (badSingletonLengthDiagonalEvent μ C)) :=
      Finset.sum_le_sum fun μ _ ↦ hm μ
    _ ≤ ENNReal.ofReal ((n : ℝ) * Real.log n) * ENNReal.ofReal (c / Real.sqrt n) +
        ENNReal.ofReal ((n : ℝ) ^ (-3 : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
      exact add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal hmean) _) hbad
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hn₀.le (Real.log_nonneg hn₁)),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      have hquot : (n : ℝ) / Real.sqrt n = Real.sqrt n :=
        (div_eq_iff hs.ne').mpr (by simpa only [pow_two] using hsq.symm)
      calc
        _ = c * ((n : ℝ) / Real.sqrt n) * Real.log n + (n : ℝ) ^ (-3 : ℝ) := by ring
        _ = _ := by rw [hquot]

/-- A matching with exactly two exposed cycles has at most two ordered marks. -/
theorem card_markedTwoForwardExposedWindow_le (p : Profile n) (b A : ℝ) :
    Nat.card (MarkedTwoForwardExposedWindow p b A) ≤
      2 * Nat.card {μ : Matching n // IsStable p μ ∧ HasTwoForwardExposedWindow p μ b A} := by
  classical
  let T := {μ : Matching n // IsStable p μ ∧ HasTwoForwardExposedWindow p μ b A}
  let base (z : MarkedTwoForwardExposedWindow p b A) : T :=
    ⟨z.val.1, z.property.1, z.val.2.1, z.val.2.2, z.property.2⟩
  let first (μ : T) := Classical.choose μ.property.2
  let second (μ : T) := Classical.choose (Classical.choose_spec μ.property.2)
  have htwo (μ : T) : HasExactlyTwoForwardExposedRotations p μ.val (first μ) (second μ) :=
    (Classical.choose_spec (Classical.choose_spec μ.property.2)).1
  let f (z : MarkedTwoForwardExposedWindow p b A) : T × Bool :=
    (base z, decide (z.val.2.1 = first (base z)))
  have hfi : Function.Injective f := by
    intro z w h
    have hm : base z = base w := congrArg Prod.fst h
    have hv : z.val.1 = w.val.1 := congrArg Subtype.val hm
    have hf : decide (z.val.2.1 = first (base z)) = decide (w.val.2.1 = first (base w)) :=
      congrArg Prod.snd h
    rw [← hm] at hf
    have he := decide_eq_decide.mp hf
    have hz := (htwo (base z)).2.2.2 _ z.property.2.1.2.1
    have hw := (htwo (base z)).2.2.2 _ (hv ▸ w.property.2.1.2.1)
    have h₁ : z.val.2.1 = w.val.2.1 := by
      by_cases hz' : z.val.2.1 = first (base z)
      · exact hz'.trans (he.mp hz').symm
      · exact (hz.resolve_left hz').trans (hw.resolve_left (fun h ↦ hz' (he.mpr h))).symm
    have h₂ : z.val.2.2 = w.val.2.2 := by
      have hw' := z.property.2.1.2.2.2 _ (hv ▸ w.property.2.1.2.2.1)
      exact (hw'.resolve_left (fun h ↦ w.property.2.1.1 (h₁.symm.trans h.symm))).symm
    exact Subtype.ext (Prod.ext hv (Prod.ext h₁ h₂))
  calc
    _ ≤ Nat.card (T × Bool) := Nat.card_le_card_of_injective f hfi
    _ = 2 * Nat.card T := by rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool)]; simp [mul_comm]

/-- The actual bare ordered count is bounded by twice the number of stable
marks carrying two exposed window cycles. -/
theorem card_incomparableEligibleAnchorMarks_le_sum {x : ScoreProfile n}
    (ht : ∀ row, Function.Injective (x row)) (b A B : ℝ) :
    (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞) ≤
      2 * ∑ μ : Matching n, (scoreStableTwoForwardWindowEvent μ b A).indicator (fun _ ↦ 1) x := by
  classical
  let P (μ : Matching n) :=
    IsStable (profileOfScores x) μ ∧ HasTwoForwardExposedWindow (profileOfScores x) μ b A
  have hcard : (Nat.card {μ // P μ} : ℝ≥0∞) =
      ∑ μ : Matching n, (scoreStableTwoForwardWindowEvent μ b A).indicator (fun _ ↦ 1) x := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype P, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    have he : P μ ↔ x ∈ scoreStableTwoForwardWindowEvent μ b A :=
      and_congr_left' (isStable_profileOfScores_iff ht μ)
    by_cases h : P μ
    · rw [ite_eq_left h, indicator_of_mem (he.mp h), Nat.cast_one]
    · rw [ite_eq_right h, indicator_of_notMem (he.not.mp h)]
  rw [← hcard, ← Nat.cast_ofNat (R := ℝ≥0∞) (n := 2), ← Nat.cast_mul]
  exact_mod_cast (card_incomparableEligibleAnchorMarks_le ht b A B).trans
    (card_markedTwoForwardExposedWindow_le (profileOfScores x) b A)

/-- In the original continuous score law the expected bare ordered
incomparable eligible count is O(√n log n). The local eligibility tests
remain part of the counted event. -/
theorem eventually_lintegral_card_incomparableEligibleAnchorMarks_le {b A : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, ∀ B : ℝ,
      (∫⁻ x, (Nat.card (IncomparableEligibleAnchorMarks b A B x) : ℝ≥0∞)
        ∂continuousScoreLaw n) ≤
        2 * ENNReal.ofReal (twoForwardWindowConstant b A * Real.sqrt n * Real.log n +
          (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_sum_measure_scoreStableTwoForwardWindowEvent_le hb hA] with n h
  intro B
  let q (μ : Matching n) := (scoreStableTwoForwardWindowEvent μ b A).indicator
    (fun _ ↦ (1 : ℝ≥0∞))
  have hq (μ : Matching n) : Measurable (q μ) :=
    measurable_const.indicator (measurableSet_scoreStableTwoForwardWindowEvent μ b A)
  calc
    _ ≤ ∫⁻ x, 2 * ∑ μ : Matching n, q μ x ∂continuousScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_injective_rows n] with x hx
      exact card_incomparableEligibleAnchorMarks_le_sum hx b A B
    _ = 2 * ∑ μ : Matching n, continuousScoreLaw n (scoreStableTwoForwardWindowEvent μ b A) := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun μ _ ↦ hq μ),
        lintegral_finsetSum _ (fun μ _ ↦ hq μ)]
      congr 1
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      exact (lintegral_indicator_const
        (measurableSet_scoreStableTwoForwardWindowEvent μ b A) (1 : ℝ≥0∞)).trans (one_mul _)
    _ ≤ _ := mul_le_mul_right h _

end LennonPittelFormalization

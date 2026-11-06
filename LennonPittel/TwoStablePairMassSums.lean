module

public import LennonPittel.PivotIncomparableScoreCount
public import LennonPittel.TwoStableOrientationCounting
public import LennonPittel.TwoStablePairSizeSums

/-!
# Partition the ordered stable-pair mass by orientation

For a fixed ordered matching pair, the two orientation sets are determined
by the score profile. Their fibers give disjoint events. We may retain any
cycle-type test that holds on the event, and then use the cardinality of
the corresponding labeled orientations without overcounting.
-/

@[expose] public section

open Filter Finset MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {n : ℕ}

/-- A fixed ordered pair of matchings and two fixed ordered support sets. -/
abbrev LabeledMatchingOrientation (n : ℕ) :=
  (Matching n × Matching n) × (Finset (Fin n) × Finset (Fin n))

/-- The two sets of men who receive a worse partner at the first and second
matching, respectively. -/
noncomputable def scorePairOrientationSides (x : ScoreProfile n) (μ ν : Matching n) :
    Finset (Fin n) × Finset (Fin n) :=
  (worsePartnerMen (profileOfScores x) μ ν, worsePartnerMen (profileOfScores x) ν μ)

/-- The sizes of the two orientation sets, in the same order. -/
noncomputable def scorePairOrientationSizes (x : ScoreProfile n) (μ ν : Matching n) : ℕ × ℕ :=
  ((scorePairOrientationSides x μ ν).1.card, (scorePairOrientationSides x μ ν).2.card)

theorem measurableSet_scorePairOrientationSides_eq (μ ν : Matching n)
    (uv : Finset (Fin n) × Finset (Fin n)) :
    MeasurableSet {x : ScoreProfile n | scorePairOrientationSides x μ ν = uv} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | (worsePartnerMen p μ ν, worsePartnerMen p ν μ) = uv})

theorem measurable_scorePairOrientationSizes (μ ν : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ scorePairOrientationSizes x μ ν) :=
  (Measurable.of_discrete (f := fun p : Profile n ↦
    ((worsePartnerMen p μ ν).card, (worsePartnerMen p ν μ).card))).comp
      (measurable_profileOfScores n)

/-- The fixed-pair score event restricted to one labeled support choice. -/
def scoreFixedOrientationPairEvent (R : ScoreProfile n → Matching n → Matching n → Prop)
    (z : LabeledMatchingOrientation n) : Set (ScoreProfile n) :=
  scoreIncomparablePairEvent R z.1.1 z.1.2 ∩
    {x | scorePairOrientationSides x z.1.1 z.1.2 = z.2}

theorem measurableSet_scoreFixedOrientationPairEvent
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (z : LabeledMatchingOrientation n) :
    MeasurableSet (scoreFixedOrientationPairEvent R z) :=
  (measurableSet_scoreIncomparablePairEvent hR z.1.1 z.1.2).inter
    (measurableSet_scorePairOrientationSides_eq z.1.1 z.1.2 z.2)

theorem scoreFixedOrientationPairEvent_data
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    {z : LabeledMatchingOrientation n} {x : ScoreProfile n}
    (hx : x ∈ scoreFixedOrientationPairEvent R z) :
    IsScoreStable x z.1.1 ∧ IsScoreStable x z.1.2 ∧
      z.2.1 = worsePartnerMen (profileOfScores x) z.1.1 z.1.2 ∧
      z.2.2 = worsePartnerMen (profileOfScores x) z.1.2 z.1.1 := by
  have he : scorePairOrientationSides x z.1.1 z.1.2 = z.2 := hx.2
  exact ⟨hx.1.1, hx.1.2.1, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- The total mass of the qualifying ordered stable pairs in one size bin. -/
noncomputable def scorePairSizeMass (R : ScoreProfile n → Matching n → Matching n → Prop)
    (s : ℕ × ℕ) : ℝ≥0∞ :=
  ∑ μ : Matching n, ∑ ν : Matching n, continuousScoreLaw n
    (scoreIncomparablePairEvent R μ ν ∩ {x | scorePairOrientationSizes x μ ν = s})

theorem scorePairSizeMass_ne_top (R : ScoreProfile n → Matching n → Matching n → Prop)
    (s : ℕ × ℕ) : scorePairSizeMass R s ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _

private theorem measure_eq_sum_inter_fibers {Ω α : Type*} [MeasurableSpace Ω]
    {m : Measure Ω} {E : Set Ω} {f : Ω → α}
    (hE : MeasurableSet E) (hf : ∀ a, MeasurableSet {x | f x = a}) (s : Finset α)
    (hc : ∀ᵐ x ∂m, x ∈ E → f x ∈ s) :
    m E = ∑ a ∈ s, m (E ∩ {x | f x = a}) := by
  have hu : E =ᵐ[m] ⋃ a ∈ s, E ∩ {x | f x = a} := by
    filter_upwards [hc] with x hx
    apply propext
    change x ∈ E ↔ x ∈ ⋃ a ∈ s, E ∩ {x | f x = a}
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨f x, hx h, h, rfl⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
  rw [measure_congr hu]
  refine measure_biUnion_finset (fun a _ b _ hab ↦ Set.disjoint_left.mpr ?_) fun a _ ↦
    hE.inter (hf a)
  exact fun _ ha hb ↦ hab (ha.2.symm.trans hb.2)

private noncomputable def orientationSupportsOfSizes (n : ℕ) (s : ℕ × ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) := by
  classical
  exact univ.filter fun uv ↦ (uv.1.card, uv.2.card) = s

private noncomputable def fixedOrientationSizeMarks (n : ℕ) (s : ℕ × ℕ) :
    Finset (LabeledMatchingOrientation n) :=
  (univ : Finset (Matching n × Matching n)).product (orientationSupportsOfSizes n s)

private theorem mem_fixedOrientationSizeMarks {z : LabeledMatchingOrientation n} {s : ℕ × ℕ} :
    z ∈ fixedOrientationSizeMarks n s ↔ (z.2.1.card, z.2.2.card) = s := by
  classical
  simp [fixedOrientationSizeMarks, orientationSupportsOfSizes, product_eq_sprod]

private theorem scorePairSizeMass_eq_sum_fixedMarks
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) :
    scorePairSizeMass R s =
      ∑ z ∈ fixedOrientationSizeMarks n s, continuousScoreLaw n
        (scoreFixedOrientationPairEvent R z) := by
  classical
  unfold scorePairSizeMass fixedOrientationSizeMarks
  rw [product_eq_sprod, sum_product, Fintype.sum_prod_type]
  refine sum_congr rfl fun μ _ ↦ sum_congr rfl fun ν _ ↦ ?_
  let E := scoreIncomparablePairEvent R μ ν
  let G := {x | scorePairOrientationSizes x μ ν = s}
  let f (x : ScoreProfile n) := scorePairOrientationSides x μ ν
  have hmG : MeasurableSet G :=
    (measurable_scorePairOrientationSizes μ ν) (measurableSet_singleton s)
  have hc : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E ∩ G → f x ∈ orientationSupportsOfSizes n s :=
    Eventually.of_forall fun x hx ↦ mem_filter.mpr ⟨mem_univ _, hx.2⟩
  rw [measure_eq_sum_inter_fibers ((measurableSet_scoreIncomparablePairEvent hR μ ν).inter hmG)
    (measurableSet_scorePairOrientationSides_eq μ ν) _ hc]
  refine sum_congr rfl fun uv huv ↦ congrArg (continuousScoreLaw n) ?_
  have hsize := (mem_filter.mp huv).2
  ext x
  change (x ∈ E ∧ x ∈ G) ∧ f x = uv ↔ x ∈ E ∧ f x = uv
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ?_⟩, h.2⟩⟩
  exact (congrArg (fun uv : Finset (Fin n) × Finset (Fin n) ↦ (uv.1.card, uv.2.card))
    h.2).trans hsize

/-- On the fixed-orientation score event, the supplied supports are a valid
labeled cycle partition, outside the null set of tied rows. -/
theorem ae_scoreFixedOrientationPairEvent_labeled
    (R : ScoreProfile n → Matching n → Matching n → Prop) (z : LabeledMatchingOrientation n) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
      LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2 := by
  filter_upwards [ae_injective_rows n] with x ht hx
  have hs : IsStable (profileOfScores x) z.1.1 :=
    (isStable_profileOfScores_iff ht _).mpr hx.1.1
  have hs' : IsStable (profileOfScores x) z.1.2 :=
    (isStable_profileOfScores_iff ht _).mpr hx.1.2.1
  have h := labeledPairOrientation_of_stable hs hs'
  have he : scorePairOrientationSides x z.1.1 z.1.2 = z.2 := hx.2
  change LabeledPairOrientation z.1.1 z.1.2
    (scorePairOrientationSides x z.1.1 z.1.2).1 (scorePairOrientationSides x z.1.1 z.1.2).2 at h
  rwa [he] at h

/-- The finite set of fixed labeled pairs in a bin, retaining both cycle-type tests. -/
noncomputable def labeledOrientationBin (n : ℕ) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop) :
    Finset (LabeledMatchingOrientation n) := by
  classical
  exact univ.filter fun z ↦
    ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
      z.2.1.card = s.1 ∧ z.2.2.card = s.2 ∧ P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType

theorem mem_labeledOrientationBin {s : ℕ × ℕ} {P T : Multiset ℕ → Prop}
    {z : LabeledMatchingOrientation n} :
    z ∈ labeledOrientationBin n s P T ↔
      ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
        z.2.1.card = s.1 ∧ z.2.2.card = s.2 ∧ P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType := by
  classical
  simp [labeledOrientationBin]

theorem card_labeledOrientationBin (n : ℕ) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop) :
    (labeledOrientationBin n s P T).card = Nat.card (LabeledOrientationPairs n s.1 s.2 P T) := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_labeledOrientationBin)

/-- Partition a size bin exactly by the fixed supports. A cycle-type test may
be retained on either side if it holds almost everywhere on its labeled event. -/
theorem scorePairSizeMass_eq_sum_labeled
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop)
    (hcycle : ∀ (z : LabeledMatchingOrientation n)
      (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2),
      ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
        P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType) :
    scorePairSizeMass R s = ∑ z ∈ labeledOrientationBin n s P T,
      continuousScoreLaw n (scoreFixedOrientationPairEvent R z) := by
  rw [scorePairSizeMass_eq_sum_fixedMarks hR]
  symm
  refine sum_subset (fun z hz ↦ ?_) fun z hz hnot ↦ ?_
  · obtain ⟨_, hu, hv, _, _⟩ := mem_labeledOrientationBin.mp hz
    exact mem_fixedOrientationSizeMarks.mpr (Prod.ext hu hv)
  have hsize := mem_fixedOrientationSizeMarks.mp hz
  rw [measure_eq_zero_iff_ae_notMem]
  by_cases h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2
  · filter_upwards [hcycle z h] with x hx he
    exact hnot (mem_labeledOrientationBin.mpr
      ⟨h, congrArg Prod.fst hsize, congrArg Prod.snd hsize, hx he⟩)
  · filter_upwards [ae_scoreFixedOrientationPairEvent_labeled R z] with x hx he
    exact h (hx he)

/-- A uniform bound on a fixed labeled event converts to a size-bin bound
with the exact cardinality of the cycle-restricted labeling type. -/
theorem scorePairSizeMass_le_card_mul
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (s : ℕ × ℕ) (P T : Multiset ℕ → Prop)
    (hcycle : ∀ (z : LabeledMatchingOrientation n)
      (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2),
      ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
        P h.leftPerm.cycleType ∧ T h.rightPerm.cycleType)
    {U : ℝ≥0∞}
    (hU : ∀ z : LabeledOrientationPairs n s.1 s.2 P T,
      continuousScoreLaw n (scoreFixedOrientationPairEvent R z.val) ≤ U) :
    scorePairSizeMass R s ≤ (Nat.card (LabeledOrientationPairs n s.1 s.2 P T) : ℝ≥0∞) * U := by
  rw [scorePairSizeMass_eq_sum_labeled hR s P T hcycle]
  calc
    _ ≤ ∑ _z ∈ labeledOrientationBin n s P T, U :=
      sum_le_sum fun z hz ↦ hU ⟨z, mem_labeledOrientationBin.mp hz⟩
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_labeledOrientationBin]

/-- The forced-cycle exception on score outcomes is exactly a cycle-type
restriction on each fixed labeled event. -/
theorem forcedCycleTypeCoverage_of_scoreForcedException
    {R : ScoreProfile n → Matching n → Matching n → Prop} (L : ℕ)
    (hrare : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν →
        ((forcedShortCycles (profileOfScores x) μ ν L).card : ℝ) <
          (9 / 10 : ℝ) * Real.log (L : ℝ))
    (z : LabeledMatchingOrientation n) (h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreFixedOrientationPairEvent R z →
      forcedShortCycleTypeException L h.leftPerm.cycleType ∧ True := by
  rcases z with ⟨⟨μ, ν⟩, U, V⟩
  filter_upwards [hrare μ ν] with x hx he
  obtain ⟨_, _, hU, hV⟩ := scoreFixedOrientationPairEvent_data he
  change U = worsePartnerMen (profileOfScores x) μ ν at hU
  change V = worsePartnerMen (profileOfScores x) ν μ at hV
  subst U V
  exact ⟨(forcedShortCycleTypeException_leftPerm_iff L h).mpr (hx he.1), trivial⟩

/-- A cover by two score exceptions bounds the size-bin mass by the sum of
their masses; no independence between the exceptions is required. -/
theorem scorePairSizeMass_le_add
    {R R₁ R₂ : ScoreProfile n → Matching n → Matching n → Prop} (s : ℕ × ℕ)
    (hcover : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν = s →
        R₁ x μ ν ∨ R₂ x μ ν) :
    scorePairSizeMass R s ≤ scorePairSizeMass R₁ s + scorePairSizeMass R₂ s := by
  unfold scorePairSizeMass
  rw [← sum_add_distrib]
  refine sum_le_sum fun μ _ ↦ ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun ν _ ↦ ?_
  refine le_trans (measure_mono_ae ?_) (measure_union_le _ _)
  filter_upwards [hcover μ ν] with x hx he
  obtain ⟨he, hs⟩ := he
  rcases hx he hs with h | h
  · exact Or.inl ⟨⟨he.1, he.2.1, he.2.2.1, h⟩, hs⟩
  · exact Or.inr ⟨⟨he.1, he.2.1, he.2.2.1, h⟩, hs⟩

theorem scorePairSizeMass_toReal_le_add
    {R R₁ R₂ : ScoreProfile n → Matching n → Matching n → Prop} (s : ℕ × ℕ)
    (hcover : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν = s →
        R₁ x μ ν ∨ R₂ x μ ν) :
    (scorePairSizeMass R s).toReal ≤ (scorePairSizeMass R₁ s).toReal +
      (scorePairSizeMass R₂ s).toReal := by
  rw [← ENNReal.toReal_add (scorePairSizeMass_ne_top R₁ s) (scorePairSizeMass_ne_top R₂ s)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨scorePairSizeMass_ne_top R₁ s, scorePairSizeMass_ne_top R₂ s⟩)
    (scorePairSizeMass_le_add s hcover)

/-- A finite carrier for all valid ordered orientation sizes. -/
noncomputable def validPairSizeFinset (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((range (n + 1)).product (range (n + 1))).filter (ValidPairSizes n)

@[simp]
theorem mem_validPairSizeFinset {s : ℕ × ℕ} :
    s ∈ validPairSizeFinset n ↔ ValidPairSizes n s := by
  classical
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    have hs := h.2.2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
      mem_range.mpr (by omega)⟩, h⟩

private theorem two_le_finsetCard_of_fixedPointFree {α : Type*} {s : Finset α}
    (hs : s.Nonempty) (f : Equiv.Perm s) (hf : ∀ i, f i ≠ i) : 2 ≤ s.card := by
  obtain ⟨i, hi⟩ := hs
  exact one_lt_card.mpr ⟨(f ⟨i, hi⟩).val, (f ⟨i, hi⟩).property, i, hi,
    fun h ↦ hf _ (Subtype.ext h)⟩

private theorem worsePartnerMen_nonempty_of_not_menWeaklyPrefer {p : Profile n} {μ ν : Matching n}
    (h : ¬ MenWeaklyPrefer p μ ν) : (worsePartnerMen p μ ν).Nonempty := by
  by_contra h0
  apply h
  intro m
  exact le_of_not_gt fun hm ↦ h0 ⟨m, mem_filter.mpr ⟨mem_univ _, hm⟩⟩

/-- Each nonempty side of a labeled orientation has at least two men,
and together the sides use at most all labels. -/
theorem LabeledPairOrientation.validPairSizes_of_nonempty {μ ν : Matching n}
    {U V : Finset (Fin n)} (h : LabeledPairOrientation μ ν U V)
    (hU : U.Nonempty) (hV : V.Nonempty) : ValidPairSizes n (U.card, V.card) := by
  refine ⟨two_le_finsetCard_of_fixedPointFree hU h.leftPerm h.leftPerm_apply_ne,
    two_le_finsetCard_of_fixedPointFree hV h.rightPerm h.rightPerm_apply_ne, ?_⟩
  rw [← card_union_of_disjoint h.disjoint, h.union_support]
  exact (card_le_univ _).trans_eq (Fintype.card_fin n)

theorem ae_validPairSizes_of_scoreIncomparablePairEvent
    (R : ScoreProfile n → Matching n → Matching n → Prop) (μ ν : Matching n) :
    ∀ᵐ x ∂continuousScoreLaw n, x ∈ scoreIncomparablePairEvent R μ ν →
      ValidPairSizes n (scorePairOrientationSizes x μ ν) := by
  filter_upwards [ae_injective_rows n] with x ht hx
  have h := labeledPairOrientation_of_stable
    ((isStable_profileOfScores_iff ht μ).mpr hx.1)
    ((isStable_profileOfScores_iff ht ν).mpr hx.2.1)
  exact h.validPairSizes_of_nonempty
    (worsePartnerMen_nonempty_of_not_menWeaklyPrefer hx.2.2.1.1)
    (worsePartnerMen_nonempty_of_not_menWeaklyPrefer hx.2.2.1.2)

/-- Sum a qualifying fixed-pair mass over any finite set of size bins
which almost surely contains every qualifying outcome. -/
theorem scorePairMass_eq_sum_sizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (S : Finset (ℕ × ℕ))
    (hS : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν ∈ S) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      continuousScoreLaw n (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ S, scorePairSizeMass R s := by
  let g (μ ν : Matching n) (s : ℕ × ℕ) :=
    continuousScoreLaw n (scoreIncomparablePairEvent R μ ν ∩
      {x | scorePairOrientationSizes x μ ν = s})
  calc
    _ = ∑ μ : Matching n, ∑ ν : Matching n, ∑ s ∈ S, g μ ν s := by
      refine sum_congr rfl fun μ _ ↦ sum_congr rfl fun ν _ ↦ ?_
      exact measure_eq_sum_inter_fibers (measurableSet_scoreIncomparablePairEvent hR μ ν)
        (fun s ↦ (measurable_scorePairOrientationSizes μ ν) (measurableSet_singleton s))
        S (hS μ ν)
    _ = ∑ μ : Matching n, ∑ s ∈ S, ∑ ν : Matching n, g μ ν s :=
      sum_congr rfl fun _ _ ↦ sum_comm
    _ = _ := sum_comm

theorem scorePairMass_eq_sum_validPairSizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      continuousScoreLaw n (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ validPairSizeFinset n, scorePairSizeMass R s :=
  scorePairMass_eq_sum_sizeMass hR _ fun μ ν ↦
    (ae_validPairSizes_of_scoreIncomparablePairEvent R μ ν).mono fun _ hx he ↦
      mem_validPairSizeFinset.mpr (hx he)

/-- The same partition for real-valued probabilities, as used by the
centered Bochner second moment. -/
theorem scorePairMass_real_eq_sum_sizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) (S : Finset (ℕ × ℕ))
    (hS : ∀ μ ν : Matching n, ∀ᵐ x ∂continuousScoreLaw n,
      x ∈ scoreIncomparablePairEvent R μ ν → scorePairOrientationSizes x μ ν ∈ S) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ S, (scorePairSizeMass R s).toReal := by
  have h := congrArg ENNReal.toReal (scorePairMass_eq_sum_sizeMass hR S hS)
  rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _),
    ENNReal.toReal_sum (fun s _ ↦ scorePairSizeMass_ne_top R s)] at h
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)] at h
  exact h

theorem scorePairMass_real_eq_sum_validPairSizeMass
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent R μ ν)) =
        ∑ s ∈ validPairSizeFinset n, (scorePairSizeMass R s).toReal :=
  scorePairMass_real_eq_sum_sizeMass hR _ fun μ ν ↦
    (ae_validPairSizes_of_scoreIncomparablePairEvent R μ ν).mono fun _ hx he ↦
      mem_validPairSizeFinset.mpr (hx he)

end LennonPittelFormalization

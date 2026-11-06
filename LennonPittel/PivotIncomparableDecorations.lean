module

public import LennonPittel.PivotResidualImageGeometry
public import LennonPittel.PivotIncomparableScoreCount

/-!
# Both orientations of a decorated incomparable pair are long

A long pivot at one endpoint is present in the other endpoint's eliminated ideal:
it belongs to the other singleton anchor and is too long for the other decoration
to remove. Every man on that pivot therefore has a strictly worse partner at the
other endpoint. This counts the two orientations without choosing an elimination
path between the matchings.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ A B : Matching n} {hopt : IsManOptimal p μ₀}
  {K : ℕ} {r s : Rotation p μ₀}

/-- A long label in the singleton anchor survives a decoration. -/
theorem PivotDecoration.mem_matching_eliminated_of_long
    (D : PivotDecoration hopt K r) (hs : K < rotationLength s) (hrs : ¬ r ≤ s) :
    s ∈ eliminatedRotations p μ₀ D.matching.val := by
  rw [D.matching_eliminated, eliminatedRotations_singletonRotationAnchor]
  refine ⟨hrs, ?_⟩
  rintro ⟨t, ht, rfl⟩
  have hlen := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (show t ∈ D.removed from ht)).trans D.totalLength_le
  exact (not_lt_of_ge hlen) hs

/-- Moving a man by an exposed rotation crosses a rank threshold. Any stable
endpoint which has already eliminated that label gives him a worse partner. -/
theorem Rotation.IsExposedAt.support_subset_worsePartnerMen_of_eliminated
    (hopt : IsManOptimal p μ₀) (hex : r.IsExposedAt A) (hB : IsStable p B)
    (hmem : r ∈ eliminatedRotations p μ₀ B) :
    r.val.cycle.support ⊆ worsePartnerMen p B A := by
  intro m hm
  have hmove := Equiv.Perm.mem_support.mp hm
  have hnew := rotationLabelNewPartner_eq (μ := A) hmove
  rw [hex.2] at hnew
  have hle := (mem_eliminatedRotations_iff_newRank_le hopt hB hmove hnew).mp hmem
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (hex.1.manRank_lt_eliminate_of_moved hmove).trans_le hle⟩

/-- Each orientation contains the men moved by the opposite endpoint's long pivot. -/
theorem PivotDecoration.supports_subset_worsePartnerMen_of_incomparable
    (D : PivotDecoration hopt K r) (E : PivotDecoration hopt K s)
    (hr : K < rotationLength r) (hs : K < rotationLength s)
    (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    r.val.cycle.support ⊆ worsePartnerMen p E.matching.val D.matching.val ∧
      s.val.cycle.support ⊆ worsePartnerMen p D.matching.val E.matching.val :=
  ⟨D.pivot_exposed.support_subset_worsePartnerMen_of_eliminated hopt E.matching.property
      (E.mem_matching_eliminated_of_long hr hsr),
    E.pivot_exposed.support_subset_worsePartnerMen_of_eliminated hopt D.matching.property
      (D.mem_matching_eliminated_of_long hs hrs)⟩

/-- Neither decorated endpoint precedes the other in men's weak preference order. -/
theorem PivotDecoration.incomparable_of_incomparable_pivots
    (D : PivotDecoration hopt K r) (E : PivotDecoration hopt K s)
    (hr : K < rotationLength r) (hs : K < rotationLength s)
    (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    (¬ MenWeaklyPrefer p D.matching.val E.matching.val) ∧
      (¬ MenWeaklyPrefer p E.matching.val D.matching.val) := by
  obtain ⟨hrsub, hssub⟩ := D.supports_subset_worsePartnerMen_of_incomparable E hr hs hrs hsr
  obtain ⟨m, hm⟩ := Finset.card_pos.mp ((Nat.zero_le K).trans_lt hr)
  obtain ⟨m', hm'⟩ := Finset.card_pos.mp ((Nat.zero_le K).trans_lt hs)
  exact ⟨fun h ↦ (Finset.mem_filter.mp (hssub hm')).2.not_ge (h m'),
    fun h ↦ (Finset.mem_filter.mp (hrsub hm)).2.not_ge (h m)⟩

/-- Both orientation cardinalities are at least their respective pivot lengths. -/
theorem PivotDecoration.rotationLength_le_card_worsePartnerMen_of_incomparable
    (D : PivotDecoration hopt K r) (E : PivotDecoration hopt K s)
    (hr : K < rotationLength r) (hs : K < rotationLength s)
    (hrs : ¬ r ≤ s) (hsr : ¬ s ≤ r) :
    rotationLength r ≤ (worsePartnerMen p E.matching.val D.matching.val).card ∧
      rotationLength s ≤ (worsePartnerMen p D.matching.val E.matching.val).card := by
  obtain ⟨hrsub, hssub⟩ := D.supports_subset_worsePartnerMen_of_incomparable E hr hs hrs hsr
  exact ⟨Finset.card_le_card hrsub, Finset.card_le_card hssub⟩

/-- Both orientations of the pair move at least the required number of men. -/
def ScoreTwoLongOrientations (b : ℝ) (x : ScoreProfile n) (μ ν : Matching n) : Prop :=
  b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen (profileOfScores x) μ ν).card : ℝ) ∧
    b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen (profileOfScores x) ν μ).card : ℝ)

theorem measurableSet_scoreTwoLongOrientations (b : ℝ) (μ ν : Matching n) :
    MeasurableSet {x | ScoreTwoLongOrientations b x μ ν} :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n |
      b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p μ ν).card : ℝ) ∧
        b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p ν μ).card : ℝ)})

namespace LongMarkedChoice

variable {x : ScoreProfile n} {L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}
  (a d : LongMarkedChoice x K L flag t) (hopt : IsManOptimal (profileOfScores x) μ₀)

private noncomputable def asDecoration : PivotDecoration hopt K (a.pivot hopt).val :=
  (markedFilteredChoicesEmbedding hopt (a.pivot hopt).val (a.pivot_anchor hopt)
    (a.pivot_cycle hopt) a.cutoff_nonneg ⟨a.reverse, a.mem_choices⟩).val

private theorem asDecoration_matching :
    (a.asDecoration hopt).matching.val = undoReverseRotation a.anchor a.reverse :=
  markedFilteredChoicesEmbedding_matching (a.pivot hopt).val (a.pivot_anchor hopt)
    (a.pivot_cycle hopt) a.cutoff_nonneg ⟨a.reverse, a.mem_choices⟩

/-- Incomparable marked anchors generate incomparable endpoints with both
orientation sizes at least the local length cutoff. -/
theorem incomparableEndpoints_of_incomparableAnchors {b : ℝ}
    (hoptimal : IsManOptimal (profileOfScores x) μ₀)
    (hinc : IncomparableAnchors (profileOfScores x) a.anchor d.anchor)
    (ha : b * Real.sqrt (n : ℝ) ≤ (a.cycle.support.card : ℝ))
    (hd : b * Real.sqrt (n : ℝ) ≤ (d.cycle.support.card : ℝ)) :
    IncomparableAnchors (profileOfScores x) (undoReverseRotation a.anchor a.reverse)
      (undoReverseRotation d.anchor d.reverse) ∧
    ScoreTwoLongOrientations b x (undoReverseRotation a.anchor a.reverse)
      (undoReverseRotation d.anchor d.reverse) := by
  let r := (a.pivot hoptimal).val
  let s := (d.pivot hoptimal).val
  have hle : MenWeaklyPrefer (profileOfScores x) a.anchor d.anchor ↔ r ≤ s := by
    rw [← a.pivot_anchor hoptimal, ← d.pivot_anchor hoptimal]
    exact menWeaklyPrefer_singletonRotationAnchor_iff hoptimal r s
  have hge : MenWeaklyPrefer (profileOfScores x) d.anchor a.anchor ↔ s ≤ r := by
    rw [← d.pivot_anchor hoptimal, ← a.pivot_anchor hoptimal]
    exact menWeaklyPrefer_singletonRotationAnchor_iff hoptimal s r
  have hrs : ¬ r ≤ s := fun h ↦ hinc.1 (hle.mpr h)
  have hsr : ¬ s ≤ r := fun h ↦ hinc.2 (hge.mpr h)
  rw [← a.asDecoration_matching hoptimal, ← d.asDecoration_matching hoptimal]
  have hl := (a.asDecoration hoptimal).rotationLength_le_card_worsePartnerMen_of_incomparable
    (d.asDecoration hoptimal) (a.pivot hoptimal).property (d.pivot hoptimal).property hrs hsr
  have hra : b * Real.sqrt (n : ℝ) ≤ (rotationLength r : ℝ) := by
    simpa only [r, rotationLength, a.pivot_cycle hoptimal] using ha
  have hsd : b * Real.sqrt (n : ℝ) ≤ (rotationLength s : ℝ) := by
    simpa only [s, rotationLength, d.pivot_cycle hoptimal] using hd
  exact ⟨(a.asDecoration hoptimal).incomparable_of_incomparable_pivots
      (d.asDecoration hoptimal) (a.pivot hoptimal).property (d.pivot hoptimal).property hrs hsr,
    hsd.trans (Nat.cast_le.mpr hl.2), hra.trans (Nat.cast_le.mpr hl.1)⟩

end LongMarkedChoice

namespace PivotCountParameters

private noncomputable def incomparableChoicePairs (q : PivotCountParameters) (x : ScoreProfile n) :
    Finset (Σ _ : PivotMark n × PivotMark n, Matching n × Matching n) := by
  classical
  exact Finset.univ.sigma fun ij ↦
    if IncomparableAnchors (profileOfScores x) ij.1.1 ij.2.1 then
      (q.eligibleChoices x ij.1).product (q.eligibleChoices x ij.2)
    else ∅

private theorem card_incomparableChoicePairs (q : PivotCountParameters) (x : ScoreProfile n) :
    ((q.incomparableChoicePairs x).card : ℝ) =
      ∑ i : PivotMark n, ∑ j : PivotMark n,
        {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
          (q.count i * q.count j) x := by
  classical
  rw [incomparableChoicePairs, Finset.card_sigma, Nat.cast_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : IncomparableAnchors (profileOfScores x) i.1 j.1 <;>
    simp [h, Pi.mul_apply, q.count_eq_card_eligibleChoices,
      Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]

private theorem incomparableChoicePairs_data (q : PivotCountParameters) (x : ScoreProfile n)
    (a : ↥(q.incomparableChoicePairs x)) :
    IncomparableAnchors (profileOfScores x) a.val.1.1.1 a.val.1.2.1 ∧
      a.val.2.1 ∈ q.eligibleChoices x a.val.1.1 ∧
      a.val.2.2 ∈ q.eligibleChoices x a.val.1.2 := by
  classical
  have hm := (Finset.mem_sigma.mp a.property).2
  split at hm
  · rename_i h
    exact ⟨h, Finset.mem_product.mp hm⟩
  · exact (Finset.notMem_empty _ hm).elim

private noncomputable def longChoiceOfEligible (q : PivotCountParameters) {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row))
    (hlong : ∀ i : PivotMark n,
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.supportCap < i.2.support.card)
    (hcut : ∀ i : PivotMark n, 0 ≤ residualChoiceCutoff x i.1 i.2)
    (i : PivotMark n) (τ : Matching n) (hτ : τ ∈ q.eligibleChoices x i) :
    LongMarkedChoice x q.supportCap q.shortCutoff (residualChoiceFlag x) (residualChoiceCutoff x) :=
  let h := eligibleChoices_data hτ
  ⟨i.1, i.2, τ, (isStable_profileOfScores_iff hties _).mpr h.1, h.2.1.isSoleForwardExposed hties,
    hlong i h.2.1, hcut i, h.2.2⟩

/-- The actual count-count products inject into the ordered stable endpoint
pairs with both orientations long. Each endpoint recovers its original mark
and decoration, so there is no multiplicity factor. -/
theorem incomparableCountProducts_le_scorePairCount (q : PivotCountParameters)
    {x : ScoreProfile n} (hties : ∀ row, Function.Injective (x row))
    (hlong : ∀ i : PivotMark n,
      IsLocallyEligiblePivot q.lowerLength q.upperLength q.geometryBudget x i.1 i.2 →
        q.supportCap < i.2.support.card)
    (hcut : ∀ i : PivotMark n, 0 ≤ residualChoiceCutoff x i.1 i.2) :
    (∑ i : PivotMark n, ∑ j : PivotMark n,
      {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
        (q.count i * q.count j) x) ≤ incomparableScorePairCount
          (ScoreTwoLongOrientations q.lowerLength) x := by
  classical
  rw [← q.card_incomparableChoicePairs x]
  let S := q.incomparableChoicePairs x
  let C := incomparableScorePairs (ScoreTwoLongOrientations q.lowerLength) x
  change (S.card : ℝ) ≤ (C.card : ℝ)
  apply Nat.cast_le.mpr
  by_cases hS : Nonempty ↥S
  · let data (a : ↥S) := q.incomparableChoicePairs_data x a
    let first (a : ↥S) := q.longChoiceOfEligible hties hlong hcut _ _ (data a).2.1
    let second (a : ↥S) := q.longChoiceOfEligible hties hlong hcut _ _ (data a).2.2
    let a₀ := first (Classical.choice hS)
    obtain ⟨m₀, hm₀⟩ := exists_manOptimal_of_exists_stable ⟨a₀.anchor, a₀.stable⟩
    let e (a : ↥S) : ↥C := by
      let A := first a
      let B := second a
      refine ⟨(undoReverseRotation A.anchor A.reverse, undoReverseRotation B.anchor B.reverse),
        mem_incomparableScorePairs.mpr ?_⟩
      exact ⟨(isStable_profileOfScores_iff hties _).mp
          (isStable_undoReverseRotation_of_mem_markedFilteredChoices A.stable A.mem_choices),
        (isStable_profileOfScores_iff hties _).mp
          (isStable_undoReverseRotation_of_mem_markedFilteredChoices B.stable B.mem_choices),
        A.incomparableEndpoints_of_incomparableAnchors B hm₀ (data a).1
          (eligibleChoices_data (data a).2.1).2.1.1.length_lower
          (eligibleChoices_data (data a).2.2).2.1.1.length_lower⟩
    have he : Function.Injective e := by
      intro a a' haa'
      have hpair := congrArg Subtype.val haa'
      have hf : first a = first a' :=
        (first a).eq_of_endpoint_eq hm₀ (congrArg Prod.fst hpair)
      have hs : second a = second a' :=
        (second a).eq_of_endpoint_eq hm₀ (congrArg Prod.snd hpair)
      exact Subtype.ext (Sigma.ext
        (Prod.ext (congrArg (fun c ↦ (c.anchor, c.cycle)) hf)
          (congrArg (fun c ↦ (c.anchor, c.cycle)) hs))
        (heq_of_eq (Prod.ext (congrArg (fun c ↦ c.reverse) hf)
          (congrArg (fun c ↦ c.reverse) hs))))
    simpa only [Nat.card_eq_finsetCard] using Nat.card_le_card_of_injective e he
  · have hz : S.card = 0 := Finset.card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_notMem.mpr fun a ha ↦ hS ⟨⟨a, ha⟩⟩)
    rw [hz]
    exact Nat.zero_le _

/-- The count-count injection applies almost surely in the original score law. -/
theorem ae_incomparableCountProducts_le_scorePairCount (q : PivotCountParameters)
    (hn : 0 < n) {κ : ℝ} (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    ∀ᵐ x ∂continuousScoreLaw n,
      (∑ i : PivotMark n, ∑ j : PivotMark n,
        {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
          (q.count i * q.count j) x) ≤ incomparableScorePairCount
            (ScoreTwoLongOrientations q.lowerLength) x := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x ht hx
  exact q.incomparableCountProducts_le_scorePairCount ht
    (fun _ he ↦ he.supportCap_lt hn hκ hcap)
    (residualChoiceCutoff_nonneg fun r i ↦ (hx r i).1.le)

/-- Integrate the exact count-count upper terms against the original score law,
reducing the estimate to a sum of masses for fixed labeled endpoint pairs. -/
theorem integral_incomparableCountProducts_le_sum (q : PivotCountParameters)
    (hn : 0 < n) {κ : ℝ} (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    (∫ x, (∑ i : PivotMark n, ∑ j : PivotMark n,
      {x | IncomparableAnchors (profileOfScores x) i.1 j.1}.indicator
        (q.count i * q.count j) x) ∂continuousScoreLaw n) ≤
      ∑ μ : Matching n, ∑ ν : Matching n,
        (continuousScoreLaw n).real
          (scoreIncomparablePairEvent (ScoreTwoLongOrientations q.lowerLength) μ ν) := by
  let Q := ScoreTwoLongOrientations (n := n) q.lowerLength
  have hQ (μ ν : Matching n) : MeasurableSet {x | Q x μ ν} :=
    measurableSet_scoreTwoLongOrientations _ _ _
  rw [← integral_incomparableScorePairCount hQ]
  have habs (i : PivotMark n) :
      ∀ᵐ x ∂continuousScoreLaw n, |q.count i x| ≤ (n.factorial : ℝ) :=
    Eventually.of_forall fun x ↦ by
      rw [abs_of_nonneg (q.count_mem_Icc i x).1]
      exact (q.count_mem_Icc i x).2
  refine integral_mono_ae ?_ (integrable_incomparableScorePairCount hQ)
    (q.ae_incomparableCountProducts_le_scorePairCount hn hκ hcap)
  refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
  exact (integrable_mul_of_ae_abs_le_real (q.measurable_count i) (q.measurable_count j)
    (Nat.cast_nonneg _) (habs i) (habs j)).indicator (measurableSet_incomparableAnchors i.1 j.1)

end PivotCountParameters

end LennonPittelFormalization

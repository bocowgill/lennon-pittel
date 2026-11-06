module

public import LennonPittel.PivotReverseFilterMoment
public import LennonPittel.PivotScoreLock
public import LennonPittel.PivotForwardExposureReveal
public import LennonPittel.PivotPairToggle

/-!
# Actual decorations passing the two reverse filters

The finite permutation count lower-bounds the count of stable endpoints whose
removed labels obey the cycle cap and whose scores obey the increment cutoff.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {n : ℕ} {x : ScoreProfile n} {μ₀ : Matching n}
  {hopt : IsManOptimal (profileOfScores x) μ₀} {K : ℕ}
  {r : Rotation (profileOfScores x) μ₀}

open scoped Classical in
/-- The cap on short removed labels and the increment test on the actual endpoint. -/
def PivotDecoration.PassesReverseFilters (D : PivotDecoration hopt K r) (L : ℕ) (t : ℝ) : Prop :=
  ((D.removed.filter (fun s ↦ rotationLength s.val ≤ L)).card : ℝ) ≤
    (3 / 2 : ℝ) * Real.log (L : ℝ) ∧
  ∀ w, femaleSpouseScore x D.matching.val w -
    femaleSpouseScore x (singletonRotationAnchor hopt r).val w ≤ t

/-- Decorations which pass both filters, as a subtype of the stable endpoints. -/
abbrev FilteredPivotDecoration (hopt : IsManOptimal (profileOfScores x) μ₀) (K : ℕ)
    (r : Rotation (profileOfScores x) μ₀) (L : ℕ) (t : ℝ) :=
  {D : PivotDecoration hopt K r // D.PassesReverseFilters L t}

/-- Restoring removed labels preserves both tests on the actual endpoint. -/
theorem PivotDecoration.PassesReverseFilters.of_removed_subset {D E : PivotDecoration hopt K r}
    {L : ℕ} {t : ℝ} (hD : D.PassesReverseFilters L t) (hsub : E.removed ⊆ D.removed)
    (hties : ∀ row, Function.Injective (x row)) : E.PassesReverseFilters L t := by
  classical
  constructor
  · exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hsub))).trans hD.1
  · have hI : eliminatedRotations (profileOfScores x) μ₀ D.matching.val ⊆
        eliminatedRotations (profileOfScores x) μ₀ E.matching.val := by
      rw [PivotDecoration.matching_eliminated, PivotDecoration.matching_eliminated]
      exact fun _ hs ↦ ⟨hs.1, fun he ↦ hs.2 (Set.image_mono hsub he)⟩
    obtain ⟨rs, hpath⟩ := exists_rotationSequence_of_menWeaklyPrefer
      D.matching.property E.matching.property
      ((eliminatedRotations_subset_iff hopt D.matching.property E.matching.property).mp hI)
    intro w
    have hscore : femaleSpouseScore x E.matching.val w ≤ femaleSpouseScore x D.matching.val w :=
      le_of_not_gt fun hw ↦ (not_lt_of_ge (hpath.womanRank_end_le w))
        ((rankPermutation_lt_iff (hties (.inr w)) _ _).mpr hw)
    exact (sub_le_sub_right hscore _).trans (hD.2 w)

/-- The shared-switch toggle stays in the actual filtered family, even when
each pivot has its own score-increment cutoff. -/
theorem ResidualPivotPair.toggledEarly_passesReverseFilters
    (R : ResidualPivotPair hopt K) (L : ℕ)
    (t : LongPivot (profileOfScores x) μ₀ K → ℝ)
    (hties : ∀ row, Function.Injective (x row))
    (h : R.early.2.PassesReverseFilters L (t R.early.1)) :
    R.toggledEarly.2.PassesReverseFilters L (t R.toggledEarly.1) :=
  R.toggledEarly_preserves (fun a D ↦ D.PassesReverseFilters L (t a))
    (fun _ _ _ hsub hD ↦ hD.of_removed_subset hsub hties) h

/-- A compatible permutation that passes the tests produces an actual filtered decoration. -/
theorem compatibleReversePermutationToDecoration_passesReverseFilters
    (σ : CompatibleReversePermutation hopt K r) {L : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcap : ¬ shortCycleCapBad L σ.val.cycleType)
    (hinc : reverseCollectionIncrementGood x (singletonRotationAnchor hopt r).val σ.val t) :
    (compatibleReversePermutationToDecoration hopt K r σ).PassesReverseFilters L t := by
  classical
  let A := singletonRotationAnchor hopt r
  constructor
  · rw [compatibleReversePermutationToDecoration_removed, realizedReverseRemovedLabels_short_card]
    exact not_lt.mp hcap
  · intro w
    rw [compatibleReversePermutationToDecoration_matching]
    change x (.inr w) ((undoReverseRotation A.val σ.val).symm w) -
      x (.inr w) (A.val.symm w) ≤ t
    rw [undoReverseRotation_symm_apply]
    by_cases hw : w ∈ σ.val.support
    · exact hinc w hw
    · rw [Equiv.Perm.notMem_support.mp hw, sub_self]
      exact ht

/-- Each permutation in the fixed-mask count contributes a distinct actual
decoration that satisfies both filters. -/
theorem sum_card_filteredReverseSupportFamily_le_card_filteredPivotDecoration
    (hopt : IsManOptimal (profileOfScores x) μ₀) (r : Rotation (profileOfScores x) μ₀)
    (flag : OffDiagonalCellIndex n → Bool) (K L : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    let μ := (singletonRotationAnchor hopt r).val
    (∑ k ∈ Finset.Icc 2 K,
      (filteredReverseSupportFamily μ r.val.cycle flag k L t x).card) ≤
        Nat.card (FilteredPivotDecoration hopt K r L t) := by
  classical
  intro μ
  let I := Finset.Icc 2 K
  let S k := filteredReverseSupportFamily μ r.val.cycle flag k L t x
  have hmem {k : ℕ} {σ : Matching n} (hs : σ ∈ S k) :
      σ.support.card = k ∧
      (∀ m ∈ r.val.cycle.support, μ m ∉ σ.support) ∧
      RealizesSuccessorPermutation (swapProfile (profileOfScores x)) μ.symm σ ∧
      IsExposedRotation (profileOfScores x) (undoReverseRotation μ σ) r.val.cycle ∧
      ¬ shortCycleCapBad L σ.cycleType ∧ reverseCollectionIncrementGood x μ σ t := by
    obtain ⟨hc, hfilters⟩ := Finset.mem_filter.mp hs
    have hcomp := mem_compatibleReversePermutations.mp hc
    have hgood := mem_goodReverseSupportPermutations.mp hcomp.1
    refine ⟨hgood.1, ?_, hcomp.2.1, hcomp.2.2, hfilters.1, hfilters.2⟩
    exact fun m hm hw ↦ (hgood.2 (μ m) hw).1 (Finset.mem_map.mpr ⟨m, hm, rfl⟩)
  have hdisj : (I : Set ℕ).PairwiseDisjoint S := by
    intro k _ l _ hne
    exact Finset.disjoint_left.mpr fun _ hs hu ↦
      hne ((hmem hs).1.symm.trans (hmem hu).1)
  change (∑ k ∈ I, (S k).card) ≤ _
  rw [← Finset.card_biUnion hdisj, ← Nat.card_eq_finsetCard]
  let f (σ : ↥(I.biUnion S)) : CompatibleReversePermutation hopt K r :=
    ⟨σ.val, by
      obtain ⟨k, hk, hs⟩ := Finset.mem_biUnion.mp σ.property
      have h := hmem hs
      exact ⟨h.2.2.1, h.1.trans_le (Finset.mem_Icc.mp hk).2, h.2.1, h.2.2.2.1⟩⟩
  let e := compatibleReversePermutationEmbedding hopt K r
  let g (σ : ↥(I.biUnion S)) : FilteredPivotDecoration hopt K r L t :=
    ⟨e (f σ), by
      obtain ⟨k, _, hs⟩ := Finset.mem_biUnion.mp σ.property
      have h := hmem hs
      exact compatibleReversePermutationToDecoration_passesReverseFilters (f σ) ht
        h.2.2.2.2.1 h.2.2.2.2.2⟩
  apply Nat.card_le_card_of_injective g
  intro σ τ he
  have hef : f σ = f τ := e.injective (congrArg Subtype.val he)
  exact Subtype.ext (congrArg (fun a : CompatibleReversePermutation hopt K r ↦ a.val) hef)

/-- At the generated matching, every short exposed label is one of the short
removed labels: the only additional exposed label is the long pivot. -/
theorem FilteredPivotDecoration.shortExposed_card_le {L : ℕ} {t : ℝ}
    (D : FilteredPivotDecoration hopt K r L t) (hL : L ≤ K) (hr : K < rotationLength r) :
    (Nat.card {s : Rotation (profileOfScores x) μ₀ //
      s.IsExposedAt D.val.matching.val ∧ rotationLength s ≤ L} : ℝ) ≤
      (3 / 2 : ℝ) * Real.log (L : ℝ) := by
  classical
  let S := D.val.removed.filter (fun s ↦ rotationLength s.val ≤ L)
  let f (s : S) : {q : Rotation (profileOfScores x) μ₀ //
      q.IsExposedAt D.val.matching.val ∧ rotationLength q ≤ L} :=
    ⟨s.val.val, (D.val.isExposedAt_matching_iff s.val.val).mpr
      (Or.inr ⟨s.val, (Finset.mem_filter.mp s.property).1, rfl⟩),
      (Finset.mem_filter.mp s.property).2⟩
  have hf : Function.Surjective f := by
    intro q
    rcases (D.val.isExposedAt_matching_iff q.val).mp q.property.1 with hq | ⟨s, hs, he⟩
    · exact (not_lt_of_ge (hL.trans' (hq ▸ q.property.2)) hr).elim
    · have hs' : s ∈ S := Finset.mem_filter.mpr ⟨hs, he ▸ q.property.2⟩
      exact ⟨⟨s, hs'⟩, Subtype.ext he⟩
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_eq_finsetCard] at hcard
  exact (Nat.cast_le.mpr hcard).trans D.property.1

/-- For any decoration, the number of changed women is
bounded by the total length of the removed labels. -/
private theorem PivotDecoration.exists_changedWomen_cover
    (D : PivotDecoration hopt K r) :
    let A := (singletonRotationAnchor hopt r).val
    ∃ S : Finset (Fin n), S.card ≤ K ∧
      ∀ w ∉ S, D.matching.val.symm w = A.symm w := by
  classical
  intro A
  let B := D.removed.biUnion (fun s ↦ s.val.val.cycle.support)
  let S := B.map A.toEmbedding
  have hB : B.card ≤ K := Finset.card_biUnion_le.trans D.totalLength_le
  refine ⟨S, (Finset.card_map _).trans_le hB, ?_⟩
  intro w hw
  let m := A.symm w
  have hm : m ∉ B := fun hm ↦ hw (Finset.mem_map.mpr ⟨m, hm, A.apply_symm_apply w⟩)
  obtain ⟨rs, _, hrs, hpath⟩ := exists_rotationUndoSequence_of_maximal_subset hopt
    (singletonRotationAnchor hopt r).property D.removed
  have hfix : D.matching.val m = A m := by
    apply hpath.partner_eq_of_fixed m
    intro q hq
    obtain ⟨s, hs, rfl⟩ := hrs ▸ (show q ∈ {q | q ∈ rs} from hq)
    exact Equiv.Perm.notMem_support.mp fun hmem ↦ hm (Finset.mem_biUnion.mpr ⟨s, hs, hmem⟩)
  exact (D.matching.val.symm_apply_eq).mpr ((A.apply_symm_apply w).symm.trans hfix.symm)

/-- Scores at an actual filtered endpoint, without requiring a particular
permutation presentation of the decoration. -/
theorem FilteredPivotDecoration.scoreGeometry {L : ℕ} {t d : ℝ}
    (D : FilteredPivotDecoration hopt K r L t)
    (hties : ∀ row, Function.Injective (x row)) (ht : 0 ≤ t)
    (hY : 0 < femaleSpouseTotal x (singletonRotationAnchor hopt r).val)
    (hy : ∀ w, 0 ≤ femaleSpouseScore x (singletonRotationAnchor hopt r).val w)
    (htd : t ≤ d * femaleSpouseTotal x (singletonRotationAnchor hopt r).val)
    (hKd : (K : ℝ) * d ≤ 1) :
    let A := (singletonRotationAnchor hopt r).val
    let N := D.val.matching.val
    (∀ i, maleSpouseScore x N i ≤ maleSpouseScore x A i) ∧
      (femaleSpouseTotal x A ≤ femaleSpouseTotal x N ∧
        femaleSpouseTotal x N ≤ 2 * femaleSpouseTotal x A) ∧
      (∀ w, femaleSpouseScore x N w / femaleSpouseTotal x N ≤
        femaleSpouseScore x A w / femaleSpouseTotal x A + d) := by
  intro A N
  let Y := femaleSpouseTotal x A
  have hsub : eliminatedRotations (profileOfScores x) μ₀ N ⊆
      eliminatedRotations (profileOfScores x) μ₀ A := by
    change eliminatedRotations (profileOfScores x) μ₀
      (undoMaximalSubsetEmbedding hopt (singletonRotationAnchor hopt r).property
        D.val.removed).val ⊆ _
    rw [eliminatedRotations_undoMaximalSubsetEmbedding]
    exact Set.sdiff_subset
  have hmen := (eliminatedRotations_subset_iff hopt D.val.matching.property
    (singletonRotationAnchor hopt r).property).mp hsub
  have hYle : Y ≤ femaleSpouseTotal x N := femaleSpouseTotal_le_of_eliminatedRotations_subset
    hties hopt D.val.matching.property (singletonRotationAnchor hopt r).property hsub
  obtain ⟨S, hS, hfix⟩ := D.val.exists_changedWomen_cover
  have hinc (w : Fin n) : femaleSpouseScore x N w - femaleSpouseScore x A w ≤ t :=
    D.property.2 w
  have hsum : femaleSpouseTotal x N - Y ≤ (K : ℝ) * t := by
    change (∑ j, femaleSpouseScore x N j) - (∑ j, femaleSpouseScore x A j) ≤ _
    have hzero (w : Fin n) (hw : w ∉ S) :
        femaleSpouseScore x N w - femaleSpouseScore x A w = 0 :=
      sub_eq_zero.mpr (congrArg (x (.inr w)) (hfix w hw))
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S) (fun w _ ↦ hzero w)]
    calc
      _ ≤ ∑ _w ∈ S, t := Finset.sum_le_sum fun w _ ↦ hinc w
      _ = (S.card : ℝ) * t := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hS) ht
  have hKt : (K : ℝ) * t ≤ Y := calc
    _ ≤ (K : ℝ) * (d * Y) := mul_le_mul_of_nonneg_left htd (Nat.cast_nonneg _)
    _ = ((K : ℝ) * d) * Y := (mul_assoc ..).symm
    _ ≤ 1 * Y := mul_le_mul_of_nonneg_right hKd hY.le
    _ = Y := one_mul _
  refine ⟨?_, ⟨hYle, ?_⟩, ?_⟩
  · intro i
    exact le_of_not_gt fun hi ↦ (not_lt_of_ge (hmen i))
      ((rankPermutation_lt_iff (hties (.inl i)) _ _).mpr hi)
  · linarith only [hsum, hKt]
  · intro w
    calc
      _ ≤ (femaleSpouseScore x A w + t) / femaleSpouseTotal x N :=
        div_le_div_of_nonneg_right (sub_le_iff_le_add'.mp (hinc w)) (hY.le.trans hYle)
      _ ≤ (femaleSpouseScore x A w + t) / Y :=
        div_le_div_of_nonneg_left (add_nonneg (hy w) ht) hY hYle
      _ = femaleSpouseScore x A w / Y + t / Y := add_div _ _ _
      _ ≤ _ := add_le_add le_rfl ((div_le_iff₀ hY).mpr htd)

/-- A stable mark is the singleton anchor when the revealed data expose just
one cycle. The corresponding realized label is allowed to vary with the scores. -/
theorem ae_exists_singletonRotationAnchor_of_forwardReveal {n : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (hU : MeasurableSet U)
    (hsingle : ∀ v ∈ U, ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ)
    (ht : ∀ᵐ z ∂offDiagonalScoreLaw n,
      ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) :
    ∀ᵐ z ∂forwardMaskRevealLaw d flag U,
      let p := profileOfScores ((splitScorePairs μ).symm (d, z))
      ∃ (μ₀ : Matching n) (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀),
        (singletonRotationAnchor hopt r).val = μ ∧ r.val.cycle = ρ := by
  have hnon : MeasurableSet (offDiagonalNonblocking d) :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_Iio.prod measurableSet_Iio).compl
  unfold forwardMaskRevealLaw
  filter_upwards [ae_restrict_mem (hU.preimage (measurable_fst.comp
      (measurable_forwardScoreMaskRevealAndInactive flag))),
    ae_restrict_of_ae (ae_restrict_mem (measurableSet_forwardScoreMaskEvent d flag)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_mem hnon)),
    ae_restrict_of_ae (ae_restrict_of_ae (ae_restrict_of_ae ht))]
    with z hz hzmask hzstable hzt
  let x := (splitScorePairs μ).symm (d, z)
  let p := profileOfScores x
  have he : splitScorePairs μ x = (d, z) := (splitScorePairs μ).apply_symm_apply _
  have hμ : IsStable p μ := (isStable_profileOfScores_iff hzt μ).mpr
    ((isScoreStable_iff_splitScorePairs μ x).mpr (by simpa only [he] using hzstable))
  have hmask : (splitScorePairs μ x).2 ∈ forwardScoreMaskEvent (splitScorePairs μ x).1 flag :=
    by simpa only [he] using hzmask
  have huniq (τ : Matching n) : IsExposedRotation p μ τ ↔ τ = ρ := by
    rw [isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag hzt hmask, he]
    exact hsingle _ hz τ
  obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨μ, hμ⟩
  let hρ := (huniq ρ).mpr rfl
  let r := rotationOfExposed hopt hμ hρ
  refine ⟨μ₀, hopt, r, ?_, rfl⟩
  have hanchor := (eq_singletonRotationAnchor_iff hopt r ⟨μ, hμ⟩).mpr fun s ↦ by
    constructor
    · intro hs
      have hc := (huniq s.val.cycle).mp hs.1
      exact Subtype.ext (hs.2.symm.trans (congrArg (rotationLabel μ) hc))
    · rintro rfl
      exact ⟨hρ, rfl⟩
  exact (congrArg Subtype.val hanchor).symm

/-- Transfer the filtered lower moment to a count of actual decorations.
Only the forward reveal needs to identify the singleton anchor. -/
theorem lintegral_filteredDecorationCount_ge {n K : ℕ} (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (U : Set (ForwardRevealedMaleScores flag)) (L : ℕ) (hL : 2 ≤ L) (hn : 0 < n)
    {a D m δlow δ C : ℝ} {η : ℝ≥0∞}
    (h : ReverseCompatibilityControls μ ρ d flag U a D)
    (hlow : ReverseUnfilteredControls μ ρ d flag K η m δlow)
    (hu : ReverseFilterUpperControls d flag δ C) (ha : 1 ≤ a)
    (hbudget : ENNReal.ofReal a ^ K * (K : ℝ≥0∞) *
      ENNReal.ofReal (a * D / ∑ i, (diagonalPairAt d i).1) ≤ ENNReal.ofReal (3 / 32))
    (hshort : ENNReal.ofReal (1 + δ) ^ K * ENNReal.ofReal (4 / Real.log (L : ℝ)) ≤
      ENNReal.ofReal (3 / 128))
    (hinc : ENNReal.ofReal (Real.sqrt (reverseFilterSecondMomentConstant C) / (n : ℝ) ^ 2) ≤
      ENNReal.ofReal (3 / 128) * ((K - 1 : ℕ) : ℝ≥0∞))
    (hsingle : ∀ v ∈ U, ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ)
    (F : OffDiagonalScorePairs n → ℝ≥0∞)
    (hF : ∀ z,
      let p := profileOfScores ((splitScorePairs μ).symm (d, z))
      ∀ (μ₀ : Matching n) (hopt : IsManOptimal p μ₀) (r : Rotation p μ₀),
        (singletonRotationAnchor hopt r).val = μ → r.val.cycle = ρ →
        (Nat.card (FilteredPivotDecoration hopt K r L
          (reverseIncrementCutoff n (∑ i, (diagonalPairAt d i).1))) : ℝ≥0∞) ≤ F z) :
    (forwardMaskRevealLaw d flag U) univ * ENNReal.ofReal (3 / 64) * ((K - 1 : ℕ) : ℝ≥0∞) ≤
      ∫⁻ z, F z ∂forwardMaskRevealLaw d flag U := by
  let t := reverseIncrementCutoff n (∑ i, (diagonalPairAt d i).1)
  have ht : 0 ≤ t := div_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hn))) h.male_total_pos.le
  refine (lintegral_sum_card_filteredReverseSupportFamily_ge μ ρ d flag U L hL hn h hlow hu
    ha hbudget hshort hinc).trans (lintegral_mono_ae ?_)
  filter_upwards [ae_exists_singletonRotationAnchor_of_forwardReveal μ ρ d flag U
    h.measurable_reveal hsingle h.tie_free] with z hz
  obtain ⟨μ₀, hopt, r, hanchor, hcycle⟩ := hz
  have hpoint := sum_card_filteredReverseSupportFamily_le_card_filteredPivotDecoration
    hopt r flag K L ht
  dsimp only at hpoint
  have hpoint' : (∑ k ∈ Finset.Icc 2 K,
      (filteredReverseSupportFamily μ ρ flag k L t ((splitScorePairs μ).symm (d, z))).card) ≤
      Nat.card (FilteredPivotDecoration hopt K r L t) := by
    simpa only [hanchor, hcycle] using hpoint
  refine le_trans ?_ (hF z μ₀ hopt r hanchor hcycle)
  exact_mod_cast hpoint'

end LennonPittelFormalization

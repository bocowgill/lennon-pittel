module

public import LennonPittel.PivotSharedReverse

/-!
# Score geometry of shared-switch images

The two endpoints inherit the eligible-anchor score bounds. Their relative
cycles split into a long orientation and a short orientation of exposed cycles
at the later endpoint, where the total short exposure count is capped.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped Topology

namespace LennonPittelFormalization

variable {n : ℕ}

/-- The explicit score domain (4) inherited by a filtered endpoint. -/
def InResidualEndpointScoreDomain (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) ^ (1 / 10 : ℝ) ≤ femaleSpouseTotal x μ ∧
  femaleSpouseTotal x μ ≤ 2 * (n : ℝ) ^ (2 / 5 : ℝ) ∧
  (∀ w, femaleSpouseScore x μ w / femaleSpouseTotal x μ ≤ 2060 * Real.log n / n) ∧
  ∀ m, maleSpouseScore x μ m ≤ 16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)

theorem measurableSet_inResidualEndpointScoreDomain (μ : Matching n) :
    MeasurableSet {x : ScoreProfile n | InResidualEndpointScoreDomain x μ} := by
  unfold InResidualEndpointScoreDomain
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const (measurable_femaleSpouseTotal μ)).inter <|
    (measurableSet_le (measurable_femaleSpouseTotal μ) measurable_const).inter <|
    (MeasurableSet.iInter fun w ↦ measurableSet_le
      ((measurable_femaleSpouseScore μ w).div (measurable_femaleSpouseTotal μ))
      measurable_const).inter <|
    MeasurableSet.iInter fun m ↦ measurableSet_le (measurable_maleSpouseScore μ m) measurable_const

/-- A support cap of order at most the square root makes the total relative
reverse increment eventually at most one. -/
theorem eventually_residualEndpointIncrementBudget (κ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * Real.sqrt (n : ℝ) →
      (K : ℝ) * (2048 * Real.log n / n) ≤ 1 := by
  have hlog := (((isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).const_mul_left
    (2048 * κ)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [hlog, eventually_gt_atTop (0 : ℕ)] with n hlog hn K hK
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have habs : |2048 * κ * Real.log n| ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := hlog
  rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  have hbound := (le_abs_self _).trans habs
  calc
    _ ≤ (κ * Real.sqrt (n : ℝ)) * (2048 * Real.log n / n) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (Real.sqrt (n : ℝ) * (2048 * κ * Real.log n)) / n := by ring
    _ ≤ (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)) hnR.le
    _ = _ := by rw [← pow_two, Real.sq_sqrt hnR.le, div_self hnR.ne']

/-- Inheriting domain (4) only costs the uniform numerical bound on the total
increment; the statement also applies to an endpoint after restoring a label. -/
theorem FilteredPivotDecoration.inResidualEndpointScoreDomain
    {x : ScoreProfile n} {μ₀ μ ρ : Matching n} {K L : ℕ} {b A B t : ℝ}
    {hopt : IsManOptimal (profileOfScores x) μ₀} {r : Rotation (profileOfScores x) μ₀}
    (D : FilteredPivotDecoration hopt K r L t)
    (hties : ∀ row, Function.Injective (x row)) (hn : 0 < n)
    (hK : (K : ℝ) * (2048 * Real.log n / n) ≤ 1)
    (hμ : (singletonRotationAnchor hopt r).val = μ)
    (ht : t = reverseIncrementCutoff n (maleSpouseTotal x μ))
    (hE : IsLocallyEligiblePivot b A B x μ ρ) :
    InResidualEndpointScoreDomain x D.val.matching.val := by
  let d := (splitScorePairs μ x).1
  let X := maleSpouseTotal x μ
  let Y := femaleSpouseTotal x μ
  let R : ℝ := (n : ℝ) ^ (1 / 10 : ℝ)
  have hX : reverseDiagonalMaleTotal d = X := reverseDiagonalMaleTotal_splitScorePairs μ x
  have hY : pivotDiagonalFemaleTotal d = Y := pivotDiagonalFemaleTotal_splitScorePairs μ x
  have hdiag (i : Fin n) :
      diagonalPairAt d i = (maleSpouseScore x μ i, femaleSpouseScore x μ (μ i)) := by
    rw [show d = (splitScorePairs μ x).1 from rfl, diagonalPairAt_splitScorePairs,
      femaleSpouseScore, maleSpouseScore, Equiv.symm_apply_apply]
  have hgeom := hE.1
  obtain ⟨hunit, hY2, hYhi, hXY, hshare, hmale⟩ := hgeom.base
  rw [hY] at hY2 hYhi hXY hshare hmale
  rw [hX] at hXY
  have hYlo := hgeom.lower_band
  change R ≤ pivotDiagonalFemaleTotal d at hYlo
  rw [hY] at hYlo
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY2
  have hXpos : 0 < X := pos_of_mul_pos_left ((by positivity : 0 < (n : ℝ) / 128).trans_le hXY)
    hYpos.le
  have hRpos : 0 < R := Real.rpow_pos_of_pos hnR _
  have hnonneg (w : Fin n) : 0 ≤ femaleSpouseScore x μ w := by
    have hw := (hunit (μ.symm w)).2.1
    rwa [hdiag, Equiv.apply_symm_apply] at hw
  have ht₀ : 0 ≤ t := by
    rw [ht, reverseIncrementCutoff]
    exact div_nonneg (mul_nonneg (by norm_num) hlog) hXpos.le
  have htY : t ≤ (2048 * Real.log n / n) * Y := by
    rw [ht, reverseIncrementCutoff]
    apply (div_le_iff₀ hXpos).2
    calc
      16 * Real.log n = (2048 * Real.log n / n) * ((n : ℝ) / 128) := by
        field_simp
        ring
      _ ≤ (2048 * Real.log n / n) * (X * Y) :=
        mul_le_mul_of_nonneg_left hXY (div_nonneg (by positivity) hnR.le)
      _ = (2048 * Real.log n / n) * Y * X := by ring
  obtain ⟨hm, hYmove, hy⟩ := D.scoreGeometry hties ht₀
    (by rw [hμ]; exact hYpos) (by rw [hμ]; exact hnonneg) (by rw [hμ]; exact htY) hK
  rw [hμ] at hm hYmove hy
  refine ⟨hYlo.trans hYmove.1, hYmove.2.trans (mul_le_mul_of_nonneg_left hYhi (by norm_num)),
    ?_, ?_⟩
  · intro w
    have hs := hshare (μ.symm w)
    rw [hdiag, Equiv.apply_symm_apply] at hs
    change femaleSpouseScore x μ w / femaleSpouseTotal x μ ≤ _ at hs
    exact (hy w).trans (by
      calc
        _ ≤ 12 * Real.log n / n + 2048 * Real.log n / n := add_le_add hs le_rfl
        _ = _ := by ring)
  · intro m
    have hs := hmale m
    rw [hdiag] at hs
    exact (hm m).trans (hs.trans (by
      have hhalf : R / 2 ≤ Y - 1 := by linarith only [hY2, hYlo]
      calc
        _ ≤ 8 * Real.log n / (R / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
        _ = _ := by ring))

/-- Men who receive a worse partner in the first of two matchings. -/
def worsePartnerMen (p : Profile n) (μ ν : Matching n) : Finset (Fin n) :=
  Finset.univ.filter fun m ↦ p.manRank m (ν m) < p.manRank m (μ m)

/-- On tie-free rows, the rank orientation agrees with the spouse-score orientation. -/
theorem mem_worsePartnerMen_iff_score_lt {x : ScoreProfile n}
    (hties : ∀ row, Function.Injective (x row)) (μ ν : Matching n) (m : Fin n) :
    m ∈ worsePartnerMen (profileOfScores x) μ ν ↔
      maleSpouseScore x ν m < maleSpouseScore x μ m := by
  rw [worsePartnerMen, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, profileOfScores, maleSpouseScore,
    rankPermutation_lt_iff (hties (.inl m))]

/-- Read each partner in `μ` as the label of her husband in `ν`. -/
def relativeMenPermutation (μ ν : Matching n) : Matching n := μ.trans ν.symm

theorem disjoint_worsePartnerMen (p : Profile n) (μ ν : Matching n) :
    Disjoint (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) := by
  refine Finset.disjoint_left.mpr fun m hm hm' ↦ ?_
  exact (Finset.mem_filter.mp hm).2.not_gt (Finset.mem_filter.mp hm').2

theorem union_worsePartnerMen_eq_support (p : Profile n) (μ ν : Matching n) :
    worsePartnerMen p μ ν ∪ worsePartnerMen p ν μ = (relativeMenPermutation μ ν).support := by
  ext m
  simp only [worsePartnerMen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.Perm.mem_support, relativeMenPermutation, Equiv.trans_apply, ← ne_iff_lt_or_gt]
  rw [(p.manRank m).injective.ne_iff]
  exact ne_comm.trans (not_congr ν.symm_apply_eq).symm

/-- All forward exposed cycles of length at most `L` at the matching. -/
noncomputable def exposedShortCycles (p : Profile n) (ν : Matching n) (L : ℕ) :
    Finset (Matching n) := by
  classical
  exact Finset.univ.filter fun c ↦ IsExposedRotation p ν c ∧ c.support.card ≤ L

/-- The cap on all short exposed cycles transfers from labels to permutations. -/
theorem FilteredPivotDecoration.exposedShortCycles_card_le
    {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ} {t : ℝ}
    {hopt : IsManOptimal (profileOfScores x) μ₀} {r : Rotation (profileOfScores x) μ₀}
    (D : FilteredPivotDecoration hopt K r L t) (hL : L ≤ K) (hr : K < rotationLength r) :
    ((exposedShortCycles (profileOfScores x) D.val.matching.val L).card : ℝ) ≤
      (3 / 2 : ℝ) * Real.log L := by
  classical
  let f (c : ↥(exposedShortCycles (profileOfScores x) D.val.matching.val L)) :
      {s : Rotation (profileOfScores x) μ₀ //
        s.IsExposedAt D.val.matching.val ∧ rotationLength s ≤ L} :=
    let hc := (Finset.mem_filter.mp c.property).2
    ⟨rotationOfExposed hopt D.val.matching.property hc.1, ⟨hc.1, rfl⟩, hc.2⟩
  have hf : Function.Injective f := fun _ _ h ↦
    Subtype.ext (congrArg (fun s ↦ s.val.val.cycle) h)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at hcard
  exact (Nat.cast_le.mpr hcard).trans (D.shortExposed_card_le hL hr)

/-- The rank-based geometry of a pair, independent of continuous score magnitudes. -/
structure IsResidualPairRankGeometry (b : ℝ) (K L : ℕ) (p : Profile n)
    (μ ν : Matching n) : Prop where
  stable_early : IsStable p μ
  stable_late : IsStable p ν
  short_nonempty : (worsePartnerMen p μ ν).Nonempty
  long_nonempty : (worsePartnerMen p ν μ).Nonempty
  short_size : (worsePartnerMen p μ ν).card ≤ K
  long_size : b * Real.sqrt (n : ℝ) ≤ ((worsePartnerMen p ν μ).card : ℝ)
  cycle_partition : ∀ c ∈ (relativeMenPermutation μ ν).cycleFactorsFinset,
    (c.support ⊆ worsePartnerMen p μ ν ∧ IsExposedRotation p ν c) ∨
      c.support ⊆ worsePartnerMen p ν μ
  short_exposure_cap : ((exposedShortCycles p ν L).card : ℝ) ≤ (3 / 2 : ℝ) * Real.log L

/-- The short relative cycles entirely on the orientation worse in the first matching. -/
def forcedShortCycles (p : Profile n) (μ ν : Matching n) (L : ℕ) : Finset (Matching n) :=
  (relativeMenPermutation μ ν).cycleFactorsFinset.filter fun c ↦
    c.support ⊆ worsePartnerMen p μ ν ∧ c.support.card ≤ L

/-- The short exposed cycles using only labels fixed by the relative permutation. -/
noncomputable def backgroundShortCycles (p : Profile n) (μ ν : Matching n) (L : ℕ) :
    Finset (Matching n) :=
  (exposedShortCycles p ν L).filter fun c ↦
    Disjoint c.support (relativeMenPermutation μ ν).support

namespace IsResidualPairRankGeometry

variable {b : ℝ} {K L : ℕ} {p : Profile n} {μ ν : Matching n}

/-- A nonempty orientation consists of nontrivial cycles and thus has at least two men. -/
theorem orientation_card_ge_two (h : IsResidualPairRankGeometry b K L p μ ν) :
    2 ≤ (worsePartnerMen p μ ν).card ∧ 2 ≤ (worsePartnerMen p ν μ).card := by
  have hex {m : Fin n}
      (hm : m ∈ worsePartnerMen p μ ν ∪ worsePartnerMen p ν μ) :
      ∃ c ∈ (relativeMenPermutation μ ν).cycleFactorsFinset, m ∈ c.support :=
    Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp
      (union_worsePartnerMen_eq_support p μ ν ▸ hm)
  have hd := Finset.disjoint_left.mp (disjoint_worsePartnerMen p μ ν)
  constructor
  · obtain ⟨m, hm⟩ := h.short_nonempty
    obtain ⟨c, hc, hmc⟩ := hex (Finset.mem_union.mpr (Or.inl hm))
    rcases h.cycle_partition c hc with hs | hl
    · exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support.trans
        (Finset.card_le_card hs.1)
    · exact (hd hm (hl hmc)).elim
  · obtain ⟨m, hm⟩ := h.long_nonempty
    obtain ⟨c, hc, hmc⟩ := hex (Finset.mem_union.mpr (Or.inr hm))
    rcases h.cycle_partition c hc with hs | hl
    · exact (hd (hs.1 hmc) hm).elim
    · exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support.trans
        (Finset.card_le_card hl)

/-- Every forced short cycle appears in the set counted by the total exposure cap. -/
theorem forcedShortCycles_subset (h : IsResidualPairRankGeometry b K L p μ ν) :
    forcedShortCycles p μ ν L ⊆ exposedShortCycles p ν L := by
  classical
  intro c hc
  obtain ⟨hc, hs, hL⟩ := Finset.mem_filter.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, hL⟩
  rcases h.cycle_partition c hc with hshort | hlong
  · exact hshort.2
  · have hcyc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
    obtain ⟨m, hm⟩ := Finset.card_pos.mp
      ((by decide : 0 < 2).trans_le hcyc.two_le_card_support)
    exact (Finset.disjoint_left.mp (disjoint_worsePartnerMen p μ ν) (hs hm) (hlong hm)).elim

/-- The total exposure cap applies jointly to forced and fixed-position background cycles. -/
theorem forced_background_card_le (h : IsResidualPairRankGeometry b K L p μ ν) :
    ((forcedShortCycles p μ ν L).card : ℝ) + ((backgroundShortCycles p μ ν L).card : ℝ) ≤
      (3 / 2 : ℝ) * Real.log L := by
  classical
  have hd : Disjoint (forcedShortCycles p μ ν L) (backgroundShortCycles p μ ν L) := by
    refine Finset.disjoint_left.mpr fun c hc hb ↦ ?_
    have hf := (Finset.mem_filter.mp hc).1
    have hcyc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hf).1
    obtain ⟨m, hm⟩ := Finset.card_pos.mp
      ((by decide : 0 < 2).trans_le hcyc.two_le_card_support)
    exact Finset.disjoint_left.mp (Finset.mem_filter.mp hb).2 hm
      (Equiv.Perm.mem_cycleFactorsFinset_support_le hf hm)
  have hsub : backgroundShortCycles p μ ν L ⊆ exposedShortCycles p ν L :=
    Finset.filter_subset _ _
  have hcard := Finset.card_le_card (Finset.union_subset h.forcedShortCycles_subset hsub)
  rw [Finset.card_union_of_disjoint hd] at hcard
  exact (by exact_mod_cast hcard :
    ((forcedShortCycles p μ ν L).card : ℝ) + ((backgroundShortCycles p μ ν L).card : ℝ) ≤
      ((exposedShortCycles p ν L).card : ℝ)).trans h.short_exposure_cap

end IsResidualPairRankGeometry

/-- A measurable event containing the actual toggle images, stated solely in
terms of the scores and two endpoint matchings. -/
structure IsResidualPairGeometry (b : ℝ) (K L : ℕ) (x : ScoreProfile n)
    (μ ν : Matching n) : Prop where
  rank : IsResidualPairRankGeometry b K L (profileOfScores x) μ ν
  early_scores : InResidualEndpointScoreDomain x μ
  late_scores : InResidualEndpointScoreDomain x ν

theorem measurableSet_isResidualPairGeometry (b : ℝ) (K L : ℕ) (μ ν : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsResidualPairGeometry b K L x μ ν} := by
  have h : MeasurableSet {x : ScoreProfile n |
      IsResidualPairRankGeometry b K L (profileOfScores x) μ ν} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsResidualPairRankGeometry b K L p μ ν})
  exact (h.inter ((measurableSet_inResidualEndpointScoreDomain μ).inter
    (measurableSet_inResidualEndpointScoreDomain ν))).congr (Set.ext fun _ ↦
      ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ⟨h.rank, h.early_scores, h.late_scores⟩⟩)

namespace ResidualPivotPair

variable {p : Profile n} {μ₀ : Matching n} {K : ℕ} {hopt : IsManOptimal p μ₀}

private theorem orientations_nonempty (R : ResidualPivotPair hopt K) :
    R.shortOrientationMen.Nonempty ∧ R.longOrientationMen.Nonempty := by
  let A := R.toggledEarly.2.matching
  let B := R.late.2.matching
  constructor
  · by_contra hn
    apply R.toggleImage.property.1
    apply (eliminatedRotations_subset_iff hopt A.property B.property).mpr
    intro m
    exact le_of_not_gt fun hm ↦ hn ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
  · by_contra hn
    apply R.toggleImage.property.2
    apply (eliminatedRotations_subset_iff hopt B.property A.property).mpr
    intro m
    exact le_of_not_gt fun hm ↦ hn ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩

/-- Each relative cycle is contained in one orientation. In the short
orientation it is a forward exposed cycle at the later endpoint. -/
theorem cycle_partition (R : ResidualPivotPair hopt K)
    {c : Matching n} (hc : c ∈ R.relativePermutation.cycleFactorsFinset) :
    (c.support ⊆ R.shortOrientationMen ∧ IsExposedRotation p R.late.2.matching.val c) ∨
      c.support ⊆ R.longOrientationMen := by
  classical
  by_cases h : ∃ m ∈ c.support, m ∈ R.shortOrientationMen
  · obtain ⟨m, hm, hshort⟩ := h
    obtain ⟨s, hs, rfl⟩ := R.exists_shortLabel_of_cycleFactor hc hm hshort
    have hs' : s ∈ eliminatedRotations p μ₀ R.toggledEarly.2.matching.val \
        eliminatedRotations p μ₀ R.late.2.matching.val :=
      R.coe_shortOrientationLabels ▸ (Finset.mem_coe.mpr hs)
    have he := (R.isExposedAt_late_of_mem_toggle_early_ideal_diff_late hs').1
    refine Or.inl ⟨fun m hm ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    have hmove := Equiv.Perm.mem_support.mp hm
    have hp := R.relativePermutation_apply_of_mem_shortLabel hs hmove
    have heq : eliminateRotation R.late.2.matching.val s.val.cycle m =
        R.toggledEarly.2.matching.val m := by
      rw [eliminateRotation_apply, ← hp]
      exact R.late.2.matching.val.apply_symm_apply _
    exact heq ▸ he.manRank_lt_eliminate_of_moved hmove
  · right
    intro m hm
    have hs := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hm
    change m ∈ (relativeMenPermutation R.toggledEarly.2.matching.val
      R.late.2.matching.val).support at hs
    rw [← union_worsePartnerMen_eq_support p R.toggledEarly.2.matching.val
      R.late.2.matching.val] at hs
    exact (Finset.mem_union.mp hs).resolve_left fun hms ↦ h ⟨m, hm, hms⟩

end ResidualPivotPair

namespace ResidualMarkedPair

variable {x : ScoreProfile n} {μ₀ : Matching n} {K L : ℕ}
  {flag : Matching n → Matching n → OffDiagonalCellIndex n → Bool}
  {t : Matching n → Matching n → ℝ}

/-- The fixed-endpoint, measurable event holds on every actual toggle image. -/
theorem toggleImage_geometry (a : ResidualMarkedPair x K L flag t)
    (hopt : IsManOptimal (profileOfScores x) μ₀)
    (hties : ∀ row, Function.Injective (x row)) (hn : 0 < n) (hL : L ≤ K)
    (hK : (K : ℝ) * (2048 * Real.log n / n) ≤ 1)
    (ht : ∀ μ ρ, t μ ρ = reverseIncrementCutoff n (maleSpouseTotal x μ))
    {b A B : ℝ}
    (hEarly : IsLocallyEligiblePivot b A B x a.early.anchor a.early.cycle)
    (hLate : IsLocallyEligiblePivot b A B x a.late.anchor a.late.cycle) :
    IsResidualPairGeometry b K L x (a.toResidualPivotPair hopt).toggleImage.val.1.val
      (a.toResidualPivotPair hopt).toggleImage.val.2.val := by
  let R := a.toResidualPivotPair hopt
  let D₁ : FilteredPivotDecoration hopt K R.early.1.val L (t a.early.anchor a.early.cycle) :=
    ⟨R.toggledEarly.2, a.toResidualPivotPair_toggledEarly_passesReverseFilters hopt hties⟩
  let D₂ : FilteredPivotDecoration hopt K R.late.1.val L (t a.late.anchor a.late.cycle) :=
    ⟨R.late.2, a.toResidualPivotPair_late_passesReverseFilters hopt⟩
  refine ⟨⟨D₁.val.matching.property, D₂.val.matching.property,
    R.orientations_nonempty.1, R.orientations_nonempty.2, R.card_shortOrientationMen_le,
    ?_, fun c hc ↦ R.cycle_partition hc, D₂.exposedShortCycles_card_le hL R.late.1.property⟩,
    D₁.inResidualEndpointScoreDomain hties hn hK (a.early.pivot_anchor hopt) (ht _ _) hEarly,
    D₂.inResidualEndpointScoreDomain hties hn hK (a.late.pivot_anchor hopt) (ht _ _) hLate⟩
  have hlen : a.early.cycle.support.card ≤ R.longOrientationMen.card := by
    have h := R.rotationLength_early_le_card_longOrientationMen
    change rotationLength (a.early.pivot hopt).val ≤ _ at h
    simpa only [rotationLength, a.early.pivot_cycle hopt] using h
  exact hEarly.1.length_lower.trans (Nat.cast_le.mpr hlen)

end ResidualMarkedPair

end LennonPittelFormalization

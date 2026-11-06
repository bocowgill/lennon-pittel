module

public import LennonPittel.DAEndpointAsymptotics
public import LennonPittel.PivotLocalEligibility
public import LennonPittel.PivotMarkedCutoffBridge
public import LennonPittel.PivotSupportMassTail
public import LennonPittel.PivotForwardIncrementTail

/-!
# Abundance of locally eligible singleton anchors

First bound a bad cycle at any stable mark, rather than conditioning on how
the walk chooses a pivot. Then intersect the walk's abundance event with the
simultaneous score regularity and the two cutoff guarantees.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The diagonal conditions for the two tilted cutoff tests. -/
def pivotCutoffDiagonal (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | d ∈ pivotBaseDiagonalBand n ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d ∧
    (∑ i, forwardSpouseWeight d i * pivotSupportMaleWeight d i) ≤ 24 / (n : ℝ)}

theorem measurableSet_pivotCutoffDiagonal (n : ℕ) :
    MeasurableSet (pivotCutoffDiagonal n) := by
  have hy (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hY : Measurable (@pivotDiagonalFemaleTotal n) :=
    Finset.measurable_sum _ fun i _ ↦ hy i
  have hmix : Measurable (fun d : DiagonalScorePairs n ↦ ∑ i,
      forwardSpouseWeight d i * pivotSupportMaleWeight d i) :=
    Finset.measurable_sum _ fun i _ ↦ ((hy i).div hY).mul (measurable_pivotSupportMaleWeight i)
  refine (measurableSet_pivotBaseDiagonalBand n).inter
    ((measurableSet_le measurable_const hY).inter (measurableSet_le hmix measurable_const))

theorem splitScorePairs_mem_pivotCutoffDiagonal {n : ℕ} (hn : 0 < n) {x : ScoreProfile n}
    (hg : x ∈ goodPivotScoreGeometry n) (μ : Matching n) (hμ : IsStable (profileOfScores x) μ)
    (hband : femaleSpouseTotal x μ ∈ Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))) :
    (splitScorePairs μ x).1 ∈ pivotCutoffDiagonal n := by
  refine ⟨(hg.1.2.2 μ hμ hband.2).1, ?_, ?_⟩
  · rw [pivotDiagonalFemaleTotal_splitScorePairs]
    exact hband.1
  · exact sum_diagonalSpouseWeights_mul_le_of_goodPivotScoreGeometry hn hg μ hμ

/-- A statistic violates a cutoff on an exposed short cycle at a fixed matching. -/
def badShortPivotAt {n : ℕ} (V : ScoreProfile n → Matching n → Matching n → ℝ)
    (A t : ℝ) (μ : Matching n) : Set (ScoreProfile n) :=
  {x | ∃ σ : Matching n, IsExposedRotation (profileOfScores x) μ σ ∧
    (σ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ) ∧ t < V x μ σ}

theorem measurableSet_badShortPivotAt {n : ℕ}
    {V : ScoreProfile n → Matching n → Matching n → ℝ} (μ : Matching n)
    (hV : ∀ σ, Measurable (fun x ↦ V x μ σ)) (A t : ℝ) :
    MeasurableSet (badShortPivotAt V A t μ) := by
  unfold badShortPivotAt
  simp only [ofPred_exists, ofPred_and]
  refine MeasurableSet.iUnion fun σ ↦ (measurable_profileOfScores n
    (MeasurableSet.of_discrete : MeasurableSet {p : Profile n | IsExposedRotation p μ σ})).inter
    ((MeasurableSet.const _).inter (measurableSet_lt measurable_const (hV σ)))

/-- A cutoff exception with the local diagonal conditions, at some stable mark. -/
def badShortStablePivot {n : ℕ} (V : ScoreProfile n → Matching n → Matching n → ℝ)
    (A t : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ pivotCutoffDiagonal n ∧
    x ∈ badShortPivotAt V A t μ}

/-- Sum per-length conditional error probabilities and transfer to the original law. -/
theorem measure_badShortStablePivot_le {n : ℕ}
    {V : ScoreProfile n → Matching n → Matching n → ℝ} {A t : ℝ}
    (hV : ∀ μ σ, Measurable (fun x ↦ V x μ σ)) {e : ℝ≥0∞} (he : e ≠ ∞)
    (hrow : ∀ μ : Matching n, ∀ᵐ d ∂diagonalScoreLaw n, d ∈ pivotCutoffDiagonal n →
      ∀ k ∈ Finset.Icc 2 n, (k : ℝ) ≤ A * Real.sqrt (n : ℝ) →
        (Measure.pi (normalizedStableScoreRowLaw d))
          {r | let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
               ∃ σ : Matching n, IsExposedRotation (profileOfScores x) μ σ ∧
                 σ.support.card = k ∧ t < V x μ σ} ≤ e) :
    continuousScoreLaw n (badShortStablePivot V A t) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) * ((n : ℝ≥0∞) * e) := by
  classical
  refine measure_exists_scoreStable_diagonal_event_le _ _ _ fun μ ↦ ?_
  apply measure_scoreStable_diagonal_scoreEvent_le μ (measurableSet_pivotCutoffDiagonal n)
    (fun _ hd ↦ ⟨fun i ↦ (hd.1.1 i).1, fun i ↦ Ico_subset_Icc_self (hd.1.1 i).2⟩)
    (measurableSet_badShortPivotAt μ (hV μ) A t)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) he)
  filter_upwards [hrow μ] with d hd hD
  let S := (Finset.Icc 2 n).filter (fun k : ℕ ↦ (k : ℝ) ≤ A * Real.sqrt (n : ℝ))
  let R := fun r : OffDiagonalScoreRows n ↦ (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  let E (k : ℕ) := {r | ∃ σ : Matching n, IsExposedRotation (profileOfScores (R r)) μ σ ∧
    σ.support.card = k ∧ t < V (R r) μ σ}
  have hsub : {r | R r ∈ badShortPivotAt V A t μ} ⊆ ⋃ k ∈ S, E k := by
    rintro r ⟨σ, hσ, hA, ht⟩
    have hk : σ.support.card ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr
      ⟨hσ.isCycle.two_le_card_support, (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)⟩
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hk, hA⟩, σ, hσ, rfl, ht⟩⟩
  have hcard : S.card ≤ n := by
    calc
      _ ≤ (Finset.Icc 2 n).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n + 1 - 2 := Nat.card_Icc 2 n
      _ ≤ n := by omega
  calc
    _ ≤ (Measure.pi (normalizedStableScoreRowLaw d)) (⋃ k ∈ S, E k) := measure_mono hsub
    _ ≤ ∑ k ∈ S, (Measure.pi (normalizedStableScoreRowLaw d)) (E k) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ S, e := Finset.sum_le_sum fun k hk ↦
      hd hD k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_left (Nat.cast_le.mpr hcard) _

/-- A power-five per-length error remains negligible after summing over
all lengths and all stable marks. -/
theorem tendsto_measure_badShortStablePivot_of_perLength {E : ∀ n, Set (ScoreProfile n)}
    (hE : ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (E n) ≤
      ENNReal.ofReal (expectedNumStableMatchings n) *
        ((n : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) ^ (-5 : ℝ)))) :
    Tendsto (fun n ↦ continuousScoreLaw n (E n)) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((n : ℝ) ^ (-2 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop)
  refine tendsto_const_nhds.squeeze' hzero (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hE, eventually_expectedNumStableMatchings_le_sizeLog,
    eventually_gt_atTop (0 : ℕ)] with n h hn hnpos
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hmean : expectedNumStableMatchings n ≤ (n : ℝ) ^ (2 : ℕ) := by
    have hlog : Real.log (n : ℝ) ≤ n :=
      (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
    simpa only [pow_two] using hn.trans (mul_le_mul_of_nonneg_left hlog hpos.le)
  refine h.trans ((mul_le_mul_left (ENNReal.ofReal_le_ofReal hmean) _).trans_eq ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hpos.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = (n : ℝ) ^ (2 : ℝ) * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-5 : ℝ)) := by
      rw [Real.rpow_two, Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]; norm_num

theorem measurable_pivotMaleSupportMass {n : ℕ} (μ σ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ pivotMaleSupportMass x μ σ) := by
  unfold pivotMaleSupportMass
  exact Finset.measurable_sum _ fun i _ ↦ by
    have hi : Measurable (fun x : ScoreProfile n ↦
        pivotSupportMaleWeight (splitScorePairs μ x).1 i) :=
      (measurable_pivotSupportMaleWeight i).comp (measurable_fst.comp (splitScorePairs μ).measurable)
    simpa only [pivotSupportMaleWeight_splitScorePairs] using hi

theorem measurable_pivotNormalizedForwardIncrement {n : ℕ} (μ σ : Matching n) :
    Measurable (fun x : ScoreProfile n ↦ pivotNormalizedForwardIncrement x μ σ) := by
  unfold pivotNormalizedForwardIncrement
  refine (measurable_femaleSpouseTotal μ).mul (Finset.measurable_sum _ fun i _ ↦ ?_)
  have hi : Measurable (fun x : ScoreProfile n ↦ x (.inl i)) := measurable_pi_apply _
  exact ((measurable_pi_apply (μ (σ i))).comp hi).sub ((measurable_pi_apply (μ i)).comp hi)

/-- The male support-mass cutoff holds at every short exposed pivot
in the marked score band, apart from an event of vanishing probability. -/
theorem tendsto_measure_badShortStablePivotMaleMass (A : ℝ) :
    Tendsto (fun n ↦ continuousScoreLaw n
      (badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt (n : ℝ))))
      atTop (𝓝 0) := by
  apply tendsto_measure_badShortStablePivot_of_perLength
  filter_upwards [eventually_measure_pi_heavyForwardSupport_length_le A 5] with n hmass
  refine measure_badShortStablePivot_le measurable_pivotMaleSupportMass ENNReal.ofReal_ne_top
    fun μ ↦ ?_
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hrows hd k _ hk
  refine (measure_mono_ae ?_).trans (hmass k hk d hd.1 hd.2.2)
  filter_upwards [hrows (fun i ↦ (hd.1.1 i).1) (fun i ↦ Ico_subset_Icc_self (hd.1.1 i).2)]
    with r hr hbad
  obtain ⟨σ, hσ, hk', hcut⟩ := hbad
  let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  have hsplit : (splitScorePairs μ x).1 = d := by simp [x]
  have hmass' : pivotMaleSupportMass x μ σ = ∑ i ∈ σ.support, pivotSupportMaleWeight d i := by
    simp_rw [pivotMaleSupportMass, ← pivotSupportMaleWeight_splitScorePairs, hsplit]
  exact ⟨σ, (realizesDirectedCycle_forwardOutcome_iff μ d r σ hr.2 hr.1).mpr hσ,
    hk', hmass' ▸ hcut⟩

/-- The normalized male increment cutoff holds for every short exposed
pivot in the marked score band, apart from an event of vanishing probability. -/
theorem tendsto_measure_badShortStablePivotForwardIncrement (A : ℝ) :
    Tendsto (fun n ↦ continuousScoreLaw n
      (badShortStablePivot pivotNormalizedForwardIncrement A
        ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ)))) atTop (𝓝 0) := by
  apply tendsto_measure_badShortStablePivot_of_perLength
  filter_upwards [eventually_measure_forwardIncrementOverflowRowEvent_le (A := A) (p := 5)]
    with n hinc
  refine measure_badShortStablePivot_le measurable_pivotNormalizedForwardIncrement
    ENNReal.ofReal_ne_top fun μ ↦ ?_
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hrows hd k _ hk
  refine (measure_mono_ae ?_).trans (hinc d hd.1 hd.2.1 k hk)
  filter_upwards [hrows (fun i ↦ (hd.1.1 i).1) (fun i ↦ Ico_subset_Icc_self (hd.1.1 i).2)]
    with r hr hbad
  obtain ⟨σ, hσ, hk', hcut⟩ := hbad
  let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  have hsplit : splitScorePairs μ x = (d, (offDiagonalRowsEquiv n).symm r) :=
    (splitScorePairs μ).apply_symm_apply _
  have hd' : (splitScorePairs μ x).1 = d := congrArg Prod.fst hsplit
  have hr' : offDiagonalRowsEquiv n (splitScorePairs μ x).2 = r := by
    rw [congrArg Prod.snd hsplit, MeasurableEquiv.apply_symm_apply]
  have hval : pivotNormalizedForwardIncrement x μ σ =
      pivotDiagonalFemaleTotal d *
        ∑ i ∈ σ.support, forwardRowScoreIncrement d i (σ i) (r i) := by
    unfold pivotNormalizedForwardIncrement
    rw [← pivotDiagonalFemaleTotal_splitScorePairs μ x, hd']
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have he := forwardRowScoreIncrement_splitScorePairs μ x
      (Equiv.Perm.mem_support.mp hi).symm
    rw [hd', hr'] at he
    exact he.symm
  exact ⟨σ, (realizesDirectedCycle_forwardOutcome_iff μ d r σ hr.2 hr.1).mpr hσ,
    hk', hval ▸ hcut⟩

/-- Distinct rotations have sufficiently many singleton anchors passing
the fixed, local score, mask and forward-reveal tests. -/
def locallyEligiblePivotAbundance (n : ℕ) (b A B : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
    Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
    ∀ r ∈ S, IsLocallyEligiblePivot b A B x
      (singletonRotationAnchor (DAState.isManOptimal_matching (profileOfScores x)) r).val
      r.val.cycle}

theorem measurableSet_locallyEligiblePivotAbundance (n : ℕ) (b A B : ℝ) :
    MeasurableSet (locallyEligiblePivotAbundance n b A B) := by
  let F (p : Profile n) : Set (ScoreProfile n) :=
    {x | ∃ S : Finset (Rotation p (DAState.matching p)),
      Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
      ∀ r ∈ S, IsLocallyEligiblePivot b A B x
        (singletonRotationAnchor (DAState.isManOptimal_matching p) r).val r.val.cycle}
  have hF (p : Profile n) : MeasurableSet (F p) := by
    unfold F
    simp only [ofPred_exists, ofPred_and, ofPred_forall]
    refine MeasurableSet.iUnion fun S ↦ (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦ ?_)
    exact measurableSet_isLocallyEligiblePivot b A B _ _
  have he : locallyEligiblePivotAbundance n b A B =
      ⋃ p, profileOfScores ⁻¹' {p} ∩ F p := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨profileOfScores x, rfl, hx⟩
    · intro hx
      obtain ⟨p, hp, h⟩ := mem_iUnion.mp hx
      have hp' : profileOfScores x = p := hp
      subst p
      exact h
  rw [he]
  exact MeasurableSet.iUnion fun p ↦
    ((measurable_profileOfScores n) (measurableSet_singleton p)).inter (hF p)

/-- Outside the global exceptions, every anchor in the certified score
and length band passes the local eligibility test. -/
theorem locallyEligiblePivotAbundance_of_good {n : ℕ} (hn : 0 < n) {b A B : ℝ}
    {x : ScoreProfile n} (ht : ∀ row, Function.Injective (x row))
    (hG : x ∈ goodPivotScoreGeometry n)
    (hE : x ∈ scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)
    (hBm : 49 * A + 1 ≤ B) (hBi : 4 * (8 * A + 1) ≤ B)
    (hM : x ∉ badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt n))
    (hI : x ∉ badShortStablePivot pivotNormalizedForwardIncrement A
      ((4 * (8 * A + 1)) * Real.sqrt n)) :
    x ∈ locallyEligiblePivotAbundance n b A B := by
  obtain ⟨S, hcard, hS⟩ := hE
  refine ⟨S, hcard, fun r hr ↦ ?_⟩
  let hopt := DAState.isManOptimal_matching (profileOfScores x)
  let m := singletonRotationAnchor hopt r
  let σ := r.val.cycle
  have hσ : IsSoleForwardExposedRotation (profileOfScores x) m.val σ :=
    ⟨(isExposedRotation_singletonRotationAnchor_iff hopt r σ).mpr rfl,
      fun τ hτ ↦ (isExposedRotation_singletonRotationAnchor_iff hopt r τ).mp hτ⟩
  obtain ⟨hlo, hhi, hband⟩ := hS r hr
  have hd := splitScorePairs_mem_pivotCutoffDiagonal hn hG m.val m.property hband
  have hstable := (isStable_profileOfScores_iff ht m.val).mp m.property
  have hm : pivotMaleSupportMass x m.val σ ≤ (49 * A + 1) / Real.sqrt n :=
    le_of_not_gt fun h ↦ hM ⟨m.val, hstable, hd, σ, hσ.1, hhi, h⟩
  have hi : pivotNormalizedForwardIncrement x m.val σ ≤ (4 * (8 * A + 1)) * Real.sqrt n :=
    le_of_not_gt fun h ↦ hI ⟨m.val, hstable, hd, σ, hσ.1, hhi, h⟩
  exact isLocallyEligiblePivot_of_good hn ht hG m.property hσ hband ⟨hlo, hhi⟩
    (hm.trans (div_le_div_of_nonneg_right hBm (Real.sqrt_nonneg _)))
    (hi.trans (mul_le_mul_of_nonneg_right hBi (Real.sqrt_nonneg _)))

/-- For every fixed tolerance one can choose fixed cutoffs with
square-root times logarithmic abundance of locally eligible anchors. -/
theorem exists_eventually_measure_badLocallyEligiblePivotAbundance_le {η : ℝ}
    (hη : 0 < η) :
    ∃ b A B : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤ ENNReal.ofReal η := by
  obtain ⟨b, A, hb, hb₁, hA, hband⟩ :=
    exists_eventually_measure_badScoreWalkAnchorAbundance_le (η := η / 2) (by positivity)
  let B := max (49 * A + 1) (4 * (8 * A + 1))
  have hB : 0 < B := lt_of_lt_of_le (by linarith : 0 < 49 * A + 1) (le_max_left _ _)
  refine ⟨b, A, B, hb, hb₁, hA, hB, ?_⟩
  have hrare := tendsto_measure_badPivotScoreGeometry_zero.add
    ((tendsto_measure_badShortStablePivotMaleMass A).add
      (tendsto_measure_badShortStablePivotForwardIncrement A))
  simp only [add_zero] at hrare
  filter_upwards [hband, hrare.eventually_lt_const (ENNReal.ofReal_pos.mpr
    (show 0 < η / 2 by positivity)), eventually_gt_atTop (0 : ℕ)] with n hn hsmall hnpos
  let E := scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A
  let G := goodPivotScoreGeometry n
  let M : Set (ScoreProfile n) :=
    badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt (n : ℝ))
  let I : Set (ScoreProfile n) := badShortStablePivot pivotNormalizedForwardIncrement A
    ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ))
  let U : Set (ScoreProfile n) := Eᶜ ∪ (Gᶜ ∪ (M ∪ I))
  have hsub : (locallyEligiblePivotAbundance n b A B)ᶜ ≤ᵐ[continuousScoreLaw n] U := by
    filter_upwards [ae_injective_rows n] with x ht hbad
    by_contra hx
    have hE : x ∈ E := by
      by_contra h
      exact hx (Or.inl h)
    have hG : x ∈ G := by
      by_contra h
      exact hx (Or.inr (Or.inl h))
    have hM : x ∉ M := fun h ↦ hx (Or.inr (Or.inr (Or.inl h)))
    have hI : x ∉ I := fun h ↦ hx (Or.inr (Or.inr (Or.inr h)))
    exact hbad (locallyEligiblePivotAbundance_of_good hnpos ht hG hE
      (le_max_left _ _) (le_max_right _ _) hM hI)
  calc
    _ ≤ continuousScoreLaw n (Eᶜ ∪ (Gᶜ ∪ (M ∪ I))) := measure_mono_ae hsub
    _ ≤ continuousScoreLaw n Eᶜ +
        (continuousScoreLaw n Gᶜ + (continuousScoreLaw n M + continuousScoreLaw n I)) := by
      exact (measure_union_le Eᶜ _).trans (add_le_add le_rfl
        ((measure_union_le Gᶜ _).trans (add_le_add le_rfl (measure_union_le M I))))
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hn hsmall.le
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The abundance parameters and the strictly smaller reverse-decoration
support coefficient can be chosen together in the needed order. -/
theorem exists_eligiblePivotAbundance_and_supportCoefficient {η : ℝ} (hη : 0 < η) :
    ∃ b A B κ : ℝ, 0 < b ∧ b ≤ 1 ∧ 1 ≤ A ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
      24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 ∧
      ∀ᶠ n : ℕ in atTop,
        continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤ ENNReal.ofReal η := by
  obtain ⟨b, A, B, hb, hb₁, hA, hB, hab⟩ :=
    exists_eventually_measure_badLocallyEligiblePivotAbundance_le hη
  obtain ⟨κ, hκ, hκb, hlabel, hcompat⟩ := exists_localPivotSupportCoefficient hb hB.le
  exact ⟨b, A, B, κ, hb, hb₁, hA, hB, hκ, hκb, hlabel, hcompat, hab⟩

end LennonPittelFormalization

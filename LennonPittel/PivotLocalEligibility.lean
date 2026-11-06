module

public import LennonPittel.PivotSpouseSquareRegularity
public import LennonPittel.PivotForwardForest

/-!
# Local eligibility of a singleton pivot

Eligibility uses only a fixed matching's spouse diagonal, forward mask, and
revealed male scores. Simultaneous regularity over all stable matchings is
used to verify eligibility, but is not part of the event on which we condition.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The diagonal and mask tests at a fixed pivot. -/
structure LocalPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) : Prop where
  base : d ∈ pivotBaseDiagonalBand n
  lower_band : (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d
  length_lower : b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ)
  length_upper : (ρ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ)
  male_squares : (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤
    ENNReal.ofReal (24 / (n : ℝ))
  female_squares : (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ)
  omitted_score : ∀ j, forwardMaskOmittedMass d flag j ≤
    (n : ℝ) ^ (-11 / 20 : ℝ) * reverseDiagonalMaleTotal d
  pivot_score : (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤
    (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal d

/-- The unnormalized increment cap at a fixed spouse diagonal. -/
noncomputable def localPivotIncrementCap {n : ℕ} (B : ℝ) (d : DiagonalScorePairs n) : ℝ :=
  B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal d

/-- The local test on a fixed diagonal, mask and active male observations. -/
def IsLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (x : ScoreProfile n)
    (μ ρ : Matching n) : Prop :=
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  LocalPivotGeometry b A B μ ρ z.1 flag ∧
    (forwardRevealWithColumns flag z.2).1 ∈
      eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)

/-- On a fixed mask fiber the local test splits into a diagonal condition and
the measurable restriction on the revealed coordinates. -/
theorem isLocallyEligiblePivot_reconstruct_iff {n : ℕ} {b A B : ℝ}
    (μ ρ : Matching n) (d : DiagonalScorePairs n) (z : OffDiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (hmask : z ∈ forwardScoreMaskEvent d flag) :
    IsLocallyEligiblePivot b A B ((splitScorePairs μ).symm (d, z)) μ ρ ↔
      LocalPivotGeometry b A B μ ρ d flag ∧
        (forwardRevealWithColumns flag z).1 ∈
          eligiblePivotRevealSet d flag ρ (localPivotIncrementCap B d) := by
  have hflag := (forwardMaskOfScores_eq_iff d z flag).mpr hmask
  unfold IsLocallyEligiblePivot
  rw [MeasurableEquiv.apply_symm_apply]
  dsimp only
  rw [hflag]

/-- On tie-free scores, the revealed singleton cycle is the actual sole
exposed rotation at the marked matching. -/
theorem IsLocallyEligiblePivot.isSoleForwardExposed {n : ℕ} {b A B : ℝ}
    {x : ScoreProfile n} {μ ρ : Matching n}
    (h : IsLocallyEligiblePivot b A B x μ ρ)
    (ht : ∀ row, Function.Injective (x row)) :
    IsSoleForwardExposedRotation (profileOfScores x) μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  have hmask : z.2 ∈ forwardScoreMaskEvent z.1 flag :=
    (forwardMaskOfScores_eq_iff _ _ _).mp rfl
  have he (τ : Matching n) := (isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag ht
    hmask).trans (h.2.1 τ)
  exact ⟨(he ρ).mpr rfl, fun τ hτ ↦ (he τ).mp hτ⟩

theorem reverseDiagonalMaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    reverseDiagonalMaleTotal (splitScorePairs μ x).1 = maleSpouseTotal x μ :=
  Finset.sum_congr rfl fun i _ ↦ congrArg Prod.fst (diagonalPairAt_splitScorePairs μ x i)

theorem pivotDiagonalFemaleTotal_splitScorePairs {n : ℕ}
    (μ : Matching n) (x : ScoreProfile n) :
    pivotDiagonalFemaleTotal (splitScorePairs μ x).1 = femaleSpouseTotal x μ := by
  rw [femaleSpouseTotal_eq_sum_byHusband]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [diagonalPairAt_splitScorePairs, femaleSpouseByHusband, femaleSpouseScore,
    Equiv.symm_apply_apply]

/-- The realized support weight, in the normalization used by the cutoff. -/
noncomputable def pivotMaleSupportMass {n : ℕ} (x : ScoreProfile n) (μ ρ : Matching n) : ℝ :=
  ∑ i ∈ ρ.support, maleSpouseScore x μ i / maleSpouseTotal x μ

/-- The realized forward male increment total in the female-score scale. -/
noncomputable def pivotNormalizedForwardIncrement {n : ℕ}
    (x : ScoreProfile n) (μ ρ : Matching n) : ℝ :=
  femaleSpouseTotal x μ *
    ∑ i ∈ ρ.support, (x (.inl i) (μ (ρ i)) - x (.inl i) (μ i))

/-- A stable mark passing the simultaneous regularity and both pivot-specific
tests satisfies the entirely local definition. -/
theorem isLocallyEligiblePivot_of_good {n : ℕ} (hn : 0 < n) {b A B : ℝ}
    {x : ScoreProfile n} {μ ρ : Matching n}
    (ht : ∀ row, Function.Injective (x row))
    (hx : x ∈ goodPivotScoreGeometry n) (hμ : IsStable (profileOfScores x) μ)
    (hρ : IsSoleForwardExposedRotation (profileOfScores x) μ ρ)
    (hband : femaleSpouseTotal x μ ∈
      Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ)))
    (hlen : (ρ.support.card : ℝ) ∈ Icc (b * Real.sqrt (n : ℝ)) (A * Real.sqrt (n : ℝ)))
    (hmass : pivotMaleSupportMass x μ ρ ≤ B / Real.sqrt (n : ℝ))
    (hinc : pivotNormalizedForwardIncrement x μ ρ ≤ B * Real.sqrt (n : ℝ)) :
    IsLocallyEligiblePivot b A B x μ ρ := by
  let z := splitScorePairs μ x
  let flag := forwardMaskOfScores z.1 z.2
  let v := (forwardRevealWithColumns flag z.2).1
  have hmask : z.2 ∈ forwardScoreMaskEvent z.1 flag :=
    (forwardMaskOfScores_eq_iff _ _ _).mp rfl
  obtain ⟨hd, hmaskBound⟩ := hx.1.2.2 μ hμ hband.2
  obtain ⟨hmale, hfemale⟩ := spouseSquareWeights_of_goodPivotScoreGeometry hn hx μ hμ
  have hY : 0 < pivotDiagonalFemaleTotal z.1 := lt_of_lt_of_le (by norm_num) hd.2.1
  have hX : 0 < reverseDiagonalMaleTotal z.1 :=
    pos_of_mul_pos_left ((div_pos (Nat.cast_pos.mpr hn) (by norm_num)).trans_le hd.2.2.2.1) hY.le
  have hXeq := reverseDiagonalMaleTotal_splitScorePairs μ x
  have hYeq := pivotDiagonalFemaleTotal_splitScorePairs μ x
  have hshare (i : Fin n) : forwardSpouseWeight z.1 i =
      femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
    rw [forwardSpouseWeight, diagonalPairAt_splitScorePairs]
    change x (.inr (μ i)) i / pivotDiagonalFemaleTotal z.1 = _
    rw [hYeq, femaleSpouseScore, Equiv.symm_apply_apply]
  have hfemale' : (∑ i, (forwardSpouseWeight z.1 i) ^ 2) ≤ 24 / (n : ℝ) := by
    simp_rw [hshare]
    rwa [Equiv.sum_comp μ (fun j ↦ (femaleSpouseScore x μ j / femaleSpouseTotal x μ) ^ 2)]
  have hpivot : (∑ i ∈ ρ.support, (diagonalPairAt z.1 i).1) ≤
      (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal z.1 := by
    have hm : (∑ i ∈ ρ.support, (diagonalPairAt z.1 i).1) /
        reverseDiagonalMaleTotal z.1 ≤ B / Real.sqrt (n : ℝ) := by
      rw [Finset.sum_div, hXeq]
      simpa only [z, pivotMaleSupportMass, diagonalPairAt_splitScorePairs, maleSpouseScore]
        using hmass
    exact (div_le_iff₀ hX).mp hm
  refine ⟨⟨hd, by rw [hYeq]; exact hband.1, hlen.1, hlen.2, hmale, hfemale',
    fun j ↦ forwardMaskOmittedMass_le_of_notMem_badForwardMask z.1 hmaskBound j, hpivot⟩,
    ?_, ?_, ?_⟩
  · intro τ
    rw [← isExposedRotation_iff_forwardRevealExposureEvent μ τ x flag ht hmask]
    exact ⟨hρ.2 τ, fun h ↦ h.symm ▸ hρ.1⟩
  · intro i hi
    have hne := Equiv.Perm.mem_support.mp hi
    rw [forwardPivotIncrement_eq_of_exposed μ ρ x flag ht hmask hρ.1 hne]
    exact sub_nonneg.mpr ((rankPermutation_lt_iff (ht (.inl i)) _ _).mp
      (hρ.1.successor i hne).eligible.1).le
  · have he : (∑ i ∈ ρ.support, forwardPivotIncrement z.1 flag ρ v i) =
        ∑ i ∈ ρ.support, (x (.inl i) (μ (ρ i)) - x (.inl i) (μ i)) :=
      Finset.sum_congr rfl fun i hi ↦ forwardPivotIncrement_eq_of_exposed μ ρ x flag ht hmask
        hρ.1 (Equiv.Perm.mem_support.mp hi)
    change (∑ i ∈ ρ.support, forwardPivotIncrement z.1 flag ρ v i) ≤
      B * Real.sqrt (n : ℝ) / pivotDiagonalFemaleTotal z.1
    rw [he]
    apply (le_div_iff₀ hY).mpr
    rw [mul_comm, hYeq]
    exact hinc

/-- The local diagonal and mask satisfy the inputs of the filtered moment
uniformly over the matching and pivot, outside a fixed finite size range. -/
theorem eventually_localPivotGeometry_certificate (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ {b A : ℝ} (μ ρ : Matching n) (d : DiagonalScorePairs n)
      (flag : OffDiagonalCellIndex n → Bool), LocalPivotGeometry b A B μ ρ d flag →
      (∀ᵐ z ∂offDiagonalScoreLaw n,
        ∀ row, Function.Injective ((splitScorePairs μ).symm (d, z) row)) →
      EligibleReverseMomentCertificate μ ρ d flag (K n) (L n) (localPivotIncrementCap B d)
        (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
        (B / Real.sqrt (n : ℝ)) := by
  have hc : 0 < (1 / 128 : ℝ) := by norm_num
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ (1 / 128 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) :=
    ((((tendsto_rpow_atTop (by norm_num : 0 < (3 / 5 : ℝ))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc).eventually_ge_atTop 2)
  filter_upwards [eventually_eligibleReverseMomentCertificate K L
    (Cx := 2048) (H := 24) (V := B / (1 / 128)) (by norm_num) (by norm_num) hB
    (div_nonneg hB hc.le) hκ hc hK hL hsmallLabel hsmallCompat,
    hlarge, eventually_gt_atTop (0 : ℕ)] with n hcert hlarge hn
  intro b A μ ρ d flag hgeom ht
  have hY : 0 < pivotDiagonalFemaleTotal d := lt_of_lt_of_le (by norm_num) hgeom.base.2.1
  have hXY : (1 / 128 : ℝ) * n ≤ reverseDiagonalMaleTotal d * pivotDiagonalFemaleTotal d := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact hgeom.base.2.2.2.1
  have hXrate := reverseMaleTotal_ge_of_scoreBand hn hc.le hY hgeom.base.2.2.1 hXY
  have hX : 0 < reverseDiagonalMaleTotal d := lt_of_lt_of_le (by norm_num) (hlarge.trans hXrate)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from hn))
  have hgeometry : ReverseMaskGeometry d flag ρ (2048 * Real.log (n : ℝ) / n)
      ((n : ℝ) ^ (-11 / 20 : ℝ)) (B / Real.sqrt (n : ℝ)) := by
    refine ⟨hgeom.base.1, hlarge.trans hXrate, ?_, by positivity, by positivity, ?_,
      hgeom.omitted_score, hgeom.pivot_score⟩
    · exact div_nonneg (mul_nonneg (by norm_num) hlog) (Nat.cast_nonneg _)
    · intro i
      apply (div_le_iff₀ hX).mp
      exact normalizedMaleScore_le_of_spouseProduct hn hgeom.base.2.1 hgeom.base.2.2.2.1
        (hgeom.base.2.2.2.2.2 i)
  have hD : pivotDiagonalFemaleTotal d * localPivotIncrementCap B d ≤ B * Real.sqrt (n : ℝ) := by
    rw [localPivotIncrementCap, mul_comm, div_mul_cancel₀ _ hY.ne']
  exact hcert μ ρ d flag _ hgeometry hXrate hgeom.male_squares
    (reversePivotIncrementRatio_le_of_scoreProduct hn hc hX hY hB hXY hD) ht

/-- The support cutoff can lie strictly below the smallest eligible pivot
while meeting the two numerical constraints in the local moment bound. -/
theorem exists_localPivotSupportCoefficient {b B : ℝ} (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ κ, 0 < κ ∧ κ < b ∧ 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
      Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 :=
  exists_eligibleSupportCoefficient hb (by norm_num) hB (by positivity)

/-- At almost every diagonal the local certificate applies without a separate
tie-freeness premise on reconstructed rows. -/
theorem eventually_ae_diagonal_localPivotGeometry_certificate (K L : ℕ → ℕ)
    {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : Tendsto L atTop atTop)
    (hsmallLabel : 24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4)
    (hsmallCompat : Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32) :
    ∀ᶠ n : ℕ in atTop, ∀ μ : Matching n, ∀ᵐ d ∂diagonalScoreLaw n,
      ∀ {b A : ℝ} (ρ : Matching n) (flag : OffDiagonalCellIndex n → Bool),
        LocalPivotGeometry b A B μ ρ d flag →
        EligibleReverseMomentCertificate μ ρ d flag (K n) (L n) (localPivotIncrementCap B d)
          (2048 * Real.log (n : ℝ) / n) ((n : ℝ) ^ (-11 / 20 : ℝ))
          (B / Real.sqrt (n : ℝ)) := by
  filter_upwards [eventually_localPivotGeometry_certificate K L hB hκ hK hL hsmallLabel
    hsmallCompat] with n hn μ
  filter_upwards [ae_diagonal_ae_injective_scoreRows μ] with d ht b A ρ flag hgeom
  exact hn μ ρ d flag hgeom ht

private theorem measurable_diagonalMaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).1) :=
  (measurable_pi_apply _).fst

private theorem measurable_diagonalFemaleScore {n : ℕ} (i : Fin n) :
    Measurable (fun d : DiagonalScorePairs n ↦ (diagonalPairAt d i).2) :=
  (measurable_pi_apply _).snd

private theorem measurable_reverseDiagonalMaleTotal (n : ℕ) :
    Measurable (@reverseDiagonalMaleTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_diagonalMaleScore i

private theorem measurable_pivotDiagonalFemaleTotal (n : ℕ) :
    Measurable (@pivotDiagonalFemaleTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_diagonalFemaleScore i

/-- The local geometry is measurable as a function of the spouse diagonal
when the mask is held fixed. -/
theorem measurableSet_localPivotGeometry {n : ℕ} (b A B : ℝ) (μ ρ : Matching n)
    (flag : OffDiagonalCellIndex n → Bool) :
    MeasurableSet {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} := by
  have hmale (j : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ reverseSpouseWeights μ d j) :=
    ENNReal.measurable_ofReal.comp ((measurable_diagonalMaleScore (μ.symm j)).div
      (measurable_reverseDiagonalMaleTotal n))
  have hfemale (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ forwardSpouseWeight d i) :=
    (measurable_diagonalFemaleScore i).div (measurable_pivotDiagonalFemaleTotal n)
  have homit (j : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦
      forwardMaskOmittedMass d flag j) := by
    unfold forwardMaskOmittedMass
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    split
    · exact measurable_diagonalMaleScore i.val
    · exact measurable_const
  have hEq : {d : DiagonalScorePairs n | LocalPivotGeometry b A B μ ρ d flag} =
      {d | d ∈ pivotBaseDiagonalBand n ∧
        (n : ℝ) ^ (1 / 10 : ℝ) ≤ pivotDiagonalFemaleTotal d ∧
        b * Real.sqrt (n : ℝ) ≤ (ρ.support.card : ℝ) ∧
        (ρ.support.card : ℝ) ≤ A * Real.sqrt (n : ℝ) ∧
        (∑ j, (reverseSpouseWeights μ d j) ^ 2) ≤ ENNReal.ofReal (24 / (n : ℝ)) ∧
        (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) ∧
        (∀ j, forwardMaskOmittedMass d flag j ≤
          (n : ℝ) ^ (-11 / 20 : ℝ) * reverseDiagonalMaleTotal d) ∧
        (∑ i ∈ ρ.support, (diagonalPairAt d i).1) ≤
          (B / Real.sqrt (n : ℝ)) * reverseDiagonalMaleTotal d} := by
    ext d
    exact ⟨fun h ↦ ⟨h.base, h.lower_band, h.length_lower, h.length_upper, h.male_squares,
      h.female_squares, h.omitted_score, h.pivot_score⟩,
      fun ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩
  rw [hEq]
  simp only [ofPred_and, ofPred_forall, Set.ofPred_mem_eq]
  exact (measurableSet_pivotBaseDiagonalBand n).inter <|
    (measurableSet_le measurable_const (measurable_pivotDiagonalFemaleTotal n)).inter <|
    (MeasurableSet.const _).inter <| (MeasurableSet.const _).inter <|
    (measurableSet_le (Finset.measurable_sum _ fun j _ ↦ (hmale j).pow_const _)
      measurable_const).inter <|
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ (hfemale i).pow_const _)
      measurable_const).inter <|
    (MeasurableSet.iInter fun j ↦ measurableSet_le (homit j)
      (measurable_const.mul (measurable_reverseDiagonalMaleTotal n))).inter <|
    measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_diagonalMaleScore i)
      (measurable_const.mul (measurable_reverseDiagonalMaleTotal n))

private theorem measurable_jointForwardPivotIncrement {n : ℕ}
    (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) (m : Fin n) :
    Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      forwardPivotIncrement z.1 flag ρ z.2 m) := by
  by_cases hm : ρ m ≠ m
  · let q : OffDiagonalCellIndex n := ⟨(m, ρ m), hm.symm⟩
    by_cases hq : flag q = true
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) = true := hq
      simp only [forwardPivotIncrement, dite_eq_left hm, dite_eq_left hq']
      exact (((measurable_pi_apply (⟨q, hq⟩ : ForwardActiveCellIndex flag)).comp
          (measurable_snd : Measurable (@Prod.snd (DiagonalScorePairs n) _))).sub
          ((measurable_diagonalMaleScore m).comp measurable_fst))
    · have hq' : flag (⟨(m, ρ m), hm.symm⟩ : OffDiagonalCellIndex n) ≠ true := hq
      simp only [forwardPivotIncrement, dite_eq_left hm, dite_eq_right hq']
      exact measurable_const
  · simp only [forwardPivotIncrement, dite_eq_right hm]
    exact measurable_const

/-- The reveal event is jointly measurable in the diagonal and active observations
for each fixed mask. -/
theorem measurableSet_jointEligiblePivotReveal {n : ℕ}
    (B : ℝ) (flag : OffDiagonalCellIndex n → Bool) (ρ : Matching n) :
    MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      z.2 ∈ eligiblePivotRevealSet z.1 flag ρ (localPivotIncrementCap B z.1)} := by
  have hs : MeasurableSet {v : ForwardRevealedMaleScores flag |
      ∀ τ : Matching n, v ∈ forwardRevealExposureEvent τ flag ↔ τ = ρ} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun τ ↦ ?_
    by_cases ht : τ = ρ
    · simpa only [ht, iff_true, ofPred_mem_eq] using
        measurableSet_forwardRevealExposureEvent ρ flag
    · simpa only [ht, iff_false, ← mem_compl_iff, ofPred_mem_eq] using
        (measurableSet_forwardRevealExposureEvent τ flag).compl
  have hcap : Measurable (fun z : DiagonalScorePairs n × ForwardRevealedMaleScores flag ↦
      localPivotIncrementCap B z.1) :=
    measurable_const.div ((measurable_pivotDiagonalFemaleTotal n).comp measurable_fst)
  have hnonneg : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      ∀ m ∈ ρ.support, 0 ≤ forwardPivotIncrement z.1 flag ρ z.2 m} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le measurable_const (measurable_jointForwardPivotIncrement flag ρ m)
  have hsum : MeasurableSet {z : DiagonalScorePairs n × ForwardRevealedMaleScores flag |
      (∑ m ∈ ρ.support, forwardPivotIncrement z.1 flag ρ z.2 m) ≤
        localPivotIncrementCap B z.1} :=
    measurableSet_le (Finset.measurable_sum _ fun m _ ↦
      measurable_jointForwardPivotIncrement flag ρ m) hcap
  exact (measurable_snd hs).inter (hnonneg.inter hsum)

/-- The forward eligibility mask is jointly measurable in spouse and off-diagonal scores. -/
theorem measurable_jointForwardMaskOfScores (n : ℕ) :
    Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2) := by
  apply Measurable.of_eval
  intro q
  apply measurable_to_bool
  have hz : Measurable (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦ z.2 q) :=
    (measurable_pi_apply q).comp measurable_snd
  have he : (fun z : DiagonalScorePairs n × OffDiagonalScorePairs n ↦
      forwardMaskOfScores z.1 z.2 q) ⁻¹' {true} =
      {z | (diagonalPairAt z.1 q.val.1).1 < (z.2 q).1} ∩
      {z | (z.2 q).2 < (diagonalPairAt z.1 q.val.2).2} := by
    ext z
    exact forwardCellFlag_eq_true.trans Set.mem_prod
  rw [he]
  exact (measurableSet_lt ((measurable_diagonalMaleScore _).comp measurable_fst) hz.fst).inter
    (measurableSet_lt hz.snd ((measurable_diagonalFemaleScore _).comp measurable_fst))

/-- At a fixed labeled mark and pivot, the actual local eligibility event is measurable. -/
theorem measurableSet_isLocallyEligiblePivot {n : ℕ} (b A B : ℝ) (μ ρ : Matching n) :
    MeasurableSet {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} := by
  let Z := splitScorePairs μ
  let mask (x : ScoreProfile n) := forwardMaskOfScores (Z x).1 (Z x).2
  let E (flag : OffDiagonalCellIndex n → Bool) := {x : ScoreProfile n | mask x = flag ∧
    LocalPivotGeometry b A B μ ρ (Z x).1 flag ∧
    (forwardRevealWithColumns flag (Z x).2).1 ∈
      eligiblePivotRevealSet (Z x).1 flag ρ (localPivotIncrementCap B (Z x).1)}
  have hmask : Measurable mask := (measurable_jointForwardMaskOfScores n).comp Z.measurable
  have hE : {x : ScoreProfile n | IsLocallyEligiblePivot b A B x μ ρ} = ⋃ flag, E flag := by
    ext x
    refine ⟨fun h ↦ mem_iUnion.mpr ⟨mask x, rfl, h.1, h.2⟩, fun h ↦ ?_⟩
    obtain ⟨f, hf, hg, hv⟩ := mem_iUnion.mp h
    subst f
    exact ⟨hg, hv⟩
  rw [hE]
  refine MeasurableSet.iUnion fun flag ↦ (hmask (measurableSet_singleton flag)).inter
    ((((measurable_fst.comp Z.measurable) (measurableSet_localPivotGeometry b A B μ ρ flag))).inter ?_)
  exact (measurableSet_jointEligiblePivotReveal B flag ρ).preimage
    ((measurable_fst.comp Z.measurable).prodMk
      (measurable_fst.comp ((measurable_forwardRevealWithColumns flag).comp
        (measurable_snd.comp Z.measurable))))

end LennonPittelFormalization

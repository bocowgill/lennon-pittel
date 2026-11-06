module

public import LennonPittel.CoexposureScoreRefutation
public import LennonPittel.PivotSpouseProductLower

/-!
# Non-tiny scores on long exposed rotations

A long rotation contains an orbit segment of fixed length with distinct sources.
The mass of each segment of tiny-target arcs is bounded using the independent
rows of the fixed-matching stable score law. A union bound over segments and
then over stable marks shows that long all-tiny rotations are rare.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology

namespace LennonPittelFormalization

/-- A normalized female spouse score below this cutoff is tiny. -/
noncomputable def nonTinyRotationShare (n : ℕ) : ℝ := (n : ℝ) ^ (-(21 / 20) : ℝ)

/-- A long cycle has a fixed-length orbit segment without repeated vertices. -/
private theorem cycle_has_injective_segment {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : σ.IsCycle) (hk : k + 1 ≤ σ.support.card) :
    ∃ a : Fin (k + 1) → Fin n, Function.Injective a ∧
      (∀ i, a i ∈ σ.support) ∧ ∀ t : Fin k, σ (a t.castSucc) = a t.succ := by
  have hc : σ.IsCycleOn (↑σ.support : Set (Fin n)) := by
    simpa only [Equiv.Perm.coe_support_eq_set_support] using hσ.isCycleOn
  obtain ⟨i, hi, -⟩ := hσ
  have hi' := Equiv.Perm.mem_support.mpr hi
  let a (t : Fin (k + 1)) := (σ ^ t.val) i
  refine ⟨a, ?_, fun j ↦ Equiv.Perm.pow_apply_mem_support.mpr hi', ?_⟩
  · intro s t hst
    have hh := (hc.pow_apply_eq_pow_apply hi').mp hst
    unfold Nat.ModEq at hh
    rw [Nat.mod_eq_of_lt (s.isLt.trans_le hk), Nat.mod_eq_of_lt (t.isLt.trans_le hk)] at hh
    exact Fin.ext hh
  · intro t
    change σ ((σ ^ t.val) i) = (σ ^ (t.val + 1)) i
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- The product law on distinct source rows pays one factor per edge of a segment. -/
private theorem measure_segment_le_of_pi {n k : ℕ} {β : Fin n → Type*}
    [∀ i, MeasurableSpace (β i)] (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (ν i)]
    (T : (i : Fin n) → Fin n → Set (β i)) (a : Fin (k + 1) → Fin n)
    (ha : Function.Injective a) (c : ℝ≥0∞)
    (hm : ∀ t : Fin k, ν (a t.castSucc) (T (a t.castSucc) (a t.succ)) ≤
      ν (a t.castSucc) univ * c) :
    (Measure.pi ν) {x | ∀ t : Fin k, x (a t.castSucc) ∈ T (a t.castSucc) (a t.succ)} ≤
      (∏ i, ν i univ) * c ^ k := by
  let f : Fin k → Fin n := a ∘ Fin.castSucc
  have hf : Function.Injective f := ha.comp (Fin.castSucc_injective _)
  let s := Finset.univ.image f
  have hfind (i : Fin n) (hi : i ∈ s) : ∃ t, f t = i := by
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hi
    exact ⟨t, ht⟩
  let B (i : Fin n) : Set (β i) :=
    if hi : i ∈ s then T i (a (Classical.choose (hfind i hi)).succ) else univ
  have hcard : s.card = k := by simp [s, Finset.card_image_of_injective _ hf]
  have hsub : {x | ∀ t : Fin k, x (a t.castSucc) ∈ T (a t.castSucc) (a t.succ)} ⊆
      univ.pi B := by
    intro x hx
    have hx' (t : Fin k) (i : Fin n) (hi : a t.castSucc = i) :
        x i ∈ T i (a t.succ) := hi ▸ hx t
    refine Set.mem_pi.mpr fun i _ ↦ ?_
    by_cases hi : i ∈ s
    · rw [show B i = T i (a (Classical.choose (hfind i hi)).succ) by simp only [B, dite_eq_left hi]]
      let t := Classical.choose (hfind i hi)
      have ht : a t.castSucc = i := Classical.choose_spec (hfind i hi)
      exact hx' t i ht
    · simp only [B, dite_eq_right hi, mem_univ]
  calc
    _ ≤ (Measure.pi ν) (univ.pi B) := measure_mono hsub
    _ = ∏ i, ν i (B i) := Measure.pi_pi ν B
    _ ≤ ∏ i, ν i univ * (if i ∈ s then c else 1) := by
      apply Finset.prod_le_prod
      intro i _
      by_cases hi : i ∈ s
      · let t := Classical.choose (hfind i hi)
        have ht : a t.castSucc = i := Classical.choose_spec (hfind i hi)
        rw [show B i = T i (a t.succ) by simp only [B, dite_eq_left hi, t], ite_eq_left hi]
        exact ht ▸ hm t
      · simp only [B, dite_eq_right hi, ite_eq_right hi, mul_one, le_rfl]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
        Finset.prod_const, hcard]

/-- A fixed matching exposes a long cycle all of whose participants are tiny. -/
def hasAllTinyLongRotation {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : Prop :=
  ∃ σ : Matching n, 81 ≤ σ.support.card ∧ IsExposedRotation (profileOfScores x) μ σ ∧
    ∀ i : {j : Fin n // j ∈ σ.support},
      femaleSpouseScore x μ (μ i.val) / femaleSpouseTotal x μ < nonTinyRotationShare n

private theorem measurableSet_hasAllTinyLongRotation {n : ℕ} (μ : Matching n) :
    MeasurableSet {x | hasAllTinyLongRotation x μ} := by
  classical
  unfold hasAllTinyLongRotation
  simp only [ofPred_exists, ofPred_and, ofPred_forall]
  refine MeasurableSet.iUnion fun σ : Matching n ↦ ?_
  have hs : MeasurableSet {a : ScoreProfile n |
      IsExposedRotation (profileOfScores a) μ σ} :=
    measurable_profileOfScores n (MeasurableSet.of_discrete :
      MeasurableSet {p : Profile n | IsExposedRotation p μ σ})
  exact (MeasurableSet.const _).inter (hs.inter (MeasurableSet.iInter fun i ↦
    measurableSet_lt ((measurable_femaleSpouseScore μ (μ i.val)).div
      (measurable_femaleSpouseTotal μ)) measurable_const))

private theorem diagonalFemaleShare_reconstruct {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n) (i : Fin n) :
    let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
    femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ =
      (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2 := by
  let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
  have he : (splitScorePairs μ x).1 = d := by simp [x]
  have hj (j : Fin n) : (diagonalPairAt d j).2 = femaleSpouseScore x μ (μ j) := by
    rw [← he, diagonalPairAt_splitScorePairs, femaleSpouseScore, Equiv.symm_apply_apply]
  change femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ = _
  rw [show femaleSpouseTotal x μ = ∑ j, femaleSpouseScore x μ (μ j) by
      exact (Equiv.sum_comp μ (femaleSpouseScore x μ)).symm]
  simp_rw [hj]

private theorem measure_diagonal_allTiny_le {n : ℕ} (μ : Matching n)
    {d : DiagonalScorePairs n} (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico (0 : ℝ) 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc (0 : ℝ) 1)
    (hδsmall : coexposureSuccessorPerturbation n ≤ 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n) (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n)
    (hrow : ∀ᵐ r ∂Measure.pi (stableScoreRowLaw d),
      let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
      (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ) :
    (Measure.pi (stableScoreRowLaw d))
      {r | hasAllTinyLongRotation
        ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ} ≤
      (∏ i, stableScoreRowLaw d i univ) *
        ((n : ℝ≥0∞) ^ 81 * ENNReal.ofReal (2 * nonTinyRotationShare n) ^ 80) := by
  classical
  let T (i j : Fin n) := if hij : i ≠ j then scoreRowSuccessorEvent d i ⟨j, hij⟩ else ∅
  let w (j : Fin n) := (diagonalPairAt d j).2 / ∑ l, (diagonalPairAt d l).2
  let Q (a : Fin 81 → Fin n) := Function.Injective a ∧
    ∀ t : Fin 80, w (a t.succ) < nonTinyRotationShare n
  let E (a : Fin 81 → Fin n) : Set (OffDiagonalScoreRows n) :=
    if Q a then {r | ∀ t : Fin 80, r (a t.castSucc) ∈ T (a t.castSucc) (a t.succ)} else ∅
  have hs : 0 ≤ ∑ l, (diagonalPairAt d l).2 :=
    Finset.sum_nonneg fun j _ ↦ (hy j).1
  have hw (j : Fin n) : 0 ≤ w j := div_nonneg (hy j).1 hs
  have hsub : {r | hasAllTinyLongRotation
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ} ≤ᵐ[
        Measure.pi (stableScoreRowLaw d)] ⋃ a, E a := by
    filter_upwards [hrow] with r hr hbad
    obtain ⟨σ, hlen, hσ, htiny⟩ := hbad
    obtain ⟨a, hinj, hmem, hnext⟩ := cycle_has_injective_segment hσ.isCycle
      (k := 80) hlen
    have hQ : Q a := ⟨hinj, fun t ↦ by
      dsimp only [w]
      rw [← diagonalFemaleShare_reconstruct μ d r (a t.succ)]
      exact htiny ⟨a t.succ, hmem t.succ⟩⟩
    refine mem_iUnion.mpr ⟨a, ?_⟩
    simp only [E, ite_eq_left hQ, mem_ofPred_eq]
    intro t
    have hmove := Equiv.Perm.mem_support.mp (hmem t.castSucc)
    have hsucc := hσ.successor _ hmove
    rw [hnext t] at hsucc
    have ht : a t.castSucc ≠ a t.succ :=
      fun hh ↦ (ne_of_lt t.castSucc_lt_succ) (hinj hh)
    simpa only [T, dite_eq_left ht] using
      scoreRowSuccessorEvent_of_isSuccessor_reconstructed μ d r _ ⟨_, ht⟩ hr.2 hr.1 hsucc
  have hE (a : Fin 81 → Fin n) :
      (Measure.pi (stableScoreRowLaw d)) (E a) ≤
        (∏ i, stableScoreRowLaw d i univ) * ENNReal.ofReal (2 * nonTinyRotationShare n) ^ 80 := by
    by_cases ha : Q a
    · simp only [E, ite_eq_left ha]
      refine measure_segment_le_of_pi (stableScoreRowLaw d) T a ha.1 _ fun t ↦ ?_
      have ht : a t.castSucc ≠ a t.succ :=
        fun hh ↦ (ne_of_lt t.castSucc_lt_succ) (ha.1 hh)
      simp only [T, dite_eq_left ht]
      refine (stableScoreRowLaw_successor_le_of_goodDiagonalScores hg hx hy hA hB hδ
        _ ⟨_, ht⟩).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _)
      change (1 + coexposureSuccessorPerturbation n) * w (a t.succ) ≤ _
      exact mul_le_mul (by linarith) (ha.2 t).le (hw _) (by norm_num)
    · simp [E, ha]
  calc
    _ ≤ (Measure.pi (stableScoreRowLaw d)) (⋃ a, E a) := measure_mono_ae hsub
    _ ≤ ∑' a, (Measure.pi (stableScoreRowLaw d)) (E a) := measure_iUnion_le E
    _ ≤ ∑ _a : Fin 81 → Fin n,
          (∏ i, stableScoreRowLaw d i univ) * ENNReal.ofReal (2 * nonTinyRotationShare n)^80 := by
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun a _ ↦ hE a
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ac_rfl

private theorem ae_diagonalMale_openUpper (n : ℕ) :
    ∀ᵐ d ∂diagonalScoreLaw n, ∀ i, (diagonalPairAt d i).1 ∈ Ico (0 : ℝ) 1 := by
  have hne : ∀ᵐ t ∂unitScoreLaw, t ≠ (1 : ℝ) := by rw [ae_iff]; simp
  have hu : ∀ᵐ t ∂unitScoreLaw, t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
      MeasurableSet (Icc (0 : ℝ) 1)), hne] with t ht hnt
    exact ⟨ht.1, lt_of_le_of_ne ht.2 hnt⟩
  have hp : ∀ᵐ z ∂unitScorePairLaw, z.1 ∈ Ico (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := unitScoreLaw)
      (ν := unitScoreLaw)).ae hu
  exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae
    (μ := fun _ : {q : ScorePairIndex n // q.1 = q.2} ↦ unitScorePairLaw)
    (i := ⟨(i,i), rfl⟩)).eventually hp

private theorem stableMass_eq_lintegral_nonTinyRows {n : ℕ} (μ : Matching n) :
    continuousScoreLaw n {x | IsScoreStable x μ} =
      ∫⁻ d, (∏ i, stableScoreRowLaw d i univ) ∂diagonalScoreLaw n := by
  have h := continuousScoreLaw_lintegral_stable_and_diagonal_rows μ
    (C := univ) MeasurableSet.univ (f := fun _ ↦ 1) measurable_const
  simpa only [mem_univ, and_true, Measure.restrict_univ, lintegral_one,
    Measure.restrict_apply_univ, Measure.pi_univ] using h

private theorem nonTiny_path_coefficient {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) ^ 81 * ENNReal.ofReal (2 * nonTinyRotationShare n) ^ 80 =
      ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_pow (Nat.cast_nonneg _) 81,
    ← ENNReal.ofReal_pow (by unfold nonTinyRotationShare; positivity) 80,
    ← ENNReal.ofReal_mul (by positivity)]
  apply congrArg ENNReal.ofReal
  unfold nonTinyRotationShare
  rw [mul_pow]
  calc
    _ = (2 : ℝ) ^ 80 * ((n : ℝ) ^ 81 * ((n : ℝ) ^ (-(21 / 20) : ℝ)) ^ 80) := by ac_rfl
    _ = _ := by
      rw [← Real.rpow_natCast (n : ℝ) 81, ← Real.rpow_mul_natCast hn'.le,
        ← Real.rpow_add hn']
      norm_num

/-- A fixed good stable mark's all-tiny event is suppressed by `2^80 / n^3`. -/
theorem eventually_measure_stable_allTinyLongRotation_le :
    ∀ᶠ n : ℕ in atTop, ∀ μ : Matching n,
      continuousScoreLaw n {x | IsScoreStable x μ ∧ GoodSpouseScores x μ ∧
        hasAllTinyLongRotation x μ} ≤
        continuousScoreLaw n {x | IsScoreStable x μ} *
          ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
  filter_upwards [eventually_coexposureSuccessorPerturbation_bounds] with n h
  rcases h with ⟨hn, -, hδsmall, hA, hB, hδ⟩
  intro μ
  let F : Set (ScoreProfile n) := {x | hasAllTinyLongRotation x μ}
  let C := goodDiagonalScores n
  let S : Set (ScoreProfile n) := {x | IsScoreStable x μ ∧ (splitScorePairs μ x).1 ∈ C}
  let c := ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ))
  have hF : MeasurableSet F := measurableSet_hasAllTinyLongRotation μ
  have hC : MeasurableSet C := measurableSet_goodDiagonalScores n
  have hδ₁ : coexposureSuccessorPerturbation n ≤ 1 := by
    refine hδsmall.trans ((div_le_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mpr ?_)
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hpre (d : DiagonalScorePairs n) :
      MeasurableSet {r | hasAllTinyLongRotation
        ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ} :=
    hF.preimage ((splitScorePairs μ).symm.measurable.comp
      (measurable_const.prodMk (offDiagonalRowsEquiv n).symm.measurable))
  calc
    _ = ∫⁻ x in S, F.indicator 1 x ∂continuousScoreLaw n := by
      rw [lintegral_indicator_one hF, Measure.restrict_apply hF]
      congr 1
      ext x
      simp only [F, S, C, mem_inter_iff, mem_ofPred_eq, mem_goodDiagonalScores_iff]
      tauto
    _ = ∫⁻ d in C, Measure.pi (stableScoreRowLaw d)
          {r | hasAllTinyLongRotation
            ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ}
          ∂diagonalScoreLaw n := by
      unfold S
      rw [continuousScoreLaw_lintegral_stable_and_diagonal_rows μ (f := F.indicator 1) hC
        (measurable_const.indicator hF)]
      apply lintegral_congr
      intro d
      rw [← lintegral_indicator_one (hpre d)]
      apply lintegral_congr
      intro r
      rfl
    _ ≤ ∫⁻ d in C, (∏ i, stableScoreRowLaw d i univ) * c ∂diagonalScoreLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hC, ae_restrict_of_ae (ae_diagonalMale_openUpper n),
        ae_restrict_of_ae (ae_diagonalPairAt_mem_Icc n),
        ae_restrict_of_ae (ae_diagonal_ae_stableRows μ)] with d hd hx hy hr
      dsimp only [c]
      rw [← nonTiny_path_coefficient hn]
      exact measure_diagonal_allTiny_le μ hd hx (fun j ↦ (hy j).2) hδ₁ hA hB hδ hr
    _ = (∫⁻ d in C, (∏ i, stableScoreRowLaw d i univ) ∂diagonalScoreLaw n) * c :=
      lintegral_mul_const' c _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      rw [stableMass_eq_lintegral_nonTinyRows μ]
      gcongr
      exact Measure.restrict_le_self

/-- Some stable matching has a long exposed cycle with only tiny participants. -/
def badNonTinyRotation (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∃ μ : Matching n, IsStable (profileOfScores x) μ ∧ hasAllTinyLongRotation x μ}

/-- Off the exceptional event, every exposed rotation of length at least 81
has a participating woman whose normalized score is not tiny. -/
theorem exists_nonTiny_participant_of_not_mem_badNonTinyRotation {n : ℕ}
    {x : ScoreProfile n} (hx : x ∉ badNonTinyRotation n) {μ σ : Matching n}
    (hμ : IsStable (profileOfScores x) μ) (hσ : IsExposedRotation (profileOfScores x) μ σ)
    (hlen : 81 ≤ σ.support.card) :
    ∃ i ∈ σ.support,
      nonTinyRotationShare n ≤ femaleSpouseScore x μ (μ i) / femaleSpouseTotal x μ := by
  by_contra! h
  exact hx ⟨μ, hμ, σ, hlen, hσ, fun i ↦ h i.val i.property⟩

private theorem eventually_measure_badNonTinyRotation_le :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (badNonTinyRotation n) ≤
      continuousScoreLaw n (goodCoexposureScores n)ᶜ + ENNReal.ofReal (2 ^ 80 / (n : ℝ)) := by
  filter_upwards [eventually_measure_stable_allTinyLongRotation_le,
    eventually_expectedNumStableMatchings_le_sizeLog, eventually_gt_atTop (0 : ℕ)]
    with n hfixed hmean hn
  let G (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ GoodSpouseScores x μ ∧ hasAllTinyLongRotation x μ}
  have hsub : badNonTinyRotation n ⊆ (goodCoexposureScores n)ᶜ ∪ ⋃ μ, G μ := by
    rintro x ⟨μ, hμ, hrot⟩
    by_cases hx : x ∈ goodCoexposureScores n
    · exact Or.inr (mem_iUnion.mpr ⟨μ, (isStable_profileOfScores_iff hx.1 μ).mp hμ,
        hx.2.2 μ hμ, hrot⟩)
    · exact Or.inl hx
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hmean' : expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
    have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn').trans (by linarith)
    simpa only [pow_two] using hmean.trans (mul_le_mul_of_nonneg_left hlog hn'.le)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_right ?_ _))
  calc
    _ ≤ ∑' μ, continuousScoreLaw n (G μ) := measure_iUnion_le G
    _ ≤ ∑ μ : Matching n, continuousScoreLaw n {x | IsScoreStable x μ} *
        ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
      rw [tsum_fintype]
      exact Finset.sum_le_sum fun μ _ ↦ hfixed μ
    _ = ENNReal.ofReal (expectedNumStableMatchings n) *
        ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) := by
      rw [← Finset.sum_mul, sum_measure_scoreStable_eq_expected]
    _ ≤ ENNReal.ofReal ((n : ℝ)^2) * ENNReal.ofReal (2 ^ 80 * (n : ℝ) ^ (-3 : ℝ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hmean') le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply congrArg ENNReal.ofReal
      have hp : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ)^3)⁻¹ := by
        rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hn'.le,
          show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hp]
      field_simp

/-- The probability that any stable matching exposes a long all-tiny cycle vanishes. -/
theorem tendsto_measure_badNonTinyRotation_zero :
    Tendsto (fun n ↦ continuousScoreLaw n (badNonTinyRotation n)) atTop (𝓝 0) := by
  have h₁ := tendsto_measure_badCoexposureScores_zero_of_mean_upper (C := 1) (by norm_num)
    (by simpa only [one_mul] using eventually_expectedNumStableMatchings_le_sizeLog)
  have h₂ := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (2 ^ 80 : ℝ))
  rw [ENNReal.ofReal_zero] at h₂
  have h := h₁.add h₂
  simp only [add_zero] at h
  exact tendsto_const_nhds.squeeze' h (Eventually.of_forall fun _ ↦ zero_le)
    eventually_measure_badNonTinyRotation_le

end LennonPittelFormalization

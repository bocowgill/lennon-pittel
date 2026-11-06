module

public import LennonPittel.PivotScoreLock
public import LennonPittel.ScoreRotationBandAbundance

/-!
# From a walk exposure to the singleton-anchor score band

The pivot's old couples stay fixed while moving from an exposure to its
singleton anchor. A lower share for one such woman and the uniform upper
share at the anchor preserve enough of the female score total.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- Two distinct pivots cannot share an anchor with only one exposed rotation. -/
theorem singletonRotationAnchor_injective {n : ℕ} {p : Profile n} {μ₀ : Matching n}
    (hopt : IsManOptimal p μ₀) : Function.Injective (singletonRotationAnchor hopt) := by
  intro r s he
  have hr := ((eq_singletonRotationAnchor_iff hopt r _).mp rfl r).mpr rfl
  have hs : r.IsExposedAt (singletonRotationAnchor hopt s).val :=
    (congrArg Subtype.val he) ▸ hr
  exact ((eq_singletonRotationAnchor_iff hopt s _).mp rfl r).mp hs

/-- The distinct rotations have singleton anchors in the wider score band
used by the marked reverse-decoration estimates. -/
def scoreWalkAnchorAbundanceAtCutoffs (n : ℕ) (K A : ℝ) : Set (ScoreProfile n) :=
  {x | ∃ S : Finset (Rotation (profileOfScores x) (DAState.matching (profileOfScores x))),
    Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
    ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
      (r.val.cycle.support.card : ℝ) ≤ A * Real.sqrt n ∧
      femaleSpouseTotal x (singletonRotationAnchor
        (DAState.isManOptimal_matching (profileOfScores x)) r).val ∈
        Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))}

theorem measurableSet_scoreWalkAnchorAbundanceAtCutoffs (n : ℕ) (K A : ℝ) :
    MeasurableSet (scoreWalkAnchorAbundanceAtCutoffs n K A) := by
  let F (p : Profile n) : Set (ScoreProfile n) :=
    {x | ∃ S : Finset (Rotation p (DAState.matching p)),
      Real.sqrt n * Real.log n / (10 * A) ≤ (S.card : ℝ) ∧
      ∀ r ∈ S, K ≤ (r.val.cycle.support.card : ℝ) ∧
        (r.val.cycle.support.card : ℝ) ≤ A * Real.sqrt n ∧
        femaleSpouseTotal x (singletonRotationAnchor (DAState.isManOptimal_matching p) r).val ∈
          Icc ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (2 / 5 : ℝ))}
  have hF (p : Profile n) : MeasurableSet (F p) := by
    unfold F
    simp only [ofPred_exists, ofPred_and, ofPred_forall]
    refine MeasurableSet.iUnion fun S ↦ (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun _ ↦
        (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_))
    exact measurableSet_Icc.preimage (measurable_femaleSpouseTotal _)
  have he : scoreWalkAnchorAbundanceAtCutoffs n K A =
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

private theorem eventually_anchorShareScale :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 10 : ℝ) ≤
      ((n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (-21 / 20 : ℝ)) /
        (12 * Real.log (n : ℝ) / n) := by
  have ho := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)
  have ht := (ho.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 12
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const zero_lt_one, eventually_gt_atTop (1 : ℕ)] with n h hn
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans hn₁
  have hlog := Real.log_pos hn₁
  have hb : 0 < 12 * Real.log (n : ℝ) / n := by positivity
  change 12 * (Real.log (n : ℝ) / (n : ℝ) ^ (1 / 20 : ℝ)) < 1 at h
  rw [← mul_div_assoc] at h
  have hle : 12 * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    simpa only [one_mul] using
      ((div_lt_iff₀ (Real.rpow_pos_of_pos hn₀ (1 / 20))).mp h).le
  apply (le_div_iff₀ hb).mpr
  calc
    _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * ((n : ℝ) ^ (1 / 20 : ℝ) / n) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hle hn₀.le) (by positivity)
    _ = (n : ℝ) ^ (-17 / 20 : ℝ) := by
      have hf := Real.rpow_sub hn₀ (1 / 10 + 1 / 20) 1
      rw [Real.rpow_one] at hf
      rw [← mul_div_assoc, ← Real.rpow_add hn₀, ← hf]
      norm_num
    _ = _ := by rw [← Real.rpow_add hn₀]; norm_num

/-- For large (n), a non-tiny female share for every exposed rotation of
length at least 81 moves the whole in-band family to the singleton-anchor band. -/
theorem eventually_scoreWalkAnchorAbundance_of_bandAbundance
    (K : ℕ → ℝ) (hK : ∀ᶠ n in atTop, 81 ≤ K n) :
    ∀ᶠ n : ℕ in atTop, ∀ {x : ScoreProfile n} {A : ℝ},
      x ∈ goodCoexposureScores n → x ∈ scoreWalkBandAbundanceAtCutoffs n (K n) A →
      (∀ μ : Matching n, IsStable (profileOfScores x) μ → ∀ ρ : Equiv.Perm (Fin n),
        IsExposedRotation (profileOfScores x) μ ρ → 81 ≤ ρ.support.card →
        ∃ m ∈ ρ.support, (n : ℝ) ^ (-21 / 20 : ℝ) ≤
          femaleSpouseScore x μ (μ m) / femaleSpouseTotal x μ) →
      x ∈ scoreWalkAnchorAbundanceAtCutoffs n (K n) A := by
  filter_upwards [eventually_anchorShareScale, hK, eventually_gt_atTop (1 : ℕ)]
    with n hscale hK hn
  intro x A hgood hband hnon
  let p := profileOfScores x
  let hopt := DAState.isManOptimal_matching p
  obtain ⟨S, hS, hcuts⟩ := hband
  refine ⟨S, hS, ?_⟩
  intro r hr
  obtain ⟨hk, hmax, t, -, hex, hY⟩ := hcuts r hr
  let μ := scoreWalkMatching x t
  let ν := (singletonRotationAnchor hopt r).val
  have hμ := scoreWalkMatching_stable (fun j ↦ hgood.1 (.inr j)) t
  have hν := (singletonRotationAnchor hopt r).property
  have hlarge : 81 ≤ r.val.cycle.support.card := by exact_mod_cast (hK.trans hk)
  obtain ⟨m, hm, hlo⟩ := hnon μ hμ r.val.cycle hex.1 hlarge
  have hgoodμ := hgood.2.2 μ hμ
  have hgoodν := hgood.2.2 ν hν
  have hμ₀ : 0 < femaleSpouseTotal x μ := by linarith only [hgoodμ.1]
  have hν₀ : 0 < femaleSpouseTotal x ν := by linarith only [hgoodν.1]
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < 12 * Real.log (n : ℝ) / n := by
    have h := Real.log_pos hn₁
    positivity
  have hbound := hex.singletonAnchor_femaleSpouseTotal_bounds_of_shares
    hgood.1 hopt hμ (Equiv.Perm.mem_support.mp hm) hb hμ₀ hν₀ hlo (hgoodν.2.1 (μ m))
  have hYlo : (n : ℝ) ^ (1 / 5 : ℝ) ≤ femaleSpouseTotal x μ := hY.1.le
  have hYhi : femaleSpouseTotal x μ ≤ (n : ℝ) ^ (2 / 5 : ℝ) := hY.2
  exact ⟨hk, hmax, hscale.trans ((div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hYlo (by positivity)) hb.le).trans hbound.1),
    hbound.2.trans hYhi⟩

end LennonPittelFormalization

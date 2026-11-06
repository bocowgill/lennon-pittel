module

public import LennonPittel.ExponentialSpouseAngles
public import LennonPittel.ExponentialSpouseLogTail
public import LennonPittel.MarkedSpouseAngleComparison
public import LennonPittel.RotationParticipationClock
public import LennonPittel.SmallSpouseTotalLog

/-!
# The log geometry of female spouse scores

Normalizing the spouse vector separates the total score from the angular
error in the log potential. The marked counting bound controls that error
simultaneously at all stable matchings.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- A positive normalized vector has nonnegative excess log potential. -/
theorem spouseAngularLogExcess_nonneg_of_sum_eq_one {n : ℕ} (hn : 0 < n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) : 0 ≤ spouseAngularLogExcess p := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold spouseAngularLogExcess
  calc
    _ = ∑ i : Fin n, (1 - (n : ℝ) * p i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
      simp
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by
      linarith only [Real.log_le_sub_one_of_pos (mul_pos hn' (hp i))]

/-- The female log potential splits into its total-score term and angular excess. -/
theorem femaleLogPotential_eq_total_add_angular {n : ℕ} (hn : 0 < n)
    (x : ScoreProfile n) (μ : Matching n) (hx : ∀ j i, 0 < x (.inr j) i) :
    femaleLogPotential x μ =
      (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) +
        spouseAngularLogExcess (spouseAngle (femaleSpouseByHusband μ x)) := by
  let y := femaleSpouseByHusband μ x
  let Y := femaleSpouseTotal x μ
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hy (i : Fin n) : 0 < y i := hx _ _
  have hYsum : Y = ∑ i, y i := femaleSpouseTotal_eq_sum_byHusband μ x
  have hY : 0 < Y := by
    rw [hYsum]
    exact Finset.sum_pos (fun i _ ↦ hy i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have ha (i : Fin n) : spouseAngle y i = y i / Y := by
    unfold spouseAngle
    rw [← hYsum]
  have heq (i : Fin n) : -Real.log (y i) =
      Real.log ((n : ℝ) / Y) - Real.log ((n : ℝ) * spouseAngle y i) := by
    rw [ha, Real.log_mul hn'.ne' (div_pos (hy i) hY).ne',
      Real.log_div hn'.ne' hY.ne', Real.log_div (hy i).ne' hY.ne']
    ring
  calc
    _ = ∑ i, -Real.log (y i) :=
      (Equiv.sum_comp μ fun j ↦ -Real.log (femaleSpouseScore x μ j)).symm
    _ = ∑ i, (Real.log ((n : ℝ) / Y) - Real.log ((n : ℝ) * spouseAngle y i)) :=
      Finset.sum_congr rfl fun i _ ↦ heq i
    _ = _ := by
      simp only [spouseAngularLogExcess, Y, y, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact sub_eq_add_neg _ _

/-- The total-score term is always a lower bound for the female log potential. -/
theorem femaleLogPotential_lower {n : ℕ} (hn : 0 < n)
    (x : ScoreProfile n) (μ : Matching n) (hx : ∀ j i, 0 < x (.inr j) i) :
    (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) ≤ femaleLogPotential x μ := by
  let y := femaleSpouseByHusband μ x
  have hy (i : Fin n) : 0 < y i := hx _ _
  have hY : 0 < ∑ i, y i :=
    Finset.sum_pos (fun i _ ↦ hy i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hp (i : Fin n) : 0 < spouseAngle y i := div_pos (hy i) hY
  have hsum : ∑ i, spouseAngle y i = 1 := by
    unfold spouseAngle
    rw [← Finset.sum_div, div_self hY.ne']
  rw [femaleLogPotential_eq_total_add_angular hn x μ hx]
  exact le_add_of_nonneg_right (spouseAngularLogExcess_nonneg_of_sum_eq_one hn hp hsum)

/-- An angular exception with tails of every inverse-power order also has
an inverse-power expected count among stable marks. -/
theorem eventually_sum_measure_scoreStable_femaleAngularException_le
    (A : (n : ℕ) → Set (Fin n → ℝ)) (hA : ∀ n, MeasurableSet (A n))
    (htail : ∀ q : ℝ, ∀ᶠ n : ℕ in atTop, spouseAngularLaw n (A n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q))) (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ spouseAngle (femaleSpouseByHusband μ x) ∈ A n}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  have hL : ∀ᶠ n : ℕ in atTop, 2 ≤ (9 / 10 : ℝ) * Real.log n :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
      (20 / 9)).mono fun n h ↦ by
        change (20 / 9 : ℝ) ≤ Real.log (n : ℝ) at h
        linarith only [h]
  have hC : ∀ᶠ n : ℕ in atTop, Real.exp 2 ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [htail (q + 4), eventually_sum_stable_smallSpouseTotalLog_le (q + 1),
    hL, hC, eventually_ge_atTop (2 : ℕ)] with n ha hsmall hlogcut hC hn
  let E (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let F (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ ∧
      spouseAngle (femaleSpouseByHusband μ x) ∈ A n}
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn₂ : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog₀ : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith only [hn₂])
  have hlog : Real.log (n : ℝ) ≤ n :=
    (Real.log_le_sub_one_of_pos hn₀).trans (by linarith)
  have hcoef : Real.exp 2 * (n : ℝ) * Real.log n ≤ (n : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ (n : ℝ) * n * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hn₀.le) hlog₀
      _ ≤ (n : ℝ) * n * n := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  let a := (n : ℝ) ^ (-(q + 1))
  have ha₀ : 0 ≤ a := by unfold a; positivity
  have hF : (∑ μ : Matching n, continuousScoreLaw n (F μ)) ≤ ENNReal.ofReal a := by
    refine (sum_measure_scoreStable_and_femaleSpouseAngle_le hn (hA n)).trans ?_
    calc
      _ ≤ ENNReal.ofReal ((n : ℝ) ^ (3 : ℕ)) * ENNReal.ofReal ((n : ℝ) ^ (-(q + 4))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) ha
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_ofNat, ← Real.rpow_add hn₀]
        congr 2
        ring
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (E μ) + continuousScoreLaw n (F μ)) := by
      apply Finset.sum_le_sum
      intro μ _
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hY : 2 ≤ femaleSpouseTotal x μ
      · exact Or.inr ⟨hx.1, hY, hx.2⟩
      · exact Or.inl ⟨hx.1, (lt_of_not_ge hY).trans_le hlogcut⟩
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hsmall hF
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add ha₀ ha₀]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = 2 * a := (two_mul _).symm
        _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₂ ha₀
        _ = _ := by
          unfold a
          calc
            _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(q + 1)) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring

/-- Angular vectors for which the female log potential exceeds the total-score
term by more than six per pair. -/
def largeSpouseAngularLogSet (n : ℕ) : Set (Fin n → ℝ) :=
  {p | 6 * (n : ℝ) < spouseAngularLogExcess p}

theorem measurableSet_largeSpouseAngularLogSet (n : ℕ) :
    MeasurableSet (largeSpouseAngularLogSet n) :=
  measurableSet_lt measurable_const (measurable_spouseAngularLogExcess n)

theorem eventually_measure_spouseAngularLogExcess_gt_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, spouseAngularLaw n (largeSpouseAngularLogSet n) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_measure_iidExponential_spouseAngularLogExcess_gt_le q] with n hn h
  rw [← map_spouseAngle_pi_expMeasure_one hn,
    Measure.map_apply (measurable_spouseAngle n) (measurableSet_largeSpouseAngularLogSet n)]
  exact h

/-- The error bound in the decomposition of a stable matching's log potential. -/
def HasFemaleLogGeometry {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : Prop :=
  (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) ≤ femaleLogPotential x μ ∧
    femaleLogPotential x μ ≤
      (n : ℝ) * Real.log ((n : ℝ) / femaleSpouseTotal x μ) + 6 * n

/-- The event that every rank-stable matching has the log-potential bounds. -/
def goodFemaleLogGeometry (n : ℕ) : Set (ScoreProfile n) :=
  {x | ∀ μ : Matching n, IsStable (profileOfScores x) μ → HasFemaleLogGeometry x μ}

/-- The log geometry holds simultaneously at every stable matching, with
failure smaller than every fixed inverse power. -/
theorem eventually_measure_badFemaleLogGeometry_le (q : ℝ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (goodFemaleLogGeometry n)ᶜ ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_sum_measure_scoreStable_femaleAngularException_le largeSpouseAngularLogSet
      measurableSet_largeSpouseAngularLogSet eventually_measure_spouseAngularLogExcess_gt_le q]
    with n hn he
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧
      spouseAngle (femaleSpouseByHusband μ x) ∈ largeSpouseAngularLogSet n}
  have hsub : (goodFemaleLogGeometry n)ᶜ ≤ᵐ[continuousScoreLaw n] ⋃ μ, B μ := by
    filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x hties hu hbad
    by_contra hnB
    apply hbad
    intro μ hμ
    have hμ' := (isStable_profileOfScores_iff hties μ).mp hμ
    have hx (j i : Fin n) : 0 < x (.inr j) i := (hu (.inr j) i).1
    have hupper : spouseAngularLogExcess (spouseAngle (femaleSpouseByHusband μ x)) ≤
        6 * (n : ℝ) :=
      le_of_not_gt fun h ↦ hnB (mem_iUnion.mpr ⟨μ, hμ', h⟩)
    exact ⟨femaleLogPotential_lower hn x μ hx, by
      rw [femaleLogPotential_eq_total_add_angular hn x μ hx]
      exact add_le_add_right hupper _⟩
  refine (measure_mono_ae hsub).trans ((measure_iUnion_le _).trans ?_)
  rwa [tsum_fintype]

/-- An interval on the path with small centered clock error has enough
participation to account for its total-score drop, up to the geometric error. -/
theorem rotationParticipation_ge_log_drop {n : ℕ} (x : ScoreProfile n) (μ ν : Matching n)
    (rs : List (Equiv.Perm (Fin n))) (hμ : HasFemaleLogGeometry x μ)
    (hν : HasFemaleLogGeometry x ν) (hYμ : 0 < femaleSpouseTotal x μ)
    (hYν : 0 < femaleSpouseTotal x ν) {E : ℝ}
    (hclock : |femaleLogPotential x ν - femaleLogPotential x μ -
      (rotationParticipation rs : ℝ)| ≤ E) :
    (n : ℝ) * Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) - 6 * n - E ≤
      (rotationParticipation rs : ℝ) := by
  have hn : (0 : ℝ) < n := by
    cases n with
    | zero => simp [femaleSpouseTotal] at hYμ
    | succ n => positivity
  have hlog : Real.log (femaleSpouseTotal x μ / femaleSpouseTotal x ν) =
      Real.log ((n : ℝ) / femaleSpouseTotal x ν) -
        Real.log ((n : ℝ) / femaleSpouseTotal x μ) := by
    rw [Real.log_div hYμ.ne' hYν.ne', Real.log_div hn.ne' hYν.ne',
      Real.log_div hn.ne' hYμ.ne']
    ring
  rw [hlog, mul_sub]
  linarith only [hμ.2, hν.1, (le_abs_self _).trans hclock]

end LennonPittelFormalization

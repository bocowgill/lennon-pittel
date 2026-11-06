module

public import LennonPittel.FinitePartitionClock
public import LennonPittel.ScoreClockFiltration
public import LennonPittel.ScoreRotationBranchTest
public import LennonPittel.ScoreRotationClockBudget

/-!
# The maximal clock bound for the actual comparison-selected walk

The one-step increment is centered in the natural history. Its expected
square is the expected number of participating pairs in that step, even
though the chosen cycle need not be predictable in the earlier history.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology

namespace LennonPittelFormalization

variable {n : ℕ}

private theorem integrable_scoreWalkMeasurableLength (n k : ℕ) :
    Integrable (fun x : ScoreProfile n ↦ scoreWalkMeasurableLength x k)
      (continuousScoreLaw n) :=
  integrable_finsetSum _ fun b _ ↦ (integrable_const _).indicator
    (measurableSet_scoreRotationBranch k b.1 b.2)

/-- The branch identities give centering in the actual natural clock filtration
and an unconditional one-step energy identity. -/
theorem scoreWalkIncrement_moments (n k : ℕ) :
    let P := continuousScoreLaw n
    let d := fun x : ScoreProfile n ↦ scoreWalkIncrement x k
    MemLp d 2 P ∧ P[d | scoreWalkClockFiltration n k] =ᵐ[P] 0 ∧
      (∫ x, (d x)^2 ∂P) = ∫ x, scoreWalkMeasurableLength x k ∂P := by
  let P := continuousScoreLaw n
  let d := fun x : ScoreProfile n ↦ scoreWalkIncrement x k
  let B := @scoreWalkSelectionPartition n k
  have hB := measurableSet_scoreWalkSelectionPartition (n := n) k
  have hm := (scoreWalkClockFiltration n).le k
  have h0 := scoreWalkIncrement_ae_eq_zero_on_stopped (n := n) k
  refine clock_moments_of_fintype_partition P hm
    ((measurable_scoreWalkClock n (k + 1)).sub (measurable_scoreWalkClock n k))
    (integrable_scoreWalkMeasurableLength n k) hB
    (pairwise_disjoint_scoreWalkSelectionPartition k) (iUnion_scoreWalkSelectionPartition k)
    ?_ ?_ ?_
  · intro b
    cases b with
    | none =>
      exact (memLp_congr_ae h0).mpr (memLp_const (0 : ℝ))
    | some b => exact memLp_scoreWalkClock_increment_on_branch k b.1 b.2
  · intro b A hA
    cases b with
    | none =>
      have h : d =ᵐ[P.restrict (B none ∩ A)] 0 :=
        h0.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
      rw [integral_congr_ae h]
      simp
    | some b =>
      exact setIntegral_scoreWalkClock_increment_on_branch_inter k b.1 b.2 (hm A hA)
        (fun _ _ hxy ↦ mem_iff_of_scoreWalkClock_history_eq hA hxy)
  · intro b
    cases b with
    | none =>
      have hs : (fun x ↦ (d x)^2) =ᵐ[P.restrict (B none)] fun _ ↦ (0 : ℝ) :=
        h0.mono fun x hx ↦ by simp [d, hx]
      calc
        (∫ x in B none, (d x)^2 ∂P) = 0 := by
          rw [integral_congr_ae hs, integral_zero]
        _ = ∫ x in B none, scoreWalkMeasurableLength x k ∂P := by
          rw [integral_congr_ae ((ae_restrict_mem (hB none)).mono fun _ hx ↦
            scoreWalkMeasurableLength_of_mem_stopped hx), integral_zero]
    | some b =>
      have hlen : (fun x ↦ scoreWalkMeasurableLength x k) =ᵐ[P.restrict (B (some b))]
          fun _ ↦ (b.2.support.card : ℝ) :=
        (ae_restrict_mem (hB (some b))).mono fun _ hx ↦
          scoreWalkMeasurableLength_of_mem_branch hx
      rw [integral_congr_ae hlen, setIntegral_const, smul_eq_mul, mul_comm]
      exact setIntegral_sq_scoreWalkClock_increment_on_branch k b.1 b.2

theorem scoreWalkClock_zero (x : ScoreProfile n) : scoreWalkClock x 0 = 0 := by
  simp [scoreWalkClock, scoreRotationWalk, rotationParticipation]

theorem memLp_scoreWalkClock (n k : ℕ) :
    MemLp (fun x : ScoreProfile n ↦ scoreWalkClock x k) 2 (continuousScoreLaw n) := by
  induction k with
  | zero =>
    simpa only [scoreWalkClock_zero] using
      (memLp_const (0 : ℝ) :
        MemLp (fun _ : ScoreProfile n ↦ (0 : ℝ)) 2 (continuousScoreLaw n))
  | succ k ih =>
    have he : ((fun x : ScoreProfile n ↦ scoreWalkClock x k) +
        (fun x ↦ scoreWalkIncrement x k)) =ᵐ[continuousScoreLaw n]
        fun x ↦ scoreWalkClock x (k + 1) :=
      Eventually.of_forall fun x ↦ by simp [scoreWalkIncrement]
    exact (memLp_congr_ae he).mp (ih.add (scoreWalkIncrement_moments n k).1)

/-- Expected quadratic energy of the centered clock is bounded by the
deterministic budget of strict rank increases. -/
theorem sum_integral_scoreWalkIncrement_sq_le (n N : ℕ) :
    (∑ k ∈ Finset.range N, ∫ x, (scoreWalkIncrement x k)^2 ∂continuousScoreLaw n) ≤
      (n * (n - 1) : ℕ) := by
  let P := continuousScoreLaw n
  let f (k : ℕ) (x : ScoreProfile n) := scoreWalkMeasurableLength x k
  have hi (k : ℕ) : Integrable (f k) P := integrable_scoreWalkMeasurableLength n k
  change (∑ k ∈ Finset.range N, ∫ x, (scoreWalkIncrement x k)^2 ∂P) ≤ _
  calc
    _ = ∑ k ∈ Finset.range N, ∫ x, f k x ∂P :=
      Finset.sum_congr rfl fun k _ ↦ (scoreWalkIncrement_moments n k).2.2
    _ = ∫ x, ∑ k ∈ Finset.range N, f k x ∂P :=
      (integral_finsetSum _ (fun k _ ↦ hi k)).symm
    _ ≤ ∫ _ : ScoreProfile n, ((n * (n - 1) : ℕ) : ℝ) ∂P :=
      integral_mono_ae (integrable_finsetSum _ (fun k _ ↦ hi k)) (integrable_const _)
        (ae_sum_scoreWalkMeasurableLength_le n N)
    _ = _ := by simp [P]

/-- A finite-horizon maximum for the actual centered clock in the iid score law. -/
theorem measure_scoreWalkClock_maximal_le (n N : ℕ) {a : ℝ} (ha : 0 < a) :
    continuousScoreLaw n {x | ∃ k ≤ N, a ≤ |scoreWalkClock x k|} ≤
      ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) / a^2) :=
  measure_clock_maximal_le_of_step_energy (stronglyAdapted_scoreWalkClock n)
    (fun k _ ↦ memLp_scoreWalkClock n k) (Eventually.of_forall scoreWalkClock_zero)
    (fun k _ ↦ (scoreWalkIncrement_moments n k).2.1)
    (sum_integral_scoreWalkIncrement_sq_le n N) ha

/-- The clock error is negligible on the participation scale $n\log n$. -/
theorem tendsto_measure_scoreWalkClock_large {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ continuousScoreLaw n
      {x | ∃ k ≤ n * (n - 1), ε * (n * Real.log n) ≤ |scoreWalkClock x k|})
      atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiv := tendsto_inv_atTop_zero.comp (hlog.const_mul_atTop hε)
  have htop :
      Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((ε * Real.log n)⁻¹ ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
      using ENNReal.tendsto_ofReal (hdiv.pow 2)
  refine tendsto_const_nhds.squeeze' htop (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := zero_lt_one.trans hn₁
  have hlog₀ := Real.log_pos hn₁
  have ha : 0 < ε * ((n : ℝ) * Real.log n) := by positivity
  have hB : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    exact_mod_cast (show n * (n - 1) ≤ n^2 by
      simpa only [pow_two] using Nat.mul_le_mul_left n (Nat.sub_le n 1))
  refine (measure_scoreWalkClock_maximal_le n (n * (n - 1)) ha).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (n : ℝ)^2 / (ε * ((n : ℝ) * Real.log n))^2 :=
      div_le_div_of_nonneg_right hB (sq_nonneg _)
    _ = _ := by
      field_simp [hε.ne', hn₀.ne', hlog₀.ne']

end LennonPittelFormalization

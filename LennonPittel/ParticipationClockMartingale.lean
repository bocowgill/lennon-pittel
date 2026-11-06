module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# A maximal estimate from a participation budget

A square-integrable martingale accumulates second moment according to the conditional second
moments of its increments. If their sum is bounded by a participation budget, Doob's inequality
controls deviations at every time through the horizon.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LennonPittelFormalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}

/-- The conditional energy of a martingale increment equals the increase in conditional second
moment. -/
theorem condExp_martingale_increment_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) {i j : ℕ} (hij : i ≤ j) :
    μ[fun ω ↦ (M j ω - M i ω)^2 | ℱ i] =ᵐ[μ]
      fun ω ↦ μ[fun ω ↦ M j ω ^ 2 | ℱ i] ω - M i ω ^ 2 := by
  have hmean := hM.condExp_ae_eq hij
  have hvar : Var[M j; μ | ℱ i] =ᵐ[μ] μ[fun ω ↦ (M j ω - M i ω)^2 | ℱ i] := by
    apply condExp_congr_ae
    filter_upwards [hmean] with ω hω
    change (M j ω - μ[M j | ℱ i] ω)^2 = _
    rw [hω]
  refine hvar.symm.trans ((condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le i) (hL2 j)).trans ?_)
  filter_upwards [hmean] with ω hω
  change μ[fun ω ↦ M j ω ^ 2 | ℱ i] ω - (μ[M j | ℱ i] ω)^2 = _
  rw [hω]

/-- The squared martingale is a nonnegative submartingale. -/
theorem martingale_sq_submartingale [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) :
    Submartingale (fun t ω ↦ M t ω ^ 2) ℱ μ := by
  refine ⟨fun t ↦ (hM.stronglyMeasurable t).pow 2, fun i j hij ↦ ?_, fun t ↦
    (hL2 t).integrable_sq⟩
  have hnonneg : 0 ≤ᵐ[μ] μ[fun ω ↦ (M j ω - M i ω)^2 | ℱ i] :=
    condExp_nonneg (.of_forall fun ω ↦ sq_nonneg (M j ω - M i ω))
  filter_upwards [hnonneg, condExp_martingale_increment_sq hM hL2 hij] with ω hω heq
  rw [heq] at hω
  exact sub_nonneg.mp hω

/-- A martingale started from zero has second moment equal to the accumulated expected
squared increments. -/
theorem integral_martingale_sq_eq_sum_increment_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) (h0 : M 0 =ᵐ[μ] 0) (N : ℕ) :
    (∫ ω, M N ω ^ 2 ∂μ) = ∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ := by
  induction N with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, ← integral_zero Ω ℝ]
    apply integral_congr_ae
    filter_upwards [h0] with ω hω
    change M 0 ω ^ 2 = 0
    rw [hω]
    norm_num
  | succ N ih =>
    have hstep :
        (∫ ω, (M (N + 1) ω - M N ω)^2 ∂μ) =
          (∫ ω, M (N + 1) ω ^ 2 ∂μ) - ∫ ω, M N ω ^ 2 ∂μ := by
      rw [← integral_condExp (ℱ.le N) (f := fun ω ↦ (M (N + 1) ω - M N ω)^2)]
      calc
        _ = ∫ ω, μ[fun ω ↦ M (N + 1) ω ^ 2 | ℱ N] ω - M N ω ^ 2 ∂μ :=
          integral_congr_ae (condExp_martingale_increment_sq hM hL2 (Nat.le_succ N))
        _ = _ := by rw [integral_sub integrable_condExp (hL2 N).integrable_sq,
          integral_condExp (ℱ.le N)]
    rw [Finset.sum_range_succ, ← ih, hstep]
    ring

/-- Doob's inequality bounds the probability of exceeding a positive level through time `N`
in terms of a bound on terminal second moment. -/
theorem measure_clock_maximal_le_of_integral_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) {N : ℕ} {B a : ℝ}
    (hB : (∫ ω, M N ω ^ 2 ∂μ) ≤ B) (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) := by
  let ε : ℝ≥0 := ⟨a^2, sq_nonneg a⟩
  have hnonneg : 0 ≤ (fun t ω ↦ M t ω ^ 2) := fun t ω ↦ sq_nonneg (M t ω)
  have h := maximal_ineq (martingale_sq_submartingale hM hL2) hnonneg (ε := ε) N
  have hevent :
      {ω | (ε : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun t ↦ M t ω ^ 2} = {ω | ∃ t ≤ N, a ≤ |M t ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
    apply exists_congr
    intro t
    change (t ≤ N ∧ a^2 ≤ M t ω ^ 2) ↔ (t ≤ N ∧ a ≤ |M t ω|)
    rw [← sq_abs (M t ω), sq_le_sq₀ ha.le (abs_nonneg _)]
  rw [hevent] at h
  have hterminal : 0 ≤ (∫ ω, M N ω ^ 2 ∂μ) :=
    integral_nonneg fun ω ↦ sq_nonneg (M N ω)
  have hscaled : ε • μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal B :=
    h.trans (ENNReal.ofReal_le_ofReal ((setIntegral_le_integral (hL2 N).integrable_sq
      (.of_forall fun ω ↦ sq_nonneg (M N ω))).trans hB))
  have hreal := (ENNReal.le_ofReal_iff_toReal_le
    (ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)) (hterminal.trans hB)).mp hscaled
  rw [ENNReal.toReal_mul] at hreal
  change a^2 * (μ {ω | ∃ t ≤ N, a ≤ |M t ω|}).toReal ≤ B at hreal
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
    (div_nonneg (hterminal.trans hB) (sq_nonneg a)), le_div_iff₀ (sq_pos_of_pos ha), mul_comm]
  exact hreal

/-- Doob's inequality in terms of the total expected squared increments. -/
theorem measure_clock_maximal_le_of_increment_sq [IsFiniteMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) (h0 : M 0 =ᵐ[μ] 0)
    {N : ℕ} {B a : ℝ}
    (hB : (∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ) ≤ B)
    (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) :=
  measure_clock_maximal_le_of_integral_sq hM hL2
    ((integral_martingale_sq_eq_sum_increment_sq hM hL2 h0 N).le.trans hB) ha

private theorem sum_integral_increment_sq_le_of_budget [IsProbabilityMeasure μ]
    {N : ℕ} {B : ℝ} {L : ℕ → Ω → ℝ} {𝒢 : ℕ → MeasurableSpace Ω}
    (h𝒢 : ∀ t < N, 𝒢 t ≤ mΩ)
    (hvar : ∀ t < N, μ[fun ω ↦ (M (t + 1) ω - M t ω)^2 | 𝒢 t] =ᵐ[μ] L t)
    (hbudget : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range N, L t ω ≤ B) :
    (∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ) ≤ B := by
  have hLint (t : ℕ) (ht : t ∈ Finset.range N) : Integrable (L t) μ :=
    integrable_condExp.congr (hvar t (Finset.mem_range.mp ht))
  calc
    _ = ∑ t ∈ Finset.range N, ∫ ω, L t ω ∂μ := by
      apply Finset.sum_congr rfl
      intro t ht
      have hlt := Finset.mem_range.mp ht
      rw [← integral_condExp (h𝒢 t hlt) (f := fun ω ↦ (M (t + 1) ω - M t ω)^2)]
      exact integral_congr_ae (hvar t hlt)
    _ = ∫ ω, ∑ t ∈ Finset.range N, L t ω ∂μ := (integral_finsetSum _ hLint).symm
    _ ≤ ∫ _ : Ω, B ∂μ := integral_mono_ae (integrable_finsetSum _ hLint)
      (integrable_const B) hbudget
    _ = B := by simp

/-- A pathwise upper bound on the accumulated conditional squared increments bounds the
terminal second moment. -/
theorem integral_martingale_sq_le_of_conditional_participation [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) (h0 : M 0 =ᵐ[μ] 0)
    {N : ℕ} {B : ℝ} {L : ℕ → Ω → ℝ}
    (hvar : ∀ t < N, μ[fun ω ↦ (M (t + 1) ω - M t ω)^2 | ℱ t] =ᵐ[μ] L t)
    (hbudget : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range N, L t ω ≤ B) :
    (∫ ω, M N ω ^ 2 ∂μ) ≤ B := by
  rw [integral_martingale_sq_eq_sum_increment_sq hM hL2 h0 N]
  exact sum_integral_increment_sq_le_of_budget (fun t _ ↦ ℱ.le t) hvar hbudget

/-- A pathwise participation budget bounds the maximum absolute fluctuation through the
horizon. -/
theorem measure_clock_maximal_le_of_conditional_participation [IsProbabilityMeasure μ]
    (hM : Martingale M ℱ μ) (hL2 : ∀ t, MemLp (M t) 2 μ) (h0 : M 0 =ᵐ[μ] 0)
    {N : ℕ} {B a : ℝ} {L : ℕ → Ω → ℝ}
    (hvar : ∀ t < N, μ[fun ω ↦ (M (t + 1) ω - M t ω)^2 | ℱ t] =ᵐ[μ] L t)
    (hbudget : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range N, L t ω ≤ B) (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) :=
  measure_clock_maximal_le_of_integral_sq hM hL2
    (integral_martingale_sq_le_of_conditional_participation hM hL2 h0 hvar hbudget) ha

/-- The maximal estimate requires only one-step centering and a total expected energy bound
through the horizon. -/
theorem measure_clock_maximal_le_of_step_energy [IsFiniteMeasure μ]
    (hM : StronglyAdapted ℱ M) {N : ℕ} (hL2 : ∀ t ≤ N, MemLp (M t) 2 μ)
    (h0 : M 0 =ᵐ[μ] 0) {B a : ℝ}
    (hmean : ∀ t < N, μ[fun ω ↦ M (t + 1) ω - M t ω | ℱ t] =ᵐ[μ] 0)
    (hB : (∑ t ∈ Finset.range N, ∫ ω, (M (t + 1) ω - M t ω)^2 ∂μ) ≤ B)
    (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) := by
  let M' : ℕ → Ω → ℝ := fun t ↦ M (min t N)
  have hM'L2 (t : ℕ) : MemLp (M' t) 2 μ := hL2 _ (min_le_right t N)
  have hM' : Martingale M' ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat
      (fun t ↦ (hM _).mono (ℱ.mono (min_le_left t N)))
      (fun t ↦ (hM'L2 t).integrable (by simp)) fun t ↦ ?_
    change μ[fun ω ↦ M (min (t + 1) N) ω - M (min t N) ω | ℱ t] =ᵐ[μ] 0
    by_cases ht : t < N
    · rw [min_eq_left ht.le, min_eq_left (Nat.succ_le_of_lt ht)]
      exact hmean t ht
    · have hle := Nat.le_of_not_gt ht
      rw [min_eq_right hle, min_eq_right (hle.trans (Nat.le_succ t))]
      simp only [sub_self, ← Pi.zero_def, condExp_zero, EventuallyEq.rfl]
  have hM'0 : M' 0 =ᵐ[μ] 0 := by simpa only [M', Nat.zero_min] using h0
  have hM'B : (∑ t ∈ Finset.range N, ∫ ω, (M' (t + 1) ω - M' t ω)^2 ∂μ) ≤ B := by
    convert hB using 1
    apply Finset.sum_congr rfl
    intro t ht
    have hlt := Finset.mem_range.mp ht
    simp only [M', min_eq_left hlt.le, min_eq_left (Nat.succ_le_of_lt hlt)]
  have h := measure_clock_maximal_le_of_increment_sq hM' hM'L2 hM'0 hM'B ha
  have hevent : {ω | ∃ t ≤ N, a ≤ |M' t ω|} = {ω | ∃ t ≤ N, a ≤ |M t ω|} := by
    ext ω
    constructor
    · rintro ⟨t, ht, hω⟩
      exact ⟨t, ht, by simpa only [M', min_eq_left ht] using hω⟩
    · rintro ⟨t, ht, hω⟩
      exact ⟨t, ht, by simpa only [M', min_eq_left ht] using hω⟩
  rwa [hevent] at h

/-- The participation length can be revealed by finer, pre-update observations. The martingale
itself need only be adapted to the checkpoint filtration. -/
theorem measure_clock_maximal_le_of_refined_step_moments [IsProbabilityMeasure μ]
    (hM : StronglyAdapted ℱ M) {N : ℕ} (hL2 : ∀ t ≤ N, MemLp (M t) 2 μ)
    (h0 : M 0 =ᵐ[μ] 0) {B a : ℝ} {L : ℕ → Ω → ℝ} {𝒢 : ℕ → MeasurableSpace Ω}
    (hℱ𝒢 : ∀ t < N, ℱ t ≤ 𝒢 t) (h𝒢 : ∀ t < N, 𝒢 t ≤ mΩ)
    (hmean : ∀ t < N, μ[fun ω ↦ M (t + 1) ω - M t ω | 𝒢 t] =ᵐ[μ] 0)
    (hvar : ∀ t < N, μ[fun ω ↦ (M (t + 1) ω - M t ω)^2 | 𝒢 t] =ᵐ[μ] L t)
    (hbudget : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range N, L t ω ≤ B) (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) := by
  refine measure_clock_maximal_le_of_step_energy hM hL2 h0 (fun t ht ↦ ?_) ?_ ha
  · refine (condExp_condExp_of_le (hℱ𝒢 t ht) (h𝒢 t ht)).symm.trans ?_
    simpa only [condExp_zero] using
      (condExp_congr_ae (m := ℱ t) (hmean t ht))
  · exact sum_integral_increment_sq_le_of_budget h𝒢 hvar hbudget

/-- One-step conditional moments through the horizon suffice for the maximal estimate. -/
theorem measure_clock_maximal_le_of_step_moments [IsProbabilityMeasure μ]
    (hM : StronglyAdapted ℱ M) {N : ℕ} (hL2 : ∀ t ≤ N, MemLp (M t) 2 μ)
    (h0 : M 0 =ᵐ[μ] 0) {B a : ℝ} {L : ℕ → Ω → ℝ}
    (hmean : ∀ t < N, μ[fun ω ↦ M (t + 1) ω - M t ω | ℱ t] =ᵐ[μ] 0)
    (hvar : ∀ t < N, μ[fun ω ↦ (M (t + 1) ω - M t ω)^2 | ℱ t] =ᵐ[μ] L t)
    (hbudget : ∀ᵐ ω ∂μ, ∑ t ∈ Finset.range N, L t ω ≤ B) (ha : 0 < a) :
    μ {ω | ∃ t ≤ N, a ≤ |M t ω|} ≤ ENNReal.ofReal (B / a^2) :=
  measure_clock_maximal_le_of_refined_step_moments hM hL2 h0
    (fun _ _ ↦ le_rfl) (fun t _ ↦ ℱ.le t) hmean hvar hbudget ha

end LennonPittelFormalization

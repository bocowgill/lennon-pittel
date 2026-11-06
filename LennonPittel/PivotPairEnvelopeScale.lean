module

public import LennonPittel.PivotShortCycleScale

/-!
# Quantitative pair envelopes on the centered-count scale

After normalization by the square of the count scale, the residual bound
has one term proportional to the cutoff exponent and two inverse-log terms.
The bound for two long orientations has just one inverse-log term.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LennonPittelFormalization

/-- Residual-pair bound after the two-to-one toggle and the two short-cycle exceptions. -/
noncomputable def residualPairEnvelope (C α : ℝ) (n : ℕ) : ℝ :=
  2 * (C * (1 + Real.log n)) *
    (8 * (n : ℝ) ^ 2 * (2 + α * Real.log n) + 4 +
      (1600 / Real.log (pivotShortCycleCutoff α n : ℝ)) *
        (12 * (n : ℝ) ^ 2 * (1 + Real.log n)))

/-- Pair bound when both orientation sizes exceed a positive square-root threshold. -/
noncomputable def longPairEnvelope (C b : ℝ) (n : ℕ) : ℝ :=
  C * (1 + Real.log n) * ((8 + 16 / b ^ 2) * (n : ℝ) ^ 2)

private theorem residualPairEnvelope_le_of_log_bounds {C α δ : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hn : 1 ≤ n)
    (hl : 1 ≤ Real.log (n : ℝ)) (hL : 0 < Real.log (pivotShortCycleCutoff α n : ℝ))
    (hαδ : 32 * α ≤ δ) (hδl : 80 ≤ δ * Real.log (n : ℝ))
    (hδL : 153600 ≤ δ * Real.log (pivotShortCycleCutoff α n : ℝ)) :
    residualPairEnvelope C α n ≤ (3 * C * δ) * ((n : ℝ) * Real.log n) ^ 2 := by
  let l := Real.log (n : ℝ)
  let L := Real.log (pivotShortCycleCutoff α n : ℝ)
  have hln : 0 ≤ l := zero_le_one.trans hl
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn'
  have hll : 1 + l ≤ 2 * l := by change 1 ≤ l at hl; linarith only [hl]
  have h4 : (4 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by linarith only [hnsq]
  have hα' : 32 * α * l ≤ δ * l := mul_le_mul_of_nonneg_right hαδ hln
  have hL' : 153600 / L ≤ δ := (div_le_iff₀ hL).2 hδL
  have hL'' := mul_le_mul_of_nonneg_right hL' hln
  calc
    residualPairEnvelope C α n =
        2 * (C * (1 + l)) *
          (8 * (n : ℝ) ^ 2 * (2 + α * l) + 4 +
            (1600 / L) * (12 * (n : ℝ) ^ 2 * (1 + l))) := rfl
    _ ≤ 2 * (C * (2 * l)) *
          (8 * (n : ℝ) ^ 2 * (2 + α * l) + 4 * (n : ℝ) ^ 2 +
            (1600 / L) * (12 * (n : ℝ) ^ 2 * (2 * l))) := by
      gcongr
    _ = (C * (n : ℝ) ^ 2 * l) * (80 + 32 * α * l + (153600 / L) * l) := by ring
    _ ≤ (C * (n : ℝ) ^ 2 * l) * (δ * l + δ * l + δ * l) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add hδl hα') hL''
    _ = _ := by ring

private theorem tendsto_log_marketSize : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_log_pivotShortCycleCutoff {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ ↦ Real.log (pivotShortCycleCutoff α n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_pivotShortCycleCutoff hα))

/-- Fix a small exponent before taking the limit to make the residual bound arbitrarily small. -/
theorem eventually_residualPairEnvelope_le {C e : ℝ} (hC : 0 < C) (he : 0 < e) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 10 ∧
      ∀ᶠ n : ℕ in atTop,
        residualPairEnvelope C α n ≤ (e / 8) * ((n : ℝ) * Real.log n) ^ 2 := by
  let δ := e / (24 * C)
  let α : ℝ := min (1 / 20) (δ / 32)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hα : 0 < α := lt_min (by norm_num) (by positivity)
  have hαsmall : α < 1 / 10 := (min_le_left _ _).trans_lt (by norm_num)
  have hαδ : 32 * α ≤ δ := by
    have h := (le_div_iff₀ (by norm_num : 0 < (32 : ℝ))).1
      (min_le_right (1 / 20 : ℝ) (δ / 32))
    nlinarith only [h]
  refine ⟨α, hα, hαsmall, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), tendsto_log_marketSize.eventually_ge_atTop 1,
    tendsto_log_marketSize.eventually_ge_atTop (80 / δ),
    (tendsto_log_pivotShortCycleCutoff hα).eventually_ge_atTop (153600 / δ)]
    with n hn hl hlδ hLδ
  have hL : 0 < Real.log (pivotShortCycleCutoff α n : ℝ) :=
    (show 0 < 153600 / δ by positivity).trans_le hLδ
  have hδl : 80 ≤ δ * Real.log (n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).1 hlδ
  have hδL : 153600 ≤ δ * Real.log (pivotShortCycleCutoff α n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).1 hLδ
  calc
    _ ≤ (3 * C * δ) * ((n : ℝ) * Real.log n) ^ 2 :=
      residualPairEnvelope_le_of_log_bounds hC.le hα.le hn hl hL hαδ hδl hδL
    _ = _ := by
      have hcoef : 3 * C * δ = e / 8 := by
        dsimp [δ]
        field_simp
        norm_num
      rw [hcoef]

/-- The two-long-orientation bound is negligible on the squared count scale. -/
theorem eventually_longPairEnvelope_le {C b e : ℝ} (hC : 0 < C) (hb : 0 < b)
    (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, longPairEnvelope C b n ≤ (e / 4) * ((n : ℝ) * Real.log n) ^ 2 := by
  let S : ℝ := 8 + 16 / b ^ 2
  filter_upwards [tendsto_log_marketSize.eventually_ge_atTop 1,
    tendsto_log_marketSize.eventually_ge_atTop (8 * C * S / e)] with n hl hscale
  let l := Real.log (n : ℝ)
  have hln : 0 ≤ l := zero_le_one.trans hl
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hll : 1 + l ≤ 2 * l := by change 1 ≤ l at hl; linarith only [hl]
  have hmul : 2 * C * S ≤ (e / 4) * l := by
    have hh := (div_le_iff₀ he).1 hscale
    change 8 * C * S ≤ l * e at hh
    nlinarith only [hh]
  calc
    longPairEnvelope C b n = C * (1 + l) * (S * (n : ℝ) ^ 2) := rfl
    _ ≤ C * (2 * l) * (S * (n : ℝ) ^ 2) := by gcongr
    _ = ((n : ℝ) ^ 2 * l) * (2 * C * S) := by ring
    _ ≤ ((n : ℝ) ^ 2 * l) * ((e / 4) * l) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by ring

/-- The same fixed cutoff exponent works for the two required eventual variance bounds. -/
theorem eventually_pairEnvelopes_le {C b e : ℝ} (hC : 0 < C) (hb : 0 < b) (he : 0 < e) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 10 ∧
      ∀ᶠ n : ℕ in atTop,
        residualPairEnvelope C α n ≤ (e / 8) * ((n : ℝ) * Real.log n) ^ 2 ∧
        longPairEnvelope C b n ≤ (e / 4) * ((n : ℝ) * Real.log n) ^ 2 := by
  obtain ⟨α, hα, hαsmall, hres⟩ := eventually_residualPairEnvelope_le hC he
  exact ⟨α, hα, hαsmall, hres.and (eventually_longPairEnvelope_le hC hb he)⟩

end LennonPittelFormalization

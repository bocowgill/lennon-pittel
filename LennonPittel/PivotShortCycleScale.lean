module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The short-cycle cutoff

The cycle cap uses the integer part of a small power of the market
size. The exponent is fixed before taking the limit.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LennonPittelFormalization

/-- The maximum length of a cycle counted by the short-cycle filter. -/
noncomputable def pivotShortCycleCutoff (α : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (α / 4)⌋₊

theorem pivotShortCycleCutoff_cast_le (α : ℝ) (n : ℕ) :
    (pivotShortCycleCutoff α n : ℝ) ≤ (n : ℝ) ^ (α / 4) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem tendsto_pivotShortCycleCutoff {α : ℝ} (hα : 0 < α) :
    Tendsto (pivotShortCycleCutoff α) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (show 0 < α / 4 by positivity)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- A positive square-root support budget eventually exceeds this cutoff. -/
theorem eventually_pivotShortCycleCutoff_le {α κ : ℝ} (hα : α < 2) (hκ : 0 < κ)
    {K : ℕ → ℕ} (hK : ∀ᶠ n : ℕ in atTop, κ * Real.sqrt (n : ℝ) / 2 ≤ (K n : ℝ)) :
    ∀ᶠ n in atTop, pivotShortCycleCutoff α n ≤ K n := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 - α / 4))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show 0 < (1 / 2 : ℝ) - α / 4 by linarith)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(tendsto_order.mp ht).2 (κ / 2) (by positivity), hK,
    eventually_gt_atTop (0 : ℕ)] with n hn hkn hn'
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn'
  apply Nat.floor_le_of_le
  calc
    (n : ℝ) ^ (α / 4) = (n : ℝ) ^ (-(1 / 2 - α / 4)) * Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
      congr 1
      ring
    _ ≤ (κ / 2) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hn.le (Real.sqrt_nonneg _)
    _ ≤ (K n : ℝ) := by linarith only [hkn]

/-- Both orientations in the regular sector are large enough for all the
short lengths to occur in their restricted permutations. -/
theorem pivotShortCycleCutoff_le_of_rpow_lt {α : ℝ} (hα : 0 ≤ α) {n v : ℕ}
    (hn : 1 ≤ n) (hv : (n : ℝ) ^ α < (v : ℝ)) :
    pivotShortCycleCutoff α n ≤ v := by
  apply Nat.floor_le_of_le
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (by linarith : α / 4 ≤ α)).trans hv.le

/-- For fixed positive exponent, rounding does not remove the logarithmic
growth that is needed in the short-cycle exception probabilities. -/
theorem eventually_log_pivotShortCycleCutoff_ge {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      (α / 8) * Real.log (n : ℝ) ≤ Real.log (pivotShortCycleCutoff α n : ℝ) := by
  let f (n : ℕ) := (n : ℝ) ^ (α / 4)
  have hf : Tendsto f atTop atTop :=
    (tendsto_rpow_atTop (show 0 < α / 4 by positivity)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(tendsto_atTop.mp hf) 2,
    (tendsto_atTop.mp hlog) (Real.log 2 / (α / 8)),
    eventually_gt_atTop (0 : ℕ)] with n hn hln hn'
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn'
  have hfpos : 0 < f n := zero_lt_two.trans_le hn
  have hfloor : f n < (pivotShortCycleCutoff α n : ℝ) + 1 := Nat.lt_floor_add_one (f n)
  have hhalf : f n / 2 ≤ (pivotShortCycleCutoff α n : ℝ) := by linarith
  calc
    (α / 8) * Real.log (n : ℝ) ≤ (α / 4) * Real.log (n : ℝ) - Real.log 2 := by
      have h := (div_le_iff₀ (show 0 < α / 8 by positivity)).mp hln
      linarith only [h]
    _ = Real.log (f n / 2) := by
      rw [Real.log_div hfpos.ne' two_ne_zero, show Real.log (f n) =
        (α / 4) * Real.log (n : ℝ) from Real.log_rpow hnR _]
    _ ≤ _ := Real.log_le_log (by positivity) hhalf

end LennonPittelFormalization

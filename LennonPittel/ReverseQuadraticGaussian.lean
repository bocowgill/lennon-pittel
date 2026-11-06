module

public import LennonPittel.CoexposureGaussianSum

/-!
# Quadratically weighted cycle sums

An additional quadratic weight in the support size preserves the Gaussian
cutoff. Bernoulli's inequality absorbs the quadratic weight by increasing the
per-vertex multiplier by a factor of the form `1 + O(1 / sqrt n)`.
-/

@[expose] public section

open Finset
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- A quadratic factor in the cycle-collection weight costs at most one extra
factor of `n` beyond the square-root bound. -/
theorem reverse_weighted_powerset_sum_le_n_mul_sqrt {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (t.card.factorial : ℝ) * ((t.card : ℝ) + 1) ^ 2 * (1 + δ) ^ t.card *
        ∏ i ∈ t, w i) ≤
      2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * (n : ℝ) * Real.sqrt n := by
  let s := Real.sqrt (n : ℝ)
  let u := 1 / s
  let Δ := (1 + δ) * (1 + u) ^ 2 - 1
  have hs₀ : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs₁ : 1 ≤ s := by
    simpa [s] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hs₂ : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hu₀ : 0 ≤ u := one_div_nonneg.mpr hs₀.le
  have hu₁ : u ≤ 1 := (div_le_one hs₀).mpr hs₁
  have hΔ : 1 + Δ = (1 + δ) * (1 + u) ^ 2 := by dsimp [Δ]; ring
  have hΔ₀ : 0 ≤ Δ := sub_nonneg.mpr
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith)))
  have hu_sq : u ^ 2 ≤ u := by nlinarith [mul_nonneg hu₀ (sub_nonneg.mpr hu₁)]
  have hpert : Δ ≤ (4 * C + 3) / s :=
    calc
      Δ ≤ (1 + δ) * (1 + 3 * u) - 1 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)) _
      _ ≤ 4 * δ + 3 * u := by nlinarith [mul_nonneg hδ₀ (sub_nonneg.mpr hu₁)]
      _ ≤ _ := by
        have hδs : δ ≤ C / s := hδ
        rw [add_div, mul_div_assoc]
        dsimp only [u]
        rw [mul_one_div]
        linarith only [hδs]
  have hq (j : ℕ) : ((j : ℝ) + 1) ^ 2 ≤ (n : ℝ) * ((1 + u) ^ 2) ^ j := by
    have hbern : 1 + (j : ℝ) * u ≤ (1 + u) ^ j := one_add_mul_le_pow (by linarith) j
    have hsu : s * u = 1 := by
      dsimp only [u]
      rw [mul_one_div, div_self hs₀.ne']
    have hscale : (j : ℝ) + 1 ≤ s * (1 + (j : ℝ) * u) := by
      rw [mul_add, mul_one, mul_left_comm s, hsu, mul_one]
      linarith only [hs₁]
    calc
      _ ≤ (s * ((1 + u) ^ j)) ^ 2 :=
        pow_le_pow_left₀ (by positivity)
          (hscale.trans (mul_le_mul_of_nonneg_left hbern hs₀.le)) _
      _ = _ := by
        rw [mul_pow, hs₂, ← pow_mul, ← pow_mul, Nat.mul_comm j 2]
  calc
    _ ≤ ∑ t ∈ (univ : Finset (Fin n)).powerset,
          (n : ℝ) * ((1 + Δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i) := by
      refine sum_le_sum fun t _ ↦ ?_
      calc
        _ ≤ (t.card.factorial : ℝ) * ((n : ℝ) * ((1 + u) ^ 2) ^ t.card) *
              (1 + δ) ^ t.card * ∏ i ∈ t, w i :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hq _) (Nat.cast_nonneg _))
              (pow_nonneg (by positivity) _))
            (prod_nonneg fun i _ ↦ hw₀ i)
        _ = _ := by
          rw [hΔ, mul_pow (1 + δ) ((1 + u) ^ 2)]
          ring
    _ = (n : ℝ) * ∑ t ∈ (univ : Finset (Fin n)).powerset,
          (1 + Δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i := (mul_sum ..).symm
    _ ≤ (n : ℝ) * (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left
        (coexposure_weighted_powerset_sum_le_sqrt hn hw₀ hw hΔ₀ hpert)
        (Nat.cast_nonneg n)
    _ = _ := by ring

/-- The quadratic bound in the nonnegative extended-real form used by the
reverse successor moment. -/
theorem reverse_weighted_powerset_sum_le_n_mul_sqrt_ennreal {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (t.card.factorial : ℝ≥0∞) * ((t.card : ℝ≥0∞) + 1) ^ 2 *
        (ENNReal.ofReal (1 + δ)) ^ t.card * ∏ i ∈ t, ENNReal.ofReal (w i)) ≤
      ENNReal.ofReal (2 * Real.exp ((4 * C + 3 + 3 / 2) ^ 2 / 2) * (n : ℝ) * Real.sqrt n) := by
  have ha : 0 ≤ 1 + δ := by positivity
  calc
    _ = ENNReal.ofReal (∑ t ∈ (univ : Finset (Fin n)).powerset,
          (t.card.factorial : ℝ) * ((t.card : ℝ) + 1) ^ 2 *
            (1 + δ) ^ t.card * ∏ i ∈ t, w i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun t _ ↦
        mul_nonneg (by positivity) (prod_nonneg fun i _ ↦ hw₀ i))]
      refine sum_congr rfl fun t _ ↦ ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_pow ha,
        ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hw₀ i)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (reverse_weighted_powerset_sum_le_n_mul_sqrt hn hw₀ hw hδ₀ hδ)

end LennonPittelFormalization

module

public import LennonPittel.CoexposureGaussianSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Gaussian bounds for the singleton cycle length

The two terms of the singleton forest estimate contain normalized falling
factorials at lengths `k` and `k - 1`. Both can absorb the small forward
perturbation with a common Gaussian envelope at length `k`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace LennonPittelFormalization

private theorem perturbedDescFactorial_le {n j k : ℕ} (hn : 0 < n) (hjn : j ≤ n)
    (hkj : k ≤ j + 1) (hkj₂ : k ≤ 2 * j) {η : ℝ}
    (hη₀ : 0 ≤ η) (hη : η ≤ 1 / Real.sqrt (n : ℝ)) :
    (1 + η) ^ k * ((n.descFactorial j : ℝ) / (n : ℝ) ^ j) ≤
      Real.exp 4 * Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ))) := by
  let r := Real.sqrt (n : ℝ)
  let t := (j : ℝ) / r
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₂ : r ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht₂ : (j : ℝ) ^ 2 / (n : ℝ) = t ^ 2 := by
    rw [show t ^ 2 = (j : ℝ) ^ 2 / r ^ 2 by simp [t, div_pow], hr₂]
  have ht₁ : (j : ℝ) / (n : ℝ) ≤ t := by
    rw [← hr₂, pow_two, ← div_div]
    exact div_le_self ht hr₁
  have hkη : (k : ℝ) * η ≤ t + 1 := calc
    _ ≤ (k : ℝ) * (1 / r) := mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg k)
    _ ≤ ((j : ℝ) + 1) * (1 / r) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) (by positivity)
    _ = t + 1 / r := by dsimp [t]; ring
    _ ≤ t + 1 := add_le_add_right ((div_le_one hr).mpr hr₁) _
  have hk₂ : (k : ℝ) ^ 2 / (16 * (n : ℝ)) ≤ t ^ 2 / 4 := by
    have hk' : (k : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hkj₂
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) k) hk' 2
    have hdiv := div_le_div_of_nonneg_right hpow
      (show 0 ≤ 16 * (n : ℝ) by positivity)
    rw [← ht₂]
    calc
      _ ≤ (2 * (j : ℝ)) ^ 2 / (16 * (n : ℝ)) := hdiv
      _ = (j : ℝ) ^ 2 / (n : ℝ) / 4 := by ring
  have hexp : (k : ℝ) * η - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)) ≤
      4 - (k : ℝ) ^ 2 / (16 * (n : ℝ)) := calc
    _ = (k : ℝ) * η - ((j : ℝ) ^ 2 / (n : ℝ) - (j : ℝ) / (n : ℝ)) / 2 := by
      ring
    _ ≤ 1 + 3 * t / 2 - t ^ 2 / 2 := by rw [ht₂]; linarith only [hkη, ht₁]
    _ ≤ 4 - t ^ 2 / 4 := by nlinarith only [sq_nonneg (t - 3)]
    _ ≤ 4 - (k : ℝ) ^ 2 / (16 * (n : ℝ)) := by linarith only [hk₂]
  calc
    _ ≤ (Real.exp η) ^ k *
        Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) :=
      mul_le_mul
        (pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp η) _)
        (descFactorial_div_pow_le_exp hn hjn) (by positivity) (by positivity)
    _ = Real.exp ((k : ℝ) * η - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert hexp using 1
      ring

/-- Uniform per-length Gaussian bound for the two terms in the singleton forest estimate. -/
theorem perturbedCycleLength_bound {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n)
    {η τ s : ℝ} (hη₀ : 0 ≤ η) (hη : η ≤ 1 / Real.sqrt (n : ℝ))
    (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    (1 + η) ^ k * (τ / (k : ℝ) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) +
      s * ((n.descFactorial (k - 1) : ℝ) / (n : ℝ) ^ (k - 1))) ≤
      Real.exp 4 * Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ))) * (τ / (k : ℝ) + s) := by
  have hmain := perturbedDescFactorial_le hn hkn (show k ≤ k + 1 by omega)
    (show k ≤ 2 * k by omega) hη₀ hη
  have hpoint := perturbedDescFactorial_le hn (show k - 1 ≤ n by omega)
    (show k ≤ (k - 1) + 1 by omega) (show k ≤ 2 * (k - 1) by omega) hη₀ hη
  rw [mul_add, mul_add]
  apply add_le_add
  · convert mul_le_mul_of_nonneg_right hmain (div_nonneg hτ (Nat.cast_nonneg k)) using 1
    ring
  · convert mul_le_mul_of_nonneg_right hpoint hs using 1
    ring

/-- The Gaussian envelope on singleton rotation lengths. -/
noncomputable def singletonLengthGaussian (n k : ℕ) : ℝ :=
  Real.exp (-(k : ℝ) ^ 2 / (16 * (n : ℝ)))

private theorem singletonLengthGaussian_eq (n k : ℕ) :
    singletonLengthGaussian n k = Real.exp (-((k : ℝ) / Real.sqrt n) ^ 2 / 16) := by
  unfold singletonLengthGaussian
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
  congr 1
  ring

private theorem singletonLengthGaussian_le_one (n k : ℕ) : singletonLengthGaussian n k ≤ 1 := by
  unfold singletonLengthGaussian
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
    (by positivity))

private theorem expGeometric_sum_le (s : Finset ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ k ∈ s, Real.exp (-(k : ℝ) / r)) ≤ 1 + r := by
  let q := Real.exp (-(1 / r))
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (one_div_pos.mpr hr))
  have hq : q ≤ r / (1 + r) := calc
    _ = (Real.exp (1 / r))⁻¹ := Real.exp_neg _
    _ ≤ (1 / r + 1)⁻¹ := inv_anti₀ (by positivity) (Real.add_one_le_exp (1 / r))
    _ = _ := by field_simp
  have hmul : 1 ≤ (1 + r) * (1 - q) := by
    have h := (le_div_iff₀ (by positivity : 0 < 1 + r)).mp hq
    nlinarith only [h]
  calc
    _ = ∑ k ∈ s, q ^ k := by
      refine sum_congr rfl fun k _ ↦ ?_
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ∑' k : ℕ, q ^ k :=
      (summable_geometric_of_lt_one hq₀ hq₁).sum_le_tsum s (fun _ _ ↦ by positivity)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq₀ hq₁
    _ ≤ 1 + r := by
      rw [← one_div]
      exact (div_le_iff₀ (sub_pos.mpr hq₁)).mpr hmul

/-- The number of effective terms in the Gaussian length sum is of order square root. -/
theorem singletonLengthGaussian_sum_le {n : ℕ} (hn : 0 < n) (K : Finset ℕ) :
    (∑ k ∈ K, singletonLengthGaussian n k) ≤ 2 * Real.exp 4 * Real.sqrt n := by
  let r := Real.sqrt (n : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  calc
    _ ≤ ∑ k ∈ K, Real.exp 4 * Real.exp (-(k : ℝ) / r) := by
      refine sum_le_sum fun k _ ↦ ?_
      rw [singletonLengthGaussian_eq, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      change -((k : ℝ) / r) ^ 2 / 16 ≤ 4 + -(k : ℝ) / r
      rw [show -(k : ℝ) / r = -((k : ℝ) / r) by ring]
      generalize (k : ℝ) / r = t
      nlinarith only [sq_nonneg (t - 8)]
    _ = Real.exp 4 * ∑ k ∈ K, Real.exp (-(k : ℝ) / r) := (mul_sum ..).symm
    _ ≤ Real.exp 4 * (1 + r) :=
      mul_le_mul_of_nonneg_left (expGeometric_sum_le K hr) (Real.exp_nonneg _)
    _ ≤ 2 * Real.exp 4 * r := by
      have h := mul_nonneg (Real.exp_nonneg 4) (sub_nonneg.mpr hr₁)
      nlinarith only [h]

/-- Summing the singleton Gaussian bound gives harmonic and square-root contributions. -/
theorem singletonLengthGaussian_countSum_le {n : ℕ} (hn : 0 < n)
    {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      τ * (1 + Real.log n) + 2 * Real.exp 4 * Real.sqrt n * s := by
  have hH : (∑ k ∈ Icc 2 n, (k : ℝ)⁻¹) ≤ 1 + Real.log n := calc
    _ ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg
      (by intro k hk; simp only [mem_Icc] at hk ⊢; omega) (fun _ _ _ ↦ by positivity)
    _ = (harmonic n : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log n
  have hweighted :
      (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ))) ≤
        τ * (1 + Real.log n) := calc
    _ ≤ ∑ k ∈ Icc 2 n, τ / (k : ℝ) :=
      sum_le_sum fun k _ ↦ mul_le_of_le_one_left (by positivity)
        (singletonLengthGaussian_le_one n k)
    _ = τ * ∑ k ∈ Icc 2 n, (k : ℝ)⁻¹ := by simp only [mul_sum, div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left hH hτ
  calc
    _ = (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ))) +
        (∑ k ∈ Icc 2 n, singletonLengthGaussian n k) * s := by
      simp_rw [sum_mul, ← sum_add_distrib, mul_add]
    _ ≤ _ := add_le_add hweighted
      (mul_le_mul_of_nonneg_right (singletonLengthGaussian_sum_le hn (Icc 2 n)) hs)

open scoped Classical in
/-- Long singleton cycles have small weighted Gaussian mass. The first term is
already small at the singleton deficit scale; the second decays in the cutoff. -/
theorem singletonLengthGaussian_longSum_le {n : ℕ} (hn : 0 < n) (a : ℝ)
    {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) :
    (∑ k ∈ (Icc 2 n).filter (fun k : ℕ ↦ a * Real.sqrt n < (k : ℝ)),
      (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      2 * Real.exp 4 * τ * Real.sqrt n + 6 * Real.exp 16 * Real.exp (-a) * s * (n : ℝ) := by
  let r := Real.sqrt (n : ℝ)
  let K := (Icc 2 n).filter (fun k : ℕ ↦ a * r < (k : ℝ))
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₂ : r ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hfirst : (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ))) ≤
      2 * Real.exp 4 * τ * r := calc
    _ = (∑ k ∈ K, singletonLengthGaussian n k) * τ := by
      rw [sum_mul]
      refine sum_congr rfl fun k hk ↦ ?_
      have hk₀ : (k : ℝ) ≠ 0 := by
        have hk₂ := (mem_Icc.mp (mem_filter.mp hk).1).1
        exact_mod_cast (show k ≠ 0 by omega)
      field_simp
    _ ≤ (2 * Real.exp 4 * r) * τ :=
      mul_le_mul_of_nonneg_right (singletonLengthGaussian_sum_le hn K) hτ
    _ = _ := by ring
  have hsecond : (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k) ≤
      6 * Real.exp 16 * Real.exp (-a) * (n : ℝ) := by
    let B := Real.exp 16 * Real.exp (-a)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hterm (k : ℕ) (hk : k ∈ K) :
        (k : ℝ) * singletonLengthGaussian n k ≤
          (2 * r * B) * Real.exp (-(k : ℝ) / (2 * r)) := by
      let t := (k : ℝ) / r
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hat : a < t := (lt_div_iff₀ hr).mpr (mem_filter.mp hk).2
      have ht_exp : t ≤ 2 * Real.exp (t / 2) := by linarith only [Real.add_one_le_exp (t / 2)]
      have hG : singletonLengthGaussian n k ≤ B * Real.exp (-t) := by
        rw [singletonLengthGaussian_eq]
        dsimp only [B]
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        change -t ^ 2 / 16 ≤ 16 + -a + -t
        nlinarith only [sq_nonneg (t - 16), hat]
      have hkr : (k : ℝ) = r * t := by dsimp [t]; field_simp
      calc
        _ ≤ (k : ℝ) * (B * Real.exp (-t)) := mul_le_mul_of_nonneg_left hG (by positivity)
        _ = (r * B * Real.exp (-t)) * t := by rw [hkr]; ring
        _ ≤ (r * B * Real.exp (-t)) * (2 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left ht_exp (by positivity)
        _ = _ := by
          rw [show (r * B * Real.exp (-t)) * (2 * Real.exp (t / 2)) =
            (2 * r * B) * (Real.exp (-t) * Real.exp (t / 2)) by ring, ← Real.exp_add]
          congr 2
          dsimp [t]
          ring
    calc
      _ ≤ ∑ k ∈ K, (2 * r * B) * Real.exp (-(k : ℝ) / (2 * r)) :=
        sum_le_sum hterm
      _ = (2 * r * B) * ∑ k ∈ K, Real.exp (-(k : ℝ) / (2 * r)) := (mul_sum ..).symm
      _ ≤ (2 * r * B) * (1 + 2 * r) :=
        mul_le_mul_of_nonneg_left (expGeometric_sum_le K (by positivity : 0 < 2 * r))
          (by positivity)
      _ ≤ (2 * r * B) * (3 * r) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [← hr₂]; dsimp [B]; ring
  change (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤ _
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul]
  refine add_le_add hfirst ((mul_le_mul_of_nonneg_right hsecond hs).trans_eq ?_)
  ring

private theorem sqrt_mul_sqrt_sqrt_eq_rpow {n : ℕ} (hn : 0 < n) :
    Real.sqrt n * Real.sqrt (Real.sqrt n) = (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow (n : ℝ), Real.sqrt_eq_rpow ((n : ℝ) ^ (1 / (2 : ℝ))),
    ← Real.rpow_mul hn'.le, ← Real.rpow_add hn']
  norm_num

/-- A uniform deficit of order `n⁻³/⁴` and a squared-share budget of order
`n⁻¹` give a summed count bound of order `n⁻¹/²`. -/
theorem singletonLengthGaussian_countSum_le_inv_sqrt {n : ℕ} (hn : 0 < n)
    {τ s T S : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hτn : τ ≤ T / (n : ℝ) ^ (3 / 4 : ℝ)) (hsn : s ≤ S / (n : ℝ)) :
    (∑ k ∈ Icc 2 n, singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      (4 * T + 2 * Real.exp 4 * S) / Real.sqrt n := by
  let r := Real.sqrt (n : ℝ)
  let q := Real.sqrt r
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.mpr hn'
  have hq : 0 < q := Real.sqrt_pos.mpr hr
  have hr₂ : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn'.le
  have hq₂ : q ^ 2 = r := Real.sq_sqrt hr.le
  have hq₄ : q ^ 4 = (n : ℝ) := by rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq₂, hr₂]
  have hlog : 1 + Real.log n ≤ 4 * q := by
    rw [← hq₄, Real.log_pow]
    norm_num
    linarith only [Real.log_le_sub_one_of_pos hq]
  have hτT : τ * (r * q) ≤ T := by
    rw [show r * q = (n : ℝ) ^ (3 / 4 : ℝ) from sqrt_mul_sqrt_sqrt_eq_rpow hn]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hn' _)).mp hτn
  have hsS : s * (n : ℝ) ≤ S := (le_div_iff₀ hn').mp hsn
  have hfirst : (τ * (1 + Real.log n)) * r ≤ 4 * T := calc
    _ ≤ (τ * (4 * q)) * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hτ) hr.le
    _ = 4 * (τ * (r * q)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hτT (by norm_num)
  have hsecond : (2 * Real.exp 4 * r * s) * r ≤ 2 * Real.exp 4 * S := calc
    _ = (2 * Real.exp 4) * (s * r ^ 2) := by ring
    _ ≤ _ := by
      rw [hr₂]
      exact mul_le_mul_of_nonneg_left hsS (by positivity)
  refine (singletonLengthGaussian_countSum_le hn hτ hs).trans ((le_div_iff₀ hr).mpr ?_)
  change (τ * (1 + Real.log n) + 2 * Real.exp 4 * r * s) * r ≤ _
  rw [add_mul]
  exact add_le_add hfirst hsecond

open scoped Classical in
/-- At the regular singleton budgets, the weighted long-length contribution
vanishes with the cutoff, up to an error of order `n⁻¹/⁴`. -/
theorem singletonLengthGaussian_longSum_le_of_budgets {n : ℕ} (hn : 0 < n) (a : ℝ)
    {τ s T S : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hτn : τ ≤ T / (n : ℝ) ^ (3 / 4 : ℝ)) (hsn : s ≤ S / (n : ℝ)) :
    (∑ k ∈ (Icc 2 n).filter (fun k : ℕ ↦ a * Real.sqrt n < (k : ℝ)),
      (k : ℝ) * singletonLengthGaussian n k * (τ / (k : ℝ) + s)) ≤
      (2 * Real.exp 4 * T) / Real.sqrt (Real.sqrt n) + 6 * Real.exp 16 * Real.exp (-a) * S := by
  let r := Real.sqrt (n : ℝ)
  let q := Real.sqrt r
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.mpr hn'
  have hq : 0 < q := Real.sqrt_pos.mpr hr
  have hτT : τ * r ≤ T / q := by
    rw [← (show r * q = (n : ℝ) ^ (3 / 4 : ℝ) from sqrt_mul_sqrt_sqrt_eq_rpow hn)] at hτn
    exact (le_div_iff₀ hq).mpr (by
      rw [mul_assoc]
      exact (le_div_iff₀ (mul_pos hr hq)).mp hτn)
  have hsS : s * (n : ℝ) ≤ S := (le_div_iff₀ hn').mp hsn
  refine (singletonLengthGaussian_longSum_le hn a hτ hs).trans ?_
  change 2 * Real.exp 4 * τ * r + 6 * Real.exp 16 * Real.exp (-a) * s * (n : ℝ) ≤
    (2 * Real.exp 4 * T) / q + 6 * Real.exp 16 * Real.exp (-a) * S
  rw [mul_assoc (2 * Real.exp 4) τ r, mul_div_assoc,
    mul_assoc (6 * Real.exp 16 * Real.exp (-a)) s (n : ℝ)]
  exact add_le_add (mul_le_mul_of_nonneg_left hτT (by positivity))
    (mul_le_mul_of_nonneg_left hsS (by positivity))

end LennonPittelFormalization

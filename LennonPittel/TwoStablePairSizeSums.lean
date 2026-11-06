module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Summing the two-stable-matching size bound

The size kernel is the factorial-ratio envelope in the two-matching estimate,
without the common factor proportional to one plus the logarithm of the market size.
The results here use only the bound on each size, not the score law that produces it.
-/

@[expose] public section

open Finset

namespace LennonPittelFormalization

/-- Both orientations are nontrivial and use disjoint sets of labels. -/
def ValidPairSizes (n : ℕ) (p : ℕ × ℕ) : Prop :=
  2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 + p.2 ≤ n

/-- The size-dependent factor in the upper bound for incomparable pairs. -/
noncomputable def twoStablePairSizeKernel (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  (n : ℝ) ^ 3 / ((↑(n - p.1) : ℝ) * ↑(n - p.2)) *
    ((↑((n - p.1).descFactorial p.2) : ℝ) / ↑(n.descFactorial p.2))

theorem twoStablePairSizeKernel_nonneg (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ twoStablePairSizeKernel n p := by
  unfold twoStablePairSizeKernel
  positivity

private theorem cast_descFactorial_eq_div {n k : ℕ} (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = (↑n.factorial : ℝ) / ↑(n - k).factorial := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  exact_mod_cast Nat.factorial_mul_descFactorial hk

/-- The kernel does not distinguish the two orientations. -/
theorem twoStablePairSizeKernel_swap {n u v : ℕ} (h : u + v ≤ n) :
    twoStablePairSizeKernel n (v, u) = twoStablePairSizeKernel n (u, v) := by
  have hu : u ≤ n := by omega
  have hv : v ≤ n := by omega
  have huv : u ≤ n - v := by omega
  have hvu : v ≤ n - u := by omega
  have ht : n - v - u = n - u - v := by omega
  change (n : ℝ) ^ 3 / (↑(n - v) * ↑(n - u)) *
      (↑((n - v).descFactorial u) / ↑(n.descFactorial u)) =
    (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
      (↑((n - u).descFactorial v) / ↑(n.descFactorial v))
  rw [cast_descFactorial_eq_div hu, cast_descFactorial_eq_div hv,
    cast_descFactorial_eq_div huv, cast_descFactorial_eq_div hvu, ht]
  rw [mul_comm (↑(n - v) : ℝ) ↑(n - u)]
  congr 1
  field_simp

/-- Factorial value of the beta integral with parameters k and n - k. -/
noncomputable def pairSizeBetaFactor (n k : ℕ) : ℝ :=
  (↑(k - 1).factorial : ℝ) * ↑(n - k - 1).factorial / ↑(n - 1).factorial

private theorem cast_factorial_pred {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) = (k : ℝ) * ↑(k - 1).factorial := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [Nat.factorial_succ]

/-- The beta factors and the unrestricted labeled-pair multiplier simplify to the
falling-factorial kernel. The two orientation derangement fractions are separate. -/
theorem twoStablePairSizeKernel_eq_beta_factors {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    twoStablePairSizeKernel n (u, v) =
      ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) *
        (pairSizeBetaFactor n u * pairSizeBetaFactor n v /
          ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hvn : v ≤ n := by omega
  have hvu : v ≤ n - u := by omega
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  have hn : 0 < n := by omega
  calc
    _ = (n : ℝ) ^ 3 * ↑(n - u - 1).factorial * ↑(n - v - 1).factorial /
        (↑(n - u - v).factorial * ↑n.factorial) := by
      change (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
        (↑((n - u).descFactorial v) / ↑(n.descFactorial v)) = _
      rw [cast_descFactorial_eq_div hvu, cast_descFactorial_eq_div hvn,
        cast_factorial_pred hnu, cast_factorial_pred hnv]
      field_simp
    _ = _ := by
      unfold pairSizeBetaFactor
      rw [cast_factorial_pred hn]
      field_simp

/-- Sampling without replacement stays below the corresponding independent power. -/
private theorem descFactorial_ratio_le_pow {n m v : ℕ} (hmn : m ≤ n) (hvm : v ≤ m) :
    ((m.descFactorial v : ℕ) : ℝ) / ↑(n.descFactorial v) ≤ ((m : ℝ) / n) ^ v := by
  simp only [Nat.descFactorial_eq_prod_range, Nat.cast_prod, ← prod_div_distrib]
  calc
    _ ≤ ∏ _i ∈ range v, (m : ℝ) / n := by
      refine prod_le_prod₀ (fun i _ ↦ by positivity) fun i hi ↦ ?_
      have him : i ≤ m := by have := mem_range.mp hi; omega
      have hin : i < n := by have := mem_range.mp hi; omega
      have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsub : (0 : ℝ) < (n : ℝ) - i := sub_pos.mpr (by exact_mod_cast hin)
      rw [Nat.cast_sub him, Nat.cast_sub hin.le]
      apply (div_le_div_iff₀ hsub hn).2
      have hmul := mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ n by exact_mod_cast hmn)
        (show (0 : ℝ) ≤ i by positivity)
      nlinarith only [hmul]
    _ = _ := by simp [div_pow]

/-- For central sizes the factorial-ratio bound is controlled by an exponential. -/
theorem twoStablePairSizeKernel_le_central {n u v : ℕ} (hn : 0 < n) (h : u + v ≤ n)
    (hu : 2 * u ≤ n) (hv : 2 * v ≤ n) :
    twoStablePairSizeKernel n (u, v) ≤ 4 * n * Real.exp (-(u : ℝ) * v / n) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hun : u ≤ n := by omega
  have hvn : v ≤ n := by omega
  have hup : (n : ℝ) / 2 ≤ n - u := by
    have h' : (2 : ℝ) * u ≤ n := by exact_mod_cast hu
    linarith
  have hvp : (n : ℝ) / 2 ≤ n - v := by
    have h' : (2 : ℝ) * v ≤ n := by exact_mod_cast hv
    linarith
  unfold twoStablePairSizeKernel
  rw [Nat.cast_sub hun, Nat.cast_sub hvn]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · calc
      _ ≤ (n : ℝ) ^ 3 / ((n / 2) * (n / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul hup hvp (by positivity) (by linarith))
      _ = _ := by field_simp; ring
  · calc
      _ ≤ ((↑(n - u) : ℝ) / n) ^ v :=
        descFactorial_ratio_le_pow (Nat.sub_le n u) (by omega)
      _ = (1 - (u : ℝ) / n) ^ v := by rw [Nat.cast_sub hun, sub_div, div_self hn'.ne']
      _ ≤ Real.exp (-(u : ℝ) * v / n) := by
        have hnon : 0 ≤ 1 - (u : ℝ) / n :=
          sub_nonneg.mpr ((div_le_iff₀ hn').2
            (by simpa using (Nat.cast_le.mpr hun : (u : ℝ) ≤ n)))
        calc
          _ ≤ Real.exp (-(u : ℝ) / n) ^ v := by
            apply pow_le_pow_left₀ hnon
            simpa only [neg_div] using Real.one_sub_le_exp_neg ((u : ℝ) / n)
          _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

private theorem sum_pow_Icc_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (l m : ℕ) :
    (∑ j ∈ Icc l m, q ^ j) ≤ q ^ l / (1 - q) := by
  calc
    _ = ∑ j ∈ range (m + 1 - l), q ^ (l + j) := by
      refine sum_bij (fun j _ ↦ j - l) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [mem_Icc] at hj
        exact mem_range.mpr (by omega)
      · intro a ha b hb hab
        change a - l = b - l at hab
        simp only [mem_Icc] at ha hb
        omega
      · intro j hj
        have := mem_range.mp hj
        refine ⟨l + j, mem_Icc.mpr (by omega), ?_⟩
        omega
      · intro j hj
        rw [Nat.add_sub_of_le (mem_Icc.mp hj).1]
    _ = q ^ l * ∑ j ∈ range (m + 1 - l), q ^ j := by simp_rw [pow_add, mul_sum]
    _ ≤ q ^ l * ∑' j : ℕ, q ^ j := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hq₀ hq₁).sum_le_tsum _ (fun _ _ ↦ by positivity))
      (by positivity)
    _ = _ := by rw [tsum_geometric_of_lt_one hq₀ hq₁, div_eq_mul_inv]

private theorem sum_exp_neg_mul_Icc_le {a : ℝ} (ha : 0 < a) (m : ℕ) :
    (∑ j ∈ Icc 1 m, Real.exp (-a * (j : ℝ))) ≤ a⁻¹ := by
  let q := Real.exp (-a)
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hqmul : q * (a + 1) ≤ 1 := by
    dsimp [q]
    rw [Real.exp_neg, ← div_eq_inv_mul]
    apply (div_le_iff₀ (Real.exp_pos a)).2
    simpa only [one_mul] using Real.add_one_le_exp a
  calc
    _ = ∑ j ∈ Icc 1 m, q ^ j := by
      refine sum_congr rfl fun j _ ↦ ?_
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ q ^ 1 / (1 - q) := sum_pow_Icc_le hq₀ hq₁ _ _
    _ ≤ a⁻¹ := by
      rw [pow_one, ← one_div a]
      apply (div_le_div_iff₀ (sub_pos.mpr hq₁) ha).2
      linarith only [hqmul]

/-- In the central range both sizes are at most half the number of labels. -/
def CentralPairSizes (n : ℕ) (p : ℕ × ℕ) : Prop :=
  2 * p.1 ≤ n ∧ 2 * p.2 ≤ n

private theorem sum_inv_Icc_le_log (m : ℕ) :
    (∑ v ∈ Icc 1 m, (v : ℝ)⁻¹) ≤ 1 + Real.log m := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log m

/-- Central pairs with right orientation size at most the cutoff pay one harmonic sum. -/
theorem sum_twoStablePairSizeKernel_le_central_right {n m : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (hc : ∀ p ∈ s, CentralPairSizes n p) (hm : ∀ p ∈ s, p.2 ≤ m) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤
      4 * (n : ℝ) ^ 2 * (1 + Real.log m) := by
  have hbox : s ⊆ Icc 1 n ×ˢ Icc 1 m := by
    intro p hp
    obtain ⟨hu, hv, huv⟩ := hs p hp
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
      mem_Icc.mpr ⟨by omega, hm p hp⟩⟩
  calc
    _ ≤ ∑ p ∈ s, 4 * n * Real.exp (-(p.1 : ℝ) * p.2 / n) :=
      sum_le_sum fun p hp ↦ twoStablePairSizeKernel_le_central hn
        (hs p hp).2.2 (hc p hp).1 (hc p hp).2
    _ ≤ ∑ p ∈ Icc 1 n ×ˢ Icc 1 m, 4 * n * Real.exp (-(p.1 : ℝ) * p.2 / n) :=
      sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ ↦ by positivity)
    _ = ∑ v ∈ Icc 1 m, 4 * n * ∑ u ∈ Icc 1 n, Real.exp (-((v : ℝ) / n) * u) := by
      rw [sum_product_right]
      refine sum_congr rfl fun v _ ↦ ?_
      rw [mul_sum]
      refine sum_congr rfl fun u _ ↦ ?_
      ring_nf
    _ ≤ ∑ v ∈ Icc 1 m, 4 * n * ((v : ℝ) / n)⁻¹ := by
      refine sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left (sum_exp_neg_mul_Icc_le ?_ n)
        (by positivity)
      have hvp : 0 < v := by have := (mem_Icc.mp hv).1; omega
      positivity
    _ = 4 * (n : ℝ) ^ 2 * ∑ v ∈ Icc 1 m, (v : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun v _ ↦ ?_
      rw [inv_div]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log m) (by positivity)

/-- Central pairs with product at least n times z pay an exponential factor. -/
theorem sum_twoStablePairSizeKernel_le_central_large_product {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (hc : ∀ p ∈ s, CentralPairSizes n p) (z : ℝ)
    (hz : ∀ p ∈ s, z ≤ (p.1 : ℝ) * p.2 / n) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-z) := by
  have hbox : s ⊆ Icc 1 n ×ˢ Icc 1 n := by
    intro p hp
    obtain ⟨hu, hv, huv⟩ := hs p hp
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
      mem_Icc.mpr ⟨by omega, by omega⟩⟩
  calc
    _ ≤ ∑ _p ∈ s, 4 * n * Real.exp (-z) := by
      refine sum_le_sum fun p hp ↦ (twoStablePairSizeKernel_le_central hn
        (hs p hp).2.2 (hc p hp).1 (hc p hp).2).trans ?_
      gcongr
      simpa only [neg_mul, neg_div] using neg_le_neg (hz p hp)
    _ ≤ ∑ _p ∈ Icc 1 n ×ˢ Icc 1 n, 4 * n * Real.exp (-z) :=
      sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ ↦ by positivity)
    _ = _ := by
      rw [sum_const, card_product]
      simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- The central sector with product at least three times n log n has kernel mass at most four. -/
theorem sum_twoStablePairSizeKernel_le_central_log_product {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (hc : ∀ p ∈ s, CentralPairSizes n p)
    (hz : ∀ p ∈ s, 3 * Real.log n ≤ (p.1 : ℝ) * p.2 / n) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 4 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-(3 * Real.log n)) :=
      sum_twoStablePairSizeKernel_le_central_large_product hn s hs hc _ hz
    _ = _ := by
      rw [Real.exp_neg, ← show ((3 : ℕ) : ℝ) = 3 by norm_num,
        Real.exp_nat_mul, Real.exp_log hn']
      field_simp

private theorem sum_le_filtered_cover {α : Type*} (s : Finset α) (f : α → ℝ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hf : ∀ p ∈ s, 0 ≤ f p) (hcov : ∀ p ∈ s, P p ∨ Q p) :
    (∑ p ∈ s, f p) ≤ (∑ p ∈ s.filter P, f p) + ∑ p ∈ s.filter Q, f p := by
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun p hp ↦ ?_
  by_cases hP : P p
  · by_cases hQ : Q p
    · simp only [hP, hQ, ite_true]
      exact le_add_of_nonneg_right (hf p hp)
    · simp [hP, hQ]
  · have hQ := (hcov p hp).resolve_left hP
    simp [hP, hQ]

private def swapSizePairs (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  s.map (Equiv.prodComm ℕ ℕ).toEmbedding

private theorem mem_swapSizePairs {p : ℕ × ℕ} {s : Finset (ℕ × ℕ)} :
    p ∈ swapSizePairs s ↔ p.swap ∈ s := by
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    change q.swap = p at hqp
    rw [← hqp, Prod.swap_swap]
    exact hq
  · intro hp
    exact mem_map.mpr ⟨p.swap, hp, Prod.swap_swap _⟩

private theorem sum_twoStablePairSizeKernel_swapSizePairs {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) :
    (∑ p ∈ swapSizePairs s, twoStablePairSizeKernel n p) =
      ∑ p ∈ s, twoStablePairSizeKernel n p := by
  rw [swapSizePairs, sum_map]
  exact sum_congr rfl fun p hp ↦ twoStablePairSizeKernel_swap (hs p hp).2.2

private theorem validPairSizes_swap {n : ℕ} {p : ℕ × ℕ} (h : ValidPairSizes n p) :
    ValidPairSizes n p.swap := by
  exact ⟨h.2.1, h.1, by simpa [add_comm] using h.2.2⟩

private theorem centralPairSizes_swap {n : ℕ} {p : ℕ × ℕ} (h : CentralPairSizes n p) :
    CentralPairSizes n p.swap :=
  ⟨h.2, h.1⟩

/-- Central pairs with either orientation size at most the cutoff pay two harmonic sums. -/
theorem sum_twoStablePairSizeKernel_le_central_small {n m : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (hc : ∀ p ∈ s, CentralPairSizes n p) (hm : ∀ p ∈ s, p.1 ≤ m ∨ p.2 ≤ m) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤
      8 * (n : ℝ) ^ 2 * (1 + Real.log m) := by
  let L := s.filter fun p ↦ p.1 ≤ m
  let R := s.filter fun p ↦ p.2 ≤ m
  have hL (p) (hp : p ∈ L) : p ∈ s ∧ p.1 ≤ m := mem_filter.mp hp
  have hR (p) (hp : p ∈ R) : p ∈ s ∧ p.2 ≤ m := mem_filter.mp hp
  have hsL (p) (hp : p ∈ swapSizePairs L) : ValidPairSizes n p := by
    simpa using validPairSizes_swap (hs p.swap (hL _ (mem_swapSizePairs.mp hp)).1)
  have hcL (p) (hp : p ∈ swapSizePairs L) : CentralPairSizes n p := by
    simpa using centralPairSizes_swap (hc p.swap (hL _ (mem_swapSizePairs.mp hp)).1)
  calc
    _ ≤ (∑ p ∈ L, twoStablePairSizeKernel n p) + ∑ p ∈ R, twoStablePairSizeKernel n p :=
      sum_le_filtered_cover s _ _ _ (fun p _ ↦ twoStablePairSizeKernel_nonneg n p) hm
    _ = (∑ p ∈ swapSizePairs L, twoStablePairSizeKernel n p) +
          ∑ p ∈ R, twoStablePairSizeKernel n p := by
      rw [sum_twoStablePairSizeKernel_swapSizePairs L (fun p hp ↦ hs p (hL _ hp).1)]
    _ ≤ 4 * (n : ℝ) ^ 2 * (1 + Real.log m) + 4 * (n : ℝ) ^ 2 * (1 + Real.log m) :=
      add_le_add
        (sum_twoStablePairSizeKernel_le_central_right hn _ hsL hcL
          (fun p hp ↦ (hL _ (mem_swapSizePairs.mp hp)).2))
        (sum_twoStablePairSizeKernel_le_central_right hn _
          (fun p hp ↦ hs p (hR _ hp).1) (fun p hp ↦ hc p (hR _ hp).1)
          (fun p hp ↦ (hR _ hp).2))
    _ = _ := by ring

/-- The central small-size contribution has a coefficient linear in the power cutoff. -/
theorem sum_twoStablePairSizeKernel_le_central_small_power {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (hc : ∀ p ∈ s, CentralPairSizes n p) {a : ℝ} (ha : 0 ≤ a)
    (hm : ∀ p ∈ s, (p.1 : ℝ) ≤ (n : ℝ) ^ a ∨ (p.2 : ℝ) ≤ (n : ℝ) ^ a) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤
      8 * (n : ℝ) ^ 2 * (1 + a * Real.log n) := by
  let m := ⌊(n : ℝ) ^ a⌋₊
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hna : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow (Nat.one_le_cast.mpr hn) ha
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.floor_pos.mpr hna)
  have hlog : Real.log m ≤ a * Real.log n := by
    rw [← Real.log_rpow hnp]
    exact Real.log_le_log hmpos (Nat.floor_le (zero_le_one.trans hna))
  calc
    _ ≤ 8 * (n : ℝ) ^ 2 * (1 + Real.log m) :=
      sum_twoStablePairSizeKernel_le_central_small hn s hs hc
        (fun p hp ↦ (hm p hp).imp Nat.le_floor Nat.le_floor)
    _ ≤ _ := by gcongr

private theorem twoStablePairSizeKernel_le_extreme_left {n u v : ℕ} (hn : 0 < n)
    (hu : n < 2 * u) (hv : 2 ≤ v) (h : u + v ≤ n) :
    twoStablePairSizeKernel n (u, v) ≤
      (2 * (n : ℝ) ^ 2 / (n - u : ℕ)) * ((↑(n - u) : ℝ) / n) ^ v := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : (0 : ℝ) < (n - u : ℕ) := by exact_mod_cast (show 0 < n - u by omega)
  have hvn : v ≤ n := by omega
  have hvp : (n : ℝ) / 2 ≤ (n - v : ℕ) := by
    rw [Nat.cast_sub hvn]
    have h' : (2 : ℝ) * v ≤ n := by exact_mod_cast (show 2 * v ≤ n by omega)
    linarith
  unfold twoStablePairSizeKernel
  calc
    _ ≤ (n : ℝ) ^ 3 / ((↑(n - u) : ℝ) * (n / 2)) * ((↑(n - u) : ℝ) / n) ^ v := by
      refine mul_le_mul ?_ (descFactorial_ratio_le_pow (Nat.sub_le n u) (by omega))
        (by positivity) (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hvp ht.le
    _ = _ := by field_simp

private theorem sum_twoStablePairSizeKernel_le_extreme_row {n u : ℕ} (hn : 0 < n)
    (hu : n < 2 * u) (ht : 2 ≤ n - u) :
    (∑ v ∈ Icc 2 (n - u), twoStablePairSizeKernel n (u, v)) ≤ 4 * (n - u : ℕ) := by
  let t := n - u
  let q : ℝ := (t : ℝ) / n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht' : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by dsimp [t]; omega)
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₂ : q ≤ 1 / 2 := by
    apply (div_le_iff₀ hn').2
    have htr : (2 : ℝ) * t ≤ n := by exact_mod_cast (show 2 * t ≤ n by dsimp [t]; omega)
    linarith
  have hq₁ : q < 1 := by linarith
  calc
    _ ≤ ∑ v ∈ Icc 2 t, (2 * (n : ℝ) ^ 2 / t) * q ^ v := by
      refine sum_le_sum fun v hv ↦ ?_
      have hv' := mem_Icc.mp hv
      exact twoStablePairSizeKernel_le_extreme_left hn hu hv'.1 (by omega)
    _ = (2 * (n : ℝ) ^ 2 / t) * ∑ v ∈ Icc 2 t, q ^ v := (mul_sum ..).symm
    _ ≤ (2 * (n : ℝ) ^ 2 / t) * (q ^ 2 / (1 - q)) :=
      mul_le_mul_of_nonneg_left (sum_pow_Icc_le hq₀ hq₁ _ _) (by positivity)
    _ ≤ (2 * (n : ℝ) ^ 2 / t) * (q ^ 2 / (1 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = _ := by change _ = 4 * (t : ℝ); dsimp [q]; field_simp; ring

private theorem sum_twoStablePairSizeKernel_le_extreme_left {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (he : ∀ p ∈ s, n < 2 * p.1) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 4 * (n : ℝ) ^ 2 := by
  have hmaps (p) (hp : p ∈ s) : p.1 ∈ Icc 1 n := by
    obtain ⟨h1, h2, hsum⟩ := hs p hp
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hrow (u : ℕ) :
      (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤ 4 * (n : ℝ) := by
    let row := s.filter (fun p ↦ p.1 = u)
    change (∑ p ∈ row, twoStablePairSizeKernel n p) ≤ _
    by_cases hempty : row = ∅
    · rw [hempty, sum_empty]
      positivity
    obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hps, hpu⟩ := mem_filter.mp hp
    have hu : n < 2 * u := hpu ▸ he p hps
    have ht : 2 ≤ n - u := by obtain ⟨_, _, h⟩ := hs p hps; have := (hs p hps).2.1; omega
    have hbox : row ⊆ {u} ×ˢ Icc 2 (n - u) := by
      intro q hq
      obtain ⟨hqs, hqu⟩ := mem_filter.mp hq
      obtain ⟨_, hq2, hqsum⟩ := hs q hqs
      exact mem_product.mpr ⟨mem_singleton.mpr hqu, mem_Icc.mpr ⟨hq2, by omega⟩⟩
    calc
      _ ≤ ∑ q ∈ {u} ×ˢ Icc 2 (n - u), twoStablePairSizeKernel n q :=
        sum_le_sum_of_subset_of_nonneg hbox (fun q _ _ ↦ twoStablePairSizeKernel_nonneg n q)
      _ = ∑ v ∈ Icc 2 (n - u), twoStablePairSizeKernel n (u, v) := by
        rw [sum_product, sum_singleton]
      _ ≤ 4 * (n - u : ℕ) := sum_twoStablePairSizeKernel_le_extreme_row hn hu ht
      _ ≤ _ := by gcongr; exact Nat.sub_le n u
  calc
    _ = ∑ u ∈ Icc 1 n, ∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p :=
      (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _u ∈ Icc 1 n, 4 * (n : ℝ) := sum_le_sum (fun u _ ↦ hrow u)
    _ = _ := by
      rw [sum_const]
      simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- Pairs with one orientation strictly larger than half have only quadratic kernel mass. -/
theorem sum_twoStablePairSizeKernel_le_extreme {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (he : ∀ p ∈ s, ¬CentralPairSizes n p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 8 * (n : ℝ) ^ 2 := by
  let L := s.filter fun p ↦ n < 2 * p.1
  let R := s.filter fun p ↦ n < 2 * p.2
  have hL (p) (hp : p ∈ L) : p ∈ s ∧ n < 2 * p.1 := mem_filter.mp hp
  have hR (p) (hp : p ∈ R) : p ∈ s ∧ n < 2 * p.2 := mem_filter.mp hp
  have hsR (p) (hp : p ∈ swapSizePairs R) : ValidPairSizes n p := by
    simpa using validPairSizes_swap (hs p.swap (hR _ (mem_swapSizePairs.mp hp)).1)
  calc
    _ ≤ (∑ p ∈ L, twoStablePairSizeKernel n p) + ∑ p ∈ R, twoStablePairSizeKernel n p :=
      sum_le_filtered_cover s _ _ _ (fun p _ ↦ twoStablePairSizeKernel_nonneg n p)
        (fun p hp ↦ by
          by_cases h : n < 2 * p.1
          · exact Or.inl h
          · exact Or.inr (lt_of_not_ge fun hv ↦ he p hp ⟨le_of_not_gt h, hv⟩))
    _ = (∑ p ∈ L, twoStablePairSizeKernel n p) +
          ∑ p ∈ swapSizePairs R, twoStablePairSizeKernel n p := by
      rw [sum_twoStablePairSizeKernel_swapSizePairs R (fun p hp ↦ hs p (hR _ hp).1)]
    _ ≤ 4 * (n : ℝ) ^ 2 + 4 * (n : ℝ) ^ 2 :=
      add_le_add
        (sum_twoStablePairSizeKernel_le_extreme_left hn _
          (fun p hp ↦ hs p (hL _ hp).1) (fun p hp ↦ (hL _ hp).2))
        (sum_twoStablePairSizeKernel_le_extreme_left hn _ hsR
          (fun p hp ↦ (hR _ (mem_swapSizePairs.mp hp)).2))
    _ = _ := by ring

/-- When both central orientation sizes are at least b times the square root,
the exponential separates and leaves no harmonic loss. -/
theorem sum_twoStablePairSizeKernel_le_central_both_long {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (hc : ∀ p ∈ s, CentralPairSizes n p) {b : ℝ} (hb : 0 < b)
    (hl : ∀ p ∈ s, b * Real.sqrt n ≤ (p.1 : ℝ) ∧ b * Real.sqrt n ≤ (p.2 : ℝ)) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 16 * (n : ℝ) ^ 2 / b ^ 2 := by
  let r := Real.sqrt (n : ℝ)
  let a := b / (2 * r)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.mpr hn'
  have ha : 0 < a := by dsimp [a]; positivity
  have hrn : r ^ 2 = n := Real.sq_sqrt hn'.le
  have hscale : a * (n : ℝ) = b * r / 2 := by
    rw [← hrn]
    dsimp [a]
    field_simp
  have hbox : s ⊆ Icc 1 n ×ˢ Icc 1 n := by
    intro p hp
    obtain ⟨hu, hv, huv⟩ := hs p hp
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
      mem_Icc.mpr ⟨by omega, by omega⟩⟩
  calc
    _ ≤ ∑ p ∈ s, 4 * n * (Real.exp (-a * p.1) * Real.exp (-a * p.2)) := by
      refine sum_le_sum fun p hp ↦ (twoStablePairSizeKernel_le_central hn
        (hs p hp).2.2 (hc p hp).1 (hc p hp).2).trans ?_
      have h₁ := mul_le_mul_of_nonneg_left (hl p hp).2 (show (0 : ℝ) ≤ p.1 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (hl p hp).1 (show (0 : ℝ) ≤ p.2 by positivity)
      have hcomp : a * (p.1 : ℝ) + a * p.2 ≤ (p.1 : ℝ) * p.2 / n := by
        apply (le_div_iff₀ hn').2
        calc
          _ = (a * n) * ((p.1 : ℝ) + p.2) := by ring
          _ = ((p.1 : ℝ) * (b * r) + b * r * p.2) / 2 := by rw [hscale]; ring
          _ ≤ _ := by linarith only [h₁, h₂]
      rw [← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      calc
        _ = -((p.1 : ℝ) * p.2 / n) := by ring
        _ ≤ -(a * (p.1 : ℝ) + a * p.2) := neg_le_neg hcomp
        _ = _ := by ring
    _ ≤ ∑ p ∈ Icc 1 n ×ˢ Icc 1 n,
          4 * n * (Real.exp (-a * p.1) * Real.exp (-a * p.2)) :=
      sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ ↦ by positivity)
    _ = 4 * n * (∑ u ∈ Icc 1 n, Real.exp (-a * u)) ^ 2 := by
      rw [sum_product]
      simp only [mul_assoc, ← mul_sum, sq, sum_mul_sum]
    _ ≤ 4 * n * (a⁻¹) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ Real.exp_nonneg _)
        (sum_exp_neg_mul_Icc_le ha n) _
    _ = _ := by
      dsimp [a]
      rw [inv_div, div_pow, mul_pow, hrn]
      ring

private theorem sum_twoStablePairSizeKernel_le_of_central_bound {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) (B : ℝ)
    (hB : ∀ t ⊆ s, (∀ p ∈ t, CentralPairSizes n p) →
      (∑ p ∈ t, twoStablePairSizeKernel n p) ≤ B) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ B + 8 * (n : ℝ) ^ 2 := by
  classical
  let C := s.filter (CentralPairSizes n)
  let E := s.filter (fun p ↦ ¬CentralPairSizes n p)
  calc
    _ = (∑ p ∈ C, twoStablePairSizeKernel n p) + ∑ p ∈ E, twoStablePairSizeKernel n p :=
      (sum_filter_add_sum_filter_not s (CentralPairSizes n) (twoStablePairSizeKernel n)).symm
    _ ≤ _ := add_le_add
      (hB C (filter_subset _ _) (fun p hp ↦ (mem_filter.mp hp).2))
      (sum_twoStablePairSizeKernel_le_extreme hn E (fun p hp ↦ hs p (mem_filter.mp hp).1)
        (fun p hp ↦ (mem_filter.mp hp).2))

/-- All valid sizes have at most quadratic-logarithmic kernel mass. -/
theorem sum_twoStablePairSizeKernel_le_total {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 12 * (n : ℝ) ^ 2 * (1 + Real.log n) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  calc
    _ ≤ 4 * (n : ℝ) ^ 2 * (1 + Real.log n) + 8 * (n : ℝ) ^ 2 :=
      sum_twoStablePairSizeKernel_le_of_central_bound hn s hs _ (fun t ht hc ↦
        sum_twoStablePairSizeKernel_le_central_right hn t
          (fun p hp ↦ hs p (ht hp)) hc
          (fun p hp ↦ (hs p (ht hp)).2.2.trans' (Nat.le_add_left _ _)))
    _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg (n : ℝ)) hlog]

/-- The full small-size contribution includes an additive quadratic extreme term. -/
theorem sum_twoStablePairSizeKernel_le_small_power {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) {a : ℝ} (ha : 0 ≤ a)
    (hm : ∀ p ∈ s, (p.1 : ℝ) ≤ (n : ℝ) ^ a ∨ (p.2 : ℝ) ≤ (n : ℝ) ^ a) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤
      8 * (n : ℝ) ^ 2 * (2 + a * Real.log n) := by
  calc
    _ ≤ 8 * (n : ℝ) ^ 2 * (1 + a * Real.log n) + 8 * (n : ℝ) ^ 2 :=
      sum_twoStablePairSizeKernel_le_of_central_bound hn s hs _ (fun t ht hc ↦
        sum_twoStablePairSizeKernel_le_central_small_power hn t
          (fun p hp ↦ hs p (ht hp)) hc ha (fun p hp ↦ hm p (ht hp)))
    _ = _ := by ring

/-- All pairs with both orientation sizes at least b times the square root
have quadratic kernel mass. -/
theorem sum_twoStablePairSizeKernel_le_both_long {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) {b : ℝ} (hb : 0 < b)
    (hl : ∀ p ∈ s, b * Real.sqrt n ≤ (p.1 : ℝ) ∧ b * Real.sqrt n ≤ (p.2 : ℝ)) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (8 + 16 / b ^ 2) * (n : ℝ) ^ 2 := by
  calc
    _ ≤ 16 * (n : ℝ) ^ 2 / b ^ 2 + 8 * (n : ℝ) ^ 2 :=
      sum_twoStablePairSizeKernel_le_of_central_bound hn s hs _ (fun t ht hc ↦
        sum_twoStablePairSizeKernel_le_central_both_long hn t
          (fun p hp ↦ hs p (ht hp)) hc hb (fun p hp ↦ hl p (ht hp)))
    _ = _ := by ring

/-- The range left after excluding extreme, small, and large-product orientation sizes. -/
def RegularPairSizes (n : ℕ) (a : ℝ) (p : ℕ × ℕ) : Prop :=
  CentralPairSizes n p ∧
    (n : ℝ) ^ a < (p.1 : ℝ) ∧ (n : ℝ) ^ a < (p.2 : ℝ) ∧
    (p.1 : ℝ) * p.2 ≤ 3 * n * Real.log n

/-- In the regular range the union of moved labels is small enough for the common-row bound. -/
theorem add_le_of_regularPairSizes {n : ℕ} (hn : 0 < n) {a : ℝ} {p : ℕ × ℕ}
    (hp : RegularPairSizes n a p) :
    (p.1 : ℝ) + p.2 ≤ 6 * (n : ℝ) ^ (1 - a) * Real.log n := by
  obtain ⟨_, h₁, h₂, hprod⟩ := hp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn' _
  have hleft : (p.1 : ℝ) ≤ (3 * n * Real.log n) / (n : ℝ) ^ a :=
    (le_div_iff₀ ha).2 ((mul_le_mul_of_nonneg_left h₂.le (by positivity)).trans hprod)
  have hright : (p.2 : ℝ) ≤ (3 * n * Real.log n) / (n : ℝ) ^ a := by
    apply (le_div_iff₀ ha).2
    rw [mul_comm (p.2 : ℝ)]
    exact (mul_le_mul_of_nonneg_right h₁.le (by positivity)).trans hprod
  calc
    _ ≤ 2 * ((3 * n * Real.log n) / (n : ℝ) ^ a) := by linarith only [hleft, hright]
    _ = _ := by rw [Real.rpow_sub hn', Real.rpow_one]; ring

/-- All size pairs outside the regular range have a linear-in-a bound, plus quadratic error. -/
theorem sum_twoStablePairSizeKernel_le_not_regular {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) {a : ℝ} (ha : 0 ≤ a)
    (he : ∀ p ∈ s, ¬RegularPairSizes n a p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤
      8 * (n : ℝ) ^ 2 * (2 + a * Real.log n) + 4 := by
  classical
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hB : ∀ t ⊆ s, (∀ p ∈ t, CentralPairSizes n p) →
      (∑ p ∈ t, twoStablePairSizeKernel n p) ≤
        8 * (n : ℝ) ^ 2 * (1 + a * Real.log n) + 4 := by
    intro t ht hc
    let P (p : ℕ × ℕ) : Prop := (p.1 : ℝ) ≤ (n : ℝ) ^ a ∨ (p.2 : ℝ) ≤ (n : ℝ) ^ a
    let Q (p : ℕ × ℕ) : Prop := 3 * Real.log n ≤ (p.1 : ℝ) * p.2 / n
    have hcov (p) (hp : p ∈ t) : P p ∨ Q p := by
      by_cases hP : P p
      · exact Or.inl hP
      · right
        by_contra hQ
        exact he p (ht hp) ⟨hc p hp,
          lt_of_not_ge (fun h ↦ hP (Or.inl h)), lt_of_not_ge (fun h ↦ hP (Or.inr h)), by
            calc
              _ ≤ (3 * Real.log n) * n :=
                (div_le_iff₀ hn').1 (le_of_lt (lt_of_not_ge hQ))
              _ = _ := by ring⟩
    calc
      _ ≤ (∑ p ∈ t.filter P, twoStablePairSizeKernel n p) +
          ∑ p ∈ t.filter Q, twoStablePairSizeKernel n p :=
        sum_le_filtered_cover t _ P Q (fun p _ ↦ twoStablePairSizeKernel_nonneg n p) hcov
      _ ≤ _ := add_le_add
        (sum_twoStablePairSizeKernel_le_central_small_power hn _
          (fun p hp ↦ hs p (ht (mem_filter.mp hp).1))
          (fun p hp ↦ hc p (mem_filter.mp hp).1) ha (fun _ hp ↦ (mem_filter.mp hp).2))
        (sum_twoStablePairSizeKernel_le_central_log_product hn _
          (fun p hp ↦ hs p (ht (mem_filter.mp hp).1))
          (fun p hp ↦ hc p (mem_filter.mp hp).1) (fun _ hp ↦ (mem_filter.mp hp).2))
  calc
    _ ≤ (8 * (n : ℝ) ^ 2 * (1 + a * Real.log n) + 4) + 8 * (n : ℝ) ^ 2 :=
      sum_twoStablePairSizeKernel_le_of_central_bound hn s hs _ hB
    _ = _ := by ring

/-- Transfer any of the kernel-sum bounds to a per-size probability or count bound
with the common prefactor from the two-matching estimate. -/
theorem sum_twoStablePairSizeWeights_le {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hw : ∀ p ∈ s, w p ≤ C * (1 + Real.log n) * twoStablePairSizeKernel n p)
    (hB : (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ B) :
    (∑ p ∈ s, w p) ≤ C * (1 + Real.log n) * B := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  calc
    _ ≤ ∑ p ∈ s, (C * (1 + Real.log n)) * twoStablePairSizeKernel n p := sum_le_sum hw
    _ = (C * (1 + Real.log n)) * ∑ p ∈ s, twoStablePairSizeKernel n p := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

end LennonPittelFormalization

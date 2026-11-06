module

public import LennonPittel.CoexposureGaussianSum

/-!
# Weighted support sums with a chosen vertex

Choosing one vertex of a support and then removing it isolates the extra
weight of that vertex. In a singleton-cycle bound this is what turns the
mass of the cycle's support into a sum of squared vertex weights.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace LennonPittelFormalization

/-- Erasing a prescribed member bijects supports containing it with smaller
supports that avoid it. The two weights of the chosen member factor out. -/
private theorem sum_supports_containing_eq {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∈ s) (k : ℕ) (p r : ι → ℝ) :
    (∑ S ∈ (s.powersetCard (k + 1)).filter (fun S ↦ i ∈ S),
      (∏ j ∈ S, p j) * r i) =
      ∑ T ∈ (s.erase i).powersetCard k, (p i * r i) * ∏ j ∈ T, p j := by
  refine sum_bij' (fun S _ ↦ S.erase i) (fun T _ ↦ insert i T) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rcases mem_filter.mp hS with ⟨hS, hiS⟩
    rcases mem_powersetCard.mp hS with ⟨hsub, hcard⟩
    exact mem_powersetCard.mpr
      ⟨fun j hj ↦ mem_erase.mpr ⟨(mem_erase.mp hj).1, hsub (mem_erase.mp hj).2⟩,
        by rw [card_erase_of_mem hiS, hcard, Nat.add_sub_cancel]⟩
  · intro T hT
    rcases mem_powersetCard.mp hT with ⟨hsub, hcard⟩
    have hiT : i ∉ T := fun h ↦ notMem_erase i s (hsub h)
    exact mem_filter.mpr
      ⟨mem_powersetCard.mpr
        ⟨insert_subset hi fun _ hj ↦ mem_of_mem_erase (hsub hj),
          by rw [card_insert_of_notMem hiT, hcard]⟩,
        mem_insert_self i T⟩
  · exact fun _ hS ↦ insert_erase (mem_filter.mp hS).2
  · exact fun _ hT ↦ erase_insert (fun h ↦ notMem_erase i s ((mem_powersetCard.mp hT).1 h))
  · intro S hS
    rw [← prod_erase_mul S p (mem_filter.mp hS).2]
    ring

/-- A support weighted by the sum of its vertex weights can be counted by
choosing the distinguished vertex first. The vertex weights in the sum
need not be the weights in the product. -/
theorem sum_powersetCard_prod_mul_sum_eq_pointed {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (k : ℕ) (p r : ι → ℝ) :
    (∑ S ∈ s.powersetCard (k + 1), (∏ j ∈ S, p j) * (∑ i ∈ S, r i)) =
      ∑ i ∈ s, (p i * r i) * coexposureEsymm (s.erase i) k p := by
  simp_rw [mul_sum]
  calc
    _ = ∑ i ∈ s, ∑ S ∈ (s.powersetCard (k + 1)).filter (fun S ↦ i ∈ S),
        (∏ j ∈ S, p j) * r i :=
      sum_comm' fun S i ↦
        ⟨fun h ↦ ⟨mem_filter.mpr h, (mem_powersetCard.mp h.1).1 h.2⟩,
          fun h ↦ mem_filter.mp h.1⟩
    _ = _ := by
      refine sum_congr rfl fun i hi ↦ ?_
      rw [sum_supports_containing_eq hi k p r, coexposureEsymm, mul_sum]

private theorem coexposureEsymm_erase_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (k : ℕ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    coexposureEsymm (s.erase i) k p ≤ coexposureEsymm s k p :=
  sum_le_sum_of_subset_of_nonneg (powersetCard_mono (erase_subset _ _))
    (fun _ _ _ ↦ prod_nonneg fun i _ ↦ hp i)

private theorem factorial_mul_esymm_le_descFactorial {n : ℕ} (hn : 0 < n) (k : ℕ)
    {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    (k.factorial : ℝ) * coexposureEsymm univ k p ≤
      (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  calc
    _ ≤ (k.factorial : ℝ) * ((n.choose k : ℝ) * (1 / (n : ℝ)) ^ k) :=
      mul_le_mul_of_nonneg_left (coexposureEsymm_le_uniform hn k hp hp1) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, one_div_pow, ← mul_assoc,
        mul_one_div]

/-- Summing the singleton forest bound over supports of size `k` gives
a falling-factorial bound with a square-weight correction. -/
theorem weightedSupportLengthSum_le {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (_hkn : k ≤ n)
    {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ((k - 1).factorial : ℝ) *
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard k, (∏ i ∈ S, p i) * (τ + ∑ i ∈ S, p i)) ≤
      (τ / (k : ℝ)) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) +
        (∑ i, p i ^ 2) * ((n.descFactorial (k - 1) : ℝ) / (n : ℝ) ^ (k - 1)) := by
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk0).ne'
  have hkfac : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred hk0.ne'
  have hpoint := sum_powersetCard_prod_mul_sum_eq_pointed univ (k - 1) p p
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hpoint
  simp_rw [← pow_two] at hpoint
  have hsplit :
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard k, (∏ i ∈ S, p i) * (τ + ∑ i ∈ S, p i)) =
        τ * coexposureEsymm univ k p + ∑ i, p i ^ 2 * coexposureEsymm (univ.erase i) (k - 1) p := by
    simp_rw [mul_add]
    rw [sum_add_distrib, hpoint, coexposureEsymm, ← sum_mul, mul_comm _ τ]
  rw [hsplit, mul_add]
  refine add_le_add ?_ ?_
  · calc
      _ = (τ / (k : ℝ)) * ((k.factorial : ℝ) * coexposureEsymm univ k p) := by
        rw [← hkfac]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_mul_esymm_le_descFactorial hn k hp hp1)
        (div_nonneg hτ (Nat.cast_nonneg _))
  · calc
      _ ≤ ((k - 1).factorial : ℝ) *
          ∑ i, p i ^ 2 * coexposureEsymm univ (k - 1) p :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
            (coexposureEsymm_erase_le univ i (k - 1) hp) (sq_nonneg _)) (Nat.cast_nonneg _)
      _ = (∑ i, p i ^ 2) * (((k - 1).factorial : ℝ) * coexposureEsymm univ (k - 1) p) := by
        rw [← sum_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (factorial_mul_esymm_le_descFactorial hn (k - 1) hp hp1)
        (sum_nonneg fun i _ ↦ sq_nonneg _)

end LennonPittelFormalization

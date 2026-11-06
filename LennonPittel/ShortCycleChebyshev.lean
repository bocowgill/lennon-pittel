module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Data.Fintype.Perm
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A finite Chebyshev bound for short permutation cycles

The cycle-counting arguments supply a first moment and an ordered-pair
moment. This file turns those inputs into a uniform tail estimate.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The harmonic sum over allowed nontrivial cycle lengths is at most `log L`. -/
theorem shortCycleHarmonic_le_log (k L : ℕ) (hL : 2 ≤ L) :
    (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ≤ Real.log (L : ℝ) := by
  have h₁ : 1 ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Finset.Icc 1 L).erase 1 = Finset.Icc 2 L := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hh := harmonic_le_one_add_log L
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  rw [← Finset.sum_erase_add (Finset.Icc 1 L) (fun j ↦ (j : ℝ)⁻¹) h₁, he,
    Nat.cast_one, inv_one] at hh
  calc
    _ ≤ ∑ j ∈ Finset.Icc 2 L, (1 : ℝ) / j :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj ↦ Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
          (Finset.mem_Icc.mp hj).2.trans (min_le_left _ _)⟩)
        (fun j _ _ ↦ by positivity)
    _ ≤ _ := by
      simp only [one_div]
      linarith only [hh]

open scoped Classical in
/-- Chebyshev's bound for a finite uniform count with an ordered-pair moment bound. -/
theorem finiteCountChebyshev {α : Type*} [Fintype α] [Nonempty α] (C : α → ℕ)
    {H B : ℝ} (hB : 0 < B) (hH : H ≤ B)
    (hmean : (∑ i, (C i : ℝ)) = (Fintype.card α : ℝ) * H)
    (hpair : (∑ i, (C i : ℝ) * ((C i : ℝ) - 1)) ≤ (Fintype.card α : ℝ) * H ^ 2) :
    ((Finset.univ.filter (fun i ↦ (3 / 2 : ℝ) * B < (C i : ℝ))).card : ℝ) /
      (Fintype.card α : ℝ) ≤ 4 / B := by
  let S := Finset.univ.filter (fun i ↦ (3 / 2 : ℝ) * B < (C i : ℝ))
  have hs : (∑ i, ((C i : ℝ) - H) ^ 2) ≤ (Fintype.card α : ℝ) * H := by
    calc
      _ = ∑ i, ((C i : ℝ) * ((C i : ℝ) - 1) + (C i : ℝ) -
          2 * H * (C i : ℝ) + H ^ 2) := Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (∑ i, (C i : ℝ) * ((C i : ℝ) - 1)) + (∑ i, (C i : ℝ)) -
          2 * H * (∑ i, (C i : ℝ)) + (Fintype.card α : ℝ) * H ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
        rw [hmean]
        nlinarith only [hpair]
  have htail : (S.card : ℝ) * (B / 2) ^ 2 ≤ (Fintype.card α : ℝ) * B := by
    calc
      _ = ∑ i ∈ S, (B / 2) ^ 2 := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, ((C i : ℝ) - H) ^ 2 := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hci : (3 / 2 : ℝ) * B < (C i : ℝ) := (Finset.mem_filter.mp hi).2
        exact pow_le_pow_left₀ (by positivity) (by linarith only [hci, hH]) 2
      _ ≤ ∑ i, ((C i : ℝ) - H) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ sq_nonneg _
      _ ≤ (Fintype.card α : ℝ) * H := hs
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  change (S.card : ℝ) / (Fintype.card α : ℝ) ≤ 4 / B
  apply (div_le_div_iff₀ hc hB).mpr
  calc
    _ = (S.card * (B / 2) ^ 2) * (4 / B) := by field_simp; ring
    _ ≤ ((Fintype.card α : ℝ) * B) * (4 / B) :=
      mul_le_mul_of_nonneg_right htail (by positivity)
    _ = _ := by field_simp

open scoped Classical in
/-- Uniform mass of counts above the short-cycle cap, given the harmonic moments. -/
theorem shortCycleChebyshev_ennreal {k L : ℕ} (hL : 2 ≤ L) (C : Equiv.Perm (Fin k) → ℕ)
    (hmean : (∑ σ, (C σ : ℝ)) =
      (k.factorial : ℝ) * (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j))
    (hpair : (∑ σ, (C σ : ℝ) * ((C σ : ℝ) - 1)) ≤
      (k.factorial : ℝ) * (∑ j ∈ Finset.Icc 2 (min L k), (1 : ℝ) / j) ^ 2) :
    ((Finset.univ.filter (fun σ ↦ (3 / 2 : ℝ) * Real.log (L : ℝ) < (C σ : ℝ))).card :
      ℝ≥0∞) / (k.factorial : ℝ≥0∞) ≤ ENNReal.ofReal (4 / Real.log (L : ℝ)) := by
  have hB : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hc : Fintype.card (Equiv.Perm (Fin k)) = k.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have h := finiteCountChebyshev C hB (shortCycleHarmonic_le_log k L hL)
    (by simpa only [hc] using hmean) (by simpa only [hc] using hpair)
  rw [hc] at h
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  simpa only [ENNReal.ofReal_div_of_pos hf, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h

end LennonPittelFormalization

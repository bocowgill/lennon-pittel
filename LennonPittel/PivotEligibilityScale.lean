module

public import LennonPittel.PivotReverseMaskLowerMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Square-root budgets for the eligible reverse moment

The three label losses are controlled by a sufficiently small square-root support cutoff.
The lower arc perturbation is negligible even after multiplying by the full support size.
-/

@[expose] public section

open Filter Real
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- At square-root support size, pair collisions are quadratic in the cutoff coefficient,
and the losses from the pivot and forbidden cells are linear. -/
theorem reverseGoodLabelLoss_le_of_squareRoot {n k : ℕ} {a C B E : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hk : (k : ℝ) ≤ a * Real.sqrt (n : ℝ)) (r : Fin n → ℝ≥0∞)
    (A : Finset (Fin n)) (η : ℝ≥0∞)
    (hsq : ∑ i, (r i) ^ 2 ≤ ENNReal.ofReal (C / n))
    (hsupport : ∑ i ∈ A, r i ≤ ENNReal.ofReal (B / Real.sqrt n))
    (hforbid : η ≤ ENNReal.ofReal (E / Real.sqrt n)) :
    reverseGoodLabelLoss k r A η ≤ ENNReal.ofReal (C * a ^ 2 / 2 + (B + E) * a) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hk2 : (k : ℝ) ^ 2 ≤ a ^ 2 * n := by
    simpa only [mul_pow, Real.sq_sqrt hnR.le] using pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  have hterm₁ : (k.choose 2 : ℝ) * (C / n) ≤ C * a ^ 2 / 2 := calc
    _ ≤ (a ^ 2 * n / 2) * (C / n) :=
      mul_le_mul_of_nonneg_right (hc.trans (div_le_div_of_nonneg_right hk2 (by norm_num)))
        (div_nonneg hC hnR.le)
    _ = _ := by field_simp
  have hterm₂ {v : ℝ} (hv : 0 ≤ v) : (k : ℝ) * (v / Real.sqrt n) ≤ v * a := calc
    _ ≤ (a * Real.sqrt n) * (v / Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hk (div_nonneg hv hs.le)
    _ = _ := by field_simp
  calc
    reverseGoodLabelLoss k r A η ≤
        (k.choose 2 : ℝ≥0∞) * ENNReal.ofReal (C / n) +
          (k : ℝ≥0∞) * ENNReal.ofReal (B / Real.sqrt n) +
          (k : ℝ≥0∞) * ENNReal.ofReal (E / Real.sqrt n) :=
      add_le_add (add_le_add (mul_le_mul_right hsq _) (mul_le_mul_right hsupport _))
        (mul_le_mul_right hforbid _)
    _ ≤ _ := by
      simp only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hterm₁, hterm₂ hB, hterm₂ hE,
        show (B + E) * a = B * a + E * a by ring])

/-- The label losses can be kept below one quarter with a positive cutoff coefficient
strictly below any prescribed positive pivot-length coefficient. -/
theorem exists_squareRootLabelBudget {b C B E : ℝ} (hb : 0 < b)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ C * a ^ 2 / 2 + (B + E) * a ≤ 1 / 4 := by
  let S := C + B + E + 1
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hS₀ : 0 < S := zero_lt_one.trans_le hS
  let a := min (b / 2) (1 / (4 * S))
  have ha₀ : 0 < a := lt_min (by positivity) (by positivity)
  have ha₁ : a ≤ 1 := (min_le_right ..).trans (by
    apply (div_le_iff₀ (by positivity : 0 < 4 * S)).2
    linarith)
  have ha₂ : a * S ≤ 1 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * S)).1 (min_le_right (b / 2) (1 / (4 * S)))
    linarith only [h, show a * (4 * S) = 4 * (a * S) by ring]
  have ha_sq : a ^ 2 ≤ a := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left ha₁ ha₀.le
  refine ⟨a, ha₀, (min_le_left ..).trans_lt (by linarith), ?_⟩
  have hCa := mul_le_mul_of_nonneg_left ha_sq hC
  dsimp only [S] at ha₂
  nlinarith only [hCa, ha₂, mul_nonneg hC ha₀.le, ha₀.le]

private theorem tendsto_reverseLowerArcEnvelope (a c C : ℝ) :
    Tendsto (fun n : ℕ ↦ (a + 1) * (14 * C * (Real.log n / Real.sqrt n) +
      (4 / c) * (n : ℝ) ^ (-(1 / 10) : ℝ))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hp := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)
  have h := ((hlog.const_mul (14 * C)).add (hp.const_mul (4 / c))).const_mul (a + 1)
  simpa only [Function.comp_def, mul_zero, add_zero] using
    h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

/-- The lower arc error is eventually small uniformly over all admissible score
vectors and support cutoffs. -/
theorem eventually_reverseArcLowerBudget_uniform {a c C : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (X m : ℝ),
      c * (n : ℝ) ^ (3 / 5 : ℝ) ≤ X → 0 ≤ m → m / X ≤ C * Real.log n / n →
      (K : ℝ) ≤ a * Real.sqrt n →
      let δ := 14 * m / X + Real.exp (-X / 4)
      0 ≤ δ ∧ δ ≤ 1 ∧ (K : ℝ) * δ ≤ 1 / 4 := by
  have hlim := (tendsto_order.1 (tendsto_reverseLowerArcEnvelope a c C)).2 (1 / 4) (by norm_num)
  filter_upwards [hlim, eventually_ge_atTop (1 : ℕ)] with n hnlim hn K X m hX hm hrat hK
  dsimp only at hnlim ⊢
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hnR
  have hp : 0 < (n : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hn₀ _
  have hX₀ : 0 < X := (mul_pos hc hp).trans_le hX
  let δ := 14 * m / X + Real.exp (-X / 4)
  have hδ₀ : 0 ≤ δ := by positivity
  have hexp : Real.exp (-X / 4) ≤ 4 / X := by
    rw [neg_div, Real.exp_neg]
    calc
      _ ≤ (X / 4)⁻¹ := inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (X / 4)])
      _ = _ := inv_div _ _
  have hδ : δ ≤ 14 * C * Real.log n / n + 4 / (c * (n : ℝ) ^ (3 / 5 : ℝ)) := by
    simpa only [δ, mul_div_assoc, mul_assoc] using
      add_le_add (mul_le_mul_of_nonneg_left hrat (by norm_num : (0 : ℝ) ≤ 14))
      (hexp.trans (div_le_div_of_nonneg_left (by norm_num) (mul_pos hc hp) hX))
  have hlog : Real.sqrt (n : ℝ) * (14 * C * Real.log n / n) =
      14 * C * (Real.log n / Real.sqrt n) := by
    have hfrac : Real.sqrt (n : ℝ) / (n : ℝ) = 1 / Real.sqrt n :=
      (div_eq_div_iff hn₀.ne' (Real.sqrt_pos.2 hn₀).ne').2
        (by simpa only [one_mul, pow_two] using Real.sq_sqrt hn₀.le)
    calc
      _ = (14 * C * Real.log n) * (Real.sqrt (n : ℝ) / n) := by ring
      _ = _ := by rw [hfrac]; ring
  have he : Real.sqrt (n : ℝ) * (4 / (c * (n : ℝ) ^ (3 / 5 : ℝ))) =
      (4 / c) * (n : ℝ) ^ (-(1 / 10) : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (-(1 / 10) : ℝ) = 1 / 2 - 3 / 5 by norm_num,
      Real.rpow_sub hn₀]
    ring
  have hscaled : Real.sqrt (n : ℝ) * δ ≤
      14 * C * (Real.log n / Real.sqrt n) + (4 / c) * (n : ℝ) ^ (-(1 / 10) : ℝ) := by
    simpa only [mul_add, hlog, he] using
      mul_le_mul_of_nonneg_left hδ (Real.sqrt_nonneg (n : ℝ))
  have hlarge : (a + 1) * (Real.sqrt (n : ℝ) * δ) ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hscaled (by positivity)).trans hnlim.le
  refine ⟨hδ₀, ?_, ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_right hs hδ₀
    have h₂ := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ a + 1)
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδ₀)
    linarith only [h₁, h₂, hlarge]
  · calc
      (K : ℝ) * δ ≤ (a * Real.sqrt (n : ℝ)) * δ := mul_le_mul_of_nonneg_right hK hδ₀
      _ ≤ (a + 1) * (Real.sqrt (n : ℝ) * δ) := by
        rw [mul_assoc]
        gcongr
        linarith
      _ ≤ _ := hlarge

end LennonPittelFormalization

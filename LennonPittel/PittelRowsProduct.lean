module

public import LennonPittel.PittelRowApprox
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# Multiplying the row approximations in Pittel's first-moment estimate

The first-order contributions to the log of the product are the coordinate weights and
the negative sum of their squares, once per row.
-/

@[expose] public section

open Filter Finset
open scoped BigOperators Topology

namespace LennonPittelFormalization

private theorem abs_log_sub_sub_one_le {q : ℝ} (h : |q - 1| ≤ 1 / 2) :
    |Real.log q - (q - 1)| ≤ 2 * |q - 1| ^ 2 := by
  have hx : |1 - q| = |q - 1| := abs_sub_comm _ _
  have hx' : |1 - q| < 1 := by rw [hx]; linarith
  have hTaylor := Real.abs_log_sub_add_sum_range_le hx' 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
    show (1 : ℝ) - (1 - q) = q by ring, hx] at hTaylor
  calc
    |Real.log q - (q - 1)| = |1 - q + Real.log q| := by congr 1; ring
    _ ≤ |q - 1| ^ 2 / (1 - |q - 1|) := hTaylor
    _ ≤ 2 * |q - 1| ^ 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - |q - 1|)).2
      nlinarith [mul_nonneg (sq_nonneg |q - 1|) (show 0 ≤ 1 - 2 * |q - 1| by linarith)]

private theorem pittel_model_error {w T m : ℝ} (hw : 0 ≤ w) (hwm : w ≤ m)
    (hm : m ≤ 1 / 2) (hT : 0 ≤ T) (hTm : T ≤ m) :
    |1 / (1 - w) - (T - w ^ 2) / (1 - w) ^ 3 - (1 + w - T)| ≤
      34 * m * w := by
  have ha : 0 < 1 - w := by linarith
  have ha2 : 1 / 2 ≤ 1 - w := by linarith
  have ha3 : 1 / 8 ≤ (1 - w) ^ 3 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ha2 3 using 1
    norm_num
  have hb3 : (1 - w) ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ ha.le (show 1 - w ≤ 1 by linarith) 3
  have hnum : 1 - (1 - w) ^ 3 ≤ 3 * w := by
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 3 - w by linarith)]
  have hA : w ^ 2 / (1 - w) ≤ 2 * w ^ 2 := by
    apply (div_le_iff₀ ha).2
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 1 - 2 * w by linarith)]
  have hB : w ^ 2 / (1 - w) ^ 3 ≤ 8 * w ^ 2 := by
    apply (div_le_iff₀ (pow_pos ha _)).2
    nlinarith [mul_nonneg (sq_nonneg w) (show 0 ≤ 8 * (1 - w) ^ 3 - 1 by linarith)]
  have hC : T * (1 - (1 - w) ^ 3) / (1 - w) ^ 3 ≤ 24 * T * w := by
    apply (div_le_iff₀ (pow_pos ha _)).2
    calc
      T * (1 - (1 - w) ^ 3) ≤ T * (3 * w) := mul_le_mul_of_nonneg_left hnum hT
      _ = 24 * T * w * (1 / 8) := by ring
      _ ≤ 24 * T * w * (1 - w) ^ 3 := mul_le_mul_of_nonneg_left ha3 (by positivity)
  have heq :
      1 / (1 - w) - (T - w ^ 2) / (1 - w) ^ 3 - (1 + w - T) =
        w ^ 2 / (1 - w) + w ^ 2 / (1 - w) ^ 3 -
          T * (1 - (1 - w) ^ 3) / (1 - w) ^ 3 := by
    field_simp
    ring
  rw [heq]
  apply abs_le.2
  have hD : T * (1 - (1 - w) ^ 3) / (1 - w) ^ 3 ≥ 0 := by
    exact div_nonneg (mul_nonneg hT (sub_nonneg.mpr hb3)) (pow_nonneg ha.le _)
  have hE := mul_le_mul_of_nonneg_right hwm hw
  have hF := mul_le_mul_of_nonneg_right hTm hw
  constructor <;> linarith [div_nonneg (sq_nonneg w) ha.le,
    div_nonneg (sq_nonneg w) (pow_nonneg ha.le 3)]

/-- Quantitative error for the log of a product of rows approximated to second order. -/
theorem abs_log_prod_pittelRows_le {n : ℕ} {w q : Fin n → ℝ} {m e : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hwm : ∀ i, w i ≤ m)
    (hm : 0 ≤ m) (hm' : m ≤ 1 / 2) (he : 0 ≤ e) :
    let T := ∑ i, w i ^ 2
    let d := 2 * m + 34 * m ^ 2 + e
    let E := 34 * m + (n : ℝ) * e
    d ≤ 1 / 2 →
    (∀ i, |q i - (1 / (1 - w i) - (T - w i ^ 2) / (1 - w i) ^ 3)| ≤ e) →
    (∀ i, 0 < q i) ∧
      |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| ≤ E + 2 * d * (1 + n * T + E) := by
  classical
  dsimp only
  let T := ∑ i, w i ^ 2
  let d := 2 * m + 34 * m ^ 2 + e
  let E := 34 * m + (n : ℝ) * e
  change d ≤ 1 / 2 → _ → (∀ i, 0 < q i) ∧
    |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| ≤ E + 2 * d * (1 + n * T + E)
  intro hd hrow
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ ↦ sq_nonneg (w i)
  have hTm : T ≤ m := calc
    T ≤ ∑ i, m * w i := Finset.sum_le_sum fun i _ ↦ by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hwm i) (hw i)
    _ = m := by rw [← Finset.mul_sum, hsum, mul_one]
  have hclose (i) : |q i - (1 + w i - T)| ≤ 34 * m * w i + e := calc
    _ ≤ |q i - (1 / (1 - w i) - (T - w i ^ 2) / (1 - w i) ^ 3)| +
        |1 / (1 - w i) - (T - w i ^ 2) / (1 - w i) ^ 3 - (1 + w i - T)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      linarith [hrow i, pittel_model_error (hw i) (hwm i) hm' hT hTm]
  have hu (i) : |q i - 1| ≤ w i + T + (34 * m * w i + e) := calc
    _ ≤ |q i - (1 + w i - T)| + |(1 + w i - T) - 1| := abs_sub_le _ _ _
    _ ≤ _ := by
      have ha : |(1 + w i - T) - 1| ≤ w i + T := by
        apply abs_le.2
        constructor <;> linarith [hw i]
      linarith [hclose i]
  have hud (i) : |q i - 1| ≤ d := by
    have hmul := mul_le_mul_of_nonneg_left (hwm i) (show 0 ≤ 34 * m by positivity)
    dsimp [d]
    nlinarith [hu i, hTm, hwm i]
  have hq (i) : 0 < q i := by
    linarith [(abs_le.1 ((hud i).trans hd)).1]
  refine ⟨hq, ?_⟩
  have hsum_close : ∑ i, |q i - (1 + w i - T)| ≤ E := calc
    _ ≤ ∑ i, (34 * m * w i + e) := Finset.sum_le_sum fun i _ ↦ hclose i
    _ = E := by simp [E, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, nsmul_eq_mul]
  have hsum_u : ∑ i, |q i - 1| ≤ 1 + n * T + E := calc
    _ ≤ ∑ i, (w i + T + (34 * m * w i + e)) := Finset.sum_le_sum fun i _ ↦ hu i
    _ = _ := by simp [E, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, nsmul_eq_mul]
  have hsum_log : ∑ i, |Real.log (q i) - (q i - 1)| ≤ 2 * d * (1 + n * T + E) := calc
    _ ≤ ∑ i, (2 * d) * |q i - 1| := by
      apply Finset.sum_le_sum
      intro i _
      refine (abs_log_sub_sub_one_le ((hud i).trans hd)).trans ?_
      have hh := mul_le_mul_of_nonneg_right (hud i) (abs_nonneg (q i - 1))
      nlinarith
    _ = 2 * d * ∑ i, |q i - 1| := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum_u (by dsimp [d]; positivity)
  rw [Real.log_prod (fun i _ ↦ (hq i).ne')]
  have hsum_target : ∑ i, (w i - T) = 1 - (n : ℝ) * T := by
    simp [Finset.sum_sub_distrib, hsum, nsmul_eq_mul]
  rw [← hsum_target, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Real.log (q i) - (w i - T)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|Real.log (q i) - (q i - 1)| + |q i - (1 + w i - T)|) := by
      apply Finset.sum_le_sum
      intro i _
      have h : q i - 1 - (w i - T) = q i - (1 + w i - T) := by ring
      simpa only [h] using abs_sub_le (Real.log (q i)) (q i - 1) (w i - T)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      linarith

/-- Uniform convergence of the row product on a neighborhood of the typical simplex weights. -/
theorem eventually_pittelRowsProduct_close_of_error {m e : ℕ → ℝ}
    (hm0 : Tendsto m atTop (𝓝 0)) (he0 : Tendsto e atTop (𝓝 0))
    (hne0 : Tendsto (fun n : ℕ ↦ (n : ℝ) * e n) atTop (𝓝 0))
    (hmn : ∀ᶠ n in atTop, 0 ≤ m n) (hen : ∀ᶠ n in atTop, 0 ≤ e n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ᶠ n in atTop, ∀ w q : Fin n → ℝ,
      (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, w i ≤ m n) →
      |(n : ℝ) * (∑ i, w i ^ 2) - 2| ≤ η →
      (∀ i, |q i - (1 / (1 - w i) - ((∑ j, w j ^ 2) - w i ^ 2) / (1 - w i) ^ 3)|
        ≤ e n) →
      |(∏ i, q i) - (Real.exp 1)⁻¹| ≤ ε := by
  let d (n : ℕ) := 2 * m n + 34 * m n ^ 2 + e n
  let E (n : ℕ) := 34 * m n + (n : ℝ) * e n
  have hd0 : Tendsto d atTop (𝓝 0) := by
    simpa [d] using ((hm0.const_mul 2).add ((hm0.pow 2).const_mul 34)).add he0
  have hE0 : Tendsto E atTop (𝓝 0) := by
    simpa [E] using (hm0.const_mul 34).add hne0
  obtain ⟨δ, hδ, hδexp⟩ := Metric.continuousAt_iff.mp
    (Real.continuous_exp.continuousAt (x := (-1 : ℝ))) ε hε
  refine ⟨δ / 2, by positivity, ?_⟩
  have hB0 : Tendsto (fun n ↦ E n + 2 * d n * (1 + (2 + δ / 2) + E n))
      atTop (𝓝 0) := by
    simpa using hE0.add ((hd0.const_mul 2).mul (hE0.const_add (1 + (2 + δ / 2))))
  filter_upwards [hmn, hen, (tendsto_order.mp hm0).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hd0).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hB0).2 (δ / 2) (by positivity)] with n hm he hml hdl hBl
  intro w q hw hsum hwm hnorm hrow
  let T := ∑ i, w i ^ 2
  change |(n : ℝ) * T - 2| ≤ δ / 2 at hnorm
  obtain ⟨hq, hlog⟩ := abs_log_prod_pittelRows_le hw hsum hwm hm hml.le he hdl.le hrow
  have hd : 0 ≤ d n := by dsimp [d]; positivity
  have hupper : (n : ℝ) * T ≤ 2 + δ / 2 := by linarith [(abs_le.1 hnorm).2]
  have hl : |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| < δ / 2 := calc
    _ ≤ E n + 2 * d n * (1 + (n : ℝ) * T + E n) := hlog
    _ ≤ E n + 2 * d n * (1 + (2 + δ / 2) + E n) := by gcongr
    _ < δ / 2 := hBl
  have htotal : |Real.log (∏ i, q i) - (-1)| < δ := calc
    _ ≤ |Real.log (∏ i, q i) - (1 - (n : ℝ) * T)| +
        |(1 - (n : ℝ) * T) - (-1)| := abs_sub_le _ _ _
    _ < δ := by
      rw [show (1 - (n : ℝ) * T) - (-1) = -((n : ℝ) * T - 2) by ring, abs_neg]
      linarith
  have hfinal := hδexp (x := Real.log (∏ i, q i)) (by simpa only [Real.dist_eq] using htotal)
  simpa only [Real.dist_eq, Real.exp_log (Finset.prod_pos fun i _ ↦ hq i), Real.exp_neg]
    using hfinal.le

private theorem pittel_row_error_rates :
    let m (n : ℕ) := 12 * Real.log n / n
    let L (n : ℕ) := 6 * Real.log n
    let e (n : ℕ) := 96 * (m n) ^ 2 + 2 * Real.exp (-(L n / 2))
    Tendsto m atTop (𝓝 0) ∧
      Tendsto (fun n ↦ L n * m n) atTop (𝓝 0) ∧
      Tendsto e atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) * e n) atTop (𝓝 0) := by
  let m (n : ℕ) := 12 * Real.log n / n
  let L (n : ℕ) := 6 * Real.log n
  let e (n : ℕ) := 96 * (m n) ^ 2 + 2 * Real.exp (-(L n / 2))
  change Tendsto m atTop (𝓝 0) ∧ Tendsto (fun n ↦ L n * m n) atTop (𝓝 0) ∧
    Tendsto e atTop (𝓝 0) ∧ Tendsto (fun n : ℕ ↦ (n : ℝ) * e n) atTop (𝓝 0)
  have hc : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hc
  have hlog2 : Tendsto (fun n : ℕ ↦ Real.log n ^ 2 / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)).tendsto_div_nhds_zero.comp hc
  have hm : Tendsto m atTop (𝓝 0) := by
    simpa only [m, mul_div_assoc, mul_zero] using hlog.const_mul 12
  have hLm : Tendsto (fun n ↦ L n * m n) atTop (𝓝 0) := by
    refine (show Tendsto (fun n : ℕ ↦ 72 * (Real.log n ^ 2 / n)) atTop (𝓝 0) by
      simpa only [mul_zero] using hlog2.const_mul 72).congr fun n ↦ ?_
    dsimp [L, m]
    ring
  have hnm2 : Tendsto (fun n : ℕ ↦ (n : ℝ) * (m n) ^ 2) atTop (𝓝 0) := by
    refine (show Tendsto (fun n : ℕ ↦ 144 * (Real.log n ^ 2 / n)) atTop (𝓝 0) by
      simpa only [mul_zero] using hlog2.const_mul 144).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp [m]
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
    ring
  have htail_eq {n : ℕ} (hn : 0 < n) :
      Real.exp (-(L n / 2)) = ((n : ℝ) ^ 3)⁻¹ := by
    rw [show -(L n / 2) = -((3 : ℕ) : ℝ) * Real.log n by dsimp [L]; norm_num; ring,
      neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.mpr hn)]
  have htail : Tendsto (fun n ↦ Real.exp (-(L n / 2))) atTop (𝓝 0) := by
    refine ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 3 ≠ 0))).comp
      hc).congr' ?_
    exact (eventually_gt_atTop 0).mono fun n hn ↦ (htail_eq hn).symm
  have hntail : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-(L n / 2))) atTop (𝓝 0) := by
    refine ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))).comp
      hc).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    change ((n : ℝ) ^ 2)⁻¹ = (n : ℝ) * Real.exp (-(L n / 2))
    rw [htail_eq hn]
    field_simp [hn'.ne']
  refine ⟨hm, hLm, ?_, ?_⟩
  · simpa only [e, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hm.pow 2).const_mul 96).add (htail.const_mul 2)
  · refine (show Tendsto
      (fun n : ℕ ↦ 96 * ((n : ℝ) * (m n) ^ 2) + 2 * ((n : ℝ) * Real.exp (-(L n / 2))))
      atTop (𝓝 0) by simpa only [mul_zero, add_zero] using
        (hnm2.const_mul 96).add (hntail.const_mul 2)).congr fun n ↦ ?_
    dsimp [e]
    ring

private theorem pittel_row_abs_of_bounds {q a b m L : ℝ} (ha : 1 / 2 ≤ a)
    (hb : 0 ≤ b) (hbm : b ≤ m) (hL : 0 ≤ L)
    (hu : q ≤ 1 / a - b / a ^ 3 + 3 * b ^ 2 / a ^ 5)
    (hl : 1 / a - b / a ^ 3 - 6 * m * b / a ^ 4 - Real.exp (-(a * L)) / a ≤ q) :
    |q - (1 / a - b / a ^ 3)| ≤ 96 * m ^ 2 + 2 * Real.exp (-(L / 2)) := by
  have ha' : 0 < a := by linarith
  have hm : 0 ≤ m := hb.trans hbm
  have ha4 : 1 / 16 ≤ a ^ 4 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ha 4 using 1
    norm_num
  have ha5 : 1 / 32 ≤ a ^ 5 := by
    convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) ha 5 using 1
    norm_num
  have hu' : 3 * b ^ 2 / a ^ 5 ≤ 96 * m ^ 2 := calc
    _ ≤ 3 * m ^ 2 / a ^ 5 := by gcongr
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos ha' _)).2
      nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ 32 * a ^ 5 - 1 by linarith)]
  have hl' : 6 * m * b / a ^ 4 ≤ 96 * m ^ 2 := calc
    _ ≤ 6 * m * m / a ^ 4 := by gcongr
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos ha' _)).2
      nlinarith [mul_nonneg (sq_nonneg m) (show 0 ≤ 16 * a ^ 4 - 1 by linarith)]
  have htail : Real.exp (-(a * L)) / a ≤ 2 * Real.exp (-(L / 2)) := by
    apply (div_le_iff₀ ha').2
    calc
      _ ≤ Real.exp (-(L / 2)) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right ha hL])
      _ = 2 * Real.exp (-(L / 2)) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)
  exact abs_le.2 ⟨by linarith, by linarith [Real.exp_pos (-(L / 2))]⟩

/-- Uniform first-moment row-product approximation for regular angular weights in the cube. -/
theorem eventually_pittelRowsProduct_close {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ᶠ n : ℕ in atTop, ∀ (w : Fin n → ℝ) (s : ℝ),
      6 * Real.log n ≤ s →
      (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, w i ≤ 12 * Real.log n / n) →
      |(n : ℝ) * (∑ i, w i ^ 2) - 2| ≤ η →
      (∀ i, s * w i ≤ 1) →
      |(∏ i, pittelRowIntegral (univ.erase i) w s) - (Real.exp 1)⁻¹| ≤ ε := by
  let m (n : ℕ) := 12 * Real.log n / n
  let L (n : ℕ) := 6 * Real.log n
  let e (n : ℕ) := 96 * (m n) ^ 2 + 2 * Real.exp (-(L n / 2))
  obtain ⟨hm0, hLm0, he0, hne0⟩ := pittel_row_error_rates
  have hLn : ∀ᶠ n : ℕ in atTop, 0 ≤ L n := (eventually_ge_atTop 1).mono fun n hn ↦ by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (by norm_num) (Real.log_nonneg hn')
  have hmn : ∀ᶠ n : ℕ in atTop, 0 ≤ m n := (eventually_ge_atTop 1).mono fun n hn ↦ by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [m]
    positivity [Real.log_nonneg hn']
  have hen : ∀ᶠ n : ℕ in atTop, 0 ≤ e n := .of_forall fun n ↦ by dsimp [e]; positivity
  obtain ⟨η, hη, hgood⟩ := eventually_pittelRowsProduct_close_of_error
    (m := m) (e := e) hm0 he0 hne0 hmn hen hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hgood, hLn, hmn, (tendsto_order.mp hm0).2 (1 / 2) (by norm_num),
    (tendsto_order.mp hLm0).2 (1 / 2) (by norm_num)] with n hg hL hm hm' hLm
  intro w s hLs hw hsum hwm hnorm hcap
  apply hg w _ hw hsum hwm hnorm
  intro i
  let I : Finset (Fin n) := univ.erase i
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, w j ^ 2
  have ha : a = 1 - w i := by
    dsimp only [a, I]
    rw [Finset.sum_erase_eq_sub (f := w) (mem_univ i), hsum]
  have hb : b = (∑ j, w j ^ 2) - w i ^ 2 :=
    Finset.sum_erase_eq_sub (f := fun j ↦ w j ^ 2) (mem_univ i)
  have hal : 1 / 2 ≤ a := by linarith [hwm i]
  have hap : 0 < a := by linarith
  have hbn : 0 ≤ b := Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j)
  have hbm : b ≤ m n := calc
    b ≤ ∑ j ∈ I, m n * w j := Finset.sum_le_sum fun j _ ↦ by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hwm j) (hw j)
    _ = m n * a := by rw [Finset.mul_sum]
    _ ≤ m n := by rw [ha]; nlinarith [mul_nonneg hm (hw i)]
  have hsmall (j : Fin n) : L n * w j ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hwm j) hL).trans hLm.le
  have hu := pittelRowIntegral_le I w (hL.trans hLs) (fun j _ ↦ hw j)
    (fun j _ ↦ hcap j) hap
  have hl := le_pittelRowIntegral I w hL hLs (fun j _ ↦ hw j)
    (fun j _ ↦ hcap j) (fun j _ ↦ hwm j) (fun j _ ↦ hsmall j) hap
  rw [← ha, ← hb]
  exact pittel_row_abs_of_bounds hal hbn hbm hL hu hl

end LennonPittelFormalization

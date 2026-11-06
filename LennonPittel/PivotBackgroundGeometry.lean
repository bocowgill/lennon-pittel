module

public import LennonPittel.CommonForwardCycleMoments
public import LennonPittel.PivotResidualImageGeometry
public import LennonPittel.PivotShortCycleScale
public import LennonPittel.TwoStablePairSizeSums

/-!
# Numerical error budgets for the common-row short-cycle bound

The cutoff is a small power of the size. This leaves both the accumulated
arc error and the chance of repeated or non-common labels negligible.
-/

@[expose] public section

open Filter Set StableMarriage
open scoped Topology BigOperators

namespace LennonPittelFormalization

/-- A bound for the male score at a regular endpoint. -/
noncomputable def backgroundMaleCeiling (n : ℕ) : ℝ :=
  16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)

/-- A bound for the normalized label weight at a regular endpoint. -/
noncomputable def backgroundWeightCeiling (n : ℕ) : ℝ :=
  2060 * Real.log n / n

private theorem tendsto_log_div_nat_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ) ^ s) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem rpow_mul_div_rpow {x : ℝ} (hx : 0 < x) (a s t : ℝ) :
    x ^ s * (a / x ^ t) = a / x ^ (t - s) := by
  rw [Real.rpow_sub hx]
  field_simp

private theorem background_arcEnvelope_tendsto {α : ℝ} (hα : α < 1 / 10) :
    Tendsto (fun n : ℕ ↦
      32 * (Real.log n / (n : ℝ) ^ (1 / 10 - α / 4)) +
        8240 * (Real.log n / (n : ℝ) ^ (1 - α / 4)) +
        2 * (n : ℝ) ^ (-(1 / 10 - α / 4))) atTop (𝓝 0) := by
  have h1 : 0 < (1 / 10 : ℝ) - α / 4 := by linarith
  have h2 : 0 < (1 : ℝ) - α / 4 := by linarith
  have hp := (tendsto_rpow_neg_atTop h1).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [mul_zero, add_zero, Function.comp_def] using
    ((((tendsto_log_div_nat_rpow h1).const_mul 32).add
      ((tendsto_log_div_nat_rpow h2).const_mul 8240)).add (hp.const_mul 2))

/-- The exact uniform relative arc error is eventually small after multiplying
by the maximum cycle length, uniformly in the endpoint's female score total. -/
theorem eventually_backgroundArcError_small {α : ℝ} (hα : 0 < α) (hα' : α < 1 / 10) :
    ∀ᶠ n : ℕ in atTop,
      backgroundMaleCeiling n + 2 * backgroundWeightCeiling n ≤ 1 / 2 ∧
      ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
        let δ := 2 * backgroundMaleCeiling n + 4 * backgroundWeightCeiling n + Real.exp (-Y / 2)
        δ ∈ Icc 0 1 ∧ (pivotShortCycleCutoff α n : ℝ) * δ ≤ 1 / 100 := by
  filter_upwards [(tendsto_order.mp (background_arcEnvelope_tendsto hα')).2 (1 / 100)
    (by norm_num), (tendsto_atTop.mp (tendsto_pivotShortCycleCutoff hα)) 2,
    eventually_gt_atTop (0 : ℕ)] with n he hL hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  let X := backgroundMaleCeiling n
  let P := backgroundWeightCeiling n
  let U := (n : ℝ) ^ (1 / 10 : ℝ)
  let L := (pivotShortCycleCutoff α n : ℝ)
  have hU : 0 < U := Real.rpow_pos_of_pos hnR _
  have hX : 0 ≤ X := by unfold X backgroundMaleCeiling; positivity
  have hP : 0 ≤ P := by unfold P backgroundWeightCeiling; positivity
  have hL2 : (2 : ℝ) ≤ L := by
    change (2 : ℝ) ≤ (pivotShortCycleCutoff α n : ℝ)
    exact_mod_cast hL
  have hXeq : (n : ℝ) ^ (α / 4) * (2 * X) =
      32 * (Real.log n / (n : ℝ) ^ (1 / 10 - α / 4)) := by
    rw [show 2 * X = (32 * Real.log n) / (n : ℝ) ^ (1 / 10 : ℝ) by
      unfold X backgroundMaleCeiling
      ring, rpow_mul_div_rpow hnR]
    ring
  have hPeq : (n : ℝ) ^ (α / 4) * (4 * P) =
      8240 * (Real.log n / (n : ℝ) ^ (1 - α / 4)) := by
    have h := rpow_mul_div_rpow hnR (8240 * Real.log n) (α / 4) 1
    rw [Real.rpow_one] at h
    rw [show 4 * P = (8240 * Real.log n) / n by unfold P backgroundWeightCeiling; ring, h]
    ring
  have hUeq : (n : ℝ) ^ (α / 4) * (2 / U) =
      2 * (n : ℝ) ^ (-(1 / 10 - α / 4)) := by
    unfold U
    rw [rpow_mul_div_rpow hnR, Real.rpow_neg hnR.le, div_eq_mul_inv]
  have hbound : L * (2 * X + 4 * P + 2 / U) ≤ 1 / 100 := by
    calc
      _ ≤ (n : ℝ) ^ (α / 4) * (2 * X + 4 * P + 2 / U) :=
        mul_le_mul_of_nonneg_right (pivotShortCycleCutoff_cast_le _ _) (by positivity)
      _ = _ := by rw [mul_add, mul_add, hXeq, hPeq, hUeq]
      _ ≤ _ := he.le
  have hsmall : 2 * X + 4 * P + 2 / U ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_right (show 1 ≤ L by linarith) (by positivity :
      0 ≤ 2 * X + 4 * P + 2 / U)
    simpa only [one_mul] using h.trans hbound
  refine ⟨by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hU.le], ?_⟩
  intro Y hY
  dsimp only
  have hexp : Real.exp (-Y / 2) ≤ 2 / U := by
    rw [show -Y / 2 = -(Y / 2) by ring, Real.exp_neg, inv_eq_one_div]
    calc
      _ ≤ 1 / (U / 2) := div_le_div_of_nonneg_left zero_le_one (by positivity) <|
        (div_le_div_of_nonneg_right hY (by norm_num)).trans
          (by linarith only [Real.add_one_le_exp (Y / 2)])
      _ = _ := by ring
  have hδ : 2 * X + 4 * P + Real.exp (-Y / 2) ≤ 2 * X + 4 * P + 2 / U :=
    add_le_add (le_refl (2 * X + 4 * P)) hexp
  exact ⟨⟨by positivity, hδ.trans (hsmall.trans (by norm_num))⟩,
    (mul_le_mul_of_nonneg_left hδ (by linarith only [hL2] : 0 ≤ L)).trans hbound⟩

private theorem tendsto_log_sq_div_nat_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ s) atTop (𝓝 0) := by
  have h := (tendsto_log_div_nat_rpow (show 0 < s / 2 by positivity)).pow 2
  rw [zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [div_pow, pow_two ((n : ℝ) ^ (s / 2)),
    ← Real.rpow_add (Nat.cast_pos.mpr hn), show s / 2 + s / 2 = s by ring]

private theorem background_labelEnvelope_tendsto {α : ℝ} (hα : 0 < α) (hα' : α < 1 / 10) :
    Tendsto (fun n : ℕ ↦
      2060 * (Real.log n / (n : ℝ) ^ (1 - α / 2)) +
        12360 * ((Real.log n) ^ 2 / (n : ℝ) ^ (3 * α / 4))) atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero, Function.comp_def] using
    (((tendsto_log_div_nat_rpow (show 0 < (1 : ℝ) - α / 2 by linarith)).const_mul 2060).add
      ((tendsto_log_sq_div_nat_rpow (show 0 < 3 * α / 4 by positivity)).const_mul 12360))

/-- The regular orientation sizes allow only a small omitted-label loss.
The squared cutoff also leaves the repeated-label loss small. -/
theorem eventually_backgroundLabelLoss_small {α : ℝ} (hα : 0 < α) (hα' : α < 1 / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : Finset (Fin n)) (p : Fin n → ℝ),
      (Cᶜ.card : ℝ) ≤ 6 * (n : ℝ) ^ (1 - α) * Real.log n →
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) → (∀ i, p i ≤ backgroundWeightCeiling n) →
      commonForwardLabelLoss C p (pivotShortCycleCutoff α n) ≤ 1 / 100 := by
  filter_upwards [(tendsto_order.mp (background_labelEnvelope_tendsto hα hα')).2
    (1 / 100) (by norm_num), eventually_gt_atTop (0 : ℕ)] with n he hn
  intro C p hC hp hp₁ hP
  let L := pivotShortCycleCutoff α n
  let X := (n : ℝ) ^ (α / 4)
  let M := 6 * (n : ℝ) ^ (1 - α) * Real.log n
  let P := backgroundWeightCeiling n
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hL : (L : ℝ) ≤ X := pivotShortCycleCutoff_cast_le α n
  have hP₀ : 0 ≤ P := by unfold P backgroundWeightCeiling; positivity
  have hM₀ : 0 ≤ M := by unfold M; positivity
  have hchoose : (L.choose 2 : ℝ) ≤ X ^ 2 := by
    rw [Nat.cast_choose_two]
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg L) hL 2
    nlinarith only [hsq, Nat.cast_nonneg (α := ℝ) L, sq_nonneg (L : ℝ)]
  have hcross : (L : ℝ) * (Cᶜ.card : ℝ) ≤ X * M :=
    mul_le_mul hL hC (Nat.cast_nonneg _) (by unfold X; positivity)
  have hcollision : X ^ 2 * P =
      2060 * (Real.log n / (n : ℝ) ^ (1 - α / 2)) := by
    have h := rpow_mul_div_rpow hnR (2060 * Real.log n) (α / 2) 1
    rw [Real.rpow_one] at h
    unfold X P backgroundWeightCeiling
    rw [pow_two, ← Real.rpow_add hnR, show α / 4 + α / 4 = α / 2 by ring, h]
    ring
  have homitted : X * M * P =
      12360 * ((Real.log n) ^ 2 / (n : ℝ) ^ (3 * α / 4)) := by
    have h := rpow_mul_div_rpow hnR (12360 * (Real.log n) ^ 2) (α / 4 + (1 - α)) 1
    rw [Real.rpow_one, show (1 : ℝ) - (α / 4 + (1 - α)) = 3 * α / 4 by ring] at h
    calc
      _ = ((n : ℝ) ^ (α / 4) * (n : ℝ) ^ (1 - α)) *
          (12360 * (Real.log n) ^ 2 / n) := by unfold X M P backgroundWeightCeiling; ring
      _ = _ := by rw [← Real.rpow_add hnR, h]; ring
  calc
    _ ≤ ((L.choose 2 : ℝ) + L * (Cᶜ.card : ℝ)) * P :=
      commonForwardLabelLoss_le_of_weight_le C p L hp hp₁ hP
    _ ≤ (X ^ 2 + X * M) * P :=
      mul_le_mul_of_nonneg_right (add_le_add hchoose hcross) hP₀
    _ ≤ _ := by rw [add_mul, hcollision, homitted]; exact he.le

/-- The complement of the common labels is the relative permutation's support. -/
theorem commonLabels_compl_eq_relative_support {n : ℕ} (μ ν : Matching n) :
    (Finset.univ.filter fun i : Fin n ↦ μ i = ν i)ᶜ =
      (relativeMenPermutation μ ν).support := by
  classical
  ext i
  simp [relativeMenPermutation, Equiv.Perm.mem_support, Equiv.symm_apply_eq]

/-- A regular pair of orientation sizes fits the omitted-label budget. -/
theorem card_compl_commonLabels_le_of_regularPairSizes {n : ℕ} (hn : 0 < n) {α : ℝ}
    (p : Profile n) (μ ν : Matching n)
    (hreg : RegularPairSizes n α
      ((worsePartnerMen p μ ν).card, (worsePartnerMen p ν μ).card)) :
    ((Finset.univ.filter fun i : Fin n ↦ μ i = ν i)ᶜ.card : ℝ) ≤
      6 * (n : ℝ) ^ (1 - α) * Real.log n := by
  classical
  rw [commonLabels_compl_eq_relative_support, ← union_worsePartnerMen_eq_support p μ ν,
    Finset.card_union_of_disjoint (disjoint_worsePartnerMen p μ ν), Nat.cast_add]
  exact add_le_of_regularPairSizes hn hreg

/-- The eventual short-cycle constraints used by the conditional Chebyshev estimate. -/
theorem eventually_backgroundShortCutoff_large {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ pivotShortCycleCutoff α n ∧
      100 ≤ Real.log (pivotShortCycleCutoff α n : ℝ) := by
  have hL := tendsto_pivotShortCycleCutoff hα
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (pivotShortCycleCutoff α n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hL)
  exact ((tendsto_atTop.mp hL) 2).and ((tendsto_atTop.mp hlog) 100)

end LennonPittelFormalization

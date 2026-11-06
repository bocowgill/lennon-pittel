module

public import LennonPittel.ForwardSuccessorRowLaw
public import LennonPittel.TruncatedScoreRowIntegral
public import LennonPittel.PivotSpouseBandMask

/-!
# A deterministic lower comparison for forward successor rows

The error in comparing an actual arc with its reference weight splits into
the blocking-rectangle normalization, the quadratic error in the competitor
product, and the finite endpoint of the successor integral.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem sum_embedding_le_sum {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) {f : β → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f (e i)) ≤ ∑ i, f i := by
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hf i

private theorem rowEligibilityProbability_le_scaled {x y M : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hM : M < 1)
    (hxy : x * y ≤ M) :
    rowEligibilityProbability x y ≤ ((1 - x) / (1 - M)) * y := by
  unfold rowEligibilityProbability
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1)
    (sub_pos.mpr hM) (sub_le_sub_left hxy 1)

/-- A lower bound for the successor of a distinguished target, with any
admissible integration cutoff. Competitors may be any subset of the reference
labels. All weights in the comparison use the full reference total. -/
theorem forwardSuccessorIntegral_ge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (j : ι) {x : ℝ} {y : ι → ℝ} {M H : ℝ}
    (hx : x ∈ Ico 0 1) (hy : ∀ i, y i ∈ Icc 0 1) (hY : 0 < ∑ i, y i)
    (hM : M ∈ Ico 0 1) (hxy : ∀ i, x * y i ≤ M) (hH : H ∈ Icc 0 1)
    (hcut : ∀ k, H * rowEligibilityProbability x (y (e k)) ≤ 1 / 2) :
    (1 - min 1 (M + 2 * (∑ i, (y i / ∑ k, y k) ^ 2) +
      Real.exp (-((1 - x) * (∑ k, y k) * H)))) * (y j / ∑ k, y k) ≤
      rowEligibilityProbability x (y j) *
        scoreRowMass Finset.univ (fun k ↦ rowEligibilityProbability x (y (e k))) 0 1 := by
  let Y := ∑ i, y i
  let c := (1 - x) / (1 - M)
  let a (k : κ) := rowEligibilityProbability x (y (e k))
  let s := ∑ i, (y i / Y) ^ 2
  let z := Real.exp (-((1 - x) * Y * H))
  have ha (k : κ) : a k ∈ Icc 0 1 :=
    ⟨rowEligibilityProbability_nonneg hx (hy _), rowEligibilityProbability_le_one hx (hy _)⟩
  have hc : 0 < c := div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hM.2)
  have hY' : Y ≠ 0 := hY.ne'
  have hA : 0 < c * Y := mul_pos hc hY
  have ha' (k : κ) : a k ≤ c * y (e k) :=
    rowEligibilityProbability_le_scaled hx (hy _) hM.2 (hxy _)
  have hsum : ∑ k, a k ≤ c * Y := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum fun k _ ↦ ha' k).trans
      (by rw [← Finset.mul_sum, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_embedding_le_sum e fun i ↦ (hy i).1) hc.le)
  have hsq : ∑ k, a k ^ 2 ≤ (c * Y) ^ 2 * s := by
    have heq : (c * Y) ^ 2 * s = c ^ 2 * ∑ i, y i ^ 2 := by
      dsimp only [s]
      simp_rw [div_pow]
      rw [← Finset.sum_div]
      field_simp [hY']
    rw [heq]
    calc
      _ ≤ ∑ k, (c * y (e k)) ^ 2 := Finset.sum_le_sum fun k _ ↦
        pow_le_pow_left₀ (ha k).1 (ha' k) 2
      _ = c ^ 2 * ∑ k, y (e k) ^ 2 := by simp only [mul_pow, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_embedding_le_sum e fun i ↦ sq_nonneg (y i))
        (sq_nonneg c)
  have hA' : (1 - x) * Y ≤ c * Y := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    exact (le_div_iff₀ (sub_pos.mpr hM.2)).mpr
      (mul_le_of_le_one_right (sub_nonneg.mpr hx.2.le) (by linarith only [hM.1]))
  have hz : Real.exp (-(c * Y * H)) ≤ z :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hA' hH.1))
  have hb := scoreRowMass_lower_truncated (J := Finset.univ) (a := a)
    (fun k _ ↦ ha k) hH (fun k _ ↦ hcut k) hA hsum hsq
  have he : 2 * ((c * Y) ^ 2 * s) / (c * Y) ^ 2 = 2 * s := by
    field_simp [hA.ne', hY']
  rw [he] at hb
  have hb' : (1 - z - 2 * s) / (c * Y) ≤ scoreRowMass Finset.univ a 0 1 :=
    (div_le_div_of_nonneg_right (by linarith only [hz]) hA.le).trans hb
  change (1 - min 1 (M + 2 * s + z)) * (y j / Y) ≤ _
  by_cases hd : M + 2 * s + z ≤ 1
  · rw [min_eq_right hd]
    have hR : 0 ≤ 1 - z - 2 * s := by linarith only [hd, hM.1]
    have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
    have hj : 0 ≤ y j / Y := div_nonneg (hy j).1 hY.le
    calc
      _ ≤ ((1 - M) * (1 - z - 2 * s)) * (y j / Y) := by
        apply mul_le_mul_of_nonneg_right _ hj
        nlinarith only [mul_nonneg hM.1 (add_nonneg (Real.exp_pos (-((1 - x) * Y * H))).le
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs))]
      _ = ((1 - x) * y j) * ((1 - z - 2 * s) / (c * Y)) := by
        dsimp only [c]
        field_simp [hY.ne', (sub_pos.mpr hx.2).ne', (sub_pos.mpr hM.2).ne']
      _ ≤ rowEligibilityProbability x (y j) * ((1 - z - 2 * s) / (c * Y)) :=
        mul_le_mul_of_nonneg_right (mul_le_rowEligibilityProbability hx (hy j))
          (div_nonneg hR hA.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb' (rowEligibilityProbability_nonneg hx (hy j))
  · rw [min_eq_left (le_of_not_ge hd), sub_self, zero_mul]
    apply mul_nonneg (rowEligibilityProbability_nonneg hx (hy j))
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun k _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right ht.2 (ha k).1).trans
        (by simpa only [one_mul] using (ha k).2))

/-- The target's share of the female spouse scores, indexed by her current husband. -/
noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2

/-- A capped deficit for comparison with the independent reference rows. -/
noncomputable def forwardReferenceRowDeficit {n : ℕ} (d : DiagonalScorePairs n)
    (M H : ℝ) (i : Fin n) : ℝ :=
  min 1 (M + 2 * (∑ j, (forwardSpouseWeight d j) ^ 2) +
    Real.exp (-((1 - (diagonalPairAt d i).1) * (∑ j, (diagonalPairAt d j).2) * H)))

theorem forwardReferenceRowDeficit_mem_Icc {n : ℕ} (d : DiagonalScorePairs n)
    {M : ℝ} (hM : 0 ≤ M) (H : ℝ) (i : Fin n) :
    forwardReferenceRowDeficit d M H i ∈ Icc 0 1 := by
  unfold forwardReferenceRowDeficit
  exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

/-- The lower comparison holds for the actual normalized stable-row arc probability. -/
theorem normalizedStableScoreRowLaw_successor_ge_reference {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) {M H : ℝ}
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1) (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1)
    (hY : 0 < ∑ k, (diagonalPairAt d k).2) (hM : M ∈ Ico 0 1)
    (hxy : ∀ k, (diagonalPairAt d i).1 * (diagonalPairAt d k).2 ≤ M)
    (hH : H ∈ Icc 0 1)
    (hcut : ∀ k, H * rowEligibilityProbability (diagonalPairAt d i).1
      (diagonalPairAt d k).2 ≤ 1 / 2) :
    ENNReal.ofReal ((1 - forwardReferenceRowDeficit d M H i) * forwardSpouseWeight d j.val) ≤
      normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) := by
  let e : {k : {k : Fin n // i ≠ k} // k ≠ j} ↪ Fin n :=
    ⟨fun k ↦ k.val.val, fun _ _ h ↦ Subtype.ext (Subtype.ext h)⟩
  rw [normalizedStableScoreRowLaw_successor_eq d i j hx hy]
  exact ENNReal.ofReal_le_ofReal
    (forwardSuccessorIntegral_ge e j.val hx hy hY hM hxy hH (fun k ↦ hcut (e k)))

/-- The weighted comparison deficit is bounded by the sum of the three errors. -/
theorem sum_forwardReferenceRowDeficit_le {n : ℕ} (d : DiagonalScorePairs n)
    {M H : ℝ} (hy : ∀ k, 0 ≤ (diagonalPairAt d k).2) (hY : 0 < ∑ k, (diagonalPairAt d k).2) :
    (∑ i, forwardSpouseWeight d i * forwardReferenceRowDeficit d M H i) ≤
      M + 2 * (∑ j, (forwardSpouseWeight d j) ^ 2) +
        ∑ i, forwardSpouseWeight d i *
          Real.exp (-((1 - (diagonalPairAt d i).1) * (∑ j, (diagonalPairAt d j).2) * H)) := by
  have hsum : ∑ i, forwardSpouseWeight d i = 1 := by
    unfold forwardSpouseWeight
    rw [← Finset.sum_div, div_self hY.ne']
  calc
    _ ≤ ∑ i, forwardSpouseWeight d i *
        (M + 2 * (∑ j, (forwardSpouseWeight d j) ^ 2) +
          Real.exp (-((1 - (diagonalPairAt d i).1) * (∑ j, (diagonalPairAt d j).2) * H))) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (min_le_right _ _)
        (div_nonneg (hy i) hY.le)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- A comparison suitable for the reference forest, with a global budget
on the deficit averaged by the target weights. -/
def HasForwardReferenceDeficit {n : ℕ} (d : DiagonalScorePairs n) (budget : ℝ) : Prop :=
  ∃ δ : Fin n → ℝ, (∀ i, δ i ∈ Icc 0 1) ∧
    (∑ i, forwardSpouseWeight d i * δ i) ≤ budget ∧
    ∀ (i : Fin n) (j : {j : Fin n // i ≠ j}),
      ENNReal.ofReal ((1 - δ i) * forwardSpouseWeight d j.val) ≤
        normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j)

/-- The mass defect plus the square correction in the reference forest bound. -/
theorem referenceForestError_le {ι : Type*} [Fintype ι] {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1) (hδ : ∀ i, δ i ∈ Icc 0 1) :
    let u (i : ι) := (1 - δ i) * p i
    1 - (∑ i, u i) + (∑ i, u i ^ 2) ≤ (∑ i, p i * δ i) + (∑ i, p i ^ 2) := by
  dsimp only
  have hdef : 1 - (∑ i, (1 - δ i) * p i) = ∑ i, p i * δ i := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, htotal, sub_sub_cancel,
      mul_comm (δ _) (p _)]
  rw [hdef]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr (hδ i).2) (hp i)) _ 2
  exact mul_le_of_le_one_left (hp i) (by linarith only [(hδ i).1])

private theorem rowEligibilityProbability_le_raw {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : rowEligibilityProbability x y ≤ y := by
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  unfold rowEligibilityProbability
  rw [div_le_iff₀ (by linarith only [hxy, hx.2])]
  rw [mul_comm y (1 - x * y)]
  exact mul_le_mul_of_nonneg_right (by linarith only [hxy]) hy.1

private theorem eventually_forwardReferenceScales :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧ 2 ≤ √(n : ℝ) ∧ 48 * Real.log n ≤ √(n : ℝ) ∧
      192 * Real.log (n : ℝ) ^ 2 / n ≤ (n : ℝ) ^ (-3 / 4 : ℝ) ∧
      48 / (n : ℝ) ≤ (n : ℝ) ^ (-3 / 4 : ℝ) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hs := Tendsto.eventually_ge_atTop
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hcast) 2
  have hq := Tendsto.eventually_ge_atTop
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp hcast) 48
  have hl := (((isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).const_mul_left
    48).comp_tendsto hcast).eventuallyLE
  have hls := (((isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) 2
    (by norm_num)).const_mul_left 192).comp_tendsto hcast).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), hs, hq, hl, hls] with n hn hs hq hl hls
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmul : (n : ℝ) ^ (-3 / 4 : ℝ) * n = (n : ℝ) ^ (1 / 4 : ℝ) := calc
    _ = (n : ℝ) ^ (-3 / 4 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn₀]; norm_num
  have hl' : |48 * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := hl
  have hls' : |192 * Real.log (n : ℝ) ^ (2 : ℝ)| ≤ |(n : ℝ) ^ (1 / 4 : ℝ)| := hls
  rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at hl'
  rw [Real.rpow_two, abs_of_nonneg (Real.rpow_nonneg hn₀.le _)] at hls'
  refine ⟨hn, ?_, (le_abs_self _).trans hl', ?_, ?_⟩
  · rw [Real.sqrt_eq_rpow]
    exact hs
  · exact (div_le_iff₀ hn₀).mpr ((le_abs_self _).trans (hls'.trans_eq hmul.symm))
  · exact (div_le_iff₀ hn₀).mpr (hq.trans_eq hmul.symm)

/-- On the regular diagonal geometry and weighted endpoint event, the true
row probabilities have deficit budget three times the endpoint cutoff.
For totals above the square-root cutoff, no endpoint event is needed. -/
theorem eventually_hasForwardReferenceDeficit :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      2 ≤ pivotDiagonalFemaleTotal d →
      (∀ i, forwardSpouseWeight d i ≤ 12 * Real.log n / n) →
      (∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (pivotDiagonalFemaleTotal d - 1)) →
      (∑ i, (forwardSpouseWeight d i) ^ 2) ≤ 24 / (n : ℝ) →
      (∑ i, forwardSpouseWeight d i *
        Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤
        (n : ℝ) ^ (-3 / 4 : ℝ) →
      HasForwardReferenceDeficit d (3 * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
  filter_upwards [eventually_forwardReferenceScales] with n ⟨hn, hs, hlog, hMbound, hsqbound⟩
  intro d hx hy hY hweight hmale hsquares hend
  let Y := pivotDiagonalFemaleTotal d
  let T : ℝ := (n : ℝ) ^ (-3 / 4 : ℝ)
  let M : ℝ := 192 * Real.log (n : ℝ) ^ 2 / n
  let H : ℝ := if Y ≤ √(n : ℝ) then 1 else 1 / 2
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₁]
  have hlog₀ := (Real.log_pos hn₁).le
  have hY' : 2 ≤ Y := hY
  have hY₀ : 0 < Y := by linarith only [hY']
  have hT : T < 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hn₁
      (show (-3 / 4 : ℝ) < 0 by norm_num)
  have hM : M ∈ Ico 0 1 := ⟨by unfold M; positivity, hMbound.trans_lt hT⟩
  have hH : H ∈ Icc 0 1 := by unfold H; split <;> norm_num
  have hweight₀ (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY₀.le
  have hweights : ∑ i, forwardSpouseWeight d i = 1 := by
    unfold forwardSpouseWeight
    rw [← Finset.sum_div]
    change Y / Y = 1
    exact div_self hY₀.ne'
  have hyraw (j : Fin n) :
      (diagonalPairAt d j).2 = Y * forwardSpouseWeight d j := by
    unfold forwardSpouseWeight
    change (diagonalPairAt d j).2 = Y * ((diagonalPairAt d j).2 / Y)
    field_simp [hY₀.ne']
  have hprod (i j : Fin n) : (diagonalPairAt d i).1 * (diagonalPairAt d j).2 ≤ M := by
    have hrat : Y / (Y - 1) ≤ 2 :=
      (div_le_iff₀ (by linarith only [hY'])).mpr (by linarith only [hY'])
    calc
      _ ≤ (8 * Real.log n / (Y - 1)) * (diagonalPairAt d j).2 :=
        mul_le_mul_of_nonneg_right (hmale i) (hy j).1
      _ = (8 * Real.log n * (Y / (Y - 1))) * forwardSpouseWeight d j := by
        rw [hyraw]
        ring
      _ ≤ (16 * Real.log n) * forwardSpouseWeight d j := by
        apply mul_le_mul_of_nonneg_right _ (hweight₀ j)
        linarith only [mul_le_mul_of_nonneg_left hrat (by positivity : 0 ≤ 8 * Real.log (n : ℝ))]
      _ ≤ (16 * Real.log n) * (12 * Real.log n / n) :=
        mul_le_mul_of_nonneg_left (hweight j) (by positivity)
      _ = M := by unfold M; ring
  have hcut (i j : Fin n) :
      H * rowEligibilityProbability (diagonalPairAt d i).1 (diagonalPairAt d j).2 ≤ 1 / 2 := by
    unfold H
    split
    · rename_i hlo
      rw [one_mul]
      have hss := Real.sq_sqrt hn₀.le
      have hyj : (diagonalPairAt d j).2 ≤ 1 / 2 := calc
        _ = Y * forwardSpouseWeight d j := hyraw j
        _ ≤ √(n : ℝ) * (12 * Real.log n / n) :=
          mul_le_mul hlo (hweight j) (hweight₀ j) (Real.sqrt_nonneg _)
        _ ≤ 1 / 2 := by
          rw [← mul_div_assoc, div_le_iff₀ hn₀]
          nlinarith only [hss,
            mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (n : ℝ))]
      exact (rowEligibilityProbability_le_raw (hx i) (hy j)).trans hyj
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (rowEligibilityProbability_le_one (hx i) (hy j)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have htrunc : (∑ i, forwardSpouseWeight d i *
      Real.exp (-((1 - (diagonalPairAt d i).1) * Y * H))) ≤ T := by
    by_cases hlo : Y ≤ √(n : ℝ)
    · simpa only [H, ite_eq_left hlo, mul_one, Y, T] using hend
    · have hhi := lt_of_not_ge hlo
      have hm (i : Fin n) : (diagonalPairAt d i).1 ≤ 1 / 2 := by
        refine (hmale i).trans ((div_le_iff₀ (by linarith only [hY'])).mpr ?_)
        linarith only [hlog, hs, hhi]
      have hE (i : Fin n) : Real.exp (-((1 - (diagonalPairAt d i).1) * Y * H)) ≤ T := by
        have hlower : Y / 4 ≤ (1 - (diagonalPairAt d i).1) * Y * H := by
          rw [show H = 1 / 2 by simp only [H, ite_eq_right hlo]]
          nlinarith only [mul_le_mul_of_nonneg_right (hm i) hY₀.le]
        rw [show T = Real.exp (Real.log n * (-3 / 4 : ℝ)) from Real.rpow_def_of_pos hn₀ _]
        exact Real.exp_le_exp.mpr (by linarith only [hlower, hlog, hhi, hlog₀])
      calc
        _ ≤ ∑ i, forwardSpouseWeight d i * T :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hE i) (hweight₀ i)
        _ = T := by rw [← Finset.sum_mul, hweights, one_mul]
  refine ⟨forwardReferenceRowDeficit d M H, forwardReferenceRowDeficit_mem_Icc d hM.1 H,
    (sum_forwardReferenceRowDeficit_le d (fun i ↦ (hy i).1) hY₀).trans ?_, ?_⟩
  · have hs' : 2 * ∑ i, (forwardSpouseWeight d i) ^ 2 ≤ T := by
      calc
        _ ≤ 2 * (24 / (n : ℝ)) := by gcongr
        _ = 48 / (n : ℝ) := by ring
        _ ≤ T := hsqbound
    change M + 2 * (∑ j, (forwardSpouseWeight d j) ^ 2) +
      (∑ i, forwardSpouseWeight d i * Real.exp (-((1 - (diagonalPairAt d i).1) * Y * H))) ≤
      3 * T
    exact (add_le_add (add_le_add hMbound hs') htrunc).trans_eq (by ring)
  · intro i j
    exact normalizedStableScoreRowLaw_successor_ge_reference d i j (hx i) hy hY₀ hM
      (hprod i) hH (hcut i)

end LennonPittelFormalization

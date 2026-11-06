module

public import LennonPittel.ContinuousScoreBridge
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# One-row integrals for the co-exposure estimates

The stability density in a fixed row is a finite product. The same integral
also bounds the probability that an eligible candidate is the successor.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace LennonPittelFormalization

variable {ι : Type*}

/-- The product of the non-blocking factors in one row. -/
noncomputable def scoreRowKernel (J : Finset ι) (y : ι → ℝ) (x : ℝ) : ℝ :=
  ∏ j ∈ J, (1 - x * y j)

/-- The integral of the row kernel over a real interval. -/
noncomputable def scoreRowMass (J : Finset ι) (y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, scoreRowKernel J y x

theorem continuous_scoreRowKernel (J : Finset ι) (y : ι → ℝ) :
    Continuous (scoreRowKernel J y) := by
  unfold scoreRowKernel
  fun_prop

private theorem scoreRowKernel_nonneg {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ scoreRowKernel J y x := by
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
    _ ≤ 1 := by simpa using hy₁ j hj)

/-- The complement union bound in product form. -/
theorem one_sub_sum_le_scoreRowKernel {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    1 - x * (∑ j ∈ J, y j) ≤ scoreRowKernel J y x := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [scoreRowKernel]
  | @insert j J hj ih =>
      rw [scoreRowKernel, Finset.prod_insert hj, Finset.sum_insert hj]
      have hyj₀ := hy₀ j (Finset.mem_insert_self j J)
      have hyj₁ := hy₁ j (Finset.mem_insert_self j J)
      have hsum : 0 ≤ ∑ k ∈ J, y k :=
        Finset.sum_nonneg fun k hk ↦ hy₀ k (Finset.mem_insert_of_mem hk)
      have hfac : 0 ≤ 1 - x * y j := by
        have := (mul_le_mul_of_nonneg_right hx.2 hyj₀).trans (one_mul (y j) ▸ hyj₁)
        linarith
      calc
        1 - x * (y j + ∑ k ∈ J, y k) ≤ (1 - x * y j) * (1 - x * ∑ k ∈ J, y k) := by
          have hm := mul_nonneg (mul_nonneg hx.1 hyj₀) (mul_nonneg hx.1 hsum)
          nlinarith only [hm]
        _ ≤ (1 - x * y j) * (∏ k ∈ J, (1 - x * y k)) :=
          mul_le_mul_of_nonneg_left (ih
            (fun k hk ↦ hy₀ k (Finset.mem_insert_of_mem hk))
            (fun k hk ↦ hy₁ k (Finset.mem_insert_of_mem hk))) hfac

/-- Dominate the row kernel by an exponential with rate the sum of the scores. -/
theorem scoreRowKernel_le_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    scoreRowKernel J y x ≤ Real.exp (-(∑ j ∈ J, y j) * x) := by
  unfold scoreRowKernel
  rw [show -(∑ j ∈ J, y j) * x = ∑ j ∈ J, -(x * y j) by
    calc
      -(∑ j ∈ J, y j) * x = -(x * ∑ j ∈ J, y j) := by ring
      _ = _ := by rw [Finset.mul_sum, Finset.sum_neg_distrib], Real.exp_sum]
  exact Finset.prod_le_prod₀
    (fun j hj ↦ sub_nonneg.mpr (calc
      x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy₀ j hj)
      _ ≤ 1 := by simpa using hy₁ j hj))
    (fun j _ ↦ Real.one_sub_le_exp_neg _)

private theorem integral_exp_neg_mul {r a b : ℝ} (hr : 0 < r) :
    (∫ x in a..b, Real.exp (-r * x)) = (Real.exp (-r * a) - Real.exp (-r * b)) / r := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun z ↦ -(Real.exp (-r * z)) / r) (Real.exp (-r * x)) x := by
    convert (((Real.hasDerivAt_exp (-r * x)).comp x
      (hasDerivAt_const_mul (-r))).neg.div_const r) using 1 <;> simp
    field_simp [hr.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- Integrating the exponential bound gives an unnormalized upper-tail estimate. -/
theorem scoreRowMass_le_exp_tail {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {r a b : ℝ} (hr : 0 < r) (hrsum : r ≤ ∑ j ∈ J, y j)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    scoreRowMass J y a b ≤ Real.exp (-r * a) / r := by
  calc
    scoreRowMass J y a b ≤ ∫ x in a..b, Real.exp (-r * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on hab
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans hb⟩
      exact (scoreRowKernel_le_exp hy₀ hy₁ hx').trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hrsum) hx'.1))
    _ = (Real.exp (-r * a) - Real.exp (-r * b)) / r := integral_exp_neg_mul hr
    _ ≤ Real.exp (-r * a) / r :=
      div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hr.le

/-- Keep the finite integration endpoint when the full score sum is small. -/
theorem scoreRowMass_le_finite_exp {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (hsum : s - c ≤ ∑ j ∈ J, y j) :
    scoreRowMass J y 0 1 ≤ Real.exp c * ((1 - Real.exp (-s)) / s) := by
  calc
    scoreRowMass J y 0 1 ≤ ∫ x in (0 : ℝ)..1, Real.exp c * Real.exp (-s * x) := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun x hx ↦ ?_
      refine (scoreRowKernel_le_exp hy₀ hy₁ hx).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_right (neg_le_neg hsum) hx.1
      have h₂ := mul_le_mul_of_nonneg_left hx.2 hc
      nlinarith only [h₁, h₂]
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul hs]; simp

/-- A short interval near zero contributes at least one quarter divided by the total. -/
theorem scoreRowMass_lower {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s : ℝ} (hs : 1 ≤ s) (hsum : ∑ j ∈ J, y j ≤ s) :
    1 / (4 * s) ≤ scoreRowMass J y 0 1 := by
  have hs₀ : 0 < s := lt_of_lt_of_le (by norm_num) hs
  let q : ℝ := 1 / (2 * s)
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q ≤ 1 := by dsimp [q]; rw [div_le_iff₀ (by positivity)]; linarith
  have hqprod : q * s = 1 / 2 := by dsimp [q]; field_simp
  calc
    1 / (4 * s) = ∫ _ in (0 : ℝ)..q, (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const]; simp [q]; ring
    _ ≤ ∫ x in (0 : ℝ)..q, scoreRowKernel J y x := by
      refine intervalIntegral.integral_mono_on hq₀ (continuous_const.intervalIntegrable _ _)
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _) fun x hx ↦ ?_
      have hxs : x * (∑ j ∈ J, y j) ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left hsum hx.1).trans
          ((mul_le_mul_of_nonneg_right hx.2 hs₀.le).trans_eq hqprod)
      exact (by linarith : 1 / 2 ≤ 1 - x * (∑ j ∈ J, y j)).trans
        (one_sub_sum_le_scoreRowKernel hy₀ hy₁ ⟨hx.1, hx.2.trans hq₁⟩)
    _ ≤ scoreRowMass J y 0 1 := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_interval le_rfl hq₀ hq₁ ?_
        ((continuous_scoreRowKernel J y).intervalIntegrable _ _)
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun x hx ↦
          scoreRowKernel_nonneg hy₀ hy₁ (Ioc_subset_Icc_self hx))

/-- An eligibility probability after excluding the blocking rectangle. -/
noncomputable def rowEligibilityProbability (x y : ℝ) : ℝ :=
  (1 - x) * y / (1 - x * y)

theorem rowEligibilityProbability_nonneg {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ rowEligibilityProbability x y := by
  unfold rowEligibilityProbability
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1) (by linarith [hx.2])

theorem rowEligibilityProbability_le_one {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : rowEligibilityProbability x y ≤ 1 := by
  unfold rowEligibilityProbability
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  rw [div_le_iff₀ (by linarith [hx.2])]
  nlinarith [hy.2]

theorem mul_le_rowEligibilityProbability {x y : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : (1 - x) * y ≤ rowEligibilityProbability x y := by
  unfold rowEligibilityProbability
  have hxy : x * y ≤ x := by simpa using mul_le_mul_of_nonneg_left hy.2 hx.1
  rw [le_div_iff₀ (by linarith [hx.2])]
  exact mul_le_of_le_one_right (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1)
    (by nlinarith [mul_nonneg hx.1 hy.1])

/-- The row successor integral is bounded by the target's relative eligibility weight.
Here `J` contains the candidates other than the spouse and the target. -/
theorem scoreRowSuccessor_le {J : Finset ι} {y : ι → ℝ} {x v : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hsum : 0 < ∑ j ∈ J, y j) :
    rowEligibilityProbability x v *
        scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1 ≤
      v / ((1 - x * v) * (∑ j ∈ J, y j)) := by
  let r := (1 - x) * (∑ j ∈ J, y j)
  have hx₁ : 0 < 1 - x := sub_pos.mpr hx.2
  have hr : 0 < r := mul_pos hx₁ hsum
  have hr' : r ≤ ∑ j ∈ J, rowEligibilityProbability x (y j) := by
    dsimp [r]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj ↦ mul_le_rowEligibilityProbability hx (hy j hj)
  have hmass :
      scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1 ≤ 1 / r := by
    simpa using scoreRowMass_le_exp_tail
      (fun j hj ↦ rowEligibilityProbability_nonneg hx (hy j hj))
      (fun j hj ↦ rowEligibilityProbability_le_one hx (hy j hj))
      hr hr' le_rfl (by norm_num) le_rfl
  have hden : 0 < 1 - x * v := by
    have h := mul_le_mul_of_nonneg_left hv.2 hx.1
    nlinarith [hx.2]
  refine (mul_le_mul_of_nonneg_left hmass (rowEligibilityProbability_nonneg hx hv)).trans_eq ?_
  dsimp [r, rowEligibilityProbability]
  field_simp

/-- Normalizing the upper-tail row integral gives the conditional exponential bound. -/
theorem scoreRowMass_div_le_exp_tail {J : Finset ι} {y : ι → ℝ}
    (hy₀ : ∀ j ∈ J, 0 ≤ y j) (hy₁ : ∀ j ∈ J, y j ≤ 1)
    {s a : ℝ} (hs : 2 ≤ s) (hsum₀ : s - 1 ≤ ∑ j ∈ J, y j)
    (hsum₁ : ∑ j ∈ J, y j ≤ s) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    scoreRowMass J y a 1 / scoreRowMass J y 0 1 ≤ 8 * Real.exp (-(s - 1) * a) := by
  have hs₀ : 0 < s := by linarith
  have hs₁ : 0 < s - 1 := by linarith
  have hL := scoreRowMass_lower hy₀ hy₁ (show 1 ≤ s by linarith) hsum₁
  have hL₀ : 0 < 1 / (4 * s) := by positivity
  have hM := scoreRowMass_le_exp_tail hy₀ hy₁ hs₁ hsum₀ ha ha₁ le_rfl
  calc
    _ ≤ (Real.exp (-(s - 1) * a) / (s - 1)) / scoreRowMass J y 0 1 :=
      div_le_div_of_nonneg_right hM (hL₀.le.trans hL)
    _ ≤ (Real.exp (-(s - 1) * a) / (s - 1)) / (1 / (4 * s)) :=
      div_le_div_of_nonneg_left (by positivity) hL₀ hL
    _ = (4 * s / (s - 1)) * Real.exp (-(s - 1) * a) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hs₁).mpr (by linarith))
      (Real.exp_pos _).le

section FiniteRows

variable [Fintype ι] [DecidableEq ι]

private theorem sum_erase_eq_total_sub (y : ι → ℝ) (i : ι) :
    ∑ j ∈ Finset.univ.erase i, y j = (∑ j, y j) - y i := by
  linarith only [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]

/-- For a row with the spouse omitted, a large total bounds its stability mass. -/
theorem scoreRowMass_erase_le_inv (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤ 1 / ((∑ j, y j) - y i) := by
  have hr : 0 < (∑ j, y j) - y i := by linarith [(hy i).2]
  simpa using scoreRowMass_le_exp_tail
    (J := Finset.univ.erase i) (y := y)
    (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hr
    (sum_erase_eq_total_sub y i).ge le_rfl (by norm_num) le_rfl

/-- For a row with the spouse omitted, the finite endpoint bounds its stability mass. -/
theorem scoreRowMass_erase_le_finite_exp (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 0 < ∑ j, y j) :
    scoreRowMass (Finset.univ.erase i) y 0 1 ≤
      Real.exp (y i) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) :=
  scoreRowMass_le_finite_exp (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
    hs (hy i).1 (sum_erase_eq_total_sub y i).ge

/-- The normalized conditional score tail for a fixed stable row. -/
theorem scoreRowMass_erase_div_le_exp_tail (y : ι → ℝ) (i : ι)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    scoreRowMass (Finset.univ.erase i) y a 1 / scoreRowMass (Finset.univ.erase i) y 0 1 ≤
      8 * Real.exp (-((∑ j, y j) - 1) * a) :=
  scoreRowMass_div_le_exp_tail (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hs
    (by rw [sum_erase_eq_total_sub]; linarith [(hy i).2])
    (by rw [sum_erase_eq_total_sub]; linarith [(hy i).1]) ha ha₁

/-- The finite-endpoint bound for the full stability density. -/
theorem scoreRowMass_prod_le_finite_exp (y : ι → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 0 < ∑ j, y j) :
    (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) ≤
      Real.exp (∑ j, y j) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) ^
        Fintype.card ι := by
  calc
    _ ≤ ∏ i, Real.exp (y i) * ((1 - Real.exp (-(∑ j, y j))) / (∑ j, y j)) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ intervalIntegral.integral_nonneg (by norm_num)
        fun _ hx ↦ scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hx)
        (fun i _ ↦ scoreRowMass_erase_le_finite_exp y i hy hs)
    _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const,
      Finset.card_univ]

/-- The large-total bound for the full stability density. -/
theorem scoreRowMass_prod_le_inv_pow (y : ι → ℝ)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hs : 2 ≤ ∑ j, y j) :
    (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) ≤
      Real.exp 2 / (∑ j, y j) ^ Fintype.card ι := by
  let s := ∑ j, y j
  have hs₀ : 0 < s := by dsimp [s]; linarith
  have hi (i : ι) : 1 / (s - y i) ≤ Real.exp (2 * (y i / s)) / s := by
    let z := y i / s
    have hz₀ : 0 ≤ z := div_nonneg (hy i).1 hs₀.le
    have hz₁ : z ≤ 1 / 2 := by
      dsimp [z]
      rw [div_le_iff₀ hs₀]
      dsimp [s]
      linarith [(hy i).2]
    have hprod : 1 ≤ (1 + 2 * z) * (1 - z) := by
      have hmul := mul_nonneg hz₀ (show 0 ≤ 1 - 2 * z by linarith)
      nlinarith only [hmul]
    have hlinear : 1 + 2 * z ≤ Real.exp (2 * z) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * z)
    have hexp : 1 ≤ Real.exp (2 * z) * (1 - z) :=
      hprod.trans (mul_le_mul_of_nonneg_right hlinear (by linarith))
    have hsi : 0 < s - y i := by dsimp [s]; linarith [(hy i).2]
    have heq : (s - y i) / s = 1 - z := by rw [sub_div, div_self hs₀.ne']
    rw [div_le_div_iff₀ hsi hs₀, one_mul]
    calc
      s = 1 * s := (one_mul s).symm
      _ ≤ Real.exp (2 * (y i / s)) * (s - y i) := (le_div_iff₀ hs₀).mp (by
        change 1 ≤ (Real.exp (2 * z) * (s - y i)) / s
        rw [mul_div_assoc, heq]
        exact hexp)
  calc
    _ ≤ ∏ i, Real.exp (2 * (y i / s)) / s :=
      Finset.prod_le_prod₀ (fun _ _ ↦ intervalIntegral.integral_nonneg (by norm_num)
        fun _ hx ↦ scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) hx)
        (fun i _ ↦ (scoreRowMass_erase_le_inv y i hy hs).trans (hi i))
    _ = _ := by
      rw [Finset.prod_div_distrib, ← Real.exp_sum, ← Finset.mul_sum, ← Finset.sum_div]
      simp [show (∑ j, y j) / s = 1 by dsimp [s]; exact div_self hs₀.ne']
      rfl

end FiniteRows

/-- Change variables from a target score above the spouse score to a unit-interval score. -/
theorem scoreRowMass_affine_eq {J : Finset ι} {y : ι → ℝ} {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1) :
    scoreRowMass J y x 1 =
      (1 - x) * scoreRowKernel J y x *
        scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1 := by
  have hpoint (t : ℝ) :
      scoreRowKernel J y (x + (1 - x) * t) =
        scoreRowKernel J y x *
          scoreRowKernel J (fun j ↦ rowEligibilityProbability x (y j)) t := by
    unfold scoreRowKernel
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    unfold rowEligibilityProbability
    have hxy : x * y j ≤ x := by simpa using mul_le_mul_of_nonneg_left (hy j hj).2 hx.1
    have hd : 1 - x * y j ≠ 0 := by linarith [hx.2]
    field_simp
    ring
  have haff :
      (1 - x) * (∫ t in (0 : ℝ)..1, scoreRowKernel J y (x + (1 - x) * t)) =
        scoreRowMass J y x 1 := by
    unfold scoreRowMass
    have h := intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
      (scoreRowKernel J y) (1 - x) x
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one] at h
    rw [show x + (1 - x) = 1 by ring] at h
    exact h
  rw [← haff]
  simp_rw [hpoint, intervalIntegral.integral_const_mul, scoreRowMass]
  ring

/-- The unnormalized successor integral is bounded by the stability mass times the arc bound. -/
theorem scoreRowSuccessor_unnormalized_le {J : Finset ι} {y : ι → ℝ} {x v : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : ∀ j ∈ J, y j ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (hsum : 0 < ∑ j ∈ J, y j) :
    v * scoreRowMass J y x 1 ≤ ((1 - x * v) * scoreRowKernel J y x) *
      (v / ((1 - x * v) * (∑ j ∈ J, y j))) := by
  have hxv : x * v ≤ x := by simpa using mul_le_mul_of_nonneg_left hv.2 hx.1
  have hden : 0 < 1 - x * v := by linarith [hx.2]
  have hK := scoreRowKernel_nonneg (fun j hj ↦ (hy j hj).1)
    (fun j hj ↦ (hy j hj).2) ⟨hx.1, hx.2.le⟩
  calc
    _ = ((1 - x * v) * scoreRowKernel J y x) *
        (rowEligibilityProbability x v *
          scoreRowMass J (fun j ↦ rowEligibilityProbability x (y j)) 0 1) := by
      rw [scoreRowMass_affine_eq hx hy, rowEligibilityProbability]
      have hden' : 1 - v * x ≠ 0 := by simpa only [mul_comm] using hden.ne'
      field_simp [hden.ne', hden']
    _ ≤ _ := mul_le_mul_of_nonneg_left (scoreRowSuccessor_le hx hy hv hsum)
      (mul_nonneg hden.le hK)

section SuccessorMass

open MeasureTheory
open scoped ENNReal

/-- The two-score law for a cell after removing the blocking rectangle, without normalization. -/
noncomputable def rowNonblockingLaw (x y : ℝ) : Measure (ℝ × ℝ) :=
  (unitScoreLaw.prod unitScoreLaw).restrict (Iio x ×ˢ Iio y)ᶜ

instance (x y : ℝ) : IsFiniteMeasure (rowNonblockingLaw x y) := by
  unfold rowNonblockingLaw
  infer_instance

theorem unitScoreLaw_apply_Iio {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    unitScoreLaw (Iio a) = ENNReal.ofReal a := by
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Iio]
  have heq : Iio a ∩ Icc (0 : ℝ) 1 = Ico 0 a := by
    ext t
    change (t < a ∧ 0 ≤ t ∧ t ≤ 1) ↔ (0 ≤ t ∧ t < a)
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.le.trans ha.2⟩⟩
  rw [heq, Real.volume_Ico, sub_zero]

/-- Removing a wider rectangle subsumes the original non-blocking restriction. -/
theorem rowNonblockingLaw_apply_avoiding {x a y : ℝ} (hxa : x ≤ a)
    (ha : a ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    rowNonblockingLaw x y (Iio a ×ˢ Iio y)ᶜ = ENNReal.ofReal (1 - a * y) := by
  have hs : MeasurableSet (Iio a ×ˢ Iio y) := measurableSet_Iio.prod measurableSet_Iio
  have hsub : (Iio x ×ˢ Iio y : Set (ℝ × ℝ)) ⊆ Iio a ×ˢ Iio y :=
    fun _ h ↦ ⟨h.1.trans_le hxa, h.2⟩
  rw [rowNonblockingLaw, Measure.restrict_apply hs.compl,
    inter_eq_left.mpr (compl_subset_compl.mpr hsub), measure_compl hs (measure_ne_top _ _),
    measure_univ, Measure.prod_prod, unitScoreLaw_apply_Iio ha, unitScoreLaw_apply_Iio hy,
    ← ENNReal.ofReal_mul ha.1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (mul_nonneg ha.1 hy.1)]

/-- The target is eligible and no other candidate willing to accept the man beats the target. -/
def scoreSuccessorPairEvent (x v : ℝ) (y : ι → ℝ) :
    Set ((ℝ × ℝ) × (ι → ℝ × ℝ)) :=
  {z | x < z.1.1 ∧ z.1.2 < v ∧ ∀ h, ¬((z.2 h).1 < z.1.1 ∧ (z.2 h).2 < y h)}

theorem measurableSet_scoreSuccessorPairEvent [Fintype ι] (x v : ℝ) (y : ι → ℝ) :
    MeasurableSet (scoreSuccessorPairEvent x v y) := by
  unfold scoreSuccessorPairEvent
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_lt measurable_const measurable_fst.fst).inter
    ((measurableSet_lt measurable_fst.snd measurable_const).inter
      (MeasurableSet.iInter fun h ↦ ?_))
  have hmeas : Measurable (fun z : (ℝ × ℝ) × (ι → ℝ × ℝ) ↦ z.2 h) :=
    (measurable_pi_apply h).comp measurable_snd
  exact ((measurableSet_lt hmeas.fst measurable_fst.fst).inter
    (measurableSet_lt hmeas.snd measurable_const)).compl

private theorem scoreSuccessorPairEvent_section {x v : ℝ} (y : ι → ℝ) (uv : ℝ × ℝ)
    (h : uv ∈ Ioi x ×ˢ Iio v) :
    Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y =
      Set.pi univ (fun j ↦ (Iio uv.1 ×ˢ Iio (y j))ᶜ) := by
  ext z
  simp only [mem_preimage, scoreSuccessorPairEvent, mem_ofPred_eq, mem_pi, mem_univ,
    true_implies, mem_compl_iff, mem_prod, mem_Iio]
  exact ⟨fun h' ↦ h'.2.2, fun h' ↦ ⟨h.1, h.2, h'⟩⟩

private theorem scoreSuccessorPairEvent_section_empty {x v : ℝ} (y : ι → ℝ) (uv : ℝ × ℝ)
    (h : uv ∉ Ioi x ×ˢ Iio v) :
    Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact h ⟨hz.1, hz.2.1⟩

/-- Exact unnormalized mass of the target-successor event on the split product law. -/
theorem scoreSuccessorPairEvent_mass [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    ((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))
        (scoreSuccessorPairEvent x v y) =
      ENNReal.ofReal (v * scoreRowMass Finset.univ y x 1) := by
  let T : Set (ℝ × ℝ) := Ioi x ×ˢ Iio v
  let F : ℝ × ℝ → ℝ≥0∞ := fun uv ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Iio
  have hsupp : ∀ᵐ uv ∂rowNonblockingLaw x v, uv ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    unfold rowNonblockingLaw unitScoreLaw
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  rw [Measure.prod_apply (measurableSet_scoreSuccessorPairEvent x v y)]
  have hsection :
      (fun uv ↦ (Measure.pi fun j ↦ rowNonblockingLaw x (y j))
        (Prod.mk uv ⁻¹' scoreSuccessorPairEvent x v y)) =ᵐ[rowNonblockingLaw x v]
          T.indicator F := by
    filter_upwards [hsupp] with uv hu
    by_cases ht : uv ∈ T
    · rw [scoreSuccessorPairEvent_section y uv ht, Measure.pi_pi, Set.indicator_of_mem ht]
      simp only [rowNonblockingLaw_apply_avoiding ht.1.le hu.1 (hy _)]
      unfold F scoreRowKernel
      exact (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ sub_nonneg.mpr (by
        nlinarith [(hy j).1, (hy j).2, hu.1.2,
          mul_nonneg (sub_nonneg.mpr hu.1.2) (hy j).1])).symm
    · rw [scoreSuccessorPairEvent_section_empty y uv ht, measure_empty, Set.indicator_of_notMem ht]
  rw [lintegral_congr_ae hsection, lintegral_indicator hT]
  have hsub : T ⊆ (Iio x ×ˢ Iio v : Set (ℝ × ℝ))ᶜ := by
    intro uv h h'
    exact (not_lt_of_ge (show x < uv.1 from h.1).le) (show uv.1 < x from h'.1)
  have hrestrict : (rowNonblockingLaw x v).restrict T =
      (unitScoreLaw.restrict (Ioi x)).prod (unitScoreLaw.restrict (Iio v)) := by
    rw [rowNonblockingLaw, Measure.restrict_restrict_of_subset hsub]
    exact (Measure.prod_restrict _ _).symm
  rw [hrestrict]
  have hf : Measurable fun u ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y u) :=
    (continuous_scoreRowKernel Finset.univ y).measurable.ennreal_ofReal
  unfold F
  rw [show (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1)) =
    (fun uv : ℝ × ℝ ↦ ENNReal.ofReal (scoreRowKernel Finset.univ y uv.1) * (1 : ℝ≥0∞)) by
      funext uv; rw [mul_one]]
  rw [lintegral_prod_mul hf.aemeasurable measurable_const.aemeasurable, lintegral_const, one_mul,
    Measure.restrict_apply_univ, unitScoreLaw_apply_Iio hv]
  have hleft : unitScoreLaw.restrict (Ioi x) = volume.restrict (Ioc x 1) := by
    rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    change (x < u ∧ 0 ≤ u ∧ u ≤ 1) ↔ (x < u ∧ u ≤ 1)
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hx.1.trans h.1.le, h.2⟩⟩
  rw [hleft, scoreRowMass, intervalIntegral.integral_of_le hx.2,
    ENNReal.ofReal_mul hv.1, mul_comm (ENNReal.ofReal v)]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact ((continuous_scoreRowKernel Finset.univ y).intervalIntegrable x 1).1
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc x 1))]
      with u hu
    exact scoreRowKernel_nonneg (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2)
      ⟨hx.1.trans hu.1.le, hu.2⟩

/-- The full mass of a non-blocking cell. -/
theorem rowNonblockingLaw_apply_univ {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    rowNonblockingLaw x y univ = ENNReal.ofReal (1 - x * y) := by
  rw [← rowNonblockingLaw_apply_avoiding le_rfl hx hy]
  unfold rowNonblockingLaw
  rw [Measure.restrict_apply_univ,
    Measure.restrict_apply (measurableSet_Iio.prod measurableSet_Iio).compl, inter_self]

/-- The weighted bound for a target-successor event with its exact product measure. -/
theorem scoreSuccessorPairEvent_mass_le [Fintype ι] {x v : ℝ} {y : ι → ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) (hsum : 0 < ∑ j, y j) :
    ((rowNonblockingLaw x v).prod (Measure.pi fun j ↦ rowNonblockingLaw x (y j)))
        (scoreSuccessorPairEvent x v y) ≤
      (rowNonblockingLaw x v univ * ∏ j, rowNonblockingLaw x (y j) univ) *
        ENNReal.ofReal (v / ((1 - x * v) * (∑ j, y j))) := by
  have hxy (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : 0 < 1 - x * z := by
    have h := mul_le_mul_of_nonneg_left hz.2 hx.1
    linarith [hx.2]
  have hK := scoreRowKernel_nonneg (J := (Finset.univ : Finset ι))
    (fun j _ ↦ (hy j).1) (fun j _ ↦ (hy j).2) ⟨hx.1, hx.2.le⟩
  rw [scoreSuccessorPairEvent_mass ⟨hx.1, hx.2.le⟩ hv hy,
    rowNonblockingLaw_apply_univ ⟨hx.1, hx.2.le⟩ hv]
  simp only [rowNonblockingLaw_apply_univ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1, hx.2.le⟩) (hy _)]
  unfold scoreRowKernel at hK
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ (hxy (y j) (hy j)).le),
    ← ENNReal.ofReal_mul (hxy v hv).le, ← ENNReal.ofReal_mul
      (mul_nonneg (hxy v hv).le hK)]
  exact ENNReal.ofReal_le_ofReal (scoreRowSuccessor_unnormalized_le hx
    (fun j _ ↦ hy j) hv hsum)

end SuccessorMass

end LennonPittelFormalization

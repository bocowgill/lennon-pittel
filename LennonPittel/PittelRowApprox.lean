module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

/-!
# Row integral estimates for Pittel's first moment

After fixing the relative spouse scores, a row contributes the integral of
a finite product of linear nonblocking factors. The second-order correction
is quadratic in the weights, with explicit remainder bounds.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace LennonPittelFormalization

/-- A row contribution after rescaling the integrated coordinate by the total spouse score. -/
noncomputable def pittelRowIntegral {ι : Type*} (I : Finset ι) (w : ι → ℝ) (s : ℝ) : ℝ :=
  ∫ t in 0..s, ∏ j ∈ I, (1 - t * w j)

private theorem one_sub_le_exp_quadratic (u : ℝ) (hu : 0 ≤ u) :
    1 - u ≤ Real.exp (-u - u ^ 2 / 2) := by
  let f (x : ℝ) := (1 - x) * Real.exp (x + x ^ 2 / 2)
  have hd (x : ℝ) : HasDerivAt f (-(x ^ 2) * Real.exp (x + x ^ 2 / 2)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := ((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).exp
    convert h₁.mul h₂ using 1
    · funext y
      simp [f, id]
    · simp [id]
      ring
  have hanti : Antitone f := antitone_of_hasDerivAt_nonpos hd (fun x ↦
    show -(x ^ 2) * Real.exp (x + x ^ 2 / 2) ≤ 0 from
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (Real.exp_nonneg _))
  have hh : f u ≤ f 0 := hanti hu
  rw [show -u - u ^ 2 / 2 = -(u + u ^ 2 / 2) by ring, Real.exp_neg, ← one_div]
  exact (le_div_iff₀ (Real.exp_pos (u + u ^ 2 / 2))).2 (by simpa [f] using hh)

private theorem exp_cubic_le_one_sub (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    Real.exp (-u - u ^ 2 / 2 - u ^ 3) ≤ 1 - u := by
  let f (x : ℝ) := (1 - x) * Real.exp (x + x ^ 2 / 2 + x ^ 3)
  have hd (x : ℝ) :
      HasDerivAt f (x ^ 2 * (2 - 3 * x) * Real.exp (x + x ^ 2 / 2 + x ^ 3)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := (((hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)).add
      (hasDerivAt_pow 3 x)).exp
    convert h₁.mul h₂ using 1
    · funext y
      simp [f, id]
    · simp [id]
      ring
  have hm : MonotoneOn f (Icc 0 (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ..)
      (show ContinuousOn f (Icc 0 (1 / 2)) by dsimp [f]; fun_prop)
      (fun x _ ↦ (hd x).hasDerivWithinAt)
    intro x hx
    have hx' : x ≤ 1 / 2 := (interior_subset hx).2
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (Real.exp_nonneg _)
  have hh : f 0 ≤ f u := hm ⟨le_rfl, by norm_num⟩ ⟨hu, hu'⟩ hu
  have hh' := (div_le_iff₀ (Real.exp_pos (u + u ^ 2 / 2 + u ^ 3))).2
    (show 1 ≤ (1 - u) * Real.exp (u + u ^ 2 / 2 + u ^ 3) by simpa [f] using hh)
  simpa only [one_div, ← Real.exp_neg, neg_add, sub_eq_add_neg] using hh'

private theorem exp_neg_le_quadratic (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let f (x : ℝ) := 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hd (x : ℝ) : HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := (hasDerivAt_pow 2 x).div_const 2
    have h₃ := (hasDerivAt_id x).neg.exp
    convert (h₁.add h₂).sub h₃ using 1
    · funext y
      simp [f, id]
    · simp [id]
  have hm := monotone_of_hasDerivAt_nonneg hd (fun x ↦
    show 0 ≤ -1 + x + Real.exp (-x) by linarith [Real.one_sub_le_exp_neg x])
  have h : f 0 ≤ f u := hm hu
  simpa [f, sub_nonneg] using h

private theorem pittel_exp_moment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ k * Real.exp (-(a * t))) = (k.factorial : ℝ) / a ^ (k + 1) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, t ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * t)) := by
      simp only [add_sub_cancel_right, Real.rpow_natCast]
    _ = _ := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) ha,
        Real.Gamma_nat_eq_factorial, ← Nat.cast_succ, Real.rpow_natCast, one_div,
        inv_pow, div_eq_mul_inv, mul_comm]

private theorem pittel_integrable_exp_moment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-(a * t))) (Ioi 0) := by
  have hbase : IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-t)) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using
      (Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity))
  have hscaled : IntegrableOn (fun t : ℝ ↦ (a * t) ^ k * Real.exp (-(a * t))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 0 ha).mpr (by simpa only [mul_zero] using hbase)
  simpa only [IntegrableOn, mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'),
    one_mul] using
    hscaled.const_mul ((a ^ k)⁻¹)

private noncomputable def expMonomial (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ k * Real.exp (-(a * t))

private noncomputable def rowUpper (a b t : ℝ) : ℝ :=
  expMonomial a 0 t - (b / 2) * expMonomial a 2 t + (b ^ 2 / 8) * expMonomial a 4 t

private noncomputable def rowLower (a b m t : ℝ) : ℝ :=
  expMonomial a 0 t - (b / 2) * expMonomial a 2 t - (m * b) * expMonomial a 3 t

private theorem rowUpper_eq (a b t : ℝ) :
    rowUpper a b t =
      Real.exp (-(a * t)) * (1 - b * t ^ 2 / 2 + (b * t ^ 2 / 2) ^ 2 / 2) := by
  simp only [rowUpper, expMonomial, pow_zero, one_mul]
  ring

private theorem rowLower_eq (a b m t : ℝ) :
    rowLower a b m t = Real.exp (-(a * t)) * (1 - b * t ^ 2 / 2 - m * b * t ^ 3) := by
  simp only [rowLower, expMonomial, pow_zero, one_mul]
  ring

private theorem prod_le_rowUpper {ι : Type*} (I : Finset ι) (w : ι → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hw : ∀ j ∈ I, 0 ≤ w j) (hcap : ∀ j ∈ I, t * w j ≤ 1) :
    (∏ j ∈ I, (1 - t * w j)) ≤ rowUpper (∑ j ∈ I, w j) (∑ j ∈ I, (w j) ^ 2) t := by
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, (w j) ^ 2
  have hb : 0 ≤ b := Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j)
  change _ ≤ rowUpper a b t
  calc
    _ ≤ ∏ j ∈ I, Real.exp (-(t * w j) - (t * w j) ^ 2 / 2) :=
      Finset.prod_le_prod₀ (fun j hj ↦ sub_nonneg.mpr (hcap j hj))
        (fun j hj ↦ one_sub_le_exp_quadratic _ (mul_nonneg ht (hw j hj)))
    _ = Real.exp (-(a * t)) * Real.exp (-(b * t ^ 2 / 2)) := by
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      simp [a, b, mul_pow, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_neg_distrib]
      ring
    _ ≤ rowUpper a b t := by
      rw [rowUpper_eq]
      exact mul_le_mul_of_nonneg_left (exp_neg_le_quadratic _ (by positivity))
        (Real.exp_nonneg _)

private theorem rowLower_le_prod {ι : Type*} (I : Finset ι) (w : ι → ℝ) (t m : ℝ)
    (ht : 0 ≤ t) (hw : ∀ j ∈ I, 0 ≤ w j) (hm : ∀ j ∈ I, w j ≤ m)
    (hsmall : ∀ j ∈ I, t * w j ≤ 1 / 2) :
    rowLower (∑ j ∈ I, w j) (∑ j ∈ I, (w j) ^ 2) m t ≤
      ∏ j ∈ I, (1 - t * w j) := by
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, (w j) ^ 2
  let c := ∑ j ∈ I, (w j) ^ 3
  have hc : c ≤ m * b := by
    dsimp [c, b]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_succ' (w j) 2] using
      mul_le_mul_of_nonneg_right (hm j hj) (sq_nonneg (w j))
  change rowLower a b m t ≤ _
  calc
    _ ≤ Real.exp (-(a * t)) * Real.exp (-(b * t ^ 2 / 2 + c * t ^ 3)) := by
      rw [rowLower_eq]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg ht 3)
      linarith [Real.one_sub_le_exp_neg (b * t ^ 2 / 2 + c * t ^ 3)]
    _ = ∏ j ∈ I, Real.exp (-(t * w j) - (t * w j) ^ 2 / 2 - (t * w j) ^ 3) := by
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      simp [a, b, c, mul_pow, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_neg_distrib]
      ring
    _ ≤ _ := Finset.prod_le_prod₀ (fun j _ ↦ Real.exp_nonneg _)
      (fun j hj ↦ exp_cubic_le_one_sub _ (mul_nonneg ht (hw j hj)) (hsmall j hj))

private theorem integrableOn_rowUpper {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (rowUpper a b) (Ioi 0) := by
  exact ((pittel_integrable_exp_moment ha 0).sub
    ((pittel_integrable_exp_moment ha 2).const_mul (b / 2))).add
      ((pittel_integrable_exp_moment ha 4).const_mul (b ^ 2 / 8))

private theorem integrableOn_rowLower {a : ℝ} (ha : 0 < a) (b m : ℝ) :
    IntegrableOn (rowLower a b m) (Ioi 0) := by
  exact ((pittel_integrable_exp_moment ha 0).sub
    ((pittel_integrable_exp_moment ha 2).const_mul (b / 2))).sub
      ((pittel_integrable_exp_moment ha 3).const_mul (m * b))

private theorem integral_rowUpper {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ t : ℝ in Ioi 0, rowUpper a b t) = 1 / a - b / a ^ 3 + 3 * b ^ 2 / a ^ 5 := by
  have h0 := pittel_integrable_exp_moment ha 0
  have h2 := (pittel_integrable_exp_moment ha 2).const_mul (b / 2)
  have h4 := (pittel_integrable_exp_moment ha 4).const_mul (b ^ 2 / 8)
  have h := integral_add (h0.sub h2) h4
  simp only [Pi.sub_apply] at h
  rw [integral_sub h0 h2, integral_const_mul, integral_const_mul] at h
  simp only [pittel_exp_moment ha] at h
  calc
    _ = _ := by simpa only [rowUpper, expMonomial] using h
    _ = _ := by norm_num [Nat.factorial]; ring

private theorem integral_rowLower {a : ℝ} (ha : 0 < a) (b m : ℝ) :
    (∫ t : ℝ in Ioi 0, rowLower a b m t) = 1 / a - b / a ^ 3 - 6 * m * b / a ^ 4 := by
  have h0 := pittel_integrable_exp_moment ha 0
  have h2 := (pittel_integrable_exp_moment ha 2).const_mul (b / 2)
  have h3 := (pittel_integrable_exp_moment ha 3).const_mul (m * b)
  have h := integral_sub (h0.sub h2) h3
  simp only [Pi.sub_apply] at h
  rw [integral_sub h0 h2, integral_const_mul, integral_const_mul] at h
  simp only [pittel_exp_moment ha] at h
  calc
    _ = _ := by simpa only [rowLower, expMonomial] using h
    _ = _ := by norm_num [Nat.factorial]; ring

/-- A row upper bound with exact second-order term and nonnegative quadratic remainder. -/
theorem pittelRowIntegral_le {ι : Type*} (I : Finset ι) (w : ι → ℝ) {s : ℝ}
    (hs : 0 ≤ s) (hw : ∀ j ∈ I, 0 ≤ w j) (hcap : ∀ j ∈ I, s * w j ≤ 1)
    (ha : 0 < ∑ j ∈ I, w j) :
    let a := ∑ j ∈ I, w j
    let b := ∑ j ∈ I, (w j) ^ 2
    pittelRowIntegral I w s ≤ 1 / a - b / a ^ 3 + 3 * b ^ 2 / a ^ 5 := by
  dsimp only
  let a := ∑ j ∈ I, w j
  let b := ∑ j ∈ I, (w j) ^ 2
  have hfi : Continuous fun t : ℝ ↦ ∏ j ∈ I, (1 - t * w j) := by fun_prop
  have hUi := integrableOn_rowUpper ha b
  have hUi' : IntegrableOn (rowUpper a b) (Ioc 0 s) := hUi.mono_set Ioc_subset_Ioi_self
  have hUn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] rowUpper a b := by
    apply ae_of_all
    intro t
    rw [rowUpper_eq]
    apply mul_nonneg (Real.exp_nonneg _)
    nlinarith [sq_nonneg (b * t ^ 2 / 2 - 1)]
  calc
    pittelRowIntegral I w s ≤ ∫ t : ℝ in Ioc 0 s, rowUpper a b t := by
      rw [pittelRowIntegral, intervalIntegral.integral_of_le hs]
      apply setIntegral_mono_on (hfi.intervalIntegrable 0 s).1 hUi' measurableSet_Ioc
      intro t ht
      exact prod_le_rowUpper I w t ht.1.le hw fun j hj ↦
        mul_le_mul_of_nonneg_right ht.2 (hw j hj) |>.trans (hcap j hj)
    _ ≤ ∫ t : ℝ in Ioi 0, rowUpper a b t :=
      setIntegral_mono_set hUi hUn Ioc_subset_Ioi_self.eventuallyLE
    _ = _ := integral_rowUpper ha b

/-- A row lower bound from a smaller integration interval with uniformly small factors. -/
theorem le_pittelRowIntegral {ι : Type*} (I : Finset ι) (w : ι → ℝ) {s L m : ℝ}
    (hL : 0 ≤ L) (hLs : L ≤ s) (hw : ∀ j ∈ I, 0 ≤ w j) (hcap : ∀ j ∈ I, s * w j ≤ 1)
    (hm : ∀ j ∈ I, w j ≤ m) (hsmall : ∀ j ∈ I, L * w j ≤ 1 / 2)
    (ha : 0 < ∑ j ∈ I, w j) :
    let a := ∑ j ∈ I, w j
    let b := ∑ j ∈ I, (w j) ^ 2
    1 / a - b / a ^ 3 - 6 * m * b / a ^ 4 - Real.exp (-(a * L)) / a ≤ pittelRowIntegral I w s :=
  by
    dsimp only
    let a := ∑ j ∈ I, w j
    let b := ∑ j ∈ I, (w j) ^ 2
    have hb : 0 ≤ b := Finset.sum_nonneg fun j _ ↦ sq_nonneg (w j)
    have hm' : 0 ≤ m := by
      obtain ⟨j, hj⟩ : I.Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at ha
        exact lt_irrefl 0 ha
      exact (hw j hj).trans (hm j hj)
    have hs := hL.trans hLs
    have hfi : Continuous fun t : ℝ ↦ ∏ j ∈ I, (1 - t * w j) := by fun_prop
    have hRi := integrableOn_rowLower ha b m
    have hRi₁ : IntegrableOn (rowLower a b m) (Ioc 0 L) :=
      hRi.mono_set Ioc_subset_Ioi_self
    have hRi₂ : IntegrableOn (rowLower a b m) (Ioi L) := hRi.mono_set (Ioi_subset_Ioi hL)
    have hdiff : (∫ t : ℝ in Ioi 0, rowLower a b m t) =
        (∫ t : ℝ in Ioc 0 L, rowLower a b m t) +
          ∫ t : ℝ in Ioi L, rowLower a b m t := by
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hRi₁ hRi₂,
        Ioc_union_Ioi_eq_Ioi hL]
    have htail : (∫ t : ℝ in Ioi L, rowLower a b m t) ≤ Real.exp (-(a * L)) / a := by
      have hneg : -a < 0 := neg_lt_zero.mpr ha
      calc
        _ ≤ ∫ t : ℝ in Ioi L, Real.exp (-a * t) := by
          apply setIntegral_mono_on hRi₂ (integrableOn_exp_mul_Ioi hneg L) measurableSet_Ioi
          intro t ht
          rw [rowLower_eq, neg_mul]
          nth_rw 2 [← mul_one (Real.exp _)]
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          have ht' : 0 ≤ t := hL.trans ht.le
          have h₂ : 0 ≤ b * t ^ 2 / 2 := by positivity
          have h₃ : 0 ≤ m * b * t ^ 3 := by positivity
          linarith
        _ = _ := by rw [integral_exp_mul_Ioi hneg, neg_div_neg_eq, neg_mul]
    calc
      _ ≤ ∫ t : ℝ in Ioc 0 L, rowLower a b m t := by
        rw [integral_rowLower ha b m] at hdiff
        linarith
      _ ≤ ∫ t : ℝ in Ioc 0 L, ∏ j ∈ I, (1 - t * w j) := by
        apply setIntegral_mono_on hRi₁ (hfi.intervalIntegrable 0 L).1 measurableSet_Ioc
        intro t ht
        exact rowLower_le_prod I w t m ht.1.le hw hm fun j hj ↦
          mul_le_mul_of_nonneg_right ht.2 (hw j hj) |>.trans (hsmall j hj)
      _ ≤ pittelRowIntegral I w s := by
        rw [pittelRowIntegral, intervalIntegral.integral_of_le hs]
        apply setIntegral_mono_set (hfi.intervalIntegrable 0 s).1 _
          (Ioc_subset_Ioc le_rfl hLs).eventuallyLE
        filter_upwards [self_mem_ae_restrict (μ := volume) (measurableSet_Ioc (a := 0) (b := s))]
          with t ht
        exact Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr
          (mul_le_mul_of_nonneg_right ht.2 (hw j hj) |>.trans (hcap j hj))

end LennonPittelFormalization

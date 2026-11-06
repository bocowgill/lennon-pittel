module

public import LennonPittel.CoexposureScoreRow
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Truncated lower bound for a score row

For a cutoff at which all competitor factors are at least one half, the
finite product dominates a quadratic correction to an exponential density.
The integral loses only an exponential endpoint term and the quadratic error.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace LennonPittelFormalization

private theorem exp_neg_sub_sq_le_one_sub {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1 / 2) :
    Real.exp (-u - u ^ 2) ≤ 1 - u := by
  let f (x : ℝ) := (1 - x) * Real.exp (x + x ^ 2)
  have hd (x : ℝ) :
      HasDerivAt f (x * (1 - 2 * x) * Real.exp (x + x ^ 2)) x := by
    have h₁ := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h₂ := ((hasDerivAt_id x).add (hasDerivAt_pow 2 x)).exp
    convert h₁.mul h₂ using 1
    · funext y
      dsimp [f, id]
    · dsimp [id]
      ring
  have hm : MonotoneOn f (Icc 0 (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ..)
      (show ContinuousOn f (Icc 0 (1 / 2)) by dsimp [f]; fun_prop)
      (fun x _ ↦ (hd x).hasDerivWithinAt)
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) (1 / 2) := interior_subset hx
    exact mul_nonneg (mul_nonneg hx'.1 (by linarith [hx'.2])) (Real.exp_nonneg _)
  have hh : f 0 ≤ f u := hm ⟨le_rfl, by norm_num⟩ ⟨hu, hu'⟩ hu
  rw [show -u - u ^ 2 = -(u + u ^ 2) by ring, Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).2 (by simpa [f] using hh)

private theorem lower_le_integral_exp_mul_one_sub_sq {A B H : ℝ} (hA : 0 < A)
    (hB : 0 ≤ B) (hH : 0 ≤ H) :
    (1 - Real.exp (-(A * H)) - 2 * B / A ^ 2) / A ≤
      ∫ t in (0 : ℝ)..H, Real.exp (-(A * t)) * (1 - B * t ^ 2) := by
  let F (t : ℝ) :=
    (B / A * t ^ 2 + (2 * B / A ^ 2) * t + 2 * B / A ^ 3 - 1 / A) *
      Real.exp (-(A * t))
  have hderiv (t : ℝ) :
      HasDerivAt F (Real.exp (-(A * t)) * (1 - B * t ^ 2)) t := by
    have hpol := ((((hasDerivAt_pow 2 t).const_mul (B / A)).add
      (hasDerivAt_const_mul (2 * B / A ^ 2))).add_const (2 * B / A ^ 3)).sub_const (1 / A)
    have hexp := ((hasDerivAt_const_mul A).neg (x := t)).exp
    convert hpol.mul hexp using 1
    simp only [Pi.neg_apply, Pi.add_apply]
    field_simp [hA.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have htail :
      0 ≤ (B / A * H ^ 2 + (2 * B / A ^ 2) * H + 2 * B / A ^ 3) *
        Real.exp (-(A * H)) := by positivity
  calc
    _ ≤ (1 - Real.exp (-(A * H)) - 2 * B / A ^ 2) / A +
        (B / A * H ^ 2 + (2 * B / A ^ 2) * H + 2 * B / A ^ 3) *
          Real.exp (-(A * H)) := le_add_of_nonneg_right htail
    _ = F H - F 0 := by simp [F]; field_simp [hA.ne']; ring

/-- Lower bound the row kernel up to a cutoff where each linear factor is at least one half. -/
private theorem exp_mul_one_sub_sq_le_scoreRowKernel {ι : Type*} {J : Finset ι}
    {a : ι → ℝ} {A B t : ℝ} (ha : ∀ j ∈ J, 0 ≤ a j) (ht : 0 ≤ t)
    (hcut : ∀ j ∈ J, t * a j ≤ 1 / 2) (hsum : ∑ j ∈ J, a j ≤ A)
    (hsq : ∑ j ∈ J, a j ^ 2 ≤ B) :
    Real.exp (-(A * t)) * (1 - B * t ^ 2) ≤ scoreRowKernel J a t := by
  have hprod :
      Real.exp (-(t * (∑ j ∈ J, a j)) - t ^ 2 * (∑ j ∈ J, a j ^ 2)) ≤
        scoreRowKernel J a t := by
    rw [show -(t * (∑ j ∈ J, a j)) - t ^ 2 * (∑ j ∈ J, a j ^ 2) =
      ∑ j ∈ J, (-(t * a j) - (t * a j) ^ 2) by
        simp only [mul_pow, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum],
      Real.exp_sum, scoreRowKernel]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ Real.exp_nonneg _)
      (fun j hj ↦ exp_neg_sub_sq_le_one_sub (mul_nonneg ht (ha j hj)) (hcut j hj))
  calc
    _ ≤ Real.exp (-(A * t)) * Real.exp (-(B * t ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg _) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply le_trans (Real.exp_le_exp.mpr ?_) hprod
      have hlinear := mul_le_mul_of_nonneg_left hsum ht
      have hquad := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
      linarith only [hlinear, hquad]

/-- The unit row mass is bounded below by the exponential integral up to
`H`, less an explicit loss controlled by the squared competitor scores. -/
theorem scoreRowMass_lower_truncated {ι : Type*} {J : Finset ι} {a : ι → ℝ}
    {A B H : ℝ} (ha : ∀ j ∈ J, a j ∈ Icc 0 1) (hH : H ∈ Icc 0 1)
    (hcut : ∀ j ∈ J, H * a j ≤ 1 / 2) (hA : 0 < A)
    (hsum : ∑ j ∈ J, a j ≤ A) (hsq : ∑ j ∈ J, a j ^ 2 ≤ B) :
    (1 - Real.exp (-(A * H)) - 2 * B / A ^ 2) / A ≤ scoreRowMass J a 0 1 := by
  have hB : 0 ≤ B := (Finset.sum_nonneg fun j _ ↦ sq_nonneg (a j)).trans hsq
  calc
    _ ≤ ∫ t in (0 : ℝ)..H, Real.exp (-(A * t)) * (1 - B * t ^ 2) :=
      lower_le_integral_exp_mul_one_sub_sq hA hB hH.1
    _ ≤ ∫ t in (0 : ℝ)..H, scoreRowKernel J a t := by
      refine intervalIntegral.integral_mono_on hH.1
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        ((continuous_scoreRowKernel J a).intervalIntegrable _ _) fun t ht ↦ ?_
      exact exp_mul_one_sub_sq_le_scoreRowKernel (fun j hj ↦ (ha j hj).1) ht.1
        (fun j hj ↦ (mul_le_mul_of_nonneg_right ht.2 (ha j hj).1).trans (hcut j hj)) hsum hsq
    _ ≤ scoreRowMass J a 0 1 := by
      unfold scoreRowMass
      refine intervalIntegral.integral_mono_interval le_rfl hH.1 hH.2 ?_
        ((continuous_scoreRowKernel J a).intervalIntegrable _ _)
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun t ht ↦
          Finset.prod_nonneg fun j hj ↦ sub_nonneg.mpr (calc
            t * a j ≤ 1 * a j := mul_le_mul_of_nonneg_right ht.2 (ha j hj).1
            _ ≤ 1 := by simpa only [one_mul] using (ha j hj).2))

end LennonPittelFormalization

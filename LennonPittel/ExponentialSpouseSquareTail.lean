module

public import LennonPittel.StandardExponentialScoreLaw
public import LennonPittel.BoundedProductChernoff
public import LennonPittel.PittelSimplexMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Concentration of squared shares of exponential scores

The radius has a lower-tail bound from its Laplace transform. A logarithmic
coordinate cutoff makes the squared scores bounded for an upper-tail estimate.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

local instance : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- Independent rate-one exponential scores, before taking their shares. -/
noncomputable def iidExponentialScoreLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ expMeasure 1

/-- The constant in the geometric lower tail of the exponential radius. -/
noncomputable def expRadiusLowerFactor : ℝ := Real.exp (1 / 2) / 2

theorem expRadiusLowerFactor_pos : 0 < expRadiusLowerFactor := by
  unfold expRadiusLowerFactor
  positivity

theorem expRadiusLowerFactor_lt_one : expRadiusLowerFactor < 1 := by
  have hsq : Real.exp (1 / 2) ^ (2 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h : Real.exp (1 / 2) < 2 :=
    (sq_lt_sq₀ (Real.exp_pos _).le (by norm_num)).mp
      (hsq.trans_lt (Real.exp_one_lt_three.trans (by norm_num)))
  exact (div_lt_one (by norm_num : 0 < (2 : ℝ))).mpr h

/-- Dividing a square sum of at most `6n` by a total of at least `n/2`
gives a scaled angular square score of at most 24. -/
theorem pittelAngularSquareScore_spouseAngle_le_of_totals {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hT : (n : ℝ) / 2 ≤ ∑ i, x i)
    (hS : (∑ i, (x i) ^ (2 : ℕ)) ≤ 6 * (n : ℝ)) :
    pittelAngularSquareScore (spouseAngle x) ≤ 24 := by
  let T := ∑ i, x i
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hhalf : 0 < (n : ℝ) / 2 := by positivity
  have hT' : 0 < T := hhalf.trans_le hT
  calc
    _ = (n : ℝ) * (∑ i, (x i) ^ (2 : ℕ)) / T ^ (2 : ℕ) := by
      simp only [pittelAngularSquareScore, spouseAngle, div_pow, ← Finset.sum_div, T,
        mul_div_assoc]
    _ ≤ ((n : ℝ) * (6 * (n : ℝ))) / ((n : ℝ) / 2) ^ (2 : ℕ) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hS hn'.le)
        (sq_pos_of_pos hhalf) (pow_le_pow_left₀ hhalf.le hT 2)
    _ = _ := by field_simp; ring

/-- The sum of exponential scores is below half its mean with geometrically small mass. -/
theorem measure_iidExponential_radius_lt_half_le (n : ℕ) :
    iidExponentialScoreLaw n {x | (∑ i, x i) < (n : ℝ) / 2} ≤
      ENNReal.ofReal (expRadiusLowerFactor ^ n) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  let g (t : ℝ) := ENNReal.ofReal (Real.exp (-t))
  let F (x : Fin n → ℝ) := ENNReal.ofReal (Real.exp ((n : ℝ) / 2 - ∑ i, x i))
  have hg : Measurable g := by unfold g; fun_prop
  have hf : Measurable F := by unfold F; fun_prop
  have hcoord (i : Fin n) : Measurable (fun x : Fin n → ℝ ↦ g (x i)) :=
    hg.comp (measurable_pi_apply i)
  have hfactor (x : Fin n → ℝ) :
      F x = ENNReal.ofReal (Real.exp ((n : ℝ) / 2)) * ∏ i, g (x i) := by
    unfold F g
    rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]
  have hrow (i : Fin n) : (∫⁻ x : Fin n → ℝ, g (x i) ∂Measure.pi ν) =
      ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [(measurePreserving_eval ν i).lintegral_comp hg]
    change (∫⁻ t, ENNReal.ofReal (Real.exp (-t)) ∂expMeasure 1) = _
    rw [lintegral_expMeasure_one_exp_neg, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  change (Measure.pi ν) _ ≤ _
  calc
    _ ≤ ∫⁻ x, F x ∂Measure.pi ν := by
      apply meas_le_lintegral₀ hf.aemeasurable
      intro x hx
      have h : 0 ≤ (n : ℝ) / 2 - ∑ i, x i := sub_nonneg.mpr hx.le
      simpa only [F, Real.exp_zero, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) / 2)) * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n := by
      simp_rw [hfactor]
      rw [lintegral_const_mul _ (Finset.univ.measurable_prod fun i _ ↦ hcoord i),
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
          (iIndepFun_pi fun _ ↦ hg.aemeasurable) hcoord]
      simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
      rw [← ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, expRadiusLowerFactor]
      congr 1
      rw [show (n : ℝ) / 2 = (n : ℝ) * (1 / 2) by ring, Real.exp_nat_mul,
        ← mul_pow, mul_one_div]

/-- A union bound for the largest coordinate of the exponential array. -/
theorem measure_iidExponential_exists_gt_le (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    iidExponentialScoreLaw n {x | ∃ i, L < x i} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L)) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  let E (i : Fin n) := {x : Fin n → ℝ | L < x i}
  have hE (i : Fin n) : (Measure.pi ν) (E i) = ENNReal.ofReal (Real.exp (-L)) := by
    have he := (measurePreserving_eval ν i).measure_preimage
      (measurableSet_Ioi (a := L)).nullMeasurableSet
    exact he.trans (expMeasure_one_Ioi hL)
  have he : {x : Fin n → ℝ | ∃ i, L < x i} = ⋃ i, E i := by
    ext x
    simp only [mem_iUnion, E, mem_ofPred_eq]
  rw [iidExponentialScoreLaw, he]
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ν, le_refl]

/-- The squared score clipped to a deterministic upper bound. -/
def clippedExponentialSquare (L t : ℝ) : ℝ := min (t ^ (2 : ℕ)) (L ^ (2 : ℕ))

/-- A bounded-product tail for the sum of the clipped squares. -/
theorem measure_iidExponential_sum_clippedSquare_gt_le (n : ℕ) {L : ℝ} (hL : 0 < L) :
    iidExponentialScoreLaw n {x | 6 * (n : ℝ) < ∑ i, clippedExponentialSquare L (x i)} ≤
      ENNReal.ofReal (Real.exp (- (2 * (n : ℝ)) / L ^ (2 : ℕ))) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  have hg : Measurable (clippedExponentialSquare L) := by unfold clippedExponentialSquare; fun_prop
  have hb (z : ℝ) : clippedExponentialSquare L z ∈ Icc 0 (L ^ (2 : ℕ)) :=
    ⟨le_min (sq_nonneg _) (sq_nonneg _), min_le_right _ _⟩
  have hmass (i : Fin n) :
      (∫⁻ z, ENNReal.ofReal (clippedExponentialSquare L z) ∂ν i) ≤ ENNReal.ofReal (2 : ℝ) := by
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (z ^ (2 : ℕ)) ∂ν i :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = _ := lintegral_expMeasure_one_sq.trans (by norm_num)
  refine (measure_pi_boundedSum_gt_le ν (fun _ ↦ clippedExponentialSquare L)
    (fun _ ↦ hg) (sq_pos_of_pos hL) (fun _ ↦ hb) (fun _ ↦ (2 : ℝ))
    (fun _ ↦ by norm_num) hmass _).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (sq_nonneg L)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith only [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
    (show 0 ≤ (n : ℝ) * 2 by positivity)]

/-- A large angular square score forces a small radius, an unclipped
coordinate, or a large clipped-square sum. -/
theorem measure_iidExponential_angleSquare_gt_le {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L) :
    iidExponentialScoreLaw n {x | 24 < pittelAngularSquareScore (spouseAngle x)} ≤
      ENNReal.ofReal (expRadiusLowerFactor ^ n) +
        (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L)) +
        ENNReal.ofReal (Real.exp (-(2 * (n : ℝ)) / L ^ (2 : ℕ))) := by
  let ν (i : Fin n) := expMeasure (1 : ℝ)
  have hae : ∀ᵐ x ∂iidExponentialScoreLaw n, ∀ i, 0 ≤ x i := ae_all_iff.2 fun i ↦
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae ae_expMeasure_one_nonneg
  let A : Set (Fin n → ℝ) := {x | (∑ i, x i) < (n : ℝ) / 2}
  let B : Set (Fin n → ℝ) := {x | ∃ i, L < x i}
  let C : Set (Fin n → ℝ) := {x | 6 * (n : ℝ) < ∑ i, clippedExponentialSquare L (x i)}
  let U : Set (Fin n → ℝ) := (A ∪ B) ∪ C
  have hsub : {x | 24 < pittelAngularSquareScore (spouseAngle x)}
      ≤ᵐ[iidExponentialScoreLaw n] U := by
    filter_upwards [hae] with x hx hbad
    by_cases hA : x ∈ A
    · exact Or.inl (Or.inl hA)
    by_cases hB : x ∈ B
    · exact Or.inl (Or.inr hB)
    by_cases hC : x ∈ C
    · exact Or.inr hC
    exfalso
    have hT : (n : ℝ) / 2 ≤ ∑ i, x i := le_of_not_gt hA
    have hS : (∑ i, clippedExponentialSquare L (x i)) ≤ 6 * (n : ℝ) := le_of_not_gt hC
    have he : (∑ i, (x i) ^ (2 : ℕ)) = ∑ i, clippedExponentialSquare L (x i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi : x i ≤ L := le_of_not_gt fun hi ↦ hB ⟨i, hi⟩
      exact (min_eq_left (pow_le_pow_left₀ (hx i) hi 2)).symm
    exact (not_lt_of_ge (pittelAngularSquareScore_spouseAngle_le_of_totals hn x hT
      (he.trans_le hS))) hbad
  exact (measure_mono_ae hsub).trans ((measure_union_le (A ∪ B) C).trans
    (add_le_add ((measure_union_le A B).trans (add_le_add
      (measure_iidExponential_radius_lt_half_le n) (measure_iidExponential_exists_gt_le n hL.le)))
        (measure_iidExponential_sum_clippedSquare_gt_le n hL)))

private theorem eventually_geometric_le_neg_rpow {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, q ^ n ≤ (n : ℝ) ^ (-p) := by
  have hq : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq₀ hq₁)
  have h := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    (p / -Real.log q)).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (0 : ℕ), h] with n hn hnlog
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have habs : |p / -Real.log q * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hnlog
  rw [Real.rpow_one, abs_of_nonneg hn'.le] at habs
  have hle : p * Real.log (n : ℝ) ≤ (n : ℝ) * -Real.log q := by
    apply (div_le_iff₀ hq).mp
    rw [mul_div_right_comm]
    exact (le_abs_self _).trans habs
  rw [Real.rpow_def_of_pos hn', ← Real.exp_log hq₀, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by linarith only [hle])

private theorem size_mul_exp_log_cutoff_eq {n : ℕ} (hn : 0 < n) (p : ℝ) :
    (n : ℝ) * Real.exp (-((p + 2) * Real.log (n : ℝ))) = (n : ℝ) ^ (-(p + 1)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [show -((p + 2) * Real.log (n : ℝ)) = Real.log (n : ℝ) * (-(p + 2)) by ring,
    ← Real.rpow_def_of_pos hn']
  calc
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 2)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn', show (1 : ℝ) + -(p + 2) = -(p + 1) by ring]

private theorem eventually_clippedSquare_rate_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(2 * (n : ℝ)) /
      ((p + 2) * Real.log (n : ℝ)) ^ (2 : ℕ)) ≤ (n : ℝ) ^ (-(p + 1)) := by
  have h := (((isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 3 (by norm_num)).const_mul_left
    ((p + 1) * (p + 2) ^ (2 : ℕ))).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ), h] with n hn hh
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have hL : 0 < (p + 2) * Real.log (n : ℝ) := by positivity
  have habs : |((p + 1) * (p + 2) ^ (2 : ℕ)) * (Real.log (n : ℝ)) ^ (3 : ℝ)| ≤
      |(n : ℝ) ^ (1 : ℝ)| := hh
  rw [Real.rpow_one, abs_of_nonneg hn₀.le, Real.rpow_ofNat] at habs
  have hprod : (p + 1) * Real.log (n : ℝ) * ((p + 2) * Real.log (n : ℝ)) ^ (2 : ℕ) ≤
      2 * (n : ℝ) := by
    calc
      _ = ((p + 1) * (p + 2) ^ (2 : ℕ)) * (Real.log (n : ℝ)) ^ (3 : ℕ) := by ring
      _ ≤ (n : ℝ) := (le_abs_self _).trans habs
      _ ≤ _ := by linarith
  have hd := (le_div_iff₀ (sq_pos_of_pos hL)).mpr hprod
  rw [Real.rpow_def_of_pos hn₀, neg_div]
  exact Real.exp_le_exp.mpr (by linarith only [hd])

/-- Uniformly for any fixed desired power, the large squared-share event
in the exponential representation eventually has probability at most that inverse power. -/
theorem eventually_measure_iidExponential_angleSquare_gt_le (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n : ℕ in atTop, iidExponentialScoreLaw n
      {x | 24 < pittelAngularSquareScore (spouseAngle x)} ≤ ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    eventually_geometric_le_neg_rpow expRadiusLowerFactor_pos expRadiusLowerFactor_lt_one (p + 1),
    eventually_clippedSquare_rate_le p hp] with n hn hR hS
  have hn' : 0 < n := by omega
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hn'
  have hn₃ : 3 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  let L := (p + 2) * Real.log (n : ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  let a := (n : ℝ) ^ (-(p + 1))
  have ha : 0 ≤ a := Real.rpow_nonneg hn₀.le _
  have hcap : (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-L)) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn₀.le,
      size_mul_exp_log_cutoff_eq hn' p]
  refine (measure_iidExponential_angleSquare_gt_le hn' hL).trans ?_
  rw [hcap]
  refine (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hR) le_rfl)
    (ENNReal.ofReal_le_ofReal hS)).trans ?_
  rw [← ENNReal.ofReal_add ha ha, ← ENNReal.ofReal_add (add_nonneg ha ha) ha]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = 3 * a := by ring
    _ ≤ (n : ℝ) * a := mul_le_mul_of_nonneg_right hn₃ ha
    _ = _ := calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(p + 1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀, show (1 : ℝ) + -(p + 1) = -p by ring]

end LennonPittelFormalization

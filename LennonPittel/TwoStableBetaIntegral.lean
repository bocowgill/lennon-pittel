module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Group.LIntegral
public import LennonPittel.PittelSimplexRadial
public import LennonPittel.TwoStablePairSizeSums

/-!
# The radial integral in the two-stable-matching bound

Translate the common-score sum to the total of the three sums. For each
positive total, dilate the other two scores separately. A pointwise
inequality extends the resulting simplex integral to the unit square,
leaving a product of ordinary beta factors.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LennonPittelFormalization

/-- The closed form of the unit-interval Laplace integral, for positive input. -/
noncomputable def pairLaplaceClosed (x : ℝ) : ℝ :=
  (1 - Real.exp (-x)) / x

theorem measurable_pairLaplaceClosed : Measurable pairLaplaceClosed := by
  unfold pairLaplaceClosed
  fun_prop

private theorem pairLaplaceClosed_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ pairLaplaceClosed x := by
  apply div_nonneg _ hx.le
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)]

private theorem pairLaplaceClosed_le_one {x : ℝ} (hx : 0 < x) :
    pairLaplaceClosed x ≤ 1 := by
  apply (div_le_iff₀ hx).2
  linarith [Real.one_sub_le_exp_neg x]

private theorem pairLaplaceClosed_le_inv {x : ℝ} (hx : 0 < x) :
    pairLaplaceClosed x ≤ x⁻¹ := by
  rw [← one_div, pairLaplaceClosed]
  gcongr
  linarith [Real.exp_nonneg (-x)]

/-- The radial integral is bounded by its length below one and a logarithm above one. -/
theorem lintegral_pairLaplaceClosed_le (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x in Ioc (0 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) ≤
      ENNReal.ofReal (1 + Real.log n) := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  have hlow : (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (pairLaplaceClosed x)) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro x hx
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (pairLaplaceClosed_le_one hx.1)
      _ = _ := by simp [Real.volume_Ioc]
  have hinv : IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioc 1 n) := by
    have hc : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Icc 1 n) :=
      continuousOn_id.inv₀ fun x hx ↦ (zero_lt_one.trans_le hx.1).ne'
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hhigh : (∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) ≤
      ENNReal.ofReal (Real.log n) := by
    calc
      _ ≤ ∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal x⁻¹ := by
        exact setLIntegral_mono' measurableSet_Ioc fun x hx ↦
          ENNReal.ofReal_le_ofReal (pairLaplaceClosed_le_inv (zero_lt_one.trans hx.1))
      _ = ENNReal.ofReal (∫ x in Ioc (1 : ℝ) n, x⁻¹) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hinv
          ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx ↦
            inv_nonneg.mpr (zero_le_one.trans hx.1.le)))
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hn', integral_inv_of_pos zero_lt_one
          (zero_lt_one.trans_le hn'), div_one]
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioc 1 n) :=
    Set.disjoint_left.mpr fun _ h₁ h₂ ↦ (not_lt_of_ge h₁.2) h₂.1
  calc
    _ = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (pairLaplaceClosed x)) +
          ∫⁻ x in Ioc (1 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x) := by
      rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hn',
        lintegral_union measurableSet_Ioc hdisj]
    _ ≤ 1 + ENNReal.ofReal (Real.log n) := add_le_add hlow hhigh
    _ = _ := by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hlog]

private theorem intervalIntegral_beta_nat (i j : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ i * (1 - x) ^ j) =
      ((i.factorial : ℝ) * j.factorial) / (i + j + 1).factorial := by
  have hu : 0 < (((i : ℂ) + 1).re) := by simp; positivity
  have hv : 0 < (((j : ℂ) + 1).re) := by simp; positivity
  have hsum : ((i : ℂ) + 1) + ((j : ℂ) + 1) = ((i + j + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  have hc := Complex.betaIntegral_eq_Gamma_mul_div ((i : ℂ) + 1) ((j : ℂ) + 1) hu hv
  rw [hsum] at hc
  simp only [Complex.Gamma_nat_eq_factorial, Complex.betaIntegral, add_sub_cancel_right,
    Complex.cpow_natCast] at hc
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using hc

/-- Ordinary beta density with integer parameters k and n - k. -/
noncomputable def pairBetaDensity (n k : ℕ) (s : ℝ) : ℝ :=
  s ^ (k - 1) * (1 - s) ^ (n - k - 1)

private theorem measurable_pairBetaDensity (n k : ℕ) : Measurable (pairBetaDensity n k) := by
  unfold pairBetaDensity
  fun_prop

/-- Integration of the integer beta density gives its factorial value. -/
theorem lintegral_pairBetaDensity (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (pairBetaDensity n k s)) =
      ENNReal.ofReal (pairSizeBetaFactor n k) := by
  have hi : IntegrableOn (pairBetaDensity n k) (Ioo 0 1) := by
    have hc : Continuous (pairBetaDensity n k) := by unfold pairBetaDensity; fun_prop
    exact hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    unfold pairBetaDensity pairSizeBetaFactor
    rw [intervalIntegral_beta_nat, show k - 1 + (n - k - 1) + 1 = n - 1 by omega]
  · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs ↦
      mul_nonneg (pow_nonneg hs.1.le _) (pow_nonneg (sub_nonneg.mpr hs.2.le) _))

private theorem map_restrict_Ioo_div {x : ℝ} (hx : 0 < x) :
    (volume.restrict (Ioo (0 : ℝ) x)).map (x⁻¹ * ·) =
      ENNReal.ofReal x • volume.restrict (Ioo (0 : ℝ) 1) := by
  have hpre : (x⁻¹ * ·) ⁻¹' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) x := by
    ext y
    change (0 < x⁻¹ * y ∧ x⁻¹ * y < 1) ↔ 0 < y ∧ y < x
    rw [← div_eq_inv_mul, div_lt_one hx]
    have hpos : 0 < y / x ↔ 0 < y := by
      rw [lt_div_iff₀ hx, zero_mul]
    rw [hpos]
  calc
    _ = ((volume : Measure ℝ).map (x⁻¹ * ·)).restrict (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_map (measurable_const_mul _) measurableSet_Ioo, hpre]
    _ = _ := by
      rw [Real.map_volume_mul_left (inv_ne_zero hx.ne'), inv_inv, abs_of_pos hx,
        Measure.restrict_smul]

private noncomputable def pairBetaDilation (n k : ℕ) (x : ℝ) : ℝ → ℝ≥0∞ :=
  (Ioo 0 x).indicator (fun y ↦ ENNReal.ofReal (x⁻¹ * pairBetaDensity n k (x⁻¹ * y)))

private theorem measurable_pairBetaDilation (n k : ℕ) (x : ℝ) :
    Measurable (pairBetaDilation n k x) := by
  unfold pairBetaDilation
  refine Measurable.indicator ?_ measurableSet_Ioo
  unfold pairBetaDensity
  fun_prop

private theorem lintegral_pairBetaDilation {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {x : ℝ} (hx : 0 < x) :
    (∫⁻ y, pairBetaDilation n k x y) = ENNReal.ofReal (pairSizeBetaFactor n k) := by
  have hf : Measurable (fun s ↦ ENNReal.ofReal (pairBetaDensity n k s)) :=
    (measurable_pairBetaDensity n k).ennreal_ofReal
  have hcomp : Measurable (fun y ↦ ENNReal.ofReal (pairBetaDensity n k (x⁻¹ * y))) :=
    hf.comp (measurable_const_mul _)
  rw [pairBetaDilation, lintegral_indicator measurableSet_Ioo]
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr hx.le)]
  rw [lintegral_const_mul _ hcomp]
  rw [← lintegral_map hf (measurable_const_mul x⁻¹), map_restrict_Ioo_div hx,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hx.le), inv_mul_cancel₀ hx.ne', ENNReal.ofReal_one,
    one_mul, lintegral_pairBetaDensity n k hk hkn]

private theorem lintegral_rotate_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (μ ν ρ : Measure ℝ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    (∫⁻ y, ∫⁻ z, ∫⁻ x, F (x, y, z) ∂μ ∂ρ ∂ν) =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, F (x, y, z) ∂ρ ∂ν ∂μ := by
  have hpair : Measurable (fun q : (ℝ × ℝ) × ℝ ↦ F (q.2, q.1)) :=
    hF.comp (measurable_snd.prodMk measurable_fst)
  have hinner : Measurable (fun q : ℝ × ℝ ↦ ∫⁻ x, F (x, q) ∂μ) :=
    hpair.lintegral_prod_right'
  calc
    _ = ∫⁻ q : ℝ × ℝ, (∫⁻ x, F (x, q) ∂μ) ∂ν.prod ρ :=
      (lintegral_prod _ hinner.aemeasurable).symm
    _ = ∫⁻ x, ∫⁻ q : ℝ × ℝ, F (x, q) ∂ν.prod ρ ∂μ :=
      lintegral_lintegral_swap hpair.aemeasurable
    _ = _ := by
      refine lintegral_congr fun x ↦ lintegral_prod _ ?_
      exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable

private theorem lintegral_translate_triple {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y : ℝ, ∫⁻ z : ℝ, ∫⁻ w : ℝ, F (w + (y + z), y, z)) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, F (x, y, z) := by
  rw [← lintegral_rotate_triple hF volume volume volume]
  refine lintegral_congr fun y ↦ lintegral_congr fun z ↦ ?_
  exact lintegral_add_right_eq_self (fun x : ℝ ↦ F (x, y, z)) (y + z)

/-- The three-sum kernel after inserting the power densities of the score sums.
Its external factorial normalizers are not included. -/
noncomputable def twoStableClosedLaplaceAggregateKernel (n u v : ℕ) (w y z : ℝ) : ℝ :=
  pairLaplaceClosed (w + (y + z)) ^ n * pairLaplaceClosed (w + z) ^ u *
    pairLaplaceClosed (w + y) ^ v * (w ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1))

private theorem scaled_pairBetaDensity_eq {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x⁻¹ * pairBetaDensity n k (x⁻¹ * y) =
      y ^ (k - 1) * (x - y) ^ (n - k - 1) / x ^ (n - 1) := by
  have hdiv : 1 - x⁻¹ * y = (x - y) / x := by
    rw [← div_eq_inv_mul, sub_div, div_self hx.ne']
  unfold pairBetaDensity
  rw [hdiv, mul_pow, inv_pow, div_pow]
  calc
    _ = y ^ (k - 1) * (x - y) ^ (n - k - 1) / (x * (x ^ (k - 1) * x ^ (n - k - 1))) := by
      field_simp
    _ = _ := by
      rw [← pow_add, ← pow_succ', show k - 1 + (n - k - 1) + 1 = n - 1 by omega]

private theorem twoStableClosedLaplaceAggregateKernel_le_beta {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) {x y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hxyz : y + z < x) :
    twoStableClosedLaplaceAggregateKernel n u v (x - (y + z)) y z ≤
      pairLaplaceClosed x * (x⁻¹ * pairBetaDensity n u (x⁻¹ * y)) *
        (x⁻¹ * pairBetaDensity n v (x⁻¹ * z)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hun : u < n := by omega
  have hvn : v < n := by omega
  have hn : 1 ≤ n := by omega
  have hx : 0 < x := by linarith
  have hxy : 0 < x - y := by linarith
  have hxz : 0 < x - z := by linarith
  have htriangle : 0 ≤ x - (y + z) := (sub_pos.mpr hxyz).le
  have htriangle' : x - (y + z) ≤ (x - y) * (x - z) / x := by
    apply (le_div_iff₀ hx).2
    nlinarith only [mul_nonneg hy.le hz.le]
  have hφ := pairLaplaceClosed_nonneg hx
  have hφyn := pairLaplaceClosed_nonneg hxy
  have hφzn := pairLaplaceClosed_nonneg hxz
  have hφx : pairLaplaceClosed x ^ n ≤ pairLaplaceClosed x * x⁻¹ ^ (n - 1) := calc
    _ = pairLaplaceClosed x * pairLaplaceClosed x ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hφ (pairLaplaceClosed_le_inv hx) _) hφ
  have hφy := pow_le_pow_left₀ hφyn (pairLaplaceClosed_le_inv hxy) u
  have hφz := pow_le_pow_left₀ hφzn (pairLaplaceClosed_le_inv hxz) v
  have hβu : (x - y) ^ (n - 1) = (x - y) ^ u * (x - y) ^ (n - u - 1) := by
    rw [← pow_add, show u + (n - u - 1) = n - 1 by omega]
  have hβv : (x - z) ^ (n - 1) = (x - z) ^ v * (x - z) ^ (n - v - 1) := by
    rw [← pow_add, show v + (n - v - 1) = n - 1 by omega]
  unfold twoStableClosedLaplaceAggregateKernel
  rw [sub_add_cancel, show x - (y + z) + z = x - y by ring,
    show x - (y + z) + y = x - z by ring]
  calc
    _ ≤ (pairLaplaceClosed x * x⁻¹ ^ (n - 1) * (x - y)⁻¹ ^ u * (x - z)⁻¹ ^ v) *
          ((x - (y + z)) ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1)) := by
      gcongr
    _ ≤ (pairLaplaceClosed x * x⁻¹ ^ (n - 1) * (x - y)⁻¹ ^ u * (x - z)⁻¹ ^ v) *
          (((x - y) * (x - z) / x) ^ (n - 1) * y ^ (u - 1) * z ^ (v - 1)) := by
      gcongr
    _ = _ := by
      rw [scaled_pairBetaDensity_eq hup hun hx, scaled_pairBetaDensity_eq hvp hvn hx,
        div_pow, mul_pow, hβu, hβv]
      simp only [inv_pow]
      field_simp

private def translatedPairDomain (N : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.1 + p.2.2 < p.1 ∧ p.1 ≤ N}

private theorem measurableSet_translatedPairDomain (N : ℝ) :
    MeasurableSet (translatedPairDomain N) := by
  have hy : Measurable (fun p : ℝ × ℝ × ℝ ↦ p.2.1) := by fun_prop
  have hz : Measurable (fun p : ℝ × ℝ × ℝ ↦ p.2.2) := by fun_prop
  exact (measurableSet_lt measurable_const hy).inter
    ((measurableSet_lt measurable_const hz).inter
      ((measurableSet_lt (hy.add hz) measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)))

private noncomputable def translatedPairKernel (n u v : ℕ) : ℝ × ℝ × ℝ → ℝ≥0∞ :=
  (translatedPairDomain n).indicator fun p ↦ ENNReal.ofReal
    (twoStableClosedLaplaceAggregateKernel n u v (p.1 - (p.2.1 + p.2.2)) p.2.1 p.2.2)

private theorem measurable_translatedPairKernel (n u v : ℕ) :
    Measurable (translatedPairKernel n u v) := by
  unfold translatedPairKernel twoStableClosedLaplaceAggregateKernel
  refine Measurable.indicator ?_ (measurableSet_translatedPairDomain n)
  unfold pairLaplaceClosed
  fun_prop

private theorem translatedPairKernel_eval (n u v : ℕ) (w y z : ℝ) :
    translatedPairKernel n u v (w + (y + z), y, z) =
      if 0 < y ∧ 0 < z ∧ 0 < w ∧ w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0 := by
  have htri : y + z < w + (y + z) ↔ 0 < w := by
    constructor <;> intro hh <;> linarith
  simp [translatedPairKernel, translatedPairDomain, indicator_apply, htri]

private theorem lintegral_closedLaplace_eq_translated (n u v : ℕ) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ),
      if w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ, translatedPairKernel n u v (x, y, z) := by
  rw [← lintegral_translate_triple (measurable_translatedPairKernel n u v)]
  simp_rw [← lintegral_indicator measurableSet_Ioi, indicator_apply, mem_Ioi,
    translatedPairKernel_eval]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : 0 < y
  · simp only [hy, ite_true, true_and]
    refine lintegral_congr fun z ↦ ?_
    by_cases hz : 0 < z
    · simp only [hz, ite_true, true_and]
      refine lintegral_congr fun w ↦ ?_
      by_cases hw : 0 < w <;> simp [hw]
    · simp [hz]
  · simp [hy]

private noncomputable def pairRadialFactor (n : ℕ) : ℝ → ℝ≥0∞ :=
  (Ioc (0 : ℝ) n).indicator (fun x ↦ ENNReal.ofReal (pairLaplaceClosed x))

private theorem measurable_pairRadialFactor (n : ℕ) : Measurable (pairRadialFactor n) :=
  measurable_pairLaplaceClosed.ennreal_ofReal.indicator measurableSet_Ioc

private theorem translatedPairKernel_le {n u v : ℕ} (h : ValidPairSizes n (u, v))
    (x y z : ℝ) :
    translatedPairKernel n u v (x, y, z) ≤
      (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z := by
  by_cases hp : (x, y, z) ∈ translatedPairDomain n
  · have hp' := hp
    obtain ⟨hy, hz, htri, hn⟩ := hp'
    change 0 < y at hy
    change 0 < z at hz
    change y + z < x at htri
    have hx : 0 < x := by linarith
    have hyx : 0 < x - y := by linarith
    have hxD : x ∈ Ioc (0 : ℝ) n := ⟨hx, hn⟩
    have hyD : y ∈ Ioo 0 x := ⟨hy, by linarith⟩
    have hzD : z ∈ Ioo 0 x := ⟨hz, by linarith⟩
    have hφ := pairLaplaceClosed_nonneg hx
    have hβ : 0 ≤ x⁻¹ * pairBetaDensity n u (x⁻¹ * y) := by
      rw [scaled_pairBetaDensity_eq
        (show 0 < u by obtain ⟨hu, hv, huv⟩ := h; omega)
        (show u < n by obtain ⟨hu, hv, huv⟩ := h; omega) hx]
      positivity
    rw [translatedPairKernel, indicator_of_mem hp, pairRadialFactor, indicator_of_mem hxD,
      pairBetaDilation, pairBetaDilation, indicator_of_mem hyD, indicator_of_mem hzD,
      ← ENNReal.ofReal_mul hφ, ← ENNReal.ofReal_mul (mul_nonneg hφ hβ)]
    exact ENNReal.ofReal_le_ofReal
      (twoStableClosedLaplaceAggregateKernel_le_beta h hy hz htri)
  · rw [translatedPairKernel, indicator_of_notMem hp]
    exact zero_le

private theorem lintegral_pairRadialDilation {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
      (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z) =
    (∫⁻ x in Ioc (0 : ℝ) n, ENNReal.ofReal (pairLaplaceClosed x)) *
      ENNReal.ofReal (pairSizeBetaFactor n u) * ENNReal.ofReal (pairSizeBetaFactor n v) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hup : 0 < u := by omega
  have hvp : 0 < v := by omega
  have hun : u < n := by omega
  have hvn : v < n := by omega
  have houter (x : ℝ) :
      (∫⁻ y : ℝ, ∫⁻ z : ℝ,
        (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z) =
      pairRadialFactor n x * ENNReal.ofReal (pairSizeBetaFactor n u) *
        ENNReal.ofReal (pairSizeBetaFactor n v) := by
    by_cases hx : x ∈ Ioc (0 : ℝ) n
    · have hm : Measurable (fun y ↦ pairRadialFactor n x * pairBetaDilation n u x y) :=
        measurable_const.mul (measurable_pairBetaDilation n u x)
      simp_rw [lintegral_const_mul _ (measurable_pairBetaDilation n v x),
        lintegral_pairBetaDilation hvp hvn hx.1]
      rw [lintegral_mul_const _ hm, lintegral_const_mul _ (measurable_pairBetaDilation n u x),
        lintegral_pairBetaDilation hup hun hx.1]
    · have hz : pairRadialFactor n x = 0 := indicator_of_notMem hx _
      simp [hz]
  simp_rw [houter]
  rw [lintegral_mul_const _ ((measurable_pairRadialFactor n).mul_const _),
    lintegral_mul_const _ (measurable_pairRadialFactor n), pairRadialFactor,
    lintegral_indicator measurableSet_Ioc]

/-- The three-sum upper integral is at most the product of the two beta factors
and one logarithmic term. Only the positive score-sum domain contributes. -/
theorem lintegral_twoStableClosedLaplaceAggregate_le {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ z in Ioi (0 : ℝ), ∫⁻ w in Ioi (0 : ℝ),
      if w + (y + z) ≤ n then
        ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z) else 0) ≤
      ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v) := by
  have hn : 1 ≤ n := by obtain ⟨hu, hv, huv⟩ := h; omega
  have hlog : 0 ≤ 1 + Real.log (n : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn))
  have hbu : 0 ≤ pairSizeBetaFactor n u := by unfold pairSizeBetaFactor; positivity
  rw [lintegral_closedLaplace_eq_translated]
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ z : ℝ,
          (pairRadialFactor n x * pairBetaDilation n u x y) * pairBetaDilation n v x z :=
      lintegral_mono fun x ↦ lintegral_mono fun y ↦ lintegral_mono (translatedPairKernel_le h x y)
    _ = _ := lintegral_pairRadialDilation h
    _ ≤ (ENNReal.ofReal (1 + Real.log n) * ENNReal.ofReal (pairSizeBetaFactor n u)) *
          ENNReal.ofReal (pairSizeBetaFactor n v) := by
      gcongr
      exact lintegral_pairLaplaceClosed_le n hn
    _ = _ := by rw [← ENNReal.ofReal_mul hlog, ← ENNReal.ofReal_mul (mul_nonneg hlog hbu)]

private theorem lintegral_triple_prod {F : ℝ × ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    (μ ν ρ : Measure ℝ) [SFinite ν] [SFinite ρ] :
    (∫⁻ p, F p ∂μ.prod (ν.prod ρ)) =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, F (x, y, z) ∂ρ ∂ν ∂μ := by
  rw [lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun x ↦ lintegral_prod _ ?_
  exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- The normalized three-sum bound for the radial laws of the three score groups. -/
theorem lintegral_twoStableClosedLaplaceRadial_le {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    (∫⁻ w, ∫⁻ y, ∫⁻ z, (if w + y + z ≤ n then ENNReal.ofReal
        (pairLaplaceClosed (w + y + z) ^ n * pairLaplaceClosed (w + z) ^ u *
          pairLaplaceClosed (w + y) ^ v) else 0)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n) ≤
      ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v /
        ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  let R := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  let F (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if p.1 + p.2.1 + p.2.2 ≤ n then ENNReal.ofReal
      (pairLaplaceClosed (p.1 + p.2.1 + p.2.2) ^ n * pairLaplaceClosed (p.1 + p.2.2) ^ u *
        pairLaplaceClosed (p.1 + p.2.1) ^ v) else 0
  let G (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if p.1 + (p.2.1 + p.2.2) ≤ n then ENNReal.ofReal
      (twoStableClosedLaplaceAggregateKernel n u v p.1 p.2.1 p.2.2) else 0
  let D (k : ℕ) (s : ℝ) : ℝ := s ^ (k - 1) / ↑(k - 1).factorial
  let ρ (k : ℕ) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (D k s)
  let H (p : ℝ × ℝ × ℝ) : ℝ≥0∞ := ρ n p.1 * (ρ u p.2.1 * ρ v p.2.2)
  let C : ℝ := ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : Measurable F := by
    dsimp [F]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    unfold pairLaplaceClosed
    fun_prop
  have hG : Measurable G := by
    dsimp [G]
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    unfold twoStableClosedLaplaceAggregateKernel pairLaplaceClosed
    fun_prop
  have hρ (k : ℕ) : Measurable (ρ k) := by
    dsimp [ρ, D]
    fun_prop
  have hH : Measurable H :=
    ((hρ n).comp measurable_fst).mul
      (((hρ u).comp (measurable_fst.comp measurable_snd)).mul
        ((hρ v).comp (measurable_snd.comp measurable_snd)))
  have hmeasure :
      (spouseRadialLaw n).prod ((spouseRadialLaw u).prod (spouseRadialLaw v)) =
        (R.prod (R.prod R)).withDensity H := by
    change (R.withDensity (ρ n)).prod ((R.withDensity (ρ u)).prod (R.withDensity (ρ v))) = _
    have hinner : Measurable (fun p : ℝ × ℝ ↦ ρ u p.1 * ρ v p.2) :=
      ((hρ u).comp measurable_fst).mul ((hρ v).comp measurable_snd)
    rw [prod_withDensity (hρ u) (hρ v), prod_withDensity (hρ n) hinner]
  have hpoint (w y z : ℝ) (hw : 0 < w) (hy : 0 < y) (hz : 0 < z) :
      (H * F) (w, y, z) = ENNReal.ofReal C * G (w, y, z) := by
    by_cases hcut : w + (y + z) ≤ n
    · have hcut' : w + y + z ≤ n := by simpa only [add_assoc] using hcut
      let P := pairLaplaceClosed (w + y + z) ^ n * pairLaplaceClosed (w + z) ^ u *
        pairLaplaceClosed (w + y) ^ v
      have hwn : 0 ≤ D n w := by dsimp [D]; positivity
      have hyn : 0 ≤ D u y := by dsimp [D]; positivity
      have hzn : 0 ≤ D v z := by dsimp [D]; positivity
      simp only [Pi.mul_apply, H, F, G, hcut, hcut', ite_true]
      change (ENNReal.ofReal (D n w) * (ENNReal.ofReal (D u y) * ENNReal.ofReal (D v z))) *
          ENNReal.ofReal P = ENNReal.ofReal C *
            ENNReal.ofReal (twoStableClosedLaplaceAggregateKernel n u v w y z)
      rw [← ENNReal.ofReal_mul hyn, ← ENNReal.ofReal_mul hwn,
        ← ENNReal.ofReal_mul (mul_nonneg hwn (mul_nonneg hyn hzn)), ← ENNReal.ofReal_mul hC]
      congr 1
      dsimp [D, C, P, twoStableClosedLaplaceAggregateKernel]
      rw [add_assoc]
      ring
    · have hcut' : ¬w + y + z ≤ n := by simpa only [add_assoc] using hcut
      simp [F, G, hcut, hcut']
  change (∫⁻ w, ∫⁻ y, ∫⁻ z, F (w, y, z) ∂spouseRadialLaw v ∂spouseRadialLaw u
    ∂spouseRadialLaw n) ≤ _
  calc
    _ = ∫⁻ p, F p ∂(spouseRadialLaw n).prod ((spouseRadialLaw u).prod (spouseRadialLaw v)) :=
      (lintegral_triple_prod hF _ _ _).symm
    _ = ∫⁻ p, (H * F) p ∂R.prod (R.prod R) := by
      rw [hmeasure, lintegral_withDensity_eq_lintegral_mul _ hH hF]
    _ = ∫⁻ w, ∫⁻ y, ∫⁻ z, (H * F) (w, y, z) ∂R ∂R ∂R := by
      exact lintegral_triple_prod (hH.mul hF) R R R
    _ = ∫⁻ w, ∫⁻ y, ∫⁻ z, ENNReal.ofReal C * G (w, y, z) ∂R ∂R ∂R := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun w hw ↦ ?_
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      exact setLIntegral_congr_fun measurableSet_Ioi fun z hz ↦ hpoint w y z hw hy hz
    _ = ENNReal.ofReal C * (∫⁻ w, ∫⁻ y, ∫⁻ z, G (w, y, z) ∂R ∂R ∂R) := by
      simp_rw [lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal C * (∫⁻ y, ∫⁻ z, ∫⁻ w, G (w, y, z) ∂R ∂R ∂R) := by
      rw [lintegral_rotate_triple hG R R R]
    _ ≤ ENNReal.ofReal C *
        ENNReal.ofReal ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v) := by
      gcongr
      exact lintegral_twoStableClosedLaplaceAggregate_le h
    _ = _ := by rw [← ENNReal.ofReal_mul hC, div_eq_inv_mul]

end LennonPittelFormalization

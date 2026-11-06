module

public import LennonPittel.PittelMeanTail
public import LennonPittel.PittelRowsProduct
public import LennonPittel.PittelSimplexMoments

/-!
# Pittel's first-moment asymptotic

The fixed-matching integral separates into the total score and the score shares.
The angular row product tends to `exp (-1)` on the typical region. The radial
factor is proportional to `1 / s`, giving the logarithmic growth.

Source: Boris Pittel, *The Average Number of Stable Matchings* (1989),
Theorem 1, https://doi.org/10.1137/0402048.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private theorem pittelRowMass_scale {ι : Type*} (I : Finset ι) (w : ι → ℝ) {s : ℝ}
    (hs : 0 < s) :
    scoreRowMass I (fun j ↦ s * w j) 0 1 = s⁻¹ * scoreRowMass I w 0 s := by
  unfold scoreRowMass
  convert intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := 1)
    (scoreRowKernel I w) hs.ne' using 1
  · congr 1
    funext t
    unfold scoreRowKernel
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    ring
  · simp

private theorem pittel_eventual_log_ge (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C

private theorem pittel_bulk_bounds {n : ℕ} (hn : 1 < n) (hlog : 12 ≤ Real.log n)
    {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ (n : ℝ) / (Real.log n) ^ 2)
    {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hmax : ∀ i, w i ≤ 12 * Real.log n / n) :
    ∀ i, s * w i ∈ Icc (0 : ℝ) 1 := by
  intro i
  refine ⟨mul_nonneg hs (hw i), ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 < Real.log n := by linarith
  calc
    s * w i ≤ ((n : ℝ) / (Real.log n) ^ 2) * (12 * Real.log n / n) :=
      mul_le_mul hu (hmax i) (hw i) (by positivity)
    _ = 12 / Real.log n := by field_simp
    _ ≤ 1 := (div_le_one hl).2 hlog

private theorem pittel_eventual_bulk_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ {s : ℝ}, 0 ≤ s → s ≤ (n : ℝ) / (Real.log n)^2 →
      ∀ {w : Fin n → ℝ}, (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ 12 * Real.log n / n) → ∀ i, s * w i ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℕ), pittel_eventual_log_ge 12] with n hn hlog
  exact pittel_bulk_bounds hn hlog

private theorem pittel_lintegral_radial_weight {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C) :
    (n.factorial : ℝ≥0∞) *
        (∫⁻ s in Ioc l u, ENNReal.ofReal (C / s ^ n)
          ∂spouseRadialLaw n) =
      ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) := by
  have hd : Measurable (fun s : ℝ ↦
      ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))) := by fun_prop
  have hg : Measurable (fun s : ℝ ↦ ENNReal.ofReal (C / s ^ n)) := by fun_prop
  rw [spouseRadialLaw, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hg measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc l u ⊆ Ioi 0 from fun s hs ↦ hl.trans hs.1),
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n.factorial)]
  calc
    _ = ∫⁻ s in Ioc l u, ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc l u))]
        with s hs
      have hs' : 0 < s := hl.trans hs.1
      have hf : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
      have hnat := Nat.factorial_succ (n - 1)
      rw [show n - 1 + 1 = n by omega] at hnat
      have hnfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
        exact_mod_cast hnat
      change (n.factorial : ℝ≥0∞) *
          (ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ)) *
            ENNReal.ofReal (C / s ^ n)) =
        ENNReal.ofReal ((n : ℝ) * C) * ENNReal.ofReal s⁻¹
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hnfac]
      congr 1
      rw [← show n - 1 + 1 = n by omega, pow_succ s (n - 1)]
      field_simp
      simp [mul_comm]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_inv_of_pos hl hlu,
        ← ENNReal.ofReal_mul (by positivity)]

private noncomputable def pittelWindowMass (n : ℕ) (A : Set ℝ) : ℝ≥0∞ :=
  (n.factorial : ℝ≥0∞) * ∫⁻ y in {y | spouseVectorTotal y ∈ A}, pittelDensity n y

private theorem measurable_pittelTotal (n : ℕ) : Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

private theorem pittelTotal_scale {n : ℕ} {w : Fin n → ℝ} (hw : ∑ i, w i = 1) (s : ℝ) :
    spouseVectorTotal (fun i ↦ s * w i) = s := by
  simp only [spouseVectorTotal, ← Finset.mul_sum, hw, mul_one]

private theorem pittelWindowMass_le_mean (n : ℕ) (A : Set ℝ) :
    pittelWindowMass n A ≤ ENNReal.ofReal (expectedNumStableMatchings n) := by
  rw [ofReal_expectedNumStableMatchings_eq_pittelDensity, pittelWindowMass]
  exact mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _

private theorem pittelMean_eq_small_add_bulk (n : ℕ) (L : ℝ) :
    ENNReal.ofReal (expectedNumStableMatchings n) =
      pittelWindowMass n (Iic L) + pittelWindowMass n (Ioc L (n : ℝ)) := by
  have ha : MeasurableSet {y : Fin n → ℝ | spouseVectorTotal y ∈ Iic L} :=
    measurableSet_Iic.preimage (measurable_pittelTotal n)
  have hb : MeasurableSet {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc L (n : ℝ)} :=
    measurableSet_Ioc.preimage (measurable_pittelTotal n)
  rw [ofReal_expectedNumStableMatchings_eq_pittelDensity, ← lintegral_add_compl _ ha,
    mul_add, pittelWindowMass, pittelWindowMass]
  congr 2
  rw [← lintegral_indicator ha.compl, ← lintegral_indicator hb]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ pittelScoreCube n
  · have hle : spouseVectorTotal y ≤ (n : ℝ) := by
      calc
        spouseVectorTotal y ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ (hy i (mem_univ i)).2
        _ = _ := by simp
    have heq : y ∈ {y : Fin n → ℝ | spouseVectorTotal y ∈ Iic L}ᶜ ↔
        y ∈ {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc L (n : ℝ)} := by
      simp [not_le, hle]
    by_cases h : y ∈ {y : Fin n → ℝ | spouseVectorTotal y ∈ Iic L}ᶜ
    · rw [indicator_of_mem h, indicator_of_mem (heq.mp h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (heq.not.mp h)]
  · have hz : pittelDensity n y = 0 := indicator_of_notMem hy _
    simp only [Set.indicator_apply, hz, ite_self]

private theorem pittelDensity_scale {n : ℕ} {s : ℝ} (hs : 0 < s) {w : Fin n → ℝ}
    (hy : ∀ j, s * w j ∈ Icc (0 : ℝ) 1) :
    pittelDensity n (fun j ↦ s * w j) =
      ENNReal.ofReal ((∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s) / s ^ n) := by
  rw [pittelDensity_eq_ofReal_prod hy]
  simp_rw [pittelRowMass_scale _ _ hs]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    inv_pow, div_eq_inv_mul]

private theorem pittel_angular_integral_le {n : ℕ} (ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure ν] {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {s C : ℝ}
    (hs : 2 ≤ s) (hC : 0 ≤ C)
    (hν : ∀ᵐ w ∂ν, ∑ i, w i = 1)
    (hrow : ∀ w ∈ B, (∀ j, s * w j ∈ Icc (0 : ℝ) 1) →
      (∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s) ≤ C) :
    (∫⁻ w, pittelDensity n (fun j ↦ s * w j) ∂ν) ≤
      ENNReal.ofReal ((C + Real.exp 2 * (ν Bᶜ).toReal) / s ^ n) := by
  have hp : 0 < s := by linarith
  have hpow : 0 < s ^ n := pow_pos hp _
  rw [← lintegral_add_compl _ hB]
  have h₁ : (∫⁻ w in B, pittelDensity n (fun j ↦ s * w j) ∂ν) ≤
      ENNReal.ofReal (C / s ^ n) := by
    calc
      _ ≤ ∫⁻ _w in B, ENNReal.ofReal (C / s ^ n) ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (μ := ν) hB] with w hw
        by_cases hy : (fun j ↦ s * w j) ∈ pittelScoreCube n
        · have hc (j : Fin n) : s * w j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ _)
          rw [pittelDensity_scale hp hc]
          exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hrow w hw hc) hpow.le)
        · simp [pittelDensity, indicator_of_notMem hy]
      _ = ENNReal.ofReal (C / s ^ n) * ν B := setLIntegral_const _ _
      _ ≤ _ := mul_le_of_le_one_right' (prob_le_one (μ := ν))
  have h₂ : (∫⁻ w in Bᶜ, pittelDensity n (fun j ↦ s * w j) ∂ν) ≤
      ENNReal.ofReal (Real.exp 2 / s ^ n) * ν Bᶜ := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hν] with w hw
    have ht := pittelTotal_scale hw s
    have htotal : 2 ≤ spouseVectorTotal (fun j ↦ s * w j) := by rwa [ht]
    simpa only [ht] using pittelDensity_le_inv_pow htotal
  calc
    _ ≤ ENNReal.ofReal (C / s ^ n) + ENNReal.ofReal (Real.exp 2 / s ^ n) * ν Bᶜ :=
      add_le_add h₁ h₂
    _ = _ := by
      conv_lhs =>
        rw [← ENNReal.ofReal_toReal (measure_ne_top ν Bᶜ),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem pittel_angular_integral_ge {n : ℕ} (ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure ν] {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {s C : ℝ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hrow : ∀ w ∈ B, (∀ j, s * w j ∈ Icc (0 : ℝ) 1) ∧
      C ≤ (∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s)) :
    ENNReal.ofReal ((C * (ν B).toReal) / s ^ n) ≤
      ∫⁻ w, pittelDensity n (fun j ↦ s * w j) ∂ν := by
  calc
    _ = ENNReal.ofReal (C / s ^ n) * ν B := by
      conv_rhs => rw [← ENNReal.ofReal_toReal (measure_ne_top ν B),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ∫⁻ _w in B, ENNReal.ofReal (C / s ^ n) ∂ν := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in B, pittelDensity n (fun j ↦ s * w j) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := ν) hB] with w hw
      obtain ⟨hc, hq⟩ := hrow w hw
      rw [pittelDensity_scale hs hc]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hq (by positivity))
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

private theorem pittelWindowMass_eq_radial {n : ℕ} (hn : 0 < n) {A : Set ℝ}
    (hA : MeasurableSet A) :
    pittelWindowMass n A =
      (n.factorial : ℝ≥0∞) *
        ∫⁻ s in A, ∫⁻ w, pittelDensity n (fun i ↦ s * w i) ∂spouseAngularLaw n
          ∂spouseRadialLaw n := by
  let B : Set (Fin n → ℝ) := {y | spouseVectorTotal y ∈ A}
  let Q : Set (Fin n → ℝ) := {y | ∀ i, 0 ≤ y i}
  have hB : MeasurableSet B := hA.preimage (measurable_pittelTotal n)
  have hQ : MeasurableSet Q := by
    change MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_le measurable_const (measurable_pi_apply i)
  let f := B.indicator (pittelDensity n)
  have hf : Measurable f := (measurable_pittelDensity n).indicator hB
  rw [pittelWindowMass, ← lintegral_indicator hB]
  congr 1
  change (∫⁻ y, f y) = _
  calc
    _ = ∫⁻ y, f y ∂(volume.restrict Q) := by
      rw [← lintegral_indicator hQ]
      apply lintegral_congr
      intro y
      by_cases h : y ∈ Q
      · rw [indicator_of_mem h]
      · have hc : y ∉ pittelScoreCube n := fun hc ↦ h (fun i ↦ (hc i (mem_univ i)).1)
        rw [indicator_of_notMem h]
        have hz : pittelDensity n y = 0 := indicator_of_notMem hc _
        change B.indicator (pittelDensity n) y = 0
        by_cases hy : y ∈ B
        · rw [indicator_of_mem hy, hz]
        · exact indicator_of_notMem hy _
    _ = ∫⁻ s, ∫⁻ w, f (fun i ↦ s * w i) ∂spouseAngularLaw n ∂spouseRadialLaw n :=
      lintegral_spouseRadialAngular hn hf
    _ = _ := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ A
      · rw [indicator_of_mem hs]
        apply lintegral_congr_ae
        filter_upwards [ae_spouseAngularLaw hn] with w hw
        exact indicator_of_mem (show (fun i ↦ s * w i) ∈ B by
          change spouseVectorTotal (fun i ↦ s * w i) ∈ A
          rwa [pittelTotal_scale hw.2]) _
      · rw [indicator_of_notMem hs, ← lintegral_zero]
        apply lintegral_congr_ae
        filter_upwards [ae_spouseAngularLaw hn] with w hw
        exact indicator_of_notMem (show (fun i ↦ s * w i) ∉ B by
          change spouseVectorTotal (fun i ↦ s * w i) ∉ A
          rwa [pittelTotal_scale hw.2]) _

private theorem pittelWindowMass_le_log {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C)
    (h : ∀ s ∈ Ioc l u,
      (∫⁻ w, pittelDensity n (fun i ↦ s * w i) ∂spouseAngularLaw n) ≤
        ENNReal.ofReal (C / s ^ n)) :
    pittelWindowMass n (Ioc l u) ≤ ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) := by
  rw [pittelWindowMass_eq_radial hn measurableSet_Ioc,
    ← pittel_lintegral_radial_weight hn hl hlu hC]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := spouseRadialLaw n) measurableSet_Ioc] with s hs
  exact h s hs

private theorem pittelWindowMass_ge_log {n : ℕ} (hn : 0 < n)
    {l u C : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hC : 0 ≤ C)
    (h : ∀ s ∈ Ioc l u, ENNReal.ofReal (C / s ^ n) ≤
      ∫⁻ w, pittelDensity n (fun i ↦ s * w i) ∂spouseAngularLaw n) :
    ENNReal.ofReal ((n : ℝ) * C * Real.log (u / l)) ≤ pittelWindowMass n (Ioc l u) := by
  rw [pittelWindowMass_eq_radial hn measurableSet_Ioc,
    ← pittel_lintegral_radial_weight hn hl hlu hC]
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := spouseRadialLaw n) measurableSet_Ioc] with s hs
  exact h s hs

private theorem pittel_ofReal_windowRatio {n : ℕ} (hn : 0 < n) (hl : 0 < Real.log n)
    (C W : ℝ) :
    ENNReal.ofReal ((n : ℝ) * C * W) / ENNReal.ofReal ((n : ℝ) * Real.log n) =
      ENNReal.ofReal (C * (W / Real.log n)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_div_of_pos (mul_pos hpos hl)]
  congr 1
  field_simp

private noncomputable def pittelNormalizer (n : ℕ) : ℝ := (n : ℝ) * Real.log n

private noncomputable def pittelSmallRatio (n : ℕ) : ℝ≥0∞ :=
  pittelWindowMass n (Iic (pittelRadiusLower n)) / ENNReal.ofReal (pittelNormalizer n)

private theorem pittelSmallRatio_ne_top {n : ℕ} (hn : 1 < n) : pittelSmallRatio n ≠ ⊤ := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < pittelNormalizer n := mul_pos (by positivity) (Real.log_pos hn')
  unfold pittelSmallRatio
  apply ENNReal.div_ne_top
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (pittelWindowMass_le_mean _ _)
  · exact (ENNReal.ofReal_pos.mpr hp).ne'

private theorem tendsto_pittelSmallRatio_toReal :
    Tendsto (fun n ↦ (pittelSmallRatio n).toReal) atTop (𝓝 0) := by
  have h : Tendsto pittelSmallRatio atTop (𝓝 0) := tendsto_pittelSmallMass_ratio_zero
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

private theorem pittelMean_sandwich {ε : ℝ} (hε : 0 < ε) (hε' : ε < (Real.exp 1)⁻¹) :
    ∃ lower upper : ℕ → ℝ,
      Tendsto lower atTop (𝓝 ((Real.exp 1)⁻¹ - ε)) ∧
      Tendsto upper atTop (𝓝 ((Real.exp 1)⁻¹ + ε)) ∧
      ∀ᶠ n in atTop, lower n ≤ expectedNumStableMatchings n / pittelNormalizer n ∧
        expectedNumStableMatchings n / pittelNormalizer n ≤ upper n := by
  obtain ⟨η, hη, hrows⟩ := eventually_pittelRowsProduct_close hε
  let c : ℝ := (Real.exp 1)⁻¹
  let B (n : ℕ) := pittelTypicalAngles n η
  let Clo (n : ℕ) := (c - ε) * (spouseAngularLaw n (B n)).toReal
  let Chi (n : ℕ) := c + ε + Real.exp 2 * (spouseAngularLaw n (B n)ᶜ).toReal
  let Wlo (n : ℕ) := Real.log (pittelRadiusUpper n / pittelRadiusLower n)
  let Whi (n : ℕ) := Real.log ((n : ℝ) / pittelRadiusLower n)
  refine ⟨fun n ↦ Clo n * (Wlo n / Real.log n),
    fun n ↦ (pittelSmallRatio n).toReal + Chi n * (Whi n / Real.log n), ?_, ?_, ?_⟩
  · have hC : Tendsto Clo atTop (𝓝 (c - ε)) := by
      simpa only [Clo, B, measureReal_def, mul_one] using
        (tendsto_probReal_pittelTypicalAngles_one hη).const_mul (c - ε)
    simpa only [Wlo, mul_one] using hC.mul tendsto_log_pittelWindowLower_ratio_one
  · have hC : Tendsto Chi atTop (𝓝 (c + ε)) := by
      simpa only [Chi, B, measureReal_def, mul_zero, add_zero] using
        ((tendsto_probReal_compl_pittelTypicalAngles_zero hη).const_mul
          (Real.exp 2)).const_add (c + ε)
    simpa only [Whi, mul_one, zero_add] using
      tendsto_pittelSmallRatio_toReal.add (hC.mul tendsto_log_pittelWindowUpper_ratio_one)
  filter_upwards [hrows, eventually_gt_atTop (1 : ℕ), eventually_two_le_pittelRadiusLower,
    eventually_pittelRadiusLower_le_upper, eventually_pittelRadiusUpper_le_size,
    pittel_eventual_bulk_bounds] with n hrow hn h2 hLU hUn hbulk
  have hn0 : 0 < n := by omega
  have hl : 0 < pittelRadiusLower n := by linarith
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hn'
  have hnorm : 0 < pittelNormalizer n := mul_pos (by positivity) hlog
  have hB : MeasurableSet (B n) := measurableSet_pittelTypicalAngles n η
  have hClo : 0 ≤ Clo n := mul_nonneg (sub_nonneg.mpr hε'.le) ENNReal.toReal_nonneg
  have hc : 0 < c := inv_pos.mpr (Real.exp_pos _)
  have hChi : 0 ≤ Chi n := by dsimp [Chi]; positivity
  have htotal : ∀ᵐ w ∂spouseAngularLaw n, ∑ i, w i = 1 :=
    (ae_spouseAngularLaw hn0).mono fun _ h ↦ h.2
  have hq (w : Fin n → ℝ) (hw : w ∈ B n) (s : ℝ) (hs : pittelRadiusLower n ≤ s)
      (hy : ∀ j, s * w j ∈ Icc (0 : ℝ) 1) :
      |(∏ i : Fin n, scoreRowMass (Finset.univ.erase i) w 0 s) - c| ≤ ε := by
    exact hrow w s hs hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 (fun j ↦ (hy j).2)
  have hupper :
      pittelWindowMass n (Ioc (pittelRadiusLower n) (n : ℝ)) ≤
        ENNReal.ofReal ((n : ℝ) * Chi n * Whi n) := by
    apply pittelWindowMass_le_log hn0 hl (hLU.trans hUn) hChi
    intro s hs
    apply pittel_angular_integral_le _ hB (h2.trans hs.1.le) (add_nonneg hc.le hε.le) htotal
    intro w hw hy
    have h := (abs_le.mp (hq w hw s hs.1.le hy)).2
    linarith only [h]
  have hlower :
      ENNReal.ofReal ((n : ℝ) * Clo n * Wlo n) ≤
        pittelWindowMass n (Ioc (pittelRadiusLower n) (pittelRadiusUpper n)) := by
    apply pittelWindowMass_ge_log hn0 hl hLU hClo
    intro s hs
    have hs' := hl.trans hs.1
    apply pittel_angular_integral_ge _ hB hs' (sub_nonneg.mpr hε'.le)
    intro w hw
    have hy := hbulk hs'.le hs.2 hw.1 hw.2.2.1
    refine ⟨hy, ?_⟩
    have h := (abs_le.mp (hq w hw s hs.1.le hy)).1
    linarith only [h]
  have hmean : 0 ≤ expectedNumStableMatchings n := integral_nonneg fun _ ↦ Nat.cast_nonneg _
  have hqmean := div_nonneg hmean hnorm.le
  have hhi : 0 ≤ Whi n / Real.log n := by
    apply div_nonneg _ hlog.le
    exact Real.log_nonneg ((one_le_div hl).2 (hLU.trans hUn))
  constructor
  · have hE := ENNReal.div_le_div_right
      (hlower.trans (pittelWindowMass_le_mean _ _)) (ENNReal.ofReal (pittelNormalizer n))
    rw [pittelNormalizer, pittel_ofReal_windowRatio hn0 hlog] at hE
    change _ ≤ ENNReal.ofReal (expectedNumStableMatchings n) /
      ENNReal.ofReal (pittelNormalizer n) at hE
    rw [← ENNReal.ofReal_div_of_pos hnorm] at hE
    exact (ENNReal.ofReal_le_ofReal_iff hqmean).mp hE
  · have hE : ENNReal.ofReal (expectedNumStableMatchings n / pittelNormalizer n) ≤
        pittelSmallRatio n + ENNReal.ofReal (Chi n * (Whi n / Real.log n)) := by
      rw [ENNReal.ofReal_div_of_pos hnorm,
        pittelMean_eq_small_add_bulk n (pittelRadiusLower n), ENNReal.add_div]
      apply add_le_add le_rfl
      exact (ENNReal.div_le_div_right hupper _).trans_eq
        (pittel_ofReal_windowRatio hn0 hlog _ _)
    have ht := pittelSmallRatio_ne_top hn
    have hR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ht, ENNReal.ofReal_ne_top⟩) hE
    simpa only [ENNReal.toReal_add ht ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hqmean,
      ENNReal.toReal_ofReal (mul_nonneg hChi hhi)] using hR

/-- Pittel's first-moment asymptotic in the balanced independent uniform preference model. -/
theorem tendsto_expectedNumStableMatchings_div_size_log :
    Tendsto (fun n : ℕ ↦ expectedNumStableMatchings n / ((n : ℝ) * Real.log n))
      atTop (𝓝 ((Real.exp 1)⁻¹)) := by
  let c : ℝ := (Real.exp 1)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.exp_pos _)
  change Tendsto (fun n : ℕ ↦ expectedNumStableMatchings n / pittelNormalizer n) atTop (𝓝 c)
  refine tendsto_order.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · let ε := min (c / 2) ((c - x) / 2)
    have hε : 0 < ε := lt_min (by positivity) (by linarith)
    have hε' : ε < c := (min_le_left _ _).trans_lt (by linarith)
    have hstrict : x < c - ε := by linarith [min_le_right (c / 2) ((c - x) / 2)]
    obtain ⟨lower, upper, hL, hU, hbounds⟩ := pittelMean_sandwich hε hε'
    filter_upwards [(tendsto_order.mp hL).1 x hstrict, hbounds] with n hn hb
    exact hn.trans_le hb.1
  · let ε := min (c / 2) ((x - c) / 2)
    have hε : 0 < ε := lt_min (by positivity) (by linarith)
    have hε' : ε < c := (min_le_left _ _).trans_lt (by linarith)
    have hstrict : c + ε < x := by linarith [min_le_right (c / 2) ((x - c) / 2)]
    obtain ⟨lower, upper, hL, hU, hbounds⟩ := pittelMean_sandwich hε hε'
    filter_upwards [(tendsto_order.mp hU).2 x hstrict, hbounds] with n hn hb
    exact hb.2.trans_lt hn

end LennonPittelFormalization

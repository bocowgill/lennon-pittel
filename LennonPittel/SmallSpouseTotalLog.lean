module

public import LennonPittel.CoexposureSpouseShells
public import LennonPittel.PittelSimplexRadial

/-!
# The small spouse-score total at a stable mark

Below the logarithmic transition the finite endpoint in each row integral
gives a strong loss. Radial integration cancels the power of the total in
the density, leaving only a polynomial prefactor.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

private theorem femaleSpouseStabilityDensity_le_smallCutoff {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ i, y i ∈ Icc (0 : ℝ) 1) {L : ℝ}
    (hY : 0 < spouseVectorTotal y) (hL : spouseVectorTotal y ≤ L) :
    femaleSpouseStabilityDensity y ≤ ENNReal.ofReal
      (Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L)) / spouseVectorTotal y ^ n) := by
  have hrow (i : Fin n) : 0 ≤ scoreRowMass (Finset.univ.erase i) y 0 1 := by
    unfold scoreRowMass
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht ↦ ?_
    unfold scoreRowKernel
    exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr
      ((mul_le_mul_of_nonneg_right ht.2 (hy j).1).trans (by simpa using (hy j).2))
  rw [femaleSpouseStabilityDensity, ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hrow i)]
  apply ENNReal.ofReal_le_ofReal
  let Y := spouseVectorTotal y
  have hq : 0 ≤ 1 - Real.exp (-Y) := sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hY.le))
  have hpow : (1 - Real.exp (-Y)) ^ n ≤ Real.exp (-(n : ℝ) * Real.exp (-L)) := calc
    _ ≤ (Real.exp (-(Real.exp (-Y)))) ^ n :=
      pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-(n : ℝ) * Real.exp (-Y)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (Real.exp_le_exp.mpr (neg_le_neg hL)) (neg_nonpos.mpr (Nat.cast_nonneg _)))
  calc
    _ ≤ Real.exp Y * ((1 - Real.exp (-Y)) / Y) ^ n := by
      simpa only [Y, spouseVectorTotal, Fintype.card_fin] using
        scoreRowMass_prod_le_finite_exp y hy hY
    _ = Real.exp Y * (1 - Real.exp (-Y)) ^ n / Y ^ n := by rw [div_pow, mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul (Real.exp_le_exp.mpr hL) hpow (pow_nonneg hq _) (Real.exp_pos _).le)
      (pow_nonneg hY.le _)

private theorem factorial_mul_radial_mid_le {n : ℕ} (hn : 0 < n) {C L : ℝ}
    (hC : 0 ≤ C) :
    (n.factorial : ℝ≥0∞) *
        (∫⁻ s in Ioc (1 / 2 : ℝ) L, ENNReal.ofReal (C / s ^ n) ∂spouseRadialLaw n) ≤
      ENNReal.ofReal (2 * (n : ℝ) * C * L) := by
  let A := Ioc (1 / 2 : ℝ) L
  let g (s : ℝ) := ENNReal.ofReal (C / s ^ n)
  let f (s : ℝ) := ENNReal.ofReal (s ^ (n - 1) / ((n - 1).factorial : ℝ))
  have hA : MeasurableSet A := measurableSet_Ioc
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  have hAZ : A ∩ Ioi (0 : ℝ) = A := inter_eq_left.mpr fun _ hs ↦
    (by norm_num : (0 : ℝ) < 1 / 2).trans hs.1
  have hrewrite :
      (∫⁻ s in A, g s ∂spouseRadialLaw n) =
        ∫⁻ s in A, f s * g s := by
    rw [← lintegral_indicator hA, spouseRadialLaw,
      lintegral_withDensity_eq_lintegral_mul _ hf (hg.indicator hA)]
    simp_rw [Pi.mul_apply, ← indicator_mul_right, lintegral_indicator hA,
      Measure.restrict_restrict hA, hAZ]
  have hfac : n.factorial = n * (n - 1).factorial := calc
    _ = (n - 1 + 1).factorial := by rw [Nat.sub_add_cancel hn]
    _ = _ := by rw [Nat.factorial_succ, Nat.sub_add_cancel hn]
  change (n.factorial : ℝ≥0∞) * (∫⁻ s in A, g s ∂spouseRadialLaw n) ≤ _
  rw [hrewrite, ← lintegral_const_mul' _ _ (by simp)]
  calc
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal (2 * (n : ℝ) * C) := by
      apply setLIntegral_mono' hA
      intro s hs
      have hs₀ : 0 < s := (by norm_num : (0 : ℝ) < 1 / 2).trans hs.1
      have hpow : s ^ n = s ^ (n - 1) * s := by rw [← pow_succ, Nat.sub_add_cancel hn]
      unfold f g
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hs₀.le _) (Nat.cast_nonneg _)),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have he : (n.factorial : ℝ) * (s ^ (n - 1) / ((n - 1).factorial : ℝ) *
          (C / s ^ n)) = (n : ℝ) * C / s := by
        rw [hfac, Nat.cast_mul, hpow]
        field_simp
      rw [he, div_le_iff₀ hs₀]
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hC) (sub_nonneg.mpr hs.1.le)]
    _ = ENNReal.ofReal (2 * (n : ℝ) * C) * ENNReal.ofReal (L - 1 / 2) := by
      rw [setLIntegral_const]
      change _ * volume (Ioc (1 / 2 : ℝ) L) = _
      rw [Real.volume_Ioc]
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

private theorem measurable_spouseVectorTotal' (n : ℕ) :
    Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

private theorem ae_spouseVectorLaw_mem_unit (n : ℕ) :
    ∀ᵐ y ∂spouseVectorLaw n, ∀ i, y i ∈ Icc (0 : ℝ) 1 := by
  rw [spouseVectorLaw_eq_restrict_volume]
  have hC : MeasurableSet (univ.pi fun _ : Fin n ↦ Icc (0 : ℝ) 1) :=
    (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure (Fin n → ℝ))) hC] with y hy
  exact fun i ↦ hy i (mem_univ i)

private theorem factorial_mul_femaleSpouse_near_le (n : ℕ) :
    (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y : Fin n → ℝ | spouseVectorTotal y ≤ 1 / 2},
        femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  let A := {y : Fin n → ℝ | spouseVectorTotal y ≤ 1 / 2}
  let S := scoreSimplex n (1 / 2)
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_spouseVectorTotal' n) measurable_const
  have hS : MeasurableSet S := measurableSet_scoreSimplex n _
  have hbound : (∫⁻ y in A, femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤ volume S := calc
    _ = ∫⁻ y, A.indicator femaleSpouseStabilityDensity y ∂spouseVectorLaw n :=
      (lintegral_indicator hA _).symm
    _ ≤ ∫⁻ y, S.indicator (fun _ ↦ 1) y ∂spouseVectorLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_spouseVectorLaw_mem_unit n] with y hy
      by_cases h : y ∈ A
      · have hs : y ∈ S := ⟨fun i ↦ (hy i).1, h⟩
        rw [indicator_of_mem h, indicator_of_mem hs]
        exact femaleSpouseStabilityDensity_le_one y hy
      · rw [indicator_of_notMem h]
        exact zero_le
    _ ≤ ∫⁻ y, S.indicator (fun _ ↦ 1) y := lintegral_mono' (spouseVectorLaw_le_volume n) le_rfl
    _ = _ := lintegral_indicator_one hS
  refine (mul_le_mul_right hbound _).trans_eq ?_
  change (n.factorial : ℝ≥0∞) * volume (scoreSimplex n (1 / 2)) = _
  rw [volume_scoreSimplex n (by norm_num), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]

private theorem factorial_mul_femaleSpouse_mid_le {n : ℕ} (hn : 0 < n)
    (L : ℝ) :
    (n.factorial : ℝ≥0∞) *
      (∫⁻ y in {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc (1 / 2) L},
        femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤
      ENNReal.ofReal (2 * (n : ℝ) * (Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L))) * L) := by
  let A := Ioc (1 / 2 : ℝ) L
  let R : Set (Fin n → ℝ) := spouseVectorTotal ⁻¹' A
  let C := Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L))
  let g (s : ℝ) := ENNReal.ofReal (C / s ^ n)
  let G (y : Fin n → ℝ) := A.indicator g (spouseVectorTotal y)
  have hA : MeasurableSet A := measurableSet_Ioc
  have hR : MeasurableSet R := hA.preimage (measurable_spouseVectorTotal' n)
  have hg : Measurable g := by unfold g; fun_prop
  have hG : Measurable G := (hg.indicator hA).comp (measurable_spouseVectorTotal' n)
  have hsub : spouseVectorLaw n ≤ (volume : Measure (Fin n → ℝ)).restrict
      {y | ∀ i, 0 ≤ y i} := by
    have hsubset : (univ.pi fun _ : Fin n ↦ Icc (0 : ℝ) 1) ⊆
        {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      intro y hy i
      exact (hy i (mem_univ i)).1
    rw [spouseVectorLaw_eq_restrict_volume]
    exact Measure.restrict_mono hsubset le_rfl
  have hbound :
      (∫⁻ y in R, femaleSpouseStabilityDensity y ∂spouseVectorLaw n) ≤
        ∫⁻ s in A, g s ∂spouseRadialLaw n := calc
    _ = ∫⁻ y, R.indicator femaleSpouseStabilityDensity y ∂spouseVectorLaw n :=
      (lintegral_indicator hR _).symm
    _ ≤ ∫⁻ y, G y ∂spouseVectorLaw n := by
      apply lintegral_mono_ae
      filter_upwards [ae_spouseVectorLaw_mem_unit n] with y hy
      by_cases h : spouseVectorTotal y ∈ A
      · change R.indicator femaleSpouseStabilityDensity y ≤ A.indicator g (spouseVectorTotal y)
        rw [indicator_of_mem (show y ∈ R from h), indicator_of_mem h]
        exact femaleSpouseStabilityDensity_le_smallCutoff hy
          ((by norm_num : (0 : ℝ) < 1 / 2).trans h.1) h.2
      · rw [indicator_of_notMem (show y ∉ R from h)]
        exact zero_le
    _ ≤ ∫⁻ y, G y ∂(volume.restrict {y | ∀ i, 0 ≤ y i}) := lintegral_mono' hsub le_rfl
    _ = _ := by
      rw [lintegral_spouseRadialAngular hn hG, ← lintegral_indicator hA]
      apply lintegral_congr
      intro s
      have h_inner : (∫⁻ w, G (fun i ↦ s * w i) ∂spouseAngularLaw n) =
          ∫⁻ _w, A.indicator g s ∂spouseAngularLaw n := by
        apply lintegral_congr_ae
        filter_upwards [ae_spouseAngularLaw hn] with w hw
        have hsum : spouseVectorTotal (fun i ↦ s * w i) = s := by
          rw [spouseVectorTotal, ← Finset.mul_sum, hw.2, mul_one]
        change A.indicator g (spouseVectorTotal (fun i ↦ s * w i)) = A.indicator g s
        rw [hsum]
      rw [h_inner, lintegral_const, measure_univ, mul_one]
  exact (mul_le_mul_right hbound _).trans (factorial_mul_radial_mid_le hn (by positivity))

/-- The near-zero simplex costs `(1/2)^n`.
Above one half, the radial density cancels the (n)-th power in the stability bound. -/
theorem sum_stable_smallSpouseTotal_le {n : ℕ} (hn : 0 < n) (L : ℝ) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < L}) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
        ENNReal.ofReal (2 * (n : ℝ) * (Real.exp L * Real.exp (-(n : ℝ) * Real.exp (-L))) * L) := by
  let S := {y : Fin n → ℝ | spouseVectorTotal y < L}
  let A := {y : Fin n → ℝ | spouseVectorTotal y ≤ 1 / 2}
  let B := {y : Fin n → ℝ | spouseVectorTotal y ∈ Ioc (1 / 2) L}
  have hS : MeasurableSet S := measurableSet_lt (measurable_spouseVectorTotal' n) measurable_const
  have hsub : S ⊆ A ∪ B := by
    intro y hy
    rcases le_or_gt (spouseVectorTotal y) (1 / 2) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, (show spouseVectorTotal y < L from hy).le⟩
  have he (μ : Matching n) :
      {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < L} =
        {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ S} := by
    ext x
    change (IsScoreStable x μ ∧ femaleSpouseTotal x μ < L) ↔
      IsScoreStable x μ ∧ spouseVectorTotal (femaleSpouseByHusband μ x) < L
    rw [femaleSpouseTotal_eq_sum_byHusband, spouseVectorTotal]
  simp_rw [he, continuousScoreLaw_stable_and_femaleSpouse _ hS]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ (n.factorial : ℝ≥0∞) *
        ((∫⁻ y in A, femaleSpouseStabilityDensity y ∂spouseVectorLaw n) +
          (∫⁻ y in B, femaleSpouseStabilityDensity y ∂spouseVectorLaw n)) :=
      mul_le_mul_right ((lintegral_mono_set hsub).trans
        (lintegral_union_le femaleSpouseStabilityDensity A B)) _
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (factorial_mul_femaleSpouse_near_le n)
        (factorial_mul_femaleSpouse_mid_le hn L)

/-- The expected number of stable marks below the logarithmic cutoff is
eventually smaller than every fixed inverse power. -/
theorem eventually_sum_stable_smallSpouseTotalLog_le (p : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ μ : Matching n, continuousScoreLaw n
        {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}) ≤
        ENNReal.ofReal ((n : ℝ) ^ (-p)) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnear : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p * Real.exp (-(n : ℝ) / 2))
      atTop (𝓝 0) := by
    refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (1 / 2) (by norm_num)).comp
      hcast).congr fun n ↦ ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  have hmidReal : Tendsto (fun x : ℝ ↦ x ^ (p + 3) * Real.exp (-(x ^ (1 / 10 : ℝ))))
      atTop (𝓝 0) := by
    refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (p + 3)) 1
      (by norm_num)).comp (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ)))).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, neg_one_mul, ← Real.rpow_mul hx]
    rw [show (1 / 10 : ℝ) * (10 * (p + 3)) = p + 3 by ring]
  have hmid := hmidReal.comp hcast
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hnear.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hmid.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)] with n hn hnearN hmidN
  have hn₀ : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let L := (9 / 10 : ℝ) * Real.log n
  have hlog := Real.log_nonneg hn1
  have hL : 0 ≤ L := mul_nonneg (by norm_num) hlog
  have hLlog : L ≤ Real.log n := mul_le_of_le_one_left hlog (by norm_num)
  have hexp : Real.exp L ≤ n := (Real.exp_le_exp.mpr hLlog).trans_eq (Real.exp_log hnR)
  have hLn : L ≤ n := hLlog.trans (by linarith [Real.log_le_sub_one_of_pos hnR])
  have hsmall : (1 / 2 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 2) := calc
    _ ≤ Real.exp (-(1 / 2 : ℝ)) ^ n := pow_le_pow_left₀ (by norm_num)
      (by simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
        Real.one_sub_le_exp_neg (1 / 2 : ℝ)) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hcut : (n : ℝ) * Real.exp (-L) = (n : ℝ) ^ (1 / 10 : ℝ) := by
    have he : Real.exp (-L) = (n : ℝ) ^ (-(9 / 10) : ℝ) := by
      rw [Real.rpow_def_of_pos hnR]
      congr 1
      dsimp only [L]
      ring
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(9 / 10) : ℝ) := by rw [Real.rpow_one, he]
      _ = _ := by rw [← Real.rpow_add hnR]; norm_num
  let E := Real.exp (-(n : ℝ) * Real.exp (-L))
  have hE : E = Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
    rw [show E = Real.exp (-((n : ℝ) * Real.exp (-L))) by simp only [E, neg_mul], hcut]
  have hmiddle : 2 * (n : ℝ) * (Real.exp L * E) * L ≤ 2 * (n : ℝ) ^ 3 * E := calc
    _ = 2 * (n : ℝ) * Real.exp L * L * E := by ring
    _ ≤ 2 * (n : ℝ) * n * n * E := by gcongr
    _ = _ := by ring
  have hnearFinal : (n : ℝ) ^ p * ((1 / 2 : ℝ) ^ n) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnR.le _)).trans hnearN.le
  have hmidFinal : (n : ℝ) ^ p * (2 * (n : ℝ) * (Real.exp L * E) * L) ≤ 1 / 2 := calc
    _ ≤ (n : ℝ) ^ p * (2 * (n : ℝ) ^ 3 * E) :=
      mul_le_mul_of_nonneg_left hmiddle (Real.rpow_nonneg hnR.le _)
    _ = 2 * ((n : ℝ) ^ p * (n : ℝ) ^ 3 * E) := by ring
    _ = 2 * ((n : ℝ) ^ (p + 3) * Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ)))) := by
      rw [hE, ← Real.rpow_natCast (n : ℝ) 3, ← Real.rpow_add hnR]
      norm_num
    _ ≤ _ := by linarith [show (n : ℝ) ^ (p + 3) *
        Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) < 1 / 4 from hmidN]
  refine (sum_stable_smallSpouseTotal_le hn₀ L).trans ?_
  change ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
    ENNReal.ofReal (2 * (n : ℝ) * (Real.exp L * E) * L) ≤ _
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_neg hnR.le, ← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hnR _)).2
  rw [mul_comm, mul_add]
  exact (add_le_add hnearFinal hmidFinal).trans_eq (by norm_num)

end LennonPittelFormalization

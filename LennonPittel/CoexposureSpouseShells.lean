module

public import LennonPittel.CoexposureScoreEstimates
public import LennonPittel.CoexposureSpouseMarginal
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Spouse-score integrals over thin shells

The stability density is controlled on a shell by its value at the lower
radius. Simplex volume then cancels the factorial for the matching labels.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

/-- The total of the women's spouse scores. -/
def spouseVectorTotal {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i

private theorem measurable_spouseVectorTotal (n : ℕ) :
    Measurable (@spouseVectorTotal n) :=
  Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i

/-- A nonnegative spouse vector of total in `[2,n]` with a large relative coordinate. -/
def largeRelativeSpouseScoreSet (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ 2 ≤ spouseVectorTotal y ∧ spouseVectorTotal y ≤ n ∧
    ∃ i, 12 * Real.log n / n < y i / spouseVectorTotal y}

/-- A nonnegative spouse vector whose total is below two. -/
def smallSpouseScoreSet (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ spouseVectorTotal y < 2}

private theorem measurableSet_nonnegativeSpouseScores (n : ℕ) :
    MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)

/-- The set of vectors with a large relative spouse score is measurable. -/
theorem measurableSet_largeRelativeSpouseScoreSet (n : ℕ) :
    MeasurableSet (largeRelativeSpouseScoreSet n) := by
  unfold largeRelativeSpouseScoreSet
  simp only [ofPred_and, ofPred_exists]
  exact (measurableSet_nonnegativeSpouseScores n).inter
    ((measurableSet_le measurable_const (measurable_spouseVectorTotal n)).inter
      ((measurableSet_le (measurable_spouseVectorTotal n) measurable_const).inter
        (MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const
          ((measurable_pi_apply i).div (measurable_spouseVectorTotal n)))))

/-- The set of vectors with a small spouse-score total is measurable. -/
theorem measurableSet_smallSpouseScoreSet (n : ℕ) :
    MeasurableSet (smallSpouseScoreSet n) := by
  unfold smallSpouseScoreSet
  rw [ofPred_and]
  exact (measurableSet_nonnegativeSpouseScores n).inter
    (measurableSet_lt (measurable_spouseVectorTotal n) measurable_const)

private theorem exists_shell_index {s b : ℝ} {n : ℕ} (hn : 0 < n) {N : ℕ}
    (hbs : b ≤ s) (hs : (s - b) * (n : ℝ) ≤ (N : ℝ)) :
    ∃ j : Fin (N + 1), b + (j.val : ℝ) / n ≤ s ∧ s ≤ b + (j.val + 1 : ℝ) / n := by
  let j := ⌊(s - b) * (n : ℝ)⌋₊
  have hj : j ≤ N := Nat.floor_le_of_le hs
  have hfloor : (j : ℝ) ≤ (s - b) * (n : ℝ) :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hbs) (Nat.cast_nonneg n))
  have hceil : (s - b) * (n : ℝ) ≤ (j : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  refine ⟨⟨j, Nat.lt_succ_of_le hj⟩, ?_, ?_⟩
  · have h := (div_le_iff₀ (Nat.cast_pos.mpr hn)).2 hfloor
    linarith
  · have h := (le_div_iff₀ (Nat.cast_pos.mpr hn)).2 hceil
    linarith

private theorem lintegral_le_const_mul_volume {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) {f : (Fin n → ℝ) → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ y ∈ S, f y ≤ c) :
    (∫⁻ y in S, f y) ≤ c * volume S := by
  calc
    _ ≤ ∫⁻ _ in S, c := setLIntegral_mono' hS hf
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

private theorem lintegral_spouseShell_le {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) {f : (Fin n → ℝ) → ℝ≥0∞} {l R c : ℝ}
    (hl : 0 < l) (hc : 0 ≤ c) (hL : ∀ y ∈ S, l ≤ spouseVectorTotal y)
    (hV : volume S ≤ ENNReal.ofReal (R ^ n / (n.factorial : ℝ)))
    (hf : ∀ y ∈ S, f y ≤ ENNReal.ofReal (c / spouseVectorTotal y ^ n)) :
    (∫⁻ y in S, f y) ≤ ENNReal.ofReal (c * (R / l) ^ n / (n.factorial : ℝ)) := by
  have hc' : 0 ≤ c / l ^ n := div_nonneg hc (pow_nonneg hl.le _)
  calc
    _ ≤ ENNReal.ofReal (c / l ^ n) * volume S :=
      lintegral_le_const_mul_volume hS fun y hy ↦ (hf y hy).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hc (pow_pos hl _)
          (pow_le_pow_left₀ hl.le (hL y hy) _)))
    _ ≤ ENNReal.ofReal (c / l ^ n) * ENNReal.ofReal (R ^ n / (n.factorial : ℝ)) :=
      by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul hc', div_pow]; congr 1; ring

private theorem thinShell_ratio_pow_le {n : ℕ} (hn : 0 < n)
    {b l a : ℝ} (hb : 0 < b) (hbl : b ≤ l) (ha : a ≤ 1) :
    ((l + 1 / (n : ℝ) - a * l) / l) ^ n ≤ Real.exp (1 / b - a * n) := by
  have hl := hb.trans_le hbl
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hR : 0 ≤ l + 1 / (n : ℝ) - a * l := by
    linarith [mul_le_of_le_one_left hl.le ha, one_div_nonneg.mpr hn'.le]
  have hdiv : (1 / (n : ℝ)) / l ≤ 1 / (n : ℝ) / b :=
    div_le_div_of_nonneg_left (by positivity) hb hbl
  have hratio : (l + 1 / (n : ℝ) - a * l) / l = 1 + ((1 / (n : ℝ)) / l - a) := by
    field_simp [hl.ne']; ring
  calc
    _ ≤ (Real.exp (1 / (n : ℝ) / b - a)) ^ n := by
      refine pow_le_pow_left₀ (div_nonneg hR hl.le) ?_ n
      rw [hratio]
      linarith [Real.add_one_le_exp (1 / (n : ℝ) / b - a)]
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hn'.ne']

/-- The factorial-scaled integral over large relative spouse scores is bounded
by a polynomial shell count times the exponentially small simplex-volume loss. -/
theorem factorial_mul_lintegral_largeRelativeSpouseScore_le {n : ℕ} (hn : 0 < n)
    (hcut : 12 * Real.log n / (n : ℝ) ≤ 1) {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf : ∀ y ∈ largeRelativeSpouseScoreSet n,
      f y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n)) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in largeRelativeSpouseScoreSet n, f y) ≤
      ENNReal.ofReal (((n : ℝ) ^ 2 + 1) * n * Real.exp (5 / 2) / (n : ℝ) ^ 12) := by
  let a := 12 * Real.log n / (n : ℝ)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ha : 0 ≤ a := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg h)) hn'.le
  let l (j : Fin (n * n + 1)) : ℝ := 2 + j.val / (n : ℝ)
  let S (q : Fin (n * n + 1) × Fin n) : Set (Fin n → ℝ) :=
    largeRelativeSpouseScoreSet n ∩ {y | y ∈ scoreSimplex n (l q.1 + 1 / (n : ℝ)) ∧
      l q.1 ≤ spouseVectorTotal y ∧ a < y q.2 / spouseVectorTotal y}
  have hS (q : Fin (n * n + 1) × Fin n) : MeasurableSet (S q) := by
    refine (measurableSet_largeRelativeSpouseScoreSet n).inter ?_
    rw [ofPred_and, ofPred_and]
    exact (measurableSet_scoreSimplex _ _).inter
      ((measurableSet_le measurable_const (measurable_spouseVectorTotal n)).inter
        (measurableSet_lt measurable_const
          ((measurable_pi_apply q.2).div (measurable_spouseVectorTotal n))))
  have hcover : largeRelativeSpouseScoreSet n ⊆ ⋃ q, S q := by
    intro y hy
    obtain ⟨hy₀, hy₂, hyn, i, hi⟩ := hy
    have hs : (spouseVectorTotal y - 2) * (n : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hn'.le
    obtain ⟨j, hj₁, hj₂⟩ := exists_shell_index hn hy₂ hs
    exact mem_iUnion.mpr ⟨(j, i), ⟨hy₀, hy₂, hyn, i, hi⟩, ⟨hy₀, hj₂.trans_eq (by
      dsimp only [l]
      ring)⟩, hj₁, hi⟩
  let c := Real.exp (5 / 2) / (n : ℝ) ^ 12
  have hc₀ : 0 ≤ c := by positivity
  have hlocal (q : Fin (n * n + 1) × Fin n) :
      (∫⁻ y in S q, f y) ≤ ENNReal.ofReal (c / (n.factorial : ℝ)) := by
    have hl₂ : 2 ≤ l q.1 := le_add_of_nonneg_right (by positivity)
    have hl : 0 < l q.1 := by linarith
    have hR : a * l q.1 ≤ l q.1 + 1 / (n : ℝ) :=
      (mul_le_of_le_one_left hl.le hcut).trans (le_add_of_nonneg_right (by positivity))
    have hV := volume_scoreSimplex_shell_large_coordinate_le n q.2 hl ha hR
    refine (lintegral_spouseShell_le (hS q) hl (Real.exp_pos _).le
      (fun y hy ↦ hy.2.2.1) ((measure_mono fun y hy ↦ hy.2).trans hV)
      (fun y hy ↦ hf y hy.1)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hratio := thinShell_ratio_pow_le hn (by norm_num : (0 : ℝ) < 2) hl₂ (show a ≤ 1 from hcut)
    have hlog : a * (n : ℝ) = 12 * Real.log n := div_mul_cancel₀ _ hn'.ne'
    have hcoef : Real.exp 2 * Real.exp (1 / (2 : ℝ) - a * n) = c := by
      dsimp only [c]
      rw [← Real.exp_add, hlog, show 2 + (1 / (2 : ℝ) - 12 * Real.log n) =
        5 / 2 - (12 : ℕ) * Real.log n by ring]
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hn']
    rw [← hcoef]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le) (Nat.cast_nonneg _)
  calc
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ q : Fin (n * n + 1) × Fin n,
          ∫⁻ y in S q, f y := by
      have h := (lintegral_mono_set hcover).trans (by simpa [tsum_fintype] using
        (lintegral_iUnion_le S f : (∫⁻ y in ⋃ q, S q, f y) ≤
          ∑' q, ∫⁻ y in S q, f y))
      exact mul_le_mul_right h _
    _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (n * n + 1) × Fin n,
          ENNReal.ofReal (c / (n.factorial : ℝ)) := by
      gcongr with q _
      exact hlocal q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      simp only [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      dsimp only [c]
      field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]

/-- The near-zero simplex has exponentially small factorial-scaled volume;
on the rest of the small-total event the finite integration endpoint gives
an exponential density loss on every shell. -/
theorem factorial_mul_lintegral_smallSpouseScore_le {n : ℕ} (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf₀ : ∀ y ∈ smallSpouseScoreSet n, spouseVectorTotal y ≤ 1 / 2 → f y ≤ 1)
    (hf₁ : ∀ y ∈ smallSpouseScoreSet n, 1 / 2 ≤ spouseVectorTotal y →
      f y ≤ ENNReal.ofReal (Real.exp (spouseVectorTotal y) *
        ((1 - Real.exp (-spouseVectorTotal y)) / spouseVectorTotal y) ^ n)) :
    (n.factorial : ℝ≥0∞) * (∫⁻ y in smallSpouseScoreSet n, f y) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
        ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * (1 - Real.exp (-2)) ^ n) := by
  let A := smallSpouseScoreSet n ∩ scoreSimplex n (1 / 2)
  have hsmall := measurableSet_smallSpouseScoreSet n
  have hA : MeasurableSet A := hsmall.inter (measurableSet_scoreSimplex _ _)
  have hnear : (n.factorial : ℝ≥0∞) * (∫⁻ y in A, f y) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    have hbound := lintegral_le_const_mul_volume hA (fun y hy ↦ hf₀ y hy.1 hy.2.2)
    have hvol : volume A ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact measure_mono inter_subset_right
    calc
      _ ≤ (n.factorial : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n / (n.factorial : ℝ)) := by
        have h := (by simpa only [one_mul] using hbound :
          (∫⁻ y in A, f y) ≤ volume A)
        exact mul_le_mul_right (h.trans hvol) _
      _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
  let l (j : Fin (2 * n + 1)) : ℝ := 1 / 2 + j.val / (n : ℝ)
  let S (j : Fin (2 * n + 1)) : Set (Fin n → ℝ) :=
    smallSpouseScoreSet n ∩ {y | y ∈ scoreSimplex n (l j + 1 / (n : ℝ)) ∧
      l j ≤ spouseVectorTotal y}
  have hS (j : Fin (2 * n + 1)) : MeasurableSet (S j) := by
    refine hsmall.inter ?_
    rw [ofPred_and]
    exact (measurableSet_scoreSimplex _ _).inter
      (measurableSet_le measurable_const (measurable_spouseVectorTotal n))
  have hcover : smallSpouseScoreSet n ⊆ A ∪ ⋃ j, S j := by
    intro y hy
    by_cases ht : spouseVectorTotal y ≤ 1 / 2
    · exact Or.inl ⟨hy, hy.1, ht⟩
    · have hs : (spouseVectorTotal y - 1 / 2) * (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
        push_cast
        exact mul_le_mul_of_nonneg_right (by linarith [hy.2]) (Nat.cast_nonneg n)
      obtain ⟨j, hj₁, hj₂⟩ := exists_shell_index hn (le_of_not_ge ht) hs
      exact Or.inr (mem_iUnion.mpr ⟨j, hy, ⟨hy.1, hj₂.trans_eq (by
        dsimp only [l]
        ring)⟩, hj₁⟩)
  let q : ℝ := 1 - Real.exp (-2)
  have hq₀ : 0 ≤ q := by
    dsimp [q]
    linarith [Real.exp_le_one_iff.mpr (by norm_num : (-2 : ℝ) ≤ 0)]
  let c := Real.exp 4 * q ^ n
  have hlocal (j : Fin (2 * n + 1)) :
      (∫⁻ y in S j, f y) ≤ ENNReal.ofReal (c / (n.factorial : ℝ)) := by
    have hlhalf : 1 / 2 ≤ l j := le_add_of_nonneg_right (by positivity)
    have hl : 0 < l j := by linarith
    have hR : 0 ≤ l j + 1 / (n : ℝ) := by positivity
    have hV : volume (S j) ≤
        ENNReal.ofReal ((l j + 1 / (n : ℝ)) ^ n / (n.factorial : ℝ)) := by
      rw [← volume_scoreSimplex n hR]
      exact measure_mono fun _ hy ↦ hy.2.1
    have hdens (y : Fin n → ℝ) (hy : y ∈ S j) :
        f y ≤ ENNReal.ofReal (Real.exp 2 * q ^ n / spouseVectorTotal y ^ n) := by
      have hs : 1 / 2 ≤ spouseVectorTotal y := hlhalf.trans hy.2.2
      refine (hf₁ y hy.1 hs).trans (ENNReal.ofReal_le_ofReal ?_)
      have hs₀ : 0 ≤ 1 - Real.exp (-spouseVectorTotal y) := by
        linarith [Real.exp_le_one_iff.mpr (by linarith : -spouseVectorTotal y ≤ 0)]
      have hsq : 1 - Real.exp (-spouseVectorTotal y) ≤ q :=
        sub_le_sub_left (Real.exp_le_exp.mpr (by linarith [hy.1.2])) 1
      rw [div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (Real.exp_le_exp.mpr hy.1.2.le)
          (pow_le_pow_left₀ hs₀ hsq _) (pow_nonneg hs₀ _) (Real.exp_pos _).le)
        (pow_nonneg (by linarith) _)
    refine (lintegral_spouseShell_le (hS j) hl (by positivity) (fun _ hy ↦ hy.2.2)
      hV hdens).trans (ENNReal.ofReal_le_ofReal ?_)
    have hratio := thinShell_ratio_pow_le hn (by norm_num : (0 : ℝ) < 1 / 2) hlhalf
      (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at hratio
    have hcoef : Real.exp 2 * q ^ n * Real.exp 2 = c := by
      dsimp only [c]
      rw [show Real.exp 4 = Real.exp 2 * Real.exp 2 by rw [← Real.exp_add]; norm_num]
      ring
    rw [← hcoef]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using hratio) (by positivity)) (Nat.cast_nonneg _)
  have hshells : (n.factorial : ℝ≥0∞) * (∫⁻ y in ⋃ j, S j, f y) ≤
      ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n) := by
    calc
      _ ≤ (n.factorial : ℝ≥0∞) * ∑ j : Fin (2 * n + 1), ∫⁻ y in S j, f y := by
        exact mul_le_mul_right (by simpa [tsum_fintype] using
          (lintegral_iUnion_le S f : (∫⁻ y in ⋃ j, S j, f y) ≤
            ∑' j, ∫⁻ y in S j, f y)) _
      _ ≤ (n.factorial : ℝ≥0∞) * ∑ _ : Fin (2 * n + 1),
          ENNReal.ofReal (c / (n.factorial : ℝ)) := by
        gcongr with j _
        exact hlocal j
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        dsimp only [c]
        field_simp [show (n.factorial : ℝ) ≠ 0 by positivity]
  have hUnion := (lintegral_mono_set hcover).trans
    (lintegral_union_le (μ := volume) f A (⋃ j, S j))
  exact (mul_le_mul_right hUnion _).trans (by rw [mul_add]; exact add_le_add hnear hshells)

/-- The large-relative-coordinate contribution tends to zero after counting all matchings. -/
theorem tendsto_factorial_mul_lintegral_largeRelativeSpouseScore_zero
    (f : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞)
    (hf : ∀ᶠ n in atTop, ∀ y ∈ largeRelativeSpouseScoreSet n,
      f n y ≤ ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n)) :
    Tendsto (fun n ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in largeRelativeSpouseScoreSet n, f n y)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ 12 * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop one_pos).tendsto_div_nhds_zero.comp hcast
    simpa only [Function.comp_apply, Real.rpow_one, ← mul_div_assoc, mul_zero] using
      h.const_mul (12 : ℝ)
  have hcut : ∀ᶠ n : ℕ in atTop, 12 * Real.log (n : ℝ) / (n : ℝ) ≤ 1 :=
    ((tendsto_order.mp hlog).2 1 zero_lt_one).mono fun _ h ↦ h.le
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * Real.exp (5 / 2) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply, ← div_eq_mul_inv, mul_zero] using
      ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero.comp hcast).const_mul
        (2 * Real.exp (5 / 2)))
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcut, hf] with n hn hc h
  refine (factorial_mul_lintegral_largeRelativeSpouseScore_le
    (zero_lt_one.trans_le hn) hc h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx₀ : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hx
  apply (div_le_div_iff₀ (pow_pos hx₀ _) hx₀).2
  have hxx : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hx
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) * n * Real.exp (5 / 2) * n := by
      gcongr
      linarith
    _ = 2 * Real.exp (5 / 2) * (n : ℝ) ^ 4 := by ring
    _ ≤ _ := by
      gcongr
      norm_num

/-- The small-total contribution tends to zero after counting all matchings. -/
theorem tendsto_factorial_mul_lintegral_smallSpouseScore_zero
    (f : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞)
    (hf₀ : ∀ᶠ n in atTop, ∀ y ∈ smallSpouseScoreSet n,
      spouseVectorTotal y ≤ 1 / 2 → f n y ≤ 1)
    (hf₁ : ∀ᶠ n in atTop, ∀ y ∈ smallSpouseScoreSet n, 1 / 2 ≤ spouseVectorTotal y →
      f n y ≤ ENNReal.ofReal (Real.exp (spouseVectorTotal y) *
        ((1 - Real.exp (-spouseVectorTotal y)) / spouseVectorTotal y) ^ n)) :
    Tendsto (fun n ↦ (n.factorial : ℝ≥0∞) *
      (∫⁻ y in smallSpouseScoreSet n, f n y)) atTop (𝓝 0) := by
  let q : ℝ := 1 - Real.exp (-2)
  have hq₀ : 0 ≤ q :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have hq₁ : q < 1 := sub_lt_self _ (Real.exp_pos _)
  have hhalf : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁
  have hngeom := tendsto_self_mul_const_pow_of_lt_one hq₀ hq₁
  have hterm : Tendsto (fun n : ℕ ↦ (2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n)
      atTop (𝓝 0) := by
    have h := ((hngeom.const_mul (2 : ℝ)).add hgeom).const_mul (Real.exp 4)
    rw [mul_zero, zero_add, mul_zero] at h
    refine h.congr fun n ↦ ?_
    ring
  have ht : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) +
      ENNReal.ofReal ((2 * (n : ℝ) + 1) * Real.exp 4 * q ^ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, zero_add] using
      (ENNReal.tendsto_ofReal hhalf).add (ENNReal.tendsto_ofReal hterm)
  refine tendsto_const_nhds.squeeze' ht (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ), hf₀, hf₁] with n hn h₀ h₁
  exact factorial_mul_lintegral_smallSpouseScore_le (zero_lt_one.trans_le hn) h₀ h₁

private def spouseScoreCube (n : ℕ) : Set (Fin n → ℝ) :=
  univ.pi fun _ ↦ Icc (0 : ℝ) 1

private theorem measurableSet_spouseScoreCube (n : ℕ) : MeasurableSet (spouseScoreCube n) :=
  (measurableSet_pi countable_univ).2 (Or.inl fun _ _ ↦ measurableSet_Icc)

private noncomputable def maskedFemaleStabilityDensity (n : ℕ) (y : Fin n → ℝ) :
    ℝ≥0∞ :=
  (spouseScoreCube n).indicator femaleSpouseStabilityDensity y

private theorem femaleSpouseStabilityDensity_eq_ofReal_prod {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) 1) :
    femaleSpouseStabilityDensity y =
      ENNReal.ofReal (∏ i, scoreRowMass (Finset.univ.erase i) y 0 1) := by
  unfold femaleSpouseStabilityDensity
  symm
  apply ENNReal.ofReal_prod_of_nonneg
  intro i _
  unfold scoreRowMass
  refine intervalIntegral.integral_nonneg (by norm_num) fun x hx ↦ ?_
  unfold scoreRowKernel
  exact Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (calc
    x * y j ≤ 1 * y j := mul_le_mul_of_nonneg_right hx.2 (hy j).1
    _ ≤ 1 := by simpa only [one_mul] using (hy j).2)

private theorem sum_stable_femaleSpouse_eq_factorial_mul {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ B}) =
      (n.factorial : ℝ≥0∞) * (∫⁻ y in B, maskedFemaleStabilityDensity n y) := by
  simp_rw [continuousScoreLaw_stable_and_femaleSpouse _ hB]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [spouseVectorLaw_eq_restrict_volume, Measure.restrict_restrict hB]
  change (n.factorial : ℝ≥0∞) *
    (∫⁻ y in B ∩ spouseScoreCube n, femaleSpouseStabilityDensity y) = _
  unfold maskedFemaleStabilityDensity
  rw [setLIntegral_indicator (measurableSet_spouseScoreCube n),
    inter_comm B (spouseScoreCube n)]

/-- Stable matchings with a small female spouse-score total have vanishing total mass. -/
theorem tendsto_sum_stable_smallSpouseScore_zero :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ smallSpouseScoreSet n})
      atTop (𝓝 0) := by
  simp_rw [sum_stable_femaleSpouse_eq_factorial_mul (measurableSet_smallSpouseScoreSet _)]
  apply tendsto_factorial_mul_lintegral_smallSpouseScore_zero
  · exact Eventually.of_forall fun n y _ _ ↦ by
      by_cases hy : y ∈ spouseScoreCube n
      · rw [maskedFemaleStabilityDensity, indicator_of_mem hy]
        exact femaleSpouseStabilityDensity_le_one y (fun j ↦ hy j (mem_univ j))
      · simp [maskedFemaleStabilityDensity, indicator_of_notMem hy]
  · exact Eventually.of_forall fun n y _ hs ↦ by
      by_cases hy : y ∈ spouseScoreCube n
      · have hcube (j : Fin n) : y j ∈ Icc (0 : ℝ) 1 := hy j (mem_univ j)
        change 1 / 2 ≤ ∑ j, y j at hs
        rw [maskedFemaleStabilityDensity, indicator_of_mem hy,
          femaleSpouseStabilityDensity_eq_ofReal_prod hcube]
        apply ENNReal.ofReal_le_ofReal
        simpa only [spouseVectorTotal, Fintype.card_fin] using
          scoreRowMass_prod_le_finite_exp y hcube (by linarith [hs])
      · simp [maskedFemaleStabilityDensity, indicator_of_notMem hy]

private theorem maskedFemaleStabilityDensity_le_of_largeRelativeSpouseScore {n : ℕ}
    {y : Fin n → ℝ} (hy : y ∈ largeRelativeSpouseScoreSet n) :
    maskedFemaleStabilityDensity n y ≤
      ENNReal.ofReal (Real.exp 2 / spouseVectorTotal y ^ n) := by
  by_cases hcube : y ∈ spouseScoreCube n
  · have hcoord (j : Fin n) : y j ∈ Icc (0 : ℝ) 1 := hcube j (mem_univ j)
    rw [maskedFemaleStabilityDensity, indicator_of_mem hcube,
      femaleSpouseStabilityDensity_eq_ofReal_prod hcoord]
    apply ENNReal.ofReal_le_ofReal
    simpa only [spouseVectorTotal, Fintype.card_fin] using
      scoreRowMass_prod_le_inv_pow y hcoord hy.2.1
  · simp [maskedFemaleStabilityDensity, indicator_of_notMem hcube]

/-- A quantitative count of stable marks with a large relative female spouse score. -/
theorem sum_stable_largeRelativeSpouseScore_le {n : ℕ} (hn : 0 < n)
    (hcut : 12 * Real.log n / (n : ℝ) ≤ 1) :
    (∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n}) ≤
        ENNReal.ofReal (((n : ℝ) ^ 2 + 1) * n * Real.exp (5 / 2) / (n : ℝ) ^ 12) := by
  rw [sum_stable_femaleSpouse_eq_factorial_mul (measurableSet_largeRelativeSpouseScoreSet n)]
  exact factorial_mul_lintegral_largeRelativeSpouseScore_le hn hcut
    (fun _ ↦ maskedFemaleStabilityDensity_le_of_largeRelativeSpouseScore)

/-- Stable matchings with a large relative female spouse score have vanishing total mass. -/
theorem tendsto_sum_stable_largeRelativeSpouseScore_zero :
    Tendsto (fun n : ℕ ↦ ∑ μ : Matching n, continuousScoreLaw n
      {x | IsScoreStable x μ ∧ femaleSpouseByHusband μ x ∈ largeRelativeSpouseScoreSet n})
      atTop (𝓝 0) := by
  simp_rw [sum_stable_femaleSpouse_eq_factorial_mul
    (measurableSet_largeRelativeSpouseScoreSet _)]
  apply tendsto_factorial_mul_lintegral_largeRelativeSpouseScore_zero
  exact Eventually.of_forall fun _ _ ↦ maskedFemaleStabilityDensity_le_of_largeRelativeSpouseScore

end LennonPittelFormalization

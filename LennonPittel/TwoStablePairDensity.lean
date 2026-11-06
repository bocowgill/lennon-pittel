module

public import LennonPittel.TwoStableScoreProduct
public import LennonPittel.PittelSimplexRadial
public import Mathlib.Probability.Independence.Integration

/-!
# Fixed-pair joint-stability density

The blocking union at a cell yields a row-product upper bound. The loss from
omitting the spouse cells is bounded by an absolute constant, so the integrated
upper kernel depends only on three female score sums. See Craig Lennon,
*On the Likely Number of Stable Marriages* (2007), §§3.2 and 4.1.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The Laplace transform of one uniform score on the unit interval. -/
noncomputable def pairLaplace (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-s * t) ∂unitScoreLaw

private theorem pairLaplace_integrable (s : ℝ) :
    Integrable (fun t ↦ Real.exp (-s * t)) unitScoreLaw :=
  (show Continuous (fun t : ℝ ↦ Real.exp (-s * t)) by fun_prop).integrableOn_Icc

theorem pairLaplace_nonneg (s : ℝ) : 0 ≤ pairLaplace s :=
  integral_nonneg fun _ ↦ (Real.exp_pos _).le

private theorem pairLaplace_of_ne_zero {s : ℝ} (hs : s ≠ 0) :
    pairLaplace s = (1 - Real.exp (-s)) / s := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun x ↦ -(Real.exp (-s * x)) / s) (Real.exp (-s * t)) t := by
    convert (((Real.hasDerivAt_exp (-s * t)).comp t
      (hasDerivAt_const_mul (-s))).neg.div_const s) using 1
    · rfl
    · rw [mul_neg, neg_neg, mul_div_cancel_right₀ _ hs]
  unfold pairLaplace unitScoreLaw
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_one, mul_zero, Real.exp_zero]
  ring

theorem pairLaplace_of_pos {s : ℝ} (hs : 0 < s) :
    pairLaplace s = (1 - Real.exp (-s)) / s :=
  pairLaplace_of_ne_zero hs.ne'

private theorem measurable_pairLaplace : Measurable pairLaplace := by
  have heq : pairLaplace = ({0} : Set ℝ).piecewise (fun _ ↦ 1)
      (fun s ↦ (1 - Real.exp (-s)) / s) := by
    funext s
    by_cases h : s = 0
    · subst s
      simp [pairLaplace]
    · simpa [h] using pairLaplace_of_ne_zero h
  rw [heq]
  exact measurable_const.piecewise (measurableSet_singleton _) (by fun_prop)

theorem pairLaplace_le_exp_mul {s a : ℝ} (ha : 0 ≤ a) :
    pairLaplace (s - a) ≤ Real.exp a * pairLaplace s := by
  unfold pairLaplace
  rw [← integral_const_mul]
  refine integral_mono_ae (pairLaplace_integrable _) ((pairLaplace_integrable _).const_mul _) ?_
  have ht : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc 0 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [ht] with t ht
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left ht.2 ha]

private theorem pairLaplace_le_exp_relative {s a : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hle : 2 * a ≤ s) :
    pairLaplace (s - a) ≤ Real.exp (2 * a / s) * pairLaplace s := by
  have hsa : 0 < s - a := by linarith
  have hnum : 1 - Real.exp (-(s - a)) ≤ 1 - Real.exp (-s) := by
    gcongr
    linarith
  have hrat : s / (s - a) ≤ 1 + 2 * a / s := by
    apply (div_le_iff₀ hsa).mpr
    rw [add_mul, one_mul, div_mul_eq_mul_div]
    have haux : a ≤ (2 * a * (s - a)) / s := by
      apply (le_div_iff₀ hs).mpr
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr hle)]
    linarith
  rw [pairLaplace_of_pos hsa, pairLaplace_of_pos hs]
  calc
    _ ≤ (1 - Real.exp (-s)) / (s - a) := div_le_div_of_nonneg_right hnum hsa.le
    _ = (s / (s - a)) * ((1 - Real.exp (-s)) / s) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hrat.trans (by simpa only [add_comm] using Real.add_one_le_exp (2 * a / s)))
      (div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) hs.le)

/-- Deleting bounded contributions of total size at most twice the full sum costs only an
absolute factor, regardless of the number of rows. -/
theorem pairLaplace_omission_product {ι : Type*} (I : Finset ι) {s : ℝ}
    (a : ι → ℝ) (ha : ∀ i ∈ I, 0 ≤ a i) (hcap : ∀ i ∈ I, a i ≤ 6)
    (hsum : (∑ i ∈ I, a i) ≤ 2 * s) :
    (∏ i ∈ I, pairLaplace (s - a i)) ≤ Real.exp 24 * pairLaplace s ^ I.card := by
  by_cases h : s ≤ 12
  · calc
      _ ≤ ∏ i ∈ I, Real.exp (a i) * pairLaplace s :=
        Finset.prod_le_prod₀ (fun _ _ ↦ pairLaplace_nonneg _)
          (fun i hi ↦ pairLaplace_le_exp_mul (ha i hi))
      _ = Real.exp (∑ i ∈ I, a i) * pairLaplace s ^ I.card := by
        rw [Finset.prod_mul_distrib, Real.exp_sum, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (pow_nonneg (pairLaplace_nonneg s) _)
  · have hs' : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 12) (le_of_not_ge h)
    calc
      _ ≤ ∏ i ∈ I, Real.exp (2 * a i / s) * pairLaplace s :=
        Finset.prod_le_prod₀ (fun _ _ ↦ pairLaplace_nonneg _)
          (fun i hi ↦ pairLaplace_le_exp_relative hs' (ha i hi) (by linarith [hcap i hi]))
      _ = Real.exp (2 * (∑ i ∈ I, a i) / s) * pairLaplace s ^ I.card := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.mul_sum,
          Finset.sum_div]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          ((div_le_iff₀ hs').mpr (by linarith)))
        (pow_nonneg (pairLaplace_nonneg s) _)

private theorem unitScoreLaw_Ico_of_mem_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitScoreLaw (Ico a b) = ENNReal.ofReal (b - a) := by
  have hsub : Ico a b ⊆ Icc 0 1 := fun _ ht ↦ ⟨ha.trans ht.1, ht.2.le.trans hb⟩
  rw [unitScoreLaw, Measure.restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub,
    Real.volume_Ico]

/-- If the left male threshold is smaller, the exact blocking area is the sum of
two disjoint rectangles: the shared strip below it, and the right threshold's remaining strip. -/
theorem unitScorePairLaw_jointNonblocking_of_le {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc 0 1) (hx₂ : x₂ ∈ Icc 0 1) (hy₁ : y₁ ∈ Icc 0 1)
    (hy₂ : y₂ ∈ Icc 0 1) (hx : x₁ ≤ x₂) :
    unitScorePairLaw (jointNonblockingScoreCell x₁ y₁ x₂ y₂) =
      1 - ENNReal.ofReal (x₁ * max y₁ y₂ + (x₂ - x₁) * y₂) := by
  let A := Iio x₁ ×ˢ Iio (max y₁ y₂)
  let B := Ico x₁ x₂ ×ˢ Iio y₂
  have hA : MeasurableSet A := measurableSet_Iio.prod measurableSet_Iio
  have hB : MeasurableSet B := measurableSet_Ico.prod measurableSet_Iio
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact (not_lt_of_ge (show x₁ ≤ p.1 from hq.1.1)) (show p.1 < x₁ from hp.1)
  have heq : jointNonblockingScoreCell x₁ y₁ x₂ y₂ = (A ∪ B)ᶜ := by
    ext p
    simp only [jointNonblockingScoreCell, nonblockingScoreCell, A, B, Set.mem_inter_iff,
      Set.mem_union, Set.mem_compl_iff, Set.mem_prod, Set.mem_Iio, Set.mem_Ico, lt_max_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ (⟨hp, h₃ | h₄⟩ | ⟨⟨_, hq⟩, h₄⟩)
      · exact h₁ ⟨hp, h₃⟩
      · exact h₂ ⟨hp.trans_le hx, h₄⟩
      · exact h₂ ⟨hq, h₄⟩
    · intro h
      refine ⟨fun ⟨hp, hq⟩ ↦ h (Or.inl ⟨hp, Or.inl hq⟩), ?_⟩
      rintro ⟨hp, hq⟩
      rcases lt_or_ge p.1 x₁ with hlt | hge
      · exact h (Or.inl ⟨hlt, Or.inr hq⟩)
      · exact h (Or.inr ⟨⟨hge, hp⟩, hq⟩)
  have hymax : max y₁ y₂ ∈ Icc 0 1 := ⟨hy₁.1.trans (le_max_left _ _), max_le hy₁.2 hy₂.2⟩
  rw [heq, measure_compl (hA.union hB) (measure_ne_top _ _), measure_univ,
    measure_union hdisj hB]
  dsimp only [A, B]
  rw [unitScorePairLaw, Measure.prod_prod, Measure.prod_prod, unitScoreLaw_Iio_of_mem_Icc hx₁,
    unitScoreLaw_Iio_of_mem_Icc hymax, unitScoreLaw_Ico_of_mem_Icc hx₁.1 hx₂.2,
    unitScoreLaw_Iio_of_mem_Icc hy₂, ← ENNReal.ofReal_mul hx₁.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr hx), ← ENNReal.ofReal_add (mul_nonneg hx₁.1 hymax.1)
      (mul_nonneg (sub_nonneg.mpr hx) hy₂.1)]

/-- The exact two-rectangle area gives a one-cell exponential upper bound. -/
theorem unitScorePairLaw_jointNonblocking_le_exp_of_le {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : x₁ ∈ Icc 0 1) (hx₂ : x₂ ∈ Icc 0 1) (hy₁ : y₁ ∈ Icc 0 1)
    (hy₂ : y₂ ∈ Icc 0 1) (hx : x₁ ≤ x₂) :
    unitScorePairLaw (jointNonblockingScoreCell x₁ y₁ x₂ y₂) ≤
      ENNReal.ofReal (Real.exp (-(x₁ * max y₁ y₂ + (x₂ - x₁) * y₂))) := by
  rw [unitScorePairLaw_jointNonblocking_of_le hx₁ hx₂ hy₁ hy₂ hx,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · exact ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg _)
  · exact add_nonneg (mul_nonneg hx₁.1 (hy₁.1.trans (le_max_left _ _)))
      (mul_nonneg (sub_nonneg.mpr hx) hy₂.1)

/-- Weak order constraints for a prescribed orientation. In `A` men prefer the left
matching; in `B` women prefer the right matching. Weak inequalities also handle common spouses. -/
def jointSpouseOrientation {μ ν : Matching n} (A B : Finset (Fin n)) :
    Set (JointSpouseScores μ ν) :=
  {d | (∀ m, if m ∈ A then jointManSpouseScoreLeft d m ≤ jointManSpouseScoreRight d m
      else jointManSpouseScoreRight d m ≤ jointManSpouseScoreLeft d m) ∧
    ∀ w, if w ∈ B then jointWomanSpouseScoreRight d w ≤ jointWomanSpouseScoreLeft d w
      else jointWomanSpouseScoreLeft d w ≤ jointWomanSpouseScoreRight d w}

/-- The four thresholds for each man and woman lie in the support of the unit score law. -/
def JointSpouseThresholdsUnit {μ ν : Matching n} (d : JointSpouseScores μ ν) : Prop :=
  (∀ m, jointManSpouseScoreLeft d m ∈ Icc 0 1 ∧ jointManSpouseScoreRight d m ∈ Icc 0 1) ∧
  (∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1 ∧ jointWomanSpouseScoreRight d w ∈ Icc 0 1)

def jointBetterMaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  min (jointManSpouseScoreLeft d m) (jointManSpouseScoreRight d m)

def jointMaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν) (m : Fin n) : ℝ :=
  max (jointManSpouseScoreLeft d m) (jointManSpouseScoreRight d m) - jointBetterMaleScore d m

def jointWorseFemaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  max (jointWomanSpouseScoreLeft d w) (jointWomanSpouseScoreRight d w)

/-- The female score from the matching in which the man has the worse partner. -/
def jointExtraFemaleThreshold {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) (m w : Fin n) : ℝ :=
  if m ∈ A then jointWomanSpouseScoreRight d w else jointWomanSpouseScoreLeft d w

/-- The cell mass is bounded by the negative exponential of its oriented blocking area. -/
theorem jointNonblockingCellAt_mass_le_orientedExp {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)}
    (hd : JointSpouseThresholdsUnit d) (ho : d ∈ jointSpouseOrientation A B)
    (q : ScorePairIndex n) :
    unitScorePairLaw (jointNonblockingCellAt d q) ≤ ENNReal.ofReal (Real.exp (-
      (jointBetterMaleScore d q.1 * jointWorseFemaleScore d q.2 +
        jointMaleScoreGap d q.1 * jointExtraFemaleThreshold d A q.1 q.2))) := by
  have hm := ho.1 q.1
  by_cases h : q.1 ∈ A
  · have hle : jointManSpouseScoreLeft d q.1 ≤ jointManSpouseScoreRight d q.1 := by
      simpa only [ite_eq_left h] using hm
    simpa only [jointNonblockingCellAt, jointBetterMaleScore, jointWorseFemaleScore,
      jointMaleScoreGap, jointExtraFemaleThreshold, ite_eq_left h, min_eq_left hle, max_eq_right hle]
      using unitScorePairLaw_jointNonblocking_le_exp_of_le (hd.1 q.1).1 (hd.1 q.1).2
        (hd.2 q.2).1 (hd.2 q.2).2 hle
  · have hle : jointManSpouseScoreRight d q.1 ≤ jointManSpouseScoreLeft d q.1 := by
      simpa only [ite_eq_right h] using hm
    have hswap : jointNonblockingCellAt d q =
        jointNonblockingScoreCell (jointManSpouseScoreRight d q.1)
          (jointWomanSpouseScoreRight d q.2) (jointManSpouseScoreLeft d q.1)
          (jointWomanSpouseScoreLeft d q.2) := Set.inter_comm _ _
    rw [hswap]
    simpa only [jointBetterMaleScore, jointWorseFemaleScore, jointMaleScoreGap,
      jointExtraFemaleThreshold, ite_eq_right h, min_eq_right hle, max_eq_left hle, max_comm]
      using unitScorePairLaw_jointNonblocking_le_exp_of_le (hd.1 q.1).2 (hd.1 q.1).1
        (hd.2 q.2).2 (hd.2 q.2).1 hle

/-- Only these one or two female columns are omitted from a given male row. -/
def pairOmittedWomen (μ ν : Matching n) (m : Fin n) : Finset (Fin n) := {μ m, ν m}

/-- Row sum over the unmarked columns. -/
def pairUnmarkedRowSum (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ w ∈ Finset.univ \ pairOmittedWomen μ ν m, y w

/-- Row deficit from the one or two spouse cells. -/
def pairRowLoss (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ w ∈ pairOmittedWomen μ ν m, y w

theorem pairUnmarkedRowSum_eq_sub (μ ν : Matching n) (m : Fin n) (y : Fin n → ℝ) :
    pairUnmarkedRowSum μ ν m y = (∑ w, y w) - pairRowLoss μ ν m y := by
  rw [pairUnmarkedRowSum, pairRowLoss, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]

private def jointOffSpouseByRow (μ ν : Matching n) :
    JointOffSpouseIndex μ ν ≃
      Σ m : Fin n, {w : Fin n // w ∈ Finset.univ \ pairOmittedWomen μ ν m} where
  toFun q := ⟨q.val.1, q.val.2, by
    simpa [JointSpouseCell, pairOmittedWomen, eq_comm] using q.property⟩
  invFun q := ⟨(q.1, q.2.val), by
    have h := (Finset.mem_sdiff.mp q.2.property).2
    simpa only [JointSpouseCell, pairOmittedWomen, Finset.mem_insert, Finset.mem_singleton,
      eq_comm] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_jointOffSpouseIndex (μ ν : Matching n) (f : Fin n → Fin n → ℝ) :
    (∑ q : JointOffSpouseIndex μ ν, f q.val.1 q.val.2) =
      ∑ m, pairUnmarkedRowSum μ ν m (f m) := by
  calc
    _ = ∑ q : Σ m : Fin n, {w : Fin n // w ∈ Finset.univ \ pairOmittedWomen μ ν m},
        f q.1 q.2.val :=
      Fintype.sum_equiv (jointOffSpouseByRow μ ν) _ _ (fun _ ↦ rfl)
    _ = _ := ?_
  rw [Fintype.sum_sigma]
  congr 1
  funext m
  exact (Finset.sum_subtype (Finset.univ \ pairOmittedWomen μ ν m)
    (fun _ ↦ Iff.rfl) (f m)).symm

/-- The pointwise fixed-pair marked density is at most the product of two exponential
row factors, with coefficients obtained by summing across unmarked columns. -/
theorem jointOffSpouseScoreLaw_nonblocking_le_rowExp {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)}
    (hd : JointSpouseThresholdsUnit d) (ho : d ∈ jointSpouseOrientation A B) :
    jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ≤ ENNReal.ofReal (Real.exp (-
      ∑ m, (jointBetterMaleScore d m * pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d) +
        jointMaleScoreGap d m * pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m)))) := by
  let e (m w : Fin n) := jointBetterMaleScore d m * jointWorseFemaleScore d w +
    jointMaleScoreGap d m * jointExtraFemaleThreshold d A m w
  rw [jointOffSpouseScoreLaw_nonblocking]
  calc
    _ ≤ ∏ q : JointOffSpouseIndex μ ν, ENNReal.ofReal (Real.exp (-e q.val.1 q.val.2)) :=
      Finset.prod_le_prod fun q _ ↦ jointNonblockingCellAt_mass_le_orientedExp hd ho q.val
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le), ← Real.exp_sum]
      simp only [Finset.sum_neg_distrib]
      rw [sum_jointOffSpouseIndex μ ν e]
      congr 3
      apply Finset.sum_congr rfl
      intro m _
      simp only [pairUnmarkedRowSum, e, Finset.sum_add_distrib, Finset.mul_sum]

private theorem pairRowLoss_le_two_scores (μ ν : Matching n) (m : Fin n)
    {y : Fin n → ℝ} (hy : ∀ w, 0 ≤ y w) :
    pairRowLoss μ ν m y ≤ y (μ m) + y (ν m) := by
  by_cases h : μ m = ν m
  · simp only [pairRowLoss, pairOmittedWomen, h, Finset.insert_eq_of_mem, Finset.mem_singleton,
      Finset.sum_singleton]
    linarith [hy (ν m)]
  · simp [pairRowLoss, pairOmittedWomen, h]

private theorem pairRowLoss_sum_le (μ ν : Matching n) (I : Finset (Fin n))
    {y : Fin n → ℝ} (hy : ∀ w, 0 ≤ y w) :
    (∑ m ∈ I, pairRowLoss μ ν m y) ≤ 2 * ∑ w, y w := by
  calc
    _ ≤ ∑ m ∈ I, (y (μ m) + y (ν m)) :=
      Finset.sum_le_sum fun m _ ↦ pairRowLoss_le_two_scores μ ν m hy
    _ ≤ ∑ m, (y (μ m) + y (ν m)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun m _ _ ↦
        add_nonneg (hy (μ m)) (hy (ν m))
    _ = _ := by
      rw [Finset.sum_add_distrib, Equiv.sum_comp μ y, Equiv.sum_comp ν y, two_mul]

/-- The row exclusions cost at most a universal factor for each family of rates. -/
theorem pairLaplace_unmarkedRowSum_product (μ ν : Matching n) (I : Finset (Fin n))
    {y : Fin n → ℝ} (hy : ∀ w, y w ∈ Icc 0 1) :
    (∏ m ∈ I, pairLaplace (pairUnmarkedRowSum μ ν m y)) ≤
      Real.exp 24 * pairLaplace (∑ w, y w) ^ I.card := by
  simp_rw [pairUnmarkedRowSum_eq_sub]
  refine pairLaplace_omission_product I _ (fun m _ ↦ Finset.sum_nonneg fun w _ ↦ (hy w).1)
    (fun m _ ↦ ?_) (pairRowLoss_sum_le μ ν I (fun w ↦ (hy w).1))
  have hm := pairRowLoss_le_two_scores μ ν m (fun w ↦ (hy w).1)
  linarith [(hy (μ m)).2, (hy (ν m)).2]

def jointBetterFemaleScore {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  min (jointWomanSpouseScoreLeft d w) (jointWomanSpouseScoreRight d w)

def jointFemaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν) (w : Fin n) : ℝ :=
  jointWorseFemaleScore d w - jointBetterFemaleScore d w

/-- The three score sums `ξ, η, ζ`: female minima, gaps on `B`, and gaps off `B`. -/
def jointFemaleAggregate {μ ν : Matching n} (d : JointSpouseScores μ ν) (B : Finset (Fin n)) :
    ℝ × ℝ × ℝ :=
  (∑ w, jointBetterFemaleScore d w,
    ∑ w ∈ B, jointFemaleScoreGap d w,
    ∑ w ∈ Finset.univ \ B, jointFemaleScoreGap d w)

private theorem jointFemale_sum_left_right {μ ν : Matching n}
    {d : JointSpouseScores μ ν} {A B : Finset (Fin n)} (ho : d ∈ jointSpouseOrientation A B) :
    (∑ w, jointWomanSpouseScoreLeft d w) =
        (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 ∧
      (∑ w, jointWomanSpouseScoreRight d w) =
        (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.2 := by
  have hL (w : Fin n) : jointWomanSpouseScoreLeft d w = jointBetterFemaleScore d w +
      if w ∈ B then jointFemaleScoreGap d w else 0 := by
    have h := ho.2 w
    by_cases hw : w ∈ B
    · simp only [ite_eq_left hw] at h ⊢
      simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore,
        min_eq_right h, max_eq_left h]
    · simp only [ite_eq_right hw] at h ⊢
      simp [jointBetterFemaleScore, min_eq_left h]
  have hR (w : Fin n) : jointWomanSpouseScoreRight d w = jointBetterFemaleScore d w +
      if w ∈ Finset.univ \ B then jointFemaleScoreGap d w else 0 := by
    have h := ho.2 w
    by_cases hw : w ∈ B
    · simp only [ite_eq_left hw] at h
      simp [jointBetterFemaleScore, hw, min_eq_right h]
    · simp only [ite_eq_right hw] at h
      simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore, hw,
        min_eq_left h, max_eq_right h]
  constructor
  · simp_rw [hL, Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [jointFemaleAggregate]
  · simp_rw [hR, Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [jointFemaleAggregate, Finset.sdiff_eq_filter]

private theorem jointFemale_sum_worse {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (B : Finset (Fin n)) :
    (∑ w, jointWorseFemaleScore d w) =
      (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 +
        (jointFemaleAggregate d B).2.2 := by
  have h (w : Fin n) :
      jointWorseFemaleScore d w = jointBetterFemaleScore d w + jointFemaleScoreGap d w := by
    simp [jointFemaleScoreGap]
  simp only [h, Finset.sum_add_distrib, jointFemaleAggregate]
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ B)]
  ring

/-- The aggregate kernel in Lennon's (4.1.6). -/
noncomputable def pairAggregateLaplace (n u v : ℕ) (s : ℝ × ℝ × ℝ) : ℝ :=
  pairLaplace (s.1 + s.2.1 + s.2.2) ^ n *
    pairLaplace (s.1 + s.2.2) ^ u * pairLaplace (s.1 + s.2.1) ^ v

/-- The product of the row Laplace factors is bounded by the kernel of the three female sums.
The sets `I, J` are the two groups of moved men; their cardinalities are the gap exponents. -/
theorem pairLaplace_rows_le_aggregate {μ ν : Matching n} {d : JointSpouseScores μ ν}
    {A B : Finset (Fin n)} (hd : JointSpouseThresholdsUnit d)
    (ho : d ∈ jointSpouseOrientation A B) (I J : Finset (Fin n)) :
    (∏ m, pairLaplace (pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d))) *
        (∏ m ∈ I, pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreRight d))) *
        (∏ m ∈ J, pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreLeft d))) ≤
      Real.exp 72 * pairAggregateLaplace n I.card J.card (jointFemaleAggregate d B) := by
  have hW (w : Fin n) : jointWorseFemaleScore d w ∈ Icc 0 1 :=
    ⟨(hd.2 w).1.1.trans (le_max_left _ _), max_le (hd.2 w).1.2 (hd.2 w).2.2⟩
  have h₀ := pairLaplace_unmarkedRowSum_product μ ν Finset.univ hW
  have h₁ := pairLaplace_unmarkedRowSum_product μ ν I (fun w ↦ (hd.2 w).2)
  have h₂ := pairLaplace_unmarkedRowSum_product μ ν J (fun w ↦ (hd.2 w).1)
  rw [Finset.card_univ, Fintype.card_fin, jointFemale_sum_worse d B] at h₀
  rw [(jointFemale_sum_left_right ho).2] at h₁
  rw [(jointFemale_sum_left_right ho).1] at h₂
  have hle := mul_le_mul
    (mul_le_mul h₀ h₁ (Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _)))
    h₂ (Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _)
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _))
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (pairLaplace_nonneg _) _)))
  apply hle.trans_eq
  rw [show (72 : ℝ) = 24 + 24 + 24 by norm_num, Real.exp_add, Real.exp_add,
    pairAggregateLaplace]
  ring

private theorem measurable_jointManSpouseScoreLeft (μ ν : Matching n) (m : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointManSpouseScoreLeft d m) :=
  measurable_fst.comp (measurable_pi_apply _)

private theorem measurable_jointManSpouseScoreRight (μ ν : Matching n) (m : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointManSpouseScoreRight d m) :=
  measurable_fst.comp (measurable_pi_apply _)

private theorem measurable_jointWomanSpouseScoreLeft (μ ν : Matching n) (w : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointWomanSpouseScoreLeft d w) :=
  measurable_snd.comp (measurable_pi_apply _)

private theorem measurable_jointWomanSpouseScoreRight (μ ν : Matching n) (w : Fin n) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointWomanSpouseScoreRight d w) :=
  measurable_snd.comp (measurable_pi_apply _)

theorem measurableSet_jointSpouseOrientation (μ ν : Matching n) (A B : Finset (Fin n)) :
    MeasurableSet (jointSpouseOrientation (μ := μ) (ν := ν) A B) := by
  unfold jointSpouseOrientation
  rw [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun m ↦ ?_).inter (MeasurableSet.iInter fun w ↦ ?_)
  · by_cases hm : m ∈ A
    · simpa only [ite_eq_left hm] using measurableSet_le (measurable_jointManSpouseScoreLeft μ ν m)
        (measurable_jointManSpouseScoreRight μ ν m)
    · simpa only [ite_eq_right hm] using measurableSet_le (measurable_jointManSpouseScoreRight μ ν m)
        (measurable_jointManSpouseScoreLeft μ ν m)
  · by_cases hw : w ∈ B
    · simpa only [ite_eq_left hw] using measurableSet_le (measurable_jointWomanSpouseScoreRight μ ν w)
        (measurable_jointWomanSpouseScoreLeft μ ν w)
    · simpa only [ite_eq_right hw] using measurableSet_le (measurable_jointWomanSpouseScoreLeft μ ν w)
        (measurable_jointWomanSpouseScoreRight μ ν w)

theorem measurable_jointFemaleAggregate (μ ν : Matching n) (B : Finset (Fin n)) :
    Measurable (fun d : JointSpouseScores μ ν ↦ jointFemaleAggregate d B) := by
  have hL := measurable_jointWomanSpouseScoreLeft μ ν
  have hR := measurable_jointWomanSpouseScoreRight μ ν
  have hb (w : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦ jointBetterFemaleScore d w) :=
    (hL w).min (hR w)
  have hg (w : Fin n) : Measurable (fun d : JointSpouseScores μ ν ↦ jointFemaleScoreGap d w) :=
    ((hL w).max (hR w)).sub (hb w)
  exact (Finset.measurable_sum _ fun w _ ↦ hb w).prodMk
    ((Finset.measurable_sum _ fun w _ ↦ hg w).prodMk (Finset.measurable_sum _ fun w _ ↦ hg w))

theorem ae_jointSpouseThresholdsUnit (μ ν : Matching n) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, JointSpouseThresholdsUnit d := by
  have h : ∀ᵐ p ∂unitScorePairLaw, p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    have h₁ : ∀ᵐ t ∂unitScoreLaw, t ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    exact (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Icc.prod measurableSet_Icc)).mpr
      (h₁.mono fun _ ht ↦ h₁.mono fun _ hs ↦ ⟨ht, hs⟩)
  have hd : ∀ᵐ d ∂jointSpouseScoreLaw μ ν,
      ∀ q, d q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ae_all_iff.mpr fun q ↦ (measurePreserving_eval (fun _ ↦ unitScorePairLaw) q).quasiMeasurePreserving.ae h
  filter_upwards [hd] with d h
  exact ⟨fun m ↦ ⟨(h ⟨(m, μ m), Or.inl rfl⟩).1, (h ⟨(m, ν m), Or.inr rfl⟩).1⟩,
    fun w ↦ ⟨(h ⟨(μ.symm w, w), Or.inl (μ.apply_symm_apply w)⟩).2,
      (h ⟨(ν.symm w, w), Or.inr (ν.apply_symm_apply w)⟩).2⟩⟩

/-- The measurable event of joint stability with the indicated marked orientation. -/
def twoStableOrientationEvent (μ ν : Matching n) (A B : Finset (Fin n)) : Set (ScoreProfile n) :=
  {x | IsScoreStable x μ ∧ IsScoreStable x ν ∧
    (splitTwoMatchingScores μ ν x).1 ∈ jointSpouseOrientation A B}

/-- The exponential upper integrand for a fixed pair, before integrating the male scores. -/
noncomputable def orientedPairRowExp {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-
    ∑ m, (jointBetterMaleScore d m * pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d) +
      jointMaleScoreGap d m * pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m))))

/-- Fixed-pair score disintegration yields the exponential upper integral on the actual
orientation event, with any nonnegative measurable weight of the three female score sums. -/
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_rowExp (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ d in jointSpouseOrientation A B, g (jointFemaleAggregate d B) * orientedPairRowExp d A
        ∂jointSpouseScoreLaw μ ν := by
  let f (x : ScoreProfile n) := g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B)
  have hf : Measurable f := hg.comp ((measurable_jointFemaleAggregate μ ν B).comp
    (measurable_fst.comp (splitTwoMatchingScores μ ν).measurable))
  let C := jointSpouseOrientation (μ := μ) (ν := ν) A B
  have hC : MeasurableSet C := measurableSet_jointSpouseOrientation μ ν A B
  change (∫⁻ x in _, f x ∂continuousScoreLaw n) ≤ _
  rw [twoStableOrientationEvent, continuousScoreLaw_lintegral_twoStable μ ν hC hf]
  have heq (d : JointSpouseScores μ ν) :
      (∫⁻ v, f ((splitTwoMatchingScores μ ν).symm (d, v))
        ∂(Measure.pi (jointOffSpouseCellLaw d))) =
      g (jointFemaleAggregate d B) *
        jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) := by
    simp only [f, MeasurableEquiv.apply_symm_apply, lintegral_const]
    rw [← jointOffSpouseScoreLaw_restrict_nonblocking, Measure.restrict_apply_univ]
  simp_rw [heq]
  calc
    _ ≤ ∫⁻ d in C, g (jointFemaleAggregate d B) *
        jointOffSpouseScoreLaw μ ν (jointOffSpouseNonblocking d) ∂jointSpouseScoreLaw μ ν :=
      lintegral_mono_set Set.inter_subset_left
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae (ae_jointSpouseThresholdsUnit μ ν),
        ae_restrict_mem hC] with d hd ho
      exact mul_le_mul_right (jointOffSpouseScoreLaw_nonblocking_le_rowExp hd ho) _

/-- Product uniform measure on a finite array of scores. -/
noncomputable def pairUnitArrayLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ unitScoreLaw

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (pairUnitArrayLaw ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : ι ↦ unitScoreLaw))

private def pairUnitCube (ι : Type*) : Set (ι → ℝ) :=
  univ.pi fun _ ↦ Icc 0 1

private theorem pairUnitArrayLaw_eq_restrict (ι : Type*) [Fintype ι] :
    pairUnitArrayLaw ι = (volume : Measure (ι → ℝ)).restrict (pairUnitCube ι) :=
  (Measure.restrict_pi_pi (fun _ : ι ↦ volume) _).symm

/-- Ordered spouse scores may be replaced by the better score and the gap, enlarging
the domain to independent unit coordinates. This is a shear of the volume measure. -/
theorem pairUnitArrayLaw_lintegral_orderedGap_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (owner : κ → ι) {f : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p in {p : (ι → ℝ) × (κ → ℝ) | ∀ j, p.1 (owner j) ≤ p.2 j},
      f (p.1, fun j ↦ p.2 j - p.1 (owner j))
        ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ))) ≤
      ∫⁻ p, f p ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ)) := by
  let Ω := (ι → ℝ) × (κ → ℝ)
  let μ := (volume : Measure (ι → ℝ)).prod (volume : Measure (κ → ℝ))
  let S : Set Ω := {p | ∀ j, p.1 (owner j) ≤ p.2 j}
  let T : Set Ω := pairUnitCube ι ×ˢ pairUnitCube κ
  let F : Ω → Ω := fun p ↦ (p.1, p.2 - fun j ↦ p.1 (owner j))
  have hS : MeasurableSet S := by
    rw [show S = ⋂ j : κ, {p : Ω | p.1 (owner j) ≤ p.2 j} from Set.ofPred_forall _]
    exact MeasurableSet.iInter fun j ↦ measurableSet_le
      ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)
  have hT : MeasurableSet T :=
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).prod
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)
  have hF : MeasurePreserving F μ μ := by
    have hm : Measurable (fun p : Ω ↦ p.2 - fun j ↦ p.1 (owner j)) :=
      measurable_snd.sub (Measurable.of_eval fun _ ↦
        (measurable_pi_apply _).comp measurable_fst)
    exact (MeasurePreserving.id (volume : Measure (ι → ℝ))).skew_product hm
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [sub_eq_add_neg] using
          (measurePreserving_add_right (volume : Measure (κ → ℝ))
            (-(fun j ↦ x (owner j)))).map_eq)
  have hsub : S ∩ T ⊆ F ⁻¹' T := by
    rintro ⟨x, y⟩ ⟨hxy, hx, hy⟩
    refine ⟨hx, Set.mem_univ_pi.mpr fun j ↦ ?_⟩
    change y j - x (owner j) ∈ Icc 0 1
    exact ⟨sub_nonneg.mpr (hxy j), sub_le_self _ ((Set.mem_univ_pi.mp hx (owner j)).1)
      |>.trans ((Set.mem_univ_pi.mp hy j).2)⟩
  change (∫⁻ p in S, f (F p) ∂_) ≤ _
  rw [pairUnitArrayLaw_eq_restrict, pairUnitArrayLaw_eq_restrict, Measure.prod_restrict,
    Measure.restrict_restrict hS]
  change (∫⁻ p in S ∩ T, f (F p) ∂μ) ≤ ∫⁻ p in T, f p ∂μ
  exact (lintegral_mono_set hsub).trans_eq (hF.setLIntegral_comp_preimage hT hf)

private noncomputable def pairExpSum {α : Type*} [Fintype α] (r : α → ℝ) (x : α → ℝ) :=
  ENNReal.ofReal (Real.exp (-(∑ i, x i * r i)))

private theorem measurable_pairExpSum {α : Type*} [Fintype α] (r : α → ℝ) :
    Measurable (pairExpSum r) := by
  apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  exact Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).mul_const _

private theorem pairUnitArrayLaw_lintegral_exp_sum {α : Type*} [Fintype α] (r : α → ℝ) :
    (∫⁻ x, pairExpSum r x ∂pairUnitArrayLaw α) = ENNReal.ofReal (∏ i, pairLaplace (r i)) := by
  let k (i : α) (t : ℝ) := ENNReal.ofReal (Real.exp (-(t * r i)))
  have hk (i : α) : Measurable (k i) := by unfold k; fun_prop
  have heq (x : α → ℝ) : pairExpSum r x = ∏ i, k i (x i) := by
    rw [pairExpSum, ← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
    exact fun _ _ ↦ (Real.exp_pos _).le
  have hcoord (i : α) : (∫⁻ x : α → ℝ, k i (x i) ∂pairUnitArrayLaw α) =
      ENNReal.ofReal (pairLaplace (r i)) := by
    unfold pairUnitArrayLaw
    rw [(measurePreserving_eval (fun _ : α ↦ unitScoreLaw) i).lintegral_comp (hk i)]
    have hk' (t : ℝ) : k i t = ENNReal.ofReal (Real.exp (-r i * t)) := by
      dsimp only [k]
      ring_nf
    simp_rw [hk']
    exact (ofReal_integral_eq_lintegral_ofReal (pairLaplace_integrable _)
      (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)).symm
  simp_rw [heq]
  change (∫⁻ x : α → ℝ, ∏ i, k i (x i) ∂Measure.pi (fun _ : α ↦ unitScoreLaw)) = _
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (ProbabilityTheory.iIndepFun_pi fun i ↦ (hk i).aemeasurable)
    (fun i ↦ (hk i).comp (measurable_pi_apply i))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ pairLaplace_nonneg _)]
  exact Finset.prod_congr rfl fun i _ ↦ hcoord i

/-- Fubini for the male scores in the relaxed cube: each better score and each gap
contributes its one-dimensional Laplace transform. -/
theorem pairUnitArrayLaw_lintegral_exp_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    (∫⁻ p : (ι → ℝ) × (κ → ℝ), ENNReal.ofReal (Real.exp
      (-(∑ i, p.1 i * a i) - ∑ j, p.2 j * b j))
      ∂((pairUnitArrayLaw ι).prod (pairUnitArrayLaw κ))) =
      ENNReal.ofReal ((∏ i, pairLaplace (a i)) * ∏ j, pairLaplace (b j)) := by
  have heq (p : (ι → ℝ) × (κ → ℝ)) : ENNReal.ofReal (Real.exp
      (-(∑ i, p.1 i * a i) - ∑ j, p.2 j * b j)) = pairExpSum a p.1 * pairExpSum b p.2 := by
    rw [pairExpSum, pairExpSum, sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [heq]
  rw [lintegral_prod_mul (measurable_pairExpSum a).aemeasurable (measurable_pairExpSum b).aemeasurable,
    pairUnitArrayLaw_lintegral_exp_sum, pairUnitArrayLaw_lintegral_exp_sum, ENNReal.ofReal_mul]
  exact Finset.prod_nonneg fun _ _ ↦ pairLaplace_nonneg _

/-- The male rows with two genuinely different spouse cells. -/
abbrev PairMovedMan (μ ν : Matching n) := {m : Fin n // μ m ≠ ν m}

private def pairBetterSpouseCell (μ ν : Matching n) (A : Finset (Fin n))
    (m : Fin n) : JointSpouseIndex μ ν :=
  if m ∈ A then ⟨(m, μ m), Or.inl rfl⟩ else ⟨(m, ν m), Or.inr rfl⟩

private def pairWorseSpouseCell (μ ν : Matching n) (A : Finset (Fin n))
    (m : Fin n) : JointSpouseIndex μ ν :=
  if m ∈ A then ⟨(m, ν m), Or.inr rfl⟩ else ⟨(m, μ m), Or.inl rfl⟩

private theorem pairBetterSpouseCell_row (μ ν : Matching n) (A : Finset (Fin n)) (m : Fin n) :
    (pairBetterSpouseCell μ ν A m).val.1 = m := by
  unfold pairBetterSpouseCell
  split <;> rfl

private theorem pairWorseSpouseCell_row (μ ν : Matching n) (A : Finset (Fin n)) (m : Fin n) :
    (pairWorseSpouseCell μ ν A m).val.1 = m := by
  unfold pairWorseSpouseCell
  split <;> rfl

private theorem pairBetterSpouseCell_ne_worse (μ ν : Matching n) (A : Finset (Fin n))
    {m : Fin n} (hm : μ m ≠ ν m) :
    pairBetterSpouseCell μ ν A m ≠ pairWorseSpouseCell μ ν A m := by
  by_cases hA : m ∈ A
  · intro h
    have h' := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.2) h
    exact hm (by simpa [pairBetterSpouseCell, pairWorseSpouseCell, hA] using h')
  · intro h
    have h' := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.2) h
    exact hm (by simpa [pairBetterSpouseCell, pairWorseSpouseCell, hA, eq_comm] using h')

private noncomputable def pairSpouseCellByRow (μ ν : Matching n) (A : Finset (Fin n)) :
    (Fin n ⊕ PairMovedMan μ ν) ≃ JointSpouseIndex μ ν := by
  let F : Fin n ⊕ PairMovedMan μ ν → JointSpouseIndex μ ν :=
    Sum.elim (pairBetterSpouseCell μ ν A) (fun m ↦ pairWorseSpouseCell μ ν A m.val)
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro i j hij
    have h := congrArg (fun q : JointSpouseIndex μ ν ↦ q.val.1) hij
    rcases i with i | i <;> rcases j with j | j
    · simpa only [F, Sum.elim_inl, pairBetterSpouseCell_row, Sum.inl.injEq] using h
    · have h' : i = j.val := by
        simpa only [F, Sum.elim_inl, Sum.elim_inr, pairBetterSpouseCell_row,
          pairWorseSpouseCell_row] using h
      subst i
      exact (pairBetterSpouseCell_ne_worse μ ν A j.property hij).elim
    · have h' : i.val = j := by
        simpa only [F, Sum.elim_inl, Sum.elim_inr, pairBetterSpouseCell_row,
          pairWorseSpouseCell_row] using h
      subst j
      exact (pairBetterSpouseCell_ne_worse μ ν A i.property hij.symm).elim
    · congr 1
      apply Subtype.ext
      simpa only [F, Sum.elim_inr, pairWorseSpouseCell_row] using h
  · rintro ⟨⟨m, w⟩, hw⟩
    rcases hw with (h : μ m = w) | (h : ν m = w)
    · subst w
      by_cases hm : m ∈ A
      · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm]⟩
      · by_cases heq : μ m = ν m
        · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm, heq]⟩
        · exact ⟨.inr ⟨m, heq⟩, by simp [F, pairWorseSpouseCell, hm]⟩
    · subst w
      by_cases hm : m ∈ A
      · by_cases heq : μ m = ν m
        · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm, heq]⟩
        · exact ⟨.inr ⟨m, heq⟩, by simp [F, pairWorseSpouseCell, hm]⟩
      · exact ⟨.inl m, by simp [F, pairBetterSpouseCell, hm]⟩

private def pairSpouseCellTranspose (μ ν : Matching n) :
    JointSpouseIndex μ.symm ν.symm ≃ JointSpouseIndex μ ν where
  toFun q := ⟨q.val.swap, by
    rcases q.property with h | h
    · exact Or.inl ((μ.symm_apply_eq).mp h).symm
    · exact Or.inr ((ν.symm_apply_eq).mp h).symm⟩
  invFun q := ⟨q.val.swap, by
    rcases q.property with h | h
    · exact Or.inl ((μ.symm_apply_eq).mpr h.symm)
    · exact Or.inr ((ν.symm_apply_eq).mpr h.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The female columns with two genuinely different spouse cells. -/
abbrev PairMovedWoman (μ ν : Matching n) := PairMovedMan μ.symm ν.symm

private noncomputable def pairSpouseCellByColumn (μ ν : Matching n) (B : Finset (Fin n)) :
    (Fin n ⊕ PairMovedWoman μ ν) ≃ JointSpouseIndex μ ν :=
  (pairSpouseCellByRow μ.symm ν.symm (Finset.univ \ B)).trans (pairSpouseCellTranspose μ ν)

/-- Better and worse spouse score arrays, with no duplicate for a common spouse. -/
abbrev PairOrderedSpouseArrays (n : ℕ) (κ : Type*) := (Fin n → ℝ) × (κ → ℝ)

@[no_expose]
noncomputable def pairSplitSpouseScores (μ ν : Matching n) (A B : Finset (Fin n)) :
    JointSpouseScores μ ν ≃ᵐ
      PairOrderedSpouseArrays n (PairMovedMan μ ν) ×
        PairOrderedSpouseArrays n (PairMovedWoman μ ν) :=
  let J := JointSpouseIndex μ ν
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ J).trans <|
    ((MeasurableEquiv.arrowCongr' (pairSpouseCellByRow μ ν A).symm (.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ)).prodCongr
    ((MeasurableEquiv.arrowCongr' (pairSpouseCellByColumn μ ν B).symm (.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ ↦ ℝ))

noncomputable def pairOrderedSpouseLaw (n : ℕ) (κ : Type*) [Fintype κ] :
    Measure (PairOrderedSpouseArrays n κ) :=
  (pairUnitArrayLaw (Fin n)).prod (pairUnitArrayLaw κ)

instance (n : ℕ) (κ : Type*) [Fintype κ] : IsProbabilityMeasure (pairOrderedSpouseLaw n κ) :=
  inferInstanceAs (IsProbabilityMeasure ((pairUnitArrayLaw (Fin n)).prod (pairUnitArrayLaw κ)))

theorem measurePreserving_pairSplitSpouseScores (μ ν : Matching n) (A B : Finset (Fin n)) :
    MeasurePreserving (pairSplitSpouseScores μ ν A B) (jointSpouseScoreLaw μ ν)
      ((pairOrderedSpouseLaw n (PairMovedMan μ ν)).prod
        (pairOrderedSpouseLaw n (PairMovedWoman μ ν))) := by
  let J := JointSpouseIndex μ ν
  have hM := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ PairMovedMan μ ν ↦ unitScoreLaw)).comp
      (measurePreserving_arrowCongr' (fun _ ↦ unitScoreLaw)
        (fun _ : Fin n ⊕ PairMovedMan μ ν ↦ unitScoreLaw)
        (pairSpouseCellByRow μ ν A).symm (.refl ℝ) (fun _ ↦ MeasurePreserving.id _))
  have hW := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ PairMovedWoman μ ν ↦ unitScoreLaw)).comp
      (measurePreserving_arrowCongr' (fun _ ↦ unitScoreLaw)
        (fun _ : Fin n ⊕ PairMovedWoman μ ν ↦ unitScoreLaw)
        (pairSpouseCellByColumn μ ν B).symm (.refl ℝ) (fun _ ↦ MeasurePreserving.id _))
  exact (hM.prod hW).comp (measurePreserving_arrowProdEquivProdArrow ℝ ℝ J
    (fun _ ↦ unitScoreLaw) (fun _ ↦ unitScoreLaw))

theorem pairSplitSpouseScores_male_first (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (m : Fin n) :
    (pairSplitSpouseScores μ ν A B d).1.1 m =
      if m ∈ A then jointManSpouseScoreLeft d m else jointManSpouseScoreRight d m := by
  change (d (pairBetterSpouseCell μ ν A m)).1 = _
  by_cases h : m ∈ A <;> simp [pairBetterSpouseCell, h, jointManSpouseScoreLeft,
    jointManSpouseScoreRight]

theorem pairSplitSpouseScores_male_second (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (m : PairMovedMan μ ν) :
    (pairSplitSpouseScores μ ν A B d).1.2 m =
      if m.val ∈ A then jointManSpouseScoreRight d m.val else jointManSpouseScoreLeft d m.val := by
  change (d (pairWorseSpouseCell μ ν A m.val)).1 = _
  by_cases h : m.val ∈ A <;> simp [pairWorseSpouseCell, h, jointManSpouseScoreLeft,
    jointManSpouseScoreRight]

theorem pairSplitSpouseScores_female_first (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (w : Fin n) :
    (pairSplitSpouseScores μ ν A B d).2.1 w =
      if w ∈ B then jointWomanSpouseScoreRight d w else jointWomanSpouseScoreLeft d w := by
  change (d (pairSpouseCellTranspose μ ν
    (pairBetterSpouseCell μ.symm ν.symm (Finset.univ \ B) w))).2 = _
  by_cases h : w ∈ B <;> simp [pairBetterSpouseCell, h, pairSpouseCellTranspose,
    jointWomanSpouseScoreLeft, jointWomanSpouseScoreRight]

theorem pairSplitSpouseScores_female_second (μ ν : Matching n) (A B : Finset (Fin n))
    (d : JointSpouseScores μ ν) (w : PairMovedWoman μ ν) :
    (pairSplitSpouseScores μ ν A B d).2.2 w =
      if w.val ∈ B then jointWomanSpouseScoreLeft d w.val else jointWomanSpouseScoreRight d w.val := by
  change (d (pairSpouseCellTranspose μ ν
    (pairWorseSpouseCell μ.symm ν.symm (Finset.univ \ B) w.val))).2 = _
  by_cases h : w.val ∈ B <;> simp [pairWorseSpouseCell, h, pairSpouseCellTranspose,
    jointWomanSpouseScoreLeft, jointWomanSpouseScoreRight]

def pairOrderedArraySet {κ : Type*} (owner : κ → Fin n) :
    Set (PairOrderedSpouseArrays n κ) :=
  {p | ∀ j, p.1 (owner j) ≤ p.2 j}

private theorem measurableSet_pairOrderedArraySet {κ : Type*} [Fintype κ]
    (owner : κ → Fin n) : MeasurableSet (pairOrderedArraySet owner) := by
  unfold pairOrderedArraySet
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun _ ↦ measurableSet_le
    ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_snd)

private theorem jointWomanSpouseScoreLeft_eq_right {μ ν : Matching n} (d : JointSpouseScores μ ν)
    {w : Fin n} (hw : μ.symm w = ν.symm w) :
    jointWomanSpouseScoreLeft d w = jointWomanSpouseScoreRight d w := by
  unfold jointWomanSpouseScoreLeft jointWomanSpouseScoreRight
  exact congrArg (fun q : JointSpouseIndex μ ν ↦ (d q).2)
    (Subtype.ext (Prod.ext hw rfl))

private theorem jointSpouseOrientation_iff_pairOrdered {μ ν : Matching n}
    (A B : Finset (Fin n)) (d : JointSpouseScores μ ν) :
    d ∈ jointSpouseOrientation A B ↔
      (pairSplitSpouseScores μ ν A B d).1 ∈
        pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val) ∧
      (pairSplitSpouseScores μ ν A B d).2 ∈
        pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr
  · change (∀ m, _) ↔ ∀ m : PairMovedMan μ ν, _
    simp only [pairSplitSpouseScores_male_first, pairSplitSpouseScores_male_second]
    constructor
    · intro h m
      by_cases hm : m.val ∈ A <;> simpa only [hm, ite_true, ite_false] using h m.val
    · intro h m
      by_cases hne : μ m = ν m
      · simp [jointManSpouseScoreLeft_eq_right d hne]
      · by_cases hm : m ∈ A
        · simpa only [ite_eq_left hm] using h ⟨m, hne⟩
        · simpa only [ite_eq_right hm] using h ⟨m, hne⟩
  · change (∀ w, _) ↔ ∀ w : PairMovedWoman μ ν, _
    simp only [pairSplitSpouseScores_female_first, pairSplitSpouseScores_female_second]
    constructor
    · intro h w
      by_cases hw : w.val ∈ B <;> simpa only [hw, ite_true, ite_false] using h w.val
    · intro h w
      by_cases hne : μ.symm w = ν.symm w
      · simp [jointWomanSpouseScoreLeft_eq_right d hne]
      · by_cases hw : w ∈ B
        · simpa only [ite_eq_left hw] using h ⟨w, hne⟩
        · simpa only [ite_eq_right hw] using h ⟨w, hne⟩

private theorem jointBetterMaleScore_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (m : Fin n) :
    jointBetterMaleScore d m = (pairSplitSpouseScores μ ν A B d).1.1 m := by
  have h := ho.1 m
  rw [pairSplitSpouseScores_male_first, jointBetterMaleScore]
  by_cases hm : m ∈ A
  · simp only [ite_eq_left hm] at h ⊢
    exact min_eq_left h
  · simp only [ite_eq_right hm] at h ⊢
    exact min_eq_right h

private theorem jointMaleScoreGap_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (m : PairMovedMan μ ν) :
    jointMaleScoreGap d m.val =
      (pairSplitSpouseScores μ ν A B d).1.2 m - (pairSplitSpouseScores μ ν A B d).1.1 m.val := by
  have h := ho.1 m.val
  rw [jointMaleScoreGap, jointBetterMaleScore_pairSplit ho, pairSplitSpouseScores_male_second]
  by_cases hm : m.val ∈ A
  · simp only [ite_eq_left hm] at h ⊢
    rw [max_eq_right h]
  · simp only [ite_eq_right hm] at h ⊢
    rw [max_eq_left h]

private theorem jointMaleScoreGap_common {μ ν : Matching n}
    (d : JointSpouseScores μ ν) {m : Fin n} (hm : μ m = ν m) : jointMaleScoreGap d m = 0 := by
  simp [jointMaleScoreGap, jointBetterMaleScore, jointManSpouseScoreLeft_eq_right d hm]

private theorem jointWomanSpouseScores_inverse_congr {μ ν : Matching n}
    (A B : Finset (Fin n)) (p q : PairOrderedSpouseArrays n (PairMovedMan μ ν))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) (w : Fin n) :
    let d := (pairSplitSpouseScores μ ν A B).symm (p, y)
    let d' := (pairSplitSpouseScores μ ν A B).symm (q, y)
    jointWomanSpouseScoreLeft d w = jointWomanSpouseScoreLeft d' w ∧
      jointWomanSpouseScoreRight d w = jointWomanSpouseScoreRight d' w := by
  let e := pairSplitSpouseScores μ ν A B
  let d := e.symm (p, y)
  let d' := e.symm (q, y)
  have h₁ := pairSplitSpouseScores_female_first μ ν A B d w
  have h₁' := pairSplitSpouseScores_female_first μ ν A B d' w
  change (e (e.symm (p, y))).2.1 w = _ at h₁
  change (e (e.symm (q, y))).2.1 w = _ at h₁'
  rw [MeasurableEquiv.apply_symm_apply] at h₁ h₁'
  by_cases hw : μ.symm w = ν.symm w
  · rw [jointWomanSpouseScoreLeft_eq_right d hw] at h₁
    rw [jointWomanSpouseScoreLeft_eq_right d' hw] at h₁'
    simp only [ite_self] at h₁ h₁'
    exact ⟨(jointWomanSpouseScoreLeft_eq_right d hw).trans
      (h₁.symm.trans (h₁'.trans (jointWomanSpouseScoreLeft_eq_right d' hw).symm)),
      h₁.symm.trans h₁'⟩
  · let j : PairMovedWoman μ ν := ⟨w, hw⟩
    have h₂ := pairSplitSpouseScores_female_second μ ν A B d j
    have h₂' := pairSplitSpouseScores_female_second μ ν A B d' j
    change (e (e.symm (p, y))).2.2 j = _ at h₂
    change (e (e.symm (q, y))).2.2 j = _ at h₂'
    rw [MeasurableEquiv.apply_symm_apply] at h₂ h₂'
    by_cases hB : w ∈ B
    · simp only [j, ite_eq_left hB] at h₁ h₁' h₂ h₂'
      exact ⟨h₂.symm.trans h₂', h₁.symm.trans h₁'⟩
    · simp only [j, ite_eq_right hB] at h₁ h₁' h₂ h₂'
      exact ⟨h₁.symm.trans h₁', h₂.symm.trans h₂'⟩

private theorem sum_jointMaleScoreGap {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (f : Fin n → ℝ) :
    (∑ m, jointMaleScoreGap d m * f m) =
      ∑ m : PairMovedMan μ ν, jointMaleScoreGap d m.val * f m.val := by
  have h (m : Fin n) : jointMaleScoreGap d m * f m =
      if μ m ≠ ν m then jointMaleScoreGap d m * f m else 0 := by
    by_cases hm : μ m = ν m
    · simp [hm, jointMaleScoreGap_common d hm]
    · simp [hm]
  calc
    _ = ∑ m, if μ m ≠ ν m then jointMaleScoreGap d m * f m else 0 :=
      Finset.sum_congr rfl fun m _ ↦ h m
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) (fun m ↦ jointMaleScoreGap d m * f m)

private theorem pairOrderedSpouseLaw_inner_le {μ ν : Matching n}
    (A B : Finset (Fin n)) (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν))
    (hy : y ∈ pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val)) :
    let e := pairSplitSpouseScores μ ν A B
    let d₀ := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
    let a m := pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d₀)
    let b (m : PairMovedMan μ ν) :=
      pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d₀ A m.val)
    (∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
      orientedPairRowExp (e.symm (p, y)) A ∂pairOrderedSpouseLaw n (PairMovedMan μ ν)) ≤
      ENNReal.ofReal ((∏ m, pairLaplace (a m)) * ∏ m, pairLaplace (b m)) := by
  dsimp only
  let e := pairSplitSpouseScores μ ν A B
  let d₀ := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
  let a m := pairUnmarkedRowSum μ ν m (jointWorseFemaleScore d₀)
  let b (m : PairMovedMan μ ν) :=
    pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d₀ A m.val)
  let f (p : PairOrderedSpouseArrays n (PairMovedMan μ ν)) :=
    ENNReal.ofReal (Real.exp (-(∑ m, p.1 m * a m) - ∑ m, p.2 m * b m))
  have hf : Measurable f := by
    unfold f
    apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.sub
      (Measurable.neg ?_) ?_))
    · exact Finset.measurable_sum _ fun _ _ ↦ ((measurable_pi_apply _).comp measurable_fst).mul_const _
    · exact Finset.measurable_sum _ fun _ _ ↦ ((measurable_pi_apply _).comp measurable_snd).mul_const _
  have hchange : (∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
      orientedPairRowExp (e.symm (p, y)) A ∂pairOrderedSpouseLaw n (PairMovedMan μ ν)) =
      ∫⁻ p in pairOrderedArraySet (fun m : PairMovedMan μ ν ↦ m.val),
        f (p.1, fun m ↦ p.2 m - p.1 m.val) ∂pairOrderedSpouseLaw n (PairMovedMan μ ν) := by
    apply setLIntegral_congr_fun (measurableSet_pairOrderedArraySet _)
    intro p hp
    let d := e.symm (p, y)
    have ho : d ∈ jointSpouseOrientation A B := (jointSpouseOrientation_iff_pairOrdered A B d).mpr
      (by simpa only [d, e, MeasurableEquiv.apply_symm_apply] using And.intro hp hy)
    have hW : jointWorseFemaleScore d = jointWorseFemaleScore d₀ := by
      funext w
      have h := jointWomanSpouseScores_inverse_congr A B p (fun _ ↦ 0, fun _ ↦ 0) y w
      exact congrArg₂ max h.1 h.2
    have hE (m : Fin n) : jointExtraFemaleThreshold d A m = jointExtraFemaleThreshold d₀ A m := by
      funext w
      have h := jointWomanSpouseScores_inverse_congr A B p (fun _ ↦ 0, fun _ ↦ 0) y w
      unfold jointExtraFemaleThreshold
      split
      · exact h.2
      · exact h.1
    change orientedPairRowExp d A = _
    unfold orientedPairRowExp f
    rw [Finset.sum_add_distrib, sum_jointMaleScoreGap]
    simp only [jointBetterMaleScore_pairSplit ho, jointMaleScoreGap_pairSplit ho,
      hW, hE, d, e, MeasurableEquiv.apply_symm_apply, a, b, neg_add_rev, sub_eq_add_neg]
    exact congrArg (fun s ↦ ENNReal.ofReal (Real.exp s)) (add_comm _ _)
  rw [hchange]
  exact (pairUnitArrayLaw_lintegral_orderedGap_le (fun m : PairMovedMan μ ν ↦ m.val) hf).trans_eq
    (pairUnitArrayLaw_lintegral_exp_sums a b)

/-- The two classes of moved male rows, determined by the prescribed orientation. -/
def pairOrientedMovedMen (μ ν : Matching n) (A : Finset (Fin n)) : Finset (Fin n) :=
  A.filter fun m ↦ μ m ≠ ν m

private theorem pairProd_moved_male_gap {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (A : Finset (Fin n)) :
    (∏ m : PairMovedMan μ ν,
      pairLaplace (pairUnmarkedRowSum μ ν m.val (jointExtraFemaleThreshold d A m.val))) =
      (∏ m ∈ pairOrientedMovedMen μ ν A,
        pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreRight d))) *
      (∏ m ∈ pairOrientedMovedMen μ ν (Finset.univ \ A),
        pairLaplace (pairUnmarkedRowSum μ ν m (jointWomanSpouseScoreLeft d))) := by
  let F m := pairLaplace (pairUnmarkedRowSum μ ν m (jointExtraFemaleThreshold d A m))
  have h₀ : (∏ m : PairMovedMan μ ν, F m.val) =
      ∏ m ∈ Finset.univ.filter (fun m ↦ μ m ≠ ν m), F m :=
    (Finset.prod_subtype _ (by simp) F).symm
  rw [h₀, ← Finset.prod_filter_mul_prod_filter_not _ (fun m ↦ m ∈ A) F]
  have h₁ : (Finset.univ.filter (fun m ↦ μ m ≠ ν m)).filter (fun m ↦ m ∈ A) =
      pairOrientedMovedMen μ ν A := by
    ext m
    simp [pairOrientedMovedMen, and_comm]
  have h₂ : (Finset.univ.filter (fun m ↦ μ m ≠ ν m)).filter (fun m ↦ m ∉ A) =
      pairOrientedMovedMen μ ν (Finset.univ \ A) := by
    ext m
    simp [pairOrientedMovedMen, and_comm]
  rw [h₁, h₂]
  congr 1
  · apply Finset.prod_congr rfl
    intro m hm
    have h := (Finset.mem_filter.mp hm).1
    have he : jointExtraFemaleThreshold d A m = jointWomanSpouseScoreRight d := by
      funext w
      simp only [jointExtraFemaleThreshold, ite_eq_left h]
    simp only [F, he]
  · apply Finset.prod_congr rfl
    intro m hm
    have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).2
    have he : jointExtraFemaleThreshold d A m = jointWomanSpouseScoreLeft d := by
      funext w
      simp only [jointExtraFemaleThreshold, ite_eq_right h]
    simp only [F, he]

private theorem pairSplitSpouseScores_thresholdsUnit {μ ν : Matching n}
    (A B : Finset (Fin n)) (d : JointSpouseScores μ ν)
    (hm₀ : ∀ m, (pairSplitSpouseScores μ ν A B d).1.1 m ∈ Icc 0 1)
    (hm₁ : ∀ m, (pairSplitSpouseScores μ ν A B d).1.2 m ∈ Icc 0 1)
    (hw₀ : ∀ w, (pairSplitSpouseScores μ ν A B d).2.1 w ∈ Icc 0 1)
    (hw₁ : ∀ w, (pairSplitSpouseScores μ ν A B d).2.2 w ∈ Icc 0 1) :
    JointSpouseThresholdsUnit d := by
  constructor
  · intro m
    have h₀ := hm₀ m
    rw [pairSplitSpouseScores_male_first] at h₀
    by_cases he : μ m = ν m
    · rw [jointManSpouseScoreLeft_eq_right d he, ite_self] at h₀
      simpa only [jointManSpouseScoreLeft_eq_right d he] using And.intro h₀ h₀
    · have h₁ := hm₁ ⟨m, he⟩
      rw [pairSplitSpouseScores_male_second] at h₁
      by_cases h : m ∈ A
      · exact ⟨by simpa only [ite_eq_left h] using h₀, by simpa only [ite_eq_left h] using h₁⟩
      · exact ⟨by simpa only [ite_eq_right h] using h₁, by simpa only [ite_eq_right h] using h₀⟩
  · intro w
    have h₀ := hw₀ w
    rw [pairSplitSpouseScores_female_first] at h₀
    by_cases he : μ.symm w = ν.symm w
    · rw [jointWomanSpouseScoreLeft_eq_right d he, ite_self] at h₀
      simpa only [jointWomanSpouseScoreLeft_eq_right d he] using And.intro h₀ h₀
    · have h₁ := hw₁ ⟨w, he⟩
      rw [pairSplitSpouseScores_female_second] at h₁
      by_cases h : w ∈ B
      · exact ⟨by simpa only [ite_eq_left h] using h₁, by simpa only [ite_eq_left h] using h₀⟩
      · exact ⟨by simpa only [ite_eq_right h] using h₀, by simpa only [ite_eq_right h] using h₁⟩

private theorem ae_pairOrderedSpouseLaw_unit (n : ℕ) (κ : Type*) [Fintype κ] :
    ∀ᵐ p ∂pairOrderedSpouseLaw n κ,
      (∀ i, p.1 i ∈ Icc 0 1) ∧ ∀ j, p.2 j ∈ Icc 0 1 := by
  rw [pairOrderedSpouseLaw, pairUnitArrayLaw_eq_restrict, pairUnitArrayLaw_eq_restrict,
    Measure.prod_restrict]
  exact (ae_restrict_mem ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).prod
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc))).mono fun _ h ↦
      ⟨Set.mem_univ_pi.mp h.1, Set.mem_univ_pi.mp h.2⟩

private theorem measurable_orientedPairRowExp (μ ν : Matching n) (A : Finset (Fin n)) :
    Measurable (fun d : JointSpouseScores μ ν ↦ orientedPairRowExp d A) := by
  have hx₁ := measurable_jointManSpouseScoreLeft μ ν
  have hx₂ := measurable_jointManSpouseScoreRight μ ν
  have hy₁ := measurable_jointWomanSpouseScoreLeft μ ν
  have hy₂ := measurable_jointWomanSpouseScoreRight μ ν
  apply ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.neg ?_))
  refine Finset.measurable_sum _ fun m _ ↦ Measurable.add (Measurable.mul
    ((hx₁ m).min (hx₂ m)) ?_) (Measurable.mul (((hx₁ m).max (hx₂ m)).sub
    ((hx₁ m).min (hx₂ m))) ?_)
  · exact Finset.measurable_sum _ fun w _ ↦ (hy₁ w).max (hy₂ w)
  · refine Finset.measurable_sum _ fun w _ ↦ ?_
    by_cases h : m ∈ A
    · simpa only [jointExtraFemaleThreshold, ite_eq_left h] using hy₂ w
    · simpa only [jointExtraFemaleThreshold, ite_eq_right h] using hy₁ w

private theorem jointFemaleAggregate_inverse_congr {μ ν : Matching n}
    (A B : Finset (Fin n)) (p q : PairOrderedSpouseArrays n (PairMovedMan μ ν))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) :
    jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm (p, y)) B =
      jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm (q, y)) B := by
  simp only [jointFemaleAggregate, jointBetterFemaleScore, jointFemaleScoreGap,
    jointWorseFemaleScore, (jointWomanSpouseScores_inverse_congr A B p q y _).1,
    (jointWomanSpouseScores_inverse_congr A B p q y _).2]

/-- The marked female aggregate expressed as a function of the raw better/worse scores alone. -/
noncomputable def pairFemaleAggregateFromOrdered {μ ν : Matching n} (A B : Finset (Fin n))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) : ℝ × ℝ × ℝ :=
  jointFemaleAggregate ((pairSplitSpouseScores μ ν A B).symm ((fun _ ↦ 0, fun _ ↦ 0), y)) B

/-- Integrate out the male coordinates. The upper kernel depends only on the three female sums. -/
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_femaleAggregate (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    let u := (pairOrientedMovedMen μ ν A).card
    let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ y in pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val),
        g (pairFemaleAggregateFromOrdered A B y) * ENNReal.ofReal
          (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromOrdered A B y))
        ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν) := by
  dsimp only
  let e := pairSplitSpouseScores μ ν A B
  let M := PairMovedMan μ ν
  let W := PairMovedWoman μ ν
  let p₀ : PairOrderedSpouseArrays n M := (fun _ ↦ 0, fun _ ↦ 0)
  let S := pairOrderedArraySet (fun m : M ↦ m.val)
  let T := pairOrderedArraySet (fun w : W ↦ w.val)
  let H (z : PairOrderedSpouseArrays n M × PairOrderedSpouseArrays n W) :=
    g (jointFemaleAggregate (e.symm z) B) * orientedPairRowExp (e.symm z) A
  have hH : Measurable H := ((hg.comp (measurable_jointFemaleAggregate μ ν B)).mul
    (measurable_orientedPairRowExp μ ν A)).comp e.symm.measurable
  have hST : e ⁻¹' (S ×ˢ T) = jointSpouseOrientation A B := by
    ext d
    exact (jointSpouseOrientation_iff_pairOrdered A B d).symm
  have hS : MeasurableSet S := measurableSet_pairOrderedArraySet _
  have hT : MeasurableSet T := measurableSet_pairOrderedArraySet _
  refine (continuousScoreLaw_lintegral_twoStableOrientation_le_rowExp μ ν A B hg).trans ?_
  have htransport := (measurePreserving_pairSplitSpouseScores μ ν A B).setLIntegral_comp_preimage
    (hS.prod hT) hH
  rw [hST] at htransport
  simp only [H, e, MeasurableEquiv.symm_apply_apply] at htransport
  rw [htransport]
  change (∫⁻ z in S ×ˢ T, H z
    ∂((pairOrderedSpouseLaw n M).prod (pairOrderedSpouseLaw n W))) ≤ _
  rw [← Measure.prod_restrict, lintegral_prod_symm' H hH]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hT,
    ae_restrict_of_ae (ae_pairOrderedSpouseLaw_unit n W)] with y hy hyu
  let d₀ := e.symm (p₀, y)
  have hunit : JointSpouseThresholdsUnit d₀ := by
    apply pairSplitSpouseScores_thresholdsUnit A B d₀
    · intro m
      simp [d₀, e, p₀]
    · intro m
      simp [d₀, e, p₀]
    · simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hyu.1
    · simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hyu.2
  have ho₀ : d₀ ∈ jointSpouseOrientation A B := by
    apply (jointSpouseOrientation_iff_pairOrdered A B d₀).mpr
    refine ⟨?_, by simpa only [d₀, e, MeasurableEquiv.apply_symm_apply] using hy⟩
    simp [d₀, e, p₀, pairOrderedArraySet]
  have hcongr (p : PairOrderedSpouseArrays n M) :
      H (p, y) = g (jointFemaleAggregate d₀ B) * orientedPairRowExp (e.symm (p, y)) A := by
    unfold H
    rw [jointFemaleAggregate_inverse_congr A B p p₀ y]
  simp_rw [hcongr]
  have hmeas : Measurable (fun p : PairOrderedSpouseArrays n M ↦
      orientedPairRowExp (e.symm (p, y)) A) :=
    (measurable_orientedPairRowExp μ ν A).comp
      (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  rw [lintegral_const_mul _ hmeas]
  apply mul_le_mul_right
  refine (pairOrderedSpouseLaw_inner_le A B y hy).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [pairProd_moved_male_gap d₀ A, ← mul_assoc]
  exact pairLaplace_rows_le_aggregate hunit ho₀ _ _

/-- The female aggregate on the relaxed cube: the second array now contains gaps,
not the raw worse spouse scores. -/
def pairFemaleAggregateFromGaps {μ ν : Matching n} (B : Finset (Fin n))
    (z : PairOrderedSpouseArrays n (PairMovedWoman μ ν)) : ℝ × ℝ × ℝ :=
  (∑ w, z.1 w,
    ∑ w : PairMovedWoman μ ν with w.val ∈ B, z.2 w,
    ∑ w : PairMovedWoman μ ν with w.val ∉ B, z.2 w)

theorem measurable_pairFemaleAggregateFromGaps (μ ν : Matching n) (B : Finset (Fin n)) :
    Measurable (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B) := by
  exact (Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_fst).prodMk
    ((Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_snd).prodMk
      (Finset.measurable_sum _ fun w _ ↦ (measurable_pi_apply w).comp measurable_snd))

private theorem jointBetterFemaleScore_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (w : Fin n) :
    jointBetterFemaleScore d w = (pairSplitSpouseScores μ ν A B d).2.1 w := by
  have h := ho.2 w
  rw [pairSplitSpouseScores_female_first, jointBetterFemaleScore]
  by_cases hw : w ∈ B
  · simp only [ite_eq_left hw] at h ⊢
    exact min_eq_right h
  · simp only [ite_eq_right hw] at h ⊢
    exact min_eq_left h

private theorem jointFemaleScoreGap_pairSplit {μ ν : Matching n}
    {A B : Finset (Fin n)} {d : JointSpouseScores μ ν} (ho : d ∈ jointSpouseOrientation A B)
    (w : PairMovedWoman μ ν) :
    jointFemaleScoreGap d w.val =
      (pairSplitSpouseScores μ ν A B d).2.2 w - (pairSplitSpouseScores μ ν A B d).2.1 w.val := by
  have h := ho.2 w.val
  rw [jointFemaleScoreGap, jointBetterFemaleScore_pairSplit ho, pairSplitSpouseScores_female_second,
    jointWorseFemaleScore]
  by_cases hw : w.val ∈ B
  · simp only [ite_eq_left hw] at h ⊢
    rw [max_eq_left h]
  · simp only [ite_eq_right hw] at h ⊢
    rw [max_eq_right h]

private theorem jointFemaleScoreGap_common {μ ν : Matching n}
    (d : JointSpouseScores μ ν) {w : Fin n} (hw : μ.symm w = ν.symm w) :
    jointFemaleScoreGap d w = 0 := by
  simp [jointFemaleScoreGap, jointBetterFemaleScore, jointWorseFemaleScore,
    jointWomanSpouseScoreLeft_eq_right d hw]

private theorem jointFemaleScoreGap_sum_filter {μ ν : Matching n} (d : JointSpouseScores μ ν)
    (I : Finset (Fin n)) :
    (∑ w ∈ I, jointFemaleScoreGap d w) =
      ∑ w : PairMovedWoman μ ν with w.val ∈ I, jointFemaleScoreGap d w.val := by
  let f w := if w ∈ I then jointFemaleScoreGap d w else 0
  have h (w : Fin n) : f w = if μ.symm w ≠ ν.symm w then f w else 0 := by
    by_cases hw : μ.symm w = ν.symm w
    · simp [f, hw, jointFemaleScoreGap_common d hw]
    · simp [hw]
  have hI : Finset.univ.filter (fun w : Fin n ↦ w ∈ I) = I := by
    ext w
    simp
  calc
    _ = ∑ w, f w := by
      conv_lhs => rw [← hI, Finset.sum_filter]
    _ = ∑ w, if μ.symm w ≠ ν.symm w then f w else 0 :=
      Finset.sum_congr rfl fun w _ ↦ h w
    _ = ∑ w : PairMovedWoman μ ν, f w.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f
    _ = _ := by rw [Finset.sum_filter]

private theorem pairFemaleAggregateFromOrdered_eq {μ ν : Matching n} (A B : Finset (Fin n))
    (y : PairOrderedSpouseArrays n (PairMovedWoman μ ν))
    (hy : y ∈ pairOrderedArraySet (fun w : PairMovedWoman μ ν ↦ w.val)) :
    pairFemaleAggregateFromOrdered A B y =
      pairFemaleAggregateFromGaps B (y.1, fun w ↦ y.2 w - y.1 w.val) := by
  let e := pairSplitSpouseScores μ ν A B
  let d := e.symm ((fun _ ↦ 0, fun _ ↦ 0), y)
  have ho : d ∈ jointSpouseOrientation A B := by
    apply (jointSpouseOrientation_iff_pairOrdered A B d).mpr
    refine ⟨?_, by simpa only [d, e, MeasurableEquiv.apply_symm_apply] using hy⟩
    simp [d, e, pairOrderedArraySet]
  unfold pairFemaleAggregateFromOrdered pairFemaleAggregateFromGaps jointFemaleAggregate
  change (∑ w, jointBetterFemaleScore d w, ∑ w ∈ B, jointFemaleScoreGap d w,
    ∑ w ∈ Finset.univ \ B, jointFemaleScoreGap d w) = _
  rw [jointFemaleScoreGap_sum_filter d B, jointFemaleScoreGap_sum_filter d (Finset.univ \ B)]
  simp only [jointBetterFemaleScore_pairSplit ho, jointFemaleScoreGap_pairSplit ho, d, e,
    MeasurableEquiv.apply_symm_apply, Finset.mem_sdiff, Finset.mem_univ, true_and]

private theorem measurable_pairAggregateLaplace (n u v : ℕ) :
    Measurable (pairAggregateLaplace n u v) := by
  unfold pairAggregateLaplace
  let p : ℝ × ℝ × ℝ → ℝ := Prod.fst
  let q : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.2.1
  let r : ℝ × ℝ × ℝ → ℝ := fun x ↦ x.2.2
  have hp : Measurable p := measurable_fst
  have hq : Measurable q := measurable_fst.comp measurable_snd
  have hr : Measurable r := measurable_snd.comp measurable_snd
  exact (((measurable_pairLaplace.comp ((hp.add hq).add hr)).pow_const _).mul
    ((measurable_pairLaplace.comp (hp.add hr)).pow_const _)).mul
    ((measurable_pairLaplace.comp (hp.add hq)).pow_const _)

/-- Fixed labeled oriented joint stability is bounded by the three-sum kernel
on independent unit female coordinates. The weight may impose any measurable
restriction on the three sums, such as the original bound `ξ + η + ζ ≤ n`. -/
theorem continuousScoreLaw_lintegral_twoStableOrientation_le_gapAggregate (μ ν : Matching n)
    (A B : Finset (Fin n)) {g : ℝ × ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    let u := (pairOrientedMovedMen μ ν A).card
    let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
    (∫⁻ x in twoStableOrientationEvent μ ν A B,
      g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n) ≤
      ∫⁻ z, g (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B z) * ENNReal.ofReal
          (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromGaps B z))
        ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν) := by
  dsimp only
  let u := (pairOrientedMovedMen μ ν A).card
  let v := (pairOrientedMovedMen μ ν (Finset.univ \ A)).card
  let W := PairMovedWoman μ ν
  let T := pairOrderedArraySet (fun w : W ↦ w.val)
  let F (z : PairOrderedSpouseArrays n W) :=
    g (pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B z) * ENNReal.ofReal
      (Real.exp 72 * pairAggregateLaplace n u v (pairFemaleAggregateFromGaps B z))
  have hF : Measurable F :=
    (hg.mul (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (measurable_pairAggregateLaplace n u v)))).comp
        (measurable_pairFemaleAggregateFromGaps μ ν B)
  refine (continuousScoreLaw_lintegral_twoStableOrientation_le_femaleAggregate μ ν A B hg).trans ?_
  calc
    _ = ∫⁻ y in T, F (y.1, fun w ↦ y.2 w - y.1 w.val) ∂pairOrderedSpouseLaw n W := by
      apply setLIntegral_congr_fun (measurableSet_pairOrderedArraySet _)
      intro y hy
      simp only [F, pairFemaleAggregateFromOrdered_eq A B y hy, u, v]
      rfl
    _ ≤ _ := pairUnitArrayLaw_lintegral_orderedGap_le (fun w : W ↦ w.val) hF

/-- Law of the sum of independent uniform unit coordinates, indexed by a finite type. -/
noncomputable def pairUniformSumLaw (ι : Type*) [Fintype ι] : Measure ℝ :=
  (pairUnitArrayLaw ι).map (fun z ↦ ∑ i, z i)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (pairUniformSumLaw ι) :=
  inferInstanceAs (IsProbabilityMeasure ((pairUnitArrayLaw ι).map (fun z ↦ ∑ i, z i)))

/-- Uniform sums are dominated by the radial density of the full nonnegative orthant. -/
theorem pairUniformSumLaw_le_spouseRadialLaw (ι : Type*) [Fintype ι]
    (hι : 0 < Fintype.card ι) :
    pairUniformSumLaw ι ≤ spouseRadialLaw (Fintype.card ι) := by
  let k := Fintype.card ι
  let e := Fintype.equivFin ι
  let T := MeasurableEquiv.arrowCongr' e (.refl ℝ)
  have hT : MeasurePreserving T (pairUnitArrayLaw ι) (pairUnitArrayLaw (Fin k)) :=
    measurePreserving_arrowCongr' _ _ _ _ (fun _ ↦ MeasurePreserving.id unitScoreLaw)
  have hs : Measurable (fun x : Fin k → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i
  have hcomp : (fun x : Fin k → ℝ ↦ ∑ i, x i) ∘ T = (fun z : ι → ℝ ↦ ∑ i, z i) := by
    funext z
    change (∑ i : Fin k, z (e.symm i)) = ∑ i : ι, z i
    exact Equiv.sum_comp e.symm z
  have heq : pairUniformSumLaw ι = pairUniformSumLaw (Fin k) := by
    unfold pairUniformSumLaw
    rw [← hcomp, ← Measure.map_map hs hT.measurable, hT.map_eq]
  have hmap :
      ((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}).map
        (fun z ↦ ∑ i, z i) = spouseRadialLaw k := by
    ext s hS
    let f := s.indicator (1 : ℝ → ℝ≥0∞)
    have hf : Measurable f := measurable_const.indicator hS
    calc
      _ = ∫⁻ t, f t ∂((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}).map
          (fun z ↦ ∑ i, z i) := (lintegral_indicator_one hS).symm
      _ = ∫⁻ z, f (∑ i, z i) ∂((volume : Measure (Fin k → ℝ)).restrict {z | ∀ i, 0 ≤ z i}) :=
        lintegral_map hf hs
      _ = ∫⁻ t, ∫⁻ w, f (∑ i, t * w i) ∂spouseAngularLaw k ∂spouseRadialLaw k :=
        lintegral_spouseRadialAngular hι (hf.comp hs)
      _ = ∫⁻ t, f t ∂spouseRadialLaw k := by
        apply lintegral_congr
        intro t
        calc
          _ = ∫⁻ _w : Fin k → ℝ, f t ∂spouseAngularLaw k := by
            apply lintegral_congr_ae
            filter_upwards [ae_spouseAngularLaw hι] with w hw
            rw [← Finset.mul_sum, hw.2, mul_one]
          _ = _ := by rw [lintegral_const, measure_univ, mul_one]
      _ = _ := lintegral_indicator_one hS
  rw [heq, ← hmap, pairUniformSumLaw, pairUnitArrayLaw_eq_restrict]
  have hsub : pairUnitCube (Fin k) ⊆ {z : Fin k → ℝ | ∀ i, 0 ≤ z i} :=
    fun z hz ↦ show ∀ i, 0 ≤ z i from fun i ↦ (Set.mem_univ_pi.mp hz i).1
  exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) hs

/-- The woman whose partner changes and whose orientation class is prescribed. -/
abbrev PairFemaleGapClass (μ ν : Matching n) (B : Finset (Fin n)) :=
  {w : PairMovedWoman μ ν // w.val ∈ B}

abbrev PairFemaleOtherGapClass (μ ν : Matching n) (B : Finset (Fin n)) :=
  {w : PairMovedWoman μ ν // w.val ∉ B}

/-- Under the relaxed law, the three sums are independent. -/
theorem map_pairFemaleAggregateFromGaps (μ ν : Matching n) (B : Finset (Fin n)) :
    (pairOrderedSpouseLaw n (PairMovedWoman μ ν)).map (pairFemaleAggregateFromGaps B) =
      (pairUniformSumLaw (Fin n)).prod
        ((pairUniformSumLaw (PairFemaleGapClass μ ν B)).prod
          (pairUniformSumLaw (PairFemaleOtherGapClass μ ν B))) := by
  let W := PairMovedWoman μ ν
  let V := PairFemaleGapClass μ ν B
  let U := PairFemaleOtherGapClass μ ν B
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : W ↦ ℝ) (fun w ↦ w.val ∈ B)
  let E := (MeasurableEquiv.refl (Fin n → ℝ)).prodCongr e
  have hE : MeasurePreserving E (pairOrderedSpouseLaw n W)
      ((pairUnitArrayLaw (Fin n)).prod ((pairUnitArrayLaw V).prod (pairUnitArrayLaw U))) :=
    (MeasurePreserving.id _).prod (measurePreserving_piEquivPiSubtypeProd (fun _ ↦ unitScoreLaw) _)
  let s₀ (x : Fin n → ℝ) := ∑ i, x i
  let s₁ (x : V → ℝ) := ∑ i, x i
  let s₂ (x : U → ℝ) := ∑ i, x i
  have hs₀ : Measurable s₀ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hs₁ : Measurable s₁ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  have hs₂ : Measurable s₂ := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
  let F := Prod.map s₀ (Prod.map s₁ s₂)
  have hF : Measurable F := hs₀.prodMap (hs₁.prodMap hs₂)
  have heq : F ∘ E = pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B := by
    funext p
    unfold pairFemaleAggregateFromGaps
    change (∑ w, p.1 w, ∑ w : V, p.2 w.val, ∑ w : U, p.2 w.val) = _
    congr 1
    exact Prod.ext
      ((Finset.sum_subtype (p := fun w : W ↦ w.val ∈ B)
        (Finset.univ.filter (fun w : W ↦ w.val ∈ B))
        (fun _ ↦ by simp) p.2).symm)
      ((Finset.sum_subtype (p := fun w : W ↦ w.val ∉ B)
        (Finset.univ.filter (fun w : W ↦ w.val ∉ B))
        (fun _ ↦ by simp) p.2).symm)
  rw [← heq, ← Measure.map_map hF hE.measurable, hE.map_eq]
  unfold F
  rw [← Measure.map_prod_map _ _ hs₀ (hs₁.prodMap hs₂), ← Measure.map_prod_map _ _ hs₁ hs₂]
  rfl

/-- The original score constraint retained after extending the independent cube. -/
def pairAggregateCutoff (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {s | s.1 + s.2.1 + s.2.2 ≤ (n : ℝ)}

private theorem measurableSet_pairAggregateCutoff (n : ℕ) :
    MeasurableSet (pairAggregateCutoff n) := by
  apply measurableSet_le _ measurable_const
  exact (measurable_fst.add (measurable_fst.comp measurable_snd)).add
    (measurable_snd.comp measurable_snd)

theorem jointFemaleAggregate_mem_cutoff {μ ν : Matching n} {d : JointSpouseScores μ ν}
    (hd : JointSpouseThresholdsUnit d) (B : Finset (Fin n)) :
    jointFemaleAggregate d B ∈ pairAggregateCutoff n := by
  change (jointFemaleAggregate d B).1 + (jointFemaleAggregate d B).2.1 +
    (jointFemaleAggregate d B).2.2 ≤ (n : ℝ)
  rw [← jointFemale_sum_worse d B]
  calc
    _ ≤ ∑ _w : Fin n, (1 : ℝ) := Finset.sum_le_sum fun w _ ↦ max_le (hd.2 w).1.2 (hd.2 w).2.2
    _ = _ := by simp

/-- The three-variable upper kernel with the original total-score cutoff. -/
noncomputable def pairRadialUpperKernel (n u v : ℕ) : ℝ × ℝ × ℝ → ℝ≥0∞ :=
  (pairAggregateCutoff n).indicator (fun s ↦ ENNReal.ofReal (pairAggregateLaplace n u v s))

theorem measurable_pairRadialUpperKernel (n u v : ℕ) : Measurable (pairRadialUpperKernel n u v) :=
  (ENNReal.measurable_ofReal.comp (measurable_pairAggregateLaplace n u v)).indicator
    (measurableSet_pairAggregateCutoff n)

/-- The fixed labeled orientation probability is bounded by the three independent
orthant-radial densities. The equalities identify the female gap classes with the
two moved-row orientation sizes; the theorem does not assume an analytic estimate. -/
theorem continuousScoreLaw_twoStableOrientation_le_radial (μ ν : Matching n)
    (A B : Finset (Fin n)) {u v : ℕ}
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v)
    (hB : Fintype.card (PairFemaleGapClass μ ν B) = u)
    (hBc : Fintype.card (PairFemaleOtherGapClass μ ν B) = v)
    (hn : 0 < n) (hu₀ : 0 < u) (hv₀ : 0 < v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A B) ≤ ENNReal.ofReal (Real.exp 72) *
      ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  let g := (pairAggregateCutoff n).indicator (1 : ℝ × ℝ × ℝ → ℝ≥0∞)
  have hg : Measurable g := measurable_const.indicator (measurableSet_pairAggregateCutoff n)
  let E := twoStableOrientationEvent μ ν A B
  let G := pairFemaleAggregateFromGaps (μ := μ) (ν := ν) B
  let F := pairRadialUpperKernel n u v
  have hF : Measurable F := measurable_pairRadialUpperKernel n u v
  have hpres : MeasurePreserving (fun x ↦ (splitTwoMatchingScores μ ν x).1)
      (continuousScoreLaw n) (jointSpouseScoreLaw μ ν) :=
    measurePreserving_fst.comp (measurePreserving_splitTwoMatchingScores μ ν)
  have hL : continuousScoreLaw n E =
      ∫⁻ x in E, g (jointFemaleAggregate (splitTwoMatchingScores μ ν x).1 B) ∂continuousScoreLaw n := by
    rw [← setLIntegral_one]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (hpres.quasiMeasurePreserving.ae
      (ae_jointSpouseThresholdsUnit μ ν))] with x hx
    dsimp only [g]
    rw [Set.indicator_of_mem (jointFemaleAggregate_mem_cutoff hx B)]
    rfl
  have hmul (s : ℝ × ℝ × ℝ) :
      g s * ENNReal.ofReal (Real.exp 72 * pairAggregateLaplace n u v s) =
      ENNReal.ofReal (Real.exp 72) * F s := by
    by_cases hs : s ∈ pairAggregateCutoff n
    · simp only [g, F, pairRadialUpperKernel, Set.indicator_of_mem hs, Pi.one_apply,
        one_mul, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · simp only [g, F, pairRadialUpperKernel, Set.indicator_of_notMem hs, zero_mul, mul_zero]
  rw [hL]
  have h := continuousScoreLaw_lintegral_twoStableOrientation_le_gapAggregate μ ν A B hg
  dsimp only at h
  rw [hu, hv] at h
  refine h.trans ?_
  simp_rw [hmul]
  have hmeas : Measurable (fun z ↦ F (G z)) :=
    hF.comp (measurable_pairFemaleAggregateFromGaps μ ν B)
  rw [lintegral_const_mul _ hmeas]
  apply mul_le_mul_right
  change (∫⁻ z, F (G z) ∂pairOrderedSpouseLaw n (PairMovedWoman μ ν)) ≤ _
  rw [← lintegral_map hF (measurable_pairFemaleAggregateFromGaps μ ν B),
    map_pairFemaleAggregateFromGaps]
  rw [lintegral_prod _ hF.aemeasurable]
  have h₀ := pairUniformSumLaw_le_spouseRadialLaw (Fin n) (by simpa using hn)
  have h₁ := pairUniformSumLaw_le_spouseRadialLaw (PairFemaleGapClass μ ν B) (hB ▸ hu₀)
  have h₂ := pairUniformSumLaw_le_spouseRadialLaw (PairFemaleOtherGapClass μ ν B) (hBc ▸ hv₀)
  rw [Fintype.card_fin] at h₀
  rw [hB] at h₁
  rw [hBc] at h₂
  refine lintegral_mono' h₀ fun ξ ↦ ?_
  have hξ : Measurable (fun t : ℝ × ℝ ↦ F (ξ, t)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hξ.aemeasurable]
  exact lintegral_mono' h₁ fun η ↦ lintegral_mono' h₂ le_rfl

private theorem pairMoved_iff_movedWoman (μ ν : Matching n) (m : Fin n) :
    μ m ≠ ν m ↔ μ.symm (μ m) ≠ ν.symm (μ m) := by
  constructor
  · intro hm h
    have he : ν m = μ m := by
      simpa only [μ.symm_apply_apply, ν.apply_symm_apply] using congrArg ν h
    exact hm he.symm
  · intro h he
    apply h
    simp only [μ.symm_apply_apply]
    rw [he, ν.symm_apply_apply]

private theorem pairCard_femaleGapClass (μ ν : Matching n) (A B : Finset (Fin n))
    (hAB : ∀ m, μ m ∈ B ↔ m ∈ A) :
    Fintype.card (PairFemaleGapClass μ ν B) = (pairOrientedMovedMen μ ν A).card := by
  let P (m : Fin n) := μ m ≠ ν m ∧ m ∈ A
  let Q (w : Fin n) := μ.symm w ≠ ν.symm w ∧ w ∈ B
  let e : Subtype P ≃ Subtype Q := μ.subtypeEquiv fun m ↦
    and_congr (pairMoved_iff_movedWoman μ ν m) (hAB m).symm
  let f : PairFemaleGapClass μ ν B ≃ Subtype Q :=
    Equiv.subtypeSubtypeEquivSubtypeInter _ _
  rw [Fintype.card_congr (f.trans e.symm), Fintype.card_subtype]
  congr 1
  ext m
  simp [pairOrientedMovedMen, and_comm]

private theorem pairCard_femaleOtherGapClass (μ ν : Matching n) (A B : Finset (Fin n))
    (hAB : ∀ m, μ m ∈ B ↔ m ∈ A) :
    Fintype.card (PairFemaleOtherGapClass μ ν B) =
      (pairOrientedMovedMen μ ν (Finset.univ \ A)).card := by
  let P (m : Fin n) := μ m ≠ ν m ∧ m ∉ A
  let Q (w : Fin n) := μ.symm w ≠ ν.symm w ∧ w ∉ B
  let e : Subtype P ≃ Subtype Q := μ.subtypeEquiv fun m ↦
    and_congr (pairMoved_iff_movedWoman μ ν m) (not_congr (hAB m).symm)
  let f : PairFemaleOtherGapClass μ ν B ≃ Subtype Q :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun w : Fin n ↦ μ.symm w ≠ ν.symm w)
      (fun w : Fin n ↦ w ∉ B)
  rw [Fintype.card_congr (f.trans e.symm), Fintype.card_subtype]
  congr 1
  ext m
  simp [pairOrientedMovedMen, and_comm]

/-- If the female orientation class is the image of the male class under the left
matching, its two gap counts match the male orientation sizes automatically. -/
theorem continuousScoreLaw_twoStableOrientation_image_le_radial (μ ν : Matching n)
    (A : Finset (Fin n)) {u v : ℕ}
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v)
    (hn : 0 < n) (hu₀ : 0 < u) (hv₀ : 0 < v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A (A.image μ)) ≤
      ENNReal.ofReal (Real.exp 72) *
        ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
          ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  have hA (m : Fin n) : μ m ∈ A.image μ ↔ m ∈ A := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨m', hm', h⟩ ↦ μ.injective h ▸ hm', fun hm ↦ ⟨m, hm, rfl⟩⟩
  exact continuousScoreLaw_twoStableOrientation_le_radial μ ν A (A.image μ) hu hv
    ((pairCard_femaleGapClass μ ν A _ hA).trans hu)
    ((pairCard_femaleOtherGapClass μ ν A _ hA).trans hv) hn hu₀ hv₀

/-- The radial integrand is the elementary closed form at almost every point
of the positive orthant. -/
theorem lintegral_pairRadialUpperKernel_eq_closed (n u v : ℕ) :
    (∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, pairRadialUpperKernel n u v (ξ, η, ζ)
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n) =
      ∫⁻ ξ, ∫⁻ η, ∫⁻ ζ, if ξ + η + ζ ≤ (n : ℝ) then
        ENNReal.ofReal (((1 - Real.exp (-(ξ + η + ζ))) / (ξ + η + ζ)) ^ n *
          ((1 - Real.exp (-(ξ + ζ))) / (ξ + ζ)) ^ u *
          ((1 - Real.exp (-(ξ + η))) / (ξ + η)) ^ v) else 0
        ∂spouseRadialLaw v ∂spouseRadialLaw u ∂spouseRadialLaw n := by
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos n] with ξ hξ
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos u] with η hη
  apply lintegral_congr_ae
  filter_upwards [ae_spouseRadialLaw_pos v] with ζ hζ
  have h₀ : 0 < ξ + η + ζ := by positivity
  have h₁ : 0 < ξ + ζ := by positivity
  have h₂ : 0 < ξ + η := by positivity
  simp only [pairRadialUpperKernel, Set.indicator, pairAggregateCutoff, Set.mem_ofPred_eq,
    pairAggregateLaplace, pairLaplace_of_pos h₀, pairLaplace_of_pos h₁, pairLaplace_of_pos h₂]

/-- On tie-free scores, the two no-block conditions determine the women's orientation
from the men's. In particular the preferred male set has the same image under both
matchings, so it is a union of relative-permutation cycles. -/
theorem twoStableOrientation_of_male_class {μ ν : Matching n} {x : ScoreProfile n}
    (hμ : IsScoreStable x μ) (hν : IsScoreStable x ν)
    (hx : ∀ r, Function.Injective (x r)) (A : Finset (Fin n))
    (hA : ∀ m, μ m ≠ ν m → (m ∈ A ↔ x (.inl m) (μ m) < x (.inl m) (ν m))) :
    x ∈ twoStableOrientationEvent μ ν A (A.image μ) ∧ A.image μ = A.image ν := by
  have hMleft (m : Fin n) (hm : m ∈ A) :
      x (.inl m) (μ m) ≤ x (.inl m) (ν m) := by
    by_cases he : μ m = ν m
    · rw [he]
    · exact ((hA m he).mp hm).le
  have hMright (m : Fin n) (hm : m ∉ A) :
      x (.inl m) (ν m) ≤ x (.inl m) (μ m) := by
    by_cases he : μ m = ν m
    · rw [he]
    · exact le_of_not_gt fun h ↦ hm ((hA m he).mpr h)
  have hWright (m : Fin n) (hm : m ∈ A) :
      x (.inr (μ m)) (ν.symm (μ m)) ≤ x (.inr (μ m)) m := by
    by_cases he : μ m = ν m
    · rw [he, ν.symm_apply_apply]
    · exact le_of_not_gt fun h ↦
        hν m (μ m) ⟨Ne.symm he, (hA m he).mp hm, h⟩
  have hWleft (m : Fin n) (hm : m ∉ A) :
      x (.inr (ν m)) (μ.symm (ν m)) ≤ x (.inr (ν m)) m := by
    by_cases he : μ m = ν m
    · rw [← he, μ.symm_apply_apply]
    · have hlt : x (.inl m) (ν m) < x (.inl m) (μ m) :=
        lt_of_le_of_ne (hMright m hm) fun h ↦ he ((hx (.inl m) h).symm)
      exact le_of_not_gt fun h ↦ hμ m (ν m) ⟨he, hlt, h⟩
  have hsub : A.image μ ⊆ A.image ν := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
    let j := ν.symm (μ m)
    have hj : ν j = μ m := ν.apply_symm_apply _
    refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
    by_contra h
    have h₁ := hWright m hm
    have h₂ := hWleft j h
    rw [hj, μ.symm_apply_apply] at h₂
    have hmj : j = m := hx (.inr (μ m)) (le_antisymm h₁ h₂)
    exact h (hmj ▸ hm)
  have hImage : A.image μ = A.image ν := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ μ.injective, Finset.card_image_of_injective _ ν.injective]
  refine ⟨⟨hμ, hν, ?_⟩, hImage⟩
  constructor
  · intro m
    rw [jointManSpouseScoreLeft_split, jointManSpouseScoreRight_split]
    by_cases hm : m ∈ A
    · simpa only [ite_eq_left hm] using hMleft m hm
    · simpa only [ite_eq_right hm] using hMright m hm
  · intro w
    rw [jointWomanSpouseScoreLeft_split, jointWomanSpouseScoreRight_split]
    by_cases hw : w ∈ A.image μ
    · simp only [ite_eq_left hw]
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
      simpa only [μ.symm_apply_apply] using hWright m hm
    · simp only [ite_eq_right hw]
      let m := ν.symm w
      have hνm : ν m = w := ν.apply_symm_apply w
      have hm : m ∉ A := fun h ↦ hw (hImage ▸ Finset.mem_image.mpr ⟨m, h, hνm⟩)
      have h := hWleft m hm
      rwa [hνm] at h

end LennonPittelFormalization

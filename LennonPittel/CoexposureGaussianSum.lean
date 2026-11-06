module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Tactic
public import Mathlib.Topology.Order.Compact

/-!
# Bounds for the co-exposure cycle sum

The falling-factorial suppression in the cycle expansion leaves only order
square-root many effective summands. We compare to a geometric series after
completing the square, rather than integrating a Gaussian.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Finset Filter

namespace LennonPittelFormalization

private theorem sum_cast_range_gaussian (j : ℕ) :
    (∑ i ∈ range j, (i : ℝ)) = (j : ℝ) * ((j : ℝ) - 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

/-- The normalized falling factorial is bounded by the Gaussian cutoff. -/
theorem descFactorial_div_pow_le_exp {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (n.descFactorial j : ℝ) / (n : ℝ) ^ j ≤
      Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hi (i : ℕ) (h : i ∈ range j) : i ≤ n := (mem_range.mp h).le.trans hj
  have hpow : (n : ℝ) ^ j = ∏ _i ∈ range j, (n : ℝ) := by simp
  calc
    _ = ∏ i ∈ range j, (1 - (i : ℝ) / (n : ℝ)) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, hpow, ← prod_div_distrib]
      refine prod_congr rfl fun i h ↦ ?_
      rw [Nat.cast_sub (hi i h)]
      field_simp
    _ ≤ ∏ i ∈ range j, Real.exp (-((i : ℝ) / (n : ℝ))) :=
      prod_le_prod₀ (fun i h ↦ sub_nonneg.mpr ((div_le_one (by positivity)).mpr
        (Nat.cast_le.mpr (hi i h)))) fun i _ ↦ by
          simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((i : ℝ) / (n : ℝ)))
    _ = _ := by
      rw [← Real.exp_sum, sum_neg_distrib, ← sum_div, sum_cast_range_gaussian]
      congr 1
      ring

private theorem sum_exp_neg_div_le (s : ℝ) (hs : 0 < s) (m : ℕ) :
    (∑ j ∈ range m, Real.exp (-((j : ℝ) / s))) ≤ 1 + s := by
  let r := Real.exp (-(1 / s))
  have hr₀ : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : r < 1 := by
    calc
      r < Real.exp 0 := Real.exp_lt_exp.mpr (neg_neg_of_pos (one_div_pos.mpr hs))
      _ = 1 := Real.exp_zero
  have hrle : r ≤ s / (1 + s) := by
    calc
      r = (Real.exp (1 / s))⁻¹ := Real.exp_neg _
      _ ≤ (1 / s + 1)⁻¹ :=
        inv_anti₀ (by positivity) (Real.add_one_le_exp (1 / s))
      _ = s / (1 + s) := by field_simp
  have hmul : 1 ≤ (1 + s) * (1 - r) := by
    have h := (le_div_iff₀ (by positivity : 0 < 1 + s)).mp hrle
    nlinarith
  have heq (j : ℕ) : Real.exp (-((j : ℝ) / s)) = r ^ j := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [heq]
  have hgeom : (∑ j ∈ range m, r ^ j) * (1 - r) ≤ 1 := by
    rw [geom_sum_mul_of_le_one hr₁.le]
    exact sub_le_self _ (pow_nonneg hr₀ _)
  exact le_of_mul_le_mul_right (hgeom.trans hmul) (sub_pos.mpr hr₁)

/-- A small multiplicative perturbation preserves the square-root cycle sum bound. -/
theorem coexposure_descFactorial_sum_le_sqrt {n : ℕ} (hn : 0 < n) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ j ∈ range (n + 1), (1 + δ) ^ j * ((n.descFactorial j : ℝ) / (n : ℝ) ^ j)) ≤
      2 * Real.exp ((C + 3 / 2) ^ 2 / 2) * Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs₂ : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hs₁ : 1 ≤ s := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  let D := C + 3 / 2
  have hexp (j : ℕ) :
      (j : ℝ) * δ - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)) ≤
        D ^ 2 / 2 - (j : ℝ) / s := by
    let t := (j : ℝ) / s
    have ht : 0 ≤ t := by positivity
    have ht₂ : (j : ℝ) ^ 2 / (n : ℝ) = t ^ 2 := by
      simp only [t, div_pow, hs₂]
    have ht₁ : (j : ℝ) / (n : ℝ) ≤ t := by
      rw [← hs₂, pow_two, ← div_div]
      exact div_le_self ht hs₁
    have hδj : (j : ℝ) * δ ≤ C * t := by
      calc
        _ ≤ (j : ℝ) * (C / s) :=
          mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)
        _ = C * t := by dsimp [t]; ring
    calc
      _ = (j : ℝ) * δ - ((j : ℝ) ^ 2 / (n : ℝ) - (j : ℝ) / (n : ℝ)) / 2 := by ring
      _ ≤ C * t - (t ^ 2 - t) / 2 := by rw [ht₂]; linarith
      _ ≤ D ^ 2 / 2 - t := by dsimp [D]; nlinarith [sq_nonneg (t - (C + 3 / 2))]
  calc
    _ ≤ ∑ j ∈ range (n + 1), Real.exp (D ^ 2 / 2) * Real.exp (-((j : ℝ) / s)) := by
      refine sum_le_sum fun j hj ↦ ?_
      have hj' : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
      have hδp : (1 + δ) ^ j ≤ (Real.exp δ) ^ j :=
        pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp δ) _
      calc
        _ ≤ (Real.exp δ) ^ j *
            Real.exp (-((j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ)))) :=
          mul_le_mul hδp (descFactorial_div_pow_le_exp hn hj') (by positivity) (by positivity)
        _ = Real.exp ((j : ℝ) * δ - (j : ℝ) * ((j : ℝ) - 1) / (2 * (n : ℝ))) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
        _ ≤ _ := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
          exact Real.exp_le_exp.mpr (hexp j)
    _ = Real.exp (D ^ 2 / 2) * ∑ j ∈ range (n + 1), Real.exp (-((j : ℝ) / s)) :=
      (mul_sum ..).symm
    _ ≤ Real.exp (D ^ 2 / 2) * (1 + s) :=
      mul_le_mul_of_nonneg_left (sum_exp_neg_div_le s hs _) (Real.exp_nonneg _)
    _ ≤ _ := by
      calc
        _ ≤ Real.exp (D ^ 2 / 2) * (2 * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
        _ = _ := by dsimp [D, s]; ring


/-- The elementary symmetric sum of a finite family of real weights. -/
noncomputable def coexposureEsymm {ι : Type*} (s : Finset ι) (j : ℕ) (w : ι → ℝ) : ℝ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, w i

private theorem coexposureEsymm_zero {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    coexposureEsymm s 0 w = 1 := by simp [coexposureEsymm]

private theorem coexposureEsymm_congr {ι : Type*} {s : Finset ι} (j : ℕ) {w v : ι → ℝ}
    (h : ∀ i ∈ s, w i = v i) : coexposureEsymm s j w = coexposureEsymm s j v :=
  sum_congr rfl fun _ ht ↦ prod_congr rfl fun i hi ↦ h i ((mem_powersetCard.mp ht).1 hi)

private theorem coexposureEsymm_nonneg {ι : Type*} (s : Finset ι) (j : ℕ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ coexposureEsymm s j w :=
  sum_nonneg fun _ _ ↦ prod_nonneg fun i _ ↦ hw i

private theorem coexposureEsymm_insert_succ {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι} (ha : a ∉ s) (j : ℕ) (w : ι → ℝ) :
    coexposureEsymm (insert a s) (j + 1) w =
      coexposureEsymm s (j + 1) w + w a * coexposureEsymm s j w := by
  have hnot (k : ℕ) {t : Finset ι} (ht : t ∈ s.powersetCard k) : a ∉ t :=
    fun hat ↦ ha ((mem_powersetCard.mp ht).1 hat)
  have hdisj : Disjoint (s.powersetCard (j + 1)) ((s.powersetCard j).image (insert a)) :=
    disjoint_left.mpr fun t ht ht' ↦ by
      obtain ⟨u, _, rfl⟩ := mem_image.mp ht'
      exact hnot (j + 1) ht (mem_insert_self a u)
  have hinj : Set.InjOn (insert a) (s.powersetCard j : Set (Finset ι)) := by
    intro t ht u hu he
    have he' := congrArg (fun v : Finset ι ↦ v.erase a) he
    simpa only [erase_insert (hnot j ht), erase_insert (hnot j hu)] using he'
  unfold coexposureEsymm
  rw [powersetCard_succ_insert ha j, sum_union hdisj, sum_image hinj, mul_sum]
  congr 1
  exact sum_congr rfl fun t ht ↦ prod_insert (hnot j ht)

private theorem coexposureEsymm_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ) :
    coexposureEsymm s 1 w = ∑ i ∈ s, w i := by
  induction s using Finset.induction_on with
  | empty => simp [coexposureEsymm, powersetCard_one]
  | @insert a s ha ih =>
    rw [coexposureEsymm_insert_succ ha 0, coexposureEsymm_zero, mul_one,
      ih, sum_insert ha, add_comm]

private theorem coexposureEsymm_insert_insert {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a b : ι} (ha : a ∉ insert b s) (hb : b ∉ s) (j : ℕ) (w : ι → ℝ) :
    coexposureEsymm (insert a (insert b s)) (j + 2) w =
      coexposureEsymm s (j + 2) w + (w a + w b) * coexposureEsymm s (j + 1) w +
        w a * w b * coexposureEsymm s j w := by
  rw [show j + 2 = (j + 1) + 1 by rfl, coexposureEsymm_insert_succ ha,
    coexposureEsymm_insert_succ hb, coexposureEsymm_insert_succ hb]
  ring

private abbrev coexposureSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

private theorem exists_coexposure_smoothing {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw : w ∈ coexposureSimplex ι) {a b : ι} (hab : a ≠ b) (hne : w a ≠ w b)
    (j : ℕ) :
    ∃ v ∈ coexposureSimplex ι, coexposureEsymm univ j w ≤ coexposureEsymm univ j v ∧
      (∑ i, (v i) ^ 2) < ∑ i, (w i) ^ 2 := by
  classical
  let t := (univ.erase a).erase b
  have hat : a ∉ t := fun h ↦ notMem_erase a _ (mem_erase.mp h).2
  have hbt : b ∉ t := notMem_erase _ _
  have hat' : a ∉ insert b t := by simp [hab, hat]
  have hdecomp : insert a (insert b t) = univ := by
    ext i
    by_cases hi : i = a
    · simp [hi]
    by_cases hi' : i = b
    · simp [hi']
    simp [t, hi, hi']
  have hsplit (f : ι → ℝ) : (∑ i, f i) = f a + f b + ∑ i ∈ t, f i := by
    rw [← hdecomp, sum_insert hat', sum_insert hbt]
    ring
  let c := (w a + w b) / 2
  let v := fun i ↦ if i = a ∨ i = b then c else w i
  have hva : v a = c := by simp [v]
  have hvb : v b = c := by simp [v]
  have hvt (i : ι) (hi : i ∈ t) : v i = w i := by
    have hia : i ≠ a := fun h ↦ hat (h ▸ hi)
    have hib : i ≠ b := fun h ↦ hbt (h ▸ hi)
    simp [v, hia, hib]
  have hsum : ∑ i, v i = 1 := by
    rw [← hw.2, hsplit v, hsplit w, hva, hvb, sum_congr rfl hvt]
    dsimp [c]
    ring
  have hnonneg (i : ι) : 0 ≤ v i := by
    dsimp [v, c]
    split_ifs <;> positivity [hw.1 i, hw.1 a, hw.1 b]
  refine ⟨v, ⟨hnonneg, hsum⟩, ?_, ?_⟩
  · cases j with
    | zero => simp only [coexposureEsymm_zero, le_refl]
    | succ j =>
      cases j with
      | zero =>
        rw [show 0 + 1 = 1 by rfl, coexposureEsymm_one, coexposureEsymm_one, hw.2, hsum]
      | succ j =>
        change coexposureEsymm univ (j + 2) w ≤ coexposureEsymm univ (j + 2) v
        rw [← hdecomp, coexposureEsymm_insert_insert hat' hbt,
          coexposureEsymm_insert_insert hat' hbt,
          coexposureEsymm_congr (j + 2) hvt, coexposureEsymm_congr (j + 1) hvt,
          coexposureEsymm_congr j hvt, hva, hvb]
        have hcc : c + c = w a + w b := by dsimp [c]; ring
        have hm : w a * w b ≤ c * c := by dsimp [c]; nlinarith [sq_nonneg (w a - w b)]
        rw [hcc]
        gcongr
        exact coexposureEsymm_nonneg t j hw.1
  · rw [hsplit (fun i ↦ (v i) ^ 2), hsplit (fun i ↦ (w i) ^ 2)]
    simp only [hva, hvb]
    rw [sum_congr rfl (fun i hi ↦ congrArg (fun z : ℝ ↦ z ^ 2) (hvt i hi))]
    dsimp [c]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]

/-- Among nonnegative weights summing to one, uniform weights maximize each
elementary symmetric sum. -/
theorem coexposureEsymm_le_uniform {n : ℕ} (hn : 0 < n) (j : ℕ) {w : Fin n → ℝ}
    (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) :
    coexposureEsymm univ j w ≤ (n.choose j : ℝ) * (1 / (n : ℝ)) ^ j := by
  classical
  let E := coexposureEsymm (univ : Finset (Fin n)) j
  have hE : Continuous E :=
    continuous_finsetSum _ fun t _ ↦ continuous_finsetProd _ fun i _ ↦ continuous_apply i
  let S := coexposureSimplex (Fin n)
  have hS : IsCompact S := by
    have hS_eq : S = Set.range
        (fun t ↦ t.weights : Convexity.StdSimplex ℝ (Fin n) → (Fin n → ℝ)) := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext v
      simp [S, coexposureSimplex]
    rw [hS_eq]
    exact isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).continuous
  have hwS : w ∈ S := ⟨hw₀, hw⟩
  obtain ⟨u, hu, humax⟩ := hS.exists_isMaxOn ⟨w, hwS⟩ hE.continuousOn
  let T := S ∩ {v | E v = E u}
  have hT : IsCompact T := hS.inter_right (isClosed_eq hE continuous_const)
  have hsq : Continuous (fun v : Fin n → ℝ ↦ ∑ i, (v i) ^ 2) :=
    continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2
  obtain ⟨v, hv, hvmin⟩ := hT.exists_isMinOn ⟨u, hu, rfl⟩ hsq.continuousOn
  have hconst (a b : Fin n) : v a = v b := by
    by_contra hne
    have hab : a ≠ b := fun h ↦ hne (congrArg v h)
    obtain ⟨z, hz, hzE, hzsq⟩ := exists_coexposure_smoothing hv.1 hab hne j
    have hzT : z ∈ T := ⟨hz, (humax hz).antisymm (hv.2 ▸ hzE)⟩
    exact (not_lt_of_ge (hvmin hzT)) hzsq
  let a : Fin n := ⟨0, hn⟩
  have hvc : ∑ i : Fin n, v i = (n : ℝ) * v a := by
    calc
      _ = ∑ _i : Fin n, v a := sum_congr rfl fun i _ ↦ hconst i a
      _ = _ := by simp
  have hva : v a = 1 / (n : ℝ) := by
    apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).mpr
    rw [mul_comm, ← hvc]
    exact hv.1.2
  have hveq (i : Fin n) : v i = 1 / (n : ℝ) := (hconst i a).trans hva
  calc
    E w ≤ E u := humax hwS
    _ = E v := hv.2.symm
    _ = coexposureEsymm univ j (fun _ ↦ 1 / (n : ℝ)) :=
      coexposureEsymm_congr j fun i _ ↦ hveq i
    _ = _ := by
      calc
        coexposureEsymm univ j (fun _ : Fin n ↦ 1 / (n : ℝ)) =
            ∑ _t ∈ (univ : Finset (Fin n)).powersetCard j, (1 / (n : ℝ)) ^ j :=
          sum_congr rfl fun _ ht ↦ by rw [prod_const, (mem_powersetCard.mp ht).2]
        _ = _ := by simp [sum_const, nsmul_eq_mul, card_powersetCard]


/-- Grouping the weighted cycle bound by support cardinality gives a
square-root bound uniform over the entire weight simplex. -/
theorem coexposure_weighted_powerset_sum_le_sqrt {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (1 + δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i) ≤
        2 * Real.exp ((C + 3 / 2) ^ 2 / 2) * Real.sqrt (n : ℝ) := by
  calc
    _ = ∑ j ∈ range (n + 1), (1 + δ) ^ j * (j.factorial : ℝ) * coexposureEsymm univ j w := by
      rw [sum_powerset, card_univ, Fintype.card_fin]
      refine sum_congr rfl fun j _ ↦ ?_
      unfold coexposureEsymm
      rw [mul_sum]
      exact sum_congr rfl fun t ht ↦ by rw [(mem_powersetCard.mp ht).2]
    _ ≤ ∑ j ∈ range (n + 1), (1 + δ) ^ j * ((n.descFactorial j : ℝ) / (n : ℝ) ^ j) := by
      refine sum_le_sum fun j _ ↦ ?_
      calc
        _ ≤ (1 + δ) ^ j * (j.factorial : ℝ) * ((n.choose j : ℝ) * (1 / (n : ℝ)) ^ j) :=
          mul_le_mul_of_nonneg_left (coexposureEsymm_le_uniform hn j hw₀ hw) (by positivity)
        _ = _ := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, div_pow, one_pow]
          ring
    _ ≤ _ := coexposure_descFactorial_sum_le_sqrt hn hδ₀ hδ


/-- The square-root estimate in the nonnegative extended-real form used by
the successor moment. -/
theorem coexposure_weighted_powerset_sum_le_sqrt_ennreal {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) {δ C : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ C / Real.sqrt (n : ℝ)) :
    (∑ t ∈ (univ : Finset (Fin n)).powerset,
      (t.card.factorial : ℝ≥0∞) * (ENNReal.ofReal (1 + δ)) ^ t.card *
        ∏ i ∈ t, ENNReal.ofReal (w i)) ≤
      ENNReal.ofReal (2 * Real.exp ((C + 3 / 2) ^ 2 / 2) * Real.sqrt (n : ℝ)) := by
  have ha : 0 ≤ 1 + δ := by positivity
  calc
    _ = ENNReal.ofReal (∑ t ∈ (univ : Finset (Fin n)).powerset,
        (1 + δ) ^ t.card * (t.card.factorial : ℝ) * ∏ i ∈ t, w i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun t _ ↦
        mul_nonneg (mul_nonneg (pow_nonneg ha _) (Nat.cast_nonneg _))
          (prod_nonneg fun i _ ↦ hw₀ i))]
      refine sum_congr rfl fun t _ ↦ ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (pow_nonneg ha _),
        ENNReal.ofReal_pow ha, ENNReal.ofReal_natCast,
        ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hw₀ i),
        mul_comm ((t.card.factorial : ℝ≥0∞))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (coexposure_weighted_powerset_sum_le_sqrt hn hw₀ hw hδ₀ hδ)


private theorem inv_one_sub_mul_le {a b : ℝ} (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) :
    (1 - a)⁻¹ * (1 - b)⁻¹ ≤ 1 + 4 * (a + b) := by
  have hinv (x : ℝ) (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - x)]
    nlinarith [mul_nonneg hx₀ (show 0 ≤ 1 - 2 * x by linarith)]
  calc
    _ ≤ (1 + 2 * a) * (1 + 2 * b) :=
      mul_le_mul (hinv a ha₀ ha) (hinv b hb₀ hb)
        (inv_nonneg.mpr (by linarith)) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg hb₀ (show 0 ≤ 2 - 4 * a by linarith)]

/-- An explicit multiplier slack absorbing the two denominator corrections
in the good-score successor bound. -/
noncomputable def coexposureSuccessorPerturbation (n : ℕ) : ℝ :=
  1000 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ)

/-- Eventually both score denominators are positive and the resulting
perturbation is small enough for the Gaussian-scale cutoff. -/
theorem eventually_coexposureSuccessorPerturbation_bounds :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧
      0 ≤ coexposureSuccessorPerturbation n ∧
      coexposureSuccessorPerturbation n ≤ 1 / Real.sqrt (n : ℝ) ∧
      0 < 1 - 192 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ∧
      0 < 1 - 24 * Real.log (n : ℝ) / (n : ℝ) ∧
      (1 - 192 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ))⁻¹ *
        (1 - 24 * Real.log (n : ℝ) / (n : ℝ))⁻¹ ≤
          1 + coexposureSuccessorPerturbation n := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  have hbound := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show 0 < (1 / 2 : ℝ) by norm_num)).comp_tendsto hcast).bound
      (show 0 < (1 / 1000 : ℝ) by norm_num)
  filter_upwards [hlog, hbound, eventually_ge_atTop (4 : ℕ)] with n hlogn hnorm hn4
  let x := (n : ℝ)
  let l := Real.log x
  let s := Real.sqrt x
  have hn : 0 < n := by omega
  have hx : 0 < x := by positivity
  have hl : 1 ≤ l := hlogn
  have hs₂ : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have hs_ge : 2 ≤ s := by
    change 2 ≤ Real.sqrt x
    have h := Real.sqrt_le_sqrt (show (4 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn4)
    rwa [show Real.sqrt (4 : ℝ) = 2 by norm_num] at h
  have hnorm' : l ^ 2 ≤ (1 / 1000 : ℝ) * s := by
    change ‖l ^ (2 : ℝ)‖ ≤ (1 / 1000 : ℝ) * ‖x ^ (1 / 2 : ℝ)‖ at hnorm
    rw [← Real.sqrt_eq_rpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg hs.le] at hnorm
    exact hnorm
  let d := coexposureSuccessorPerturbation n
  have hd : d = 1000 * l ^ 2 / x := rfl
  have hd₀ : 0 ≤ d := by rw [hd]; positivity
  have hd_s : d ≤ 1 / s := by
    calc
      d ≤ s / x := by rw [hd]; exact div_le_div_of_nonneg_right (by linarith) hx.le
      _ = s / s ^ 2 := by rw [hs₂]
      _ = 1 / s := by field_simp
  have hd_half : d ≤ 1 / 2 :=
    hd_s.trans (one_div_le_one_div_of_le (by norm_num) hs_ge)
  let a := 192 * l ^ 2 / x
  let b := 24 * l / x
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hsum : 4 * (a + b) ≤ d := by
    rw [hd]
    dsimp [a, b]
    rw [← add_div, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hx.le
    nlinarith [mul_nonneg (show 0 ≤ l - 1 by linarith) (show 0 ≤ l by linarith)]
  have ha : a ≤ 1 / 2 := (show a ≤ 4 * (a + b) by linarith).trans (hsum.trans hd_half)
  have hb : b ≤ 1 / 2 := (show b ≤ 4 * (a + b) by linarith).trans (hsum.trans hd_half)
  exact ⟨hn, hd₀, hd_s, by change 0 < 1 - a; linarith, by change 0 < 1 - b; linarith,
    (inv_one_sub_mul_le ha₀ hb₀ ha hb).trans (add_le_add_right hsum _)⟩

end LennonPittelFormalization

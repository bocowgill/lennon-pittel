module

public import LennonPittel.CycleSupportCount
public import LennonPittel.PivotForwardForest
public import LennonPittel.PointedSymmetricSums

/-!
# Two prescribed forward cycles and the complement forest

Fixing the outgoing rows on two disjoint cycle supports contributes one
arc product for each cycle. The remaining rows must form a forest rooted
at the union of the two supports (and at rows with no successor).
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The same outgoing arc at a shared vertex forces two realized cycles to coincide. -/
theorem RealizesDirectedCycle.eq_of_mem_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Option ι} {σ τ : Equiv.Perm ι} (hσ : RealizesDirectedCycle f σ)
    (hτ : RealizesDirectedCycle f τ) {i : ι} (hiσ : i ∈ σ.support)
    (hiτ : i ∈ τ.support) : σ = τ := by
  have hagree (j : ι) (hjσ : j ∈ σ.support) (hjτ : j ∈ τ.support) : σ j = τ j :=
    Option.some.inj ((hσ.2 j hjσ).symm.trans (hτ.2 j hjτ))
  have horbit (k : ℕ) : (σ ^ k) i = (τ ^ k) i ∧
      (σ ^ k) i ∈ σ.support ∧ (τ ^ k) i ∈ τ.support := by
    induction k with
    | zero => simpa using And.intro (rfl : i = i) (And.intro hiσ hiτ)
    | succ k ih =>
      obtain ⟨heq, hs, ht⟩ := ih
      simp only [pow_succ', Equiv.Perm.mul_apply]
      exact ⟨(hagree _ hs (heq ▸ ht)).trans (congrArg τ heq),
        Equiv.Perm.apply_mem_support.mpr hs, Equiv.Perm.apply_mem_support.mpr ht⟩
  apply Equiv.ext
  intro j
  by_cases hj : j ∈ σ.support
  · obtain ⟨k, hk⟩ := hσ.1.exists_pow_eq
      (Equiv.Perm.mem_support.mp hiσ) (Equiv.Perm.mem_support.mp hj)
    apply hagree j hj
    rw [← hk, (horbit k).1]
    exact (horbit k).2.2
  · have hjτ : j ∉ τ.support := by
      intro hjτ
      obtain ⟨k, hk⟩ := hτ.1.exists_pow_eq
        (Equiv.Perm.mem_support.mp hiτ) (Equiv.Perm.mem_support.mp hjτ)
      apply hj
      rw [← hk, ← (horbit k).1]
      exact (horbit k).2.1
    exact (Equiv.Perm.notMem_support.mp hj).trans (Equiv.Perm.notMem_support.mp hjτ).symm

/-- Distinct realized cycles have disjoint supports. -/
theorem RealizesDirectedCycle.disjoint_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Option ι} {σ τ : Equiv.Perm ι} (hσ : RealizesDirectedCycle f σ)
    (hτ : RealizesDirectedCycle f τ) (hne : σ ≠ τ) : Disjoint σ.support τ.support :=
  Finset.disjoint_left.mpr fun _ hiσ hiτ ↦ hne (hσ.eq_of_mem_support hτ hiσ hiτ)

/-- The two given cycles are distinct and exhaust the realized cycles. -/
def HasExactlyTwoDirectedCycles {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ τ : Equiv.Perm ι) : Prop :=
  σ ≠ τ ∧ RealizesDirectedCycle f σ ∧ RealizesDirectedCycle f τ ∧
    ∀ ρ, RealizesDirectedCycle f ρ → ρ = σ ∨ ρ = τ

/-- Two disjoint cyclic permutations are the only cycles iff the prescribed
arcs are present and the graph with both support sets erased is acyclic. -/
theorem hasExactlyTwoDirectedCycles_iff_prescribedRows_erase
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → Option ι}
    {σ τ : Equiv.Perm ι} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hd : Disjoint σ.support τ.support) :
    HasExactlyTwoDirectedCycles f σ τ ↔
      (∀ i ∈ σ.support ∪ τ.support, f i = if i ∈ σ.support then some (σ i) else some (τ i)) ∧
      IsAcyclicSuccessor (eraseSuccessorRows (σ.support ∪ τ.support) f) := by
  constructor
  · rintro ⟨_, hs, ht, hsole⟩
    refine ⟨fun i hi ↦ ?_, fun ρ hρ ↦ ?_⟩
    · by_cases h : i ∈ σ.support
      · simpa [h] using hs.2 i h
      · simpa [h] using ht.2 i ((Finset.mem_union.mp hi).resolve_left h)
    · have hout (i : ι) (hi : i ∈ ρ.support) : i ∉ σ.support ∪ τ.support := by
        intro h
        have harc := hρ.2 i hi
        simp [eraseSuccessorRows, h] at harc
      have hr : RealizesDirectedCycle f ρ :=
        ⟨hρ.1, fun i hi ↦ by simpa [eraseSuccessorRows, hout i hi] using hρ.2 i hi⟩
      rcases hsole ρ hr with rfl | rfl
      · obtain ⟨i, hi⟩ := hσ.nonempty_support
        exact hout i hi (Finset.mem_union_left _ hi)
      · obtain ⟨i, hi⟩ := hτ.nonempty_support
        exact hout i hi (Finset.mem_union_right _ hi)
  · rintro ⟨harc, hforest⟩
    have hne : σ ≠ τ := by
      rintro rfl
      obtain ⟨i, hi⟩ := hσ.nonempty_support
      exact Finset.disjoint_left.mp hd hi hi
    have hs : RealizesDirectedCycle f σ :=
      ⟨hσ, fun i hi ↦ by simpa [hi] using harc i (Finset.mem_union_left _ hi)⟩
    have ht : RealizesDirectedCycle f τ :=
      ⟨hτ, fun i hi ↦ by
        have hn : i ∉ σ.support := fun hm ↦ Finset.disjoint_left.mp hd hm hi
        simpa [hn] using harc i (Finset.mem_union_right _ hi)⟩
    refine ⟨hne, hs, ht, fun ρ hr ↦ ?_⟩
    by_cases hρσ : ρ = σ
    · exact Or.inl hρσ
    by_cases hρτ : ρ = τ
    · exact Or.inr hρτ
    exact False.elim (hforest ρ ⟨hr.1, fun i hi ↦ by
      have hn : i ∉ σ.support ∪ τ.support := by
        rw [Finset.mem_union, not_or]
        exact ⟨Finset.disjoint_left.mp (hr.disjoint_support hs hρσ) hi,
          Finset.disjoint_left.mp (hr.disjoint_support ht hρτ) hi⟩
      simpa [eraseSuccessorRows, hn] using hr.2 i hi⟩)

open scoped Classical in
/-- The exact two-cycle product mass factors into the two arc products and
the forest mass on the remaining rows. -/
theorem sum_product_hasExactlyTwoDirectedCycles_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → Option ι → ℝ)
    {σ τ : Equiv.Perm ι} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hd : Disjoint σ.support τ.support) :
    (∑ f : ι → Option ι, if HasExactlyTwoDirectedCycles f σ τ then ∏ i, w i (f i) else 0) =
      ((∏ i ∈ σ.support, w i (some (σ i))) * (∏ i ∈ τ.support, w i (some (τ i)))) *
        forestProductMass (eraseSuccessorWeights (σ.support ∪ τ.support) w) := by
  let s := σ.support ∪ τ.support
  let a : ι → Option ι := fun i ↦ if i ∈ σ.support then some (σ i) else some (τ i)
  have hp : (∏ i ∈ s, w i (a i)) =
      (∏ i ∈ σ.support, w i (some (σ i))) * (∏ i ∈ τ.support, w i (some (τ i))) := by
    rw [show s = σ.support ∪ τ.support from rfl, Finset.prod_union hd]
    congr 1
    · exact Finset.prod_congr rfl fun i hi ↦ congrArg (w i) (ite_eq_left hi)
    · exact Finset.prod_congr rfl fun i hi ↦ by
        exact congrArg (w i) (ite_eq_right fun hm ↦ Finset.disjoint_left.mp hd hm hi)
  rw [← hp, forestProductMass, ← sum_product_prescribed_rows_erase_eq w s a]
  apply Finset.sum_congr rfl
  intro f _
  rw [hasExactlyTwoDirectedCycles_iff_prescribedRows_erase hσ hτ hd]
  let A := ∀ i ∈ s, f i = a i
  let F := IsAcyclicSuccessor (eraseSuccessorRows s f)
  by_cases ha : ∀ i ∈ s, f i = a i
  · by_cases hf : IsAcyclicSuccessor (eraseSuccessorRows s f)
    · rw [ite_eq_left (show A ∧ F from ⟨ha, hf⟩), ite_eq_left ha, ite_eq_left hf, mul_one]
    · rw [ite_eq_right (show ¬ (A ∧ F) from fun h ↦ hf h.2), ite_eq_left ha, ite_eq_right hf, mul_zero]
  · rw [ite_eq_right (show ¬ (A ∧ F) from fun h ↦ ha h.1), ite_eq_right ha, mul_zero]

/-- Given the diagonal of a stable mark, the probability of exactly two
prescribed forward cycles is their arc product times the complement forest mass. -/
theorem measureReal_pi_exactlyTwoForwardCycles_eq {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n)
    {σ τ : Matching n} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hd : Disjoint σ.support τ.support)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    (Measure.pi (normalizedStableScoreRowLaw d)).real
      {r | HasExactlyTwoDirectedCycles (fun i ↦ forwardSuccessorOutcome d i (r i)) σ τ} =
      ((∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
        (∏ i ∈ τ.support, forwardOutcomeWeight d i (some (τ i)))) *
          forestProductMass
            (eraseSuccessorWeights (σ.support ∪ τ.support) (forwardOutcomeWeight d)) := by
  classical
  change (Measure.pi (normalizedStableScoreRowLaw d)).real
    ((fun r i ↦ forwardSuccessorOutcome d i (r i)) ⁻¹'
      {f | HasExactlyTwoDirectedCycles f σ τ}) = _
  rw [measureReal_pi_forwardOutcome_eq_sum d hx hy]
  simpa only [Set.mem_ofPred_eq] using
    sum_product_hasExactlyTwoDirectedCycles_eq (forwardOutcomeWeight d) hσ hτ hd

/-- The two-cycle forest bound with a weighted row deficit. -/
theorem measureReal_pi_exactlyTwoForwardCycles_le {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n)
    {σ τ : Matching n} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hdisj : Disjoint σ.support τ.support)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    (hY : 0 < ∑ i, (diagonalPairAt d i).2) {b : ℝ}
    (hdef : HasForwardReferenceDeficit d b) :
    (Measure.pi (normalizedStableScoreRowLaw d)).real
      {r | HasExactlyTwoDirectedCycles (fun i ↦ forwardSuccessorOutcome d i (r i)) σ τ} ≤
      ((∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
        (∏ i ∈ τ.support, forwardOutcomeWeight d i (some (τ i)))) *
          (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
            ∑ i ∈ σ.support ∪ τ.support, forwardSpouseWeight d i)) := by
  let w := forwardOutcomeWeight d
  let p := forwardSpouseWeight d
  let : ∀ i : Fin n, IsProbabilityMeasure (forwardSuccessorOutcomeLaw d i) := fun i ↦
    forwardSuccessorOutcomeLaw_isProbabilityMeasure d i (hx i) hy
  have hw (i : Fin n) (o : Option (Fin n)) : 0 ≤ w i o := ENNReal.toReal_nonneg
  have hw₁ (i : Fin n) : ∑ o, w i o = 1 := by
    unfold w forwardOutcomeWeight
    rw [sum_measureReal_singleton]
    simp only [Finset.coe_univ, measureReal_def, measure_univ, ENNReal.toReal_one]
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have ht : ∑ i, p i = 1 := by
    unfold p forwardSpouseWeight
    rw [← Finset.sum_div, div_self hY.ne']
  obtain ⟨δ, hd, hbudget, harc⟩ := hdef
  have harc' (i j : Fin n) (hij : i ≠ j) : (1 - δ i) * p j ≤ w i (some j) := by
    let := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
    rw [show w i (some j) = _ from forwardOutcomeWeight_some d i ⟨j, hij⟩]
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (harc i ⟨j, hij⟩)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr (hd i).2) (hp j))] at h
  rw [measureReal_pi_exactlyTwoForwardCycles_eq d hσ hτ hdisj hx hy]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg fun i _ ↦ hw i _) (Finset.prod_nonneg fun i _ ↦ hw i _))
  refine (forestProductMass_eraseSuccessorWeights_le (σ.support ∪ τ.support)
    w hw hw₁ hp ht hd harc').trans ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hbudget le_rfl) le_rfl) (Real.exp_pos _).le

/-- The given distinct rotations exhaust the exposed forward rotations. -/
def HasExactlyTwoForwardExposedRotations {n : ℕ} (p : Profile n) (μ σ τ : Matching n) : Prop :=
  σ ≠ τ ∧ IsExposedRotation p μ σ ∧ IsExposedRotation p μ τ ∧
    ∀ ρ, IsExposedRotation p μ ρ → ρ = σ ∨ ρ = τ

/-- The two-rotation event on reconstructed rows at a fixed marked diagonal. -/
def exactlyTwoForwardExposedRowEvent {n : ℕ} (μ σ τ : Matching n)
    (d : DiagonalScorePairs n) : Set (OffDiagonalScoreRows n) :=
  {r | HasExactlyTwoForwardExposedRotations
    (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ σ τ}

/-- At almost every valid diagonal, the same fixed-pair bound holds for actual
rank-exposed rotations of the reconstructed profiles. -/
theorem ae_diagonal_measureReal_exactlyTwoForwardExposed_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      0 < (∑ i, (diagonalPairAt d i).2) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b →
        ∀ {σ τ : Matching n}, σ.IsCycle → τ.IsCycle → Disjoint σ.support τ.support →
          (Measure.pi (normalizedStableScoreRowLaw d)).real
            (exactlyTwoForwardExposedRowEvent μ σ τ d) ≤
              ((∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
                (∏ i ∈ τ.support, forwardOutcomeWeight d i (some (τ i)))) *
                  (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
                    ∑ i ∈ σ.support ∪ τ.support, forwardSpouseWeight d i)) := by
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hd
  intro hx hy hY b hdef σ τ hσ hτ hdisj
  have heq : exactlyTwoForwardExposedRowEvent μ σ τ d
      =ᵐ[Measure.pi (normalizedStableScoreRowLaw d)]
      {r | HasExactlyTwoDirectedCycles (fun i ↦ forwardSuccessorOutcome d i (r i)) σ τ} := by
    filter_upwards [hd hx hy] with r hr
    have hbridge (ρ : Matching n) := realizesDirectedCycle_forwardOutcome_iff μ d r ρ hr.2 hr.1
    apply propext
    constructor
    · rintro ⟨hne, hs, ht, hsole⟩
      exact ⟨hne, (hbridge σ).mpr hs, (hbridge τ).mpr ht,
        fun ρ hρ ↦ hsole ρ ((hbridge ρ).mp hρ)⟩
    · rintro ⟨hne, hs, ht, hsole⟩
      exact ⟨hne, (hbridge σ).mp hs, (hbridge τ).mp ht,
        fun ρ hρ ↦ hsole ρ ((hbridge ρ).mpr hρ)⟩
  have hm := measure_congr heq
  unfold Measure.real
  rw [hm]
  exact measureReal_pi_exactlyTwoForwardCycles_le d hσ hτ hdisj hx hy hY hdef

/-- On a good diagonal, bound both arc products by the reference spouse weights. -/
theorem ae_diagonal_measureReal_exactlyTwoForwardExposed_le_of_goodDiagonalScores {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (μ : Matching n) (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b →
        ∀ {σ τ : Matching n}, σ.IsCycle → τ.IsCycle → Disjoint σ.support τ.support →
          (Measure.pi (normalizedStableScoreRowLaw d)).real
            (exactlyTwoForwardExposedRowEvent μ σ τ d) ≤
              ((1 + coexposureSuccessorPerturbation n) ^ (σ.support ∪ τ.support).card *
                ∏ i ∈ σ.support ∪ τ.support, forwardSpouseWeight d i) *
                  (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
                    ∑ i ∈ σ.support ∪ τ.support, forwardSpouseWeight d i)) := by
  filter_upwards [ae_diagonal_measureReal_exactlyTwoForwardExposed_le μ] with d hd
  intro hg hx hy b hb σ τ hσ hτ hdisj
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY.le
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hsum, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hsum
  have hprod (ρ : Matching n) :=
    prod_forwardOutcomeWeight_le_of_arc_le ρ fun i j hij ↦
      forwardOutcomeWeight_some_le_of_goodDiagonalScores hg hx hy hA hB hδ i ⟨j, hij⟩
  refine (hd hx hy hY b hb hσ hτ hdisj).trans ?_
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (Real.exp_pos _).le (add_nonneg
      (add_nonneg hb₀ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (Finset.sum_nonneg fun i _ ↦ hp i)))
  rw [Finset.card_union_of_disjoint hdisj, Finset.prod_union hdisj, pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hprod σ) (hprod τ)
    (Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg)
    ((Finset.prod_nonneg fun _ _ ↦ ENNReal.toReal_nonneg).trans (hprod σ))

open scoped Classical in
/-- Cyclic permutations of the specified length. -/
noncomputable def forwardCyclesOfLength (n k : ℕ) : Finset (Matching n) :=
  Finset.univ.filter fun σ ↦ σ.IsCycle ∧ σ.support.card = k

private theorem descFactorialRatio_le_one {n j : ℕ} (hn : 0 < n) (hj : j ≤ n)
    (hj₁ : 1 ≤ j) : (n.descFactorial j : ℝ) / (n : ℝ) ^ j ≤ 1 := by
  have hj₁' : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
  exact (descFactorial_div_pow_le_exp hn hj).trans <| Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hj₁'))
      (by positivity)))

/-- Summing the reference arc product over length-k cycles costs at most 1/k. -/
theorem sum_forwardCyclesOfLength_prod_le {n k : ℕ} (hn : 0 < n)
    (hk : 2 ≤ k) (hkn : k ≤ n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    (∑ σ ∈ forwardCyclesOfLength n k, ∏ i ∈ σ.support, p i) ≤ 1 / (k : ℝ) := by
  have hk0 : 0 < k := by omega
  have hkfac : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred hk0.ne'
  have hchoose : (k.factorial : ℝ) * (n.choose k : ℝ) = (n.descFactorial k : ℝ) := by
    rw [← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
  rw [forwardCyclesOfLength, sum_cyclesWithLength_by_support k hk (fun S ↦ ∏ i ∈ S, p i)]
  change ((k - 1).factorial : ℝ) * coexposureEsymm Finset.univ k p ≤ _
  calc
    _ ≤ ((k - 1).factorial : ℝ) * ((n.choose k : ℝ) * (1 / (n : ℝ)) ^ k) :=
      mul_le_mul_of_nonneg_left (coexposureEsymm_le_uniform hn k hp hp₁) (Nat.cast_nonneg _)
    _ = (1 / (k : ℝ)) * ((n.descFactorial k : ℝ) / (n : ℝ) ^ k) := by
      rw [← hchoose, ← hkfac, one_div_pow]
      field_simp
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (descFactorialRatio_le_one hn hkn (by omega))

/-- If the support mass is included, the length-k sum costs at most
the sum of squared reference weights. -/
theorem sum_forwardCyclesOfLength_prod_mul_mass_le {n k : ℕ} (hn : 0 < n)
    (hk : 2 ≤ k) (hkn : k ≤ n) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    (∑ σ ∈ forwardCyclesOfLength n k,
      (∏ i ∈ σ.support, p i) * (∑ i ∈ σ.support, p i)) ≤ ∑ i, p i ^ 2 := by
  rw [forwardCyclesOfLength, sum_cyclesWithLength_by_support k hk
    (fun S ↦ (∏ i ∈ S, p i) * (∑ i ∈ S, p i))]
  have hw := weightedSupportLengthSum_le hn hk hkn hp hp₁ (τ := 0) le_rfl
  simp only [zero_add, zero_div, zero_mul] at hw
  exact hw.trans (mul_le_of_le_one_right (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
    (descFactorialRatio_le_one hn (show k - 1 ≤ n by omega) (by omega)))

/-- The finite sum of exact-two probabilities counts ordered choices of the
two rotations. The bound retains the two inverse-length factors; the
support-mass term costs one additional squared weight at a chosen vertex. -/
theorem sum_measureReal_exactlyTwoForwardExposedLengths_le {n k l : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (P : Ω → Profile n) (μ : Matching n)
    (hn : 0 < n) (hk : 2 ≤ k) (hl : 2 ≤ l) (hkn : k ≤ n) (hln : l ≤ n)
    {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {b η : ℝ} (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hcycle : ∀ {σ τ : Matching n}, σ.IsCycle → τ.IsCycle → Disjoint σ.support τ.support →
      ν.real {x | HasExactlyTwoForwardExposedRotations (P x) μ σ τ} ≤
        ((1 + η) ^ (σ.support ∪ τ.support).card * ∏ i ∈ σ.support ∪ τ.support, p i) *
          (Real.exp 1 * (b + (∑ i, p i ^ 2) + ∑ i ∈ σ.support ∪ τ.support, p i))) :
    (∑ σ ∈ forwardCyclesOfLength n k, ∑ τ ∈ forwardCyclesOfLength n l,
      ν.real {x | HasExactlyTwoForwardExposedRotations (P x) μ σ τ}) ≤
      Real.exp 1 * (1 + η) ^ (k + l) *
        ((b + (∑ i, p i ^ 2) + ((k : ℝ) + l) * ∑ i, p i ^ 2) / ((k : ℝ) * l)) := by
  classical
  let K := forwardCyclesOfLength n k
  let L := forwardCyclesOfLength n l
  let A (σ : Matching n) := ∏ i ∈ σ.support, p i
  let M (σ : Matching n) := ∑ i ∈ σ.support, p i
  let s := ∑ i, p i ^ 2
  let c := Real.exp 1 * (1 + η) ^ (k + l)
  have hA (σ : Matching n) : 0 ≤ A σ := Finset.prod_nonneg fun i _ ↦ hp i
  have hM (σ : Matching n) : 0 ≤ M σ := Finset.sum_nonneg fun i _ ↦ hp i
  have hs : 0 ≤ s := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hc : 0 ≤ c := mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith) _)
  have hkl (σ : Matching n) (hσ : σ ∈ K) : σ.IsCycle ∧ σ.support.card = k :=
    (Finset.mem_filter.mp hσ).2
  have hll (τ : Matching n) (hτ : τ ∈ L) : τ.IsCycle ∧ τ.support.card = l :=
    (Finset.mem_filter.mp hτ).2
  change (∑ σ ∈ K, ∑ τ ∈ L, _) ≤ c * ((b + s + ((k : ℝ) + l) * s) / ((k : ℝ) * l))
  calc
    _ ≤ ∑ σ ∈ K, ∑ τ ∈ L, c *
        ((b + s) * (A σ * A τ) + (A σ * M σ) * A τ + A σ * (A τ * M τ)) := by
      refine Finset.sum_le_sum fun σ hσ ↦ Finset.sum_le_sum fun τ hτ ↦ ?_
      obtain ⟨hcσ, hkσ⟩ := hkl σ hσ
      obtain ⟨hcτ, hkτ⟩ := hll τ hτ
      by_cases hd : Disjoint σ.support τ.support
      · refine (hcycle hcσ hcτ hd).trans_eq ?_
        rw [Finset.card_union_of_disjoint hd, hkσ, hkτ, Finset.prod_union hd, Finset.sum_union hd]
        change ((1 + η) ^ (k + l) * (A σ * A τ)) *
          (Real.exp 1 * (b + s + (M σ + M τ))) = _
        unfold c
        ring
      · have he : {x | HasExactlyTwoForwardExposedRotations (P x) μ σ τ} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨hne, hσ, hτ, _⟩ := hx
          exact hd (Finset.disjoint_left.mpr fun i hiσ hiτ ↦
            (Equiv.Perm.mem_support.mp hiτ)
              (hσ.disjoint_moved hτ hne i (Equiv.Perm.mem_support.mp hiσ)))
        rw [he, measureReal_empty]
        exact mul_nonneg hc (add_nonneg (add_nonneg
          (mul_nonneg (add_nonneg hb hs) (mul_nonneg (hA σ) (hA τ)))
          (mul_nonneg (mul_nonneg (hA σ) (hM σ)) (hA τ)))
          (mul_nonneg (hA σ) (mul_nonneg (hA τ) (hM τ))))
    _ = c * ((b + s) * ((∑ σ ∈ K, A σ) * ∑ τ ∈ L, A τ) +
          (∑ σ ∈ K, A σ * M σ) * (∑ τ ∈ L, A τ) +
          (∑ σ ∈ K, A σ) * ∑ τ ∈ L, A τ * M τ) := by
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_add]
      rw [Finset.sum_comm (s := K) (t := L), Finset.sum_comm (s := K) (t := L),
        Finset.sum_comm (s := K) (t := L)]
    _ ≤ c * ((b + s) * ((1 / (k : ℝ)) * (1 / (l : ℝ))) +
          s * (1 / (l : ℝ)) + (1 / (k : ℝ)) * s) := by
      have hAk := sum_forwardCyclesOfLength_prod_le hn hk hkn hp hp₁
      have hAl := sum_forwardCyclesOfLength_prod_le hn hl hln hp hp₁
      have hMk := sum_forwardCyclesOfLength_prod_mul_mass_le hn hk hkn hp hp₁
      have hMl := sum_forwardCyclesOfLength_prod_mul_mass_le hn hl hln hp hp₁
      have hAl₀ : 0 ≤ ∑ τ ∈ L, A τ := Finset.sum_nonneg fun _ _ ↦ hA _
      have hMl₀ : 0 ≤ ∑ τ ∈ L, A τ * M τ :=
        Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hA _) (hM _)
      have hk₀ : 0 ≤ 1 / (k : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul hAk hAl hAl₀ hk₀) (add_nonneg hb hs))
        (mul_le_mul hMk hAl hAl₀ hs)) (mul_le_mul hAk hMl hMl₀ hk₀)) hc
    _ = _ := by
      congr 1
      have hk₀ : (k : ℝ) ≠ 0 := by positivity
      have hl₀ : (l : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- The exact conditional score law satisfies the ordered two-cycle
length bound on almost every good diagonal. -/
theorem ae_diagonal_sum_measureReal_exactlyTwoForwardExposedLengths_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (hn : 0 < n) (μ : Matching n) (hη : 0 ≤ coexposureSuccessorPerturbation n)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n) (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b →
        ∀ k l : ℕ, 2 ≤ k → 2 ≤ l → k ≤ n → l ≤ n →
          (∑ σ ∈ forwardCyclesOfLength n k, ∑ τ ∈ forwardCyclesOfLength n l,
            (Measure.pi (normalizedStableScoreRowLaw d)).real
              (exactlyTwoForwardExposedRowEvent μ σ τ d)) ≤
            Real.exp 1 * (1 + coexposureSuccessorPerturbation n) ^ (k + l) *
              ((b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
                ((k : ℝ) + l) * ∑ i, (forwardSpouseWeight d i) ^ 2) / ((k : ℝ) * l)) := by
  filter_upwards
    [ae_diagonal_measureReal_exactlyTwoForwardExposed_le_of_goodDiagonalScores μ hA hB hδ]
    with d hd
  intro hg hx hy b hb k l hk hl hkn hln
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY.le
  have hp₁ : ∑ i, forwardSpouseWeight d i = 1 := by
    unfold forwardSpouseWeight
    rw [← Finset.sum_div, div_self hY.ne']
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hsum, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hsum
  exact sum_measureReal_exactlyTwoForwardExposedLengths_le _ _ μ hn hk hl hkn hln
    hp hp₁ hb₀ hη (hd hg hx hy b hb)

/-- Integer lengths in the closed square-root window, restricted to actual
cycle lengths in the market. -/
noncomputable def forwardLengthWindow (n : ℕ) (α A : ℝ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun k ↦ α * Real.sqrt n ≤ (k : ℝ) ∧ (k : ℝ) ≤ A * Real.sqrt n

/-- Double summation over square-root windows absorbs the two inverse lengths.
The exponent is uniform as long as the row perturbation is at most 1/√n. -/
theorem sum_forwardLengthWindow_pairs_le {n : ℕ} (hn : 0 < n) {α A b s η : ℝ}
    (hα : 0 < α) (hA : 0 ≤ A) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hη₀ : 0 ≤ η) (hη : η ≤ 1 / Real.sqrt (n : ℝ)) (g : ℕ → ℕ → ℝ)
    (hg : ∀ k l, 2 ≤ k → 2 ≤ l → k ≤ n → l ≤ n →
      g k l ≤ Real.exp 1 * (1 + η) ^ (k + l) *
        ((b + s + ((k : ℝ) + l) * s) / ((k : ℝ) * l))) :
    (∑ k ∈ forwardLengthWindow n α A, ∑ l ∈ forwardLengthWindow n α A, g k l) ≤
      Real.exp (1 + 2 * A) * ((A + 1) / α) ^ 2 * (b + s + (2 * A * Real.sqrt n) * s) := by
  let r := Real.sqrt (n : ℝ)
  let L := forwardLengthWindow n α A
  let N := b + s + (2 * A * r) * s
  let C := Real.exp (1 + 2 * A) * (N / (α * r) ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hr₁ : 1 ≤ r := by
    change 1 ≤ Real.sqrt (n : ℝ)
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hmem (k : ℕ) (hk : k ∈ L) :
      (2 ≤ k ∧ k ≤ n) ∧ α * r ≤ (k : ℝ) ∧ (k : ℝ) ≤ A * r := by
    simpa only [L, forwardLengthWindow, Finset.mem_filter, Finset.mem_Icc] using hk
  have hAr : 0 ≤ A * r := mul_nonneg hA hr.le
  have hcL : (L.card : ℝ) ≤ (A + 1) * r := by
    let m := ⌊A * r⌋₊
    have hsub : L ⊆ Finset.range (m + 1) := by
      intro k hk
      have hkm : k ≤ m := Nat.le_floor ((hmem k hk).2.2)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hkm)
    calc
      _ ≤ ((Finset.range (m + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (m : ℝ) + 1 := by rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
      _ ≤ (A + 1) * r := by linarith [Nat.floor_le hAr]
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hαr : 0 < α * r := mul_pos hα hr
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgC (k l : ℕ) (hk : k ∈ L) (hl : l ∈ L) : g k l ≤ C := by
    obtain ⟨⟨hk₂, hkn⟩, hkl, hku⟩ := hmem k hk
    obtain ⟨⟨hl₂, hln⟩, hll, hlu⟩ := hmem l hl
    have hsum : (k : ℝ) + l ≤ 2 * A * r := by linarith
    have hpow : (1 + η) ^ (k + l) ≤ Real.exp (2 * A) := calc
      _ ≤ (Real.exp η) ^ (k + l) := pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp η) _
      _ = Real.exp (((k : ℝ) + l) * η) := by rw [← Real.exp_nat_mul, Nat.cast_add]
      _ ≤ _ := Real.exp_le_exp.mpr <| calc
        _ ≤ ((k : ℝ) + l) * (1 / r) := mul_le_mul_of_nonneg_left hη (by positivity)
        _ ≤ (2 * A * r) * (1 / r) := mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = _ := by field_simp
    have hden : (α * r) ^ 2 ≤ (k : ℝ) * l := by
      rw [pow_two]
      exact mul_le_mul hkl hll hαr.le (hαr.le.trans hkl)
    have hnumer : b + s + ((k : ℝ) + l) * s ≤ N :=
      add_le_add_right (mul_le_mul_of_nonneg_right hsum hs) _
    have hfrac : (b + s + ((k : ℝ) + l) * s) / ((k : ℝ) * l) ≤ N / (α * r) ^ 2 :=
      (div_le_div_of_nonneg_right hnumer (by positivity)).trans
        (div_le_div_of_nonneg_left hN (by positivity) hden)
    refine (hg k l hk₂ hl₂ hkn hln).trans ?_
    unfold C
    rw [Real.exp_add]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le) hfrac
      (by positivity) (by positivity)
  calc
    _ ≤ ∑ k ∈ L, ∑ l ∈ L, C := Finset.sum_le_sum fun k hk ↦
      Finset.sum_le_sum fun l hl ↦ hgC k l hk hl
    _ = (L.card : ℝ) ^ 2 * C := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two, mul_assoc]
    _ ≤ ((A + 1) * r) ^ 2 * C :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcL 2) hC
    _ = _ := by
      unfold C
      change ((A + 1) * r) ^ 2 * (Real.exp (1 + 2 * A) * (N / (α * r) ^ 2)) =
        Real.exp (1 + 2 * A) * ((A + 1) / α) ^ 2 * N
      field_simp

/-- On almost every good diagonal, the normalized conditional law gives the
square-root-window bound for the ordered exact-two mass. -/
theorem ae_diagonal_sum_measureReal_exactlyTwoForwardExposedWindow_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (hn : 0 < n) (μ : Matching n) {α A : ℝ} (hα : 0 < α) (hA₀ : 0 ≤ A)
    (hη₀ : 0 ≤ coexposureSuccessorPerturbation n)
    (hη : coexposureSuccessorPerturbation n ≤ 1 / Real.sqrt (n : ℝ))
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n) (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b →
        (∑ k ∈ forwardLengthWindow n α A, ∑ l ∈ forwardLengthWindow n α A,
          ∑ σ ∈ forwardCyclesOfLength n k, ∑ τ ∈ forwardCyclesOfLength n l,
            (Measure.pi (normalizedStableScoreRowLaw d)).real
              (exactlyTwoForwardExposedRowEvent μ σ τ d)) ≤
          Real.exp (1 + 2 * A) * ((A + 1) / α) ^ 2 *
            (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
              (2 * A * Real.sqrt n) * ∑ i, (forwardSpouseWeight d i) ^ 2) := by
  filter_upwards
    [ae_diagonal_sum_measureReal_exactlyTwoForwardExposedLengths_le hn μ hη₀ hA hB hδ] with d hd
  intro hg hx hy b hb
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY.le
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hsum, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hsum
  exact sum_forwardLengthWindow_pairs_le hn hα hA₀ hb₀
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hη₀ hη _ (hd hg hx hy b hb)

end LennonPittelFormalization

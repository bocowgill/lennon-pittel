module

public import LennonPittel.CoexposureScoreMomentBound
public import LennonPittel.ForestProductProbability
public import LennonPittel.ForestRankOne
public import LennonPittel.ForestRowThinning
public import LennonPittel.ForwardSuccessorOutcome
public import LennonPittel.PivotForwardRowDeficit
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The complement forest bound for actual forward successors

The finite successor outcomes retain the independent score-row law. After
the rows of a prescribed cycle are fixed, a second cycle must be contained
in the remaining rows. These rows can be compared to the reference forest.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

open scoped Classical in
/-- The real mass of an event of finitely many independent finite outcomes. -/
theorem measureReal_pi_eq_sum_event {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : ι → Measure β) [∀ i, IsProbabilityMeasure (ν i)] (E : Set (ι → β)) :
    (Measure.pi ν).real E =
      ∑ f : ι → β, if f ∈ E then ∏ i, (ν i).real {f i} else 0 := by
  let S : Finset (ι → β) := Finset.univ.filter (· ∈ E)
  have hS : (S : Set (ι → β)) = E := by
    ext f
    simp [S]
  have hsingle (f : ι → β) : (Measure.pi ν).real {f} = ∏ i, (ν i).real {f i} := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rw [← hS, ← sum_measureReal_singleton S]
  simp_rw [hsingle]
  rw [hS, ← Finset.sum_filter]

private theorem sum_measureReal_singletons_eq_one {β : Type*} [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Measure β) [IsProbabilityMeasure ν] : ∑ o, ν.real {o} = 1 := by
  rw [sum_measureReal_singleton]
  simp only [Finset.coe_univ, measureReal_def, measure_univ, ENNReal.toReal_one]

open scoped Classical in
/-- The reference keeps each off-diagonal arc at its rank-one weight and
sends the remaining probability to the sink. -/
noncomputable def forwardReferenceWeight {ι : Type*} [Fintype ι]
    (p δ : ι → ℝ) (i : ι) : Option ι → ℝ
  | some j => if i = j then 0 else (1 - δ i) * p j
  | none => 1 - ∑ j, if i = j then 0 else (1 - δ i) * p j

theorem sum_forwardReferenceWeight {ι : Type*} [Fintype ι] (p δ : ι → ℝ) (i : ι) :
    (∑ o, forwardReferenceWeight p δ i o) = 1 := by
  rw [Fintype.sum_option]
  simp only [forwardReferenceWeight, sub_add_cancel]

open scoped Classical in
theorem forwardReferenceWeight_nonneg {ι : Type*} [Fintype ι] {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hd : ∀ i, δ i ∈ Icc 0 1)
    (i : ι) (o : Option ι) : 0 ≤ forwardReferenceWeight p δ i o := by
  have harc (j : ι) : 0 ≤ (1 - δ i) * p j :=
    mul_nonneg (sub_nonneg.mpr (hd i).2) (hp j)
  have hfac : 1 - δ i ≤ 1 := sub_le_self _ (hd i).1
  cases o with
  | none =>
    simp only [forwardReferenceWeight]
    apply sub_nonneg.mpr
    refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_) (le_of_eq ht)
    by_cases hij : i = j
    · simpa only [ite_eq_left hij] using hp j
    · simpa only [ite_eq_right hij] using mul_le_of_le_one_left (hp j) hfac
  | some j =>
    by_cases hij : i = j
    · simp only [forwardReferenceWeight, ite_eq_left hij, le_refl]
    · simpa only [forwardReferenceWeight, ite_eq_right hij] using harc j

open scoped Classical in
/-- The reference forest bound when all outgoing arcs on a given support
are removed. The removed rows contribute at most their total target weight. -/
theorem forestProductMass_forwardReferenceWeight_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hd : ∀ i, δ i ∈ Icc 0 1) :
    forestProductMass (forwardReferenceWeight p (fun i ↦ if i ∈ S then 1 else δ i)) ≤
      Real.exp 1 * ((∑ i, p i * δ i) + (∑ i, p i ^ 2) + ∑ i ∈ S, p i) := by
  let δ' (i : ι) := if i ∈ S then (1 : ℝ) else δ i
  let u (i : ι) := (1 - δ' i) * p i
  have hd' (i : ι) : δ' i ∈ Icc 0 1 := by
    by_cases hi : i ∈ S
    · simp [δ', hi]
    · simpa only [δ', ite_eq_right hi] using hd i
  have hloop (i : ι) : forwardReferenceWeight p δ' i (some i) = 0 := by
    simp [forwardReferenceWeight]
  have hu (i : ι) : 0 ≤ u i := mul_nonneg (sub_nonneg.mpr (hd' i).2) (hp i)
  have hut : ∑ i, u i ≤ 1 :=
    (Finset.sum_le_sum fun i _ ↦ mul_le_of_le_one_left (hp i) (sub_le_self _ (hd' i).1)).trans_eq ht
  rw [forestProductMass_eq_det _ (sum_forwardReferenceWeight p δ') hloop]
  have hM : Matrix.of (fun i j ↦ forwardReferenceWeight p δ' i (some j)) =
      rankOneOffDiagonal (fun i ↦ 1 - δ' i) p := by
    ext i j
    by_cases h : i = j <;> simp [forwardReferenceWeight, rankOneOffDiagonal, h]
  rw [hM]
  refine (det_one_sub_rankOneOffDiagonal_le _ _ hu hut).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine (referenceForestError_le hp ht hd').trans ?_
  have hδsum : (∑ i, p i * δ' i) ≤ (∑ i, p i * δ i) + ∑ i ∈ S, p i := by
    calc
      _ ≤ ∑ i, (p i * δ i + if i ∈ S then p i else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ S
        · simpa only [δ', ite_eq_left hi, mul_one] using
            (le_add_of_nonneg_left (mul_nonneg (hp i) (hd i).1))
        · simp only [δ', ite_eq_right hi, add_zero, le_refl]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_filter]; simp
  linarith only [hδsum]

open scoped Classical in
/-- Rowwise thinning and the complement determinant bound apply to any
normalized nonnegative array of actual forward outcomes. -/
theorem forestProductMass_eraseSuccessorWeights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : ι → Option ι → ℝ) {p δ : ι → ℝ}
    (hw : ∀ i o, 0 ≤ w i o) (hw₁ : ∀ i, ∑ o, w i o = 1)
    (hp : ∀ i, 0 ≤ p i) (ht : ∑ i, p i = 1) (hd : ∀ i, δ i ∈ Icc 0 1)
    (harc : ∀ i j, i ≠ j → (1 - δ i) * p j ≤ w i (some j)) :
    forestProductMass (eraseSuccessorWeights S w) ≤
      Real.exp 1 * ((∑ i, p i * δ i) + (∑ i, p i ^ 2) + ∑ i ∈ S, p i) := by
  let δ' (i : ι) := if i ∈ S then (1 : ℝ) else δ i
  have hd' (i : ι) : δ' i ∈ Icc 0 1 := by
    by_cases hi : i ∈ S
    · simp [δ', hi]
    · simpa only [δ', ite_eq_right hi] using hd i
  refine (forestProductMass_le_of_arc_le (eraseSuccessorWeights S w)
    (forwardReferenceWeight p δ') (eraseSuccessorWeights_nonneg S hw)
    (forwardReferenceWeight_nonneg hp ht hd') (sum_eraseSuccessorWeights S hw₁)
    (sum_forwardReferenceWeight p δ') ?_).trans
      (forestProductMass_forwardReferenceWeight_le S hp ht hd)
  intro i j
  by_cases hi : i ∈ S
  · rw [eraseSuccessorWeights_some, ite_eq_left hi]
    simp [forwardReferenceWeight, δ', hi]
  · rw [eraseSuccessorWeights_some, ite_eq_right hi]
    by_cases hij : i = j
    · simpa [forwardReferenceWeight, hij] using hw i (some j)
    · simpa only [forwardReferenceWeight, ite_eq_right hij, δ', ite_eq_right hi] using harc i j hij

/-- The real finite row weights of the actual conditional forward outcome. -/
noncomputable def forwardOutcomeWeight {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) (o : Option (Fin n)) : ℝ :=
  (forwardSuccessorOutcomeLaw d i).real {o}

theorem forwardOutcomeWeight_some {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    forwardOutcomeWeight d i (some j.val) =
      (normalizedStableScoreRowLaw d i).real (scoreRowSuccessorEvent d i j) := by
  simp only [forwardOutcomeWeight, measureReal_def, forwardSuccessorOutcomeLaw_some]

/-- The complementary upper comparison uses the existing good-diagonal
arc estimate, with normalization removed explicitly. -/
theorem forwardOutcomeWeight_some_le_of_goodDiagonalScores {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    {d : DiagonalScorePairs n} (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ j, (diagonalPairAt d j).2 ∈ Icc 0 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    forwardOutcomeWeight d i (some j.val) ≤
      (1 + coexposureSuccessorPerturbation n) * forwardSpouseWeight d j.val := by
  rw [forwardOutcomeWeight_some]
  let ν := stableScoreRowLaw d i
  let E := scoreRowSuccessorEvent d i j
  let C := (1 + coexposureSuccessorPerturbation n) * forwardSpouseWeight d j.val
  have hC : 0 ≤ C :=
    mul_nonneg ((mul_nonneg (inv_nonneg.mpr hA.le) (inv_nonneg.mpr hB.le)).trans hδ)
      (div_nonneg (hy j.val).1 ((by norm_num : (0 : ℝ) ≤ 2).trans hg.1))
  have h := stableScoreRowLaw_successor_le_of_goodDiagonalScores hg hx hy hA hB hδ i j
  change ν E ≤ ν univ * ENNReal.ofReal C at h
  have hn : normalizedStableScoreRowLaw d i E ≤ ENNReal.ofReal C := by
    rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul]
    change (ν univ)⁻¹ * ν E ≤ _
    calc
      _ ≤ (ν univ)⁻¹ * (ν univ * ENNReal.ofReal C) := mul_le_mul_right h _
      _ = ((ν univ)⁻¹ * ν univ) * ENNReal.ofReal C := (mul_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal C := by
        simpa only [one_mul] using
          (mul_le_mul' (ν univ).inv_mul_le_one (le_refl (ENNReal.ofReal C)))
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hn

/-- Multiplying the arc comparisons on a cycle uses each support weight once. -/
theorem prod_forwardOutcomeWeight_le_of_arc_le {n : ℕ} [MeasurableSpace (Option (Fin n))]
    {d : DiagonalScorePairs n} (σ : Matching n) {C : ℝ}
    (harc : ∀ i j, i ≠ j → forwardOutcomeWeight d i (some j) ≤ C * forwardSpouseWeight d j) :
    (∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) ≤
      C ^ σ.support.card * ∏ i ∈ σ.support, forwardSpouseWeight d i := by
  calc
    _ ≤ ∏ i ∈ σ.support, C * forwardSpouseWeight d (σ i) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ ENNReal.toReal_nonneg)
        (fun i hi ↦ harc i (σ i) (Equiv.Perm.mem_support.mp hi).symm)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      congr 1
      exact Finset.prod_equiv σ (fun i ↦ Equiv.Perm.apply_mem_support.symm) (fun _ _ ↦ rfl)

open scoped Classical in
/-- For any event of the actual successor graph, the normalized score-row
law gives the finite product of its exact row outcome weights. -/
theorem measureReal_pi_forwardOutcome_eq_sum {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) (E : Set (Fin n → Option (Fin n))) :
    (Measure.pi (normalizedStableScoreRowLaw d)).real
      ((fun r i ↦ forwardSuccessorOutcome d i (r i)) ⁻¹' E) =
        ∑ f : Fin n → Option (Fin n), if f ∈ E then ∏ i, forwardOutcomeWeight d i (f i) else 0 := by
  have (i : Fin n) := forwardSuccessorOutcomeLaw_isProbabilityMeasure d i (hx i) hy
  have hmeas : Measurable fun r : OffDiagonalScoreRows n ↦
      fun i ↦ forwardSuccessorOutcome d i (r i) :=
    measurable_pi_iff.mpr fun i ↦
      (measurable_forwardSuccessorOutcome d i).comp (measurable_pi_apply i)
  have hE : MeasurableSet E := E.to_countable.measurableSet
  unfold Measure.real
  rw [← Measure.map_apply hmeas hE, map_forwardSuccessorOutcome_pi d hx hy]
  exact measureReal_pi_eq_sum_event (forwardSuccessorOutcomeLaw d) E

open scoped Classical in
/-- Given the diagonal of a stable mark, the probability of a prescribed
sole forward cycle is at most its arc product times the complement forest bound. -/
theorem measureReal_pi_soleForwardCycle_le {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n) (σ : Matching n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1)
    (hY : 0 < ∑ i, (diagonalPairAt d i).2) {b : ℝ}
    (hdef : HasForwardReferenceDeficit d b) :
    (Measure.pi (normalizedStableScoreRowLaw d)).real
      {r | IsSoleDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ} ≤
      (∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
        (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
          ∑ i ∈ σ.support, forwardSpouseWeight d i)) := by
  let w := forwardOutcomeWeight d
  let p := forwardSpouseWeight d
  have (i : Fin n) := forwardSuccessorOutcomeLaw_isProbabilityMeasure d i (hx i) hy
  have hw (i : Fin n) (o : Option (Fin n)) : 0 ≤ w i o := ENNReal.toReal_nonneg
  have hw₁ (i : Fin n) : ∑ o, w i o = 1 := sum_measureReal_singletons_eq_one _
  have hp (i : Fin n) : 0 ≤ p i := div_nonneg (hy i).1 hY.le
  have ht : ∑ i, p i = 1 := by
    unfold p forwardSpouseWeight
    rw [← Finset.sum_div, div_self hY.ne']
  obtain ⟨δ, hd, hbudget, harc⟩ := hdef
  have harc' (i j : Fin n) (hij : i ≠ j) : (1 - δ i) * p j ≤ w i (some j) := by
    have := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
    rw [show w i (some j) = _ from forwardOutcomeWeight_some d i ⟨j, hij⟩]
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (harc i ⟨j, hij⟩)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (sub_nonneg.mpr (hd i).2) (hp j))] at h
  change (Measure.pi (normalizedStableScoreRowLaw d)).real
    ((fun r i ↦ forwardSuccessorOutcome d i (r i)) ⁻¹' {f | IsSoleDirectedCycle f σ}) ≤ _
  rw [measureReal_pi_forwardOutcome_eq_sum d hx hy]
  have heq : (∑ f : Fin n → Option (Fin n), if f ∈ {f | IsSoleDirectedCycle f σ} then
      ∏ i, w i (f i) else 0) = soleDirectedCycleProductMass w σ := by
    unfold soleDirectedCycleProductMass
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : IsSoleDirectedCycle f σ <;> simp [hf]
  change (∑ f : Fin n → Option (Fin n), if f ∈ {f | IsSoleDirectedCycle f σ} then
    ∏ i, w i (f i) else 0) ≤ _
  rw [heq]
  refine (soleDirectedCycleProductMass_le_arc_prod_mul_forestProductMass w hw σ).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ ↦ hw i _)
  refine (forestProductMass_eraseSuccessorWeights_le σ.support w hw hw₁ hp ht hd harc').trans ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hbudget le_rfl) le_rfl) (Real.exp_pos _).le

/-- The fixed permutation is the unique forward rotation exposed at the matching. -/
def IsSoleForwardExposedRotation {n : ℕ} (p : Profile n) (μ σ : Matching n) : Prop :=
  IsExposedRotation p μ σ ∧ ∀ τ, IsExposedRotation p μ τ → τ = σ

/-- The sole-exposure event on the rows of a fixed marked diagonal. -/
def soleForwardExposedRowEvent {n : ℕ} (μ σ : Matching n)
    (d : DiagonalScorePairs n) : Set (OffDiagonalScoreRows n) :=
  {r | IsSoleForwardExposedRotation
    (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ σ}

/-- The directed cycles of the actual score outcome are exactly the exposed rotations. -/
theorem realizesDirectedCycle_forwardOutcome_iff {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n) (σ : Matching n)
    (hs : IsScoreStable ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) row)) :
    RealizesDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ ↔
      IsExposedRotation
        (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r))) μ σ := by
  refine ⟨fun h ↦ ⟨h.1, ?_⟩, fun h ↦ ⟨h.isCycle, ?_⟩⟩
  · intro i hi
    exact (forwardSuccessorOutcome_eq_some_iff_isSuccessor μ d r i ⟨σ i, hi.symm⟩ hs ht).mp
      (h.2 i (Equiv.Perm.mem_support.mpr hi))
  · intro i hi
    have hne := Equiv.Perm.mem_support.mp hi
    exact (forwardSuccessorOutcome_eq_some_iff_isSuccessor μ d r i ⟨σ i, hne.symm⟩ hs ht).mpr
      (h.successor i hne)

/-- At almost every valid diagonal, the sole-cycle bound holds for actual
rank-exposed rotations of the reconstructed profiles. -/
theorem ae_diagonal_measureReal_soleForwardExposed_le {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      0 < (∑ i, (diagonalPairAt d i).2) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b → ∀ σ : Matching n,
        (Measure.pi (normalizedStableScoreRowLaw d)).real (soleForwardExposedRowEvent μ σ d) ≤
          (∏ i ∈ σ.support, forwardOutcomeWeight d i (some (σ i))) *
            (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
              ∑ i ∈ σ.support, forwardSpouseWeight d i)) := by
  filter_upwards [ae_diagonal_ae_normalizedStableRows μ] with d hd
  intro hx hy hY b hdef σ
  have heq : soleForwardExposedRowEvent μ σ d
      =ᵐ[Measure.pi (normalizedStableScoreRowLaw d)]
      {r | IsSoleDirectedCycle (fun i ↦ forwardSuccessorOutcome d i (r i)) σ} := by
    filter_upwards [hd hx hy] with r hr
    have hbridge (τ : Matching n) := realizesDirectedCycle_forwardOutcome_iff μ d r τ hr.2 hr.1
    apply propext
    exact ⟨fun h ↦ ⟨(hbridge σ).mpr h.1, fun τ hτ ↦ h.2 τ ((hbridge τ).mp hτ)⟩,
      fun h ↦ ⟨(hbridge σ).mp h.1, fun τ hτ ↦ h.2 τ ((hbridge τ).mpr hτ)⟩⟩
  have hm := measure_congr heq
  unfold Measure.real
  rw [hm]
  exact measureReal_pi_soleForwardCycle_le d σ hx hy hY hdef

/-- The fixed sole-exposure bound in the form used to sum over cycle lengths. -/
theorem ae_diagonal_measureReal_soleForwardExposed_le_of_goodDiagonalScores {n : ℕ}
    [MeasurableSpace (Option (Fin n))] [MeasurableSingletonClass (Option (Fin n))]
    (μ : Matching n) (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      d ∈ goodDiagonalScores n →
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ (b : ℝ), HasForwardReferenceDeficit d b → ∀ σ : Matching n,
        (Measure.pi (normalizedStableScoreRowLaw d)).real (soleForwardExposedRowEvent μ σ d) ≤
          ((1 + coexposureSuccessorPerturbation n) ^ σ.support.card *
            ∏ i ∈ σ.support, forwardSpouseWeight d i) *
            (Real.exp 1 * (b + (∑ i, (forwardSpouseWeight d i) ^ 2) +
              ∑ i ∈ σ.support, forwardSpouseWeight d i)) := by
  filter_upwards [ae_diagonal_measureReal_soleForwardExposed_le μ] with d hd
  intro hg hx hy b hb σ
  have hY : 0 < ∑ i, (diagonalPairAt d i).2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hg.1
  have hp (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY.le
  have hb₀ : 0 ≤ b := by
    obtain ⟨δ, hδ, hsum, _⟩ := hb
    exact (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (hδ i).1).trans hsum
  refine (hd hx hy hY b hb σ).trans ?_
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (Real.exp_pos _).le (add_nonneg
      (add_nonneg hb₀ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (Finset.sum_nonneg fun i _ ↦ hp i)))
  exact prod_forwardOutcomeWeight_le_of_arc_le σ fun i j hij ↦
    forwardOutcomeWeight_some_le_of_goodDiagonalScores hg hx hy hA hB hδ i ⟨j, hij⟩

end LennonPittelFormalization

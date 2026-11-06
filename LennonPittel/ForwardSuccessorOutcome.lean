module

public import LennonPittel.FiniteProductDensity
public import LennonPittel.ForwardSuccessorRowLaw

/-!
# Finite outcomes of forward successor rows

A normalized stable score row determines one off-diagonal arc or no arc.
The finite outcome law retains the exact score-event probabilities, and
mapping all rows gives the product of those finite laws.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private def uniqueScoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (j : {j : Fin n // i ≠ j}) : Set ({j : Fin n // i ≠ j} → ℝ × ℝ) :=
  scoreRowSuccessorEvent d i j ∩ ⋂ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
    (scoreRowSuccessorEvent d i k.val)ᶜ

private theorem measurableSet_uniqueScoreRowSuccessorEvent {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    MeasurableSet (uniqueScoreRowSuccessorEvent d i j) :=
  (measurableSet_scoreRowSuccessorEvent d i j).inter
    (MeasurableSet.iInter fun k ↦ (measurableSet_scoreRowSuccessorEvent d i k.val).compl)

private theorem uniqueScoreRowSuccessorEvent_of_unique {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ} {j : {j : Fin n // i ≠ j}}
    (hj : r ∈ scoreRowSuccessorEvent d i j)
    (huniq : ∀ k, r ∈ scoreRowSuccessorEvent d i k → k = j) :
    r ∈ uniqueScoreRowSuccessorEvent d i j :=
  ⟨hj, Set.mem_iInter.mpr fun k hk ↦ k.property (huniq k.val hk)⟩

private theorem uniqueScoreRowSuccessorEvent_unique {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ} {j k : {j : Fin n // i ≠ j}}
    (hj : r ∈ uniqueScoreRowSuccessorEvent d i j)
    (hk : r ∈ scoreRowSuccessorEvent d i k) : k = j := by
  by_contra hne
  exact (Set.mem_iInter.mp hj.2 ⟨k, hne⟩) hk

/-- The uniquely determined successor label, or no arc if no label is unique. -/
@[no_expose]
noncomputable def forwardSuccessorOutcome {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {j : Fin n // i ≠ j} → ℝ × ℝ) : Option (Fin n) := by
  classical
  exact if h : ∃ j, r ∈ uniqueScoreRowSuccessorEvent d i j then some h.choose.val else none

private theorem forwardSuccessorOutcome_eq_some_iff_unique {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (r : {j : Fin n // i ≠ j} → ℝ × ℝ) (j : {j : Fin n // i ≠ j}) :
    forwardSuccessorOutcome d i r = some j.val ↔ r ∈ uniqueScoreRowSuccessorEvent d i j := by
  classical
  unfold forwardSuccessorOutcome
  split
  · rename_i h
    constructor
    · intro he
      have hej : h.choose = j := Subtype.ext (Option.some.inj he)
      simpa only [hej] using h.choose_spec
    · intro hj
      rw [uniqueScoreRowSuccessorEvent_unique hj h.choose_spec.1]
  · rename_i h
    constructor
    · intro he
      cases he
    · exact fun hj ↦ (h ⟨j, hj⟩).elim

/-- No forward row selects its own label. -/
theorem forwardSuccessorOutcome_ne_some_self {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n)
    (r : {j : Fin n // i ≠ j} → ℝ × ℝ) : forwardSuccessorOutcome d i r ≠ some i := by
  classical
  unfold forwardSuccessorOutcome
  split
  · rename_i h
    exact fun he ↦ h.choose.property (Option.some.inj he).symm
  · intro he
    cases he

/-- The finite successor outcome is measurable. -/
theorem measurable_forwardSuccessorOutcome {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) : Measurable (forwardSuccessorOutcome d i) := by
  apply measurable_to_countable'
  intro o
  cases o with
  | none =>
    have hset : forwardSuccessorOutcome d i ⁻¹' {none} =
        (⋃ j, uniqueScoreRowSuccessorEvent d i j)ᶜ := by
      classical
      ext r
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion]
      unfold forwardSuccessorOutcome
      split <;> simp_all
    rw [hset]
    exact (MeasurableSet.iUnion (measurableSet_uniqueScoreRowSuccessorEvent d i)).compl
  | some j =>
    by_cases hj : i = j
    · subst j
      have hset : forwardSuccessorOutcome d i ⁻¹' {some i} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun r ↦ forwardSuccessorOutcome_ne_some_self d i r
      rw [hset]
      exact MeasurableSet.empty
    · have hset : forwardSuccessorOutcome d i ⁻¹' {some j} =
          uniqueScoreRowSuccessorEvent d i ⟨j, hj⟩ :=
        Set.ext fun r ↦ forwardSuccessorOutcome_eq_some_iff_unique d i r ⟨j, hj⟩
      rw [hset]
      exact measurableSet_uniqueScoreRowSuccessorEvent d i ⟨j, hj⟩

private theorem scoreRowSuccessorEvent_unique_of_injective {n : ℕ} {d : DiagonalScorePairs n}
    {i : Fin n} {r : {j : Fin n // i ≠ j} → ℝ × ℝ}
    (hinj : Function.Injective (fun k ↦ (r k).1))
    {j k : {j : Fin n // i ≠ j}} (hj : r ∈ scoreRowSuccessorEvent d i j)
    (hk : r ∈ scoreRowSuccessorEvent d i k) : k = j := by
  by_contra hne
  have hle : (r j).1 ≤ (r k).1 :=
    le_of_not_gt fun h ↦ hj.2.2 ⟨k, hne⟩ ⟨h, hk.2.1⟩
  have hge : (r k).1 ≤ (r j).1 :=
    le_of_not_gt fun h ↦ hk.2.2 ⟨j, fun e ↦ hne e.symm⟩ ⟨h, hj.2.1⟩
  exact hne (hinj (le_antisymm hge hle))

/-- If the man's scores do not tie, the finite outcome is exactly the successor event. -/
theorem forwardSuccessorOutcome_eq_some_iff {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (r : {j : Fin n // i ≠ j} → ℝ × ℝ) (j : {j : Fin n // i ≠ j})
    (hinj : Function.Injective (fun k ↦ (r k).1)) :
    forwardSuccessorOutcome d i r = some j.val ↔ r ∈ scoreRowSuccessorEvent d i j :=
  (forwardSuccessorOutcome_eq_some_iff_unique d i r j).trans
    ⟨fun h ↦ h.1, fun hj ↦ uniqueScoreRowSuccessorEvent_of_unique hj fun _ hk ↦
      scoreRowSuccessorEvent_unique_of_injective hinj hj hk⟩

/-- On stable tie-free reconstructed arrays, the outcome selects exactly the rank arc. -/
theorem forwardSuccessorOutcome_eq_some_iff_isSuccessor {n : ℕ} (μ : Matching n)
    (d : DiagonalScorePairs n) (r : OffDiagonalScoreRows n)
    (i : Fin n) (j : {j : Fin n // i ≠ j})
    (hs : IsScoreStable ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)) μ)
    (ht : ∀ row, Function.Injective
      ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r) row)) :
    forwardSuccessorOutcome d i (r i) = some j.val ↔
      IsSuccessor
        (profileOfScores ((splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)))
        μ i (μ j.val) := by
  have hiff (k : {k : Fin n // i ≠ k}) :=
    scoreRowSuccessorEvent_iff_isSuccessor_reconstructed μ d r i k hs ht
  apply (forwardSuccessorOutcome_eq_some_iff_unique d i (r i) j).trans
  exact ⟨fun hj ↦ (hiff j).mp hj.1, fun hj ↦
    uniqueScoreRowSuccessorEvent_of_unique ((hiff j).mpr hj) fun k hk ↦
      Subtype.ext (μ.injective (((hiff k).mp hk).unique hj))⟩

private theorem ae_injective_unitScoreLaw_pi (ι : Type*) [Fintype ι] :
    ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ unitScoreLaw), Function.Injective (x : ι → ℝ) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hpres := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ unitScoreLaw) e
  filter_upwards [hpres.quasiMeasurePreserving.ae
    (ae_injective_iid unitScoreLaw (Fintype.card ι))] with x hx
  intro i j hij
  apply e.injective
  apply hx
  simpa only [MeasurableEquiv.piCongrLeft_apply_apply] using hij

/-- In a normalized stable row the man's off-diagonal scores are almost surely distinct. -/
theorem ae_injective_fst_normalizedStableScoreRowLaw {n : ℕ}
    (d : DiagonalScorePairs n) (i : Fin n) :
    ∀ᵐ r ∂normalizedStableScoreRowLaw d i,
      Function.Injective (fun k ↦ (r k).1) := by
  let ι := {j : Fin n // i ≠ j}
  let ν := Measure.pi fun _ : ι ↦ unitScorePairLaw
  have hm : Measure.map Prod.fst unitScorePairLaw = unitScoreLaw := by
    simp [unitScorePairLaw]
  have hmap : ν.map (fun (r : ι → ℝ × ℝ) k ↦ (r k).1) =
      Measure.pi fun _ : ι ↦ unitScoreLaw := by
    unfold ν
    rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
    simp only [hm]
  have hpres : MeasurePreserving (fun (r : ι → ℝ × ℝ) k ↦ (r k).1) ν
      (Measure.pi fun _ : ι ↦ unitScoreLaw) :=
    ⟨Measurable.of_eval fun k ↦ measurable_fst.comp (measurable_pi_apply k), hmap⟩
  have hν : ∀ᵐ r ∂ν, Function.Injective (fun k ↦ (r k).1) :=
    hpres.quasiMeasurePreserving.ae (ae_injective_unitScoreLaw_pi ι)
  have hsub : stableScoreRowLaw d i ≤ ν := by
    rw [stableScoreRowLaw, ← Measure.restrict_pi_pi]
    exact Measure.restrict_le_self
  exact (Measure.smul_absolutelyContinuous.trans
    (Measure.absolutelyContinuous_of_le hsub)).ae_le hν

/-- The finite successor distribution of a normalized stable score row. -/
noncomputable def forwardSuccessorOutcomeLaw {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) : Measure (Option (Fin n)) :=
  Measure.map (forwardSuccessorOutcome d i) (normalizedStableScoreRowLaw d i)

/-- Each finite row law is a probability law for valid diagonal scores. -/
theorem forwardSuccessorOutcomeLaw_isProbabilityMeasure {n : ℕ}
    [MeasurableSpace (Option (Fin n))] (d : DiagonalScorePairs n) (i : Fin n)
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1) (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1) :
    IsProbabilityMeasure (forwardSuccessorOutcomeLaw d i) := by
  have := normalizedStableScoreRowLaw_isProbabilityMeasure d i hx hy
  unfold forwardSuccessorOutcomeLaw
  infer_instance

/-- The finite arc mass agrees with the normalized row event at every off-diagonal label. -/
theorem forwardSuccessorOutcomeLaw_some {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))]
    (d : DiagonalScorePairs n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    forwardSuccessorOutcomeLaw d i {some j.val} =
      normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) := by
  rw [forwardSuccessorOutcomeLaw, Measure.map_apply (measurable_forwardSuccessorOutcome d i)
    (measurableSet_singleton _)]
  apply measure_congr
  filter_upwards [ae_injective_fst_normalizedStableScoreRowLaw d i] with r hr
  exact propext (forwardSuccessorOutcome_eq_some_iff d i r j hr)

/-- The finite outcome law gives mass zero to a self-arc. -/
theorem forwardSuccessorOutcomeLaw_self {n : ℕ} [MeasurableSpace (Option (Fin n))]
    [MeasurableSingletonClass (Option (Fin n))] (d : DiagonalScorePairs n) (i : Fin n) :
    forwardSuccessorOutcomeLaw d i {some i} = 0 := by
  rw [forwardSuccessorOutcomeLaw, Measure.map_apply (measurable_forwardSuccessorOutcome d i)
    (measurableSet_singleton _)]
  rw [show forwardSuccessorOutcome d i ⁻¹' {some i} = ∅ from
    eq_empty_iff_forall_notMem.mpr fun r ↦ forwardSuccessorOutcome_ne_some_self d i r]
  exact measure_empty

/-- Independent normalized score rows push forward to independent finite successor rows. -/
theorem map_forwardSuccessorOutcome_pi {n : ℕ} [MeasurableSpace (Option (Fin n))]
    (d : DiagonalScorePairs n) (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    (Measure.pi (normalizedStableScoreRowLaw d)).map
      (fun r i ↦ forwardSuccessorOutcome d i (r i)) =
      Measure.pi (forwardSuccessorOutcomeLaw d) := by
  have (i : Fin n) := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  exact Measure.pi_map_pi fun i ↦ (measurable_forwardSuccessorOutcome d i).aemeasurable

/-- The product of unnormalized rows differs from its probability law by the
mass of the stable off-diagonal score section. -/
theorem pi_stableScoreRowLaw_eq_smul_normalized {n : ℕ} (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    Measure.pi (stableScoreRowLaw d) =
      (offDiagonalScoreLaw n (offDiagonalNonblocking d)) •
        Measure.pi (normalizedStableScoreRowLaw d) := by
  have (i : Fin n) := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  rw [← prod_stableScoreRowLaw_univ]
  calc
    _ = Measure.pi (fun i ↦ stableScoreRowLaw d i univ • normalizedStableScoreRowLaw d i) :=
      congrArg Measure.pi (funext fun i ↦ stableScoreRowLaw_eq_smul_normalized d i (hx i) hy)
    _ = _ := pi_smul_coordinates (normalizedStableScoreRowLaw d)
      (fun i ↦ stableScoreRowLaw d i univ) fun i ↦ measure_ne_top _ _

/-- The stable off-diagonal section has positive mass at valid diagonal scores. -/
theorem offDiagonalScoreLaw_nonblocking_ne_zero_of_valid {n : ℕ} (d : DiagonalScorePairs n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) :
    offDiagonalScoreLaw n (offDiagonalNonblocking d) ≠ 0 := by
  rw [← prod_stableScoreRowLaw_univ]
  refine Finset.prod_ne_zero_iff.mpr fun i _ h ↦ ?_
  have := normalizedStableScoreRowLaw_isProbabilityMeasure d i (hx i) hy
  have h1 : normalizedStableScoreRowLaw d i univ = 1 := measure_univ
  rw [normalizedStableScoreRowLaw, Measure.smul_apply, smul_eq_mul, h, mul_zero] at h1
  exact zero_ne_one h1

/-- For almost every fixed valid diagonal, the normalized product reconstructs
tie-free stable score arrays almost surely. -/
theorem ae_diagonal_ae_normalizedStableRows {n : ℕ} (μ : Matching n) :
    ∀ᵐ d ∂diagonalScoreLaw n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      ∀ᵐ r ∂Measure.pi (normalizedStableScoreRowLaw d),
        let x := (splitScorePairs μ).symm (d, (offDiagonalRowsEquiv n).symm r)
        (∀ row, Function.Injective (x row)) ∧ IsScoreStable x μ := by
  filter_upwards [ae_diagonal_ae_stableRows μ] with d hd
  intro hx hy
  rw [pi_stableScoreRowLaw_eq_smul_normalized d hx hy,
    Measure.ae_ennreal_smul_measure_iff
      (offDiagonalScoreLaw_nonblocking_ne_zero_of_valid d hx hy)] at hd
  exact hd

end LennonPittelFormalization

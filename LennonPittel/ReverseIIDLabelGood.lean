module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Independent label sampling for cycle collections

A candidate collection is sampled by putting independent labels at the
positions of a fixed-point-free permutation. We bound the weight of distinct
labelings that avoid the pivot and prescribe only available arcs. The arc
bound needs only that its two positions are different, not that all arcs
are independent.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

section Measures

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

private theorem iid_two_marginal (μ : Measure α) [IsProbabilityMeasure μ]
    {i j : ι} (hij : i ≠ j) {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.pi (fun _ : ι ↦ μ)) {x | x i ∈ A ∧ x j ∈ B} = μ A * μ B := by
  have h : iIndepFun (fun i (x : ι → α) ↦ x i) (Measure.pi (fun _ : ι ↦ μ)) :=
    iIndepFun_pi (X := fun _ : ι ↦ id) (fun _ ↦ measurable_id.aemeasurable)
  have hp := (h.indepFun hij).measure_inter_preimage_eq_mul A B hA hB
  exact hp.trans (congrArg₂ (· * ·)
    ((measurePreserving_eval (fun _ : ι ↦ μ) i).measure_preimage hA.nullMeasurableSet)
    ((measurePreserving_eval (fun _ : ι ↦ μ) j).measure_preimage hB.nullMeasurableSet))

variable [Fintype α] [DiscreteMeasurableSpace α]

/-- The probability of a forbidden arc is bounded by the average forbidden target mass. -/
theorem iid_forbiddenArc_measure_le (μ : Measure α) [IsProbabilityMeasure μ]
    {i j : ι} (hij : i ≠ j) (F : α → Set α) :
    (Measure.pi (fun _ : ι ↦ μ)) {x | x j ∈ F (x i)} ≤
      ∑ a, μ {a} * μ (F a) := by
  have he : {x : ι → α | x j ∈ F (x i)} =
      ⋃ a : α, {x : ι → α | x i = a ∧ x j ∈ F a} := by
    ext x
    simp
  rw [he]
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  exact (iid_two_marginal μ hij (A := {a}) MeasurableSet.of_discrete
    (B := F a) MeasurableSet.of_discrete).le

/-- The chance of a collision is at most one collision probability per unordered position pair. -/
theorem iid_labelCollision_measure_le (μ : Measure α) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι ↦ μ)) {x | ¬ Function.Injective x} ≤
      ((Fintype.card ι).choose 2 : ℝ≥0∞) * ∑ a, (μ {a}) ^ 2 := by
  classical
  let pairs := (Finset.univ : Finset ι).powersetCard 2
  let C (s : ↥pairs) : Set (ι → α) := {x | ¬ Set.InjOn x (s.val : Set ι)}
  have hsub : {x | ¬ Function.Injective x} ⊆ ⋃ s, C s := by
    intro x hx
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hx
    have hm : {i, j} ∈ pairs :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hij⟩
    refine Set.mem_iUnion.mpr ⟨⟨{i, j}, hm⟩, ?_⟩
    change ¬ Set.InjOn x (↑({i, j} : Finset ι))
    rw [Finset.coe_pair, Set.injOn_pair]
    exact fun h ↦ hij (h heq)
  calc
    _ ≤ ∑ s, (Measure.pi (fun _ : ι ↦ μ)) (C s) :=
      (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _ : ↥pairs, ∑ a, (μ {a}) ^ 2 := by
      refine Finset.sum_le_sum fun s _ ↦ ?_
      obtain ⟨i, j, hij, hs⟩ :=
        Finset.card_eq_two.mp (Finset.mem_powersetCard.mp s.property).2
      have he : C s = {x : ι → α | x j ∈ ({x i} : Set α)} := by
        ext x
        simp [C, hs, hij, eq_comm]
      rw [he]
      simpa only [pow_two] using iid_forbiddenArc_measure_le μ hij (fun a ↦ {a})
    _ = _ := by simp [pairs, Finset.card_powersetCard, nsmul_eq_mul]

/-- A labeling is good if labels are distinct, avoid the pivot, and use no forbidden arcs. -/
def iidLabelGood (A : Set α) (F : α → Set α) (e : ι → ι) : Set (ι → α) :=
  {x | Function.Injective x ∧ (∀ i, x i ∉ A) ∧ ∀ i, x (e i) ∉ F (x i)}

/-- For independent labels, the losses from collisions, the pivot, and forbidden arcs add. -/
theorem iidLabelGood_measure_lower (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (F : α → Set α) (e : ι → ι) (he : ∀ i, e i ≠ i)
    (η : ℝ≥0∞) (hη : ∀ a, μ (F a) ≤ η) :
    1 - (((Fintype.card ι).choose 2 : ℝ≥0∞) * (∑ a, (μ {a}) ^ 2) +
        (Fintype.card ι : ℝ≥0∞) * μ A + (Fintype.card ι : ℝ≥0∞) * η) ≤
      (Measure.pi (fun _ : ι ↦ μ)) (iidLabelGood A F e) := by
  classical
  let ν := Measure.pi (fun _ : ι ↦ μ)
  let C : Set (ι → α) := {x | ¬ Function.Injective x}
  let P : Set (ι → α) := ⋃ i, {x | x i ∈ A}
  let M : Set (ι → α) := ⋃ i, {x | x (e i) ∈ F (x i)}
  have hbad : (iidLabelGood A F e)ᶜ = C ∪ P ∪ M := by
    ext x
    simp only [iidLabelGood, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, C, P, M,
      Set.mem_iUnion, not_and_or, not_forall, not_not, or_assoc]
  have hP : ν P ≤ (Fintype.card ι : ℝ≥0∞) * μ A := by
    calc
      _ ≤ ∑ i : ι, ν {x | x i ∈ A} := measure_iUnion_fintype_le _ _
      _ = ∑ _ : ι, μ A := Finset.sum_congr rfl fun i _ ↦
        (measurePreserving_eval (fun _ : ι ↦ μ) i).measure_preimage
          MeasurableSet.of_discrete.nullMeasurableSet
      _ = _ := by simp [nsmul_eq_mul]
  have hM : ν M ≤ (Fintype.card ι : ℝ≥0∞) * η := by
    calc
      _ ≤ ∑ i : ι, ν {x | x (e i) ∈ F (x i)} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _ : ι, η := by
        refine Finset.sum_le_sum fun i _ ↦
          (iid_forbiddenArc_measure_le μ (he i).symm F).trans ?_
        calc
          _ ≤ ∑ a, μ {a} * η := Finset.sum_le_sum fun a _ ↦ mul_le_mul_right (hη a) _
          _ = _ := by rw [← Finset.sum_mul]; simp
      _ = _ := by simp [nsmul_eq_mul]
  have hcomp : ν (iidLabelGood A F e) = 1 - ν (iidLabelGood A F e)ᶜ := by
    rw [← (measure_univ : ν univ = 1), ← measure_compl
      MeasurableSet.of_discrete (measure_ne_top ν _), compl_compl]
  rw [← show ν (iidLabelGood A F e) = _ from rfl, hcomp, hbad]
  apply tsub_le_tsub_left
  exact (measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add (iid_labelCollision_measure_le μ) hP)) hM)

omit [Fintype α] in
private theorem iidLabelFinset_measure_eq_sum (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Finset (ι → α)) :
    (Measure.pi (fun _ : ι ↦ μ)) (S : Set (ι → α)) = ∑ x ∈ S, ∏ i, μ {x i} := by
  rw [← sum_measure_singleton]
  simp only [Measure.pi_singleton]

end Measures

open scoped Classical in
/-- The good-label lower bound as a finite sum of products of label weights. -/
theorem iidLabelGood_sum_weights_lower {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → ℝ≥0∞) (hr : ∑ a, r a = 1) (A : Finset α) (F : α → Finset α)
    (e : ι → ι) (he : ∀ i, e i ≠ i) (η : ℝ≥0∞)
    (hη : ∀ a, ∑ b ∈ F a, r b ≤ η) :
    1 - (((Fintype.card ι).choose 2 : ℝ≥0∞) * (∑ a, (r a) ^ 2) +
        (Fintype.card ι : ℝ≥0∞) * (∑ a ∈ A, r a) + (Fintype.card ι : ℝ≥0∞) * η) ≤
      ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e),
        ∏ i, r (x i) := by
  classical
  let : MeasurableSpace α := ⊤
  let : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  let μ := (PMF.ofFintype r hr).toMeasure
  let G := iidLabelGood (A : Set α) (fun a ↦ ↑(F a)) e
  let S := Finset.univ.filter (fun x ↦ x ∈ G)
  have hS : (S : Set (ι → α)) = G := by simp [S]
  have hmass (s : Finset α) : μ (s : Set α) = ∑ a ∈ s, r a :=
    (PMF.ofFintype r hr).toMeasure_apply_finset s
  have hatom (a : α) : μ {a} = r a :=
    (PMF.ofFintype r hr).toMeasure_apply_singleton a MeasurableSet.of_discrete
  have hg := iidLabelGood_measure_lower μ (A : Set α) (fun a ↦ ↑(F a)) e he η
    (fun a ↦ (hmass (F a)).symm ▸ hη a)
  change _ ≤ (Measure.pi (fun _ : ι ↦ μ)) G at hg
  rw [← hS, iidLabelFinset_measure_eq_sum μ S, hmass A] at hg
  simpa only [hatom] using hg

end LennonPittelFormalization

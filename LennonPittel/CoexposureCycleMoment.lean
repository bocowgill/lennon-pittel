module

public import LennonPittel.CoexposedRotationMultiplicity
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Successor permutations and the co-exposure moment

A union of exposed cycles is encoded by a permutation whose nontrivial arrows
are all realized successors. This gives a finite moment bound from the joint
arc bounds; it does not assume any independence of scores or of stable matchings.
-/

@[expose] public section

open StableMarriage MeasureTheory
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- On every moved point, the permutation follows the successor at the matching. -/
def RealizesSuccessorPermutation {n : ℕ} (p : Profile n) (M σ : Matching n) : Prop :=
  ∀ i ∈ σ.support, IsSuccessor p M i (M (σ i))

/-- The empty cycle subset gives the identity permutation. -/
theorem realizesSuccessorPermutation_one {n : ℕ} (p : Profile n) (M : Matching n) :
    RealizesSuccessorPermutation p M 1 := by
  intro i hi
  simp at hi

/-- Without any successor arrows, only the identity permutation is realized. -/
theorem realizesSuccessorPermutation_iff_eq_one_of_no_successors {n : ℕ}
    {p : Profile n} {M σ : Matching n} (h : ∀ i j, ¬ IsSuccessor p M i (M j)) :
    RealizesSuccessorPermutation p M σ ↔ σ = 1 := by
  constructor
  · intro hσ
    apply Equiv.ext
    intro i
    change σ i = i
    by_contra hi
    exact h i (σ i) (hσ i (Equiv.Perm.mem_support.mpr hi))
  · rintro rfl
    exact realizesSuccessorPermutation_one p M

/-- A realized permutation is exactly a union of exposed successor cycles. -/
theorem realizesSuccessorPermutation_iff_factors {n : ℕ}
    {p : Profile n} {M σ : Matching n} :
    RealizesSuccessorPermutation p M σ ↔
      ∀ ρ ∈ σ.cycleFactorsFinset, IsExposedRotation p M ρ := by
  constructor
  · intro h ρ hρ
    obtain ⟨hc, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ
    refine ⟨hc, fun i hi ↦ ?_⟩
    have hmem := Equiv.Perm.mem_support.mpr hi
    rw [heq i hmem]
    exact h i (Equiv.Perm.mem_cycleFactorsFinset_support_le hρ hmem)
  · intro h i hi
    obtain ⟨ρ, hρ, hmem⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hi
    rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hρ).2 i hmem]
    exact (h ρ hρ).successor i (Equiv.Perm.mem_support.mp hmem)

/-- For a collection of disjoint cycles, the total cycle length is the
size of the support of its encoding permutation. -/
theorem card_support_eq_sum_cycleFactors_support {n : ℕ} (σ : Matching n) :
    σ.support.card = ∑ ρ ∈ σ.cycleFactorsFinset, ρ.support.card := by
  have hs : σ.cycleFactorsFinset.biUnion (fun ρ ↦ ρ.support) = σ.support := by
    ext i
    rw [Finset.mem_biUnion]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.symm
  refine (congrArg Finset.card hs.symm).trans (Finset.card_biUnion ?_)
  intro ρ hρ τ hτ hne
  exact Equiv.Perm.disjoint_iff_disjoint_support.mp
    (σ.cycleFactorsFinset_pairwise_disjoint hρ hτ hne)

/-- A set of distinct exposed rotations is a set of disjoint nontrivial cycles. -/
private theorem exposedRotation_pairwise_disjoint {n : ℕ} {p : Profile n} {M : Matching n}
    {C : Finset (Matching n)} (hC : ∀ ρ ∈ C, IsExposedRotation p M ρ) :
    (C : Set (Matching n)).Pairwise Equiv.Perm.Disjoint := by
  intro ρ hρ σ hσ hne i
  by_cases hi : ρ i = i
  · exact Or.inl hi
  · exact Or.inr ((hC ρ hρ).disjoint_moved (hC σ hσ) hne i hi)

open scoped Classical in
/-- Sum any cycle-set weight over realized permutations by summing over the exposed subsets. -/
private theorem sum_realized_cycleFactors {n : ℕ} {A : Type*} [AddCommMonoid A]
    (p : Profile n) (M : Matching n) (f : Finset (Matching n) → A) :
    (∑ σ ∈ Finset.univ.filter (RealizesSuccessorPermutation p M), f σ.cycleFactorsFinset) =
      ∑ S ∈ (Finset.univ.filter (IsExposedRotation p M)).powerset, f S := by
  let C := Finset.univ.filter (IsExposedRotation p M)
  let P := Finset.univ.filter (RealizesSuccessorPermutation p M)
  have hC : ∀ ρ, ρ ∈ C ↔ IsExposedRotation p M ρ := by simp [C]
  have hP : ∀ σ, σ ∈ P ↔ RealizesSuccessorPermutation p M σ := by simp [P]
  refine Finset.sum_bij (fun σ _ ↦ σ.cycleFactorsFinset) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro σ hσ
    exact Finset.mem_powerset.mpr fun ρ hρ ↦
      (hC ρ).mpr (realizesSuccessorPermutation_iff_factors.mp ((hP σ).mp hσ) ρ hρ)
  · intro σ _ τ _ h
    exact Equiv.Perm.cycleFactorsFinset_injective h
  · intro S hS
    have hrot : ∀ ρ ∈ S, IsExposedRotation p M ρ :=
      fun ρ hρ ↦ (hC ρ).mp (Finset.mem_powerset.mp hS hρ)
    have hd := exposedRotation_pairwise_disjoint hrot
    let σ := S.noncommProd id (hd.mono' fun _ _ ↦ Equiv.Perm.Disjoint.commute)
    have heq : σ.cycleFactorsFinset = S :=
      Equiv.Perm.cycleFactorsFinset_eq_finset.mpr
        ⟨fun ρ hρ ↦ (hrot ρ hρ).isCycle, hd, rfl⟩
    refine ⟨σ, (hP σ).mpr (realizesSuccessorPermutation_iff_factors.mpr ?_), heq⟩
    simpa only [heq] using hrot

/-- Each subset of exposed rotations is encoded by exactly one successor permutation. -/
theorem card_realizesSuccessorPermutation {n : ℕ} (p : Profile n) (M : Matching n) :
    Nat.card {σ : Matching n // RealizesSuccessorPermutation p M σ} =
      2 ^ numExposedRotations p M := by
  classical
  let C := Finset.univ.filter (IsExposedRotation p M)
  let P := Finset.univ.filter (RealizesSuccessorPermutation p M)
  have hC : ∀ ρ, ρ ∈ C ↔ IsExposedRotation p M ρ := by simp [C]
  have hP : ∀ σ, σ ∈ P ↔ RealizesSuccessorPermutation p M σ := by simp [P]
  rw [numExposedRotations, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype P hP, Fintype.card_of_subtype C hC, ← Finset.card_powerset]
  simpa using (sum_realized_cycleFactors p M (fun _ ↦ (1 : ℕ)))

/-- Giving each selected cycle weight `b` makes the subset sum equal to
`(b + 1)` to the number of exposed rotations. -/
theorem sum_successorPermutation_cycleWeight_indicators {n : ℕ} {Ω : Type*}
    (P : Ω → Profile n) (M : Matching n) (x : Ω) (b : ℝ≥0∞) :
    (∑ σ : Matching n, ({y | RealizesSuccessorPermutation (P y) M σ} : Set Ω).indicator
      (fun _ ↦ b ^ σ.cycleFactorsFinset.card) x) = (b + 1) ^ numExposedRotations (P x) M := by
  classical
  let C := Finset.univ.filter (IsExposedRotation (P x) M)
  have hC : ∀ ρ, ρ ∈ C ↔ IsExposedRotation (P x) M ρ := by simp [C]
  have hcard : numExposedRotations (P x) M = C.card := by
    rw [numExposedRotations, Nat.card_eq_fintype_card, Fintype.card_of_subtype C hC]
  calc
    _ = ∑ σ ∈ Finset.univ.filter (RealizesSuccessorPermutation (P x) M),
        b ^ σ.cycleFactorsFinset.card := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_filter]
    _ = ∑ S ∈ C.powerset, b ^ S.card :=
      sum_realized_cycleFactors (P x) M (fun S ↦ b ^ S.card)
    _ = (b + 1) ^ C.card := by simpa only [Finset.prod_const] using
      (Finset.prod_add_one (f := fun _ ↦ b) C).symm
    _ = _ := by rw [hcard]

private theorem sum_successorPermutation_indicators {n : ℕ} {Ω : Type*}
    (P : Ω → Profile n) (M : Matching n) (x : Ω) :
    (∑ σ : Matching n, ({y | RealizesSuccessorPermutation (P y) M σ} : Set Ω).indicator
      (fun _ ↦ (1 : ℝ≥0∞)) x) = (2 : ℝ≥0∞) ^ numExposedRotations (P x) M := by
  simpa only [one_pow, one_add_one_eq_two] using
    sum_successorPermutation_cycleWeight_indicators P M x 1

/-- An upper bound on each realized permutation's mass gives a weighted cycle moment bound. -/
theorem lintegral_cycleWeight_numExposedRotations_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (b : ℝ≥0∞) (bound : Matching n → ℝ≥0∞)
    (harc : ∀ σ, ν {x | RealizesSuccessorPermutation (P x) M σ} ≤ bound σ) :
    (∫⁻ x, (b + 1) ^ numExposedRotations (P x) M ∂ν) ≤
      ∑ σ : Matching n, b ^ σ.cycleFactorsFinset.card * bound σ := by
  have hm (σ : Matching n) : MeasurableSet {x | RealizesSuccessorPermutation (P x) M σ} :=
    hP (MeasurableSet.of_discrete : MeasurableSet {p : Profile n |
      RealizesSuccessorPermutation p M σ})
  simp_rw [← sum_successorPermutation_cycleWeight_indicators P M _ b]
  rw [lintegral_finsetSum _ (fun σ _ ↦ measurable_const.indicator (hm σ))]
  exact Finset.sum_le_sum fun σ _ ↦
    (lintegral_indicator_const (hm σ) _).le.trans (mul_le_mul_right (harc σ) _)

/-- The product of target weights depends only on the permutation's support.
Grouping by that support leaves only a finite sum of the coefficients. -/
theorem sum_weighted_successorPermutation_product_by_support {n : ℕ}
    (f : Matching n → ℝ≥0∞) (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞) :
    (∑ σ : Matching n, f σ * ∏ i ∈ σ.support, a * w (σ i)) =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (∑ σ ∈ Finset.univ.filter (fun σ : Matching n ↦ σ.support = s), f σ) *
          (a ^ s.card * ∏ i ∈ s, w i) := by
  classical
  have hmem (σ : Matching n) (_ : σ ∈ (Finset.univ : Finset (Matching n))) :
      σ.support ∈ (Finset.univ : Finset (Fin n)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun σ ↦ f σ * ∏ i ∈ σ.support, a * w (σ i))]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [σ.prod_comp σ.support (fun j ↦ a * w j)
    (fun _ h ↦ Equiv.Perm.mem_support.mpr h), (Finset.mem_filter.mp hσ).2,
    Finset.prod_mul_distrib, Finset.prod_const]

private theorem card_permutations_support_eq_le_factorial {n : ℕ} (s : Finset (Fin n)) :
    ((Finset.univ : Finset (Matching n)).filter (fun σ ↦ σ.support = s)).card ≤
      s.card.factorial := by
  classical
  rw [← card_perms_of_finset s]
  apply Finset.card_le_card
  intro σ hσ
  rw [mem_perms_of_finset_iff]
  intro i hi
  rw [← (Finset.mem_filter.mp hσ).2]
  exact Equiv.Perm.mem_support.mpr hi

/-- The sum of target-weight products over permutations is bounded by sorting
permutations by their support and allowing all permutations of that support. -/
theorem sum_successorPermutation_product_le {n : ℕ} (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞) :
    (∑ σ : Matching n, ∏ i ∈ σ.support, a * w (σ i)) ≤
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (s.card.factorial : ℝ≥0∞) * a ^ s.card * ∏ j ∈ s, w j := by
  classical
  have hmem (σ : Matching n) (_ : σ ∈ (Finset.univ : Finset (Matching n))) :
      σ.support ∈ (Finset.univ : Finset (Fin n)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun σ ↦ ∏ i ∈ σ.support, a * w (σ i))]
  apply Finset.sum_le_sum
  intro s _
  let F := (Finset.univ : Finset (Matching n)).filter (fun σ ↦ σ.support = s)
  have hF : (F.card : ℝ≥0∞) ≤ s.card.factorial := by
    exact_mod_cast card_permutations_support_eq_le_factorial s
  calc
    _ = ∑ σ ∈ F, a ^ s.card * ∏ i ∈ s, w i := by
      refine Finset.sum_congr rfl fun σ hσ ↦ ?_
      rw [σ.prod_comp σ.support (fun j ↦ a * w j)
        (fun _ h ↦ Equiv.Perm.mem_support.mpr h), (Finset.mem_filter.mp hσ).2,
        Finset.prod_mul_distrib, Finset.prod_const]
    _ = (F.card : ℝ≥0∞) * (a ^ s.card * ∏ i ∈ s, w i) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_left hF _

/-- A joint arc bound with a common mass factor bounds the corresponding moment. -/
theorem lintegral_pow_numExposedRotations_le_mul {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (c a : ℝ≥0∞) (w : Fin n → ℝ≥0∞)
    (harc : ∀ σ : Matching n,
      ν {x | RealizesSuccessorPermutation (P x) M σ} ≤ c * ∏ i ∈ σ.support, a * w (σ i)) :
    (∫⁻ x, (2 : ℝ≥0∞) ^ numExposedRotations (P x) M ∂ν) ≤
      c * ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (s.card.factorial : ℝ≥0∞) * a ^ s.card * ∏ j ∈ s, w j := by
  have hm (σ : Matching n) : MeasurableSet {x | RealizesSuccessorPermutation (P x) M σ} :=
    hP (MeasurableSpace.measurableSet_top :
      MeasurableSet {p : Profile n | RealizesSuccessorPermutation p M σ})
  simp_rw [← sum_successorPermutation_indicators P M]
  rw [lintegral_finsetSum _ (fun σ _ ↦ measurable_const.indicator (hm σ))]
  calc
    _ = ∑ σ : Matching n, ν {x | RealizesSuccessorPermutation (P x) M σ} :=
      Finset.sum_congr rfl fun σ _ ↦ lintegral_indicator_one (hm σ)
    _ ≤ ∑ σ : Matching n, c * ∏ i ∈ σ.support, a * w (σ i) :=
      Finset.sum_le_sum fun σ _ ↦ harc σ
    _ = c * ∑ σ : Matching n, ∏ i ∈ σ.support, a * w (σ i) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right (sum_successorPermutation_product_le a w) c

/-- A joint bound for the realized arrows of each permutation gives a bound
on the moment of two to the exposed rotation count. Each tested permutation
uses at most one arrow per row; no independence is asserted in this lemma. -/
theorem lintegral_pow_numExposedRotations_le {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (P : Ω → Profile n) (hP : Measurable P) (M : Matching n)
    (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞)
    (harc : ∀ σ : Matching n,
      ν {x | RealizesSuccessorPermutation (P x) M σ} ≤ ∏ i ∈ σ.support, a * w (σ i)) :
    (∫⁻ x, (2 : ℝ≥0∞) ^ numExposedRotations (P x) M ∂ν) ≤
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        (s.card.factorial : ℝ≥0∞) * a ^ s.card * ∏ j ∈ s, w j := by
  simpa only [one_mul] using
    lintegral_pow_numExposedRotations_le_mul ν P hP M 1 a w (by simpa only [one_mul])

/-- Under a product law, distinct rows' arc bounds multiply. The row tests
need only contain realized successor events almost everywhere. -/
theorem measure_realizesSuccessorPermutation_le_of_pi {n : ℕ} {β : Fin n → Type*}
    [∀ i, MeasurableSpace (β i)] (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (ν i)]
    (P : (∀ i, β i) → Profile n) (M σ : Matching n)
    (T : (i : Fin n) → Fin n → Set (β i)) (arcWeight : Fin n → Fin n → ℝ≥0∞)
    (hvalid : ∀ᵐ x ∂Measure.pi ν, ∀ i j, IsSuccessor (P x) M i (M j) → x i ∈ T i j)
    (hmarg : ∀ i j, i ≠ j → ν i (T i j) ≤ ν i Set.univ * arcWeight i j) :
    (Measure.pi ν) {x | RealizesSuccessorPermutation (P x) M σ} ≤
      (∏ i, ν i Set.univ) * ∏ i ∈ σ.support, arcWeight i (σ i) := by
  classical
  let B : (i : Fin n) → Set (β i) :=
    fun i ↦ if i ∈ σ.support then T i (σ i) else Set.univ
  have hsub : {x | RealizesSuccessorPermutation (P x) M σ} ≤ᵐ[Measure.pi ν] Set.univ.pi B := by
    filter_upwards [hvalid] with x hx hp
    refine Set.mem_pi.mpr fun i _ ↦ ?_
    by_cases hi : i ∈ σ.support
    · simpa only [B, ite_eq_left hi] using hx i (σ i) (hp i hi)
    · simp only [B, ite_eq_right hi, Set.mem_univ]
  calc
    _ ≤ (Measure.pi ν) (Set.univ.pi B) := measure_mono_ae hsub
    _ = ∏ i, ν i (B i) := Measure.pi_pi ν B
    _ ≤ ∏ i, ν i Set.univ * (if i ∈ σ.support then arcWeight i (σ i) else 1) := by
      refine Finset.prod_le_prod fun i _ ↦ ?_
      by_cases hi : i ∈ σ.support
      · simpa only [B, ite_eq_left hi] using hmarg i (σ i) (Equiv.Perm.mem_support.mp hi).symm
      · simp only [B, ite_eq_right hi, mul_one, le_refl]
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]

/-- For a product of row measures, marginal bounds on row tests suffice.
The row measures need not be probabilities, and it suffices that the
tests capture realized successors almost everywhere. -/
theorem lintegral_pow_numExposedRotations_le_of_pi {n : ℕ} {β : Fin n → Type*}
    [∀ i, MeasurableSpace (β i)] (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (ν i)]
    (P : (∀ i, β i) → Profile n) (hP : Measurable P) (M : Matching n)
    (T : (i : Fin n) → Fin n → Set (β i)) (a : ℝ≥0∞) (w : Fin n → ℝ≥0∞)
    (hvalid : ∀ᵐ x ∂Measure.pi ν, ∀ i j, IsSuccessor (P x) M i (M j) → x i ∈ T i j)
    (hmarg : ∀ i j, i ≠ j → ν i (T i j) ≤ ν i Set.univ * (a * w j)) :
    (∫⁻ x, (2 : ℝ≥0∞) ^ numExposedRotations (P x) M ∂(Measure.pi ν)) ≤
      (∏ i, ν i Set.univ) *
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          (s.card.factorial : ℝ≥0∞) * a ^ s.card * ∏ j ∈ s, w j :=
  lintegral_pow_numExposedRotations_le_mul _ P hP M _ a w fun σ ↦
    measure_realizesSuccessorPermutation_le_of_pi ν P M σ T (fun _ j ↦ a * w j) hvalid hmarg

end LennonPittelFormalization

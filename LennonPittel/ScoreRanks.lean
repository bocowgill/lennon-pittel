module

public import LennonPittel.Model
public import Mathlib.Data.Finset.Sort
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Order.WellFounded

/-!
# Deterministic score ranks for stable marriage

A continuous score profile has one row for each agent. Ranking each row yields the discrete
preference profile, preserving the blocking-pair predicate whenever no row contains a tie.
-/

@[expose] public section

open Function MeasureTheory Set

namespace LennonPittelFormalization

private noncomputable def scoreImage {n : ℕ} (x : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image x

private theorem card_scoreImage {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) :
    (scoreImage x).card = n := by
  rw [scoreImage, Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]

private noncomputable def scoreEquiv {n : ℕ} (x : Fin n → ℝ) (hx : Injective x) :
    Fin n ≃ (scoreImage x : Set ℝ) :=
  Equiv.ofBijective (fun i ↦ ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩)
    ⟨fun _ _ h ↦ hx (congrArg Subtype.val h), fun y ↦
      let ⟨i, _, hi⟩ := Finset.mem_image.mp (show y.val ∈ Finset.univ.image x from y.property)
      ⟨i, Subtype.ext hi⟩⟩

/-- The permutation sending each candidate to its increasing score rank.
On tied scores we use the identity permutation. -/
@[no_expose]
noncomputable def rankPermutation {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Injective x then
    (scoreEquiv x h).trans ((scoreImage x).orderIsoOfFin (card_scoreImage h)).symm.toEquiv
  else Equiv.refl _

/-- On an injective score row, rank comparison is exactly score comparison. -/
theorem rankPermutation_lt_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x) (i j : Fin n) :
    rankPermutation x i < rankPermutation x j ↔ x i < x j := by
  classical
  unfold rankPermutation
  rw [dite_eq_left hx]
  exact ((scoreImage x).orderIsoOfFin (card_scoreImage hx)).symm.lt_iff_lt
    (x := scoreEquiv x hx i) (y := scoreEquiv x hx j)

private def rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  {x | ∀ i j, p i < p j → x i < x j}

private theorem measurableSet_rankChamber {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurableSet (rankChamber p) := by
  unfold rankChamber
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : p i < p j
  · simpa only [h, true_implies] using
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j) :
        MeasurableSet {x : Fin n → ℝ | x i < x j})
  · simp [h]

private theorem measurableSet_injective_row (n : ℕ) :
    MeasurableSet {x : Fin n → ℝ | Injective x} := by
  unfold Injective
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases h : i = j
  · simp [h]
  · exact ((measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j) :
      MeasurableSet {x : Fin n → ℝ | x i = x j}).compl).congr (by ext x; simp [h])

private theorem rankPermutation_eq_iff {n : ℕ} {x : Fin n → ℝ} (hx : Injective x)
    (p : Equiv.Perm (Fin n)) : rankPermutation x = p ↔ x ∈ rankChamber p := by
  constructor
  · rintro rfl i j hij
    exact (rankPermutation_lt_iff hx i j).mp hij
  · intro hp
    have hmono : StrictMono (rankPermutation x ∘ p.symm) := fun i j hij ↦
      (rankPermutation_lt_iff hx (p.symm i) (p.symm j)).mpr <|
        hp (p.symm i) (p.symm j) (by simpa using hij)
    apply Equiv.ext
    intro i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, id_eq] using
      le_antisymm (hmono.le_id (p i)) (hmono.id_le (p i))

/-- Ranking a score row is measurable for the discrete space of permutations. -/
theorem measurable_rankPermutation (n : ℕ) :
    @Measurable (Fin n → ℝ) (Equiv.Perm (Fin n)) inferInstance ⊤ rankPermutation := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  apply measurable_to_countable'
  intro p
  have hpre : rankPermutation ⁻¹' {p} =
      ({x : Fin n → ℝ | Injective x} ∩ rankChamber p) ∪
        ({x : Fin n → ℝ | Injective x}ᶜ ∩ {x : Fin n → ℝ | Equiv.refl (Fin n) = p}) := by
    ext x
    by_cases hx : Injective x
    · simpa only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, hx, not_true_eq_false, true_and, false_and, or_false] using
          rankPermutation_eq_iff hx p
    · simp [rankPermutation, hx]
  rw [hpre]
  exact ((measurableSet_injective_row n).inter (measurableSet_rankChamber p)).union
    ((measurableSet_injective_row n).compl.inter (MeasurableSet.const _))

/-- A row for each man (left summand) and woman (right summand), with one score per candidate. -/
abbrev ScoreProfile (n : ℕ) := (Fin n ⊕ Fin n) → Fin n → ℝ

/-- Replace each score row by its increasing rank permutation. -/
noncomputable def profileOfScores {n : ℕ} (x : ScoreProfile n) : StableMarriage.Profile n :=
  ⟨fun m ↦ rankPermutation (x (.inl m)), fun w ↦ rankPermutation (x (.inr w))⟩

/-- The discrete profile induced by the score array is measurable. -/
theorem measurable_profileOfScores (n : ℕ) : Measurable (@profileOfScores n) := by
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) :=
    ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hrow (r : Fin n ⊕ Fin n) (p : Equiv.Perm (Fin n)) :
      MeasurableSet {x : ScoreProfile n | rankPermutation (x r) = p} :=
    ((measurable_rankPermutation n).comp (measurable_pi_apply r)) (measurableSet_singleton p)
  apply measurable_to_countable'
  rintro ⟨men, women⟩
  change MeasurableSet {x | profileOfScores x = ⟨men, women⟩}
  simp only [profileOfScores, StableMarriage.Profile.mk.injEq, funext_iff, Set.ofPred_and,
    Set.ofPred_forall]
  exact (MeasurableSet.iInter fun m ↦ hrow (.inl m) (men m)).inter
    (MeasurableSet.iInter fun w ↦ hrow (.inr w) (women w))

/-- A blocking pair when smaller real scores mean a better partner. -/
def IsScoreBlockingPair {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n)
    (m w : Fin n) : Prop :=
  μ m ≠ w ∧ x (.inl m) w < x (.inl m) (μ m) ∧ x (.inr w) m < x (.inr w) (μ.symm w)

/-- A matching is score-stable when no pair strictly prefers each other to their partners. -/
def IsScoreStable {n : ℕ} (x : ScoreProfile n) (μ : StableMarriage.Matching n) : Prop :=
  ∀ m w, ¬ IsScoreBlockingPair x μ m w

/-- Strict score comparisons give exactly the same blocking pairs as the induced ranks. -/
theorem isBlockingPair_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) (m w : Fin n) :
    StableMarriage.IsBlockingPair (profileOfScores x) μ m w ↔ IsScoreBlockingPair x μ m w := by
  simp only [StableMarriage.IsBlockingPair, profileOfScores, IsScoreBlockingPair,
    rankPermutation_lt_iff (hx (.inl m)), rankPermutation_lt_iff (hx (.inr w))]

/-- For a score profile without ties in any row, stability is unchanged by taking ranks. -/
theorem isStable_profileOfScores_iff {n : ℕ} {x : ScoreProfile n}
    (hx : ∀ r, Injective (x r)) (μ : StableMarriage.Matching n) :
    StableMarriage.IsStable (profileOfScores x) μ ↔ IsScoreStable x μ := by
  simp only [StableMarriage.IsStable, IsScoreStable, isBlockingPair_profileOfScores_iff hx]

/-- For a fixed matching, score stability is a measurable event even on tied rows. -/
theorem measurableSet_isScoreStable {n : ℕ} (μ : StableMarriage.Matching n) :
    MeasurableSet {x : ScoreProfile n | IsScoreStable x μ} := by
  have hcell (r : Fin n ⊕ Fin n) (a : Fin n) : Measurable (fun x : ScoreProfile n ↦ x r a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply r)
  unfold IsScoreStable
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun m ↦ ?_
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun w ↦ ?_
  by_cases h : μ m = w
  · simp [IsScoreBlockingPair, h]
  · exact ((measurableSet_lt (hcell (.inl m) w) (hcell (.inl m) (μ m))).inter
      (measurableSet_lt (hcell (.inr w) m) (hcell (.inr w) (μ.symm w)))).compl.congr
        (Set.ext fun x ↦ by simp [IsScoreBlockingPair, h])

/-- Score stability is a measurable event in the space of profiles with a marked matching. -/
theorem measurableSet_scoreStableEvent (n : ℕ) [MeasurableSpace (StableMarriage.Matching n)]
    [MeasurableSingletonClass (StableMarriage.Matching n)] :
    MeasurableSet {z : ScoreProfile n × StableMarriage.Matching n | IsScoreStable z.1 z.2} :=
  (measurable_from_prod_countable_left fun μ ↦
    measurableSet_setOfPred.mp (measurableSet_isScoreStable μ)).setOf

end LennonPittelFormalization


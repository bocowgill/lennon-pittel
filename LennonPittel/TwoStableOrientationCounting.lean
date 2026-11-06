module

public import LennonPittel.PivotResidualImageGeometry
public import LennonPittel.ShortCycleChebyshev
public import LennonPittel.UniformShortCycleMoments

/-!
# Counting labeled two-matching orientations

Fix the sizes of an ordered cycle partition of the relative permutation.
One matching, the two disjoint sets of men, and two permutations on these
sets determine the full labeled data. The permutations have no fixed
points. Keeping their cycle-type restrictions makes a rare uniform cycle
event reduce the same labeling envelope.
-/

@[expose] public section

open Equiv Equiv.Perm Finset StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {n : ℕ}

/-- Two sets that partition the nontrivial cycles of the relative permutation. -/
structure LabeledPairOrientation (μ ν : Matching n) (U V : Finset (Fin n)) : Prop where
  disjoint : Disjoint U V
  union_support : U ∪ V = (relativeMenPermutation μ ν).support
  preserves_left : ∀ i, relativeMenPermutation μ ν i ∈ U ↔ i ∈ U
  preserves_right : ∀ i, relativeMenPermutation μ ν i ∈ V ↔ i ∈ V

namespace LabeledPairOrientation

variable {μ ν : Matching n} {U V : Finset (Fin n)}

/-- The relative permutation restricted to the first orientation. -/
def leftPerm (h : LabeledPairOrientation μ ν U V) : Perm U :=
  (relativeMenPermutation μ ν).subtypePerm h.preserves_left

/-- The relative permutation restricted to the second orientation. -/
def rightPerm (h : LabeledPairOrientation μ ν U V) : Perm V :=
  (relativeMenPermutation μ ν).subtypePerm h.preserves_right

theorem leftPerm_apply_ne (h : LabeledPairOrientation μ ν U V) (i : U) :
    h.leftPerm i ≠ i := by
  intro he
  apply mem_support.mp (h.union_support ▸ mem_union_left V i.property)
  exact congrArg Subtype.val he

theorem rightPerm_apply_ne (h : LabeledPairOrientation μ ν U V) (i : V) :
    h.rightPerm i ≠ i := by
  intro he
  apply mem_support.mp (h.union_support ▸ mem_union_right U i.property)
  exact congrArg Subtype.val he

end LabeledPairOrientation

/-- Ordered disjoint side choices of sizes u and v. -/
abbrev OrientationSideChoices (n u v : ℕ) :=
  Σ U : ↥((univ : Finset (Fin n)).powersetCard u), ↥(U.valᶜ.powersetCard v)

theorem card_orientationSideChoices (n u v : ℕ) :
    Nat.card (OrientationSideChoices n u v) = n.choose u * (n - u).choose v := by
  rw [Nat.card_sigma]
  have hcard (U : ↥((univ : Finset (Fin n)).powersetCard u)) : U.val.card = u :=
    (mem_powersetCard.mp U.property).2
  simp only [Nat.card_eq_finsetCard, card_powersetCard, card_compl, Fintype.card_fin, hcard,
    sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe]
  rfl

/-- Derangements on k labels whose cycle types satisfy P. -/
abbrev RestrictedOrientationPerm (k : ℕ) (P : Multiset ℕ → Prop) :=
  {f : Perm (Fin k) // (∀ i, f i ≠ i) ∧ P f.cycleType}

/-- The labeled two-matching data with ordered orientations and cycle-type tests. -/
abbrev LabeledOrientationPairs (n u v : ℕ) (P Q : Multiset ℕ → Prop) :=
  {z : (Matching n × Matching n) × (Finset (Fin n) × Finset (Fin n)) //
    ∃ h : LabeledPairOrientation z.1.1 z.1.2 z.2.1 z.2.2,
      z.2.1.card = u ∧ z.2.2.card = v ∧ P h.leftPerm.cycleType ∧ Q h.rightPerm.cycleType}

private noncomputable def relabelOrientationSide {k : ℕ} {S : Finset (Fin n)}
    (hS : S.card = k) : Fin k ≃ S :=
  Fintype.equivOfCardEq (by simp [hS])

private theorem cycleType_ofSubtype_finset {S : Finset (Fin n)} (p : Perm S) :
    p.ofSubtype.cycleType = p.cycleType :=
  cycleType_ofSubtype (g := p)

private theorem relabelSide_cycleType {k : ℕ} {S : Finset (Fin n)}
    (e : Fin k ≃ S) (p : Perm S) : (e.permCongr.symm p).cycleType = p.cycleType := by
  rw [← cycleType_extendDomain e]
  change (ofSubtype (e.permCongr (e.permCongr.symm p))).cycleType = _
  rw [e.permCongr.apply_symm_apply, cycleType_ofSubtype_finset]

private theorem relabelSide_apply_ne {k : ℕ} {S : Finset (Fin n)}
    (e : Fin k ≃ S) {p : Perm S} (hp : ∀ i, p i ≠ i) (j : Fin k) :
    e.permCongr.symm p j ≠ j := by
  intro he
  apply hp (e j)
  simpa only [Equiv.permCongr_symm_apply, Equiv.apply_symm_apply] using congrArg e he

/-- One matching, the two side sets, and the two restricted derangements
encode the labeled ordered pair and its orientation without loss. -/
@[no_expose]
noncomputable def labeledOrientationPairsEmbedding (n u v : ℕ) (P Q : Multiset ℕ → Prop) :
    LabeledOrientationPairs n u v P Q ↪
      Matching n × OrientationSideChoices n u v ×
        RestrictedOrientationPerm u P × RestrictedOrientationPerm v Q := by
  let encode (z : LabeledOrientationPairs n u v P Q) :
      Matching n × OrientationSideChoices n u v ×
        RestrictedOrientationPerm u P × RestrictedOrientationPerm v Q := by
    let h := z.property.choose
    have hU := z.property.choose_spec.1
    have hV := z.property.choose_spec.2.1
    have hP := z.property.choose_spec.2.2.1
    have hQ := z.property.choose_spec.2.2.2
    let eU := relabelOrientationSide hU
    let eV := relabelOrientationSide hV
    exact ⟨z.val.1.1, ⟨⟨z.val.2.1, mem_powersetCard.mpr ⟨subset_univ _, hU⟩⟩,
      ⟨z.val.2.2, mem_powersetCard.mpr
        ⟨fun _ hi ↦ mem_compl.mpr fun hU' ↦ disjoint_left.mp h.disjoint hU' hi, hV⟩⟩⟩,
      ⟨eU.permCongr.symm h.leftPerm, relabelSide_apply_ne eU h.leftPerm_apply_ne,
        (relabelSide_cycleType eU h.leftPerm).symm ▸ hP⟩,
      ⟨eV.permCongr.symm h.rightPerm, relabelSide_apply_ne eV h.rightPerm_apply_ne,
        (relabelSide_cycleType eV h.rightPerm).symm ▸ hQ⟩⟩
  refine ⟨encode, ?_⟩
  rintro ⟨⟨⟨μ, ν⟩, U, V⟩, hz⟩ ⟨⟨⟨μ', ν'⟩, U', V'⟩, hw⟩ he
  have hμ : μ = μ' := congrArg (fun z ↦ z.1) he
  have hU : U = U' := congrArg (fun z ↦ z.2.1.1.val) he
  have hV : V = V' := congrArg (fun z ↦ z.2.1.2.val) he
  subst μ' U' V'
  have hleft : hz.choose.leftPerm = hw.choose.leftPerm := by
    have hp := congrArg (fun z ↦ z.2.2.1.val) he
    exact (relabelOrientationSide hz.choose_spec.1).permCongr.symm.injective hp
  have hright : hz.choose.rightPerm = hw.choose.rightPerm := by
    have hp := congrArg (fun z ↦ z.2.2.2.val) he
    exact (relabelOrientationSide hz.choose_spec.2.1).permCongr.symm.injective hp
  have hrel : relativeMenPermutation μ ν = relativeMenPermutation μ ν' := by
    apply Equiv.ext
    intro i
    by_cases hiU : i ∈ U
    · exact congrArg (fun f : Perm U ↦ (f ⟨i, hiU⟩).val) hleft
    by_cases hiV : i ∈ V
    · exact congrArg (fun f : Perm V ↦ (f ⟨i, hiV⟩).val) hright
    have hi : i ∉ U ∪ V := fun h ↦ (mem_union.mp h).elim hiU hiV
    exact (notMem_support.mp (hz.choose.union_support ▸ hi)).trans
      (notMem_support.mp (hw.choose.union_support ▸ hi)).symm
  have hνsymm : ν.symm = ν'.symm := by
    apply Equiv.ext
    intro i
    simpa only [relativeMenPermutation, Equiv.trans_apply, Equiv.apply_symm_apply] using
      congrArg (fun f : Matching n ↦ f (μ.symm i)) hrel
  have hν : ν = ν' := congrArg Equiv.symm hνsymm
  exact Subtype.ext (congrArg (fun m ↦ ((μ, m), U, V)) hν)

/-- The labeled-pair count with arbitrary invariant tests on the cycle types. -/
theorem card_labeledOrientationPairs_le (n u v : ℕ) (P Q : Multiset ℕ → Prop) :
    Nat.card (LabeledOrientationPairs n u v P Q) ≤
      n.factorial * (n.choose u * (n - u).choose v) *
        (Nat.card (RestrictedOrientationPerm u P) * Nat.card (RestrictedOrientationPerm v Q)) := by
  have h := Nat.card_le_card_of_injective _ (labeledOrientationPairsEmbedding n u v P Q).injective
  refine h.trans_eq ?_
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_orientationSideChoices,
    Nat.card_eq_fintype_card (α := Matching n)]
  simp only [Matching, Fintype.card_perm, Fintype.card_fin, mul_assoc]

private theorem orientationChoices_mul_factorials {n u v : ℕ} :
    (n.choose u * (n - u).choose v) * u.factorial * v.factorial =
      n.descFactorial (u + v) := by
  calc
    _ = ((n - u).choose v * v.factorial) * (n.choose u * u.factorial) := by ring
    _ = (n - u).descFactorial v * n.descFactorial u := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
    _ = _ := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.descFactorial_mul_descFactorial (n := n) (Nat.le_add_right u v))

/-- The factorial envelope with both cycle-type tests paid as derangement
fractions relative to uniform permutations. -/
theorem card_labeledOrientationPairs_real_le {n u v : ℕ} (h : u + v ≤ n)
    (P Q : Multiset ℕ → Prop) :
    (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ) ≤
      ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) *
        ((Nat.card (RestrictedOrientationPerm u P) : ℝ) / u.factorial) *
          ((Nat.card (RestrictedOrientationPerm v Q) : ℝ) / v.factorial) := by
  have hdesc : (n.factorial : ℝ) / (n - u - v).factorial =
      (n.descFactorial (u + v) : ℝ) := by
    apply (div_eq_iff (by positivity)).mpr
    rw [← Nat.sub_add_eq, mul_comm]
    exact_mod_cast (Nat.factorial_mul_descFactorial h).symm
  have hc : (n.choose u : ℝ) * (n - u).choose v * u.factorial * v.factorial =
      (n.descFactorial (u + v) : ℝ) := by exact_mod_cast orientationChoices_mul_factorials
  calc
    _ ≤ (n.factorial : ℝ) * ((n.choose u : ℝ) * (n - u).choose v) *
        ((Nat.card (RestrictedOrientationPerm u P) : ℝ) *
          Nat.card (RestrictedOrientationPerm v Q)) := by
      exact_mod_cast card_labeledOrientationPairs_le n u v P Q
    _ = _ := by
      rw [pow_two, mul_div_assoc, hdesc, ← hc]
      field_simp

/-- Unrestricted uniform permutation mass of the cycle-type condition. -/
noncomputable def orientationCycleTypeFraction (k : ℕ) (P : Multiset ℕ → Prop) : ℝ≥0∞ :=
  (Nat.card {f : Perm (Fin k) // P f.cycleType} : ℝ≥0∞) / k.factorial

/-- Dropping the derangement restriction gives the desired uniform fraction,
without changing the factorial envelope or losing the cycle-type test. -/
theorem card_labeledOrientationPairs_le_cycleTypeFractions {n u v : ℕ} (h : u + v ≤ n)
    (P Q : Multiset ℕ → Prop) :
    (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ≥0∞) ≤
      ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        orientationCycleTypeFraction u P * orientationCycleTypeFraction v Q := by
  let B (k : ℕ) (F : Multiset ℕ → Prop) := Nat.card {f : Perm (Fin k) // F f.cycleType}
  have hB (k : ℕ) (F : Multiset ℕ → Prop) : Nat.card (RestrictedOrientationPerm k F) ≤ B k F :=
    Nat.card_le_card_of_injective (fun f : RestrictedOrientationPerm k F ↦ ⟨f.val, f.property.2⟩)
      (fun _ _ he ↦ Subtype.ext (congrArg (fun f : {f : Perm (Fin k) // F f.cycleType} ↦ f.val) he))
  have hr := card_labeledOrientationPairs_real_le h P Q
  have ht : (Nat.card (LabeledOrientationPairs n u v P Q) : ℝ) ≤
      ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) *
        ((B u P : ℝ) / u.factorial) * ((B v Q : ℝ) / v.factorial) := by
    refine hr.trans ?_
    gcongr
    · exact_mod_cast hB u P
    · exact_mod_cast hB v Q
  have he := ENNReal.ofReal_le_ofReal ht
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)] at he
  simpa only [ENNReal.ofReal_natCast, orientationCycleTypeFraction, B] using he

@[simp]
theorem orientationCycleTypeFraction_true (k : ℕ) :
    orientationCycleTypeFraction k (fun _ ↦ True) = 1 := by
  unfold orientationCycleTypeFraction
  have e : {f : Perm (Fin k) // True} ≃ Perm (Fin k) :=
    Equiv.subtypeUnivEquiv (fun _ ↦ trivial)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  exact ENNReal.div_self (by positivity) (ENNReal.natCast_ne_top _)

/-- The unrestricted count for fixed orientation sizes. -/
theorem card_labeledOrientationPairs_unrestricted_le {n u v : ℕ} (h : u + v ≤ n) :
    (Nat.card (LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True)) : ℝ≥0∞) ≤
      (n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial := by
  simpa only [orientationCycleTypeFraction_true, mul_one] using
    card_labeledOrientationPairs_le_cycleTypeFractions h (fun _ ↦ True) (fun _ ↦ True)

/-- When a moved man prefers the first matching, his first wife prefers her
partner in the second matching, by stability of the second matching. -/
theorem womanRank_second_lt_first_of_worsePartnerMen {p : Profile n} {μ ν : Matching n}
    (hν : IsStable p ν) {i : Fin n} (hi : i ∈ worsePartnerMen p ν μ) :
    p.womanRank (μ i) (ν.symm (μ i)) < p.womanRank (μ i) i := by
  have hm := (mem_filter.mp hi).2
  have hne : ν i ≠ μ i := fun h ↦ hm.ne (congrArg (p.manRank i) h).symm
  have hj : ν.symm (μ i) ≠ i := fun h ↦ hne (ν.symm_apply_eq.mp h).symm
  refine lt_of_le_of_ne (le_of_not_gt ?_) ((p.womanRank (μ i)).injective.ne hj)
  exact fun h ↦ hν i (μ i) ⟨hne, hm, h⟩

private theorem relativeMenPermutation_maps_worsePartnerMen {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) {i : Fin n} (hi : i ∈ worsePartnerMen p ν μ) :
    relativeMenPermutation μ ν i ∈ worsePartnerMen p ν μ := by
  let j := ν.symm (μ i)
  have hνj : ν j = μ i := ν.apply_symm_apply _
  have hw : p.womanRank (μ i) j < p.womanRank (μ i) i :=
    womanRank_second_lt_first_of_worsePartnerMen hν hi
  have hμj : μ j ≠ ν j := by
    intro h
    have hj : j = i := μ.injective (h.trans hνj)
    exact hw.ne (congrArg (p.womanRank (μ i)) hj)
  refine mem_filter.mpr ⟨mem_univ _, lt_of_le_of_ne (le_of_not_gt ?_)
    ((p.manRank j).injective.ne hμj)⟩
  intro h
  exact hμ j (μ i) ⟨fun h' ↦ hμj (h'.trans hνj.symm), hνj ▸ h,
    by simpa only [Equiv.symm_apply_apply] using hw⟩

private theorem perm_mem_iff_of_maps_finset (f : Matching n) (S : Finset (Fin n))
    (hf : ∀ i ∈ S, f i ∈ S) (i : Fin n) : f i ∈ S ↔ i ∈ S := by
  have he : S.image f = S := eq_of_subset_of_card_le (by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
    exact hf k hk) ((card_image_of_injective S f.injective).ge)
  refine ⟨fun h ↦ ?_, hf i⟩
  obtain ⟨k, hk, heq⟩ := mem_image.mp (he.symm ▸ h)
  exact f.injective heq ▸ hk

/-- Any two stable matchings determine a labeled orientation, not just the
ones obtained by the shared-switch toggle. -/
theorem labeledPairOrientation_of_stable {p : Profile n} {μ ν : Matching n}
    (hμ : IsStable p μ) (hν : IsStable p ν) :
    LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) := by
  have hright := perm_mem_iff_of_maps_finset (relativeMenPermutation μ ν) (worsePartnerMen p ν μ)
    (fun _ hi ↦ relativeMenPermutation_maps_worsePartnerMen hμ hν hi)
  have hleft' := perm_mem_iff_of_maps_finset (relativeMenPermutation ν μ) (worsePartnerMen p μ ν)
    (fun _ hi ↦ relativeMenPermutation_maps_worsePartnerMen hν hμ hi)
  refine ⟨disjoint_worsePartnerMen p μ ν, union_worsePartnerMen_eq_support p μ ν, ?_, hright⟩
  intro i
  have hi := hleft' (relativeMenPermutation μ ν i)
  have he : relativeMenPermutation ν μ (relativeMenPermutation μ ν i) = i := by
    simp only [relativeMenPermutation, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]
  rw [he] at hi
  exact hi.symm

/-- The labeled orientation of any stable pair with specified sizes. -/
def labeledOrientationPairOfStable {p : Profile n} {μ ν : Matching n} {u v : ℕ}
    (hμ : IsStable p μ) (hν : IsStable p ν)
    (hu : (worsePartnerMen p μ ν).card = u) (hv : (worsePartnerMen p ν μ).card = v) :
    LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True) :=
  ⟨((μ, ν), worsePartnerMen p μ ν, worsePartnerMen p ν μ),
    labeledPairOrientation_of_stable hμ hν, hu, hv, trivial, trivial⟩

/-- The orientation of a residual pair provides the labeled cycle partition. -/
theorem IsResidualPairRankGeometry.labeledPairOrientation {b : ℝ} {K L : ℕ}
    {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν) :
    LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ) :=
  labeledPairOrientation_of_stable h.stable_early h.stable_late

/-- Extending the restricted permutation by fixed points retains precisely
the ambient cycles contained in the first orientation. -/
theorem LabeledPairOrientation.cycleFactorsFinset_ofSubtype_leftPerm
    {μ ν : Matching n} {U V : Finset (Fin n)} (h : LabeledPairOrientation μ ν U V) :
    h.leftPerm.ofSubtype.cycleFactorsFinset =
      (relativeMenPermutation μ ν).cycleFactorsFinset.filter fun c ↦ c.support ⊆ U := by
  classical
  let f := relativeMenPermutation μ ν
  let g := h.leftPerm.ofSubtype
  have hsub : g.support ⊆ U := by
    intro i hi
    by_contra hn
    exact mem_support.mp hi (ofSubtype_apply_of_not_mem h.leftPerm hn)
  have hagree (i : Fin n) (hi : i ∈ U) : g i = f i :=
    ofSubtype_apply_of_mem h.leftPerm hi
  ext c
  rw [mem_filter]
  constructor
  · intro hc
    have hcu := (mem_cycleFactorsFinset_support_le hc).trans hsub
    obtain ⟨hcyc, hcg⟩ := mem_cycleFactorsFinset_iff.mp hc
    exact ⟨mem_cycleFactorsFinset_iff.mpr ⟨hcyc, fun i hi ↦
      (hcg i hi).trans (hagree i (hcu hi))⟩, hcu⟩
  · rintro ⟨hc, hcu⟩
    obtain ⟨hcyc, hcf⟩ := mem_cycleFactorsFinset_iff.mp hc
    exact mem_cycleFactorsFinset_iff.mpr ⟨hcyc, fun i hi ↦
      (hcf i hi).trans (hagree i (hcu hi)).symm⟩

/-- The short cycles forced by the residual orientation are exactly the
short nontrivial cycles of the restricted permutation. -/
theorem forcedShortCycles_card_eq_shortCycleCount_leftPerm
    {p : Profile n} {μ ν : Matching n} (L : ℕ)
    (h : LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ)) :
    (forcedShortCycles p μ ν L).card = shortCycleCount L h.leftPerm := by
  unfold shortCycleCount
  rw [← cycleType_ofSubtype_finset h.leftPerm]
  simp only [Equiv.Perm.cycleType, Multiset.filter_map, Multiset.card_map]
  change (forcedShortCycles p μ ν L).card =
    (h.leftPerm.ofSubtype.cycleFactorsFinset.filter (fun c ↦ c.support.card ≤ L)).card
  rw [h.cycleFactorsFinset_ofSubtype_leftPerm, filter_filter]
  apply congrArg Finset.card
  ext c
  simp only [forcedShortCycles, mem_filter]

/-- The forced-cycle exception expressed as a predicate of the first
relative permutation's cycle type. -/
def forcedShortCycleTypeException (L : ℕ) (T : Multiset ℕ) : Prop :=
  (((T.filter (· ≤ L)).card : ℕ) : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)

/-- On a residual pair the fixed forced-cycle test is a cycle-type test
on the first orientation, independent of the actual labels. -/
theorem forcedShortCycleTypeException_leftPerm_iff
    {p : Profile n} {μ ν : Matching n} (L : ℕ)
    (h : LabeledPairOrientation μ ν (worsePartnerMen p μ ν) (worsePartnerMen p ν μ)) :
    forcedShortCycleTypeException L h.leftPerm.cycleType ↔
      ((forcedShortCycles p μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ) := by
  rw [forcedShortCycles_card_eq_shortCycleCount_leftPerm L h]
  rfl

open scoped Classical in
/-- A finite uniform count falls below a threshold separated from its mean
only on a fraction controlled by its variance. -/
theorem finiteCountChebyshev_below {α : Type*} [Fintype α] [Nonempty α]
    (C : α → ℕ) {H T : ℝ} (hT : T < H)
    (hmean : (∑ i, (C i : ℝ)) = (Fintype.card α : ℝ) * H)
    (hpair : (∑ i, (C i : ℝ) * ((C i : ℝ) - 1)) ≤ (Fintype.card α : ℝ) * H ^ 2) :
    ((univ.filter (fun i ↦ (C i : ℝ) < T)).card : ℝ) / (Fintype.card α : ℝ) ≤
      H / (H - T) ^ 2 := by
  let S := univ.filter (fun i ↦ (C i : ℝ) < T)
  have hs : (∑ i, ((C i : ℝ) - H) ^ 2) ≤ (Fintype.card α : ℝ) * H := by
    calc
      _ = ∑ i, ((C i : ℝ) * ((C i : ℝ) - 1) + (C i : ℝ) -
          2 * H * (C i : ℝ) + H ^ 2) := sum_congr rfl fun i _ ↦ by ring
      _ = (∑ i, (C i : ℝ) * ((C i : ℝ) - 1)) + (∑ i, (C i : ℝ)) -
          2 * H * (∑ i, (C i : ℝ)) + (Fintype.card α : ℝ) * H ^ 2 := by
        simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
      _ ≤ _ := by rw [hmean]; nlinarith only [hpair]
  have ht : (S.card : ℝ) * (H - T) ^ 2 ≤ (Fintype.card α : ℝ) * H := by
    calc
      _ = ∑ i ∈ S, (H - T) ^ 2 := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, ((C i : ℝ) - H) ^ 2 := by
        refine sum_le_sum fun i hi ↦ ?_
        have hci := (mem_filter.mp hi).2
        rw [show ((C i : ℝ) - H) ^ 2 = (H - (C i : ℝ)) ^ 2 by ring]
        exact pow_le_pow_left₀ (sub_nonneg.mpr hT.le) (sub_le_sub_left hci.le H) 2
      _ ≤ ∑ i, ((C i : ℝ) - H) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
      _ ≤ _ := hs
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (div_le_div_iff₀ hc (pow_pos (sub_pos.mpr hT) _)).mpr (by simpa [mul_comm] using ht)

private theorem log_sub_one_le_shortCycleHarmonic {k L : ℕ} (hL : 2 ≤ L) (hk : L ≤ k) :
    Real.log (L : ℝ) - 1 ≤ ∑ j ∈ Icc 2 (min L k), (1 : ℝ) / j := by
  have h₁ : 1 ∈ Icc 1 L := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Icc 1 L).erase 1 = Icc 2 L := by
    ext j
    simp only [mem_erase, mem_Icc]
    omega
  have hh := log_le_harmonic_floor (L : ℝ) (by positivity)
  rw [Nat.floor_natCast] at hh
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  rw [← sum_erase_add (Icc 1 L) (fun j ↦ (j : ℝ)⁻¹) h₁, he, Nat.cast_one, inv_one] at hh
  rw [min_eq_left hk]
  simpa only [one_div] using (sub_le_iff_le_add.mpr hh)

/-- The exceptional forced-cycle fraction vanishes uniformly for a side
with at least L labels. -/
theorem forcedShortCycleTypeException_fraction_le {k L : ℕ} (hL : 2 ≤ L) (hk : L ≤ k)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    orientationCycleTypeFraction k (forcedShortCycleTypeException L) ≤
      ENNReal.ofReal (400 / Real.log (L : ℝ)) := by
  classical
  let H := ∑ j ∈ Icc 2 (min L k), (1 : ℝ) / j
  let ell := Real.log (L : ℝ)
  let T := (9 / 10 : ℝ) * ell
  have hl : 0 < ell := by linarith
  have hHlo : ell - 1 ≤ H := log_sub_one_le_shortCycleHarmonic hL hk
  have hHhi : H ≤ ell := shortCycleHarmonic_le_log k L hL
  have hgap : ell / 20 ≤ H - T := by dsimp [T]; linarith
  have hT : T < H := by linarith
  have hc : Fintype.card (Perm (Fin k)) = k.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  have h := finiteCountChebyshev_below (shortCycleCount L) hT
    (by rw [hc]; exact sum_shortCycleCount k L)
    (by rw [hc]; exact sum_shortCycleCount_mul_sub_one_le k L)
  rw [hc] at h
  have hbound : H / (H - T) ^ 2 ≤ 400 / ell := calc
    _ ≤ ell / (H - T) ^ 2 :=
      div_le_div_of_nonneg_right hHhi (sq_nonneg _)
    _ ≤ ell / (ell / 20) ^ 2 :=
      div_le_div_of_nonneg_left hl.le (by positivity)
        (pow_le_pow_left₀ (by positivity) hgap 2)
    _ = _ := by field_simp; ring
  have hb := ENNReal.ofReal_le_ofReal (h.trans hbound)
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast] at hb
  unfold orientationCycleTypeFraction
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [ENNReal.ofReal_natCast, forcedShortCycleTypeException, shortCycleCount, T, ell] at hb ⊢
  exact hb

/-- The usual factorial envelope multiplied by the rare forced-cycle fraction. -/
theorem card_labeledOrientationPairs_forcedShortException_le {n u v L : ℕ} (h : u + v ≤ n)
    (hL : 2 ≤ L) (hu : L ≤ u) (hlog : 100 ≤ Real.log (L : ℝ)) :
    (Nat.card (LabeledOrientationPairs n u v (forcedShortCycleTypeException L) (fun _ ↦ True)) :
      ℝ≥0∞) ≤ ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (400 / Real.log (L : ℝ)) := by
  have hc := card_labeledOrientationPairs_le_cycleTypeFractions h
    (forcedShortCycleTypeException L) (fun _ ↦ True)
  rw [orientationCycleTypeFraction_true, mul_one] at hc
  exact hc.trans (mul_le_mul_right (forcedShortCycleTypeException_fraction_le hL hu hlog) _)

/-- Attach the two rank-oriented supports to the endpoints of a residual pair. -/
def IsResidualPairRankGeometry.toLabeledOrientationPair {b : ℝ} {K L u v : ℕ}
    {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν)
    (hu : (worsePartnerMen p μ ν).card = u) (hv : (worsePartnerMen p ν μ).card = v) :
    LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True) :=
  ⟨((μ, ν), worsePartnerMen p μ ν, worsePartnerMen p ν μ),
    h.labeledPairOrientation, hu, hv, trivial, trivial⟩

/-- The same labeled pair carries the rare short-side cycle-type test when
the forced short-cycle count is below its threshold. -/
def IsResidualPairRankGeometry.toForcedExceptionLabeledOrientationPair {b : ℝ} {K L u v : ℕ}
    {p : Profile n} {μ ν : Matching n} (h : IsResidualPairRankGeometry b K L p μ ν)
    (hu : (worsePartnerMen p μ ν).card = u) (hv : (worsePartnerMen p ν μ).card = v)
    (he : ((forcedShortCycles p μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)) :
    LabeledOrientationPairs n u v (forcedShortCycleTypeException L) (fun _ ↦ True) :=
  ⟨((μ, ν), worsePartnerMen p μ ν, worsePartnerMen p ν μ),
    h.labeledPairOrientation, hu, hv,
    (forcedShortCycleTypeException_leftPerm_iff L h.labeledPairOrientation).mpr he, trivial⟩

end LennonPittelFormalization

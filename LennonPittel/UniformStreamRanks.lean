module

public import LennonPittel.MarkedCounting
public import LennonPittel.ScoreRanks
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Completing a finite proposal stream to a ranking

The first occurrence in a stream determines each observed receiver's priority. Receivers
absent from the stream follow in an independent fallback order. Relabeling the receivers
commutes with the completion, so independent uniform inputs give a uniform ranking.
-/

@[expose] public section

open Function MeasureTheory
open scoped ENNReal LennonPittelFormalization

namespace LennonPittelFormalization

variable {n T : ℕ}

private def IsStreamHit (raw : Fin T → Fin n) (w : Fin n) (k : ℕ) : Prop :=
  k = T ∨ ∃ i : Fin T, i.val = k ∧ raw i = w

private theorem exists_streamHit (raw : Fin T → Fin n) (w : Fin n) :
    ∃ k, IsStreamHit raw w k :=
  ⟨T, Or.inl rfl⟩

/-- The index of the first draw of a receiver, or the stream length if it never appears. -/
@[no_expose]
noncomputable def streamFirstHit (raw : Fin T → Fin n) (w : Fin n) : ℕ := by
  classical
  exact Nat.find (exists_streamHit raw w)

private theorem streamFirstHit_spec (raw : Fin T → Fin n) (w : Fin n) :
    IsStreamHit raw w (streamFirstHit raw w) := by
  classical
  exact Nat.find_spec (exists_streamHit raw w)

private theorem streamFirstHit_le (raw : Fin T → Fin n) (w : Fin n) {k : ℕ}
    (hk : IsStreamHit raw w k) : streamFirstHit raw w ≤ k := by
  classical
  exact Nat.find_min' (exists_streamHit raw w) hk

/-- A receiver is seen before a cutoff exactly when its first hit precedes the cutoff. -/
theorem streamFirstHit_lt_iff (raw : Fin T → Fin n) (w : Fin n) {k : ℕ} (hk : k ≤ T) :
    streamFirstHit raw w < k ↔ ∃ j : Fin T, j.val < k ∧ raw j = w := by
  constructor
  · intro h
    rcases streamFirstHit_spec raw w with hT | ⟨j, hj, hw⟩
    · omega
    · exact ⟨j, hj ▸ h, hw⟩
  · rintro ⟨j, hj, hw⟩
    exact (streamFirstHit_le raw w (Or.inr ⟨j, rfl, hw⟩)).trans_lt hj

/-- A fresh draw occurs at its own first-hit index. -/
theorem streamFirstHit_fresh (raw : Fin T → Fin n) (i : Fin T)
    (hfresh : ∀ j : Fin T, j < i → raw j ≠ raw i) :
    streamFirstHit raw (raw i) = i.val := by
  apply le_antisymm (streamFirstHit_le raw (raw i) (Or.inr ⟨i, rfl, rfl⟩))
  by_contra! h
  obtain ⟨j, hj, heq⟩ := (streamFirstHit_lt_iff raw (raw i) i.isLt.le).1 h
  exact hfresh j hj heq

private noncomputable def streamKey (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n))
    (w : Fin n) : ℕ :=
  streamFirstHit raw w * (n + 1) + (fallback w).val

private theorem streamKey_lt_of_firstHit_lt (raw : Fin T → Fin n)
    (fallback : Equiv.Perm (Fin n)) {w u : Fin n}
    (h : streamFirstHit raw w < streamFirstHit raw u) :
    streamKey raw fallback w < streamKey raw fallback u := by
  have hmul := Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at hmul
  have hw := (fallback w).isLt
  unfold streamKey
  omega

private theorem streamKey_injective (raw : Fin T → Fin n)
    (fallback : Equiv.Perm (Fin n)) : Injective (streamKey raw fallback) := by
  intro w u h
  have hfirst : streamFirstHit raw w = streamFirstHit raw u :=
    le_antisymm (le_of_not_gt fun h' ↦
      (streamKey_lt_of_firstHit_lt raw fallback h').ne h.symm)
      (le_of_not_gt fun h' ↦ (streamKey_lt_of_firstHit_lt raw fallback h').ne h)
  apply fallback.injective
  apply Fin.ext
  simpa only [streamKey, hfirst, Nat.add_left_cancel_iff] using h

/-- Complete a proposal stream by putting first appearances first and breaking remaining
ties using a fallback ranking. -/
@[no_expose]
noncomputable def streamRank (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  rankPermutation fun w ↦ (streamKey raw fallback w : ℝ)

private theorem streamRank_lt_iff (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n))
    (w u : Fin n) :
    streamRank raw fallback w < streamRank raw fallback u ↔
      streamKey raw fallback w < streamKey raw fallback u := by
  have hinj : Injective (fun w ↦ (streamKey raw fallback w : ℝ)) :=
    (Nat.cast_injective (R := ℝ)).comp (streamKey_injective raw fallback)
  exact (rankPermutation_lt_iff hinj w u).trans Nat.cast_lt

/-- The ranks preceding a fresh draw are precisely the receivers already drawn. -/
theorem streamRank_lt_fresh_iff (raw : Fin T → Fin n) (fallback : Equiv.Perm (Fin n))
    (i : Fin T) (hfresh : ∀ j : Fin T, j < i → raw j ≠ raw i) (w : Fin n) :
    streamRank raw fallback w < streamRank raw fallback (raw i) ↔
      ∃ j : Fin T, j < i ∧ raw j = w := by
  have hi := streamFirstHit_fresh raw i hfresh
  change streamRank raw fallback w < streamRank raw fallback (raw i) ↔
    ∃ j : Fin T, j.val < i.val ∧ raw j = w
  rw [streamRank_lt_iff, ← streamFirstHit_lt_iff raw w i.isLt.le]
  constructor
  · intro h
    rcases lt_trichotomy (streamFirstHit raw w) i.val with hlt | heq | hgt
    · exact hlt
    · rcases streamFirstHit_spec raw w with hT | ⟨j, hj, hw⟩
      · omega
      · have hji : j = i := Fin.ext (hj.trans heq)
        exact (h.ne (by rw [← hw, hji])).elim
    · exact (lt_asymm h (streamKey_lt_of_firstHit_lt raw fallback (hi ▸ hgt))).elim
  · intro h
    exact streamKey_lt_of_firstHit_lt raw fallback (hi.symm ▸ h)

private theorem streamFirstHit_relabel (raw : Fin T → Fin n) (e : Equiv.Perm (Fin n))
    (w : Fin n) :
    streamFirstHit (fun i ↦ e.symm (raw i)) w = streamFirstHit raw (e w) := by
  have h (k : ℕ) : IsStreamHit (fun i ↦ e.symm (raw i)) w k ↔
      IsStreamHit raw (e w) k := by
    simp [IsStreamHit, Equiv.symm_apply_eq]
  exact le_antisymm
    (streamFirstHit_le _ _ ((h _).mpr (streamFirstHit_spec raw (e w))))
    (streamFirstHit_le _ _ ((h _).mp (streamFirstHit_spec _ w)))

/-- Relabeling the receivers in both inputs relabels the completed ranking. -/
theorem streamRank_relabel (raw : Fin T → Fin n) (fallback e : Equiv.Perm (Fin n)) :
    streamRank (fun i ↦ e.symm (raw i)) (e.trans fallback) =
      e.trans (streamRank raw fallback) := by
  let p := streamRank (fun i ↦ e.symm (raw i)) (e.trans fallback)
  let q := e.trans (streamRank raw fallback)
  have hcmp (i j : Fin n) : p i < p j ↔ q i < q j := by
    change streamRank _ _ i < streamRank _ _ j ↔
      streamRank raw fallback (e i) < streamRank raw fallback (e j)
    simp only [streamRank_lt_iff, streamKey, streamFirstHit_relabel, Equiv.trans_apply]
  have hmono : StrictMono (q ∘ p.symm) := fun i j hij ↦
    (hcmp (p.symm i) (p.symm j)).mp (by simpa using hij)
  apply Equiv.ext
  intro i
  change p i = q i
  simpa only [id_eq, Function.comp_apply, Equiv.symm_apply_apply] using
    (hmono.id_le (p i)).antisymm (hmono.le_id (p i))

private theorem uniformOfFintype_equiv_preserving {α : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (e : Equiv.Perm α) :
    MeasurePreserving e (PMF.fintypeUniform α).toMeasure (PMF.fintypeUniform α).toMeasure := by
  have hm : Measurable e := measurable_of_countable _
  refine ⟨hm, Measure.ext_of_singleton fun a ↦ ?_⟩
  have he : e ⁻¹' ({a} : Set α) = {e.symm a} := by
    ext x
    change e x = a ↔ x = e.symm a
    exact e.eq_symm_apply.symm
  rw [Measure.map_apply hm (measurableSet_singleton a), he,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (e.symm a)),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  simp

/-- Independent uniform draws and an independent uniform fallback give a uniform ranking. -/
theorem measurePreserving_streamRank [Nonempty (Fin n)]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))] :
    MeasurePreserving (fun z : (Fin T → Fin n) × Equiv.Perm (Fin n) ↦ streamRank z.1 z.2)
      ((Measure.pi fun _ : Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure).prod
        (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure)
      (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure := by
  let law := (Measure.pi fun _ : Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure).prod
    (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure
  let rank := fun z : (Fin T → Fin n) × Equiv.Perm (Fin n) ↦ streamRank z.1 z.2
  have hr : Measurable rank := measurable_of_countable _
  let ν := law.map rank
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (law.map rank))
  have hequal (p q : Equiv.Perm (Fin n)) : ν {p} = ν {q} := by
    let e : Equiv.Perm (Fin n) := q.trans p.symm
    let precompose : Equiv.Perm (Equiv.Perm (Fin n)) :=
      ⟨e.trans, e.symm.trans, fun u ↦ Equiv.ext fun i ↦ by
        change u (e (e.symm i)) = u i
        rw [e.apply_symm_apply], fun u ↦ Equiv.ext fun i ↦ by
        change u (e.symm (e i)) = u i
        rw [e.symm_apply_apply]⟩
    let reindex := Prod.map (fun raw : Fin T → Fin n ↦ fun i ↦ e.symm (raw i)) precompose
    have hm : MeasurePreserving reindex law law :=
      (measurePreserving_pi _ _ (fun _ : Fin T ↦ uniformOfFintype_equiv_preserving e.symm)).prod
        (uniformOfFintype_equiv_preserving precompose)
    have hcongr : rank ⁻¹' ({p} : Set (Equiv.Perm (Fin n))) =
        reindex ⁻¹' (rank ⁻¹' {q}) := by
      ext z
      change (rank z = p) ↔ rank (reindex z) = q
      change (streamRank z.1 z.2 = p) ↔
        streamRank (fun i ↦ e.symm (z.1 i)) (e.trans z.2) = q
      rw [streamRank_relabel]
      constructor
      · rintro rfl
        simp [e, Equiv.trans_assoc]
      · intro h
        apply Equiv.ext
        intro i
        have hi := DFunLike.congr_fun h (e.symm i)
        simpa [e] using hi
    change law.map rank {p} = law.map rank {q}
    rw [Measure.map_apply hr (measurableSet_singleton p),
      Measure.map_apply hr (measurableSet_singleton q), hcongr]
    exact hm.measure_preimage (hr (measurableSet_singleton q)).nullMeasurableSet
  refine ⟨hr, Measure.ext_of_singleton fun p ↦ ?_⟩
  have hsum : ν {p} * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑' q : Equiv.Perm (Fin n), ν {q} := by
        rw [tsum_fintype, Finset.sum_congr rfl (fun q _ ↦ hequal q p), Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ = 1 := by simpa only [Measure.toPMF_apply] using ν.toPMF.tsum_coe
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.fintypeUniform_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum

/-- Rebracket independent finite arrays so that each row is paired with its fallback. -/
private theorem measurePreserving_pairRows {ι α β : Type*} [Fintype ι] [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : (ι → α) × (ι → β) ↦ fun i ↦ (z.1 i, z.2 i))
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ ν))
      (Measure.pi fun _ : ι ↦ μ.prod ν) := by
  let f := fun z : (ι → α) × (ι → β) ↦ fun i ↦ (z.1 i, z.2 i)
  have hf : Measurable f := measurable_of_countable _
  refine ⟨hf, Measure.ext_of_singleton fun a ↦ ?_⟩
  have hpre : f ⁻¹' ({a} : Set (ι → α × β)) =
      {fun i ↦ (a i).1} ×ˢ {fun i ↦ (a i).2} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, funext_iff,
      Prod.ext_iff, f, forall_and]
  rw [Measure.map_apply hf (measurableSet_singleton a), hpre, Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton, Measure.pi_singleton, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by
    rw [← Measure.prod_prod, Set.singleton_prod_singleton]

/-- Currying a finite iid array preserves the independent row law. -/
theorem measurePreserving_curry_iid {ι κ α : Type*} [Fintype ι] [Fintype κ] [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (Equiv.curry ι κ α)
      (Measure.pi fun _ : ι × κ ↦ μ)
      (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ) := by
  let e := Equiv.curry ι κ α
  have he : Measurable e := measurable_of_countable _
  refine ⟨he, Measure.ext_of_singleton fun a ↦ ?_⟩
  have hpre : e ⁻¹' ({a} : Set (ι → κ → α)) = {e.symm a} := by
    ext x
    change e x = a ↔ x = e.symm a
    exact e.eq_symm_apply.symm
  rw [Measure.map_apply he (measurableSet_singleton a), hpre, Measure.pi_singleton,
    Measure.pi_singleton]
  simp only [Measure.pi_singleton, e, Equiv.curry_symm_apply, Function.uncurry,
    ← Finset.univ_product_univ, Finset.prod_product]

/-- Completing independent rows against independent fallback rows gives independent
uniform permutations. -/
theorem measurePreserving_streamRankRows {ι : Type*} [Fintype ι] [Nonempty (Fin n)]
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))] :
    MeasurePreserving
      (fun z : (ι → Fin T → Fin n) × (ι → Equiv.Perm (Fin n)) ↦
        fun i ↦ streamRank (z.1 i) (z.2 i))
      ((Measure.pi fun _ : ι ↦ Measure.pi fun _ : Fin T ↦
        (PMF.fintypeUniform (Fin n)).toMeasure).prod
          (Measure.pi fun _ : ι ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure))
      (Measure.pi fun _ : ι ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure) := by
  let rawLaw : Measure (Fin T → Fin n) :=
    Measure.pi fun _ : Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure
  let permLaw : Measure (Equiv.Perm (Fin n)) :=
    (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure rawLaw := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  have : IsProbabilityMeasure permLaw :=
    inferInstanceAs (IsProbabilityMeasure (PMF.fintypeUniform _).toMeasure)
  have h := measurePreserving_pi (fun _ : ι ↦ rawLaw.prod permLaw) (fun _ ↦ permLaw)
    (fun _ ↦ measurePreserving_streamRank (n := n) (T := T))
  have hpair := measurePreserving_pairRows (ι := ι) rawLaw permLaw
  have hc := h.comp hpair
  change MeasurePreserving _ ((Measure.pi fun _ : ι ↦ rawLaw).prod
    (Measure.pi fun _ : ι ↦ permLaw)) (Measure.pi fun _ : ι ↦ permLaw)
  exact hc

private theorem measurePreserving_profileOfRankPairs (n : ℕ) :
    MeasurePreserving
      (fun z : (Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)) ↦
        (⟨z.1, z.2⟩ : StableMarriage.Profile n))
      ((Measure.pi fun _ : Fin n ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure).prod
        (Measure.pi fun _ : Fin n ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure))
      (StableMarriage.uniformProfile n).toMeasure := by
  let e : ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))) ≃
      StableMarriage.Profile n :=
    ⟨fun z ↦ ⟨z.1, z.2⟩, fun p ↦ (p.manRank, p.womanRank), fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hm : Measurable e := measurable_of_countable _
  refine ⟨hm, Measure.ext_of_singleton fun p ↦ ?_⟩
  have hpre : e ⁻¹' ({p} : Set (StableMarriage.Profile n)) = {p.manRank} ×ˢ {p.womanRank} := by
    rw [Set.singleton_prod_singleton]
    ext z
    change e z = p ↔ z = e.symm p
    exact e.eq_symm_apply.symm
  change Measure.map e _ {p} = _
  rw [Measure.map_apply hm (measurableSet_singleton p), hpre, Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton, StableMarriage.uniformProfile,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.fintypeUniform_apply]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.fintypeUniform_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, ← pow_add, ENNReal.inv_pow]

/-- A flat independent proposal table, independent fallback rankings, and independent
receiver rankings give the uniform law on complete preference profiles. -/
theorem measurePreserving_streamProfile [Nonempty (Fin n)] :
    MeasurePreserving
      (fun z : (Fin n × Fin T → Fin n) × (Fin n → Equiv.Perm (Fin n)) ×
          (Fin n → Equiv.Perm (Fin n)) ↦
        (⟨fun m ↦ streamRank (fun j ↦ z.1 (m, j)) (z.2.1 m), z.2.2⟩ :
          StableMarriage.Profile n))
      ((Measure.pi fun _ : Fin n × Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure).prod
        ((Measure.pi fun _ : Fin n ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure).prod
          (Measure.pi fun _ : Fin n ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure)))
      (StableMarriage.uniformProfile n).toMeasure := by
  let rawLaw : Measure (Fin n × Fin T → Fin n) :=
    Measure.pi fun _ : Fin n × Fin T ↦ (PMF.fintypeUniform (Fin n)).toMeasure
  let permRows : Measure (Fin n → Equiv.Perm (Fin n)) :=
    Measure.pi fun _ : Fin n ↦ (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure permRows := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  have hcur := measurePreserving_curry_iid (ι := Fin n) (κ := Fin T)
    (PMF.fintypeUniform (Fin n)).toMeasure
  have hman := (measurePreserving_streamRankRows (ι := Fin n) (n := n) (T := T)).comp
    (hcur.prod (MeasurePreserving.id permRows))
  exact (measurePreserving_profileOfRankPairs n).comp
    ((hman.prod (MeasurePreserving.id permRows)).comp
      (measurePreserving_prodAssoc rawLaw permRows permRows).symm)

end LennonPittelFormalization

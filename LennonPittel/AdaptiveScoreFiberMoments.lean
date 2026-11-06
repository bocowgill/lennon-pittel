module

public import LennonPittel.AdaptiveScoreRectangles
public import LennonPittel.UniformLogScoreMoments
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Log moments on measurable cache fibers

Fix a structural branch of a score query history. Split off the selected,
still hidden coordinates; all other coordinates can be included in the first
factor. A measurable event in that factor and positive, history-dependent
upper cutoffs determine the branch. Rescaling the selected scores gives a
product law with the original first marginal. In particular, no conditioning
on a singleton value of a previously observed real score is needed.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory

namespace LennonPittelFormalization

section Fiber

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- If a measurable transformation has the same normalized output law on every
restricted fiber, the joint output law factors with the actual first marginal. -/
theorem measurePreserving_prod_restrict_of_map_fiber (μ : Measure α) [IsFiniteMeasure μ]
    (ν : Measure β) [IsFiniteMeasure ν] (η : Measure γ) [IsProbabilityMeasure η]
    (E : Set (α × β)) (hE : MeasurableSet E) (g : α × β → γ) (hg : Measurable g)
    (hfiber : ∀ a, Measure.map (fun b ↦ g (a, b)) (ν.restrict (Prod.mk a ⁻¹' E)) =
      ν (Prod.mk a ⁻¹' E) • η) :
    MeasurePreserving (fun z ↦ (z.1, g z)) ((μ.prod ν).restrict E)
      ((Measure.map Prod.fst ((μ.prod ν).restrict E)).prod η) := by
  have hmap := measurable_fst.prodMk hg
  refine ⟨hmap, ?_⟩
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply hmap (hs.prod ht),
    Measure.restrict_apply (hmap (hs.prod ht)),
    Measure.map_apply measurable_fst hs, Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((hmap (hs.prod ht)).inter hE),
    Measure.prod_apply ((measurable_fst hs).inter hE),
    ← lintegral_mul_const' (η t) _ (measure_ne_top η t)]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ s
  · have hmeas : Measurable (fun b ↦ g (a, b)) := hg.comp measurable_prodMk_left
    have ht' : (Prod.mk a ⁻¹' ((fun z : α × β ↦ (z.1, g z)) ⁻¹' (s ×ˢ t) ∩ E)) =
        (fun b ↦ g (a, b)) ⁻¹' t ∩ (Prod.mk a ⁻¹' E) := by
      ext b
      simp [ha]
    have hs' : (Prod.mk a ⁻¹' (Prod.fst ⁻¹' s ∩ E)) = Prod.mk a ⁻¹' E := by
      ext b
      simp [ha]
    rw [ht', hs', ← Measure.restrict_apply (hmeas ht), ← Measure.map_apply hmeas ht,
      hfiber a, Measure.smul_apply, smul_eq_mul]
  · have ht' : (Prod.mk a ⁻¹' ((fun z : α × β ↦ (z.1, g z)) ⁻¹' (s ×ˢ t) ∩ E)) = ∅ := by
      ext b
      simp [ha]
    have hs' : (Prod.mk a ⁻¹' (Prod.fst ⁻¹' s ∩ E)) = ∅ := by
      ext b
      simp [ha]
    simp [ht', hs']

end Fiber

section Cache

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

local notation "unitScorePi" => Measure.pi (fun _ : ι ↦ unitScoreLaw)

/-- The branch with specified information in the first factor and passing scores
in the second. The selected coordinates are indexed by `ι`. -/
def scoreCacheFiberEvent (A : Set α) (upper : α → ι → ℝ) : Set (α × (ι → ℝ)) :=
  {z | z.1 ∈ A ∧ ∀ i, z.2 i ∈ Ioo 0 (upper z.1 i)}

theorem measurableSet_scoreCacheFiberEvent (A : Set α) (hA : MeasurableSet A)
    (upper : α → ι → ℝ) (hu : ∀ i, Measurable (fun a ↦ upper a i)) :
    MeasurableSet (scoreCacheFiberEvent A upper) := by
  have he (i : ι) : Measurable (fun z : α × (ι → ℝ) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have heq : scoreCacheFiberEvent A upper = Prod.fst ⁻¹' A ∩ ⋂ i,
      {z : α × (ι → ℝ) | z.2 i ∈ Ioo 0 (upper z.1 i)} := by
    ext z
    simp [scoreCacheFiberEvent]
  rw [heq]
  exact (measurable_fst hA).inter (MeasurableSet.iInter fun i ↦
    (measurableSet_lt measurable_const (he i)).inter
      (measurableSet_lt (he i) ((hu i).comp measurable_fst)))

private theorem unitScoreLaw_restrict_Ioo {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    unitScoreLaw.restrict (Ioo 0 u) = ENNReal.ofReal u • cachedUniformScoreLaw u := by
  have hsub : Ioo (0 : ℝ) u ⊆ Icc 0 1 :=
    fun _ hx ↦ ⟨hx.1.le, hx.2.le.trans hu₁⟩
  rw [unitScoreLaw, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub, cachedUniformScoreLaw, smul_smul,
    ENNReal.mul_inv_cancel (by simpa using hu) ENNReal.ofReal_ne_top, one_smul]

/-- On a measurable branch with history-dependent passing cutoffs, the normalized
hidden scores have the iid uniform law, independently of the entire first factor. -/
theorem measurePreserving_normalize_scoreCacheFiber (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (upper : α → ι → ℝ)
    (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a ∈ A, ∀ i, 0 < upper a i ∧ upper a i ≤ 1) :
    MeasurePreserving (fun z : α × (ι → ℝ) ↦ (z.1, fun i ↦ z.2 i / upper z.1 i))
      ((μ.prod unitScorePi).restrict (scoreCacheFiberEvent A upper))
      ((Measure.map Prod.fst ((μ.prod unitScorePi).restrict
        (scoreCacheFiberEvent A upper))).prod unitScorePi) := by
  have hg : Measurable (fun (z : α × (ι → ℝ)) i ↦ z.2 i / upper z.1 i) :=
    Measurable.of_eval fun i ↦
      ((measurable_pi_apply i).comp measurable_snd).div ((hu i).comp measurable_fst)
  apply measurePreserving_prod_restrict_of_map_fiber _ _ _ _
    (measurableSet_scoreCacheFiberEvent A hA upper hu) _ hg
  intro a
  by_cases ha : a ∈ A
  · have hbox : Prod.mk a ⁻¹' scoreCacheFiberEvent A upper =
        univ.pi (fun i ↦ Ioo 0 (upper a i)) := by
      ext z
      simp [scoreCacheFiberEvent, ha]
    have hpos (i : ι) := (hcut a ha i).1
    have hscale (i : ι) : unitScoreLaw (Ioo 0 (upper a i)) = ENNReal.ofReal (upper a i) := by
      rw [← Measure.restrict_apply_univ, unitScoreLaw_restrict_Ioo (hpos i) (hcut a ha i).2,
        Measure.smul_apply, smul_eq_mul]
      have := isProbabilityMeasure_cachedUniformScoreLaw (hpos i)
      simp
    rw [hbox, Measure.restrict_pi_pi, Measure.pi_pi]
    simp_rw [unitScoreLaw_restrict_Ioo (hpos _) (hcut a ha _).2, hscale]
    have (i : ι) := isProbabilityMeasure_cachedUniformScoreLaw (hpos i)
    have hnormalize := measurePreserving_normalize_cachedUniformScoreLaw (upper a) hpos
    rw [pi_smul_coordinates _ _ (fun _ ↦ ENNReal.ofReal_ne_top),
      Measure.map_smul _ hnormalize.measurable.aemeasurable, hnormalize.map_eq]
  · have hempty : Prod.mk a ⁻¹' scoreCacheFiberEvent A upper = ∅ := by
      ext z
      simp [scoreCacheFiberEvent, ha]
    simp [hempty]

/-- The centered logarithmic increment from revealing the selected scores. -/
noncomputable def centeredCacheLogIncrement (upper : α → ι → ℝ)
    (z : α × (ι → ℝ)) : ℝ :=
  ∑ i, (-Real.log (z.2 i / upper z.1 i) - 1)

set_option maxHeartbeats 450000 in
/-- The centered increment on the history branch is square-integrable and has
zero integral. Its squared integral is the branch mass times the number of
revealed scores. The same assertion applies after any measurable refinement
of the first-factor event. -/
theorem scoreCacheFiber_logMoments (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (upper : α → ι → ℝ)
    (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a ∈ A, ∀ i, 0 < upper a i ∧ upper a i ≤ 1) :
    let E := scoreCacheFiberEvent A upper
    let L := centeredCacheLogIncrement upper
    MemLp L 2 ((μ.prod unitScorePi).restrict E) ∧
      (∫ z in E, L z ∂(μ.prod unitScorePi)) = 0 ∧
      (∫ z in E, (L z) ^ 2 ∂(μ.prod unitScorePi)) =
        (Fintype.card ι : ℝ) * (μ.prod unitScorePi).real E := by
  let E := scoreCacheFiberEvent A upper
  let ν := (μ.prod unitScorePi).restrict E
  let ρ := Measure.map Prod.fst ν
  let T (z : α × (ι → ℝ)) := (z.1, fun i ↦ z.2 i / upper z.1 i)
  let L₀ (z : ι → ℝ) := ∑ i, (-Real.log (z i) - 1)
  have hT : MeasurePreserving T ν (ρ.prod unitScorePi) :=
    measurePreserving_normalize_scoreCacheFiber μ A hA upper hu hcut
  have hL₀ : MemLp L₀ 2 unitScorePi :=
    memLp_two_sum_centeredNegLog_unitScoreLaw_pi Finset.univ
  have h₁ : (∫ z, L₀ z ∂unitScorePi) = 0 :=
    integral_sum_centeredNegLog_unitScoreLaw_pi Finset.univ
  have h₂ : (∫ z, (L₀ z) ^ 2 ∂unitScorePi) = (Fintype.card ι : ℝ) := by
    simpa only [Finset.card_univ] using integral_sq_sum_centeredNegLog_unitScoreLaw_pi
      (Finset.univ : Finset ι)
  have hρ : ρ.real univ = (μ.prod unitScorePi).real E := by
    simp [ρ, ν, measureReal_def, Measure.map_apply measurable_fst]
  have hL : MemLp (fun z : α × (ι → ℝ) ↦ L₀ z.2) 2 (ρ.prod unitScorePi) :=
    hL₀.comp_snd ρ
  have hint (f : (ι → ℝ) → ℝ) (hf : Integrable f unitScorePi) :
      (∫ z, f (T z).2 ∂ν) = ρ.real univ * (∫ z, f z ∂unitScorePi) := by
    have hprod := hf.comp_snd ρ
    have hmap : (∫ z, f z.2 ∂Measure.map T ν) = (∫ z, f (T z).2 ∂ν) :=
      integral_map hT.measurable.aemeasurable (hT.map_eq ▸ hprod.aestronglyMeasurable)
    rw [← hmap, hT.map_eq, integral_prod _ hprod]
    change (∫ _ : α, ∫ y, f y ∂unitScorePi ∂ρ) = _
    rw [integral_const, smul_eq_mul]
  change MemLp (centeredCacheLogIncrement upper) 2 ν ∧
    (∫ z, centeredCacheLogIncrement upper z ∂ν) = 0 ∧
    (∫ z, (centeredCacheLogIncrement upper z) ^ 2 ∂ν) =
      (Fintype.card ι : ℝ) * (μ.prod unitScorePi).real E
  have hLT := hL.comp_measurePreserving hT
  refine ⟨hLT, ?_, ?_⟩
  · change (∫ z, L₀ (T z).2 ∂ν) = 0
    rw [hint _ (hL₀.integrable (by norm_num)), h₁, mul_zero]
  · change (∫ z, (L₀ (T z).2) ^ 2 ∂ν) = _
    rw [hint _ hL₀.integrable_sq, h₂, hρ, mul_comm]

/-- Under the branch measure, the conditional mean and second moment given
the whole first factor are zero and the number of revealed scores. -/
theorem scoreCacheFiber_condExp_logMoments (μ : Measure α) [IsFiniteMeasure μ]
    (A : Set α) (hA : MeasurableSet A) (upper : α → ι → ℝ)
    (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a ∈ A, ∀ i, 0 < upper a i ∧ upper a i ≤ 1) :
    let ν := (μ.prod unitScorePi).restrict (scoreCacheFiberEvent A upper)
    let L := centeredCacheLogIncrement upper
    let m := MeasurableSpace.comap (Prod.fst : α × (ι → ℝ) → α) ‹MeasurableSpace α›
    ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (Fintype.card ι : ℝ)) := by
  let ν := (μ.prod unitScorePi).restrict (scoreCacheFiberEvent A upper)
  let L := centeredCacheLogIncrement upper
  let m := MeasurableSpace.comap (Prod.fst : α × (ι → ℝ) → α) ‹MeasurableSpace α›
  have hm : m ≤ MeasurableSpace.prod ‹MeasurableSpace α› (inferInstance :
      MeasurableSpace (ι → ℝ)) := measurable_fst.comap_le
  have hl : MemLp L 2 ν := (scoreCacheFiber_logMoments μ A hA upper hu hcut).1
  have hrefine (B : Set α) (hB : MeasurableSet B) :
      ν.restrict (Prod.fst ⁻¹' B) =
        (μ.prod unitScorePi).restrict (scoreCacheFiberEvent (B ∩ A) upper) := by
    dsimp only [ν]
    rw [Measure.restrict_restrict (measurable_fst hB)]
    congr 1
    ext z
    simp only [scoreCacheFiberEvent, mem_inter_iff, mem_preimage, mem_ofPred_eq, and_assoc]
  have hmass (B : Set α) (hB : MeasurableSet B) :
      ν.real (Prod.fst ⁻¹' B) = (μ.prod unitScorePi).real (scoreCacheFiberEvent (B ∩ A) upper) := by
    rw [measureReal_def, measureReal_def,
      ← Measure.restrict_apply_univ (μ := ν) (Prod.fst ⁻¹' B), hrefine B hB,
      Measure.restrict_apply_univ]
  change ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
    ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (Fintype.card ι : ℝ))
  constructor
  · symm
    refine ae_eq_condExp_of_forall_setIntegral_eq hm (hl.integrable (by norm_num))
      (fun _ _ _ ↦ (integrable_const _).integrableOn) ?_
      stronglyMeasurable_const.aestronglyMeasurable
    rintro s ⟨B, hB, rfl⟩ _
    rw [integral_zero, hrefine B hB]
    exact (scoreCacheFiber_logMoments μ (B ∩ A) (hB.inter hA) upper hu
      (fun a ha ↦ hcut a ha.2)).2.1.symm
  · symm
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hl.integrable_sq
      (fun _ _ _ ↦ (integrable_const _).integrableOn) ?_
      stronglyMeasurable_const.aestronglyMeasurable
    rintro s ⟨B, hB, rfl⟩ _
    rw [setIntegral_const, smul_eq_mul, hmass B hB, mul_comm]
    change _ = ∫ z, (L z) ^ 2 ∂ν.restrict (Prod.fst ⁻¹' B)
    rw [hrefine B hB]
    exact (scoreCacheFiber_logMoments μ (B ∩ A) (hB.inter hA) upper hu
      (fun a ha ↦ hcut a ha.2)).2.2.symm

end Cache

end LennonPittelFormalization

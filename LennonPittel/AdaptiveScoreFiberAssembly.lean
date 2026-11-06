module

public import LennonPittel.AdaptiveScoreFiberMoments

/-!
# From exact replay to the passing-box law

A fixed structural branch can be compared between two completions of the
same complementary scores. If, whenever the branch is attained, its fiber
consists exactly of the passing completions, its positive-mass fibers
define a measurable first-factor event. This avoids choosing a measurable
representative completion for every attainable history.
-/

@[expose] public section

open MeasureTheory Set

namespace LennonPittelFormalization

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

local notation "unitScorePi" => Measure.pi (fun _ : ι ↦ unitScoreLaw)

/-- Complementary observations for which the branch has positive fiber mass. -/
def scoreBranchBase (E : Set (α × (ι → ℝ))) : Set α :=
  {a | 0 < unitScorePi (Prod.mk a ⁻¹' E)}

theorem measurableSet_scoreBranchBase {E : Set (α × (ι → ℝ))} (hE : MeasurableSet E) :
    MeasurableSet (scoreBranchBase E) :=
  measurableSet_lt measurable_const (measurable_measure_prodMk_left hE)

omit [MeasurableSpace α] in
private theorem nonempty_fiber_of_mem_scoreBranchBase {E : Set (α × (ι → ℝ))} {a : α}
    (ha : a ∈ scoreBranchBase E) : (Prod.mk a ⁻¹' E).Nonempty := by
  by_contra! hnone
  have hpos : 0 < unitScorePi (Prod.mk a ⁻¹' E) := ha
  rw [hnone, measure_empty] at hpos
  exact lt_irrefl _ hpos

/-- An almost-sure replay equivalence gives an almost-sure passing-box event. -/
theorem ae_eq_scoreCacheFiberEvent_of_replay (μ : Measure α) [IsFiniteMeasure μ]
    {E G : Set (α × (ι → ℝ))} (hE : MeasurableSet E) (hG : MeasurableSet G)
    (hgood : ∀ᵐ z ∂μ.prod unitScorePi, z ∈ G)
    (upper : α → ι → ℝ) (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hreplay : ∀ a u, (a, u) ∈ E → ∀ v, (a, v) ∈ G →
      ((a, v) ∈ E ↔ ∀ i, v i ∈ Ioo 0 (upper a i))) :
    E =ᵐ[μ.prod unitScorePi] scoreCacheFiberEvent (scoreBranchBase E) upper := by
  have hbox := measurableSet_scoreCacheFiberEvent _ (measurableSet_scoreBranchBase hE) upper hu
  have heq :
      MeasurableSet {z | z ∈ E ↔ z ∈ scoreCacheFiberEvent (scoreBranchBase E) upper} := by
    rw [show {z | z ∈ E ↔ z ∈ scoreCacheFiberEvent (scoreBranchBase E) upper} =
      (E ∩ scoreCacheFiberEvent (scoreBranchBase E) upper) ∪
        (Eᶜ ∩ (scoreCacheFiberEvent (scoreBranchBase E) upper)ᶜ) by
      ext z
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto]
    exact (hE.inter hbox).union (hE.compl.inter hbox.compl)
  have hg := (Measure.ae_prod_iff_ae_ae hG).mp hgood
  apply Filter.Eventually.set_eq
  apply (Measure.ae_prod_iff_ae_ae heq).mpr
  filter_upwards [hg] with a ha
  by_cases hb : a ∈ scoreBranchBase E
  · obtain ⟨u, huE⟩ := nonempty_fiber_of_mem_scoreBranchBase hb
    filter_upwards [ha] with v hv
    simpa only [scoreCacheFiberEvent, mem_ofPred_eq, hb, true_and] using hreplay a u huE v hv
  · have hzero : unitScorePi (Prod.mk a ⁻¹' E) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hb)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with v hv
    simp only [scoreCacheFiberEvent, mem_ofPred_eq, hb, false_and, iff_false]
    exact hv

/-- On a replayable branch, exact conditional moments hold given all
complementary coordinates, without defining conditional laws at null points. -/
theorem scoreBranch_condExp_logMoments_of_replay (μ : Measure α) [IsFiniteMeasure μ]
    {E G : Set (α × (ι → ℝ))} (hE : MeasurableSet E) (hG : MeasurableSet G)
    (hgood : ∀ᵐ z ∂μ.prod unitScorePi, z ∈ G)
    (upper : α → ι → ℝ) (hu : ∀ i, Measurable (fun a ↦ upper a i))
    (hcut : ∀ a v, (a, v) ∈ E → ∀ i, 0 < upper a i ∧ upper a i ≤ 1)
    (hreplay : ∀ a u, (a, u) ∈ E → ∀ v, (a, v) ∈ G →
      ((a, v) ∈ E ↔ ∀ i, v i ∈ Ioo 0 (upper a i))) :
    let ν := (μ.prod unitScorePi).restrict E
    let L := centeredCacheLogIncrement upper
    let m := MeasurableSpace.comap (Prod.fst : α × (ι → ℝ) → α) ‹MeasurableSpace α›
    MemLp L 2 ν ∧ ν[L | m] =ᵐ[ν] (fun _ ↦ 0) ∧
      ν[(fun z ↦ (L z) ^ 2) | m] =ᵐ[ν] (fun _ ↦ (Fintype.card ι : ℝ)) := by
  have he := ae_eq_scoreCacheFiberEvent_of_replay μ hE hG hgood upper hu hreplay
  have hb : ∀ a ∈ scoreBranchBase E, ∀ i, 0 < upper a i ∧ upper a i ≤ 1 := by
    intro a ha
    obtain ⟨v, hv⟩ := nonempty_fiber_of_mem_scoreBranchBase ha
    exact hcut a v hv
  dsimp only
  rw [Measure.restrict_congr_set he]
  exact ⟨(scoreCacheFiber_logMoments μ _ (measurableSet_scoreBranchBase hE) upper hu hb).1,
    scoreCacheFiber_condExp_logMoments μ _ (measurableSet_scoreBranchBase hE) upper hu hb⟩

end LennonPittelFormalization

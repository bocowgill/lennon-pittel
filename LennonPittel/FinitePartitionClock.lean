module

public import LennonPittel.ParticipationClockMartingale

/-!
# Assembling conditional moments over a finite partition

The partition may include information discovered just before the step.
It need not belong to the earlier filtration. Each past-measurable event
is cut by the partition, and its branch integrals are summed.
-/

@[expose] public section

open MeasureTheory Set
open scoped Function

namespace LennonPittelFormalization

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]

/-- Square integrability, centering and energy assemble from a finite disjoint
partition. The centered identities are tested against the earlier sigma-algebra. -/
theorem clock_moments_of_fintype_partition (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {d l : Ω → ℝ}
    (hd : Measurable[mΩ] d) (hl : Integrable l μ) {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet[mΩ] (B i)) (hdisj : Pairwise (Disjoint on B))
    (hcover : (⋃ i, B i) = univ) (hLp : ∀ i, MemLp d 2 (μ.restrict (B i)))
    (hmean : ∀ i A, MeasurableSet[m] A → (∫ x in B i ∩ A, d x ∂μ) = 0)
    (henergy : ∀ i, (∫ x in B i, (d x)^2 ∂μ) = ∫ x in B i, l x ∂μ) :
    MemLp d 2 μ ∧ μ[d | m] =ᵐ[μ] 0 ∧
      (∫ x, (d x)^2 ∂μ) = ∫ x, l x ∂μ := by
  have hsq (i : ι) : IntegrableOn (fun x ↦ (d x)^2) (B i) μ := (hLp i).integrable_sq
  have hwholeSq : Integrable (fun x ↦ (d x)^2) μ := by
    rw [← integrableOn_univ, ← hcover, integrableOn_finite_iUnion]
    exact hsq
  have hdm : AEStronglyMeasurable[mΩ] d μ := hd.aestronglyMeasurable
  have hL : MemLp d 2 μ := (memLp_two_iff_integrable_sq hdm).mpr hwholeSq
  refine ⟨hL, ?_, ?_⟩
  · refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hL.integrable (by norm_num))
      (fun _ _ _ ↦ (integrable_zero Ω ℝ μ).integrableOn) ?_
      stronglyMeasurable_zero.aestronglyMeasurable).symm
    intro A hA _
    have hA₀ : MeasurableSet[mΩ] A := hm A hA
    have hsplit : (⋃ i, B i ∩ A) = A := by rw [← iUnion_inter, hcover, univ_inter]
    have hdisj' : Pairwise (Disjoint on fun i ↦ B i ∩ A) :=
      fun _ _ hij ↦ (hdisj hij).mono inter_subset_left inter_subset_left
    rw [← hsplit,
      integral_iUnion_fintype (fun i ↦ (hB i).inter hA₀) hdisj'
        (fun _ ↦ (hL.integrable (by norm_num)).integrableOn)]
    simp only [hmean _ A hA, Finset.sum_const_zero, integral_zero']
  · calc
      (∫ x, (d x)^2 ∂μ) = ∑ i, ∫ x in B i, (d x)^2 ∂μ := by
        rw [← integral_iUnion_fintype hB hdisj hsq, hcover, setIntegral_univ]
      _ = ∑ i, ∫ x in B i, l x ∂μ := Finset.sum_congr rfl fun i _ ↦ henergy i
      _ = ∫ x, l x ∂μ := by
        rw [← integral_iUnion_fintype hB hdisj (fun _ ↦ hl.integrableOn),
          hcover, setIntegral_univ]

end LennonPittelFormalization

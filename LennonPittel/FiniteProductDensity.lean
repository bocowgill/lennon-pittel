module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Independence.Integration

/-!
# Densities and normalization of finite product measures
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- A coordinatewise product density gives the product of the tilted marginal laws. -/
theorem pi_withDensity_product (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, IsFiniteMeasure ((ν i).withDensity (f i))] :
    (Measure.pi ν).withDensity (fun x ↦ ∏ i, f i (x i)) =
      Measure.pi (fun i ↦ (ν i).withDensity (f i)) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  let g (i : ι) := (s i).indicator (f i)
  have hg (i : ι) : Measurable (g i) := (hf i).indicator (hs i)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  calc
    _ = ∫⁻ x, ∏ i, g i (x i) ∂Measure.pi ν := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ univ.pi s
      · rw [indicator_of_mem hx]
        exact Finset.prod_congr rfl fun i _ ↦
          (indicator_of_mem (mem_univ_pi.mp hx i) (f i)).symm
      · obtain ⟨i, hi⟩ := not_forall.mp (mt mem_univ_pi.mpr hx)
        rw [indicator_of_notMem hx]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi (f i))).symm
    _ = ∏ i, ∫⁻ x : ∀ j, Ω j, g i (x i) ∂Measure.pi ν :=
      lintegral_prod_eq_prod_lintegral_of_indepFun _ _
        (iIndepFun_pi fun i ↦ (hg i).aemeasurable)
        (fun i ↦ (hg i).comp (measurable_pi_apply i))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [(measurePreserving_eval ν i).lintegral_comp (hg i), withDensity_apply _ (hs i)]
      exact lintegral_indicator (hs i) (f i)

/-- Scaling the factors by finite constants scales their product by the product of the constants. -/
theorem pi_smul_coordinates (ν : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (ν i)]
    (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i ↦ c i • ν i) = (∏ i, c i) • Measure.pi ν := by
  let (i : ι) : IsFiniteMeasure (c i • ν i) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hc i)) (measure_lt_top _ _)⟩
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

/-- A finite product with nonzero factor masses is the normalized product times its total mass. -/
theorem pi_eq_prod_smul_pi_normalized (ν : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (ν i)]
    (hν : ∀ i, ν i univ ≠ 0) :
    Measure.pi ν = (∏ i, ν i univ) • Measure.pi (fun i ↦ (ν i univ)⁻¹ • ν i) := by
  let ν₀ (i : ι) := (ν i univ)⁻¹ • ν i
  let (i : ι) : IsProbabilityMeasure (ν₀ i) := ⟨by
    change ((ν i univ)⁻¹ • ν i) univ = 1
    rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (hν i) (measure_ne_top _ _)]⟩
  calc
    Measure.pi ν = Measure.pi (fun i ↦ (ν i univ) • ν₀ i) := by
      congr 1
      funext i
      change ν i = (ν i univ) • ((ν i univ)⁻¹ • ν i)
      rw [smul_smul, ENNReal.mul_inv_cancel (hν i) (measure_ne_top _ _), one_smul]
    _ = _ := pi_smul_coordinates ν₀ _ (fun i ↦ measure_ne_top _ _)

end LennonPittelFormalization

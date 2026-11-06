module

public import LennonPittel.TwoStablePairDensity
public import LennonPittel.TwoStableBetaIntegral
public import LennonPittel.TwoStableOrientationCounting

/-!
# Uniform bound for a fixed labeled pair

The fixed-pair probability bound depends only on the two orientation
sizes. No part of either cycle type is used in the score integral.
-/

@[expose] public section

open MeasureTheory Set StableMarriage
open scoped ENNReal

namespace LennonPittelFormalization

/-- The probability envelope for one labeled pair and prescribed orientations. -/
noncomputable def labeledStablePairMassBound (n u v : ℕ) : ℝ :=
  Real.exp 72 * ((1 + Real.log n) * pairSizeBetaFactor n u * pairSizeBetaFactor n v /
    ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial))

theorem labeledStablePairMassBound_nonneg (n u v : ℕ) :
    0 ≤ labeledStablePairMassBound n u v := by
  have h := Real.log_natCast_nonneg n
  unfold labeledStablePairMassBound pairSizeBetaFactor
  positivity

theorem measure_twoStableOrientationEvent_le_labeledStablePairMassBound
    {n u v : ℕ} (h : ValidPairSizes n (u, v)) (μ ν : Matching n) (A : Finset (Fin n))
    (hu : (pairOrientedMovedMen μ ν A).card = u)
    (hv : (pairOrientedMovedMen μ ν (Finset.univ \ A)).card = v) :
    continuousScoreLaw n (twoStableOrientationEvent μ ν A (A.image μ)) ≤
      ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  have hn : 0 < n := by have := h.1; have := h.2.2; omega
  have hu₀ : 0 < u := by have := h.1; omega
  have hv₀ : 0 < v := by have := h.2.1; omega
  have hp := continuousScoreLaw_twoStableOrientation_image_le_radial μ ν A hu hv hn hu₀ hv₀
  rw [lintegral_pairRadialUpperKernel_eq_closed] at hp
  refine hp.trans ?_
  rw [labeledStablePairMassBound, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul_right
    (by simpa only [pairLaplaceClosed] using lintegral_twoStableClosedLaplaceRadial_le h) _

private theorem pairOrientedMovedMen_eq_sides {n : ℕ} {μ ν : Matching n}
    {U V : Finset (Fin n)} (hUV : LabeledPairOrientation μ ν U V) :
    pairOrientedMovedMen ν μ U = U ∧
      pairOrientedMovedMen ν μ (Finset.univ \ U) = V := by
  have hm (i : Fin n) : ν i ≠ μ i ↔ i ∈ U ∨ i ∈ V := by
    rw [← Finset.mem_union, hUV.union_support]
    simp only [relativeMenPermutation, Equiv.Perm.mem_support, Equiv.trans_apply]
    exact ne_comm.trans (not_congr ν.symm_apply_eq).symm
  constructor
  · ext i
    simp only [pairOrientedMovedMen, Finset.mem_filter, hm, and_iff_left_iff_imp]
    exact fun hi ↦ Or.inl hi
  · ext i
    simp only [pairOrientedMovedMen, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, hm]
    exact ⟨fun ⟨hi, h⟩ ↦ h.resolve_left hi,
      fun hi ↦ ⟨fun hj ↦ Finset.disjoint_left.mp hUV.disjoint hj hi, Or.inr hi⟩⟩

/-- A fixed-pair sector with the two specified orientations has at most the
uniform labeled mass. Any extra score or cycle conditions only shrink it. -/
theorem measure_stablePairSector_le_labeledStablePairMassBound {n u v : ℕ}
    {μ ν : Matching n} {U V : Finset (Fin n)}
    (h : ValidPairSizes n (u, v)) (hUV : LabeledPairOrientation μ ν U V)
    (hu : U.card = u) (hv : V.card = v)
    {E : Set (ScoreProfile n)}
    (hE : ∀ᵐ x ∂continuousScoreLaw n, x ∈ E →
      IsScoreStable x μ ∧ IsScoreStable x ν ∧
        U = worsePartnerMen (profileOfScores x) μ ν) :
    continuousScoreLaw n E ≤ ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  have hsub : continuousScoreLaw n E ≤
      continuousScoreLaw n (twoStableOrientationEvent ν μ U (U.image ν)) := by
    apply measure_mono_ae
    filter_upwards [ae_injective_rows n, hE] with x hx hs he
    obtain ⟨hμ, hν, hU⟩ := hs he
    exact (twoStableOrientation_of_male_class hν hμ hx U
      (fun m _ ↦ hU ▸ mem_worsePartnerMen_iff_score_lt hx μ ν m)).1
  exact hsub.trans (measure_twoStableOrientationEvent_le_labeledStablePairMassBound
    h ν μ U ((congrArg Finset.card (pairOrientedMovedMen_eq_sides hUV).1).trans hu)
    ((congrArg Finset.card (pairOrientedMovedMen_eq_sides hUV).2).trans hv))

/-- Multiplying by the unrestricted labeled cardinal restores the size kernel. -/
theorem labeledStablePairMassBound_mul_factorials {n u v : ℕ}
    (h : ValidPairSizes n (u, v)) :
    ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) * labeledStablePairMassBound n u v =
      Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v) := by
  rw [twoStablePairSizeKernel_eq_beta_factors h, labeledStablePairMassBound]
  ring

end LennonPittelFormalization

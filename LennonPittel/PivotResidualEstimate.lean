module

public import LennonPittel.PivotIncomparableScoreCount
public import LennonPittel.PivotResidualImageGeometry

/-!
# The residual is bounded by a fixed-pair score event

After the shared switch, the long orientation, the short orientation, the
score domain and the exposure cap are conditions on the two endpoint
matchings. This is the interface to the two-stable probability estimate.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization
namespace PivotCountParameters

variable {n : ℕ}

theorem ae_comparableResidualMass_le_scoreGeometry (q : PivotCountParameters)
    {κ : ℝ} (hn : 0 < n) (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : q.shortCutoff ≤ q.supportCap)
    (hK : (q.supportCap : ℝ) * (2048 * Real.log n / n) ≤ 1) :
    q.comparableResidualMass ≤ᵐ[continuousScoreLaw n] fun x ↦
      2 * incomparableScorePairCount
        (IsResidualPairGeometry q.lowerLength q.supportCap q.shortCutoff) x := by
  filter_upwards [ae_injective_rows n, ae_unitOpen_scores n] with x ht hx
  let hlong (i : PivotMark n) (h : IsLocallyEligiblePivot q.lowerLength q.upperLength
      q.geometryBudget x i.1 i.2) : q.supportCap < i.2.support.card :=
    h.supportCap_lt hn hκ hcap
  let hcut (i : PivotMark n) : 0 ≤ residualChoiceCutoff x i.1 i.2 :=
    residualChoiceCutoff_nonneg (fun r i ↦ (hx r i).1.le) i
  apply q.comparableResidualMass_le_twice_scorePairCount ht hlong hcut
  intro μ₀ hopt a
  have ha := q.residualMarkedPairOfChoice_eligible ht hlong hcut a
  exact (q.residualMarkedPairOfChoice ht hlong hcut a).toggleImage_geometry
    hopt ht hn hL hK (fun _ _ ↦ rfl) ha.1 ha.2

/-- Bound the comparable residual expectation by two times the original-law
mass of the measurable endpoint geometry, summed over fixed ordered pairs. -/
theorem integral_comparableResidualMass_le_geometry (q : PivotCountParameters)
    {κ : ℝ} (hn : 0 < n) (hκ : κ < q.lowerLength)
    (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hL : q.shortCutoff ≤ q.supportCap)
    (hK : (q.supportCap : ℝ) * (2048 * Real.log n / n) ≤ 1) :
    (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
      2 * ∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
        (scoreIncomparablePairEvent
          (IsResidualPairGeometry q.lowerLength q.supportCap q.shortCutoff) μ ν) :=
  q.integral_comparableResidualMass_le_twice_sum
    (measurableSet_isResidualPairGeometry q.lowerLength q.supportCap q.shortCutoff)
    (q.ae_comparableResidualMass_le_scoreGeometry hn hκ hcap hL hK)

end PivotCountParameters

variable {n : ℕ}

/-- Too few forced short cycles for the contradiction with the exposure cap. -/
def forcedShortCycleException (μ ν : Matching n) (L : ℕ) : Set (ScoreProfile n) :=
  {x | ((forcedShortCycles (profileOfScores x) μ ν L).card : ℝ) <
    (9 / 10 : ℝ) * Real.log L}

/-- Too few background short cycles for the contradiction with the exposure cap. -/
def backgroundShortCycleException (μ ν : Matching n) (L : ℕ) : Set (ScoreProfile n) :=
  {x | ((backgroundShortCycles (profileOfScores x) μ ν L).card : ℝ) <
    (9 / 10 : ℝ) * Real.log L}

theorem measurableSet_forcedShortCycleException (μ ν : Matching n) (L : ℕ) :
    MeasurableSet (forcedShortCycleException μ ν L) :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | ((forcedShortCycles p μ ν L).card : ℝ) <
      (9 / 10 : ℝ) * Real.log L})

theorem measurableSet_backgroundShortCycleException (μ ν : Matching n) (L : ℕ) :
    MeasurableSet (backgroundShortCycleException μ ν L) :=
  measurable_profileOfScores n (MeasurableSet.of_discrete :
    MeasurableSet {p : Profile n | ((backgroundShortCycles p μ ν L).card : ℝ) <
      (9 / 10 : ℝ) * Real.log L})

/-- In each fixed-pair event at least one of the two short-cycle counts
is below its typical threshold. No independence of the exceptions is used. -/
theorem scoreResidualPairEvent_subset_shortCycleExceptions {b : ℝ} {K L : ℕ}
    (hL : 2 ≤ L) (μ ν : Matching n) :
    scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν ⊆
      forcedShortCycleException μ ν L ∪ backgroundShortCycleException μ ν L := by
  intro x hx
  by_contra h
  have h1 := not_lt.mp (fun h1 ↦ h (Or.inl h1) :
    ¬ ((forcedShortCycles (profileOfScores x) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log L)
  have h2 := not_lt.mp (fun h2 ↦ h (Or.inr h2) :
    ¬ ((backgroundShortCycles (profileOfScores x) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log L)
  have hl : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hc := hx.2.2.2.rank.forced_background_card_le
  linarith

/-- Keep both joint stability tests when applying the exception union bound. -/
theorem measure_scoreResidualPairEvent_le_shortCycleExceptions {b : ℝ} {K L : ℕ}
    (hL : 2 ≤ L) (μ ν : Matching n) :
    let E := scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν
    continuousScoreLaw n E ≤ continuousScoreLaw n (E ∩ forcedShortCycleException μ ν L) +
      continuousScoreLaw n (E ∩ backgroundShortCycleException μ ν L) := by
  dsimp only
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  rcases scoreResidualPairEvent_subset_shortCycleExceptions hL μ ν hx with hf | hb
  · exact Or.inl ⟨hx, hf⟩
  · exact Or.inr ⟨hx, hb⟩

end LennonPittelFormalization

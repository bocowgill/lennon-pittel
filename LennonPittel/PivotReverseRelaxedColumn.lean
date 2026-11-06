module

public import LennonPittel.ReverseCompatibilityRectangle

/-!
# Removing a crossed cell from a reverse column test

Restrict the test to a set of kept candidates. An omitted crossed cell is
then independent of the target and of all kept competitors, even though
the height of its blocking rectangle is the target's random increment.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The event that the kept column has the designated successor and the
omitted cell lies in the crossed rectangle. -/
def reverseRelaxedColumnCrossBlockerEvent {ι : Type*} [DecidableEq ι]
    (keep : ι → Prop) (target : {i // keep i}) (crossed : {i // ¬ keep i})
    (v : ι → ℝ) (x y dx : ℝ) : Set (ι → ℝ × ℝ) :=
  {z | (fun i : {i // keep i} ↦ z i.val) ∈
      reverseSuccessorColumnEvent y (fun i ↦ v i.val) target ∧
    z crossed.val ∈ reverseCompatibilityRectangle x y dx ((z target.val).2 - y)}

/-- Under the original inactive column law, one omitted crossed cell
contributes at most its male width times the target threshold divided by
the squared kept-competitor total. -/
theorem reverseRelaxedColumnCrossBlocker_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keep : ι → Prop) [DecidablePred keep] (target : {i // keep i}) (crossed : {i // ¬ keep i})
    {v : ι → ℝ} {x y dx : ℝ} (hy₀ : 0 ≤ y) (hy₁ : y < 1) (hdx : 0 ≤ dx)
    (hv : ∀ i, v i ∈ Icc 0 1)
    (hS : 0 < ∑ j : {j : {i // keep i} // j ≠ target}, v j.val.val) :
    (Measure.pi fun _ : ι ↦ unitScoreLaw.prod (inactiveFemaleScoreLaw y))
      (reverseRelaxedColumnCrossBlockerEvent keep target crossed v x y dx) ≤
      ENNReal.ofReal (dx * (v target.val /
        (∑ j : {j : {i // keep i} // j ≠ target}, v j.val.val) ^ 2)) := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy₀ hy₁
  let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw y)
  let p := measurePreserving_piEquivPiSubtypeProd (fun _ : ι ↦ ν) keep
  let ht := measurePreserving_rowTargetAndCompetitors (fun _ : {i // keep i} ↦ ν) target
  let hc := measurePreserving_eval (fun _ : {i // ¬ keep i} ↦ ν) crossed
  let hm := (ht.prod hc).comp p
  let J := {j : {i // keep i} // j ≠ target}
  let E : Set (((ℝ × ℝ) × (J → ℝ × ℝ)) × (ℝ × ℝ)) :=
    {z | z.1 ∈ reverseSuccessorPairEvent y (v target.val) (fun j ↦ v j.val.val) ∧
      z.2 ∈ reverseCompatibilityRectangle x y dx (z.1.1.2 - y)}
  have hE : MeasurableSet E := by
    change MeasurableSet ((Prod.fst ⁻¹' reverseSuccessorPairEvent y (v target.val)
      (fun j : J ↦ v j.val.val)) ∩
      {z : ((ℝ × ℝ) × (J → ℝ × ℝ)) × (ℝ × ℝ) |
        z.2 ∈ reverseCompatibilityRectangle x y dx (z.1.1.2 - y)})
    refine ((measurableSet_reverseSuccessorPairEvent _ _ _).preimage measurable_fst).inter ?_
    change MeasurableSet ((fun z : ((ℝ × ℝ) × (J → ℝ × ℝ)) × (ℝ × ℝ) ↦ z.2.1) ⁻¹'
      Ioo x (x + dx) ∩ ({z | y < z.2.2} ∩ {z | z.2.2 < y + (z.1.1.2 - y)}))
    exact (measurableSet_Ioo.preimage measurable_snd.fst).inter
      ((measurableSet_lt measurable_const measurable_snd.snd).inter
        (measurableSet_lt measurable_snd.snd
          (measurable_const.add (measurable_fst.fst.snd.sub_const y))))
  change (Measure.pi fun _ : ι ↦ ν)
    ((fun z : ι → ℝ × ℝ ↦ ((z target.val, fun j : J ↦ z j.val.val), z crossed.val)) ⁻¹' E) ≤ _
  exact (hm.measure_preimage hE.nullMeasurableSet).trans_le
    (inactiveCell_reverseSuccessorCrossBlocker_mass_le hy₀ hy₁ hdx
      (hv target.val) (fun j : J ↦ hv j.val.val) hS)

end LennonPittelFormalization

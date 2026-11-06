module

public import LennonPittel.Model
public import Mathlib.Data.List.OfFn
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Uniform

/-!
# Fresh adaptive queries of a finite table

A prescribed transcript fixes the coordinate read at every step. If these coordinates are
distinct, the transcript event is a product rectangle with one singleton factor per query.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {I A : Type*}

/-- At each tick, append the answer to the query chosen from the preceding answers. -/
def adaptiveTranscript (next : List A → I) (table : I → A) : ℕ → List A
  | 0 => []
  | t + 1 =>
      let history := adaptiveTranscript next table t
      history ++ [table (next history)]

@[simp]
theorem length_adaptiveTranscript (next : List A → I) (table : I → A) (T : ℕ) :
    (adaptiveTranscript next table T).length = T := by
  induction T with
  | zero => rfl
  | succ T ih => simp [adaptiveTranscript, ih]

/-- The transcript, indexed by the finite type of ticks. -/
def adaptiveTranscriptFn (next : List A → I) (table : I → A) (T : ℕ) (t : Fin T) : A :=
  (adaptiveTranscript next table T)[t.val]'(by simp [t.isLt])

@[simp]
theorem ofFn_adaptiveTranscriptFn (next : List A → I) (table : I → A) (T : ℕ) :
    List.ofFn (adaptiveTranscriptFn next table T) = adaptiveTranscript next table T := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp [adaptiveTranscriptFn]

/-- The first \(t\) entries of a later transcript agree with the transcript after \(t\) ticks. -/
theorem take_adaptiveTranscript (next : List A → I) (table : I → A) {t T : ℕ} (h : t ≤ T) :
    (adaptiveTranscript next table T).take t = adaptiveTranscript next table t := by
  induction T with
  | zero => simp [adaptiveTranscript, Nat.eq_zero_of_le_zero h]
  | succ T ih =>
    by_cases ht : t ≤ T
    · rw [adaptiveTranscript, List.take_append_of_le_length (by simpa using ht), ih ht]
    · have hEq : t = T + 1 := by omega
      subst t
      exact List.take_of_length_le (by simp)

/-- Every initial segment of the indexed transcript is its own completed history. -/
theorem take_ofFn_adaptiveTranscriptFn (next : List A → I) (table : I → A) {t T : ℕ}
    (h : t ≤ T) :
    (List.ofFn (adaptiveTranscriptFn next table T)).take t = adaptiveTranscript next table t := by
  rw [ofFn_adaptiveTranscriptFn, take_adaptiveTranscript next table h]

/-- The chosen coordinate on a prescribed branch is a function of its preceding answers. -/
def adaptiveQueryIndex (next : List A → I) {T : ℕ} (y : Fin T → A) (t : Fin T) : I :=
  next ((List.ofFn y).take t.val)

/-- The answer at a tick is the table entry queried from the history before that tick. -/
theorem adaptiveTranscriptFn_apply (next : List A → I) (table : I → A)
    (T : ℕ) (t : Fin T) :
    adaptiveTranscriptFn next table T t = table (next (adaptiveTranscript next table t.val)) := by
  have ht : t.val < (adaptiveTranscript next table T).length := by simp [t.isLt]
  have heq := List.take_succ_eq_append_getElem ht
  rw [take_adaptiveTranscript next table (Nat.succ_le_of_lt t.isLt),
    take_adaptiveTranscript next table (Nat.le_of_lt t.isLt), adaptiveTranscript] at heq
  exact (List.singleton_inj.mp (List.append_cancel_left heq)).symm

/-- A table produces the prescribed transcript exactly when it agrees at its branch queries. -/
theorem adaptiveTranscriptFn_eq_iff (next : List A → I) (table : I → A) {T : ℕ} (y : Fin T → A) :
    adaptiveTranscriptFn next table T = y ↔ ∀ t, table (adaptiveQueryIndex next y t) = y t := by
  constructor
  · rintro rfl t
    simp only [adaptiveQueryIndex, ofFn_adaptiveTranscriptFn,
      take_adaptiveTranscript next table (Nat.le_of_lt t.isLt)]
    exact (adaptiveTranscriptFn_apply next table T t).symm
  · intro hy
    apply List.ofFn_injective
    rw [ofFn_adaptiveTranscriptFn]
    suffices h : ∀ k ≤ T, adaptiveTranscript next table k = (List.ofFn y).take k by
      rw [h T le_rfl, List.take_of_length_le (by simp)]
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk' : k < T := hk
      rw [adaptiveTranscript, ih (Nat.le_of_lt hk'),
        List.take_succ_eq_append_getElem (show k < (List.ofFn y).length by simpa)]
      simpa only [List.getElem_ofFn, adaptiveQueryIndex] using
        congrArg ((List.ofFn y).take k ++ [·]) (hy ⟨k, hk'⟩)

variable [Fintype I] [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A fresh adaptive query rule sends independent table entries to independent answers. -/
theorem map_adaptiveTranscriptFn_eq_pi (μ : Measure A) [IsProbabilityMeasure μ]
    (next : List A → I) (T : ℕ)
    (fresh : ∀ y : Fin T → A, Function.Injective (adaptiveQueryIndex next y)) :
    Measure.map (fun table ↦ adaptiveTranscriptFn next table T)
      (Measure.pi (fun _ : I ↦ μ)) = Measure.pi (fun _ : Fin T ↦ μ) := by
  classical
  refine Measure.ext_of_singleton fun y ↦ ?_
  let q := adaptiveQueryIndex next y
  let B (i : I) : Set A := {a | ∀ t, q t = i → a = y t}
  have hbox : (fun table ↦ adaptiveTranscriptFn next table T) ⁻¹' {y} = univ.pi B := by
    ext table
    change adaptiveTranscriptFn next table T = y ↔ _
    rw [adaptiveTranscriptFn_eq_iff, Set.mem_univ_pi]
    exact ⟨fun h _ t ht ↦ ht ▸ h t, fun h t ↦ h (q t) t rfl⟩
  have hsingle (t : Fin T) : B (q t) = {y t} := by
    ext a
    change (∀ s, q s = q t → a = y s) ↔ a = y t
    exact ⟨fun h ↦ h t rfl, fun ha s hs ↦ (fresh y hs).symm ▸ ha⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y), hbox,
    Measure.pi_pi, Measure.pi_singleton]
  calc
    (∏ i, μ (B i)) = ∏ i ∈ Finset.univ.image q, μ (B i) := by
      symm
      refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ ?_
      have hBi : B i = univ := by
        ext a
        simp only [B, mem_ofPred_eq, mem_univ, iff_true]
        exact fun t ht ↦ (hi (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)).elim
      rw [hBi, measure_univ]
    _ = ∏ t, μ (B (q t)) := Finset.prod_image (fresh y).injOn
    _ = ∏ t, μ {y t} := by simp only [hsingle]

/-- The finite uniform law on a function type is the product of the uniform coordinate laws. -/
theorem pi_uniformOfFintype_toMeasure [DecidableEq I] [Nonempty A] :
    Measure.pi (fun _ : I ↦ (PMF.fintypeUniform A).toMeasure) =
      (PMF.fintypeUniform (I → A)).toMeasure := by
  classical
  refine Measure.ext_of_singleton fun y ↦ ?_
  simp only [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.fintypeUniform_apply, Fintype.card_pi]
  push_cast
  exact (ENNReal.prod_inv_distrib (by simp [Set.Pairwise])).symm

/-- Fresh adaptive queries of a uniform table give a uniform transcript. -/
theorem map_adaptiveTranscriptFn_eq_uniform [DecidableEq I] [Nonempty A] (next : List A → I) (T : ℕ)
    (fresh : ∀ y : Fin T → A, Function.Injective (adaptiveQueryIndex next y)) :
    Measure.map (fun table ↦ adaptiveTranscriptFn next table T)
      (PMF.fintypeUniform (I → A)).toMeasure = (PMF.fintypeUniform (Fin T → A)).toMeasure := by
  rw [← pi_uniformOfFintype_toMeasure (I := I), ← pi_uniformOfFintype_toMeasure (I := Fin T)]
  exact map_adaptiveTranscriptFn_eq_pi _ next T fresh

end LennonPittelFormalization

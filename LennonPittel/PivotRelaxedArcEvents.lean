module

public import LennonPittel.PivotReverseRelaxedColumn
public import LennonPittel.PivotReverseScoreSuccessor

/-!
# Relaxed arcs and crossed cells in an actual inactive column

Omit every pivot man from the reverse successor competition. The actual
successor passes the relaxed test if its target is not omitted. Each
potential blocker then belongs to a coordinate not used by that test.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The male index of an inactive cell in a given column. -/
abbrev forwardInactiveColumnMan {n : ℕ} {flag : OffDiagonalCellIndex n → Bool}
    {i : Fin n} (q : ForwardInactiveColumnIndex flag i) : Fin n :=
  q.val.val.val.1

theorem forwardInactiveColumnMan_injective {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (i : Fin n) : Function.Injective (forwardInactiveColumnMan (flag := flag) (i := i)) := by
  intro q t h
  exact Subtype.ext (Subtype.ext (Subtype.ext
    (Prod.ext h (q.property.trans t.property.symm))))

/-- The candidates remaining in the column when the pivot men are omitted. -/
abbrev ForwardKeptColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i : Fin n) :=
  {q : ForwardInactiveColumnIndex flag i // forwardInactiveColumnMan q ∉ P}

/-- The omitted inactive cells in a given column. -/
abbrev ForwardOmittedColumnIndex {n : ℕ} (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i : Fin n) :=
  {q : ForwardInactiveColumnIndex flag i // ¬ (forwardInactiveColumnMan q ∉ P)}

/-- The threshold of an inactive cell is its man's spouse score. -/
abbrev forwardInactiveColumnThreshold {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {i : Fin n}
    (q : ForwardInactiveColumnIndex flag i) : ℝ :=
  (diagonalPairAt d (forwardInactiveColumnMan q)).1

/-- The total threshold of the kept competitors, excluding the target. -/
noncomputable def forwardKeptCompetitorMass {n : ℕ} (d : DiagonalScorePairs n)
    {flag : OffDiagonalCellIndex n → Bool} {P : Finset (Fin n)} {i : Fin n}
    (t : ForwardKeptColumnIndex flag P i) : ℝ :=
  ∑ q : {q : ForwardKeptColumnIndex flag P i // q ≠ t},
    forwardInactiveColumnThreshold d q.val.val

/-- The arc test on the original inactive array after ignoring pivot men. -/
def forwardInactiveRelaxedReverseArcEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (P : Finset (Fin n)) (i j : Fin n) :
    Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
  ⋃ t : {t : ForwardKeptColumnIndex flag P i // forwardInactiveColumnMan t.val = j},
    (fun z : ForwardInactiveColumnIndex flag i → ℝ × ℝ ↦
      fun q : ForwardKeptColumnIndex flag P i ↦ z q.val) ⁻¹'
    reverseSuccessorColumnEvent (diagonalPairAt d i).2
      (fun q : ForwardKeptColumnIndex flag P i ↦ forwardInactiveColumnThreshold d q.val) t.val

/-- The relaxed arc and the rectangle for the omitted inactive cell of the crossed man. -/
def forwardInactiveRelaxedCrossEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (P : Finset (Fin n)) (i j m : Fin n)
    (dx : ℝ) : Set (ForwardInactiveColumnIndex flag i → ℝ × ℝ) :=
  ⋃ t : {t : ForwardKeptColumnIndex flag P i // forwardInactiveColumnMan t.val = j},
    ⋃ c : {c : ForwardOmittedColumnIndex flag P i // forwardInactiveColumnMan c.val = m},
      reverseRelaxedColumnCrossBlockerEvent (fun q ↦ forwardInactiveColumnMan q ∉ P)
        t.val c.val (forwardInactiveColumnThreshold d) (diagonalPairAt d m).1
        (diagonalPairAt d i).2 dx

/-- An unavailable or omitted target cannot pass the relaxed arc test. -/
theorem forwardInactiveRelaxedReverseArcEvent_eq_empty_of_noTarget {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i j : Fin n)
    (h : ¬ ∃ t : ForwardKeptColumnIndex flag P i, forwardInactiveColumnMan t.val = j) :
    forwardInactiveRelaxedReverseArcEvent d flag P i j = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨t, _⟩ := mem_iUnion.mp hz
  exact h ⟨t.val, t.property⟩

/-- The crossed event is empty if either of its two cells is unavailable. -/
theorem forwardInactiveRelaxedCrossEvent_eq_empty_of_noCell {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i j m : Fin n) (dx : ℝ)
    (h : (¬ ∃ t : ForwardKeptColumnIndex flag P i, forwardInactiveColumnMan t.val = j) ∨
      (¬ ∃ c : ForwardOmittedColumnIndex flag P i, forwardInactiveColumnMan c.val = m)) :
    forwardInactiveRelaxedCrossEvent d flag P i j m dx = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  obtain ⟨c, _⟩ := mem_iUnion.mp ht
  exact h.elim (fun h' ↦ h' ⟨t.val, t.property⟩) (fun h' ↦ h' ⟨c.val, c.property⟩)

private theorem reverseSuccessorColumnEvent_restrict {ι : Type*} [DecidableEq ι]
    {keep : ι → Prop} {y : ℝ} {v : ι → ℝ} (t : {q // keep q}) {z : ι → ℝ × ℝ}
    (h : z ∈ reverseSuccessorColumnEvent y v t.val) :
    (fun q : {q // keep q} ↦ z q.val) ∈
      reverseSuccessorColumnEvent y (fun q : {q // keep q} ↦ v q.val) t :=
  ⟨h.1, h.2.1, fun q ↦ h.2.2 ⟨q.val.val, fun he ↦ q.property (Subtype.ext he)⟩⟩

/-- Omitting other men cannot remove an actual successor whose target is kept. -/
theorem forwardInactiveReverseArcEvent_subset_relaxed {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (P : Finset (Fin n)) (i j : Fin n) (hj : j ∉ P) :
    forwardInactiveReverseArcEvent d flag i j ⊆
      forwardInactiveRelaxedReverseArcEvent d flag P i j := by
  intro z hz
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  let t : ForwardKeptColumnIndex flag P i := ⟨q.val, by
    rwa [show forwardInactiveColumnMan q.val = j from q.property]⟩
  exact mem_iUnion.mpr ⟨⟨t, q.property⟩, reverseSuccessorColumnEvent_restrict t hq⟩

/-- An actual arc and a crossed rectangle at an omitted coordinate give the
relaxed crossed event. The rectangle may already be enlarged in male width. -/
theorem mem_forwardInactiveRelaxedCrossEvent_of_reverseArc {n : ℕ}
    {d : DiagonalScorePairs n} {flag : OffDiagonalCellIndex n → Bool}
    {P : Finset (Fin n)} {i j m : Fin n} {dx : ℝ}
    {z : ForwardInactiveColumnIndex flag i → ℝ × ℝ}
    (t c : ForwardInactiveColumnIndex flag i)
    (ht : forwardInactiveColumnMan t = j) (hc : forwardInactiveColumnMan c = m)
    (hj : j ∉ P) (hm : m ∈ P)
    (harc : z ∈ reverseSuccessorColumnEvent (diagonalPairAt d i).2
      (forwardInactiveColumnThreshold d) t)
    (hrect : z c ∈ reverseCompatibilityRectangle (diagonalPairAt d m).1
      (diagonalPairAt d i).2 dx ((z t).2 - (diagonalPairAt d i).2)) :
    z ∈ forwardInactiveRelaxedCrossEvent d flag P i j m dx := by
  let t' : ForwardKeptColumnIndex flag P i := ⟨t, ht ▸ hj⟩
  let c' : ForwardOmittedColumnIndex flag P i := ⟨c, fun h ↦ h (hc ▸ hm)⟩
  exact mem_iUnion.mpr ⟨⟨t', ht⟩,
    mem_iUnion.mpr ⟨⟨c', hc⟩, reverseSuccessorColumnEvent_restrict t' harc, hrect⟩⟩

/-- The relaxed arc is a measurable event in its original column. -/
theorem measurableSet_forwardInactiveRelaxedReverseArcEvent {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i j : Fin n) :
    MeasurableSet (forwardInactiveRelaxedReverseArcEvent d flag P i j) :=
  MeasurableSet.iUnion fun t ↦ (measurableSet_reverseSuccessorColumnEvent _ _ t.val).preimage
    (Measurable.of_eval fun q ↦ measurable_pi_apply q.val)

/-- The crossed event is jointly measurable when the male width is a
measurable function of the revealed data. -/
theorem measurableSet_forwardInactiveRelaxedCrossEvent_varying {n : ℕ}
    {Y : Type*} [MeasurableSpace Y]
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i j m : Fin n) {dx : Y → ℝ} (hdx : Measurable dx) :
    MeasurableSet {z : Y × (ForwardInactiveColumnIndex flag i → ℝ × ℝ) |
      z.2 ∈ forwardInactiveRelaxedCrossEvent d flag P i j m (dx z.1)} := by
  classical
  let W := Y × (ForwardInactiveColumnIndex flag i → ℝ × ℝ)
  let x := (diagonalPairAt d m).1
  let y := (diagonalPairAt d i).2
  let S (t : {t : ForwardKeptColumnIndex flag P i // forwardInactiveColumnMan t.val = j})
      (c : {c : ForwardOmittedColumnIndex flag P i // forwardInactiveColumnMan c.val = m}) :
      Set W :=
    {z | z.2 ∈ reverseRelaxedColumnCrossBlockerEvent
      (fun q ↦ forwardInactiveColumnMan q ∉ P) t.val c.val
      (forwardInactiveColumnThreshold d) x y (dx z.1)}
  have he : {z : W | z.2 ∈ forwardInactiveRelaxedCrossEvent d flag P i j m (dx z.1)} =
      ⋃ t, ⋃ c, S t c := by
    ext z
    simp only [forwardInactiveRelaxedCrossEvent, mem_ofPred_eq, mem_iUnion, S, x, y]
  rw [he]
  refine MeasurableSet.iUnion fun t ↦ MeasurableSet.iUnion fun c ↦ ?_
  have hc : Measurable (fun z : W ↦ z.2 c.val.val) :=
    (measurable_pi_apply c.val.val).comp measurable_snd
  have ht : Measurable (fun z : W ↦ z.2 t.val.val) :=
    (measurable_pi_apply t.val.val).comp measurable_snd
  change MeasurableSet
    ((fun z : W ↦ fun q : ForwardKeptColumnIndex flag P i ↦ z.2 q.val) ⁻¹'
      reverseSuccessorColumnEvent y
        (fun q : ForwardKeptColumnIndex flag P i ↦ forwardInactiveColumnThreshold d q.val) t.val ∩
    {z : W | z.2 c.val.val ∈ reverseCompatibilityRectangle x y (dx z.1)
      ((z.2 t.val.val).2 - y)})
  refine ((measurableSet_reverseSuccessorColumnEvent _ _ t.val).preimage
    (Measurable.of_eval fun q ↦ (measurable_pi_apply q.val).comp measurable_snd)).inter ?_
  change MeasurableSet
    ({z : W | x < (z.2 c.val.val).1} ∩
    ({z : W | (z.2 c.val.val).1 < x + dx z.1}) ∩
    ({z : W | y < (z.2 c.val.val).2} ∩
    {z : W | (z.2 c.val.val).2 < y + ((z.2 t.val.val).2 - y)}))
  exact ((measurableSet_lt measurable_const hc.fst).inter
    (measurableSet_lt hc.fst (measurable_const.add (hdx.comp measurable_fst)))).inter
    ((measurableSet_lt measurable_const hc.snd).inter
      (measurableSet_lt hc.snd (measurable_const.add (ht.snd.sub_const y))))

/-- In particular, a fixed-width crossed event is measurable. -/
theorem measurableSet_forwardInactiveRelaxedCrossEvent {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (P : Finset (Fin n)) (i j m : Fin n) (dx : ℝ) :
    MeasurableSet (forwardInactiveRelaxedCrossEvent d flag P i j m dx) :=
  (measurableSet_forwardInactiveRelaxedCrossEvent_varying d flag P i j m
    (Y := Unit) (dx := fun _ ↦ dx) measurable_const).preimage
    ((show Measurable (fun _ : ForwardInactiveColumnIndex flag i → ℝ × ℝ ↦ ()) from
      measurable_const).prodMk measurable_id)

private theorem measure_iUnion_le_of_subsingleton {Ω ι : Type*} [MeasurableSpace Ω]
    [Subsingleton ι] (ν : Measure Ω) (S : ι → Set Ω) (C : ℝ≥0∞)
    (h : ∀ i, ν (S i) ≤ C) : ν (⋃ i, S i) ≤ C := by
  cases isEmpty_or_nonempty ι with
  | inl hi => simp
  | inr hi =>
    obtain ⟨i⟩ := hi
    exact (measure_mono (iUnion_subset fun j ↦ Subsingleton.elim j i ▸ subset_rfl)).trans (h i)

private theorem keptColumn_projection_preserving {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool) (P : Finset (Fin n))
    (i : Fin n) (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1) :
    MeasurePreserving (fun z : ForwardInactiveColumnIndex flag i → ℝ × ℝ ↦
      fun q : ForwardKeptColumnIndex flag P i ↦ z q.val)
      (normalizedForwardInactiveColumnLaw d flag i)
      (Measure.pi fun _ : ForwardKeptColumnIndex flag P i ↦
        unitScoreLaw.prod (inactiveFemaleScoreLaw (diagonalPairAt d i).2)) := by
  let := inactiveFemaleScoreLaw_isProbabilityMeasure hy0 hy1
  let ν := unitScoreLaw.prod (inactiveFemaleScoreLaw (diagonalPairAt d i).2)
  exact measurePreserving_fst.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ForwardInactiveColumnIndex flag i ↦ ν)
      (fun q ↦ forwardInactiveColumnMan q ∉ P))

/-- Upper bound for the normalized relaxed arc, including absent targets. -/
theorem normalizedForwardInactiveColumnLaw_relaxedReverseArc_le {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i j : Fin n) {X a : ℝ}
    (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1)
    (hx : ∀ k, (diagonalPairAt d k).1 ∈ Icc 0 1) (hX : 0 < X) (ha : 0 < a)
    (hcomp : ∀ t : ForwardKeptColumnIndex flag P i, forwardInactiveColumnMan t.val = j →
      X / a ≤ forwardKeptCompetitorMass d t) :
    normalizedForwardInactiveColumnLaw d flag i
      (forwardInactiveRelaxedReverseArcEvent d flag P i j) ≤
      ENNReal.ofReal a * ENNReal.ofReal ((diagonalPairAt d j).1 / X) := by
  have : Subsingleton {t : ForwardKeptColumnIndex flag P i //
      forwardInactiveColumnMan t.val = j} :=
    ⟨fun t q ↦ Subtype.ext (Subtype.ext
      (forwardInactiveColumnMan_injective flag i (t.property.trans q.property.symm)))⟩
  refine measure_iUnion_le_of_subsingleton _ _ _ fun t ↦ ?_
  rw [(keptColumn_projection_preserving d flag P i hy0 hy1).measure_preimage
    (measurableSet_reverseSuccessorColumnEvent _ _ t.val).nullMeasurableSet]
  have h := reverseSuccessorColumnEvent_mass_le t.val hy0 hy1
    (fun q : ForwardKeptColumnIndex flag P i ↦ hx (forwardInactiveColumnMan q.val))
    hX ha (hcomp t.val t.property)
  simpa only [forwardInactiveColumnThreshold, t.property] using h

/-- The probability of one crossed cell with a prescribed relaxed arc.
The arc factor is the same as for an ordinary relaxed column. -/
theorem normalizedForwardInactiveColumnLaw_relaxedCross_le {n : ℕ}
    (d : DiagonalScorePairs n) (flag : OffDiagonalCellIndex n → Bool)
    (P : Finset (Fin n)) (i j m : Fin n) {X a dx : ℝ}
    (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1)
    (hx : ∀ k, (diagonalPairAt d k).1 ∈ Icc 0 1) (hX : 0 < X) (ha : 0 < a) (hdx : 0 ≤ dx)
    (hcomp : ∀ t : ForwardKeptColumnIndex flag P i, forwardInactiveColumnMan t.val = j →
      X / a ≤ forwardKeptCompetitorMass d t) :
    normalizedForwardInactiveColumnLaw d flag i
      (forwardInactiveRelaxedCrossEvent d flag P i j m dx) ≤
      (ENNReal.ofReal a * ENNReal.ofReal ((diagonalPairAt d j).1 / X)) *
        ENNReal.ofReal (a * dx / X) := by
  have : Subsingleton {t : ForwardKeptColumnIndex flag P i //
      forwardInactiveColumnMan t.val = j} :=
    ⟨fun t q ↦ Subtype.ext (Subtype.ext
      (forwardInactiveColumnMan_injective flag i (t.property.trans q.property.symm)))⟩
  have : Subsingleton {c : ForwardOmittedColumnIndex flag P i //
      forwardInactiveColumnMan c.val = m} :=
    ⟨fun c q ↦ Subtype.ext (Subtype.ext
      (forwardInactiveColumnMan_injective flag i (c.property.trans q.property.symm)))⟩
  refine measure_iUnion_le_of_subsingleton _ _ _ fun t ↦
    measure_iUnion_le_of_subsingleton _ _ _ fun c ↦ ?_
  let S := forwardKeptCompetitorMass d t.val
  have hS : X / a ≤ S := hcomp t.val t.property
  have hpos : 0 < X / a := div_pos hX ha
  have h := reverseRelaxedColumnCrossBlocker_mass_le
    (fun q ↦ forwardInactiveColumnMan q ∉ P) t.val c.val hy0 hy1 hdx
    (v := forwardInactiveColumnThreshold d) (x := (diagonalPairAt d m).1)
    (fun q ↦ hx (forwardInactiveColumnMan q)) (hpos.trans_le hS)
  refine h.trans ?_
  change ENNReal.ofReal (dx * ((diagonalPairAt d (forwardInactiveColumnMan t.val.val)).1 /
    S ^ 2)) ≤ _
  rw [t.property, ← ENNReal.ofReal_mul ha.le,
    ← ENNReal.ofReal_mul (mul_nonneg ha.le (div_nonneg (hx j).1 hX.le))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ dx * ((diagonalPairAt d j).1 / (X / a) ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (hx j).1 (by positivity)
        (pow_le_pow_left₀ hpos.le hS _)) hdx
    _ = _ := by field_simp

end LennonPittelFormalization

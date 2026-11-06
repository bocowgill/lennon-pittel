module

public import LennonPittel.RotationPathIndependence

/-!
# Rank information in rotation traces

A moved man's new partner is the old partner of his successor in the cycle. Along a
path, the man's ranks before and after an occurrence of a label bound the ranks at
that label's two partners. The last label that moves him records his final partner.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n}

/-- The new partner of a man moved by a rotation is the old partner of his successor. -/
def rotationLabelNewPartner (r : RotationLabel n) (m : Fin n) : Option (Fin n) :=
  r.oldPartner (r.cycle m)

/-- The recorded new partner is the actual partner after elimination. -/
theorem rotationLabelNewPartner_eq {μ : Matching n} {ρ : Equiv.Perm (Fin n)}
    {m : Fin n} (hm : ρ m ≠ m) :
    rotationLabelNewPartner (rotationLabel μ ρ) m = some (eliminateRotation μ ρ m) := by
  have hnext : ρ (ρ m) ≠ ρ m := fun h ↦ hm (ρ.injective h)
  simp [rotationLabelNewPartner, rotationLabel, eliminateRotation_apply, hnext]

namespace RotationSequence

variable {μ ν τ : Matching n} {rs ss : List (Equiv.Perm (Fin n))}

/-- The first matching of a rotation sequence is stable. -/
theorem isStable_start (h : RotationSequence p μ rs ν) : IsStable p μ := by
  cases h with
  | nil hμ | cons hμ _ _ => exact hμ

/-- The last matching of a rotation sequence is stable. -/
theorem isStable_end (h : RotationSequence p μ rs ν) : IsStable p ν := by
  induction h with
  | nil hμ => exact hμ
  | cons _ _ _ ih => exact ih

/-- Two rotation sequences with a shared endpoint can be concatenated. -/
theorem append (h : RotationSequence p μ rs ν) (k : RotationSequence p ν ss τ) :
    RotationSequence p μ (rs ++ ss) τ := by
  induction h with
  | nil _ => exact k
  | cons hμ hρ _ ih => exact .cons hμ hρ (ih k)

/-- The labels of a concatenation are the concatenation of its two label traces. -/
theorem rotationLabels_append (h : RotationSequence p μ rs ν) :
    rotationLabels μ (rs ++ ss) = rotationLabels μ rs ++ rotationLabels ν ss := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ ih => simp only [List.cons_append, rotationLabels, ih]

/-- A realized rotation label moves at least one man. -/
theorem label_moves_someone (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs) : ∃ m, r.cycle m ≠ m := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | cons _ hρ _ ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨m, hm, _⟩ := hρ.isCycle
      exact ⟨m, hm⟩
    · exact ih hr

/-- A realized label records a strict rank increase for each man it moves, bounded by
the ranks at the start and end of the path. -/
theorem label_rank_bounds (h : RotationSequence p μ rs ν)
    {r : RotationLabel n} (hr : r ∈ rotationLabels μ rs)
    {m : Fin n} (hm : r.cycle m ≠ m) :
    ∃ old new, r.oldPartner m = some old ∧ rotationLabelNewPartner r m = some new ∧
      p.manRank m (μ m) ≤ p.manRank m old ∧ p.manRank m old < p.manRank m new ∧
      p.manRank m new ≤ p.manRank m (ν m) := by
  induction h with
  | nil _ => exact (List.not_mem_nil hr).elim
  | @cons μ ν ρ rs hμ hρ rest ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨μ m, eliminateRotation μ ρ m, ?_, rotationLabelNewPartner_eq hm,
        le_rfl, hρ.manRank_lt_eliminate_of_moved hm, rest.menWeaklyPrefer m⟩
      simp [rotationLabel, show ρ m ≠ m from hm]
    · obtain ⟨old, new, hold, hnew, hle, hlt, hend⟩ := ih hr
      have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
        .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
      exact ⟨old, new, hold, hnew, (hstep.menWeaklyPrefer m).trans hle, hlt, hend⟩

/-- A man's final partner is his initial partner or the new partner recorded by some
rotation in the trace. -/
theorem partner_eq_or_label_newPartner (h : RotationSequence p μ rs ν) (m : Fin n) :
    μ m = ν m ∨ ∃ r, r ∈ rotationLabels μ rs ∧ r.cycle m ≠ m ∧
      rotationLabelNewPartner r m = some (ν m) := by
  induction h with
  | nil _ => exact Or.inl rfl
  | @cons μ ν ρ rs _ _ _ ih =>
    rcases ih with he | ⟨r, hr, hm, hnew⟩
    · by_cases hm : ρ m = m
      · exact Or.inl (by simpa only [eliminateRotation_apply, hm] using he)
      · exact Or.inr ⟨rotationLabel μ ρ, List.mem_cons_self, hm,
          (rotationLabelNewPartner_eq hm).trans (congrArg some he)⟩
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hm, hnew⟩

/-- If either of two distinct labels occurs, there is a path from the same start
that contains one label but not the other. Take the prefix ending at the first
occurrence of either label. -/
theorem separating_prefix (h : RotationSequence p μ rs ν) {a b : RotationLabel n}
    (hne : a ≠ b) (hmem : a ∈ rotationLabels μ rs ∨ b ∈ rotationLabels μ rs) :
    ∃ τ ts, RotationSequence p μ ts τ ∧
      ((a ∈ rotationLabels μ ts ∧ b ∉ rotationLabels μ ts) ∨
        (b ∈ rotationLabels μ ts ∧ a ∉ rotationLabels μ ts)) := by
  classical
  induction h with
  | nil _ => exact (hmem.elim (List.not_mem_nil ·) (List.not_mem_nil ·)).elim
  | @cons μ _ ρ _ hμ hρ _ ih =>
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    by_cases ha : rotationLabel μ ρ = a
    · exact ⟨_, _, hstep, Or.inl (by simp [rotationLabels, ha, Ne.symm hne])⟩
    · by_cases hb : rotationLabel μ ρ = b
      · exact ⟨_, _, hstep, Or.inr (by simp [rotationLabels, hb, hne])⟩
      · simp only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or] at hmem
        obtain ⟨τ, ts, hts, hsep⟩ := ih hmem
        exact ⟨τ, ρ :: ts, .cons hμ hρ hts, by
          simpa only [rotationLabels, List.mem_cons, Ne.symm ha, Ne.symm hb, false_or]⟩

end RotationSequence

end LennonPittelFormalization

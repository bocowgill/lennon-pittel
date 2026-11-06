module

public import LennonPittel.RotationAntichain

/-!
# Simultaneously exposed rotations form an antichain

At any stable matching, the labels of the exposed rotations are pairwise incomparable.
The antichain bound then applies to any finite collection of these rotations.
-/

@[expose] public section

open StableMarriage

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ₀ μ : Matching n}

/-- The label of an exposed rotation is realized by extending a path to its matching. -/
def rotationOfExposed (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ)
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) : Rotation p μ₀ :=
  ⟨rotationLabel μ ρ, by
    obtain ⟨rs, hrs⟩ := exists_rotationSequence_of_manOptimal hopt hμ
    have hstep : RotationSequence p μ [ρ] (eliminateRotation μ ρ) :=
      .cons hμ hρ (.nil (hρ.isStable_eliminate hμ))
    refine ⟨_, rs ++ [ρ], hrs.append hstep, ?_⟩
    simp [hrs.rotationLabels_append, rotationLabels]⟩

/-- A rotation exposed at a stable matching has not already been eliminated there. -/
theorem rotationOfExposed_not_mem_eliminatedRotations (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) :
    rotationOfExposed hopt hμ hρ ∉ eliminatedRotations p μ₀ μ := by
  obtain ⟨m, hm, _⟩ := hρ.isCycle
  exact fun hr ↦ (not_le_of_gt (hρ.manRank_lt_eliminate_of_moved hm))
    ((mem_eliminatedRotations_iff_newRank_le hopt hμ (m := m) hm
      (rotationLabelNewPartner_eq hm)).mp hr)

/-- Cycles exposed at one stable matching embed in the rotation poset by their labels. -/
def exposedRotationsEmbedding (hopt : IsManOptimal p μ₀) (hμ : IsStable p μ) :
    {ρ : Equiv.Perm (Fin n) // IsExposedRotation p μ ρ} ↪ Rotation p μ₀ :=
  ⟨fun ρ ↦ rotationOfExposed hopt hμ ρ.property, fun _ _ h ↦
    Subtype.ext (congrArg (fun r : Rotation p μ₀ ↦ r.val.cycle) h)⟩

/-- All rotations exposed at one stable matching form an antichain in the rotation poset. -/
theorem isAntichain_range_exposedRotationsEmbedding (hopt : IsManOptimal p μ₀)
    (hμ : IsStable p μ) :
    IsAntichain (· ≤ ·) (Set.range (exposedRotationsEmbedding hopt hμ)) := by
  rintro _ ⟨r, rfl⟩ _ ⟨s, rfl⟩ hne hrs
  exact rotationOfExposed_not_mem_eliminatedRotations hopt hμ r.property
    ((Rotation.lt_iff_before_exposure hopt hne).mp (lt_of_le_of_ne hrs hne)
      μ hμ s.property rfl)

/-- A stable matching with `A.card` distinct exposed rotations gives at least
`2 ^ A.card` stable matchings for the profile. -/
theorem pow_card_exposedRotations_le_numStableMatchings (hμ : IsStable p μ)
    (A : Finset (Equiv.Perm (Fin n))) (hA : ∀ ρ ∈ A, IsExposedRotation p μ ρ) :
    2 ^ A.card ≤ numStableMatchings p := by
  obtain ⟨μ₀, hopt⟩ := exists_manOptimal_of_exists_stable ⟨μ, hμ⟩
  let e : ↥A ↪ {ρ : Equiv.Perm (Fin n) // IsExposedRotation p μ ρ} :=
    ⟨fun ρ ↦ ⟨ρ.val, hA ρ.val ρ.property⟩, fun _ _ h ↦
      Subtype.ext (congrArg (Subtype.val :
        {ρ : Equiv.Perm (Fin n) // IsExposedRotation p μ ρ} → _) h)⟩
  let B := A.attach.map (e.trans (exposedRotationsEmbedding hopt hμ))
  have hB : IsAntichain (· ≤ ·) (B : Set (Rotation p μ₀)) :=
    (isAntichain_range_exposedRotationsEmbedding hopt hμ).subset (by
      intro r hr
      obtain ⟨ρ, _, rfl⟩ := Finset.mem_map.mp (show r ∈ B from hr)
      exact ⟨e ρ, rfl⟩)
  simpa only [B, Finset.card_map, Finset.card_attach] using
    pow_card_rotationAntichain_le_numStableMatchings hopt B hB

end LennonPittelFormalization

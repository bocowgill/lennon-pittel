module

public import LennonPittel.CoexposureGoodScores
public import LennonPittel.RotationTrace

/-!
# The deterministic part of the participation clock

Every rotation changes exactly its support's wives. The log potential
telescopes over those changes, and strict increases in the ranks of the
moved men bound total participation on every legal path.
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

/-- The total number of moved pairs along a path, with multiplicity. -/
def rotationParticipation {n : ℕ} (rs : List (Equiv.Perm (Fin n))) : ℕ :=
  (rs.map fun σ ↦ σ.support.card).sum

/-- The sum of negative logarithms of the women's current spouse scores. -/
noncomputable def femaleLogPotential {n : ℕ} (x : ScoreProfile n) (μ : Matching n) : ℝ :=
  ∑ j, -Real.log (femaleSpouseScore x μ j)

/-- The relative change of the spouse score of the old wife of man `i`. -/
noncomputable def femaleRotationRatio {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  femaleSpouseScore x (eliminateRotation μ ρ) (μ i) / femaleSpouseScore x μ (μ i)

/-- The old wife of an unmoved man retains her score. -/
theorem femaleSpouseScore_eliminate_eq_of_not_mem_support {n : ℕ} (x : ScoreProfile n)
    (μ : Matching n) (ρ : Equiv.Perm (Fin n)) {i : Fin n} (hi : i ∉ ρ.support) :
    femaleSpouseScore x (eliminateRotation μ ρ) (μ i) = femaleSpouseScore x μ (μ i) := by
  have hfix : ρ i = i := by simpa only [Equiv.Perm.mem_support, not_not] using hi
  have hpartner : eliminateRotation μ ρ i = μ i := by rw [eliminateRotation_apply, hfix]
  unfold femaleSpouseScore
  rw [(Equiv.symm_apply_eq (eliminateRotation μ ρ)).mpr hpartner.symm, μ.symm_apply_apply]

open scoped Classical in
/-- The one-step log progress is exactly the sum of log score ratios on the support. -/
theorem femaleLogPotential_eliminate_sub {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) (hx : ∀ j i, 0 < x (.inr j) i) :
    femaleLogPotential x (eliminateRotation μ ρ) - femaleLogPotential x μ =
      ∑ i ∈ ρ.support, -Real.log (femaleRotationRatio x μ ρ i) := by
  let ν := eliminateRotation μ ρ
  have he (M : Matching n) : femaleLogPotential x M =
      ∑ i, -Real.log (femaleSpouseScore x M (μ i)) :=
    (Equiv.sum_comp μ fun j ↦ -Real.log (femaleSpouseScore x M j)).symm
  rw [he ν, he μ, ← Finset.sum_sub_distrib]
  have hsupport : Finset.univ.filter (· ∈ ρ.support) = ρ.support := by ext; simp
  rw [← hsupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ ρ.support
  · rw [ite_eq_left hi]
    unfold femaleRotationRatio
    have ho : 0 < femaleSpouseScore x μ (μ i) := hx _ _
    have hn : 0 < femaleSpouseScore x ν (μ i) := hx _ _
    rw [Real.log_div hn.ne' ho.ne']
    ring
  · rw [ite_eq_right hi, femaleSpouseScore_eliminate_eq_of_not_mem_support x μ ρ hi, sub_self]

/-- The sum of the individual log losses in a path, read at their actual starting matchings. -/
noncomputable def rotationPathFemaleLogLoss {n : ℕ} (x : ScoreProfile n) :
    Matching n → List (Equiv.Perm (Fin n)) → ℝ
  | _, [] => 0
  | μ, ρ :: rs => (∑ i ∈ ρ.support, -Real.log (femaleRotationRatio x μ ρ i)) +
      rotationPathFemaleLogLoss x (eliminateRotation μ ρ) rs

/-- The log losses telescope along every legal rotation sequence. -/
theorem RotationSequence.femaleLogPotential_sub_eq_pathLoss {n : ℕ} {p : Profile n}
    {μ ν : Matching n} {rs : List (Equiv.Perm (Fin n))}
    (h : RotationSequence p μ rs ν) (x : ScoreProfile n) (hx : ∀ j i, 0 < x (.inr j) i) :
    femaleLogPotential x ν - femaleLogPotential x μ = rotationPathFemaleLogLoss x μ rs := by
  induction h with
  | nil => simp [rotationPathFemaleLogLoss]
  | @cons μ ν ρ rs _ _ _ ih =>
    rw [rotationPathFemaleLogLoss, ← femaleLogPotential_eliminate_sub x μ ρ hx, ← ih]
    ring

private def rankPotential {n : ℕ} (p : Profile n) (μ : Matching n) : ℕ :=
  ∑ m, (p.manRank m (μ m)).val

open scoped Classical in
private theorem rankPotential_add_support_le {n : ℕ} {p : Profile n} {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation p μ ρ) :
    rankPotential p μ + ρ.support.card ≤ rankPotential p (eliminateRotation μ ρ) := by
  have hc : ρ.support.card = ∑ i : Fin n, if i ∈ ρ.support then 1 else 0 := by
    have hsupport : Finset.univ.filter (· ∈ ρ.support) = ρ.support := by ext; simp
    rw [← Finset.sum_filter, hsupport]
    simp
  rw [hc, rankPotential, rankPotential, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ ρ.support
  · rw [ite_eq_left hi]
    exact hρ.manRank_lt_eliminate_of_moved (Equiv.Perm.mem_support.mp hi)
  · have he : ρ i = i := by simpa only [Equiv.Perm.mem_support, not_not] using hi
    simp only [ite_eq_right hi, add_zero, eliminateRotation_apply, he, le_refl]

private theorem RotationSequence.participation_add_rankPotential_le {n : ℕ} {p : Profile n}
    {μ ν : Matching n} {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    rankPotential p μ + rotationParticipation rs ≤ rankPotential p ν := by
  induction h with
  | nil => simp [rotationParticipation]
  | @cons μ ν ρ rs _ hρ _ ih =>
    simp only [rotationParticipation, List.map_cons, List.sum_cons] at ih ⊢
    rw [← add_assoc]
    exact (Nat.add_le_add_right (rankPotential_add_support_le hρ) _).trans ih

/-- The deterministic horizon bound counts every move, even if a man moves repeatedly. -/
theorem RotationSequence.participation_le {n : ℕ} {p : Profile n} {μ ν : Matching n}
    {rs : List (Equiv.Perm (Fin n))} (h : RotationSequence p μ rs ν) :
    rotationParticipation rs ≤ n * (n - 1) := by
  refine (Nat.le_add_left _ _).trans (h.participation_add_rankPotential_le.trans ?_)
  calc
    rankPotential p ν ≤ ∑ _m : Fin n, (n - 1) :=
      Finset.sum_le_sum fun m _ ↦ Nat.le_pred_of_lt (p.manRank m (ν m)).isLt
    _ = _ := by simp

/-- Each female spouse score weakly decreases at a rank-exposed rotation. -/
theorem femaleSpouseScore_eliminate_le {n : ℕ} (x : ScoreProfile n) {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) (j : Fin n) :
    femaleSpouseScore x (eliminateRotation μ ρ) j ≤ femaleSpouseScore x μ j := by
  apply le_of_not_gt
  intro h
  exact (not_lt_of_ge (hρ.womanRank_eliminate_le j))
    ((rankPermutation_lt_iff (ht j) _ _).mpr h)

/-- The female total weakly decreases at each rank-exposed rotation. -/
theorem femaleSpouseTotal_eliminate_le {n : ℕ} (x : ScoreProfile n) {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) :
    femaleSpouseTotal x (eliminateRotation μ ρ) ≤ femaleSpouseTotal x μ :=
  Finset.sum_le_sum fun j _ ↦ femaleSpouseScore_eliminate_le x hρ ht j

/-- The score ratio has the unit-interval range required by the log clock. -/
theorem femaleRotationRatio_mem_Ioc {n : ℕ} (x : ScoreProfile n) {μ : Matching n}
    {ρ : Equiv.Perm (Fin n)} (hρ : IsExposedRotation (profileOfScores x) μ ρ)
    (ht : ∀ j, Function.Injective (x (.inr j))) (hx : ∀ j i, 0 < x (.inr j) i) (i : Fin n) :
    femaleRotationRatio x μ ρ i ∈ Set.Ioc 0 1 :=
  ⟨div_pos (hx _ _) (hx _ _),
    (div_le_one (hx _ _)).mpr (femaleSpouseScore_eliminate_le x hρ ht (μ i))⟩

open scoped Classical in
/-- The total score drop is bounded by the rotation length times a bound
on every old female spouse score. -/
theorem femaleSpouseTotal_drop_le_support_mul {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {B : ℝ} (hB : ∀ j, femaleSpouseScore x μ j ≤ B)
    (hx : ∀ j, 0 ≤ femaleSpouseScore x (eliminateRotation μ ρ) j) :
    femaleSpouseTotal x μ - femaleSpouseTotal x (eliminateRotation μ ρ) ≤
      (ρ.support.card : ℝ) * B := by
  have he (M : Matching n) : femaleSpouseTotal x M = ∑ i, femaleSpouseScore x M (μ i) :=
    (Equiv.sum_comp μ (femaleSpouseScore x M)).symm
  have hsupport : Finset.univ.filter (· ∈ ρ.support) = ρ.support := by ext; simp
  rw [he μ, he (eliminateRotation μ ρ), ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, if i ∈ ρ.support then B else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ ρ.support
      · rw [ite_eq_left hi]
        exact (sub_le_self _ (hx (μ i))).trans (hB (μ i))
      · rw [ite_eq_right hi, femaleSpouseScore_eliminate_eq_of_not_mem_support x μ ρ hi, sub_self]
    _ = _ := by rw [← Finset.sum_filter, hsupport]; simp [nsmul_eq_mul]

/-- Expressing the old scores as shares makes the drop a relative bound. -/
theorem femaleSpouseTotal_drop_le_support_mul_share {n : ℕ} (x : ScoreProfile n) (μ : Matching n)
    (ρ : Equiv.Perm (Fin n)) {B : ℝ} (hY : 0 < femaleSpouseTotal x μ)
    (hB : ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ B)
    (hx : ∀ j, 0 ≤ femaleSpouseScore x (eliminateRotation μ ρ) j) :
    femaleSpouseTotal x μ - femaleSpouseTotal x (eliminateRotation μ ρ) ≤
      ((ρ.support.card : ℝ) * B) * femaleSpouseTotal x μ := by
  rw [mul_assoc]
  exact femaleSpouseTotal_drop_le_support_mul x μ ρ (fun j ↦ (div_le_iff₀ hY).mp (hB j)) hx

end LennonPittelFormalization

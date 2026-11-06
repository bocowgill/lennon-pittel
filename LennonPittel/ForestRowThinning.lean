module

public import LennonPittel.ForestProductProbability
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Independent row thinning and the sole-cycle bound

Couple each reference row to the original row so that it can only delete
an arc. Erasing the support rows of a prescribed sole cycle then leaves
an independent forest comparison on the other rows.
-/

@[expose] public section

open scoped BigOperators Classical

namespace LennonPittelFormalization

/-- The joint row weight with the original outcome first. A retained arc keeps its target,
and all discarded arc mass is placed at the absent outcome. -/
private noncomputable def thinningWeight {ι : Type*} [DecidableEq ι]
    (w v : Option ι → ℝ) : Option ι → Option ι → ℝ
  | none, none => w none
  | none, some _ => 0
  | some i, none => w (some i) - v (some i)
  | some i, some j => if i = j then v (some j) else 0

private theorem thinningWeight_nonneg {ι : Type*} [DecidableEq ι]
    {w v : Option ι → ℝ} (hw : ∀ a, 0 ≤ w a) (hv : ∀ a, 0 ≤ v a)
    (hle : ∀ i, v (some i) ≤ w (some i)) (a b : Option ι) :
    0 ≤ thinningWeight w v a b := by
  cases a <;> cases b <;> simp [thinningWeight, hw, sub_nonneg.mpr, hle]
  split <;> simp [hv]

private theorem sum_thinningWeight_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : Option ι → ℝ) (a : Option ι) :
    (∑ b, thinningWeight w v a b) = w a := by
  rw [Fintype.sum_option]
  cases a <;> simp [thinningWeight]

private theorem sum_thinningWeight_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w v : Option ι → ℝ} (hw : ∑ a, w a = 1) (hv : ∑ a, v a = 1) (b : Option ι) :
    (∑ a, thinningWeight w v a b) = v b := by
  rw [Fintype.sum_option] at hw hv ⊢
  cases b with
  | none =>
    simp only [thinningWeight, Finset.sum_sub_distrib]
    rw [← add_sub_assoc, hw, ← hv, add_sub_cancel_right]
  | some j =>
    simp [thinningWeight, eq_comm]

private theorem thinningWeight_ne_zero_of_arc {ι : Type*} [DecidableEq ι]
    {w v : Option ι → ℝ} {a : Option ι} {j : ι}
    (h : thinningWeight w v a (some j) ≠ 0) : a = some j := by
  cases a with
  | none => simp [thinningWeight] at h
  | some k =>
    by_contra hk
    exact h (ite_eq_right fun hkj ↦ hk (congrArg some hkj))

/-- An arc-deletion-increasing observable increases in expectation when the row
probabilities of all arcs decrease. The rows in both models are independent. -/
theorem sum_product_le_of_arc_thinning {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : ι → Option ι → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hv : ∀ i a, 0 ≤ v i a)
    (hw1 : ∀ i, ∑ a, w i a = 1) (hv1 : ∀ i, ∑ a, v i a = 1)
    (hle : ∀ i j, v i (some j) ≤ w i (some j)) (F : (ι → Option ι) → ℝ)
    (hmono : ∀ f g, (∀ i j, g i = some j → f i = some j) → F f ≤ F g) :
    (∑ f, (∏ i, w i (f i)) * F f) ≤ ∑ g, (∏ i, v i (g i)) * F g := by
  let c (f g : ι → Option ι) := ∏ i, thinningWeight (w i) (v i) (f i) (g i)
  have hc0 (f g : ι → Option ι) : 0 ≤ c f g :=
    Finset.prod_nonneg fun i _ ↦ thinningWeight_nonneg (hw i) (hv i) (hle i) _ _
  have hm1 (f : ι → Option ι) : (∑ g, c f g) = ∏ i, w i (f i) := by
    dsimp [c]
    rw [← Fintype.prod_sum]
    simp only [sum_thinningWeight_right]
  have hm2 (g : ι → Option ι) : (∑ f, c f g) = ∏ i, v i (g i) := by
    dsimp [c]
    rw [← Fintype.prod_sum (fun i (a : Option ι) ↦ thinningWeight (w i) (v i) a (g i))]
    simp only [sum_thinningWeight_left (hw1 _) (hv1 _)]
  have hobs (f g : ι → Option ι) : c f g * F f ≤ c f g * F g := by
    by_cases h : c f g = 0
    · simp [h]
    apply mul_le_mul_of_nonneg_left _ (hc0 f g)
    apply hmono
    intro i j hij
    apply thinningWeight_ne_zero_of_arc
    intro hzero
    apply h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa only [hij] using hzero
  calc
    _ = ∑ f, ∑ g, c f g * F f := by simp_rw [← Finset.sum_mul, hm1]
    _ ≤ ∑ f, ∑ g, c f g * F g :=
      Finset.sum_le_sum fun f _ ↦ Finset.sum_le_sum fun g _ ↦ hobs f g
    _ = _ := by rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hm2]

/-- Every cycle in an arc-deleted graph is also a cycle in the original graph. -/
theorem isAcyclicSuccessor_of_arc_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : ι → Option ι} (hfg : ∀ i j, g i = some j → f i = some j)
    (hf : IsAcyclicSuccessor f) : IsAcyclicSuccessor g := by
  intro σ hσ
  exact hf σ ⟨hσ.1, fun i hi ↦ hfg i (σ i) (hσ.2 i hi)⟩

/-- Independent row thinning can only increase the no-cycle probability. -/
theorem forestProductMass_le_of_arc_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : ι → Option ι → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hv : ∀ i a, 0 ≤ v i a)
    (hw1 : ∀ i, ∑ a, w i a = 1) (hv1 : ∀ i, ∑ a, v i a = 1)
    (hle : ∀ i j, v i (some j) ≤ w i (some j)) :
    forestProductMass w ≤ forestProductMass v := by
  unfold forestProductMass
  apply sum_product_le_of_arc_thinning w v hw hv hw1 hv1 hle
  intro f g hfg
  by_cases hf : IsAcyclicSuccessor f
  · simp [hf, isAcyclicSuccessor_of_arc_subset hfg hf]
  · by_cases hg : IsAcyclicSuccessor g <;> simp [hf, hg]

/-- Remove all outgoing arcs from the chosen rows, preserving other rows exactly. -/
def eraseSuccessorRows {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Option ι) (i : ι) : Option ι :=
  if i ∈ s then none else f i

/-- Replace the row distribution by the absent outcome on the chosen rows. -/
noncomputable def eraseSuccessorWeights {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → Option ι → ℝ) (i : ι) (a : Option ι) : ℝ :=
  if i ∈ s then (if a = none then 1 else 0) else w i a

theorem eraseSuccessorWeights_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {w : ι → Option ι → ℝ} (hw : ∀ i a, 0 ≤ w i a) (i : ι) (a : Option ι) :
    0 ≤ eraseSuccessorWeights s w i a := by
  by_cases hi : i ∈ s <;> cases a <;> simp [eraseSuccessorWeights, hi, hw]

theorem sum_eraseSuccessorWeights {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    {w : ι → Option ι → ℝ} (hw : ∀ i, ∑ a, w i a = 1) (i : ι) :
    (∑ a, eraseSuccessorWeights s w i a) = 1 := by
  by_cases hi : i ∈ s <;> simp [eraseSuccessorWeights, hi, hw]

@[simp] theorem eraseSuccessorWeights_some {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → Option ι → ℝ) (i j : ι) :
    eraseSuccessorWeights s w i (some j) = if i ∈ s then 0 else w i (some j) := by
  simp [eraseSuccessorWeights]

/-- A prescribed permutation is the only directed cycle in the partial successor map. -/
def IsSoleDirectedCycle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Option ι) (σ : Equiv.Perm ι) : Prop :=
  RealizesDirectedCycle f σ ∧ ∀ τ, RealizesDirectedCycle f τ → τ = σ

/-- Probability of having exactly the prescribed cycle under independent row weights. -/
noncomputable def soleDirectedCycleProductMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (σ : Equiv.Perm ι) : ℝ :=
  ∑ f : ι → Option ι, (∏ i, w i (f i)) * (if IsSoleDirectedCycle f σ then 1 else 0)

/-- Erasing the support of the sole directed cycle leaves a forest. -/
theorem IsSoleDirectedCycle.isAcyclicSuccessor_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Option ι} {σ : Equiv.Perm ι} (h : IsSoleDirectedCycle f σ) :
    IsAcyclicSuccessor (eraseSuccessorRows σ.support f) := by
  intro τ hτ
  have hnot (i : ι) (hi : i ∈ τ.support) : i ∉ σ.support := by
    intro his
    have hArc := hτ.2 i hi
    simp [eraseSuccessorRows, his] at hArc
  have hτf : RealizesDirectedCycle f τ :=
    ⟨hτ.1, fun i hi ↦ by simpa [eraseSuccessorRows, hnot i hi] using hτ.2 i hi⟩
  have hτσ := h.2 τ hτf
  subst τ
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun hs ↦ h.1.1.ne_one (Equiv.Perm.support_eq_empty_iff.mp hs))
  exact hnot i hi hi

/-- Conditioning prescribed rows to equal fixed outcomes leaves the product law
on the other rows. Erasing the prescribed rows exhibits this factorization. -/
theorem sum_product_prescribed_rows_erase_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Option ι → ℝ) (s : Finset ι) (a : ι → Option ι)
    (F : (ι → Option ι) → ℝ) :
    (∑ f : ι → Option ι, (∏ i, w i (f i)) *
        (if ∀ i ∈ s, f i = a i then F (eraseSuccessorRows s f) else 0)) =
      (∏ i ∈ s, w i (a i)) * ∑ g : ι → Option ι,
        (∏ i, eraseSuccessorWeights s w i (g i)) * F g := by
  let E : Finset (ι → Option ι) := Finset.univ.filter (fun f ↦ ∀ i ∈ s, f i = a i)
  let G : Finset (ι → Option ι) := Finset.univ.filter (fun g ↦ ∀ i ∈ s, g i = none)
  let restore (g : ι → Option ι) (i : ι) : Option ι := if i ∈ s then a i else g i
  have hE (f : ι → Option ι) : f ∈ E ↔ ∀ i ∈ s, f i = a i := by simp [E]
  have hG (g : ι → Option ι) : g ∈ G ↔ ∀ i ∈ s, g i = none := by simp [G]
  have hprod (g : ι → Option ι) (hg : g ∈ G) :
      (∏ i, eraseSuccessorWeights s w i (g i)) = ∏ i ∈ sᶜ, w i (g i) := by
    rw [← Finset.prod_mul_prod_compl s]
    have hleft : (∏ i ∈ s, eraseSuccessorWeights s w i (g i)) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by simp [eraseSuccessorWeights, hi, (hG g).mp hg i hi]
    rw [hleft, one_mul]
    exact Finset.prod_congr rfl fun i hi ↦ by
      simp [eraseSuccessorWeights, Finset.mem_compl.mp hi]
  have hzero (g : ι → Option ι) (hg : g ∉ G) :
      (∏ i, eraseSuccessorWeights s w i (g i)) = 0 := by
    have hn : ¬ ∀ i ∈ s, g i = none := fun h ↦ hg ((hG g).mpr h)
    push Not at hn
    obtain ⟨i, hi, hgi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [eraseSuccessorWeights, hi, hgi])
  calc
    _ = ∑ f ∈ E, (∏ i, w i (f i)) * F (eraseSuccessorRows s f) := by
      unfold E
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun f _ ↦ by split <;> simp
    _ = ∑ g ∈ G, (∏ i ∈ s, w i (a i)) * ((∏ i ∈ sᶜ, w i (g i)) * F g) := by
      refine Finset.sum_bij' (fun f _ ↦ eraseSuccessorRows s f) (fun g _ ↦ restore g)
        (fun f _ ↦ (hG _).mpr fun i hi ↦ by simp [eraseSuccessorRows, hi])
        (fun g _ ↦ (hE _).mpr fun i hi ↦ by simp [restore, hi]) ?_ ?_ ?_
      · intro f hf
        funext i
        by_cases hi : i ∈ s <;> simp [restore, eraseSuccessorRows, hi, (hE f).mp hf]
      · intro g hg
        funext i
        by_cases hi : i ∈ s <;> simp [restore, eraseSuccessorRows, hi, (hG g).mp hg]
      · intro f hf
        rw [← Finset.prod_mul_prod_compl s, mul_assoc]
        congr 1
        · exact Finset.prod_congr rfl fun i hi ↦ congrArg (w i) ((hE f).mp hf i hi)
        · congr 1
          exact Finset.prod_congr rfl fun i hi ↦ by
            simp [eraseSuccessorRows, Finset.mem_compl.mp hi]
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      unfold G
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : g ∈ G
      · rw [ite_eq_left ((hG g).mp hg), hprod g hg]
      · rw [ite_eq_right (fun h ↦ hg ((hG g).mpr h)), hzero g hg, zero_mul]

/-- A prescribed cycle can be the sole cycle only if the independent graph obtained
by erasing its support rows is acyclic. -/
theorem soleDirectedCycleProductMass_le_arc_prod_mul_forestProductMass
    {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → Option ι → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (σ : Equiv.Perm ι) :
    soleDirectedCycleProductMass w σ ≤
      (∏ i ∈ σ.support, w i (some (σ i))) *
        forestProductMass (eraseSuccessorWeights σ.support w) := by
  unfold soleDirectedCycleProductMass forestProductMass
  rw [← sum_product_prescribed_rows_erase_eq w σ.support (fun i ↦ some (σ i))
    (fun g ↦ if IsAcyclicSuccessor g then 1 else 0)]
  apply Finset.sum_le_sum
  intro f _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ ↦ hw i (f i))
  by_cases hf : IsSoleDirectedCycle f σ
  · rw [ite_eq_left hf, ite_eq_left hf.1.2, ite_eq_left hf.isAcyclicSuccessor_erase]
  · rw [ite_eq_right hf]
    split
    · split <;> simp
    · exact le_rfl

end LennonPittelFormalization

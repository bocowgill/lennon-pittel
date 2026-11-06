module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Rank-one reference forest matrix

The reference adjacency matrix is a rank-one outer product with its
diagonal removed. Its determinant formula gives an acyclicity bound
controlled by missing mass and a square-weight correction.
-/

@[expose] public section

namespace LennonPittelFormalization

/-- Rank-one entries off the diagonal and zero self-arcs. -/
def rankOneOffDiagonal {ι : Type*} [DecidableEq ι] (q p : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ if i = j then 0 else q i * p j

/-- The reference determinant, obtained by factoring its positive diagonal
and applying the rank-one determinant lemma. -/
theorem det_one_sub_rankOneOffDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q p : ι → ℝ) (hu : ∀ i, 0 ≤ q i * p i) :
    (1 - rankOneOffDiagonal q p).det =
      (∏ i, (1 + q i * p i)) * (1 - ∑ i, q i * p i / (1 + q i * p i)) := by
  let v : ι → ℝ := fun i ↦ -(q i / (1 + q i * p i))
  have hd (i : ι) : 1 + q i * p i ≠ 0 := ne_of_gt (by linarith only [hu i])
  have hfactor : 1 - rankOneOffDiagonal q p =
      Matrix.diagonal (fun i ↦ 1 + q i * p i) *
        (1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit p) := by
    ext i j
    rw [Matrix.diagonal_mul, ← Matrix.vecMulVec_eq Unit]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      rankOneOffDiagonal, v]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, sub_zero]
      field_simp [hd i]
      ring
    · simp only [ite_eq_right hij, zero_sub, zero_add]
      field_simp [hd i]
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : p ⬝ᵥ v = -(∑ i, q i * p i / (1 + q i * p i)) := by
    rw [dotProduct, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v]
    simp only [mul_neg, ← mul_div_assoc, mul_comm (p i) (q i)]
  rw [hdot, sub_eq_add_neg]

/-- A mass defect and a square-weight correction bound the reference determinant. -/
theorem det_one_sub_rankOneOffDiagonal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q p : ι → ℝ) (hu : ∀ i, 0 ≤ q i * p i) (hsum : ∑ i, q i * p i ≤ 1) :
    (1 - rankOneOffDiagonal q p).det ≤
      Real.exp 1 * ((1 - ∑ i, q i * p i) + ∑ i, (q i * p i) ^ 2) := by
  rw [det_one_sub_rankOneOffDiagonal q p hu]
  let u : ι → ℝ := fun i ↦ q i * p i
  change (∏ i, (1 + u i)) * (1 - ∑ i, u i / (1 + u i)) ≤
    Real.exp 1 * ((1 - ∑ i, u i) + ∑ i, (u i) ^ 2)
  have hu' (i : ι) : 0 ≤ u i := hu i
  have hfrac (i : ι) : u i - (u i) ^ 2 ≤ u i / (1 + u i) := by
    apply (le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (hu' i))).2
    nlinarith only [mul_nonneg (sq_nonneg (u i)) (hu' i)]
  have hbracket : 1 - ∑ i, u i / (1 + u i) ≤ (1 - ∑ i, u i) + ∑ i, (u i) ^ 2 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hfrac i)
    rw [Finset.sum_sub_distrib] at h
    linarith only [h]
  have hprod : ∏ i, (1 + u i) ≤ Real.exp 1 := by
    calc
      ∏ i, (1 + u i) ≤ ∏ i, Real.exp (u i) :=
        Finset.prod_le_prod₀ (fun i _ ↦ add_nonneg zero_le_one (hu' i))
          (fun i _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (u i))
      _ = Real.exp (∑ i, u i) := (Real.exp_sum Finset.univ u).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
  exact (mul_le_mul_of_nonneg_left hbracket
    (Finset.prod_nonneg (fun i _ ↦ add_nonneg zero_le_one (hu' i)))).trans
      (mul_le_mul_of_nonneg_right hprod
        (add_nonneg (sub_nonneg.mpr hsum) (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (u i)))))

/-- Restricting to the complement of a prescribed cycle adds its weight to
the forest error budget. -/
theorem det_one_sub_rankOneOffDiagonal_complement_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (p δ : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hδ : ∀ i, δ i ∈ Set.Icc (0 : ℝ) 1) :
    (1 - rankOneOffDiagonal (fun i : {i // i ∉ S} ↦ 1 - δ i.val) (fun i ↦ p i.val)).det ≤
      Real.exp 1 * ((∑ i, p i * δ i) + (∑ i, (p i) ^ 2) + ∑ i ∈ S, p i) := by
  let u : ι → ℝ := fun i ↦ (1 - δ i) * p i
  have hu (i : ι) : 0 ≤ u i := mul_nonneg (sub_nonneg.mpr (hδ i).2) (hp i)
  have hup (i : ι) : u i ≤ p i :=
    mul_le_of_le_one_left (hp i) (sub_le_self 1 (hδ i).1)
  have hsub (f : ι → ℝ) : (∑ i : {i // i ∉ S}, f i.val) = ∑ i ∈ Sᶜ, f i :=
    (Finset.sum_subtype Sᶜ (fun _ ↦ Finset.mem_compl) f).symm
  have hcomp (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) : ∑ i ∈ Sᶜ, f i ≤ ∑ i, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hf i)
  have husum : ∑ i : {i // i ∉ S}, u i.val ≤ 1 := by
    rw [hsub]
    exact (hcomp u hu).trans (hsum ▸ Finset.sum_le_sum (fun i _ ↦ hup i))
  refine (det_one_sub_rankOneOffDiagonal_le
    (fun i : {i // i ∉ S} ↦ 1 - δ i.val) (fun i ↦ p i.val)
    (fun i ↦ hu i.val) husum).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  change (1 - ∑ i : {i // i ∉ S}, u i.val) + ∑ i : {i // i ∉ S}, (u i.val) ^ 2 ≤ _
  rw [hsub u, hsub (fun i ↦ (u i) ^ 2)]
  have hdef : 1 - ∑ i ∈ Sᶜ, u i =
      (∑ i ∈ S, p i) + ∑ i ∈ Sᶜ, p i * δ i := by
    have hsplit := S.sum_add_sum_compl p
    simp only [u, sub_mul, one_mul, Finset.sum_sub_distrib, mul_comm (δ _) (p _)]
    linarith only [hsum, hsplit]
  have hsq : ∑ i ∈ Sᶜ, (u i) ^ 2 ≤ ∑ i, (p i) ^ 2 :=
    (Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (hu i) (hup i) 2)).trans
      (hcomp (fun i ↦ (p i) ^ 2) (fun i ↦ sq_nonneg (p i)))
  rw [hdef]
  linarith only [hsq, hcomp (fun i ↦ p i * δ i) (fun i ↦ mul_nonneg (hp i) (hδ i).1)]

end LennonPittelFormalization

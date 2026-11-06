module

public import LennonPittel.Model
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic

/-!
# The law of ranks of independent real scores

Independent atomless scores are almost surely distinct. Permuting their candidate labels
preserves the joint law and permutes the rank outcomes transitively, so every rank permutation
has the same probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LennonPittelFormalization

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- The scores in a finite row of independent atomless real draws are almost surely distinct. -/
theorem ae_injective_iid (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ), Function.Injective (x : Fin n → ℝ) := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  have hind : iIndepFun (fun i (x : Fin n → ℝ) ↦ x i) law :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ ↦ hij
  have hi := (measurable_pi_apply i : Measurable (fun x : Fin n → ℝ ↦ x i))
  have hj := (measurable_pi_apply j : Measurable (fun x : Fin n → ℝ ↦ x j))
  -- Two distinct coordinates have product law, whose diagonal has measure zero.
  have hpair : law.map (fun x ↦ (x i, x j)) = μ.prod μ :=
    ((indepFun_iff_map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable).1
      (hind.indepFun hij)).trans
        (congrArg₂ Measure.prod (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
          (measurePreserving_eval (fun _ : Fin n ↦ μ) j).map_eq)
  let diagonal : Set (ℝ × ℝ) := {z | z.1 = z.2}
  have hd : MeasurableSet diagonal := measurableSet_eq_fun measurable_fst measurable_snd
  have hnull : (μ.prod μ) diagonal = 0 := by
    rw [Measure.prod_apply hd]
    have hsection (u : ℝ) : Prod.mk u ⁻¹' diagonal = {u} :=
      Set.ext fun _ ↦ eq_comm
    simp [hsection]
  have hpull : law {x | x i = x j} = 0 := by
    rw [← hpair, Measure.map_apply (hi.prodMk hj) hd] at hnull
    exact hnull
  exact ae_iff.2 (by simpa [hij] using hpull)

private theorem perm_eq_of_lt_iff {n : ℕ} {p q : Equiv.Perm (Fin n)}
    (h : ∀ i j, p i < p j ↔ q i < q j) : p = q := by
  let f := fun i ↦ q (p.symm i)
  have hf : StrictMono f := fun i j hij ↦ (h (p.symm i) (p.symm j)).1
    (by simpa using hij)
  exact Equiv.ext fun i ↦ by
    simpa [f] using (hf.id_le (p i)).antisymm (hf.le_id (p i))

/-- Ranking independent atomless real draws gives the uniform law on rank permutations. -/
theorem measurePreserving_rank_of_iid {n : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    {r : (Fin n → ℝ) → Equiv.Perm (Fin n)} (hr : Measurable r)
    (hcmp : ∀ x, Function.Injective x → ∀ i j, r x i < r x j ↔ x i < x j) :
    MeasurePreserving r (Measure.pi fun _ : Fin n ↦ μ)
      (PMF.fintypeUniform (Equiv.Perm (Fin n))).toMeasure := by
  let law : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ μ
  let ν : Measure (Equiv.Perm (Fin n)) := law.map r
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (law.map r))
  -- Reindex the candidates so that the chamber for p maps to the chamber for q.
  have hequal (p q : Equiv.Perm (Fin n)) : ν {p} = ν {q} := by
    let e : Equiv.Perm (Fin n) := q.trans p.symm
    let reindex := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e.symm
    have hm : MeasurePreserving reindex law law :=
      measurePreserving_piCongrLeft (fun _ : Fin n ↦ μ) e.symm
    have he (x : Fin n → ℝ) (i : Fin n) : reindex x i = x (e i) := by
      simp [reindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    have hcongr : r ⁻¹' ({p} : Set (Equiv.Perm (Fin n))) =ᶠ[ae law] reindex ⁻¹' (r ⁻¹' {q}) :=
      (ae_injective_iid μ n).mono fun x hx ↦ by
        have hre : r (reindex x) = e.trans (r x) := perm_eq_of_lt_iff fun i j ↦
          (hcmp (reindex x) (by
            simpa only [Function.Injective, Function.comp_apply, he] using hx.comp e.injective) i j).trans
            (by simpa only [he, Equiv.trans_apply] using (hcmp x hx (e i) (e j)).symm)
        apply propext
        change (r x = p) ↔ r (reindex x) = q
        rw [hre]
        constructor
        · rintro rfl
          simp [e, Equiv.trans_assoc]
        · intro h
          apply Equiv.ext
          intro i
          have hi := DFunLike.congr_fun h (e.symm i)
          simpa [e] using hi
    change law.map r {p} = law.map r {q}
    rw [Measure.map_apply hr (measurableSet_singleton p),
      Measure.map_apply hr (measurableSet_singleton q)]
    exact (measure_congr hcongr).trans
      (hm.measure_preimage (hr (measurableSet_singleton q)).nullMeasurableSet)
  refine ⟨hr, Measure.ext_of_singleton fun p ↦ ?_⟩
  -- The common singleton mass is the reciprocal of the number of permutations.
  have hsum : ν {p} * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑' q : Equiv.Perm (Fin n), ν {q} := by
        rw [tsum_fintype, Finset.sum_congr rfl (fun q _ ↦ hequal q p), Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_comm]
      _ = 1 := by simpa only [Measure.toPMF_apply] using ν.toPMF.tsum_coe
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), PMF.fintypeUniform_apply]
  exact ENNReal.eq_inv_of_mul_eq_one_left hsum

end LennonPittelFormalization

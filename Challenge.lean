/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
# Lennon–Pittel conjecture on random stable matchings

Let $S_n$ count the stable complete matchings in a market with $n$ participants on each side.
Each participant ranks all participants on the other side in a strict order. The preference
profile is uniform over the product of the $2n$ sets of rankings, so the individual rankings
are independent and uniform.

Craig Lennon stated the conjecture in Eq. (6.0.1) of his
[2007 dissertation](https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1194991095&disposition=inline#page=126).
The [2009 paper with Boris Pittel](https://doi.org/10.1017/S0963548308009607) estimates the
second moment and leaves the probability limit open. The definitions below are the finite model
used for the conjecture in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/pull/4955).
-/

open scoped ENNReal

namespace PMF

/-- The uniform probability mass function on a nonempty finite type. -/
noncomputable def fintypeUniform (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  ofFintype (fun _ ↦ (Fintype.card α : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.mul_inv_cancel]
    · exact_mod_cast Fintype.card_ne_zero
    · exact ENNReal.natCast_ne_top _)

@[simp]
theorem fintypeUniform_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    fintypeUniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [fintypeUniform]

end PMF

namespace StableMarriage

/-- A preference profile for `n` men and `n` women. Each permutation maps a candidate to their
rank, with lower ranks preferred. -/
structure Profile (n : ℕ) where
  /-- The rank that each man assigns to each woman. -/
  manRank : Fin n → Equiv.Perm (Fin n)
  /-- The rank that each woman assigns to each man. -/
  womanRank : Fin n → Equiv.Perm (Fin n)
  deriving Inhabited

/-- Preference profiles form a finite type. -/
instance {n : ℕ} : Fintype (Profile n) :=
  Fintype.ofEquiv
    ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.manRank, p.womanRank)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A complete matching of `n` men to `n` women. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

/-- A man and woman form a blocking pair when they are not matched to each other and each ranks
the other above their current partner. -/
def IsBlockingPair {n : ℕ} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  μ m ≠ w ∧
    p.manRank m w < p.manRank m (μ m) ∧
      p.womanRank w m < p.womanRank w (μ.symm w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {n : ℕ} (p : Profile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair p μ m w

/-- The number of stable complete matchings for a preference profile. -/
noncomputable def numStableMatchings {n : ℕ} (p : Profile n) : ℕ := by
  classical
  exact Fintype.card {μ : Matching n // IsStable p μ}

/-- The discrete measurable structure on preference profiles. -/
instance {n : ℕ} : MeasurableSpace (Profile n) := ⊤

/-- The uniform probability mass function on preference profiles. -/
noncomputable def uniformProfile (n : ℕ) : PMF (Profile n) :=
  PMF.fintypeUniform (Profile n)

/-- The expected number of stable matchings under the uniform profile distribution. -/
noncomputable def expectedNumStableMatchings (n : ℕ) : ℝ :=
  ∫ p, (numStableMatchings p : ℝ) ∂((uniformProfile n).toMeasure)

end StableMarriage

open Filter
open scoped Topology

namespace LennonPittel

/-- For independent uniform strict preferences, the probability that the number of stable
matchings is at least $\varepsilon_n$ times its expectation tends to one for every positive
nonincreasing sequence $\varepsilon_n$ tending to zero. -/
theorem lennon_pittel_conjecture
    (ε : ℕ → ℝ) (hε_pos : ∀ n, 0 < ε n) (hε_antitone : Antitone ε)
    (hε_tendsto : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun n ↦
        (StableMarriage.uniformProfile n).toMeasure
          {p | (StableMarriage.numStableMatchings p : ℝ) ≥
            ε n * StableMarriage.expectedNumStableMatchings n})
      atTop (𝓝 1) := by
  sorry

end LennonPittel

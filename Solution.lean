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

public import LennonPittel.LennonPittelProof

/-!
# The Lennon–Pittel conjecture

The proof below specializes the lower-tail theorem to the original hypotheses.
-/

public section

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
      atTop (𝓝 1) :=
  LennonPittelFormalization.lennon_pittel_conjecture_verified ε hε_pos hε_antitone hε_tendsto

end LennonPittel

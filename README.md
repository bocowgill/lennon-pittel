# The Lennon–Pittel conjecture on random stable matchings

Consider a market with $n$ participants on each of two sides. Each
participant independently chooses a uniform strict ranking of the other side.
A complete matching is stable if no unmatched pair both prefer each other to
their assigned partners. Write $S_n$ for the number of stable matchings.

This project proves that for every positive nonincreasing sequence
$\varepsilon_n \to 0$,

$$
\mathbb P\!\left(S_n \ge \varepsilon_n\,\mathbb E[S_n]\right) \to 1.
$$

The theorem is Eq. (6.0.1) in Lennon's dissertation. The 2009 paper of Lennon
and Pittel gives a second-moment estimate and asks whether the lower-tail
success probability tends to one. Pittel's first-moment asymptotic puts the
expectation at scale $n\log n$. [Lennon 2007][thesis] · [Lennon–Pittel 2009][lp]
· [Pittel 1989][pittel]

An accompanying working paper is in preparation.

## Formal statement

[Challenge.lean](Challenge.lean) states
`LennonPittel.lennon_pittel_conjecture` and defines the finite model directly.
A profile consists of $2n$ permutations, each sending a candidate to their
rank. The uniform law on the product of these permutation spaces makes the
rankings independent and uniform. The stability predicate excludes strict
blocking pairs, and the probability and expectation use the same finite law.
The Lean 4.35 port constructs the uniform probability mass function
directly, assigning each profile the reciprocal of the number of profiles.

[Solution.lean](Solution.lean) proves that declaration using the theorem in
[LennonPittelProof.lean](LennonPittel/LennonPittelProof.lean). The latter also
gives the same conclusion for an arbitrary real sequence tending to zero.
The formal statement and finite model retain their original attribution.
[Formal Conjectures PR #4955][fc]

## Proof outline

1. Transfer the finite model to independent continuous scores and use that
   representation to prove Pittel's first-moment asymptotic.
2. Count a subfamily of stable matchings indexed by a rotation and compatible
   earlier rotations. Each counted matching determines its index. Bound the
   resulting random count's conditional center from below at scale
   $n\log n$.
3. Bound the centered second moment using pair estimates. A switch sends the
   comparable-pair contribution to an endpoint event involving counts of
   short cycles. The proof chooses the cycle cutoff after fixing the lower
   scale, so reducing the variance bound preserves the lower threshold.

## Local verification

Run these commands from the project root with Elan installed.

```sh
lake exe cache get
lake --wfail build Solution
```

On Linux with Bubblewrap and unprivileged user namespaces, run
`scripts/verify-comparator.sh`. On macOS, run
`scripts/verify-comparator.sh --local-exports` from a trusted checkout.
The macOS command compares exports from separate local builds without the
Linux sandbox. Both commands run Lean Comparator with NanoDa and con-ron.
Comparator checks that the Solution proves the Challenge statement and
checks its axiom dependencies.
The Challenge has one deliberate `sorry` at its headline declaration.
The axiom allowlist is `propext`, `Quot.sound`, and `Classical.choice`.
[Palomar submission guide][palomar]

The project uses Apache-2.0. See [LICENSE](LICENSE) and
[formalization.yaml](formalization.yaml) for attribution and provenance.

[thesis]: https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1194991095&disposition=inline#page=126
[lp]: https://doi.org/10.1017/S0963548308009607
[pittel]: https://doi.org/10.1137/0402048
[fc]: https://github.com/google-deepmind/formal-conjectures/pull/4955
[palomar]: https://palomar-registry.org/how-to-submit

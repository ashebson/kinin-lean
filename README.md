# Kinnim in Lean

An executable Lean 4 formalization of all sixteen units of Mishnah Kinnim in
the **4 + 6 + 6** division used by Moshe Koppel's *Seder Kinnim*.

The formalization is split into focused modules:

- `Kinin/Core.lean` — birds, offerings, pairs, owners, actions, possible
  worlds, permutations, and basic uncertainty algorithms;
- `Kinin/Uncertainty.lean` — semantic maximin problems, attaining strategies,
  adversarial upper-bound worlds, and uniqueness of an optimal guarantee;
- `Kinin/Flights.lean` — flight events and repeated group-loss recurrences;
- `Kinin/Majority.lean` — subset-sum majority and replacement-shortfall
  algorithms;
- `Kinin/Chapter1.lean`, `Chapter2.lean`, and `Chapter3.lean` — the sixteen
  source-mapped theorem groups;
- `Kinin.lean` — the public entry point importing all three chapters.

Together they provide reusable definitions for:

- bird species, offering designation, owners, pairs, and liabilities;
- altar levels, priestly actions, local validity, and possible worlds;
- permutations and maximal guaranteed counts under hidden information;
- consulted mixtures and ownership blocks;
- flights and repeated round-trip loss through groups;
- Koppel's generalized largest-minority / smallest-majority subset-sum solver;
- componentwise replacement shortfalls and separately represented opinions.

Every unit has a theorem named `mishnah_<chapter>_<unit>`. The original
`mishnah_1_1` theorem and its symmetry lemmas are preserved. See
[`SOURCES.md`](SOURCES.md) for the source crosswalk and assumptions.

## Proof status

The chapter 3 one-level result and Koppel/Reiss subset-sum result are connected
to `UncertaintyProblem.HasOptimalGuarantee`.  Consequently their theorems now
contain both parts of a maximin proof: an attaining strategy and an admissible
counter-world against every legal strategy.  In particular,
`generalized_smallest_majority_no_better` rules out every larger guarantee.

The chapter 2 flight recurrences and the chapter 3:6 shortfall scenarios are
still explicit interpretive premises.  Their computed consequences are kernel
checked, but they have not yet been derived from the individual `Bird` and
`PriestAction` semantics.  The project records this boundary rather than
describing those calculations as independent verification.

Build with Lean 4.32.1:

```sh
lake build
```

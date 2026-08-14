# Kinnim in Lean

An executable Lean 4 formalization of all sixteen units of Mishnah Kinnim in
the **4 + 6 + 6** division used by Moshe Koppel's *Seder Kinnim*.

The formalization is split into focused modules:

- `Kinin/Core.lean` — birds, offerings, pairs, owners, actions, possible
  worlds, permutations, and basic uncertainty algorithms;
- `Kinin/Uncertainty.lean` — semantic maximin problems, attaining strategies,
  adversarial upper-bound worlds, and uniqueness of an optimal guarantee;
- `Kinin/Flights.lean` — flight observations, remedial classification, and
  path-exposure transitions;
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
- atomic replacement liabilities, componentwise uncertainty covers, and
  separately represented opinions.

Every unit has a theorem named `mishnah_<chapter>_<unit>`. The original
`mishnah_1_1` theorem and its symmetry lemmas are preserved. See
[`SOURCES.md`](SOURCES.md) for the source crosswalk and assumptions.

## Proof status

The chapter 3 one-level result and Koppel/Reiss subset-sum result are connected
to `UncertaintyProblem.HasOptimalGuarantee`.  Consequently their theorems now
contain both parts of a maximin proof: an attaining strategy and an admissible
counter-world against every legal strategy.  In particular,
`generalized_smallest_majority_no_better` rules out every larger guarantee.
The majority payoff is also realized by explicit per-block services: every
pair is classified as below/below, split, or above/above, exactly half of the
birds are performed above, and the valid count is proved to equal the payoff.

Chapter 2 now separates observed consequences from their remedial rule and
derives the 1-through-7 recurrence from endpoint/interior path exposures.  In
3:6, scenario inventories are assembled from atomic species/designation
liabilities, and `coverShortfalls_minimal` proves that their componentwise
maximum is both sufficient and least.

The remaining textual-to-model boundary is explicit: assigning a Mishnah case
to a flight observation, whole-owner cut, or list of atomic replacement
liabilities is an interpretive premise.  Lean checks every consequence after
that assignment; it does not independently establish that the assignment is
the uniquely correct reading of the Hebrew source.

Build with Lean 4.32.1:

```sh
lake build
```

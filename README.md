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

The chapter 3 one-level result is connected to
`UncertaintyProblem.HasOptimalGuarantee`. The Koppel/Reiss result is stated in
the form actually proved by Reiss: an exact minimum over all possible
owner-by-owner apportionments after the priest has already performed half the
birds each way. In particular, `generalized_smallest_majority_no_better`
rules out every larger universal lower bound. The chapter 3:2 action is the
concrete, world-independent list
`canonicalHalfSplitActions`: half of the numbered unidentified birds are
offered as burnts above and half as sins below. Lean proves its length, split,
and local validity before quantifying over hidden ownership worlds. Each world
contains an individual level assignment for every physical bird of every
owner. Validity is computed directly from those lists and the closed-pair
quota. `PhysicalOwnershipWorld.compatibleWithCanonicalPlan` proves that every
world's flattened individual-bird levels are a permutation of the fixed
action list. `ownerLevelsValid_order_irrelevant` proves that reordering physical
birds cannot affect validity when the number above is unchanged, while
`OwnerBirdAssignment.valid_eq_compressed` proves that compression to per-owner
above counts is lossless. The physical valid-bird count contains no majority
formula. The formula is a theorem: every compatible physical apportionment
achieves the smallest-majority bound, while a concrete apportionment
constructed from the largest subset sum attains it exactly.

Chapter 2 now separates observed consequences from their remedial rule and
derives the 1-through-7 recurrence from endpoint/interior path exposures.  In
3:6, scenario inventories are assembled from atomic species/designation
liabilities, and `coverShortfalls_minimal` proves that their componentwise
maximum is both sufficient and least.

The remaining textual-to-model boundary is explicit: chapter 3:2 represents a
physical apportionment by each owner's complete list of individual action
levels. Compatibility with the global fixed plan is proved by permutation,
and owner-level order-invariance and lossless compression show that temporal
interleaving carries no additional payoff information. Other chapters still assign textual cases to flight
observations or lists of atomic replacement liabilities. Lean does not
independently establish that these are the uniquely correct readings of the
Hebrew source.

Build with Lean 4.32.2:

```sh
lake build
```

## Palomar submission

`Challenge.lean` states the exact Kinnim 3:2 physical-apportionment theorem:
every owner-by-owner assignment is compatible with the fixed action list,
every such assignment meets the smallest-majority bound, and a concrete one
attains it. `Solution.lean` proves it;
`comparator.json` selects the advertised declaration and its supporting
definitions; and `formalization.yaml` records provenance, scope, automation,
review status, and known fidelity boundaries for the Palomar Registry.

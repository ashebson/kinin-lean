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
The chapter 3:2 strategy is the concrete, world-independent list
`canonicalHalfSplitActions`: half of the numbered unidentified birds are
offered as burnts above and half as sins below. Lean proves its length, split,
and local validity before quantifying over hidden ownership worlds. Each world
contains an individual level assignment for every physical bird of every
owner. Validity is computed directly from those lists and the closed-pair
quota. `ownerLevelsValid_order_irrelevant` proves that reordering physical
birds cannot affect validity when the number above is unchanged, while
`OwnerBirdAssignment.valid_eq_compressed` proves that compression to per-owner
above counts is lossless. The operational payoff contains no majority formula.
The formula is a theorem: every physical world achieves the
smallest-majority bound, while a concrete physical world constructed from the
largest subset sum attains it.

Chapter 2 now separates observed consequences from their remedial rule and
derives the 1-through-7 recurrence from endpoint/interior path exposures.  In
3:6, scenario inventories are assembled from atomic species/designation
liabilities, and `coverShortfalls_minimal` proves that their componentwise
maximum is both sufficient and least.

The remaining textual-to-model boundary is explicit: chapter 3:2 represents a
physical permutation by each owner's complete list of individual service
levels and treats global interleaving as operationally irrelevant. The latter
is supported by the proved owner-level order-invariance and lossless-
compression theorems. Other chapters still assign textual cases to flight
observations or lists of atomic replacement liabilities. Lean does not
independently establish that these are the uniquely correct readings of the
Hebrew source.

Build with Lean 4.32.2:

```sh
lake build
```

## Palomar submission

`Challenge.lean` gives a project-independent operational statement of the
exact Kinnim 3:2 maximin theorem: a fixed physical plan, hidden whole-owner
worlds, individual pair services, direct valid-bird counting, and a matching
worst world. `Solution.lean` proves it;
`comparator.json` selects the advertised declaration and its supporting
definitions; and `formalization.yaml` records provenance, scope, automation,
review status, and known fidelity boundaries for the Palomar Registry.

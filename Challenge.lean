import Kinin.Majority

/-!
# Kinnim 3:2: the exact minimum over physical apportionments

Suppose several owners contribute closed obligatory pairs. After all their
birds have become mixed, the priest acts on exactly half above and half below.
The remaining uncertainty is how the individual birds acted on at each level
were apportioned among the owners.

`PhysicalOwnershipWorld pairsByOwner` records that uncertainty without an
aggregate payoff shortcut. For every owner it contains one `Level` entry for
each of her `2 * pairs` individual birds, and its `halfAbove` field requires
exactly half of all birds globally to have been acted on above.

`OwnerBirdAssignment.validBirds` then counts valid birds owner by owner from
the closed-pair quota: at most `pairs` above-level burnt offerings and at most
`pairs` below-level sin offerings can be valid for an owner who brought
`pairs` pairs.

The theorem first proves that every such world is compatible with the fixed
action list: after owner labels are forgotten, its individual-bird levels are
a permutation of the plan's levels. It then says that the Koppel--Reiss
smallest-majority value is the exact minimum of the direct physical count: it
is a lower bound for every possible apportionment, and one concrete compatible
apportionment attains it.
-/

namespace PalomarKinnim

open Kinnim

theorem physicalApportionmentExactMinimum (pairsByOwner : List Nat) :
    (∀ world : PhysicalOwnershipWorld pairsByOwner,
      world.assignment.levels.Perm
          (actionLevels
            (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
      guaranteedHalfSplitBirds pairsByOwner ≤ world.assignment.validBirds) ∧
    (∃ worst : PhysicalOwnershipWorld pairsByOwner,
      worst.assignment.levels.Perm
          (actionLevels
            (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
      worst.assignment.validBirds = guaranteedHalfSplitBirds pairsByOwner) := by
  sorry

end PalomarKinnim

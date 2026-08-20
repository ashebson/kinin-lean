/-!
# Kinnim 3:2: the exact minimum over physical apportionments

Suppose several owners contribute closed obligatory pairs. After all their
birds have become mixed, the priest acts on exactly half above and half below.
The remaining uncertainty is how the individual birds acted on at each level
were apportioned among the owners.

`OwnerBirdAssignment pairsByOwner` records that uncertainty directly. For
every owner it contains one `Level` entry for each of that owner's
`2 * pairs` individual birds. A `PhysicalOwnershipWorld` additionally requires
exactly half of all birds globally to have been acted on above.

`OwnerBirdAssignment.validBirds` counts valid birds owner by owner from the
closed-pair quota: at most `pairs` above-level burnt offerings and at most
`pairs` below-level sin offerings can be valid for an owner who brought
`pairs` pairs.

The theorem first says that every physical world is compatible with the fixed
half-above, half-below action levels after owner labels are forgotten. It then
says that the Koppel--Reiss smallest-majority value is the exact minimum of the
direct physical count: it is a lower bound for every possible apportionment,
and one concrete compatible apportionment attains it.
-/

namespace PalomarKinnim

def sumNats : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNats xs

def subsetSums : List Nat → List Nat
  | [] => [0]
  | x :: xs =>
      let rest := subsetSums xs
      rest ++ rest.map (fun n => n + x)

def greatestAtMost (limit : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs =>
      let tail := greatestAtMost limit xs
      if x ≤ limit then Nat.max x tail else tail

def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

/-- Twice the complementary smallest majority, measured in individual birds. -/
def guaranteedHalfSplitBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

inductive Level where
  | below
  | above
  deriving DecidableEq, Repr

def countLevel (wanted : Level) : List Level → Nat
  | [] => 0
  | level :: levels =>
      (if level = wanted then 1 else 0) + countLevel wanted levels

/-- Valid birds for one owner, counted directly from the individual action
levels and the owner's closed-pair quota. -/
def ownerLevelsValid (pairs : Nat) (levels : List Level) : Nat :=
  Nat.min (countLevel .below levels) pairs +
    Nat.min (countLevel .above levels) pairs

/-- For each owner, retain one entry for every physical bird and the level at
which that individual bird is acted upon. -/
inductive OwnerBirdAssignment : List Nat → Type where
  | nil : OwnerBirdAssignment []
  | cons {pairs rest} (levels : List Level)
      (birdCount : levels.length = 2 * pairs)
      (tail : OwnerBirdAssignment rest) :
      OwnerBirdAssignment (pairs :: rest)

/-- Forget the owner-block boundaries while retaining every action level. -/
def OwnerBirdAssignment.levels :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → List Level
  | _, .nil => []
  | _, .cons levels _ tail => levels ++ tail.levels

def OwnerBirdAssignment.aboveBirds :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → Nat
  | _, .nil => 0
  | _, .cons levels _ tail =>
      countLevel .above levels + tail.aboveBirds

def OwnerBirdAssignment.validBirds :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerBirdAssignment.cons pairs _ levels _ tail =>
      ownerLevelsValid pairs levels + tail.validBirds

/-- A full physical world with exactly half of all birds acted on above. -/
structure PhysicalOwnershipWorld (pairsByOwner : List Nat) where
  assignment : OwnerBirdAssignment pairsByOwner
  halfAbove : assignment.aboveBirds = sumNats pairsByOwner

/-- The action levels of the fixed half-above, half-below plan. -/
def canonicalHalfSplitLevels (pairs : Nat) : List Level :=
  List.replicate pairs .above ++ List.replicate pairs .below

theorem physicalApportionmentExactMinimum (pairsByOwner : List Nat) :
    (∀ world : PhysicalOwnershipWorld pairsByOwner,
      world.assignment.levels.Perm
          (canonicalHalfSplitLevels (sumNats pairsByOwner)) ∧
      guaranteedHalfSplitBirds pairsByOwner ≤ world.assignment.validBirds) ∧
    (∃ worst : PhysicalOwnershipWorld pairsByOwner,
      worst.assignment.levels.Perm
          (canonicalHalfSplitLevels (sumNats pairsByOwner)) ∧
      worst.assignment.validBirds = guaranteedHalfSplitBirds pairsByOwner) := by
  sorry

end PalomarKinnim

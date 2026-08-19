/-!
# Kinnim 3:2: the exact whole-owner-cut guarantee

Suppose several owners contribute closed pairs of birds.  A whole-owner cut
places all pairs belonging to each owner on one side or the other.  Among cuts
whose smaller side contains at most half of all pairs, the worst valid-bird
payoff is twice the complement of the largest attainable minority.

This is the small statement surface for the Koppel--Reiss interpretation of
Mishnah Kinnim 3:2.  Counts in `pairsByOwner` are pairs; `cutPayoff` counts
individual birds.
-/

namespace PalomarKinnim

/-- Sum a list of natural numbers. -/
def sumNats : List Nat → Nat
  | [] => 0
  | n :: ns => n + sumNats ns

/-- All subset sums of a list, retaining multiplicity. -/
def subsetSums : List Nat → List Nat
  | [] => [0]
  | n :: ns =>
      let rest := subsetSums ns
      rest ++ rest.map (fun total => total + n)

/-- The greatest member of a list not exceeding `limit`, or zero if none exists. -/
def greatestAtMost (limit : Nat) : List Nat → Nat
  | [] => 0
  | n :: ns =>
      let tail := greatestAtMost limit ns
      if n ≤ limit then Nat.max n tail else tail

/-- The largest whole-owner subset containing at most half of all pairs. -/
def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

/-- Koppel--Reiss's guaranteed number of valid individual birds. -/
def guaranteedValidBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

/-- A cut is admissible when it occurs between whole owner blocks and its
recorded minority contains at most half of all pairs. -/
def AdmissibleCut (pairsByOwner : List Nat) (minorityPairs : Nat) : Prop :=
  minorityPairs ∈ subsetSums pairsByOwner ∧
    minorityPairs ≤ sumNats pairsByOwner / 2

/-- The number of valid individual birds supplied by a whole-owner cut. -/
def cutPayoff (pairsByOwner : List Nat) (minorityPairs : Nat) : Nat :=
  2 * (sumNats pairsByOwner - minorityPairs)

/-- The Koppel--Reiss number is the exact minimum payoff: every admissible
whole-owner cut attains at least it, and one admissible cut attains equality. -/
theorem exactCutGuarantee (pairsByOwner : List Nat) :
    (∀ minorityPairs, AdmissibleCut pairsByOwner minorityPairs →
      guaranteedValidBirds pairsByOwner ≤
        cutPayoff pairsByOwner minorityPairs) ∧
    ∃ minorityPairs, AdmissibleCut pairsByOwner minorityPairs ∧
      cutPayoff pairsByOwner minorityPairs =
        guaranteedValidBirds pairsByOwner := by
  sorry

end PalomarKinnim

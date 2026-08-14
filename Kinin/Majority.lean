import Kinin.Core

/-!
# Majority and replacement arithmetic
-/

namespace Kinnim

/-! ## Koppel's subset-sum formulation of chapter 3 -/

def subsetSums : List Nat → List Nat
  | [] => [0]
  | x :: xs =>
      let rest := subsetSums xs
      rest ++ rest.map (fun n => n + x)

def greatestAtMost (limit : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs =>
      let tail := greatestAtMost limit xs
      if x <= limit then Nat.max x tail else tail

def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

/-- Twice the complementary smallest majority, measured in birds. -/
def guaranteedHalfSplitBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

def allAtOneLevelValidBirds (pairsByOwner : List Nat) : Nat :=
  sumNats pairsByOwner

def specifiedOppositesHalfSplitGuarantee (_pairsEach : Nat) : Nat := 0

def closedComponentGuarantee (closedPairs : Nat) : Nat := closedPairs

/-! ## Componentwise shortfalls for 3:6 -/

structure Inventory where
  turtleSin : Nat := 0
  turtleBurnt : Nat := 0
  youngSin : Nat := 0
  youngBurnt : Nat := 0
  deriving DecidableEq, Repr

def Inventory.total (i : Inventory) : Nat :=
  i.turtleSin + i.turtleBurnt + i.youngSin + i.youngBurnt

def Inventory.join (a b : Inventory) : Inventory where
  turtleSin := Nat.max a.turtleSin b.turtleSin
  turtleBurnt := Nat.max a.turtleBurnt b.turtleBurnt
  youngSin := Nat.max a.youngSin b.youngSin
  youngBurnt := Nat.max a.youngBurnt b.youngBurnt

def coverShortfalls : List Inventory → Inventory
  | [] => {}
  | x :: xs => x.join (coverShortfalls xs)

def oneSpeciesSimpleShortfalls : List Inventory :=
  [{ turtleBurnt := 1 }]

def twoSpeciesSimpleShortfalls : List Inventory :=
  [{ turtleBurnt := 1 }, { youngBurnt := 1 }]

def oneSpeciesSpecifiedShortfalls : List Inventory :=
  [{ turtleSin := 1, turtleBurnt := 2 }]

def twoSpeciesSpecifiedShortfalls : List Inventory :=
  [{ turtleSin := 1, turtleBurnt := 2 }, { youngBurnt := 1 }]

def oneSpeciesFixedShortfalls : List Inventory :=
  [{ turtleSin := 2, turtleBurnt := 3 }]

def twoSpeciesFixedShortfalls : List Inventory :=
  [{ turtleSin := 2, turtleBurnt := 3 }, { youngBurnt := 1 }]

def finalMajorityShortfalls : List Inventory :=
  [{ turtleSin := 2, turtleBurnt := 2,
     youngSin := 1, youngBurnt := 2 }]

def finalBenAzzaiShortfalls : List Inventory :=
  finalMajorityShortfalls ++ [{ youngSin := 2 }]


end Kinnim

import Kinin.Core

/-!
# Flights between bird groups
-/

namespace Kinnim

/-! ## Flights -/

inductive FlightEvent where
  | toAir
  | toDead
  | birdDied
  | toOffered
  | closedToSpecified
  | returnedFromSpecified
  | specifiedFlewFirst
  | deadBirdEntered
  deriving DecidableEq, Repr

inductive FlightResult where
  | takeMate
  | migrantInvalidatesOne
  | noAdditionalLoss
  | allDie
  deriving DecidableEq, Repr

def flightResult : FlightEvent → FlightResult
  | .toAir => .takeMate
  | .toDead => .takeMate
  | .birdDied => .takeMate
  | .toOffered => .migrantInvalidatesOne
  | .closedToSpecified => .takeMate
  | .returnedFromSpecified => .allDie
  | .specifiedFlewFirst => .allDie
  | .deadBirdEntered => .allDie

/-- Equal two-group mixtures stabilize after their first round trip. -/
def equalTwoGroupGuarantee (pairs trips : Nat) : List Nat :=
  if trips = 0 then [pairs, pairs] else [pairs - 1, pairs - 1]

def loseInteriorAndLast : List Nat → List Nat
  | [] => []
  | [x] => [x - 1]
  | x :: xs => (x - 2) :: loseInteriorAndLast xs

/-- Endpoints lose one guaranteed pair; interior groups lose two. -/
def roundTripLoss : List Nat → List Nat
  | [] => []
  | x :: xs => (x - 1) :: loseInteriorAndLast xs

def iterateRoundTrips : Nat → List Nat → List Nat
  | 0, state => state
  | n + 1, state => iterateRoundTrips n (roundTripLoss state)

/-- Separate representation of the opinion protecting the final group. -/
def protectLast : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: xs => x :: protectLast xs

def speciesMatch (a b : BirdSpecies) : Bool := a == b

def majorityCompletionSpecies (other : BirdSpecies) : BirdSpecies := other

def benAzzaiCompletionSpecies (first : BirdSpecies) : BirdSpecies := first


end Kinnim

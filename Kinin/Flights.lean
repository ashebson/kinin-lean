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

/-- Observable consequences of a flight, before applying the remedial rule. -/
structure FlightState where
  mateDeficit : Nat := 0
  offeredContaminants : Nat := 0
  designationConflict : Bool := false
  deriving DecidableEq, Repr

/-- Translate the physical event into state changes.  Loss to an inaccessible
place creates a mate deficit; entry into an already-offered pool creates an
unidentifiable contaminant; return across a specified/closed boundary creates
an irresolvable designation conflict. -/
def observeFlight : FlightEvent → FlightState
  | .toAir => { mateDeficit := 1 }
  | .toDead => { mateDeficit := 1 }
  | .birdDied => { mateDeficit := 1 }
  | .toOffered => { offeredContaminants := 1 }
  | .closedToSpecified => { mateDeficit := 1 }
  | .returnedFromSpecified => { designationConflict := true }
  | .specifiedFlewFirst => { designationConflict := true }
  | .deadBirdEntered => { designationConflict := true }

def classifyFlightState (state : FlightState) : FlightResult :=
  if state.designationConflict then .allDie
  else if state.offeredContaminants > 0 then .migrantInvalidatesOne
  else if state.mateDeficit > 0 then .takeMate
  else .noAdditionalLoss

def flightResult (event : FlightEvent) : FlightResult :=
  classifyFlightState (observeFlight event)

theorem designationConflict_forces_allDie
    (state : FlightState) (conflict : state.designationConflict = true) :
    classifyFlightState state = .allDie := by
  simp [classifyFlightState, conflict]

theorem offeredContamination_invalidates_one
    (state : FlightState) (clean : state.designationConflict = false)
    (contaminated : state.offeredContaminants > 0) :
    classifyFlightState state = .migrantInvalidatesOne := by
  simp [classifyFlightState, clean, contaminated]

theorem mateDeficit_requires_mate
    (state : FlightState) (clean : state.designationConflict = false)
    (unoffered : state.offeredContaminants = 0)
    (missing : state.mateDeficit > 0) :
    classifyFlightState state = .takeMate := by
  simp [classifyFlightState, clean, unoffered, missing]

/-- Equal two-group mixtures stabilize after their first round trip. -/
def equalTwoGroupGuarantee (pairs trips : Nat) : List Nat :=
  if trips = 0 then [pairs, pairs] else [pairs - 1, pairs - 1]

def loseInteriorAndLast : List Nat → List Nat
  | [] => []
  | [x] => [x - 1]
  | x :: xs => (x - 2) :: loseInteriorAndLast xs

/-! A round trip across a path creates one unresolved exchange at every
boundary.  Endpoint groups touch one boundary and interior groups touch two. -/

inductive GroupExposure where
  | immune
  | endpoint
  | interior
  deriving DecidableEq, Repr

def GroupExposure.loss : GroupExposure → Nat
  | .immune => 0
  | .endpoint => 1
  | .interior => 2

def tailPathExposures : List Nat → List GroupExposure
  | [] => []
  | [_] => [.endpoint]
  | _ :: xs => .interior :: tailPathExposures xs

def pathExposures : List Nat → List GroupExposure
  | [] => []
  | [_] => [.endpoint]
  | _ :: xs => .endpoint :: tailPathExposures xs

def applyExposures : List Nat → List GroupExposure → List Nat
  | pairs :: rest, exposure :: exposures =>
      (pairs - exposure.loss) :: applyExposures rest exposures
  | _, _ => []

/-- The recurrence is now the consequence of the path's incident-boundary
exposures, rather than a direct table of endpoint/interior answers. -/
def roundTripLoss (state : List Nat) : List Nat :=
  applyExposures state (pathExposures state)

theorem roundTripLoss_eq_exposure_semantics (state : List Nat) :
    roundTripLoss state = applyExposures state (pathExposures state) := rfl

def iterateRoundTrips : Nat → List Nat → List Nat
  | 0, state => state
  | n + 1, state => iterateRoundTrips n (roundTripLoss state)

/-- Replace the last exposure by the alternative opinion's protected case. -/
def protectLastExposure : List GroupExposure → List GroupExposure
  | [] => []
  | [_] => [.immune]
  | x :: xs => x :: protectLastExposure xs

def protectedLastPathExposures (state : List Nat) : List GroupExposure :=
  protectLastExposure (pathExposures state)

def roundTripLossProtectedLast (state : List Nat) : List Nat :=
  applyExposures state (protectedLastPathExposures state)

/-- Backward-compatible identity on already-computed states.  New theorems
should use `roundTripLossProtectedLast` to represent the variant opinion. -/
def protectLast : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: xs => x :: protectLast xs

def speciesMatch (a b : BirdSpecies) : Bool := a == b

def majorityCompletionSpecies (other : BirdSpecies) : BirdSpecies := other

def benAzzaiCompletionSpecies (first : BirdSpecies) : BirdSpecies := first


end Kinnim

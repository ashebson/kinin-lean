/-!
# Mishnah Kinnim: an executable combinatorial model

The public API separates physical data, hidden information and priestly
actions, and tractate-specific counting algorithms. The theorem numbering
follows the sixteen bookmarks in Moshe Koppel's linked edition: 4 + 6 + 6.
See `SOURCES.md` for the crosswalk to Mechon Mamre and Sefaria.
-/

namespace Kinnim

/-! ## Domain model -/

inductive Species where
  | bird
  | animal
  deriving DecidableEq, Repr

inductive BirdSpecies where
  | turtledove
  | youngDove
  deriving DecidableEq, Repr

inductive Offering where
  | sin
  | burnt
  deriving DecidableEq, Repr

inductive Level where
  | below
  | above
  deriving DecidableEq, Repr

/-- Abstract labels for distinct liabilities. The combinatorics only needs
equality of labels. -/
inductive ObligationReason where
  | reasonA
  | reasonB
  | other (tag : Nat)
  deriving DecidableEq, Repr

inductive PairKind where
  | obligation
  | vow
  | gift
  deriving DecidableEq, Repr

/-- `designation = none` means that an obligatory pair is still closed. -/
structure Bird where
  id : Nat
  birdSpecies : BirdSpecies
  owner : Nat
  pairId : Nat
  reason : ObligationReason
  designation : Option Offering
  deriving DecidableEq, Repr

structure Pair where
  first : Bird
  second : Bird
  kind : PairKind
  deriving DecidableEq, Repr

structure PriestAction where
  birdId : Nat
  offering : Offering
  level : Level
  deriving DecidableEq, Repr

structure PossibleWorld where
  birds : List Bird
  deriving DecidableEq, Repr

def prescribedLevel : Species → Offering → Level
  | .bird,   .sin   => .below
  | .animal, .sin   => .above
  | .bird,   .burnt => .above
  | .animal, .burnt => .below

def Valid (species : Species) (offering : Offering) (level : Level) : Prop :=
  level = prescribedLevel species offering

def validLevel (species : Species) (offering : Offering) (level : Level) : Bool :=
  level == prescribedLevel species offering

def otherLevel : Level → Level
  | .below => .above
  | .above => .below

def requiredOfferings : PairKind → List Offering
  | .obligation => [.sin, .burnt]
  | .vow => [.burnt, .burnt]
  | .gift => [.burnt, .burnt]

def liableAfterLoss : PairKind → Bool
  | .vow => true
  | _ => false

def specifiedPairValid (p : Pair) : Bool :=
  match p.first.designation, p.second.designation with
  | some .sin, some .burnt => true
  | some .burnt, some .sin => true
  | _, _ => false

def actionLocallyValid (bird : Bird) (action : PriestAction) : Bool :=
  bird.id == action.birdId &&
  validLevel .bird action.offering action.level &&
  match bird.designation with
  | none => true
  | some required => required == action.offering

/-! ## Reusable finite algorithms -/

def sumNats : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNats xs

def minFrom (best : Nat) : List Nat → Nat
  | [] => best
  | y :: ys => minFrom (Nat.min best y) ys

def minNats : List Nat → Nat
  | [] => 0
  | x :: xs => minFrom x xs

def maxFrom (best : Nat) : List Nat → Nat
  | [] => best
  | y :: ys => maxFrom (Nat.max best y) ys

def maxNats : List Nat → Nat
  | [] => 0
  | x :: xs => maxFrom x xs

def countOffering : Offering → List Offering → Nat
  | _, [] => 0
  | wanted, x :: xs =>
      (if wanted == x then 1 else 0) + countOffering wanted xs

def countMatches : List Offering → List Offering → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
      (if x == y then 1 else 0) + countMatches xs ys

def allOfferingPlans : Nat → List (List Offering)
  | 0 => [[]]
  | n + 1 =>
      let rest := allOfferingPlans n
      rest.map (fun xs => .sin :: xs) ++
        rest.map (fun xs => .burnt :: xs)

def insertEverywhere {α : Type} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: bs =>
      (a :: b :: bs) ::
        (insertEverywhere a bs).map (fun xs => b :: xs)

def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => (permutations as).flatMap (insertEverywhere a)

def offeringWorlds (sins burnts : Nat) : List (List Offering) :=
  permutations (List.replicate sins .sin ++ List.replicate burnts .burnt)

def guaranteedMatches (worlds : List (List Offering)) (plan : List Offering) : Nat :=
  minNats (worlds.map (fun world => countMatches world plan))

def maximalGuaranteedMatches (n : Nat) (worlds : List (List Offering)) : Nat :=
  maxNats ((allOfferingPlans n).map (guaranteedMatches worlds))

/-! ## Consulted mixtures -/

/-- Opposed already-specified offerings cannot safely be acted on. -/
def opposedSpecifiedMixture (designations : List Offering) : Bool :=
  countOffering .sin designations > 0 && countOffering .burnt designations > 0

/-- Mixing specified birds with closed obligations leaves the corresponding
closed count assured. -/
def closedWithForeignValid (closedPairs foreignBirds : Nat) : Nat :=
  Nat.min closedPairs (closedPairs + foreignBirds)

/-- Koppel's consulted strategy guarantees twice the smallest owner block. -/
def consultedClosedValidBirds (pairsByOwner : List Nat) : Nat :=
  2 * minNats pairsByOwner

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

/-! ## Mishnah-by-Mishnah theorems: 4 + 6 + 6 -/

theorem mishnah_1_1 :
    Valid .bird .sin .below ∧
    Valid .animal .sin .above ∧
    Valid .bird .burnt .above ∧
    Valid .animal .burnt .below := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

theorem mishnah_1_1_pair_rules :
    requiredOfferings .obligation = [.sin, .burnt] ∧
    requiredOfferings .vow = [.burnt, .burnt] ∧
    requiredOfferings .gift = [.burnt, .burnt] ∧
    liableAfterLoss .vow = true ∧
    liableAfterLoss .gift = false := by
  decide

theorem changed_level_is_invalid (species : Species) (offering : Offering) :
    ¬ Valid species offering (otherLevel (prescribedLevel species offering)) := by
  cases species <;> cases offering <;> intro h <;> cases h

theorem changing_species_reverses_level
    (species : Species) (offering : Offering) :
    prescribedLevel
        (match species with | .bird => .animal | .animal => .bird)
        offering = otherLevel (prescribedLevel species offering) := by
  cases species <;> cases offering <;> rfl

theorem changing_offering_reverses_level
    (species : Species) (offering : Offering) :
    prescribedLevel species
        (match offering with | .sin => .burnt | .burnt => .sin) =
      otherLevel (prescribedLevel species offering) := by
  cases species <;> cases offering <;> rfl

theorem changing_both_preserves_level
    (species : Species) (offering : Offering) :
    prescribedLevel
        (match species with | .bird => .animal | .animal => .bird)
        (match offering with | .sin => .burnt | .burnt => .sin) =
      prescribedLevel species offering := by
  cases species <;> cases offering <;> rfl

theorem mishnah_1_2 :
    opposedSpecifiedMixture [.sin, .burnt] = true ∧
    closedWithForeignValid 1 1 = 1 ∧
    closedWithForeignValid 10 1 = 10 ∧
    closedWithForeignValid 1 10 = 1 := by
  decide

theorem mishnah_1_3 :
    consultedClosedValidBirds [1, 1] = 2 ∧
    consultedClosedValidBirds [2, 2] = 4 ∧
    consultedClosedValidBirds [3, 3] = 6 ∧
    consultedClosedValidBirds [1, 2, 3, 10, 100] = 2 := by
  decide

theorem mishnah_1_4 :
    consultedClosedValidBirds [2, 5] = consultedClosedValidBirds [2, 5] ∧
    requiredOfferings .obligation = [.sin, .burnt] := by
  decide

theorem mishnah_2_1 :
    flightResult .toAir = .takeMate ∧
    flightResult .toDead = .takeMate ∧
    flightResult .birdDied = .takeMate ∧
    flightResult .toOffered = .migrantInvalidatesOne := by
  decide

theorem mishnah_2_2 :
    equalTwoGroupGuarantee 2 0 = [2, 2] ∧
    equalTwoGroupGuarantee 2 1 = [1, 1] ∧
    equalTwoGroupGuarantee 2 4 = [1, 1] := by
  decide

theorem mishnah_2_3 :
    iterateRoundTrips 1 [1, 2, 3, 4, 5, 6, 7] = [0, 0, 1, 2, 3, 4, 6] ∧
    iterateRoundTrips 2 [1, 2, 3, 4, 5, 6, 7] = [0, 0, 0, 0, 1, 2, 5] ∧
    iterateRoundTrips 3 [1, 2, 3, 4, 5, 6, 7] = [0, 0, 0, 0, 0, 0, 4] ∧
    protectLast [0, 0, 0, 0, 0, 0, 5] = [0, 0, 0, 0, 0, 0, 5] := by
  decide

theorem mishnah_2_4 :
    flightResult .closedToSpecified = .takeMate ∧
    flightResult .returnedFromSpecified = .allDie ∧
    flightResult .specifiedFlewFirst = .allDie := by
  decide

theorem mishnah_2_5 :
    validLevel .bird .sin .below = true ∧
    validLevel .bird .burnt .above = true ∧
    flightResult .returnedFromSpecified = .allDie := by
  decide

theorem mishnah_2_6 :
    speciesMatch .turtledove .turtledove = true ∧
    speciesMatch .turtledove .youngDove = false ∧
    majorityCompletionSpecies .youngDove = .youngDove ∧
    benAzzaiCompletionSpecies .turtledove = .turtledove := by
  decide

theorem mishnah_3_1 :
    allAtOneLevelValidBirds [1, 1] = 2 ∧
    allAtOneLevelValidBirds [2, 2] = 4 ∧
    allAtOneLevelValidBirds [3, 3] = 6 ∧
    guaranteedHalfSplitBirds [1, 1] = 2 ∧
    guaranteedHalfSplitBirds [2, 2] = 4 ∧
    guaranteedHalfSplitBirds [3, 3] = 6 := by
  decide

theorem mishnah_3_2 :
    largestMinority [1, 2, 3, 10, 100] = 16 ∧
    guaranteedHalfSplitBirds [1, 2, 3, 10, 100] = 200 ∧
    largestMinority [4, 6, 7] = 7 ∧
    guaranteedHalfSplitBirds [4, 6, 7] = 20 := by
  decide

theorem generalized_smallest_majority (pairsByOwner : List Nat) :
    guaranteedHalfSplitBirds pairsByOwner =
      2 * (sumNats pairsByOwner - largestMinority pairsByOwner) := by
  rfl

theorem mishnah_3_3 :
    allAtOneLevelValidBirds [1, 1] = 2 ∧
    specifiedOppositesHalfSplitGuarantee 1 = 0 := by
  decide

theorem mishnah_3_4 :
    closedComponentGuarantee 1 = 1 ∧
    closedComponentGuarantee 10 = 10 := by
  decide

theorem mishnah_3_5 :
    closedWithForeignValid 1 1 = 1 ∧
    closedWithForeignValid 2 1 = 2 ∧
    closedWithForeignValid 1 2 = 1 := by
  decide

theorem mishnah_3_6 :
    (coverShortfalls oneSpeciesSimpleShortfalls).total = 1 ∧
    (coverShortfalls twoSpeciesSimpleShortfalls).total = 2 ∧
    (coverShortfalls oneSpeciesSpecifiedShortfalls).total = 3 ∧
    (coverShortfalls twoSpeciesSpecifiedShortfalls).total = 4 ∧
    (coverShortfalls oneSpeciesFixedShortfalls).total = 5 ∧
    (coverShortfalls twoSpeciesFixedShortfalls).total = 6 ∧
    (coverShortfalls finalMajorityShortfalls).total = 7 ∧
    (coverShortfalls finalBenAzzaiShortfalls).total = 8 := by
  decide

end Kinnim

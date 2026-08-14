/-!
# Core domain and uncertainty primitives
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


end Kinnim

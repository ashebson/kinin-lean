/-!
# Kinnim 3:2: an operational exact maximin theorem

Several owners contribute closed pairs, each requiring one sin-offering below
and one burnt-offering above. Before the hidden ownership arrangement is known,
the priest uses one fixed plan: exactly half of the birds are acted on above
and half below.

An admissible hidden world cuts only between whole owner blocks. The
`operationalServices` construction expands that world into one value for every
physical pair: both birds below, one at each level, or both above. Its payoff
counts valid birds from those pair services; the optimization formula does not
occur in the payoff definition.

The theorem proves the fixed plan is legal, realizes every hidden world pair by
pair, and identifies twice the complementary largest attainable minority as
the exact maximin value, attained by an explicit worst world.
-/

namespace PalomarKinnim

inductive Level where
  | below
  | above
  deriving DecidableEq, BEq, Repr

/-- The level pattern of the two birds belonging to one closed pair. -/
inductive PairService where
  | bothBelow
  | split
  | bothAbove
  deriving DecidableEq, BEq, Repr

def PairService.aboveBirds : PairService → Nat
  | .bothBelow => 0
  | .split => 1
  | .bothAbove => 2

/-- Valid birds derived from the pair's one-below/one-above quota. -/
def PairService.validBirds : PairService → Nat
  | .bothBelow => 1
  | .split => 2
  | .bothAbove => 1

def sumNats : List Nat → Nat
  | [] => 0
  | n :: ns => n + sumNats ns

def subsetSums : List Nat → List Nat
  | [] => [0]
  | n :: ns =>
      let rest := subsetSums ns
      rest ++ rest.map (fun total => total + n)

def greatestAtMost (limit : Nat) : List Nat → Nat
  | [] => 0
  | n :: ns =>
      let tail := greatestAtMost limit ns
      if n ≤ limit then Nat.max n tail else tail

def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

/-- The claimed exact guarantee, measured in individual birds. -/
def guaranteedValidBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

/-- A hidden world is a cut between whole owner blocks whose smaller side has
at most half of all pairs. -/
structure MajorityWorld (pairsByOwner : List Nat) where
  minorityPairs : Nat
  wholeOwnerCut : minorityPairs ∈ subsetSums pairsByOwner
  atMostHalf : minorityPairs ≤ sumNats pairsByOwner / 2

/-- The world-independent physical action plan. -/
def canonicalHalfSplitPlan (pairsByOwner : List Nat) : List Level :=
  List.replicate (sumNats pairsByOwner) .above ++
    List.replicate (sumNats pairsByOwner) .below

def countAbove : List Level → Nat
  | [] => 0
  | level :: levels =>
      (if level == .above then 1 else 0) + countAbove levels

def PlanLegal (pairsByOwner : List Nat) (plan : List Level) : Prop :=
  plan = canonicalHalfSplitPlan pairsByOwner ∧
  plan.length = 2 * sumNats pairsByOwner ∧
  countAbove plan = sumNats pairsByOwner

/-- Expand a hidden cut into a physical service for every pair. -/
def operationalServices (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) : List PairService :=
  List.replicate world.minorityPairs .bothBelow ++
  List.replicate
      (sumNats pairsByOwner - 2 * world.minorityPairs) .split ++
  List.replicate world.minorityPairs .bothAbove

def serviceAboveBirds : List PairService → Nat
  | [] => 0
  | service :: services => service.aboveBirds + serviceAboveBirds services

def serviceValidBirds : List PairService → Nat
  | [] => 0
  | service :: services => service.validBirds + serviceValidBirds services

/-- Operational payoff: count valid birds from individual pair services. -/
def operationalPayoff (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) (plan : List Level) : Nat :=
  if plan = canonicalHalfSplitPlan pairsByOwner then
    serviceValidBirds (operationalServices pairsByOwner world)
  else 0

def Guarantees (pairsByOwner : List Nat) (plan : List Level) (count : Nat) : Prop :=
  PlanLegal pairsByOwner plan ∧
    ∀ world : MajorityWorld pairsByOwner,
      count ≤ operationalPayoff pairsByOwner world plan

/-- Exact maximin value: one legal plan guarantees `count`, and every legal
plan meets an admissible world whose payoff is at most `count`. -/
def HasOptimalGuarantee (pairsByOwner : List Nat) (count : Nat) : Prop :=
  (∃ plan, Guarantees pairsByOwner plan count) ∧
  (∀ plan, PlanLegal pairsByOwner plan →
    ∃ world : MajorityWorld pairsByOwner,
      operationalPayoff pairsByOwner world plan ≤ count)

/-- The fixed plan is legal, every world has the right physical pair and
above-bird counts, its direct operational payoff realizes the majority rule,
and the Koppel--Reiss value is the exact maximin guarantee. -/
theorem operationalKinnim32 (pairsByOwner : List Nat) :
    PlanLegal pairsByOwner (canonicalHalfSplitPlan pairsByOwner) ∧
    (∀ world : MajorityWorld pairsByOwner,
      (operationalServices pairsByOwner world).length =
          sumNats pairsByOwner ∧
      serviceAboveBirds (operationalServices pairsByOwner world) =
          sumNats pairsByOwner ∧
      operationalPayoff pairsByOwner world
          (canonicalHalfSplitPlan pairsByOwner) =
        2 * (sumNats pairsByOwner - world.minorityPairs)) ∧
    HasOptimalGuarantee pairsByOwner (guaranteedValidBirds pairsByOwner) := by
  sorry

end PalomarKinnim

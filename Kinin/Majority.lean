import Kinin.Uncertainty
import Lean.Elab.Tactic.Omega

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

theorem greatestAtMost_le (limit : Nat) (values : List Nat) :
    greatestAtMost limit values ≤ limit := by
  induction values with
  | nil => simp [greatestAtMost]
  | cons x xs ih =>
      by_cases hx : x ≤ limit
      · simp [greatestAtMost, hx, Nat.max_le, ih]
      · simpa [greatestAtMost, hx] using ih

theorem le_greatestAtMost_of_mem
    {limit value : Nat} {values : List Nat}
    (member : value ∈ values) (bounded : value ≤ limit) :
    value ≤ greatestAtMost limit values := by
  induction values with
  | nil => simp at member
  | cons x xs ih =>
      simp only [List.mem_cons] at member
      by_cases hx : x ≤ limit
      · simp only [greatestAtMost, hx, if_pos]
        cases member with
        | inl equal =>
            subst x
            exact Nat.le_max_left _ _
        | inr tailMember =>
            exact Nat.le_trans (ih tailMember) (Nat.le_max_right _ _)
      · simp only [greatestAtMost, hx]
        cases member with
        | inl equal =>
            subst x
            exact False.elim (hx bounded)
        | inr tailMember => exact ih tailMember

theorem greatestAtMost_eq_zero_or_mem (limit : Nat) (values : List Nat) :
    greatestAtMost limit values = 0 ∨
      greatestAtMost limit values ∈ values := by
  induction values with
  | nil => simp [greatestAtMost]
  | cons x xs ih =>
      by_cases hx : x ≤ limit
      · simp only [greatestAtMost, hx, if_pos]
        rcases ih with zero | member
        · rw [zero]
          simp
        · by_cases htail : greatestAtMost limit xs ≤ x
          · right
            rw [show x.max (greatestAtMost limit xs) = x from Nat.max_eq_left htail]
            exact List.mem_cons_self
          · right
            rw [show x.max (greatestAtMost limit xs) = greatestAtMost limit xs from
              Nat.max_eq_right (Nat.le_of_not_ge htail)]
            exact List.mem_cons_of_mem x member
      · simp only [greatestAtMost, hx]
        rcases ih with zero | member
        · exact Or.inl zero
        · exact Or.inr (List.mem_cons_of_mem x member)

theorem zero_mem_subsetSums (values : List Nat) : 0 ∈ subsetSums values := by
  induction values with
  | nil => simp [subsetSums]
  | cons x xs ih =>
      simp only [subsetSums, List.mem_append]
      exact Or.inl ih

def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

theorem largestMinority_le_half (pairsByOwner : List Nat) :
    largestMinority pairsByOwner ≤ sumNats pairsByOwner / 2 := by
  exact greatestAtMost_le _ _

theorem largestMinority_mem (pairsByOwner : List Nat) :
    largestMinority pairsByOwner ∈ subsetSums pairsByOwner := by
  rcases greatestAtMost_eq_zero_or_mem
      (sumNats pairsByOwner / 2) (subsetSums pairsByOwner) with zero | member
  · simp only [largestMinority]
    rw [zero]
    exact zero_mem_subsetSums pairsByOwner
  · exact member

theorem minority_le_largest
    {pairsByOwner : List Nat} {minority : Nat}
    (wholeOwnerCut : minority ∈ subsetSums pairsByOwner)
    (atMostHalf : minority ≤ sumNats pairsByOwner / 2) :
    minority ≤ largestMinority pairsByOwner := by
  exact le_greatestAtMost_of_mem wholeOwnerCut atMostHalf

/-- Twice the complementary smallest majority, measured in birds. -/
def guaranteedHalfSplitBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

def allAtOneLevelValidBirds (pairsByOwner : List Nat) : Nat :=
  sumNats pairsByOwner

/-! ## Semantic maximin certificates for chapter 3 -/

/-- Once every bird is performed at one level, order is irrelevant; the
hidden world reduces to the number of sin- and burnt-offerings present. -/
structure OfferingInventory where
  sins : Nat
  burnts : Nat
  deriving DecidableEq, Repr

def oneLevelPayoff (world : OfferingInventory) : Offering → Nat
  | .sin => world.sins
  | .burnt => world.burnts

def oneLevelProblem (pairs : Nat) :
    UncertaintyProblem OfferingInventory Offering where
  admissible world := world.sins = pairs ∧ world.burnts = pairs
  legal _ := True
  payoff := oneLevelPayoff

theorem oneLevel_has_optimal_guarantee (pairs : Nat) :
    (oneLevelProblem pairs).HasOptimalGuarantee pairs := by
  constructor
  · refine ⟨.sin, True.intro, ?_⟩
    intro world admissible
    simp [oneLevelProblem, oneLevelPayoff, admissible.1]
  · intro action _
    refine ⟨{ sins := pairs, burnts := pairs }, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · cases action <;> simp [oneLevelProblem, oneLevelPayoff]

/-- An admissible uncertainty world for Koppel's argument is a cut made only
between whole owner blocks, with the smaller side containing at most half of
all pairs.  The Mishnah's `ha-merubeh kasher` rule assigns the complementary
majority twice as many valid individual birds. -/
structure MajorityWorld (pairsByOwner : List Nat) where
  minorityPairs : Nat
  wholeOwnerCut : minorityPairs ∈ subsetSums pairsByOwner
  atMostHalf : minorityPairs ≤ sumNats pairsByOwner / 2

def majorityPayoff (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) (_action : Unit) : Nat :=
  2 * (sumNats pairsByOwner - world.minorityPairs)

def majorityProblem (pairsByOwner : List Nat) :
    UncertaintyProblem (MajorityWorld pairsByOwner) Unit where
  admissible _ := True
  legal _ := True
  payoff := majorityPayoff pairsByOwner

def largestMinorityWorld (pairsByOwner : List Nat) :
    MajorityWorld pairsByOwner where
  minorityPairs := largestMinority pairsByOwner
  wholeOwnerCut := largestMinority_mem pairsByOwner
  atMostHalf := largestMinority_le_half pairsByOwner

theorem majority_has_optimal_guarantee (pairsByOwner : List Nat) :
    (majorityProblem pairsByOwner).HasOptimalGuarantee
      (guaranteedHalfSplitBirds pairsByOwner) := by
  constructor
  · refine ⟨(), True.intro, ?_⟩
    intro world _
    have bounded := minority_le_largest world.wholeOwnerCut world.atMostHalf
    simp only [majorityProblem, majorityPayoff, guaranteedHalfSplitBirds]
    omega
  · intro action _
    refine ⟨largestMinorityWorld pairsByOwner, True.intro, ?_⟩
    cases action
    exact Nat.le_refl _

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

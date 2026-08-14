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

/-! ## Pair-level realization of the majority payoff -/

/-- A block service records how many closed pairs had both birds performed
below, one bird at each level, or both birds above.  A same-level pair has one
valid bird; a split pair has two. -/
structure BlockService where
  belowPairs : Nat
  splitPairs : Nat
  abovePairs : Nat
  deriving DecidableEq, Repr

def BlockService.pairCount (service : BlockService) : Nat :=
  service.belowPairs + service.splitPairs + service.abovePairs

def BlockService.aboveBirds (service : BlockService) : Nat :=
  service.splitPairs + 2 * service.abovePairs

def BlockService.validBirds (service : BlockService) : Nat :=
  service.belowPairs + 2 * service.splitPairs + service.abovePairs

theorem BlockService.valid_eq_pairs_plus_splits (service : BlockService) :
    service.validBirds = service.pairCount + service.splitPairs := by
  simp only [BlockService.validBirds, BlockService.pairCount]
  omega

/-- An explicit pairing that maximizes split pairs for a block with `pairs`
closed pairs and `above` of its birds performed above. -/
def optimalBlockService (pairs above : Nat) : BlockService :=
  if above ≤ pairs then
    { belowPairs := pairs - above, splitPairs := above, abovePairs := 0 }
  else
    { belowPairs := 0, splitPairs := 2 * pairs - above,
      abovePairs := above - pairs }

theorem optimalBlockService_pairCount
    {pairs above : Nat} (capacity : above ≤ 2 * pairs) :
    (optimalBlockService pairs above).pairCount = pairs := by
  by_cases low : above ≤ pairs
  · simp [optimalBlockService, low, BlockService.pairCount]
  · simp [optimalBlockService, low, BlockService.pairCount]
    omega

theorem optimalBlockService_aboveBirds
    {pairs above : Nat} (capacity : above ≤ 2 * pairs) :
    (optimalBlockService pairs above).aboveBirds = above := by
  by_cases low : above ≤ pairs
  · simp [optimalBlockService, low, BlockService.aboveBirds]
  · simp [optimalBlockService, low, BlockService.aboveBirds]
    omega

theorem optimalBlockService_validBirds
    {pairs above : Nat} (capacity : above ≤ 2 * pairs) :
    (optimalBlockService pairs above).validBirds =
      pairs + Nat.min above (2 * pairs - above) := by
  by_cases low : above ≤ pairs
  · have minEq : Nat.min above (2 * pairs - above) = above := by
      apply Nat.min_eq_left
      omega
    simp [optimalBlockService, low, BlockService.validBirds, minEq]
    omega
  · have minEq : Nat.min above (2 * pairs - above) = 2 * pairs - above := by
      apply Nat.min_eq_right
      omega
    simp [optimalBlockService, low, BlockService.validBirds, minEq]
    omega

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

/-- The individual-pair realization of a whole-owner cut.  The minority block
is performed entirely below.  The complementary block supplies all birds
performed above, so exactly half of all birds are above. -/
def cutBlockServices (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) : BlockService × BlockService :=
  (optimalBlockService world.minorityPairs 0,
   optimalBlockService
      (sumNats pairsByOwner - world.minorityPairs)
      (sumNats pairsByOwner))

def cutServicePairCount (services : BlockService × BlockService) : Nat :=
  services.1.pairCount + services.2.pairCount

def cutServiceAboveBirds (services : BlockService × BlockService) : Nat :=
  services.1.aboveBirds + services.2.aboveBirds

def cutServiceValidBirds (services : BlockService × BlockService) : Nat :=
  services.1.validBirds + services.2.validBirds

theorem majorityWorld_twice_minority_le_total
    {pairsByOwner : List Nat} (world : MajorityWorld pairsByOwner) :
    2 * world.minorityPairs ≤ sumNats pairsByOwner := by
  have multiplied :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 world.atMostHalf
  simpa [Nat.mul_comm] using multiplied

theorem cutBlockServices_realize_majorityPayoff
    (pairsByOwner : List Nat) (world : MajorityWorld pairsByOwner) :
    cutServicePairCount (cutBlockServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    cutServiceAboveBirds (cutBlockServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    cutServiceValidBirds (cutBlockServices pairsByOwner world) =
        majorityPayoff pairsByOwner world () := by
  have twiceMinority := majorityWorld_twice_minority_le_total world
  have minorityCapacity : 0 ≤ 2 * world.minorityPairs := Nat.zero_le _
  have majorityCapacity :
      sumNats pairsByOwner ≤
        2 * (sumNats pairsByOwner - world.minorityPairs) := by
    omega
  have minorityPairs := optimalBlockService_pairCount minorityCapacity
  have majorityPairs := optimalBlockService_pairCount majorityCapacity
  have minorityAbove := optimalBlockService_aboveBirds minorityCapacity
  have majorityAbove := optimalBlockService_aboveBirds majorityCapacity
  have minorityValid := optimalBlockService_validBirds minorityCapacity
  have majorityValid := optimalBlockService_validBirds majorityCapacity
  have minorityMin :
      Nat.min 0 (2 * world.minorityPairs - 0) = 0 :=
    Nat.min_eq_left (Nat.zero_le _)
  have majorityMin :
      Nat.min (sumNats pairsByOwner)
          (2 * (sumNats pairsByOwner - world.minorityPairs) -
            sumNats pairsByOwner) =
        2 * (sumNats pairsByOwner - world.minorityPairs) -
          sumNats pairsByOwner := by
    apply Nat.min_eq_right
    omega
  constructor
  · simp only [cutServicePairCount, cutBlockServices]
    rw [minorityPairs, majorityPairs]
    omega
  constructor
  · simp only [cutServiceAboveBirds, cutBlockServices]
    rw [minorityAbove, majorityAbove]
    omega
  · simp only [cutServiceValidBirds, cutBlockServices]
    rw [minorityValid, majorityValid]
    rw [minorityMin, majorityMin]
    simp only [majorityPayoff]
    omega

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

/-- One replacement liability, stated in the same species/designation
vocabulary used for individual birds elsewhere in the model. -/
structure ReplacementNeed where
  species : BirdSpecies
  offering : Offering
  deriving DecidableEq, Repr

def Inventory.add (a b : Inventory) : Inventory where
  turtleSin := a.turtleSin + b.turtleSin
  turtleBurnt := a.turtleBurnt + b.turtleBurnt
  youngSin := a.youngSin + b.youngSin
  youngBurnt := a.youngBurnt + b.youngBurnt

def ReplacementNeed.inventory : ReplacementNeed → Inventory
  | ⟨.turtledove, .sin⟩ => { turtleSin := 1 }
  | ⟨.turtledove, .burnt⟩ => { turtleBurnt := 1 }
  | ⟨.youngDove, .sin⟩ => { youngSin := 1 }
  | ⟨.youngDove, .burnt⟩ => { youngBurnt := 1 }

def inventoryOfNeeds : List ReplacementNeed → Inventory
  | [] => {}
  | need :: needs => need.inventory.add (inventoryOfNeeds needs)

def turtleSinNeed : ReplacementNeed := ⟨.turtledove, .sin⟩
def turtleBurntNeed : ReplacementNeed := ⟨.turtledove, .burnt⟩
def youngSinNeed : ReplacementNeed := ⟨.youngDove, .sin⟩
def youngBurntNeed : ReplacementNeed := ⟨.youngDove, .burnt⟩

def Inventory.join (a b : Inventory) : Inventory where
  turtleSin := Nat.max a.turtleSin b.turtleSin
  turtleBurnt := Nat.max a.turtleBurnt b.turtleBurnt
  youngSin := Nat.max a.youngSin b.youngSin
  youngBurnt := Nat.max a.youngBurnt b.youngBurnt

def coverShortfalls : List Inventory → Inventory
  | [] => {}
  | x :: xs => x.join (coverShortfalls xs)

/-- `supply.Covers need` means that the proposed replacement inventory meets
every component of this possible shortfall. -/
def Inventory.Covers (supply need : Inventory) : Prop :=
  need.turtleSin ≤ supply.turtleSin ∧
  need.turtleBurnt ≤ supply.turtleBurnt ∧
  need.youngSin ≤ supply.youngSin ∧
  need.youngBurnt ≤ supply.youngBurnt

theorem Inventory.covers_refl (i : Inventory) : i.Covers i := by
  simp [Inventory.Covers]

theorem Inventory.covers_trans {a b c : Inventory}
    (hab : a.Covers b) (hbc : b.Covers c) : a.Covers c := by
  simp only [Inventory.Covers] at hab hbc ⊢
  exact ⟨Nat.le_trans hbc.1 hab.1,
    Nat.le_trans hbc.2.1 hab.2.1,
    Nat.le_trans hbc.2.2.1 hab.2.2.1,
    Nat.le_trans hbc.2.2.2 hab.2.2.2⟩

theorem Inventory.join_covers_left (a b : Inventory) :
    (a.join b).Covers a := by
  simp only [Inventory.Covers, Inventory.join]
  exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _,
    Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem Inventory.join_covers_right (a b : Inventory) :
    (a.join b).Covers b := by
  simp only [Inventory.Covers, Inventory.join]
  exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _,
    Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem Inventory.covers_join {supply a b : Inventory}
    (ha : supply.Covers a) (hb : supply.Covers b) :
    supply.Covers (a.join b) := by
  simp only [Inventory.Covers, Inventory.join] at ha hb ⊢
  exact ⟨(Nat.max_le).2 ⟨ha.1, hb.1⟩,
    (Nat.max_le).2 ⟨ha.2.1, hb.2.1⟩,
    (Nat.max_le).2 ⟨ha.2.2.1, hb.2.2.1⟩,
    (Nat.max_le).2 ⟨ha.2.2.2, hb.2.2.2⟩⟩

theorem coverShortfalls_covers_of_mem
    {scenario : Inventory} {scenarios : List Inventory}
    (member : scenario ∈ scenarios) :
    (coverShortfalls scenarios).Covers scenario := by
  induction scenarios with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      simp only [coverShortfalls]
      cases member with
      | inl equal =>
          subst first
          exact Inventory.join_covers_left _ _
      | inr tailMember =>
          exact Inventory.covers_trans
            (Inventory.join_covers_right _ _) (ih tailMember)

/-- Componentwise maximum is not only sufficient: it is the least inventory
that covers every possible shortfall scenario. -/
theorem coverShortfalls_minimal
    (scenarios : List Inventory) (supply : Inventory)
    (coversAll : ∀ scenario ∈ scenarios, supply.Covers scenario) :
    supply.Covers (coverShortfalls scenarios) := by
  induction scenarios with
  | nil => simp [coverShortfalls, Inventory.Covers]
  | cons first rest ih =>
      simp only [coverShortfalls]
      apply Inventory.covers_join
      · exact coversAll first (List.mem_cons_self)
      · apply ih
        intro scenario member
        exact coversAll scenario (List.mem_cons_of_mem first member)

def oneSpeciesSimpleShortfalls : List Inventory :=
  [inventoryOfNeeds [turtleBurntNeed]]

def twoSpeciesSimpleShortfalls : List Inventory :=
  [inventoryOfNeeds [turtleBurntNeed],
   inventoryOfNeeds [youngBurntNeed]]

def oneSpeciesSpecifiedShortfalls : List Inventory :=
  [inventoryOfNeeds [turtleSinNeed, turtleBurntNeed, turtleBurntNeed]]

def twoSpeciesSpecifiedShortfalls : List Inventory :=
  [inventoryOfNeeds [turtleSinNeed, turtleBurntNeed, turtleBurntNeed],
   inventoryOfNeeds [youngBurntNeed]]

def oneSpeciesFixedShortfalls : List Inventory :=
  [inventoryOfNeeds
    [turtleSinNeed, turtleSinNeed,
     turtleBurntNeed, turtleBurntNeed, turtleBurntNeed]]

def twoSpeciesFixedShortfalls : List Inventory :=
  [inventoryOfNeeds
    [turtleSinNeed, turtleSinNeed,
     turtleBurntNeed, turtleBurntNeed, turtleBurntNeed],
   inventoryOfNeeds [youngBurntNeed]]

def finalMajorityShortfalls : List Inventory :=
  [inventoryOfNeeds
    [turtleSinNeed, turtleSinNeed, turtleBurntNeed, turtleBurntNeed,
     youngSinNeed, youngBurntNeed, youngBurntNeed]]

def finalBenAzzaiShortfalls : List Inventory :=
  finalMajorityShortfalls ++
    [inventoryOfNeeds [youngSinNeed, youngSinNeed]]


end Kinnim

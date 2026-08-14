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

/-! ## An executable, world-independent half-split service -/

/-- The offering appropriate to a bird service level. -/
def offeringAtLevel : Level → Offering
  | .below => .sin
  | .above => .burnt

/-- A concrete action on a numbered unidentified bird. -/
def actionAtLevel (birdId : Nat) (level : Level) : PriestAction where
  birdId := birdId
  offering := offeringAtLevel level
  level := level

/-- One fixed strategy, selected before any hidden ownership world: act on the
first half above and the second half below.  Because the birds are
unidentified, the numerical labels express physical order only. -/
def canonicalHalfSplitActions (pairs : Nat) : List PriestAction :=
  (List.range pairs).map (fun id => actionAtLevel id .above) ++
  (List.range pairs).map (fun id => actionAtLevel (pairs + id) .below)

def countAboveActions : List PriestAction → Nat
  | [] => 0
  | action :: actions =>
      (if action.level == .above then 1 else 0) + countAboveActions actions

def actionBirdIds (actions : List PriestAction) : List Nat :=
  actions.map PriestAction.birdId

def ActionsLocallyValid (actions : List PriestAction) : Prop :=
  ∀ action ∈ actions, validLevel .bird action.offering action.level = true

theorem countAboveActions_map_above (ids : List Nat) :
    countAboveActions (ids.map (fun id => actionAtLevel id .above)) = ids.length := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
      change 1 + countAboveActions
        (ids.map (fun id => actionAtLevel id .above)) = ids.length + 1
      rw [ih]
      omega

theorem countAboveActions_map_below (offset : Nat) (ids : List Nat) :
    countAboveActions
        (ids.map (fun id => actionAtLevel (offset + id) .below)) = 0 := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
      have head :
          (if (actionAtLevel (offset + id) .below).level == .above then 1 else 0) = 0 :=
        rfl
      simp only [List.map, countAboveActions, head, Nat.zero_add]
      exact ih

theorem countAboveActions_append (first second : List PriestAction) :
    countAboveActions (first ++ second) =
      countAboveActions first + countAboveActions second := by
  induction first with
  | nil => simp [countAboveActions]
  | cons action actions ih => simp [countAboveActions, ih, Nat.add_assoc]

theorem canonicalHalfSplitActions_length (pairs : Nat) :
    (canonicalHalfSplitActions pairs).length = 2 * pairs := by
  simp [canonicalHalfSplitActions]
  omega

theorem canonicalHalfSplitActions_above (pairs : Nat) :
    countAboveActions (canonicalHalfSplitActions pairs) = pairs := by
  simp [canonicalHalfSplitActions, countAboveActions_append,
    countAboveActions_map_above, countAboveActions_map_below]

theorem canonicalHalfSplitActions_birdIds (pairs : Nat) :
    actionBirdIds (canonicalHalfSplitActions pairs) = List.range (2 * pairs) := by
  have ranges := (List.range_add (n := pairs) (m := pairs)).symm
  simp [actionBirdIds, canonicalHalfSplitActions, actionAtLevel,
    Function.comp_def]
  rw [show 2 * pairs = pairs + pairs by omega]
  exact ranges

theorem canonicalHalfSplitActions_noDuplicateBirds (pairs : Nat) :
    (actionBirdIds (canonicalHalfSplitActions pairs)).Nodup := by
  rw [canonicalHalfSplitActions_birdIds]
  exact List.nodup_range

theorem canonicalHalfSplitActions_locallyValid (pairs : Nat) :
    ActionsLocallyValid (canonicalHalfSplitActions pairs) := by
  intro action member
  simp only [canonicalHalfSplitActions, List.mem_append, List.mem_map] at member
  rcases member with ⟨id, _, equal⟩ | ⟨id, _, equal⟩
  · subst action
    simp [actionAtLevel, offeringAtLevel, validLevel, prescribedLevel]
  · subst action
    simp [actionAtLevel, offeringAtLevel, validLevel, prescribedLevel]

/-- The three possible level patterns of the two individual birds belonging
to a closed pair. -/
inductive PairService where
  | bothBelow
  | split
  | bothAbove
  deriving DecidableEq, Repr

def PairService.levels : PairService → List Level
  | .bothBelow => [.below, .below]
  | .split => [.below, .above]
  | .bothAbove => [.above, .above]

def countLevel (wanted : Level) : List Level → Nat
  | [] => 0
  | level :: levels =>
      (if level == wanted then 1 else 0) + countLevel wanted levels

/-- Validity is calculated from the closed pair's quota of one sin and one
burnt offering, not entered as a 1/2/1 answer table. -/
def PairService.validBirds (service : PairService) : Nat :=
  Nat.min (countLevel .below service.levels) 1 +
  Nat.min (countLevel .above service.levels) 1

def PairService.aboveBirds (service : PairService) : Nat :=
  countLevel .above service.levels

theorem PairService.validBirds_cases :
    PairService.bothBelow.validBirds = 1 ∧
    PairService.split.validBirds = 2 ∧
    PairService.bothAbove.validBirds = 1 := by
  decide

/-- Expand aggregate bookkeeping into one value for every physical pair. -/
def BlockService.individualPairs (service : BlockService) : List PairService :=
  List.replicate service.belowPairs .bothBelow ++
  List.replicate service.splitPairs .split ++
  List.replicate service.abovePairs .bothAbove

def individualPairCount (services : List PairService) : Nat := services.length

def individualAboveBirds : List PairService → Nat
  | [] => 0
  | service :: services => service.aboveBirds + individualAboveBirds services

def individualValidBirds : List PairService → Nat
  | [] => 0
  | service :: services => service.validBirds + individualValidBirds services

theorem individualAboveBirds_append (first second : List PairService) :
    individualAboveBirds (first ++ second) =
      individualAboveBirds first + individualAboveBirds second := by
  induction first with
  | nil => simp [individualAboveBirds]
  | cons service services ih => simp [individualAboveBirds, ih, Nat.add_assoc]

theorem individualValidBirds_append (first second : List PairService) :
    individualValidBirds (first ++ second) =
      individualValidBirds first + individualValidBirds second := by
  induction first with
  | nil => simp [individualValidBirds]
  | cons service services ih => simp [individualValidBirds, ih, Nat.add_assoc]

theorem individualAboveBirds_replicate (n : Nat) (service : PairService) :
    individualAboveBirds (List.replicate n service) = n * service.aboveBirds := by
  induction n with
  | zero => simp [individualAboveBirds]
  | succ n ih =>
      rw [List.replicate_succ, individualAboveBirds, ih, Nat.succ_mul]
      omega

theorem individualValidBirds_replicate (n : Nat) (service : PairService) :
    individualValidBirds (List.replicate n service) = n * service.validBirds := by
  induction n with
  | zero => simp [individualValidBirds]
  | succ n ih =>
      rw [List.replicate_succ, individualValidBirds, ih, Nat.succ_mul]
      omega

theorem individualPairs_pairCount (service : BlockService) :
    individualPairCount service.individualPairs = service.pairCount := by
  simp [individualPairCount, BlockService.individualPairs, BlockService.pairCount]
  omega

theorem individualPairs_aboveBirds (service : BlockService) :
    individualAboveBirds service.individualPairs = service.aboveBirds := by
  simp [BlockService.individualPairs, individualAboveBirds_append,
    individualAboveBirds_replicate, PairService.aboveBirds,
    PairService.levels, countLevel, BlockService.aboveBirds]
  omega

theorem individualPairs_validBirds (service : BlockService) :
    individualValidBirds service.individualPairs = service.validBirds := by
  simp [BlockService.individualPairs, individualValidBirds_append,
    individualValidBirds_replicate, PairService.validBirds,
    PairService.levels, countLevel, BlockService.validBirds]
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

/-! ## Hidden ownership allocations for the fixed action list -/

/-- A selection of whole owner blocks. -/
inductive OwnerSelection : List Nat → Type where
  | nil : OwnerSelection []
  | take {pairs rest} : OwnerSelection rest → OwnerSelection (pairs :: rest)
  | skip {pairs rest} : OwnerSelection rest → OwnerSelection (pairs :: rest)

def OwnerSelection.selectedPairs :
    {pairsByOwner : List Nat} → OwnerSelection pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerSelection.take pairs _ selection =>
      pairs + selection.selectedPairs
  | _, @OwnerSelection.skip _ _ selection => selection.selectedPairs

def OwnerSelection.unselectedPairs :
    {pairsByOwner : List Nat} → OwnerSelection pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerSelection.take _ _ selection => selection.unselectedPairs
  | _, @OwnerSelection.skip pairs _ selection =>
      pairs + selection.unselectedPairs

theorem OwnerSelection.selected_add_unselected
    {pairsByOwner : List Nat} (selection : OwnerSelection pairsByOwner) :
    selection.selectedPairs + selection.unselectedPairs = sumNats pairsByOwner := by
  induction selection with
  | nil => rfl
  | @take pairs rest selection ih =>
      simp [OwnerSelection.selectedPairs, OwnerSelection.unselectedPairs, sumNats]
      omega
  | @skip pairs rest selection ih =>
      simp [OwnerSelection.selectedPairs, OwnerSelection.unselectedPairs, sumNats]
      omega

theorem selection_exists_of_mem_subsetSums
    {pairsByOwner : List Nat} {target : Nat}
    (member : target ∈ subsetSums pairsByOwner) :
    ∃ selection : OwnerSelection pairsByOwner,
      selection.selectedPairs = target := by
  induction pairsByOwner generalizing target with
  | nil =>
      simp [subsetSums] at member
      subst target
      exact ⟨.nil, rfl⟩
  | cons pairs rest ih =>
      simp only [subsetSums, List.mem_append] at member
      rcases member with tailMember | addedMember
      · obtain ⟨selection, selected⟩ := ih tailMember
        exact ⟨.skip selection, selected⟩
      · simp only [List.mem_map] at addedMember
        obtain ⟨tailTarget, tailMember, equal⟩ := addedMember
        obtain ⟨selection, selected⟩ := ih tailMember
        refine ⟨.take selection, ?_⟩
        simp [OwnerSelection.selectedPairs, selected]
        omega

/-- For every owner block, record how many of its birds occupy the above half
of the fixed action list.  Capacity is the only local restriction. -/
inductive OwnerAllocation : List Nat → Type where
  | nil : OwnerAllocation []
  | cons {pairs rest} (above : Nat) (capacity : above ≤ 2 * pairs)
      (tail : OwnerAllocation rest) : OwnerAllocation (pairs :: rest)

def OwnerAllocation.aboveBirds :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner → Nat
  | _, .nil => 0
  | _, .cons above _ tail => above + tail.aboveBirds

def OwnerAllocation.validBirds :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerAllocation.cons pairs _ above _ tail =>
      (optimalBlockService pairs above).validBirds + tail.validBirds

def OwnerAllocation.deficit :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerAllocation.cons pairs _ above _ tail =>
      (pairs - above) + tail.deficit

def OwnerAllocation.excess :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerAllocation.cons pairs _ above _ tail =>
      (above - pairs) + tail.excess

def OwnerAllocation.lowPairs :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerAllocation.cons pairs _ above _ tail =>
      if above ≤ pairs then pairs + tail.lowPairs else tail.lowPairs

def OwnerAllocation.highPairs :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerAllocation.cons pairs _ above _ tail =>
      if above ≤ pairs then tail.highPairs else pairs + tail.highPairs

theorem OwnerAllocation.low_mem_subsetSums
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.lowPairs ∈ subsetSums pairsByOwner := by
  induction allocation with
  | nil => simp [OwnerAllocation.lowPairs, subsetSums]
  | @cons pairs rest above capacity tail ih =>
      by_cases low : above ≤ pairs
      · simp only [OwnerAllocation.lowPairs, low, if_pos, subsetSums,
          List.mem_append, List.mem_map]
        right
        exact ⟨tail.lowPairs, ih, by omega⟩
      · simp only [OwnerAllocation.lowPairs, low, subsetSums,
          List.mem_append]
        exact Or.inl ih

theorem OwnerAllocation.high_mem_subsetSums
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.highPairs ∈ subsetSums pairsByOwner := by
  induction allocation with
  | nil => simp [OwnerAllocation.highPairs, subsetSums]
  | @cons pairs rest above capacity tail ih =>
      by_cases low : above ≤ pairs
      · simp only [OwnerAllocation.highPairs, low, if_pos, subsetSums,
          List.mem_append]
        exact Or.inl ih
      · simp only [OwnerAllocation.highPairs, low, subsetSums,
          List.mem_append, List.mem_map]
        right
        exact ⟨tail.highPairs, ih, by simp [Nat.add_comm]⟩

theorem OwnerAllocation.low_add_high
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.lowPairs + allocation.highPairs = sumNats pairsByOwner := by
  induction allocation with
  | nil => rfl
  | @cons pairs rest above capacity tail ih =>
      by_cases low : above ≤ pairs
      · simp [OwnerAllocation.lowPairs, OwnerAllocation.highPairs, low, sumNats]
        omega
      · simp [OwnerAllocation.lowPairs, OwnerAllocation.highPairs, low, sumNats]
        omega

theorem OwnerAllocation.deficit_le_lowPairs
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.deficit ≤ allocation.lowPairs := by
  induction allocation with
  | nil => simp [OwnerAllocation.deficit, OwnerAllocation.lowPairs]
  | @cons pairs rest above capacity tail ih =>
      by_cases low : above ≤ pairs
      · simp [OwnerAllocation.deficit, OwnerAllocation.lowPairs, low]
        omega
      · simp [OwnerAllocation.deficit, OwnerAllocation.lowPairs, low]
        omega

theorem OwnerAllocation.excess_le_highPairs
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.excess ≤ allocation.highPairs := by
  induction allocation with
  | nil => simp [OwnerAllocation.excess, OwnerAllocation.highPairs]
  | @cons pairs rest above capacity tail ih =>
      by_cases low : above ≤ pairs
      · simp [OwnerAllocation.excess, OwnerAllocation.highPairs, low]
        omega
      · simp [OwnerAllocation.excess, OwnerAllocation.highPairs, low]
        omega

theorem OwnerAllocation.balance
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.aboveBirds + allocation.deficit =
      sumNats pairsByOwner + allocation.excess := by
  induction allocation with
  | nil => rfl
  | @cons pairs rest above capacity tail ih =>
      simp [OwnerAllocation.aboveBirds, OwnerAllocation.deficit,
        OwnerAllocation.excess, sumNats]
      omega

theorem optimalBlockService_valid_plus_deviation
    {pairs above : Nat} (capacity : above ≤ 2 * pairs) :
    (optimalBlockService pairs above).validBirds +
        (pairs - above) + (above - pairs) = 2 * pairs := by
  rw [optimalBlockService_validBirds capacity]
  by_cases low : above ≤ pairs
  · have minEq : Nat.min above (2 * pairs - above) = above := by
      apply Nat.min_eq_left
      omega
    rw [minEq]
    omega
  · have minEq : Nat.min above (2 * pairs - above) = 2 * pairs - above := by
      apply Nat.min_eq_right
      omega
    rw [minEq]
    omega

theorem OwnerAllocation.valid_plus_deviation
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    allocation.validBirds + allocation.deficit + allocation.excess =
      2 * sumNats pairsByOwner := by
  induction allocation with
  | nil => rfl
  | @cons pairs rest above capacity tail ih =>
      have localEq := optimalBlockService_valid_plus_deviation capacity
      simp [OwnerAllocation.validBirds, OwnerAllocation.deficit,
        OwnerAllocation.excess, sumNats]
      omega

/-- Fill the unselected owner blocks above their one-per-pair baseline until
`amount` excess birds have been placed. Selected blocks are entirely below. -/
def allocationFromSelection :
    {pairsByOwner : List Nat} → (selection : OwnerSelection pairsByOwner) →
      Nat → OwnerAllocation pairsByOwner
  | _, .nil, _ => .nil
  | _, @OwnerSelection.take pairs rest selection, amount =>
      .cons 0 (Nat.zero_le _) (allocationFromSelection selection amount)
  | _, @OwnerSelection.skip pairs rest selection, amount =>
      .cons (pairs + Nat.min amount pairs) (by
        calc
          pairs + Nat.min amount pairs ≤ pairs + pairs :=
            Nat.add_le_add_left (Nat.min_le_right amount pairs) pairs
          _ = 2 * pairs := by omega)
        (allocationFromSelection selection (amount - pairs))

theorem allocationFromSelection_spec
    {pairsByOwner : List Nat} (selection : OwnerSelection pairsByOwner)
    (amount : Nat) (fits : amount ≤ selection.unselectedPairs) :
    let allocation := allocationFromSelection selection amount
    allocation.aboveBirds = selection.unselectedPairs + amount ∧
    allocation.deficit = selection.selectedPairs ∧
    allocation.excess = amount := by
  induction selection generalizing amount with
  | nil =>
      have zero : amount = 0 := by
        simpa [OwnerSelection.unselectedPairs] using fits
      subst amount
      decide
  | @take pairs rest selection ih =>
      simp only [OwnerSelection.unselectedPairs] at fits
      obtain ⟨above, deficit, excess⟩ := ih amount fits
      simp only [allocationFromSelection, OwnerAllocation.aboveBirds,
        OwnerAllocation.deficit, OwnerAllocation.excess,
        OwnerSelection.unselectedPairs, OwnerSelection.selectedPairs]
      exact ⟨by simpa using above, by omega, by simpa using excess⟩
  | @skip pairs rest selection ih =>
      by_cases small : amount ≤ pairs
      · have tailFits : amount - pairs ≤ selection.unselectedPairs := by omega
        obtain ⟨above, deficit, excess⟩ := ih (amount - pairs) tailFits
        have minEq : Nat.min amount pairs = amount := Nat.min_eq_left small
        simp only [allocationFromSelection, OwnerAllocation.aboveBirds,
          OwnerAllocation.deficit, OwnerAllocation.excess,
          OwnerSelection.unselectedPairs, OwnerSelection.selectedPairs]
        rw [minEq]
        exact ⟨by omega, by omega, by omega⟩
      · have pairsLe : pairs ≤ amount := Nat.le_of_not_ge small
        have tailFits : amount - pairs ≤ selection.unselectedPairs := by
          simp only [OwnerSelection.unselectedPairs] at fits
          omega
        obtain ⟨above, deficit, excess⟩ := ih (amount - pairs) tailFits
        have minEq : Nat.min amount pairs = pairs := Nat.min_eq_right pairsLe
        simp only [allocationFromSelection, OwnerAllocation.aboveBirds,
          OwnerAllocation.deficit, OwnerAllocation.excess,
          OwnerSelection.unselectedPairs, OwnerSelection.selectedPairs]
        rw [minEq]
        exact ⟨by omega, by omega, by omega⟩

/-! ## Physical individual-bird ownership worlds -/

theorem countLevel_append (wanted : Level) (first second : List Level) :
    countLevel wanted (first ++ second) =
      countLevel wanted first + countLevel wanted second := by
  induction first with
  | nil => simp [countLevel]
  | cons level levels ih => simp [countLevel, ih, Nat.add_assoc]

theorem countLevel_le_length (wanted : Level) (levels : List Level) :
    countLevel wanted levels ≤ levels.length := by
  induction levels with
  | nil => simp [countLevel]
  | cons level levels ih =>
      cases level <;> cases wanted <;> simp [countLevel] <;> omega

theorem countLevel_below_add_above (levels : List Level) :
    countLevel .below levels + countLevel .above levels = levels.length := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      cases level <;> simp [countLevel] <;> omega

def ownerLevelsValid (pairs : Nat) (levels : List Level) : Nat :=
  Nat.min (countLevel .below levels) pairs +
  Nat.min (countLevel .above levels) pairs

theorem ownerLevelsValid_eq_optimalBlockService
    {pairs : Nat} {levels : List Level} (birdCount : levels.length = 2 * pairs) :
    ownerLevelsValid pairs levels =
      (optimalBlockService pairs (countLevel .above levels)).validBirds := by
  have partition := countLevel_below_add_above levels
  have capacity : countLevel .above levels ≤ 2 * pairs := by
    have bounded := countLevel_le_length .above levels
    omega
  rw [optimalBlockService_validBirds capacity]
  by_cases low : countLevel .above levels ≤ pairs
  · have belowLarge : pairs ≤ countLevel .below levels := by omega
    have formulaMin :
        Nat.min (countLevel .above levels)
            (2 * pairs - countLevel .above levels) =
          countLevel .above levels := by
      apply Nat.min_eq_left
      omega
    simp only [ownerLevelsValid]
    have belowMin :
        Nat.min (countLevel .below levels) pairs = pairs :=
      Nat.min_eq_right belowLarge
    have aboveMin :
        Nat.min (countLevel .above levels) pairs = countLevel .above levels :=
      Nat.min_eq_left low
    rw [belowMin, aboveMin, formulaMin]
  · have aboveLarge : pairs ≤ countLevel .above levels := Nat.le_of_not_ge low
    have belowSmall : countLevel .below levels ≤ pairs := by omega
    have formulaMin :
        Nat.min (countLevel .above levels)
            (2 * pairs - countLevel .above levels) =
          2 * pairs - countLevel .above levels := by
      apply Nat.min_eq_right
      omega
    simp only [ownerLevelsValid]
    have belowMin :
        Nat.min (countLevel .below levels) pairs = countLevel .below levels :=
      Nat.min_eq_left belowSmall
    have aboveMin :
        Nat.min (countLevel .above levels) pairs = pairs :=
      Nat.min_eq_right aboveLarge
    rw [belowMin, aboveMin, formulaMin]
    omega

/-- For each owner, retain one entry for every physical bird and the level at
which that individual bird is acted upon. -/
inductive OwnerBirdAssignment : List Nat → Type where
  | nil : OwnerBirdAssignment []
  | cons {pairs rest} (levels : List Level) (birdCount : levels.length = 2 * pairs)
      (tail : OwnerBirdAssignment rest) : OwnerBirdAssignment (pairs :: rest)

def OwnerBirdAssignment.aboveBirds :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → Nat
  | _, .nil => 0
  | _, .cons levels _ tail => countLevel .above levels + tail.aboveBirds

def OwnerBirdAssignment.validBirds :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerBirdAssignment.cons pairs _ levels _ tail =>
      ownerLevelsValid pairs levels + tail.validBirds

def OwnerBirdAssignment.toAllocation :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner →
      OwnerAllocation pairsByOwner
  | _, .nil => .nil
  | _, @OwnerBirdAssignment.cons pairs _ levels birdCount tail =>
      .cons (countLevel .above levels) (by
        have bounded := countLevel_le_length .above levels
        omega) tail.toAllocation

theorem OwnerBirdAssignment.toAllocation_aboveBirds
    {pairsByOwner : List Nat} (assignment : OwnerBirdAssignment pairsByOwner) :
    assignment.toAllocation.aboveBirds = assignment.aboveBirds := by
  induction assignment with
  | nil => rfl
  | cons levels birdCount tail ih =>
      simp [OwnerBirdAssignment.toAllocation, OwnerAllocation.aboveBirds,
        OwnerBirdAssignment.aboveBirds, ih]

/-- Compression to one above-count per owner loses no validity information. -/
theorem OwnerBirdAssignment.valid_eq_compressed
    {pairsByOwner : List Nat} (assignment : OwnerBirdAssignment pairsByOwner) :
    assignment.validBirds = assignment.toAllocation.validBirds := by
  induction assignment with
  | nil => rfl
  | @cons pairs rest levels birdCount tail ih =>
      simp only [OwnerBirdAssignment.validBirds,
        OwnerBirdAssignment.toAllocation, OwnerAllocation.validBirds]
      rw [ownerLevelsValid_eq_optimalBlockService birdCount, ih]

/-- Consequently, permuting an owner's physical birds without changing the
number placed above cannot change that owner's valid count. -/
theorem ownerLevelsValid_order_irrelevant
    {pairs : Nat} {first second : List Level}
    (firstCount : first.length = 2 * pairs)
    (secondCount : second.length = 2 * pairs)
    (sameAbove : countLevel .above first = countLevel .above second) :
    ownerLevelsValid pairs first = ownerLevelsValid pairs second := by
  rw [ownerLevelsValid_eq_optimalBlockService firstCount,
    ownerLevelsValid_eq_optimalBlockService secondCount, sameAbove]

theorem countLevel_above_replicate_above (n : Nat) :
    countLevel .above (List.replicate n .above) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, countLevel, ih]
      omega

theorem countLevel_above_replicate_below (n : Nat) :
    countLevel .above (List.replicate n .below) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countLevel, ih]

def levelsFromAbove (pairs above : Nat) : List Level :=
  List.replicate above .above ++ List.replicate (2 * pairs - above) .below

theorem levelsFromAbove_length {pairs above : Nat} (capacity : above ≤ 2 * pairs) :
    (levelsFromAbove pairs above).length = 2 * pairs := by
  simp [levelsFromAbove]
  omega

theorem levelsFromAbove_above {pairs above : Nat} (_capacity : above ≤ 2 * pairs) :
    countLevel .above (levelsFromAbove pairs above) = above := by
  simp [levelsFromAbove, countLevel_append,
    countLevel_above_replicate_above, countLevel_above_replicate_below]

/-- Every aggregate allocation has a concrete realization by individual bird
level assignments. -/
def assignmentFromAllocation :
    {pairsByOwner : List Nat} → OwnerAllocation pairsByOwner →
      OwnerBirdAssignment pairsByOwner
  | _, .nil => .nil
  | _, @OwnerAllocation.cons pairs _ above capacity tail =>
      .cons (levelsFromAbove pairs above) (levelsFromAbove_length capacity)
        (assignmentFromAllocation tail)

theorem assignmentFromAllocation_aboveBirds
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    (assignmentFromAllocation allocation).aboveBirds = allocation.aboveBirds := by
  induction allocation with
  | nil => rfl
  | @cons pairs rest above capacity tail ih =>
      simp [assignmentFromAllocation, OwnerBirdAssignment.aboveBirds,
        OwnerAllocation.aboveBirds, levelsFromAbove_above capacity, ih]

theorem assignmentFromAllocation_validBirds
    {pairsByOwner : List Nat} (allocation : OwnerAllocation pairsByOwner) :
    (assignmentFromAllocation allocation).validBirds = allocation.validBirds := by
  induction allocation with
  | nil => rfl
  | @cons pairs rest above capacity tail ih =>
      simp only [assignmentFromAllocation, OwnerBirdAssignment.validBirds,
        OwnerAllocation.validBirds]
      rw [ownerLevelsValid_eq_optimalBlockService
        (levelsFromAbove_length capacity), levelsFromAbove_above capacity, ih]

/-- A full physical world, before compression: every owner contributes exactly
two birds per pair, and globally exactly half of all birds receive above-level
actions. -/
structure PhysicalOwnershipWorld (pairsByOwner : List Nat) where
  assignment : OwnerBirdAssignment pairsByOwner
  halfAbove : assignment.aboveBirds = sumNats pairsByOwner

/-- A hidden ownership world assigns the fixed above-half positions among the
owner blocks. Every owner has at most twice its pair count in birds, and the
fixed strategy places exactly half of all birds above. -/
structure HiddenOwnershipWorld (pairsByOwner : List Nat) where
  allocation : OwnerAllocation pairsByOwner
  halfAbove : allocation.aboveBirds = sumNats pairsByOwner

def PhysicalOwnershipWorld.toHidden
    {pairsByOwner : List Nat} (world : PhysicalOwnershipWorld pairsByOwner) :
    HiddenOwnershipWorld pairsByOwner where
  allocation := world.assignment.toAllocation
  halfAbove := by
    rw [world.assignment.toAllocation_aboveBirds]
    exact world.halfAbove

/-- Operational payoff: count valid birds owner by owner. No majority or
subset-sum formula occurs in this definition. -/
def ownershipMajorityPayoff (pairsByOwner : List Nat)
    (world : HiddenOwnershipWorld pairsByOwner)
    (actions : List PriestAction) : Nat :=
  if actions == canonicalHalfSplitActions (sumNats pairsByOwner) then
    world.allocation.validBirds
  else 0

theorem HiddenOwnershipWorld.deficit_eq_excess
    {pairsByOwner : List Nat} (world : HiddenOwnershipWorld pairsByOwner) :
    world.allocation.deficit = world.allocation.excess := by
  have balance := world.allocation.balance
  rw [world.halfAbove] at balance
  omega

theorem HiddenOwnershipWorld.deficit_le_largestMinority
    {pairsByOwner : List Nat} (world : HiddenOwnershipWorld pairsByOwner) :
    world.allocation.deficit ≤ largestMinority pairsByOwner := by
  have lowPlusHigh := world.allocation.low_add_high
  have equalDeviation := world.deficit_eq_excess
  by_cases lowHalf :
      world.allocation.lowPairs ≤ sumNats pairsByOwner / 2
  · exact Nat.le_trans world.allocation.deficit_le_lowPairs
      (minority_le_largest world.allocation.low_mem_subsetSums lowHalf)
  · have highHalf :
        world.allocation.highPairs ≤ sumNats pairsByOwner / 2 := by
      omega
    exact Nat.le_trans
      (by
        rw [equalDeviation]
        exact world.allocation.excess_le_highPairs)
      (minority_le_largest world.allocation.high_mem_subsetSums highHalf)

theorem ownershipMajorityPayoff_lower_bound
    (pairsByOwner : List Nat) (world : HiddenOwnershipWorld pairsByOwner) :
    guaranteedHalfSplitBirds pairsByOwner ≤
      ownershipMajorityPayoff pairsByOwner world
        (canonicalHalfSplitActions (sumNats pairsByOwner)) := by
  have deviation := world.allocation.valid_plus_deviation
  have equalDeviation := world.deficit_eq_excess
  have bounded := world.deficit_le_largestMinority
  have minorityHalf := largestMinority_le_half pairsByOwner
  simp only [ownershipMajorityPayoff, beq_self_eq_true, if_true,
    guaranteedHalfSplitBirds]
  omega

theorem exists_worstHiddenOwnershipWorld (pairsByOwner : List Nat) :
    ∃ world : HiddenOwnershipWorld pairsByOwner,
      ownershipMajorityPayoff pairsByOwner world
          (canonicalHalfSplitActions (sumNats pairsByOwner)) =
        guaranteedHalfSplitBirds pairsByOwner := by
  obtain ⟨selection, selected⟩ := selection_exists_of_mem_subsetSums
    (largestMinority_mem pairsByOwner)
  have totals := selection.selected_add_unselected
  have minorityHalf := largestMinority_le_half pairsByOwner
  have fits : largestMinority pairsByOwner ≤ selection.unselectedPairs := by
    omega
  let allocation :=
    allocationFromSelection selection (largestMinority pairsByOwner)
  have specification := allocationFromSelection_spec selection
    (largestMinority pairsByOwner) fits
  refine ⟨{ allocation := allocation, halfAbove := ?_ }, ?_⟩
  · dsimp only [allocation]
    rw [specification.1]
    omega
  · have deviation := allocation.valid_plus_deviation
    have deficit := specification.2.1
    have excess := specification.2.2
    simp only [ownershipMajorityPayoff, beq_self_eq_true, if_true,
      guaranteedHalfSplitBirds]
    dsimp only [allocation] at deviation ⊢
    omega

/-- The public physical evaluator counts directly over each owner's individual
bird assignments. -/
def physicalMajorityPayoff (pairsByOwner : List Nat)
    (world : PhysicalOwnershipWorld pairsByOwner)
    (actions : List PriestAction) : Nat :=
  if actions == canonicalHalfSplitActions (sumNats pairsByOwner) then
    world.assignment.validBirds
  else 0

theorem physicalMajorityPayoff_eq_compressed
    (pairsByOwner : List Nat) (world : PhysicalOwnershipWorld pairsByOwner)
    (actions : List PriestAction) :
    physicalMajorityPayoff pairsByOwner world actions =
      ownershipMajorityPayoff pairsByOwner world.toHidden actions := by
  simp only [physicalMajorityPayoff, ownershipMajorityPayoff,
    PhysicalOwnershipWorld.toHidden]
  by_cases canonical :
      actions == canonicalHalfSplitActions (sumNats pairsByOwner)
  · simp only [canonical, if_true]
    exact world.assignment.valid_eq_compressed
  · simp [canonical]

theorem physicalMajorityPayoff_lower_bound
    (pairsByOwner : List Nat) (world : PhysicalOwnershipWorld pairsByOwner) :
    guaranteedHalfSplitBirds pairsByOwner ≤
      physicalMajorityPayoff pairsByOwner world
        (canonicalHalfSplitActions (sumNats pairsByOwner)) := by
  rw [physicalMajorityPayoff_eq_compressed]
  exact ownershipMajorityPayoff_lower_bound pairsByOwner world.toHidden

theorem exists_worstPhysicalOwnershipWorld (pairsByOwner : List Nat) :
    ∃ world : PhysicalOwnershipWorld pairsByOwner,
      physicalMajorityPayoff pairsByOwner world
          (canonicalHalfSplitActions (sumNats pairsByOwner)) =
        guaranteedHalfSplitBirds pairsByOwner := by
  obtain ⟨hidden, worst⟩ := exists_worstHiddenOwnershipWorld pairsByOwner
  let assignment := assignmentFromAllocation hidden.allocation
  have halfAbove : assignment.aboveBirds = sumNats pairsByOwner := by
    dsimp only [assignment]
    rw [assignmentFromAllocation_aboveBirds, hidden.halfAbove]
  refine ⟨{ assignment := assignment, halfAbove := halfAbove }, ?_⟩
  have hiddenValid :
      hidden.allocation.validBirds = guaranteedHalfSplitBirds pairsByOwner := by
    simpa [ownershipMajorityPayoff] using worst
  simp only [physicalMajorityPayoff, beq_self_eq_true, if_true]
  dsimp only [assignment]
  rw [assignmentFromAllocation_validBirds, hiddenValid]

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

/-- The physical pair-by-pair outcome induced by a hidden whole-owner cut. -/
def cutIndividualServices (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) : List PairService :=
  (cutBlockServices pairsByOwner world).1.individualPairs ++
  (cutBlockServices pairsByOwner world).2.individualPairs

def HalfSplitLegal (pairsByOwner : List Nat)
    (actions : List PriestAction) : Prop :=
  actions = canonicalHalfSplitActions (sumNats pairsByOwner) ∧
  actions.length = 2 * sumNats pairsByOwner ∧
  countAboveActions actions = sumNats pairsByOwner ∧
  ActionsLocallyValid actions

theorem canonicalHalfSplitLegal (pairsByOwner : List Nat) :
    HalfSplitLegal pairsByOwner
      (canonicalHalfSplitActions (sumNats pairsByOwner)) := by
  refine ⟨rfl, canonicalHalfSplitActions_length _,
    canonicalHalfSplitActions_above _, canonicalHalfSplitActions_locallyValid _⟩

/-- Unlike `majorityPayoff`, this evaluator does not contain Koppel's formula.
It counts validity across the individual pair services produced by the fixed
action list.  The equality check makes noncanonical action lists score zero;
all legal strategies are definitionally the fixed, pre-world list. -/
def operationalMajorityPayoff (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) (actions : List PriestAction) : Nat :=
  if actions == canonicalHalfSplitActions (sumNats pairsByOwner) then
    individualValidBirds (cutIndividualServices pairsByOwner world)
  else 0

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

theorem cutIndividualServices_realize_majorityPayoff
    (pairsByOwner : List Nat) (world : MajorityWorld pairsByOwner) :
    individualPairCount (cutIndividualServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    individualAboveBirds (cutIndividualServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    individualValidBirds (cutIndividualServices pairsByOwner world) =
        majorityPayoff pairsByOwner world () := by
  obtain ⟨pairCount, aboveCount, validCount⟩ :=
    cutBlockServices_realize_majorityPayoff pairsByOwner world
  constructor
  · simp only [cutIndividualServices, individualPairCount, List.length_append]
    change individualPairCount
        (cutBlockServices pairsByOwner world).1.individualPairs +
      individualPairCount
        (cutBlockServices pairsByOwner world).2.individualPairs = _
    rw [individualPairs_pairCount, individualPairs_pairCount]
    simpa [cutServicePairCount] using pairCount
  constructor
  · simp only [cutIndividualServices, individualAboveBirds_append]
    rw [individualPairs_aboveBirds, individualPairs_aboveBirds]
    simpa [cutServiceAboveBirds] using aboveCount
  · simp only [cutIndividualServices, individualValidBirds_append]
    rw [individualPairs_validBirds, individualPairs_validBirds]
    simpa [cutServiceValidBirds] using validCount

theorem operationalMajorityPayoff_eq_formula
    (pairsByOwner : List Nat) (world : MajorityWorld pairsByOwner)
    (actions : List PriestAction) (legal : HalfSplitLegal pairsByOwner actions) :
    operationalMajorityPayoff pairsByOwner world actions =
      majorityPayoff pairsByOwner world () := by
  simp only [operationalMajorityPayoff, legal.1, beq_self_eq_true, if_true]
  exact (cutIndividualServices_realize_majorityPayoff pairsByOwner world).2.2

def majorityProblem (pairsByOwner : List Nat) :
    UncertaintyProblem (PhysicalOwnershipWorld pairsByOwner) (List PriestAction) where
  admissible _ := True
  legal := HalfSplitLegal pairsByOwner
  payoff := physicalMajorityPayoff pairsByOwner

def largestMinorityWorld (pairsByOwner : List Nat) :
    MajorityWorld pairsByOwner where
  minorityPairs := largestMinority pairsByOwner
  wholeOwnerCut := largestMinority_mem pairsByOwner
  atMostHalf := largestMinority_le_half pairsByOwner

theorem majority_has_optimal_guarantee (pairsByOwner : List Nat) :
    (majorityProblem pairsByOwner).HasOptimalGuarantee
      (guaranteedHalfSplitBirds pairsByOwner) := by
  constructor
  · refine ⟨canonicalHalfSplitActions (sumNats pairsByOwner),
      canonicalHalfSplitLegal pairsByOwner, ?_⟩
    intro world _
    exact physicalMajorityPayoff_lower_bound pairsByOwner world
  · intro actions legal
    obtain ⟨world, worst⟩ := exists_worstPhysicalOwnershipWorld pairsByOwner
    refine ⟨world, True.intro, ?_⟩
    simp only [majorityProblem]
    rw [legal.1, worst]
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

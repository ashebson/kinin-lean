import Kinin.Majority

/-!
# Mishnah Kinnim, chapter 3
-/

namespace Kinnim

theorem mishnah_3_1 :
    (∀ pairs, (oneLevelProblem pairs).HasOptimalGuarantee pairs) ∧
    allAtOneLevelValidBirds [1, 1] = 2 ∧
    allAtOneLevelValidBirds [2, 2] = 4 ∧
    allAtOneLevelValidBirds [3, 3] = 6 ∧
    guaranteedHalfSplitBirds [1, 1] = 2 ∧
    guaranteedHalfSplitBirds [2, 2] = 4 ∧
    guaranteedHalfSplitBirds [3, 3] = 6 := by
  constructor
  · exact oneLevel_has_optimal_guarantee
  · decide

theorem mishnah_3_2 :
    (∀ pairsByOwner,
      (∀ world : PhysicalOwnershipWorld pairsByOwner,
        world.assignment.levels.Perm
            (actionLevels
              (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
        guaranteedHalfSplitBirds pairsByOwner ≤ world.assignment.validBirds) ∧
      (∃ worst : PhysicalOwnershipWorld pairsByOwner,
        worst.assignment.levels.Perm
            (actionLevels
              (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
        worst.assignment.validBirds =
          guaranteedHalfSplitBirds pairsByOwner)) ∧
    (∀ pairsByOwner,
      HalfSplitLegal pairsByOwner
        (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
    (∀ pairsByOwner world,
      cutServicePairCount (cutBlockServices pairsByOwner world) =
          sumNats pairsByOwner ∧
      cutServiceAboveBirds (cutBlockServices pairsByOwner world) =
          sumNats pairsByOwner ∧
      cutServiceValidBirds (cutBlockServices pairsByOwner world) =
          majorityPayoff pairsByOwner world ()) ∧
    (∀ pairsByOwner world,
      individualPairCount (cutIndividualServices pairsByOwner world) =
          sumNats pairsByOwner ∧
      individualAboveBirds (cutIndividualServices pairsByOwner world) =
          sumNats pairsByOwner ∧
      individualValidBirds (cutIndividualServices pairsByOwner world) =
          majorityPayoff pairsByOwner world ()) ∧
    largestMinority [1, 2, 3, 10, 100] = 16 ∧
    guaranteedHalfSplitBirds [1, 2, 3, 10, 100] = 200 ∧
    largestMinority [4, 6, 7] = 7 ∧
    guaranteedHalfSplitBirds [4, 6, 7] = 20 := by
  constructor
  · intro pairsByOwner
    constructor
    · intro world
      refine ⟨world.compatibleWithCanonicalPlan, ?_⟩
      simpa [physicalMajorityPayoff] using
        physicalMajorityPayoff_lower_bound pairsByOwner world
    · obtain ⟨worst, exactWorst⟩ :=
        exists_worstPhysicalOwnershipWorld pairsByOwner
      refine ⟨worst, worst.compatibleWithCanonicalPlan, ?_⟩
      simpa [physicalMajorityPayoff] using exactWorst
  constructor
  · exact canonicalHalfSplitLegal
  constructor
  · exact cutBlockServices_realize_majorityPayoff
  constructor
  · exact cutIndividualServices_realize_majorityPayoff
  · decide

theorem generalized_smallest_majority (pairsByOwner : List Nat) :
    (∀ world : PhysicalOwnershipWorld pairsByOwner,
      world.assignment.levels.Perm
          (actionLevels
            (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
      guaranteedHalfSplitBirds pairsByOwner ≤ world.assignment.validBirds) ∧
    (∃ worst : PhysicalOwnershipWorld pairsByOwner,
      worst.assignment.levels.Perm
          (actionLevels
            (canonicalHalfSplitActions (sumNats pairsByOwner))) ∧
      worst.assignment.validBirds = guaranteedHalfSplitBirds pairsByOwner) := by
  constructor
  · intro world
    refine ⟨world.compatibleWithCanonicalPlan, ?_⟩
    simpa [physicalMajorityPayoff] using
      physicalMajorityPayoff_lower_bound pairsByOwner world
  · obtain ⟨worst, exactWorst⟩ :=
      exists_worstPhysicalOwnershipWorld pairsByOwner
    refine ⟨worst, worst.compatibleWithCanonicalPlan, ?_⟩
    simpa [physicalMajorityPayoff] using exactWorst

theorem generalized_smallest_majority_pair_service
    (pairsByOwner : List Nat) (world : MajorityWorld pairsByOwner) :
    cutServicePairCount (cutBlockServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    cutServiceAboveBirds (cutBlockServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    cutServiceValidBirds (cutBlockServices pairsByOwner world) =
        majorityPayoff pairsByOwner world () :=
  cutBlockServices_realize_majorityPayoff pairsByOwner world

theorem generalized_smallest_majority_individual_service
    (pairsByOwner : List Nat) (world : MajorityWorld pairsByOwner) :
    individualPairCount (cutIndividualServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    individualAboveBirds (cutIndividualServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    individualValidBirds (cutIndividualServices pairsByOwner world) =
        majorityPayoff pairsByOwner world () :=
  cutIndividualServices_realize_majorityPayoff pairsByOwner world

theorem generalized_smallest_majority_operational_lower_bound
    (pairsByOwner : List Nat) (world : PhysicalOwnershipWorld pairsByOwner) :
    guaranteedHalfSplitBirds pairsByOwner ≤
      physicalMajorityPayoff pairsByOwner world
        (canonicalHalfSplitActions (sumNats pairsByOwner)) :=
  physicalMajorityPayoff_lower_bound pairsByOwner world

theorem generalized_smallest_majority_worst_world (pairsByOwner : List Nat) :
    ∃ world : PhysicalOwnershipWorld pairsByOwner,
      physicalMajorityPayoff pairsByOwner world
          (canonicalHalfSplitActions (sumNats pairsByOwner)) =
        guaranteedHalfSplitBirds pairsByOwner :=
  exists_worstPhysicalOwnershipWorld pairsByOwner

theorem generalized_owner_order_irrelevant
    {pairs : Nat} {first second : List Level}
    (firstCount : first.length = 2 * pairs)
    (secondCount : second.length = 2 * pairs)
    (sameAbove : countLevel .above first = countLevel .above second) :
    ownerLevelsValid pairs first = ownerLevelsValid pairs second :=
  ownerLevelsValid_order_irrelevant firstCount secondCount sameAbove

theorem generalized_smallest_majority_no_better
    (pairsByOwner : List Nat) {larger : Nat}
    (h : guaranteedHalfSplitBirds pairsByOwner < larger) :
    ¬ ∀ world : PhysicalOwnershipWorld pairsByOwner,
      larger ≤ world.assignment.validBirds := by
  intro allegedLowerBound
  obtain ⟨worst, exactWorst⟩ :=
    exists_worstPhysicalOwnershipWorld pairsByOwner
  have contradicted := allegedLowerBound worst
  simp only [physicalMajorityPayoff, beq_self_eq_true, if_true] at exactWorst
  omega

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
    (∀ (scenarios : List Inventory) (scenario : Inventory), scenario ∈ scenarios →
      (coverShortfalls scenarios).Covers scenario) ∧
    (∀ (scenarios : List Inventory) (supply : Inventory),
      (∀ scenario ∈ scenarios, supply.Covers scenario) →
      supply.Covers (coverShortfalls scenarios)) ∧
    (coverShortfalls oneSpeciesSimpleShortfalls).total = 1 ∧
    (coverShortfalls twoSpeciesSimpleShortfalls).total = 2 ∧
    (coverShortfalls oneSpeciesSpecifiedShortfalls).total = 3 ∧
    (coverShortfalls twoSpeciesSpecifiedShortfalls).total = 4 ∧
    (coverShortfalls oneSpeciesFixedShortfalls).total = 5 ∧
    (coverShortfalls twoSpeciesFixedShortfalls).total = 6 ∧
    (coverShortfalls finalMajorityShortfalls).total = 7 ∧
    (coverShortfalls finalBenAzzaiShortfalls).total = 8 := by
  constructor
  · intro scenarios scenario member
    exact coverShortfalls_covers_of_mem member
  constructor
  · exact coverShortfalls_minimal
  · decide

end Kinnim

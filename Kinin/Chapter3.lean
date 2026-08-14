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
      (majorityProblem pairsByOwner).HasOptimalGuarantee
        (guaranteedHalfSplitBirds pairsByOwner)) ∧
    largestMinority [1, 2, 3, 10, 100] = 16 ∧
    guaranteedHalfSplitBirds [1, 2, 3, 10, 100] = 200 ∧
    largestMinority [4, 6, 7] = 7 ∧
    guaranteedHalfSplitBirds [4, 6, 7] = 20 := by
  constructor
  · exact majority_has_optimal_guarantee
  · decide

theorem generalized_smallest_majority (pairsByOwner : List Nat) :
    (majorityProblem pairsByOwner).HasOptimalGuarantee
      (guaranteedHalfSplitBirds pairsByOwner) :=
  majority_has_optimal_guarantee pairsByOwner

theorem generalized_smallest_majority_no_better
    (pairsByOwner : List Nat) {larger : Nat}
    (h : guaranteedHalfSplitBirds pairsByOwner < larger) :
    ¬ ∃ action,
      (majorityProblem pairsByOwner).Guarantees action larger := by
  exact UncertaintyProblem.no_strategy_guarantees_more
    (majority_has_optimal_guarantee pairsByOwner) h

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

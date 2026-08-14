import Kinin.Core

/-!
# Mishnah Kinnim, chapter 1
-/

namespace Kinnim

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


end Kinnim

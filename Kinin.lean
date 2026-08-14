/-!
# Kinnim 1:1

A small formal model of the opening mishnah of tractate Kinnim.

The mishnah assigns a place of service to each combination of species and
offering:

* a bird sin-offering is performed below;
* an animal sin-offering is performed above;
* a bird burnt-offering is performed above;
* an animal burnt-offering is performed below.

Performing any one of these at the other level is invalid.
-/

namespace Kinnim

/-- The two kinds of creature relevant to the opening mishnah. -/
inductive Species where
  | bird
  | animal
  deriving DecidableEq, Repr

/-- The two offering designations compared by the opening mishnah. -/
inductive Offering where
  | sin
  | burnt
  deriving DecidableEq, Repr

/-- The two regions of the altar distinguished by the mishnah. -/
inductive Level where
  | below
  | above
  deriving DecidableEq, Repr

/-- The level prescribed by Kinnim 1:1. -/
def prescribedLevel : Species → Offering → Level
  | .bird,   .sin   => .below
  | .animal, .sin   => .above
  | .bird,   .burnt => .above
  | .animal, .burnt => .below

/-- A service is valid exactly when it occurs at its prescribed level. -/
def Valid (species : Species) (offering : Offering) (level : Level) : Prop :=
  level = prescribedLevel species offering

/-- The other altar level. -/
def otherLevel : Level → Level
  | .below => .above
  | .above => .below

/-- The four positive rules stated in Kinnim 1:1. -/
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

/-- Reversing the prescribed level always makes the service invalid. -/
theorem changed_level_is_invalid (species : Species) (offering : Offering) :
    ¬ Valid species offering (otherLevel (prescribedLevel species offering)) := by
  cases species <;> cases offering <;> intro h <;> cases h

/-- Changing only the species reverses the prescribed level. -/
theorem changing_species_reverses_level
    (species : Species) (offering : Offering) :
    prescribedLevel
        (match species with | .bird => .animal | .animal => .bird)
        offering =
      otherLevel (prescribedLevel species offering) := by
  cases species <;> cases offering <;> rfl

/-- Changing only the offering designation reverses the prescribed level. -/
theorem changing_offering_reverses_level
    (species : Species) (offering : Offering) :
    prescribedLevel species
        (match offering with | .sin => .burnt | .burnt => .sin) =
      otherLevel (prescribedLevel species offering) := by
  cases species <;> cases offering <;> rfl

/-- Changing both dimensions preserves the prescribed level. -/
theorem changing_both_preserves_level
    (species : Species) (offering : Offering) :
    prescribedLevel
        (match species with | .bird => .animal | .animal => .bird)
        (match offering with | .sin => .burnt | .burnt => .sin) =
      prescribedLevel species offering := by
  cases species <;> cases offering <;> rfl

end Kinnim

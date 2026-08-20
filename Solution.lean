import Kinin.Majority

namespace PalomarKinnim

open Kinnim

theorem physicalApportionmentExactMinimum (pairsByOwner : List Nat) :
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

end PalomarKinnim

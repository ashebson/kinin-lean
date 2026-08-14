import Kinin.Flights

/-!
# Mishnah Kinnim, chapter 2
-/

namespace Kinnim

theorem mishnah_2_1 :
    flightResult .toAir = .takeMate ∧
    flightResult .toDead = .takeMate ∧
    flightResult .birdDied = .takeMate ∧
    flightResult .toOffered = .migrantInvalidatesOne := by
  decide

theorem mishnah_2_2 :
    equalTwoGroupGuarantee 2 0 = [2, 2] ∧
    equalTwoGroupGuarantee 2 1 = [1, 1] ∧
    equalTwoGroupGuarantee 2 4 = [1, 1] := by
  decide

theorem mishnah_2_3 :
    iterateRoundTrips 1 [1, 2, 3, 4, 5, 6, 7] = [0, 0, 1, 2, 3, 4, 6] ∧
    iterateRoundTrips 2 [1, 2, 3, 4, 5, 6, 7] = [0, 0, 0, 0, 1, 2, 5] ∧
    iterateRoundTrips 3 [1, 2, 3, 4, 5, 6, 7] = [0, 0, 0, 0, 0, 0, 4] ∧
    protectLast [0, 0, 0, 0, 0, 0, 5] = [0, 0, 0, 0, 0, 0, 5] := by
  decide

theorem mishnah_2_4 :
    flightResult .closedToSpecified = .takeMate ∧
    flightResult .returnedFromSpecified = .allDie ∧
    flightResult .specifiedFlewFirst = .allDie := by
  decide

theorem mishnah_2_5 :
    validLevel .bird .sin .below = true ∧
    validLevel .bird .burnt .above = true ∧
    flightResult .returnedFromSpecified = .allDie := by
  decide

theorem mishnah_2_6 :
    speciesMatch .turtledove .turtledove = true ∧
    speciesMatch .turtledove .youngDove = false ∧
    majorityCompletionSpecies .youngDove = .youngDove ∧
    benAzzaiCompletionSpecies .turtledove = .turtledove := by
  decide


end Kinnim

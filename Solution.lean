import Kinin.Majority

namespace PalomarKinnim

def sumNats : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNats xs

def subsetSums : List Nat → List Nat
  | [] => [0]
  | x :: xs =>
      let rest := subsetSums xs
      rest ++ rest.map (fun n => n + x)

def greatestAtMost (limit : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs =>
      let tail := greatestAtMost limit xs
      if x ≤ limit then Nat.max x tail else tail

def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

def guaranteedHalfSplitBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

inductive Level where
  | below
  | above
  deriving DecidableEq, Repr

def countLevel (wanted : Level) : List Level → Nat
  | [] => 0
  | level :: levels =>
      (if level = wanted then 1 else 0) + countLevel wanted levels

def ownerLevelsValid (pairs : Nat) (levels : List Level) : Nat :=
  Nat.min (countLevel .below levels) pairs +
    Nat.min (countLevel .above levels) pairs

inductive OwnerBirdAssignment : List Nat → Type where
  | nil : OwnerBirdAssignment []
  | cons {pairs rest} (levels : List Level)
      (birdCount : levels.length = 2 * pairs)
      (tail : OwnerBirdAssignment rest) :
      OwnerBirdAssignment (pairs :: rest)

def OwnerBirdAssignment.levels :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → List Level
  | _, .nil => []
  | _, .cons levels _ tail => levels ++ tail.levels

def OwnerBirdAssignment.aboveBirds :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → Nat
  | _, .nil => 0
  | _, .cons levels _ tail =>
      countLevel .above levels + tail.aboveBirds

def OwnerBirdAssignment.validBirds :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner → Nat
  | _, .nil => 0
  | _, @OwnerBirdAssignment.cons pairs _ levels _ tail =>
      ownerLevelsValid pairs levels + tail.validBirds

structure PhysicalOwnershipWorld (pairsByOwner : List Nat) where
  assignment : OwnerBirdAssignment pairsByOwner
  halfAbove : assignment.aboveBirds = sumNats pairsByOwner

def canonicalHalfSplitLevels (pairs : Nat) : List Level :=
  List.replicate pairs .above ++ List.replicate pairs .below

private theorem sumNats_eq_kinnim (values : List Nat) :
    sumNats values = Kinnim.sumNats values := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp [sumNats, Kinnim.sumNats, ih]

private theorem subsetSums_eq_kinnim (values : List Nat) :
    subsetSums values = Kinnim.subsetSums values := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp [subsetSums, Kinnim.subsetSums, ih]

private theorem greatestAtMost_eq_kinnim (limit : Nat) (values : List Nat) :
    greatestAtMost limit values = Kinnim.greatestAtMost limit values := by
  induction values with
  | nil => rfl
  | cons x xs ih => simp [greatestAtMost, Kinnim.greatestAtMost, ih]

private theorem largestMinority_eq_kinnim (pairsByOwner : List Nat) :
    largestMinority pairsByOwner = Kinnim.largestMinority pairsByOwner := by
  simp only [largestMinority, Kinnim.largestMinority,
    sumNats_eq_kinnim, subsetSums_eq_kinnim, greatestAtMost_eq_kinnim]

private theorem guarantee_eq_kinnim (pairsByOwner : List Nat) :
    guaranteedHalfSplitBirds pairsByOwner =
      Kinnim.guaranteedHalfSplitBirds pairsByOwner := by
  simp only [guaranteedHalfSplitBirds, Kinnim.guaranteedHalfSplitBirds,
    sumNats_eq_kinnim, largestMinority_eq_kinnim]

private def Level.toKinnim : Level → Kinnim.Level
  | .below => .below
  | .above => .above

private def Level.fromKinnim : Kinnim.Level → Level
  | .below => .below
  | .above => .above

@[simp] private theorem Level.fromKinnim_toKinnim (level : Level) :
    Level.fromKinnim level.toKinnim = level := by
  cases level <;> rfl

@[simp] private theorem Level.toKinnim_fromKinnim (level : Kinnim.Level) :
    (Level.fromKinnim level).toKinnim = level := by
  cases level <;> rfl

@[simp] private theorem map_fromKinnim_toKinnim (levels : List Level) :
    (levels.map Level.toKinnim).map Level.fromKinnim = levels := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      cases level <;> simp [Level.toKinnim, Level.fromKinnim, ih]

@[simp] private theorem map_fromKinnim_toKinnim_comp (levels : List Level) :
    levels.map (Level.fromKinnim ∘ Level.toKinnim) = levels := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      simp only [List.map_cons]
      rw [show (Level.fromKinnim ∘ Level.toKinnim) level = level by
        exact Level.fromKinnim_toKinnim level, ih]

private theorem countLevel_toKinnim (wanted : Level) (levels : List Level) :
    Kinnim.countLevel wanted.toKinnim (levels.map Level.toKinnim) =
      countLevel wanted levels := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      cases wanted <;> cases level <;>
        simp [Kinnim.countLevel, countLevel, Level.toKinnim] at ih ⊢
      all_goals exact ih

private theorem countLevel_fromKinnim
    (wanted : Kinnim.Level) (levels : List Kinnim.Level) :
    countLevel (Level.fromKinnim wanted) (levels.map Level.fromKinnim) =
      Kinnim.countLevel wanted levels := by
  induction levels with
  | nil => rfl
  | cons level levels ih =>
      cases wanted <;> cases level <;>
        simp [Kinnim.countLevel, countLevel, Level.fromKinnim] at ih ⊢
      all_goals exact ih

private theorem countBelow_toKinnim (levels : List Level) :
    Kinnim.countLevel .below (levels.map Level.toKinnim) =
      countLevel .below levels := by
  simpa [Level.toKinnim] using countLevel_toKinnim .below levels

private theorem countAbove_toKinnim (levels : List Level) :
    Kinnim.countLevel .above (levels.map Level.toKinnim) =
      countLevel .above levels := by
  simpa [Level.toKinnim] using countLevel_toKinnim .above levels

private theorem countBelow_fromKinnim (levels : List Kinnim.Level) :
    countLevel .below (levels.map Level.fromKinnim) =
      Kinnim.countLevel .below levels := by
  simpa [Level.fromKinnim] using countLevel_fromKinnim .below levels

private theorem countAbove_fromKinnim (levels : List Kinnim.Level) :
    countLevel .above (levels.map Level.fromKinnim) =
      Kinnim.countLevel .above levels := by
  simpa [Level.fromKinnim] using countLevel_fromKinnim .above levels

private theorem ownerLevelsValid_toKinnim (pairs : Nat) (levels : List Level) :
    Kinnim.ownerLevelsValid pairs (levels.map Level.toKinnim) =
      ownerLevelsValid pairs levels := by
  simp only [Kinnim.ownerLevelsValid, ownerLevelsValid]
  rw [countBelow_toKinnim, countAbove_toKinnim]

private theorem ownerLevelsValid_fromKinnim
    (pairs : Nat) (levels : List Kinnim.Level) :
    ownerLevelsValid pairs (levels.map Level.fromKinnim) =
      Kinnim.ownerLevelsValid pairs levels := by
  simp only [ownerLevelsValid, Kinnim.ownerLevelsValid]
  rw [countBelow_fromKinnim, countAbove_fromKinnim]

private def OwnerBirdAssignment.toKinnim :
    {pairsByOwner : List Nat} → OwnerBirdAssignment pairsByOwner →
      Kinnim.OwnerBirdAssignment pairsByOwner
  | _, .nil => .nil
  | _, .cons levels birdCount tail =>
      .cons (levels.map Level.toKinnim) (by simpa using birdCount)
        tail.toKinnim

private theorem OwnerBirdAssignment.toKinnim_levels
    {pairsByOwner : List Nat} (assignment : OwnerBirdAssignment pairsByOwner) :
    assignment.toKinnim.levels = assignment.levels.map Level.toKinnim := by
  induction assignment with
  | nil => rfl
  | cons levels birdCount tail ih =>
      simp [OwnerBirdAssignment.toKinnim,
        Kinnim.OwnerBirdAssignment.levels, OwnerBirdAssignment.levels,
        List.map_append, ih]

private theorem OwnerBirdAssignment.toKinnim_aboveBirds
    {pairsByOwner : List Nat} (assignment : OwnerBirdAssignment pairsByOwner) :
    assignment.toKinnim.aboveBirds = assignment.aboveBirds := by
  induction assignment with
  | nil => rfl
  | cons levels birdCount tail ih =>
      simp [OwnerBirdAssignment.toKinnim,
        Kinnim.OwnerBirdAssignment.aboveBirds,
        OwnerBirdAssignment.aboveBirds, countAbove_toKinnim, ih]

private theorem OwnerBirdAssignment.toKinnim_validBirds
    {pairsByOwner : List Nat} (assignment : OwnerBirdAssignment pairsByOwner) :
    assignment.toKinnim.validBirds = assignment.validBirds := by
  induction assignment with
  | nil => rfl
  | @cons pairs rest levels birdCount tail ih =>
      simp [OwnerBirdAssignment.toKinnim,
        Kinnim.OwnerBirdAssignment.validBirds,
        OwnerBirdAssignment.validBirds, ownerLevelsValid_toKinnim, ih]

private def OwnerBirdAssignment.fromKinnim :
    {pairsByOwner : List Nat} → Kinnim.OwnerBirdAssignment pairsByOwner →
      OwnerBirdAssignment pairsByOwner
  | _, .nil => .nil
  | _, .cons levels birdCount tail =>
      .cons (levels.map Level.fromKinnim) (by simpa using birdCount)
        (OwnerBirdAssignment.fromKinnim tail)

private theorem OwnerBirdAssignment.fromKinnim_levels
    {pairsByOwner : List Nat}
    (assignment : Kinnim.OwnerBirdAssignment pairsByOwner) :
    (OwnerBirdAssignment.fromKinnim assignment).levels =
      assignment.levels.map Level.fromKinnim := by
  induction assignment with
  | nil => rfl
  | cons levels birdCount tail ih =>
      simp [OwnerBirdAssignment.fromKinnim,
        OwnerBirdAssignment.levels, Kinnim.OwnerBirdAssignment.levels,
        List.map_append, ih]

private theorem OwnerBirdAssignment.fromKinnim_aboveBirds
    {pairsByOwner : List Nat}
    (assignment : Kinnim.OwnerBirdAssignment pairsByOwner) :
    (OwnerBirdAssignment.fromKinnim assignment).aboveBirds =
      assignment.aboveBirds := by
  induction assignment with
  | nil => rfl
  | cons levels birdCount tail ih =>
      simp [OwnerBirdAssignment.fromKinnim,
        OwnerBirdAssignment.aboveBirds,
        Kinnim.OwnerBirdAssignment.aboveBirds,
        countAbove_fromKinnim, ih]

private theorem OwnerBirdAssignment.fromKinnim_validBirds
    {pairsByOwner : List Nat}
    (assignment : Kinnim.OwnerBirdAssignment pairsByOwner) :
    (OwnerBirdAssignment.fromKinnim assignment).validBirds =
      assignment.validBirds := by
  induction assignment with
  | nil => rfl
  | @cons pairs rest levels birdCount tail ih =>
      simp [OwnerBirdAssignment.fromKinnim,
        OwnerBirdAssignment.validBirds,
        Kinnim.OwnerBirdAssignment.validBirds,
        ownerLevelsValid_fromKinnim, ih]

private def PhysicalOwnershipWorld.toKinnim
    {pairsByOwner : List Nat} (world : PhysicalOwnershipWorld pairsByOwner) :
    Kinnim.PhysicalOwnershipWorld pairsByOwner where
  assignment := world.assignment.toKinnim
  halfAbove := by
    rw [world.assignment.toKinnim_aboveBirds, world.halfAbove,
      sumNats_eq_kinnim]

private theorem PhysicalOwnershipWorld.compatibleWithCanonicalPlan
    {pairsByOwner : List Nat} (world : PhysicalOwnershipWorld pairsByOwner) :
    world.assignment.levels.Perm
      (canonicalHalfSplitLevels (sumNats pairsByOwner)) := by
  have compatible := world.toKinnim.compatibleWithCanonicalPlan
  rw [Kinnim.actionLevels_canonicalHalfSplitActions] at compatible
  change world.assignment.toKinnim.levels.Perm
    (Kinnim.canonicalHalfSplitLevels (Kinnim.sumNats pairsByOwner)) at compatible
  rw [world.assignment.toKinnim_levels] at compatible
  have mapped := compatible.map Level.fromKinnim
  simpa [canonicalHalfSplitLevels, Kinnim.canonicalHalfSplitLevels,
    sumNats_eq_kinnim,
    Level.fromKinnim, Level.toKinnim] using mapped

theorem physicalApportionmentExactMinimum (pairsByOwner : List Nat) :
    (∀ world : PhysicalOwnershipWorld pairsByOwner,
      world.assignment.levels.Perm
          (canonicalHalfSplitLevels (sumNats pairsByOwner)) ∧
      guaranteedHalfSplitBirds pairsByOwner ≤ world.assignment.validBirds) ∧
    (∃ worst : PhysicalOwnershipWorld pairsByOwner,
      worst.assignment.levels.Perm
          (canonicalHalfSplitLevels (sumNats pairsByOwner)) ∧
      worst.assignment.validBirds = guaranteedHalfSplitBirds pairsByOwner) := by
  constructor
  · intro world
    refine ⟨world.compatibleWithCanonicalPlan, ?_⟩
    have lower :=
      Kinnim.physicalMajorityPayoff_lower_bound pairsByOwner world.toKinnim
    simpa [PhysicalOwnershipWorld.toKinnim,
      Kinnim.physicalMajorityPayoff, guarantee_eq_kinnim,
      world.assignment.toKinnim_validBirds] using lower
  · obtain ⟨hiddenWorst, exactWorst⟩ :=
      Kinnim.exists_worstPhysicalOwnershipWorld pairsByOwner
    let assignment := OwnerBirdAssignment.fromKinnim hiddenWorst.assignment
    have halfAbove : assignment.aboveBirds = sumNats pairsByOwner := by
      dsimp only [assignment]
      rw [OwnerBirdAssignment.fromKinnim_aboveBirds,
        hiddenWorst.halfAbove]
      exact (sumNats_eq_kinnim pairsByOwner).symm
    let worst : PhysicalOwnershipWorld pairsByOwner :=
      { assignment := assignment, halfAbove := halfAbove }
    refine ⟨worst, worst.compatibleWithCanonicalPlan, ?_⟩
    have exactAssignment :
        hiddenWorst.assignment.validBirds =
          Kinnim.guaranteedHalfSplitBirds pairsByOwner := by
      simpa [Kinnim.physicalMajorityPayoff] using exactWorst
    dsimp only [worst, assignment]
    rw [OwnerBirdAssignment.fromKinnim_validBirds, exactAssignment]
    exact (guarantee_eq_kinnim pairsByOwner).symm

end PalomarKinnim

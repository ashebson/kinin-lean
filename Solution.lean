import Lean.Elab.Tactic.Omega

/-! # Proved solution: operational Kinnim 3:2 maximin theorem -/

namespace PalomarKinnim

inductive Level where
  | below
  | above
  deriving DecidableEq, BEq, Repr

inductive PairService where
  | bothBelow
  | split
  | bothAbove
  deriving DecidableEq, BEq, Repr

def PairService.aboveBirds : PairService → Nat
  | .bothBelow => 0
  | .split => 1
  | .bothAbove => 2

def PairService.validBirds : PairService → Nat
  | .bothBelow => 1
  | .split => 2
  | .bothAbove => 1

def sumNats : List Nat → Nat
  | [] => 0
  | n :: ns => n + sumNats ns

def subsetSums : List Nat → List Nat
  | [] => [0]
  | n :: ns =>
      let rest := subsetSums ns
      rest ++ rest.map (fun total => total + n)

def greatestAtMost (limit : Nat) : List Nat → Nat
  | [] => 0
  | n :: ns =>
      let tail := greatestAtMost limit ns
      if n ≤ limit then Nat.max n tail else tail

def largestMinority (pairsByOwner : List Nat) : Nat :=
  greatestAtMost (sumNats pairsByOwner / 2) (subsetSums pairsByOwner)

def guaranteedValidBirds (pairsByOwner : List Nat) : Nat :=
  2 * (sumNats pairsByOwner - largestMinority pairsByOwner)

structure MajorityWorld (pairsByOwner : List Nat) where
  minorityPairs : Nat
  wholeOwnerCut : minorityPairs ∈ subsetSums pairsByOwner
  atMostHalf : minorityPairs ≤ sumNats pairsByOwner / 2

def canonicalHalfSplitPlan (pairsByOwner : List Nat) : List Level :=
  List.replicate (sumNats pairsByOwner) .above ++
    List.replicate (sumNats pairsByOwner) .below

def countAbove : List Level → Nat
  | [] => 0
  | level :: levels =>
      (if level == .above then 1 else 0) + countAbove levels

def PlanLegal (pairsByOwner : List Nat) (plan : List Level) : Prop :=
  plan = canonicalHalfSplitPlan pairsByOwner ∧
  plan.length = 2 * sumNats pairsByOwner ∧
  countAbove plan = sumNats pairsByOwner

def operationalServices (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) : List PairService :=
  List.replicate world.minorityPairs .bothBelow ++
  List.replicate
      (sumNats pairsByOwner - 2 * world.minorityPairs) .split ++
  List.replicate world.minorityPairs .bothAbove

def serviceAboveBirds : List PairService → Nat
  | [] => 0
  | service :: services => service.aboveBirds + serviceAboveBirds services

def serviceValidBirds : List PairService → Nat
  | [] => 0
  | service :: services => service.validBirds + serviceValidBirds services

def operationalPayoff (pairsByOwner : List Nat)
    (world : MajorityWorld pairsByOwner) (plan : List Level) : Nat :=
  if plan = canonicalHalfSplitPlan pairsByOwner then
    serviceValidBirds (operationalServices pairsByOwner world)
  else 0

def Guarantees (pairsByOwner : List Nat) (plan : List Level) (count : Nat) : Prop :=
  PlanLegal pairsByOwner plan ∧
    ∀ world : MajorityWorld pairsByOwner,
      count ≤ operationalPayoff pairsByOwner world plan

def HasOptimalGuarantee (pairsByOwner : List Nat) (count : Nat) : Prop :=
  (∃ plan, Guarantees pairsByOwner plan count) ∧
  (∀ plan, PlanLegal pairsByOwner plan →
    ∃ world : MajorityWorld pairsByOwner,
      operationalPayoff pairsByOwner world plan ≤ count)

private theorem greatestAtMost_le (limit : Nat) (values : List Nat) :
    greatestAtMost limit values ≤ limit := by
  induction values with
  | nil => simp [greatestAtMost]
  | cons value values ih =>
      by_cases bounded : value ≤ limit
      · simp [greatestAtMost, bounded, Nat.max_le, ih]
      · simpa [greatestAtMost, bounded] using ih

private theorem le_greatestAtMost_of_mem
    {limit value : Nat} {values : List Nat}
    (member : value ∈ values) (bounded : value ≤ limit) :
    value ≤ greatestAtMost limit values := by
  induction values with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      by_cases headBounded : head ≤ limit
      · simp only [greatestAtMost, headBounded, if_pos]
        cases member with
        | inl equal =>
            subst head
            exact Nat.le_max_left _ _
        | inr tailMember =>
            exact Nat.le_trans (ih tailMember) (Nat.le_max_right _ _)
      · simp only [greatestAtMost, headBounded]
        cases member with
        | inl equal =>
            subst head
            exact False.elim (headBounded bounded)
        | inr tailMember => exact ih tailMember

private theorem greatestAtMost_eq_zero_or_mem (limit : Nat) (values : List Nat) :
    greatestAtMost limit values = 0 ∨
      greatestAtMost limit values ∈ values := by
  induction values with
  | nil => simp [greatestAtMost]
  | cons value values ih =>
      by_cases bounded : value ≤ limit
      · simp only [greatestAtMost, bounded, if_pos]
        rcases ih with zero | member
        · rw [zero]
          simp
        · by_cases tailLe : greatestAtMost limit values ≤ value
          · right
            rw [show value.max (greatestAtMost limit values) = value from
              Nat.max_eq_left tailLe]
            exact List.mem_cons_self
          · right
            rw [show value.max (greatestAtMost limit values) =
                greatestAtMost limit values from
              Nat.max_eq_right (Nat.le_of_not_ge tailLe)]
            exact List.mem_cons_of_mem value member
      · simp only [greatestAtMost, bounded]
        rcases ih with zero | member
        · exact Or.inl zero
        · exact Or.inr (List.mem_cons_of_mem value member)

private theorem zero_mem_subsetSums (values : List Nat) :
    0 ∈ subsetSums values := by
  induction values with
  | nil => simp [subsetSums]
  | cons value values ih =>
      simp only [subsetSums, List.mem_append]
      exact Or.inl ih

private theorem largestMinority_mem (pairsByOwner : List Nat) :
    largestMinority pairsByOwner ∈ subsetSums pairsByOwner := by
  rcases greatestAtMost_eq_zero_or_mem
      (sumNats pairsByOwner / 2) (subsetSums pairsByOwner) with zero | member
  · simp only [largestMinority]
    rw [zero]
    exact zero_mem_subsetSums pairsByOwner
  · exact member

private theorem largestMinority_le_half (pairsByOwner : List Nat) :
    largestMinority pairsByOwner ≤ sumNats pairsByOwner / 2 := by
  exact greatestAtMost_le _ _

private theorem minority_le_largest
    {pairsByOwner : List Nat} (world : MajorityWorld pairsByOwner) :
    world.minorityPairs ≤ largestMinority pairsByOwner := by
  exact le_greatestAtMost_of_mem world.wholeOwnerCut world.atMostHalf

private theorem countAbove_append (first second : List Level) :
    countAbove (first ++ second) = countAbove first + countAbove second := by
  induction first with
  | nil => simp [countAbove]
  | cons level levels ih => simp [countAbove, ih, Nat.add_assoc]

private theorem countAbove_replicate_above (n : Nat) :
    countAbove (List.replicate n .above) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 1 + countAbove (List.replicate n .above) = n + 1
      rw [ih]
      omega

private theorem countAbove_replicate_below (n : Nat) :
    countAbove (List.replicate n .below) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 0 + countAbove (List.replicate n .below) = 0
      simpa using ih

private theorem canonicalPlan_legal (pairsByOwner : List Nat) :
    PlanLegal pairsByOwner (canonicalHalfSplitPlan pairsByOwner) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [canonicalHalfSplitPlan]
    omega
  · simp [canonicalHalfSplitPlan, countAbove_append,
      countAbove_replicate_above, countAbove_replicate_below]

private theorem serviceAbove_append (first second : List PairService) :
    serviceAboveBirds (first ++ second) =
      serviceAboveBirds first + serviceAboveBirds second := by
  induction first with
  | nil => simp [serviceAboveBirds]
  | cons service services ih =>
      simp [serviceAboveBirds, ih, Nat.add_assoc]

private theorem serviceValid_append (first second : List PairService) :
    serviceValidBirds (first ++ second) =
      serviceValidBirds first + serviceValidBirds second := by
  induction first with
  | nil => simp [serviceValidBirds]
  | cons service services ih =>
      simp [serviceValidBirds, ih, Nat.add_assoc]

private theorem serviceAbove_replicate (n : Nat) (service : PairService) :
    serviceAboveBirds (List.replicate n service) = n * service.aboveBirds := by
  induction n with
  | zero => simp [serviceAboveBirds]
  | succ n ih =>
      simp [List.replicate_succ, serviceAboveBirds, ih, Nat.succ_mul]
      omega

private theorem serviceValid_replicate (n : Nat) (service : PairService) :
    serviceValidBirds (List.replicate n service) = n * service.validBirds := by
  induction n with
  | zero => simp [serviceValidBirds]
  | succ n ih =>
      simp [List.replicate_succ, serviceValidBirds, ih, Nat.succ_mul]
      omega

private theorem twice_minority_le_total
    {pairsByOwner : List Nat} (world : MajorityWorld pairsByOwner) :
    2 * world.minorityPairs ≤ sumNats pairsByOwner := by
  have multiplied :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 world.atMostHalf
  simpa [Nat.mul_comm] using multiplied

private theorem operational_realization
    (pairsByOwner : List Nat) (world : MajorityWorld pairsByOwner) :
    (operationalServices pairsByOwner world).length =
        sumNats pairsByOwner ∧
    serviceAboveBirds (operationalServices pairsByOwner world) =
        sumNats pairsByOwner ∧
    operationalPayoff pairsByOwner world
        (canonicalHalfSplitPlan pairsByOwner) =
      2 * (sumNats pairsByOwner - world.minorityPairs) := by
  have bounded := twice_minority_le_total world
  constructor
  · simp only [operationalServices, List.length_append, List.length_replicate]
    omega
  constructor
  · simp only [operationalServices, serviceAbove_append,
      serviceAbove_replicate, PairService.aboveBirds]
    omega
  · simp only [operationalPayoff, if_true,
      operationalServices, serviceValid_append, serviceValid_replicate,
      PairService.validBirds]
    omega

private def largestMinorityWorld (pairsByOwner : List Nat) :
    MajorityWorld pairsByOwner where
  minorityPairs := largestMinority pairsByOwner
  wholeOwnerCut := largestMinority_mem pairsByOwner
  atMostHalf := largestMinority_le_half pairsByOwner

private theorem canonical_guarantees (pairsByOwner : List Nat) :
    Guarantees pairsByOwner (canonicalHalfSplitPlan pairsByOwner)
      (guaranteedValidBirds pairsByOwner) := by
  constructor
  · exact canonicalPlan_legal pairsByOwner
  · intro world
    rw [(operational_realization pairsByOwner world).2.2]
    have maximal := minority_le_largest world
    simp only [guaranteedValidBirds]
    omega

private theorem exact_optimal_guarantee (pairsByOwner : List Nat) :
    HasOptimalGuarantee pairsByOwner (guaranteedValidBirds pairsByOwner) := by
  constructor
  · exact ⟨canonicalHalfSplitPlan pairsByOwner,
      canonical_guarantees pairsByOwner⟩
  · intro plan legal
    let world := largestMinorityWorld pairsByOwner
    refine ⟨world, ?_⟩
    rw [legal.1]
    rw [(operational_realization pairsByOwner world).2.2]
    simp [world, guaranteedValidBirds, largestMinorityWorld]

theorem operationalKinnim32 (pairsByOwner : List Nat) :
    PlanLegal pairsByOwner (canonicalHalfSplitPlan pairsByOwner) ∧
    (∀ world : MajorityWorld pairsByOwner,
      (operationalServices pairsByOwner world).length =
          sumNats pairsByOwner ∧
      serviceAboveBirds (operationalServices pairsByOwner world) =
          sumNats pairsByOwner ∧
      operationalPayoff pairsByOwner world
          (canonicalHalfSplitPlan pairsByOwner) =
        2 * (sumNats pairsByOwner - world.minorityPairs)) ∧
    HasOptimalGuarantee pairsByOwner (guaranteedValidBirds pairsByOwner) := by
  exact ⟨canonicalPlan_legal pairsByOwner,
    operational_realization pairsByOwner,
    exact_optimal_guarantee pairsByOwner⟩

end PalomarKinnim

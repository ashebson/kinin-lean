import Lean.Elab.Tactic.Omega

/-!
# Proved solution for the Kinnim 3:2 challenge
-/

namespace PalomarKinnim

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

def AdmissibleCut (pairsByOwner : List Nat) (minorityPairs : Nat) : Prop :=
  minorityPairs ∈ subsetSums pairsByOwner ∧
    minorityPairs ≤ sumNats pairsByOwner / 2

def cutPayoff (pairsByOwner : List Nat) (minorityPairs : Nat) : Nat :=
  2 * (sumNats pairsByOwner - minorityPairs)

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

theorem exactCutGuarantee (pairsByOwner : List Nat) :
    (∀ minorityPairs, AdmissibleCut pairsByOwner minorityPairs →
      guaranteedValidBirds pairsByOwner ≤
        cutPayoff pairsByOwner minorityPairs) ∧
    ∃ minorityPairs, AdmissibleCut pairsByOwner minorityPairs ∧
      cutPayoff pairsByOwner minorityPairs =
        guaranteedValidBirds pairsByOwner := by
  constructor
  · intro minorityPairs admissible
    have minorityLe :
        minorityPairs ≤ largestMinority pairsByOwner :=
      le_greatestAtMost_of_mem admissible.1 admissible.2
    simp only [guaranteedValidBirds, cutPayoff]
    omega
  · refine ⟨largestMinority pairsByOwner, ?_, rfl⟩
    exact ⟨largestMinority_mem pairsByOwner,
      greatestAtMost_le _ _⟩

end PalomarKinnim

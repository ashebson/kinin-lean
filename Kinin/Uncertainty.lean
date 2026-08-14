import Kinin.Core

/-!
# Semantic guarantees under uncertainty

This module separates a claimed numerical answer from the two obligations
needed to justify it:

* a legal priestly strategy that attains the number in every admissible world;
* an admissible counter-world for every legal strategy, showing that no larger
  number can be guaranteed.

The definitions are intentionally propositional rather than executable.  A
finite problem may still use the algorithms in `Kinin.Core` to construct the
certificates.
-/

namespace Kinnim

structure UncertaintyProblem (World Action : Type) where
  admissible : World → Prop
  legal : Action → Prop
  payoff : World → Action → Nat

namespace UncertaintyProblem

def Guarantees (p : UncertaintyProblem World Action)
    (action : Action) (count : Nat) : Prop :=
  p.legal action ∧
    ∀ world, p.admissible world → count ≤ p.payoff world action

/-- `count` is the exact maximin value: one strategy guarantees it, while an
admissible world defeats every attempt to guarantee anything larger. -/
def HasOptimalGuarantee (p : UncertaintyProblem World Action)
    (count : Nat) : Prop :=
  (∃ action, p.Guarantees action count) ∧
    (∀ action, p.legal action →
      ∃ world, p.admissible world ∧ p.payoff world action ≤ count)

theorem no_strategy_guarantees_more
    {p : UncertaintyProblem World Action} {count larger : Nat}
    (optimal : p.HasOptimalGuarantee count) (h : count < larger) :
    ¬ ∃ action, p.Guarantees action larger := by
  rintro ⟨action, legal, guarantee⟩
  obtain ⟨world, admissible, upper⟩ := optimal.2 action legal
  exact (Nat.not_le_of_lt h) (Nat.le_trans (guarantee world admissible) upper)

theorem optimal_guarantee_unique
    {p : UncertaintyProblem World Action} {a b : Nat}
    (ha : p.HasOptimalGuarantee a) (hb : p.HasOptimalGuarantee b) : a = b := by
  apply Nat.le_antisymm
  · obtain ⟨action, legal, guarantee⟩ := ha.1
    obtain ⟨world, admissible, upper⟩ := hb.2 action legal
    exact Nat.le_trans (guarantee world admissible) upper
  · obtain ⟨action, legal, guarantee⟩ := hb.1
    obtain ⟨world, admissible, upper⟩ := ha.2 action legal
    exact Nat.le_trans (guarantee world admissible) upper

end UncertaintyProblem

end Kinnim

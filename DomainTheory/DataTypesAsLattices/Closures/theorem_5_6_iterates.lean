/-ai
The Kleene iterates of the identity combinator under an operator that sends closures to closures are themselves closures, and the identity combinator is contained in the least fixed point of the operator above the identity.

The iterates are closures by induction on the stage: the zeroth iterate is the identity combinator, which is a closure, and a successor iterate is the operator applied to a closure. The zeroth iterate is one term of the union that defines the least fixed point above the identity, so the identity is contained in that union.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_isClosure

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- Kleene iterates of `I` under a closure-preserving operator stay closures. -/
theorem theorem_5_6_iterates {F : Pomega → Pomega}
    (_hF : IsScottContinuous F)
    (hcl : ∀ a, Closure a → Closure (F a)) :
    (∀ n, Closure (iterateFrom F Icomb n)) ∧
      Icomb ⊆ lfpAbove F Icomb := by
  have hiter : ∀ n, Closure (iterateFrom F Icomb n) := by
    intro n
    induction n with
    | zero => exact Icomb_isClosure
    | succ n ih => exact hcl _ ih
  exact ⟨hiter, Set.subset_iUnion (iterateFrom F Icomb) 0⟩

end DomainTheory.DataTypesAsLattices

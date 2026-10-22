/-ai
Scott's definition in §5 says that an element a of Pω is a closure operation when the identity combinator is contained in a and a is a retract, that is, when the identity is contained in a and a equals a composed with itself.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §5, Definition.** `a` is a closure operation iff `I ⊆ a = a ∘ a`. -/
def IsClosure (a : Pomega) : Prop :=
  Icomb ⊆ a ∧ IsRetract a

end DomainTheory.DataTypesAsLattices

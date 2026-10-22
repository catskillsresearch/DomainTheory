
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §5, Definition.** `a` is a closure operation iff `I ⊆ a = a ∘ a`. -/
class Closure (a : Pomega) : Prop where
  out : Icomb ⊆ a ∧ Retract a

end DomainTheory.DataTypesAsLattices

module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §4, Definition.** `a` is a retract iff `a = a ∘ a`. -/
class Retract (a : Pomega) : Prop where
  out : a = comp a a

end DomainTheory.DataTypesAsLattices

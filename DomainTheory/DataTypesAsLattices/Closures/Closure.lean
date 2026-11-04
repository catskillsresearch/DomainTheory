module

public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

class Closure (a : Pomega) : Prop where
  out : Icomb ⊆ a ∧ Retract a

end DomainTheory.DataTypesAsLattices

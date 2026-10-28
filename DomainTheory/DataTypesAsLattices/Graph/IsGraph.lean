
module

public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

class IsGraph (u : Pomega) : Prop where
  out : ∀ ⦃k m n⦄, pair k m ∈ u → e k ⊆ e n → pair n m ∈ u

end DomainTheory.DataTypesAsLattices

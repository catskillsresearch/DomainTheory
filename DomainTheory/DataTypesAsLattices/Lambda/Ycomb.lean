/-ai
Scott's equation (2.8) defines the combinator Y to be the graph of the map sending u to the application of omega(u) to itself.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.omegaComb

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.8).** `Y = λ u. ω(u)(ω(u))`. -/
def Ycomb : Pomega :=
  graph (fun u => funOf (omegaComb u) (omegaComb u))

end DomainTheory.DataTypesAsLattices

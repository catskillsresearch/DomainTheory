module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embR

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- `1P ∪ 2Q`: the product-style neighbourhood of `D^§`. -/
def embPair (P Q : Set (List Bool × α)) : Set (List Bool × α) := embL P ∪ embR Q

end Example61
end DomainTheory.NeighbourhoodSystems

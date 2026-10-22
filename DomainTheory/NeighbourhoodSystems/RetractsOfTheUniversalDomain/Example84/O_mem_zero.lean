module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem O_mem_zero : O.mem ({0} : Set (Fin 2)) := Or.inl rfl

end DomainTheory.NeighbourhoodSystems

/-ai
The master of the two-point system is the full two-point set.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

theorem O_master_eq : O.master = ({0, 1} : Set (Fin 2)) := rfl

end DomainTheory.NeighbourhoodSystems

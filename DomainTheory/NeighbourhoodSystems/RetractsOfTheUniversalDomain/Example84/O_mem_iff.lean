module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

@[simp] theorem O_mem_iff {X : Set (Fin 2)} :
    O.mem X ↔ X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2)) := Iff.rfl

end DomainTheory.NeighbourhoodSystems

/-ai
A set of the two tokens is a neighbourhood of the two-point system if and only if it is the singleton of zero or the full two-point set.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

@[simp] theorem O_mem_iff {X : Set (Fin 2)} :
    O.mem X ↔ X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2)) := Iff.rfl

end DomainTheory.NeighbourhoodSystems

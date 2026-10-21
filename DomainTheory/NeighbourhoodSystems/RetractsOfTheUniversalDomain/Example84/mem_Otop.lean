/-ai
A set Y belongs to Otop if and only if Y is an O-neighbourhood and {0} is contained in Y.

This is the defining membership condition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Otop

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

@[simp] theorem mem_Otop {Y : Set (Fin 2)} : Otop.mem Y ↔ O.mem Y ∧ ({0} : Set (Fin 2)) ⊆ Y :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems

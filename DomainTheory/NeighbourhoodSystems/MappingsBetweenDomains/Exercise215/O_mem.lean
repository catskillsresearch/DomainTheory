/-ai
A set of a one-element type is a neighbourhood of O if and only if it satisfies memO.

The two sides are definitionally the same proposition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.memO
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise215.O

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem O_mem {X : Set (Fin 1)} : O.mem X ↔ memO X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise215

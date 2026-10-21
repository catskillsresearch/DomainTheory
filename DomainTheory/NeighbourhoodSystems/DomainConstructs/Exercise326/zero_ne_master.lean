/-ai
The singleton of zero in the truth domain is distinct from the master neighbourhood.

Extensionality at the token one, simplified in the two sets, is contradictory.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

theorem zero_ne_master : (Example12.zero : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h1 := Set.ext_iff.mp h 1
  simp [Example12.zero, Example12.master] at h1

end DomainTheory.NeighbourhoodSystems.Exercise326

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

theorem one_ne_master : (Example12.one : Set Example12.Token) ≠ Example12.master := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.one, Example12.master] at h0

end DomainTheory.NeighbourhoodSystems.Exercise326

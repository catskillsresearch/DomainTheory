module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

theorem zero_ne_one : (Example12.zero : Set Example12.Token) ≠ Example12.one := by
  intro h
  have h0 := Set.ext_iff.mp h 0
  simp [Example12.zero, Example12.one] at h0

end DomainTheory.NeighbourhoodSystems.Exercise326

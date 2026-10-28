module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

theorem Subsystem.trianglelefteq {D E : NeighborhoodSystem α} (h : D ◁ E) : D ⊴ E :=
  ⟨D, h, Isomorphic.refl D⟩

end
end DomainTheory.NeighbourhoodSystems
end

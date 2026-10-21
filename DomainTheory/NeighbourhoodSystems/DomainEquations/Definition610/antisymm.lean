/-ai
The subsystem relation is antisymmetric: if each of two neighbourhood systems is a subsystem of the other, then the systems are equal.

Extensionality of neighbourhood systems applies. Each inclusion clause gives one direction of the agreement of membership, and the master-equality clause of the first hypothesis gives the equality of the masters.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610._root_u2eDomainTheoryu2eNeighborhoodu2eNeighborhoodSystemu2eext

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}


namespace Subsystem

/-- The subsystem relation is **antisymmetric**: `D ◁ E` and `E ◁ D` force `D = E`. (Mutual `sub`
gives equal `mem`, and `master_eq` gives equal masters.) -/
theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

end Subsystem
end DomainTheory.NeighbourhoodSystems

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610.Basic.notation2

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

variable {α : Type*}


namespace Subsystem

/-- The subsystem relation is **reflexive**: `D ◁ D`. (The `inter_closed` clause is trivial — the
hypothesis is already the conclusion.) -/
theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

end Subsystem
end DomainTheory.NeighbourhoodSystems

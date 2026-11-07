module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.subsystemLattice

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem SubsystemLattice Exercise222

variable {α : Type*}

/-- Scott's Proposition 6.11: subsystems of `E` form a domain. -/
theorem proposition_611 (E : NeighborhoodSystem α) :
    Nonempty ({D : NeighborhoodSystem α // D ◁ E} ≃o
      (reprSystem (subFam E) (subFam_sInter_mem E) (subFam_nonempty E)).Element) :=
  ⟨subsystemReprIso E⟩

end DomainTheory.NeighbourhoodSystems

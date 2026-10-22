module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.unionSys_nbset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- **Closure under directed union** (Exercise 2.22's hypothesis (ii)) — Scott's remark. -/
theorem subFam_sUnion_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    ⋃₀ ℱ ∈ subFam E :=
  ⟨unionSys E ℱ hne hℱ hdir, unionSys_subsystem E ℱ hne hℱ hdir,
    (unionSys_nbset E ℱ hne hℱ hdir).symm⟩

end DomainTheory.NeighbourhoodSystems.Proposition611

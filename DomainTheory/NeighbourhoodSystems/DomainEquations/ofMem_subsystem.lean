/-ai
The neighbourhood system rebuilt from a subdomain neighbourhood-set is a subsystem of E.

The masters agree. Every member of the set is a neighbourhood of E, and the set is closed under intersections that lie in E.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_mem_E
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam_inter_closed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611Inst16
public import DomainTheory.NeighbourhoodSystems.DomainEquations.ofMem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- `ofMem` lands in the subsystems of `E`. -/
theorem ofMem_subsystem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    ofMem E 𝒮 h ◁ E where
  master_eq := rfl
  sub := subFam_mem_E E h
  inter_closed := subFam_inter_closed E h

end DomainTheory.NeighbourhoodSystems.Proposition611

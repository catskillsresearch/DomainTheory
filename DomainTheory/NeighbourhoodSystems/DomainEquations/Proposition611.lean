module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.ofMem_subsystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}


end DomainTheory.NeighbourhoodSystems.Proposition611

namespace DomainTheory.NeighbourhoodSystems.Proposition611

set_option linter.unusedVariables false

theorem theorem_611.{u_1} : ∀ {α : Type u_1} (E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (𝒮 : Set (Set α))
  (h :
    @Membership.mem (Set (Set α)) (Set (Set (Set α))) (@Set.instMembership (Set (Set α)))
      (@DomainTheory.NeighbourhoodSystems.Proposition611.subFam α E) 𝒮),
  @DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.Proposition611.ofMem α E 𝒮 h) E :=
  @DomainTheory.NeighbourhoodSystems.Proposition611.ofMem_subsystem

end DomainTheory.NeighbourhoodSystems.Proposition611

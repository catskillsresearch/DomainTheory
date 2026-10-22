module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.openOfMap_isOpen

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise325

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set


variable {α : Type*} (V : NeighborhoodSystem α)


end DomainTheory.NeighbourhoodSystems.Exercise325

namespace DomainTheory.NeighbourhoodSystems.Exercise325

set_option linter.unusedVariables false

theorem example_325.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V
      DomainTheory.NeighbourhoodSystems.Exercise325.sierpinski),
  @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
    (@DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap α V f) :=
  @DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap_isOpen

end DomainTheory.NeighbourhoodSystems.Exercise325

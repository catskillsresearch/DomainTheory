module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.opensDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise325

section
set_option linter.unusedVariables false

theorem example_325.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α Unit V
      DomainTheory.NeighbourhoodSystems.Exercise325.sierpinski),
  @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
    (@DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap α V f) :=
  @DomainTheory.NeighbourhoodSystems.Exercise325.openOfMap_isOpen
end

end DomainTheory.NeighbourhoodSystems.Exercise325
end

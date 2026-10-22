module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.bracket_spec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise508

set_option linter.unusedVariables false

theorem example_508 : ∀ {X A : DomainTheory.NeighbourhoodSystems.Exercise508.Dom} (t : DomainTheory.NeighbourhoodSystems.Exercise508.Poly X A)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element X.carrier X.sys),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element A.carrier A.sys)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap X.carrier A.carrier X.sys A.sys
      (@DomainTheory.NeighbourhoodSystems.toApproxMap X.carrier A.carrier X.sys A.sys
        (@DomainTheory.NeighbourhoodSystems.Exercise508.CL.denote (X.arrow A)
          (@DomainTheory.NeighbourhoodSystems.Exercise508.bracket X A t)))
      x)
    (@DomainTheory.NeighbourhoodSystems.Exercise508.Poly.denote X A t x) :=
  @DomainTheory.NeighbourhoodSystems.Exercise508.bracket_spec

end DomainTheory.NeighbourhoodSystems.Exercise508

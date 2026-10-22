module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826.translateAbs_idMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_826.{u} : ∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
    (@DomainTheory.NeighbourhoodSystems.translateAbs α E a b
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E E E b a) :=
  @DomainTheory.NeighbourhoodSystems.translateAbs_idMap

end DomainTheory.NeighbourhoodSystems

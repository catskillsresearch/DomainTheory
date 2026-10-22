module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.descAlgHom_uniq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Example62C

open Example44 ExampleB Example62

end Example62C

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_617 : ∀
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc)
  (h' :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.StrictDomainObj
      DomainTheory.NeighbourhoodSystems.instCategoryStrictDomainObj DomainTheory.NeighbourhoodSystems.Tc
      DomainTheory.NeighbourhoodSystems.Calg B)
    h' (DomainTheory.NeighbourhoodSystems.descAlgHom B) :=
  DomainTheory.NeighbourhoodSystems.descAlgHom_uniq

end DomainTheory.NeighbourhoodSystems

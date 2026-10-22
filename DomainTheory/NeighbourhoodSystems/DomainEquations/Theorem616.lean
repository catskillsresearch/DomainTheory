module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem616.trianglelefteq_of_isInitial

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_616.{w} : ∀
  (T :
    @DomainTheory.NeighbourhoodSystems.Endofunctor.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}),
  DomainTheory.NeighbourhoodSystems.ContinuousOnMaps.{w} T →
    ∀
      (Dalg :
        @DomainTheory.NeighbourhoodSystems.TAlgebra.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T)
      (hinit :
        @DomainTheory.NeighbourhoodSystems.IsInitial.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T Dalg)
      (E : DomainTheory.NeighbourhoodSystems.DomainObj.{w})
      (isoE :
        @DomainTheory.NeighbourhoodSystems.Iso.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T E)
          E),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq.{w, w}
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T Dalg).carrier
        E.carrier
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{w + 1, w} DomainTheory.NeighbourhoodSystems.DomainObj.{w}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{w} T Dalg).sys
        E.sys :=
  DomainTheory.NeighbourhoodSystems.trianglelefteq_of_isInitial.{w}

end DomainTheory.NeighbourhoodSystems

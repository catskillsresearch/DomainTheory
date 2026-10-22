module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69.nonempty_algHom_of_continuousOnMaps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_69.{u_4} : ∀
  (T :
    @DomainTheory.NeighbourhoodSystems.Endofunctor.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}),
  DomainTheory.NeighbourhoodSystems.ContinuousOnMaps.{u_4} T →
    ∀ {D : DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}}
      (iso :
        @DomainTheory.NeighbourhoodSystems.Iso.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
            DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
          D)
      (B :
        @DomainTheory.NeighbourhoodSystems.TAlgebra.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T),
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{u_4, u_4}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B)).carrier
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).carrier
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B)).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{u_4 + 1, u_4}
            DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B) →
        Nonempty.{u_4 + 1}
          (@Subtype.{u_4 + 1}
            (@DomainTheory.NeighbourhoodSystems.AlgHom.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                  (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                  D iso))
              B)
            fun
              (g :
                @DomainTheory.NeighbourhoodSystems.AlgHom.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))
                  B) =>
            @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{u_4, u_4}
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).sys
              (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                  (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                    (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                    D iso))
                B g)) :=
  DomainTheory.NeighbourhoodSystems.nonempty_algHom_of_continuousOnMaps.{u_4}

end DomainTheory.NeighbourhoodSystems

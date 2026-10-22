module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.exists_X_of_mem_step
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.exists_X_of_mem_stepFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.hii_hard_direction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.hii_piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piD_of_formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitaryProjection_piU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitary_piU_of_formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isFinitary_piU_of_isFinitary_piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.piD_rel_self_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_827 : And
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
    (∀
      {d :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsFinitary
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (DomainTheory.NeighbourhoodSystems.piD d) →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.piU d)))
  (∀
    (d :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
    {X :
      Set
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (DomainTheory.NeighbourhoodSystems.piD d) X X)
      (∃ (hX :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          X),
        @Membership.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          (@Set.instMembership
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          X
          (@DomainTheory.NeighbourhoodSystems.gSection
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            Rat Rat
            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX))) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
    (∀
      {d :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsFinitary
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (DomainTheory.NeighbourhoodSystems.piD d) →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.piU d)))
  (∀
    (d :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
    {X :
      Set
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (DomainTheory.NeighbourhoodSystems.piD d) X X)
      (∃ (hX :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          X),
        @Membership.mem
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (Set
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          (@Set.instMembership
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U))
          X
          (@DomainTheory.NeighbourhoodSystems.gSection
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            Rat Rat
            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
    (∀
      {d :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsFinitary
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (DomainTheory.NeighbourhoodSystems.piD d) →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.piU d))
    (@And.intro
      (And
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d)))
      (∀
        {d :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
            {Y :
              Set
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)},
            Iff
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (DomainTheory.NeighbourhoodSystems.piD d) x)
                Y)
              (And
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  Y)
                (∃ (X :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)),
                  And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      x X)
                    (And
                      (@LE.le
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instLE
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        X Y)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d))
      (@And.intro
        (And
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
        (∀
          (d :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.piU d))
        (@And.intro
          (And
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d)))
          (∀
            (d :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            (∀
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))) →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d))
          (@And.intro
            (And
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X))))))
            (∀
              (d :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (DomainTheory.NeighbourhoodSystems.piD d))
            (@And.intro
              (And
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
              (∀
                (d :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                (x :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                {Y :
                  Set
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)},
                Iff
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.piD d) x)
                    Y)
                  (And
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y)
                    (∃ (X :
                      Set
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)),
                      And
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          x X)
                        (And
                          (@LE.le
                            (Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            (@Set.instLE
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                            X Y)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (DomainTheory.NeighbourhoodSystems.piD d) X X)))))
              (@And.intro
                (And
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X))))
                (∀
                  (d :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                  (x :
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U))
                  {Y :
                    Set
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)},
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      Y →
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        Y
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X Y)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                (@And.intro
                  (And
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y))
                  (∀
                    (d :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                    (x :
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U))
                    (L : List (Prod (Set Rat) (Set Rat))),
                    @Membership.mem
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                        (Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@Set.instMembership
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                        (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U L)
                        (DomainTheory.NeighbourhoodSystems.piDApply d
                          (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U x)) →
                      ∃ (X :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                        And
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            x X)
                          (And
                            (@LE.le
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instLE
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              X
                              (@DomainTheory.NeighbourhoodSystems.stepFun Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U L))
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                  (@And.intro
                    (And
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x))))))
                    (∀
                      (d :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U)
                      (x :
                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U))
                      {Y :
                        Set
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                            DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                          Y →
                        ∀
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              x X →
                            @LE.le
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instLE
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                X Y →
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (DomainTheory.NeighbourhoodSystems.piD d) X X →
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (DomainTheory.NeighbourhoodSystems.piD d) x)
                                  Y)
                    (@And.intro
                      (And
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z)))
                      (∀
                        (d :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U)
                        (x :
                          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U))
                        {Y :
                          Set
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                        Iff
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                              DomainTheory.NeighbourhoodSystems.U)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              (DomainTheory.NeighbourhoodSystems.piD d) x)
                            Y)
                          (And
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              Y)
                            (@Membership.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              (@Set.instMembership
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                              Y
                              (DomainTheory.NeighbourhoodSystems.piDApply d
                                (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)))))
                      (@And.intro
                        (And
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)))))
                        (∀
                          (d :
                            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                          {X :
                            Set
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)}
                          (hX :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                              (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                DomainTheory.NeighbourhoodSystems.U)
                              X)
                          {Y Z : Set Rat}
                          (hY :
                            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem Rat
                              DomainTheory.NeighbourhoodSystems.U Y),
                          Iff
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel Rat Rat
                              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.gSection
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                Rat Rat
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX)
                              Y Z)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem Rat
                              DomainTheory.NeighbourhoodSystems.U
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      X hX)))
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Rat
                                  DomainTheory.NeighbourhoodSystems.U Y hY))
                              Z))
                        (@And.intro
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            (x :
                              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U))
                            {Y₀ Z₀ : Set Rat},
                            @Membership.mem
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@Set.instMembership
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                (@DomainTheory.NeighbourhoodSystems.step Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U Y₀ Z₀)
                                (DomainTheory.NeighbourhoodSystems.piDApply d
                                  (@DomainTheory.NeighbourhoodSystems.toApproxMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U x)) →
                              ∃ (X :
                                Set
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    x X)
                                  (And
                                    (@LE.le
                                      (Set
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      (@Set.instLE
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                      X
                                      (@DomainTheory.NeighbourhoodSystems.step Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U Y₀ Z₀))
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      (DomainTheory.NeighbourhoodSystems.piD d) X X)))
                          (∀
                            (d :
                              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                            {X W :
                              Set
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)},
                            Iff
                              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                                  DomainTheory.NeighbourhoodSystems.U)
                                (DomainTheory.NeighbourhoodSystems.piD d) X W)
                              (∃ (hX :
                                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                  X),
                                And
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    W)
                                  (@Membership.mem
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                    (Set
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    (@Set.instMembership
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U))
                                    W
                                    (@DomainTheory.NeighbourhoodSystems.gSection
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.piDUncurried d) X hX))))
                          DomainTheory.NeighbourhoodSystems.exists_X_of_mem_step
                          DomainTheory.NeighbourhoodSystems.piD_rel_iff)
                        DomainTheory.NeighbourhoodSystems.gSection_piDUncurried_rel_iff)
                      DomainTheory.NeighbourhoodSystems.piD_toElementMap_mem_iff)
                    DomainTheory.NeighbourhoodSystems.hii_easy_direction)
                  DomainTheory.NeighbourhoodSystems.exists_X_of_mem_stepFun)
                DomainTheory.NeighbourhoodSystems.hii_hard_direction)
              DomainTheory.NeighbourhoodSystems.hii_piD)
            DomainTheory.NeighbourhoodSystems.isFinitaryProjection_piD)
          DomainTheory.NeighbourhoodSystems.isFinitaryProjection_piD_of_formula)
        DomainTheory.NeighbourhoodSystems.isFinitaryProjection_piU)
      @DomainTheory.NeighbourhoodSystems.isFinitary_piU_of_formula)
    @DomainTheory.NeighbourhoodSystems.isFinitary_piU_of_isFinitary_piD)
  DomainTheory.NeighbourhoodSystems.piD_rel_self_iff

end DomainTheory.NeighbourhoodSystems

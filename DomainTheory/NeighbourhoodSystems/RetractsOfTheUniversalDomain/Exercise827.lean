/-ai
If the closed form of the product of d at the approximable map of x lies in the single step from Y0 to Z0, then some neighbourhood X of the function space lies in x, is contained in that step, and is self-related by the product. If H is a retraction of the function space of the universal domain, then i-arrow composed with H composed with j-arrow is a retraction of the universal domain. If the closed form of the product of d at the approximable map of x lies in the step function of a list of rational pairs, then some neighbourhood X lies in x, is contained in that step function, and is self-related by the product. If Y is a neighbourhood of the function space and the closed form of the product of d at the approximable map of x lies in Y, then some neighbourhood X lies in x, is contained in Y, and is self-related by the product. The image of a function-space element x under the product of d lies in Y if and only if Y is a neighbourhood and some neighbourhood X lies in x, is contained in Y, and is self-related by the product. The product of every approximable self-map d, as a self-map of the function space, is a finitary projection. If the product of d on the function space satisfies Scott's step-closure formula, then it is a finitary projection. The product of d, regarded as a self-map of the universal domain, is a finitary projection. If the product of d on the function space satisfies the step-closure formula, then the product regarded as a self-map of the universal domain is finitary. If the product of d on the function space is finitary, then the product regarded as a self-map of the universal domain is finitary. The function-space product of d relates a set X to itself if and only if X is a neighbourhood and the section of the uncurried product at X lies in X.

The numbered name example_827 is the conjunction of these statements. The proof is that conjunction.
ai-/
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

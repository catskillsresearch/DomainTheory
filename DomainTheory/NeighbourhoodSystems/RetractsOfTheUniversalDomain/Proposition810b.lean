module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.proposition_8_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_combinators
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitaryProjection_sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_sumComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_810_b : And
  (And
    (And
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
    (∀
      (a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U),
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
  (∀
    (a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U),
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.sumComb a b)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
    (∀
      (a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U),
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
  (∀
    (a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U),
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
        @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.sumComb a b))
  (@And.intro
    (And
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
    (∀
      (a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U),
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
          @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.prodComb a b))
    (@And.intro
      (And
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b)))
      (∀
        (a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            @DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
      (@And.intro
        (And
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b)))
        (∀
          (a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b))
        (@And.intro
          (And
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
          (∀
            (a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U),
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
          (@And.intro
            (And
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.sumComb a b))
                    (And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.prodComb a b))
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b))))
            (@And.intro
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    And
                      (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.sumComb a b))
                      (And
                        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.prodComb a b))
                        (And
                          (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat
                            DomainTheory.NeighbourhoodSystems.U (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                          (And
                            (Nonempty
                              (@OrderIso
                                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                  (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U a)
                                    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                      DomainTheory.NeighbourhoodSystems.U b)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                    (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                (@Subtype
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)
                                (@Preorder.toLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum Rat Rat))
                                    (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                      (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                  (@PartialOrder.toPreorder
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                      (Option (Sum Rat Rat))
                                      (@DomainTheory.NeighbourhoodSystems.sum Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty a)
                                        (DomainTheory.NeighbourhoodSystems.fixedNbhd_mem_nonempty b)))))
                                (@Subtype.instLE
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                    DomainTheory.NeighbourhoodSystems.U)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement Rat
                                        DomainTheory.NeighbourhoodSystems.U)))
                                  fun
                                    (y :
                                      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U) =>
                                  @Eq
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                      (DomainTheory.NeighbourhoodSystems.sumComb a b) y)
                                    y)))
                            (And
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                    (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                      (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (Sum Rat Rat)
                                        (@DomainTheory.NeighbourhoodSystems.prod Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.prodComb a b) y)
                                      y)))
                              (Nonempty
                                (@OrderIso
                                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b))
                                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U a)
                                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                        DomainTheory.NeighbourhoodSystems.U b)))
                                  (@Subtype
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y)
                                  (@Preorder.toLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b))
                                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U a)
                                        (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                          DomainTheory.NeighbourhoodSystems.U b)))
                                    (@PartialOrder.toPreorder
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b))
                                        (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U a)
                                          (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat
                                            DomainTheory.NeighbourhoodSystems.U b)))))
                                  (@Subtype.instLE
                                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                      DomainTheory.NeighbourhoodSystems.U)
                                    (@Preorder.toLE
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@PartialOrder.toPreorder
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U)
                                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                                          Rat DomainTheory.NeighbourhoodSystems.U)))
                                    fun
                                      (y :
                                        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                          DomainTheory.NeighbourhoodSystems.U) =>
                                    @Eq
                                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Rat
                                        DomainTheory.NeighbourhoodSystems.U)
                                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Rat Rat
                                        DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U
                                        (DomainTheory.NeighbourhoodSystems.arrowComb a b) y)
                                      y))))))))
              (∀
                (a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                      (DomainTheory.NeighbourhoodSystems.arrowComb a b))
              (@DomainTheory.NeighbourhoodSystems.proposition_8_10)
              DomainTheory.NeighbourhoodSystems.finitaryProjection_arrowComb)
            @DomainTheory.NeighbourhoodSystems.finitaryProjection_combinators)
          DomainTheory.NeighbourhoodSystems.finitaryProjection_prodComb)
        DomainTheory.NeighbourhoodSystems.finitaryProjection_sumComb)
      DomainTheory.NeighbourhoodSystems.finitary_arrowComb)
    DomainTheory.NeighbourhoodSystems.finitary_prodComb)
  DomainTheory.NeighbourhoodSystems.finitary_sumComb

end DomainTheory.NeighbourhoodSystems

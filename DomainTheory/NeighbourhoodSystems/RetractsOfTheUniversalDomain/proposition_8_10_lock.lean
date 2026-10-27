module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_810 : And
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
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))))
    (∀
      {a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            (DomainTheory.NeighbourhoodSystems.prodComb a b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
  (∀
    {a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @LE.le
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          (DomainTheory.NeighbourhoodSystems.sumComb a b)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)) :=
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
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))))
    (∀
      {a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            (DomainTheory.NeighbourhoodSystems.prodComb a b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
  (∀
    {a b :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @LE.le
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
              DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          (DomainTheory.NeighbourhoodSystems.sumComb a b)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U))
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
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))))
    (∀
      {a b :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U)
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
          a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            (DomainTheory.NeighbourhoodSystems.prodComb a b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U))
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
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U)))
      (∀
        {a b :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @LE.le
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U)
            (@Preorder.toLE
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@PartialOrder.toPreorder
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                  DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
            a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U))
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U))
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U))))
              (DomainTheory.NeighbourhoodSystems.lamComb a b)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)))
      (@And.intro
        (And
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
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.sumComb a b)))
        (∀
          {a b :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @LE.le
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                    DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
              a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
            @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                b (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U) →
              @LE.le
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U)
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap Rat Rat
                      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U)))
                (DomainTheory.NeighbourhoodSystems.arrowComb a b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap Rat DomainTheory.NeighbourhoodSystems.U))
        (@And.intro
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
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                    (DomainTheory.NeighbourhoodSystems.prodComb a b)))
          (∀
            {a b :
              @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                DomainTheory.NeighbourhoodSystems.U},
            @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
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
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b)))
            (∀
              {a b :
                @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                  DomainTheory.NeighbourhoodSystems.U},
              @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
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
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b)))
              (∀
                {a b :
                  @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                    DomainTheory.NeighbourhoodSystems.U},
                @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                    @DomainTheory.NeighbourhoodSystems.Retraction
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U)
                      (DomainTheory.NeighbourhoodSystems.lamComb a b))
              (@And.intro
                (And
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b)))
                (∀
                  {a b :
                    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                      DomainTheory.NeighbourhoodSystems.U},
                  @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
                    @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U b →
                      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
                        (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                (@And.intro
                  (And
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b)))
                  (∀
                    {a b :
                      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                        DomainTheory.NeighbourhoodSystems.U},
                    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                          (DomainTheory.NeighbourhoodSystems.sumComb a b))
                  (@And.intro
                    (And
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))))
                    (∀
                      {a b :
                        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                          DomainTheory.NeighbourhoodSystems.U},
                      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                            (DomainTheory.NeighbourhoodSystems.prodComb a b))
                    (@And.intro
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                              (DomainTheory.NeighbourhoodSystems.arrowComb a b))
                      (∀
                        {a b :
                          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
                            DomainTheory.NeighbourhoodSystems.U},
                        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
                          @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
                            And
                              (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                (DomainTheory.NeighbourhoodSystems.sumComb a b))
                              (And
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                                (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
                                  (DomainTheory.NeighbourhoodSystems.arrowComb a b))))
                      @DomainTheory.NeighbourhoodSystems.arrowComb.isProjection
                      @DomainTheory.NeighbourhoodSystems.isProjection_combinators)
                    @DomainTheory.NeighbourhoodSystems.prodComb.isProjection)
                  @DomainTheory.NeighbourhoodSystems.sumComb.isProjection)
                @DomainTheory.NeighbourhoodSystems.arrowComb.isRetraction)
              @DomainTheory.NeighbourhoodSystems.isRetraction_lamComb)
            @DomainTheory.NeighbourhoodSystems.prodComb.isRetraction)
          @DomainTheory.NeighbourhoodSystems.sumComb.isRetraction)
        @DomainTheory.NeighbourhoodSystems.arrowComb.le_idMap)
      @DomainTheory.NeighbourhoodSystems.le_idMap_lamComb)
    @DomainTheory.NeighbourhoodSystems.prodComb.le_idMap)
  @DomainTheory.NeighbourhoodSystems.sumComb.le_idMap

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
              DomainTheory.NeighbourhoodSystems.arrowComb.finitaryProjection)
            @DomainTheory.NeighbourhoodSystems.finitaryProjection_combinators)
          DomainTheory.NeighbourhoodSystems.prodComb.finitaryProjection)
        DomainTheory.NeighbourhoodSystems.sumComb.finitaryProjection)
      DomainTheory.NeighbourhoodSystems.arrowComb.finitary)
    DomainTheory.NeighbourhoodSystems.prodComb.finitary)
  DomainTheory.NeighbourhoodSystems.sumComb.finitary

end DomainTheory.NeighbourhoodSystems

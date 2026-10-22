/-ai
If two self-maps of the universal domain are projections, then so is their arrow combinator. If two self-maps of the universal domain are projections, then so are their sum, their product, and their arrow. If two self-maps of the universal domain are projections, then so is their product combinator. If two self-maps of the universal domain are projections, then so is their sum combinator. If two self-maps of the universal domain are retractions, then so is their arrow combinator. If two self-maps of the universal domain are retractions, then so is their lambda combinator. If two self-maps of the universal domain are retractions, then so is their product combinator. If two self-maps of the universal domain are retractions, then so is their sum combinator. If two self-maps of the universal domain lie below the identity, then so does their arrow combinator. If two self-maps of the universal domain lie below the identity, then their lambda combinator lies below the identity of the function space. If two self-maps of the universal domain lie below the identity, then so does their product combinator. If two self-maps of the universal domain lie below the identity, then so does their sum combinator.

The numbered name theorem_810 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isProjection_arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isProjection_combinators
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isProjection_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isProjection_sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_lamComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.le_idMap_arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.le_idMap_lamComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.le_idMap_prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.le_idMap_sumComb

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
                      @DomainTheory.NeighbourhoodSystems.isProjection_arrowComb
                      @DomainTheory.NeighbourhoodSystems.isProjection_combinators)
                    @DomainTheory.NeighbourhoodSystems.isProjection_prodComb)
                  @DomainTheory.NeighbourhoodSystems.isProjection_sumComb)
                @DomainTheory.NeighbourhoodSystems.isRetraction_arrowComb)
              @DomainTheory.NeighbourhoodSystems.isRetraction_lamComb)
            @DomainTheory.NeighbourhoodSystems.isRetraction_prodComb)
          @DomainTheory.NeighbourhoodSystems.isRetraction_sumComb)
        @DomainTheory.NeighbourhoodSystems.le_idMap_arrowComb)
      @DomainTheory.NeighbourhoodSystems.le_idMap_lamComb)
    @DomainTheory.NeighbourhoodSystems.le_idMap_prodComb)
  @DomainTheory.NeighbourhoodSystems.le_idMap_sumComb

end DomainTheory.NeighbourhoodSystems

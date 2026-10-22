module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.idMap_fixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise412.no_greatest_fixedPoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise412

set_option linter.unusedVariables false

theorem example_412 : And
  (∀
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T
        DomainTheory.NeighbourhoodSystems.Exercise412.T
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise412.T)
        x)
      x)
  (Not
    (∃ (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
      And
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Exercise412.T)
            z)
          z)
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T),
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                x)
              x →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)))
              x z))) :=
  @And.intro
  (∀
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T
        DomainTheory.NeighbourhoodSystems.Exercise412.T
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise412.T)
        x)
      x)
  (Not
    (∃ (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
      And
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Exercise412.T)
            z)
          z)
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T),
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                x)
              x →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)))
              x z)))
  DomainTheory.NeighbourhoodSystems.Exercise412.idMap_fixed
  DomainTheory.NeighbourhoodSystems.Exercise412.no_greatest_fixedPoint

end DomainTheory.NeighbourhoodSystems.Exercise412

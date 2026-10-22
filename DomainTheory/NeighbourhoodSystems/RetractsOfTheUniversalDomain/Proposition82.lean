module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.isRetraction_retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82.retraction_of_subsystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Subsystem

set_option linter.unusedVariables false

theorem theorem_82.{u_1} : And
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @DomainTheory.NeighbourhoodSystems.Retraction α E
      (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    And
      (@DomainTheory.NeighbourhoodSystems.Retraction α E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
      (Nonempty
        (@OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
          (@Subtype (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
          (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y)))) :=
  @And.intro
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @DomainTheory.NeighbourhoodSystems.Retraction α E
      (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    And
      (@DomainTheory.NeighbourhoodSystems.Retraction α E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
      (Nonempty
        (@OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
          (@Subtype (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
          (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y))))
  @DomainTheory.NeighbourhoodSystems.Subsystem.isRetraction_retractionOfSubsystem
  @DomainTheory.NeighbourhoodSystems.Subsystem.retraction_of_subsystem

end DomainTheory.NeighbourhoodSystems.Subsystem

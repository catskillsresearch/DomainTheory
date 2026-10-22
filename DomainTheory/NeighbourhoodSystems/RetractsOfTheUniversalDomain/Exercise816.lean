module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816.exercise_8_16
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816.isFinitaryProjection_le_iff_fixedNbhd_subsystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_816.{u} : And
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    And
      (∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            Iff
              (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                a b)
              (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
      (∀ {P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E}
        {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α α E E P P a →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
        Iff
          (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
            a b)
          (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b))) :=
  @And.intro
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    And
      (∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            Iff
              (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                a b)
              (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
      (∀ {P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E}
        {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α α E E P P a →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
        Iff
          (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
            a b)
          (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
  @DomainTheory.NeighbourhoodSystems.exercise_8_16
  @DomainTheory.NeighbourhoodSystems.isFinitaryProjection_le_iff_fixedNbhd_subsystem

end DomainTheory.NeighbourhoodSystems

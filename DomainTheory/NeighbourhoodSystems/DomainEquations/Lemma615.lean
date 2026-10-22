module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.trianglelefteq_of_projectionPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_615.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (i : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β D E)
  (j : @DomainTheory.NeighbourhoodSystems.ApproximableMap β α E D),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D E D j i)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D) →
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap β β E E)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β α β E D E i j)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β E) →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E :=
  @DomainTheory.NeighbourhoodSystems.trianglelefteq_of_projectionPair

end DomainTheory.NeighbourhoodSystems

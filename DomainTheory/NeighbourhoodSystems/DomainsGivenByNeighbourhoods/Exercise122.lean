module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.isOpen_isUpperSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.isOpen_basicOpen
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.isOpen_iff_upper_basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.le_iff_isOpen_imp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_122.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        {U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)},
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U →
          ∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Set α),
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
      Iff
        (@IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U)
        (And
          (∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
          (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              ∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V x X)
                  (@LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                    (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X) U)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    Iff
      (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x y)
      (∀ (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U →
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        {U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)},
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U →
          ∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Set α),
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
      Iff
        (@IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U)
        (And
          (∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
          (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              ∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V x X)
                  (@LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                    (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X) U)))))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    Iff
      (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x y)
      (∀ (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U →
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        {U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)},
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U →
          ∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Set α),
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
      Iff
        (@IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U)
        (And
          (∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
          (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              ∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V x X)
                  (@LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                    (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X) U))))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        {U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)},
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V) U →
          ∀ ⦃x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V⦄,
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U x →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  x y →
                @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) U y)
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Set α),
        @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.basicOpen α V X))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isOpen_isUpperSet
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isOpen_basicOpen)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isOpen_iff_upper_basic)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.le_iff_isOpen_imp

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.galois
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_bounded
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_eq_sInf
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.inj_sSup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.lowerSet_directed
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.proj_eq_sSup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.upperSet_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair

set_option linter.unusedVariables false

theorem example_625.{u_1} : And
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y))))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
    @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y))))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
    @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x))
  (@And.intro
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y)))
    (@And.intro
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c)))
      (@And.intro
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS)))
        (@And.intro
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x)))
          (@And.intro
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S))
            @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.galois
            @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded)
          @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_eq_sInf)
        @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_sSup)
      @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_directed)
    @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj_eq_sSup)
  @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty

end DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.fixedDomain_fixOp_iso_T
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.fixedNbhd_fixOp_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.isFinitaryProjection_fixOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise823

set_option linter.unusedVariables false

theorem example_823 : And
  (And
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
              (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
        ∀
          (T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T a)))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T a))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T a)))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a)))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))))))) →
            Nonempty
              (@OrderIso
                (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                    (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                  (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                    (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t) y)
                    y)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                      (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                    (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                      (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
              (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
        ∀ {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a) a →
              @DomainTheory.NeighbourhoodSystems.Subsystem α
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)))
  (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (t :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
    (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
            (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)) :=
  @And.intro
  (And
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
              (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
        ∀
          (T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T a)))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T a))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T a)))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a)))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))))))) →
            Nonempty
              (@OrderIso
                (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                    (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                  (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                    (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t) y)
                    y)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                      (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                    (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                      (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
              (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
        ∀ {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a) a →
              @DomainTheory.NeighbourhoodSystems.Subsystem α
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)))
  (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (t :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
    (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
            (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
        (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
  (@And.intro
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
              (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
        ∀
          (T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T a)))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T a))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T a)))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a)))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a))))))) →
            Nonempty
              (@OrderIso
                (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                    (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                  (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                    (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t) y)
                    y)
                (@Preorder.toLE
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                      (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                    (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                      (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                  (@PartialOrder.toPreorder
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
              (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a)) →
        ∀ {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                (@DomainTheory.NeighbourhoodSystems.Exercise823.tOp α E t a) a →
              @DomainTheory.NeighbourhoodSystems.Subsystem α
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp α E t))
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
    @DomainTheory.NeighbourhoodSystems.Exercise823.fixedDomain_fixOp_iso_T
    @DomainTheory.NeighbourhoodSystems.Exercise823.fixedNbhd_fixOp_subsystem)
  @DomainTheory.NeighbourhoodSystems.Exercise823.isFinitaryProjection_fixOp

end DomainTheory.NeighbourhoodSystems.Exercise823

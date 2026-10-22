/-ai
If an operator on self-maps sends finitary projections to finitary projections, and a correspondence identifies the fixed-point set of the operator at each finitary projection with the domain assigned to that projection, then the fixed-point set of the fixed point of the operator is order-isomorphic to the domain assigned to that fixed point. If an operator on self-maps sends finitary projections to finitary projections, and a finitary projection lies above its image under the operator, then the fixed neighbourhood system of the operator's fixed point is a literal subsystem of the fixed neighbourhood system of that projection. If an operator on the function space sends finitary projections to finitary projections, then its fixed point is a finitary projection.

The numbered name example_823 is the conjunction of these statements. The proof is that conjunction.
ai-/
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

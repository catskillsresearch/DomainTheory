/-ai
If two operators on pairs of self-maps send finitary projections to finitary projections, and two correspondences identify the fixed-point sets of those images with the domains assigned to the pair, then the fixed-point set of the first simultaneous component is order-isomorphic to the first assigned domain, and the fixed-point set of the second component is order-isomorphic to the second assigned domain. If two operators on pairs of self-maps send finitary projections to finitary projections, and two finitary projections each lie above the corresponding operator applied to the pair, then the fixed neighbourhood system of the first simultaneous component is a literal subsystem of the first projection's fixed neighbourhood system, and likewise for the second component. If two approximable maps from the pair space into the function space send pairs of finitary projections to finitary projections, then both components of their simultaneous fixed point are finitary projections.

The numbered name example_824 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.fixedDomain_aStar_bStar_iso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.fixedNbhd_aStar_bStar_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise824.isFinitaryProjection_aStar_bStar

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise824

set_option linter.unusedVariables false

theorem example_824 : And
  (And
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀
          (S T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
                @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                  Nonempty
                    (@OrderIso
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b)))
                      (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                        fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) y)
                          y)
                      (@Preorder.toLE
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b)))
                        (@PartialOrder.toPreorder
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b)))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))))))) →
            (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                    Nonempty
                      (@OrderIso
                        (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b)))
                        (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                          fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) y)
                            y)
                        (@Preorder.toLE
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b)))
                          (@PartialOrder.toPreorder
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b)))
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                                (T a b))))))) →
              And
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))))))
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) a →
                @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                    (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b))))
  (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (s t :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
    (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            And
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
      And
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))) :=
  @And.intro
  (And
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀
          (S T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
                @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                  Nonempty
                    (@OrderIso
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b)))
                      (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                        fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) y)
                          y)
                      (@Preorder.toLE
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b)))
                        (@PartialOrder.toPreorder
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b)))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))))))) →
            (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                    Nonempty
                      (@OrderIso
                        (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b)))
                        (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                          fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) y)
                            y)
                        (@Preorder.toLE
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b)))
                          (@PartialOrder.toPreorder
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b)))
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                                (T a b))))))) →
              And
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))))))
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) a →
                @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                    (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b))))
  (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (s t :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
    (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            And
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
      And
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
  (@And.intro
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀
          (S T :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
              @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E →
                @Sigma Type fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
          (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
              @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                  Nonempty
                    (@OrderIso
                      (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S a b)))
                      (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                        fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) y)
                          y)
                      (@Preorder.toLE
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S a b)))
                        (@PartialOrder.toPreorder
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b)))
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (S a b))))))) →
            (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
                @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
                  @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
                    Nonempty
                      (@OrderIso
                        (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T a b)))
                        (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@PartialOrder.toPreorder
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                          fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) y)
                            y)
                        (@Preorder.toLE
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                            (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b))
                            (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                              (T a b)))
                          (@PartialOrder.toPreorder
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b)))
                            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                              (@Sigma.fst Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) (T a b))
                              (@Sigma.snd Type
                                (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                                (T a b))))))) →
              And
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (S (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))))))
                (Nonempty
                  (@OrderIso
                    (@DomainTheory.NeighbourhoodSystems.Exercise823.Fix α E
                      (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                      (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                      (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                        (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                    (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                      fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
                      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                          (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t) y)
                        y)
                    (@Preorder.toLE
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                        (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                        (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                          (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                            (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                      (@PartialOrder.toPreorder
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))))
                        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                          (@Sigma.fst Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))
                          (@Sigma.snd Type (fun (β : Type) => DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
                            (T (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t)
                              (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t)))))))))
    (∀ {α : Type} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (s t :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.Exercise824.PairSpace α E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
      (∀ (a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b))) →
        ∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
              @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                  (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E s a b) a →
                @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                    (@DomainTheory.NeighbourhoodSystems.Exercise824.binOp α E t a b) b →
                  And
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.aStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem α
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E
                        (@DomainTheory.NeighbourhoodSystems.Exercise824.bStar α E s t))
                      (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
    @DomainTheory.NeighbourhoodSystems.Exercise824.fixedDomain_aStar_bStar_iso
    @DomainTheory.NeighbourhoodSystems.Exercise824.fixedNbhd_aStar_bStar_subsystem)
  @DomainTheory.NeighbourhoodSystems.Exercise824.isFinitaryProjection_aStar_bStar

end DomainTheory.NeighbourhoodSystems.Exercise824

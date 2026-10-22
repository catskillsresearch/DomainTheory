module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.formula_of_isFinitaryProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.finitaryProjection_iff_formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.isFinitaryProjection_of_formula

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_85.{u} : And
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
          Iff
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
            (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
              (∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                  (And (@LE.le (Set α) (@Set.instLE α) X Y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X)))))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
      Iff (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a)
        (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
          Iff
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
            (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
              (∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                  (And (@LE.le (Set α) (@Set.instLE α) X Y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X)))))))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
          (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
            (∃ (X : Set α),
              And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                (And (@LE.le (Set α) (@Set.instLE α) X Y)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X))))) →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a) :=
  @And.intro
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
          Iff
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
            (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
              (∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                  (And (@LE.le (Set α) (@Set.instLE α) X Y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X)))))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
      Iff (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a)
        (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
          Iff
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
            (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
              (∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                  (And (@LE.le (Set α) (@Set.instLE α) X Y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X)))))))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
          (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
            (∃ (X : Set α),
              And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                (And (@LE.le (Set α) (@Set.instLE α) X Y)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X))))) →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a)
  (@And.intro
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
          Iff
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
            (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
              (∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                  (And (@LE.le (Set α) (@Set.instLE α) X Y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X)))))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E),
      Iff (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a)
        (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) {Y : Set α},
          Iff
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a x) Y)
            (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E Y)
              (∃ (X : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α E x X)
                  (And (@LE.le (Set α) (@Set.instLE α) X Y)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α α E E a X X))))))
    @DomainTheory.NeighbourhoodSystems.formula_of_isFinitaryProjection
    @DomainTheory.NeighbourhoodSystems.finitaryProjection_iff_formula)
  @DomainTheory.NeighbourhoodSystems.isFinitaryProjection_of_formula

end DomainTheory.NeighbourhoodSystems

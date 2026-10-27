module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}
/- concordance: source L4854 THEOREM 8.5 finitary projection test -/
/-- **Theorem 8.5 (Scott 1981, PRG-19), in full.** `a : E → E` is a finitary projection iff it
satisfies the step-closure formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`. -/
theorem finitaryProjection_iff_formula (a : ApproximableMap E E) :
    FinitaryProjection a ↔ ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X :=
  ⟨fun h => formula_of_isFinitaryProjection h, fun hii => isFinitaryProjection_of_formula a hii⟩
end

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


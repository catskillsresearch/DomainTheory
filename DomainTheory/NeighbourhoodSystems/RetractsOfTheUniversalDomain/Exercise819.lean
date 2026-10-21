/-ai
If every neighbourhood of E is nonempty, the truth-value domain embeds in E, and the function space of E with itself embeds in E, then both the sum of E with itself and the product of E with itself embed in E. If the three-point domain is a retract of E and the function space from E to E is a retract of E, then the product of E with itself is a retract of E. If the three-point domain is a retract of E and the function space from E to E is a retract of E, then the sum of E with itself is a retract of E.

The numbered name example_819 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.exercise_8_19
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_trianglelefteq_of
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sum_trianglelefteq_of

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_819.{u} : And
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          And
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
              (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
              (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
            (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
        DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E) :=
  @And.intro
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          And
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
              (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
              (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
            (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
        DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
  (@And.intro
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (hE : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X → @Set.Nonempty α X),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          And
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Option (Sum α α)) α
              (@DomainTheory.NeighbourhoodSystems.sum α α E E hE hE) E)
            (@DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
              (@DomainTheory.NeighbourhoodSystems.prod α α E E) E))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.Example12.Token α
          DomainTheory.NeighbourhoodSystems.Exercise326.TD E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq (Sum α α) α
            (@DomainTheory.NeighbourhoodSystems.prod α α E E) E)
    @DomainTheory.NeighbourhoodSystems.exercise_8_19 @DomainTheory.NeighbourhoodSystems.prod_trianglelefteq_of)
  @DomainTheory.NeighbourhoodSystems.sum_trianglelefteq_of

end DomainTheory.NeighbourhoodSystems

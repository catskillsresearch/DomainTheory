/-ai
A fixed point of a closure operator is compact if and only if it equals the image of the principal element of a single neighbourhood. The fixed-point set of a closure operator is a finitary domain.

The numbered name example_814 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.isCompactFix_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.isFinitary_of_isClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_814.{u} : And
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E}
    (h : @DomainTheory.NeighbourhoodSystems.IsClosureOperator α E a)
    (y : @DomainTheory.NeighbourhoodSystems.FixSet α E a),
    Iff (@DomainTheory.NeighbourhoodSystems.IsCompactFix α E a h y)
      (∃ (X : Set α) (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
          (@Subtype.val (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a y) y)
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α E X hX))))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.IsClosureOperator α E a → @DomainTheory.NeighbourhoodSystems.IsFinitary α E a) :=
  @And.intro
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E}
    (h : @DomainTheory.NeighbourhoodSystems.IsClosureOperator α E a)
    (y : @DomainTheory.NeighbourhoodSystems.FixSet α E a),
    Iff (@DomainTheory.NeighbourhoodSystems.IsCompactFix α E a h y)
      (∃ (X : Set α) (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α E X),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
          (@Subtype.val (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a y) y)
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E a
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α E X hX))))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.IsClosureOperator α E a → @DomainTheory.NeighbourhoodSystems.IsFinitary α E a)
  @DomainTheory.NeighbourhoodSystems.isCompactFix_iff @DomainTheory.NeighbourhoodSystems.isFinitary_of_isClosureOperator

end DomainTheory.NeighbourhoodSystems

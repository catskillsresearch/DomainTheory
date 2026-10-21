/-ai
If zero is never a successor and successor is injective, the carved-out subtype carries a Peano model.

The numbered name example_422 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.exists_peano_submodel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

set_option linter.unusedVariables false

theorem example_422.{u_1} : ∀ {M : Type u_1} (zero : M) (succ : M → M),
  (∀ (n : M), @Ne M zero (succ n)) →
    @Function.Injective M M succ →
      Nonempty
        (DomainTheory.NeighbourhoodSystems.PeanoModel (@DomainTheory.NeighbourhoodSystems.Exercise422.Nat' M zero succ)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise422.exists_peano_submodel

end DomainTheory.NeighbourhoodSystems.Exercise422

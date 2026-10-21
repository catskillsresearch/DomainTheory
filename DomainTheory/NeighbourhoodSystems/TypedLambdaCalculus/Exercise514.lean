/-ai
For every set u of codes, the application of u is an approximable map.

The numbered name example_514 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Fun_isApprox

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

set_option linter.unusedVariables false

theorem example_514 : ∀ (u : Set Nat),
  DomainTheory.NeighbourhoodSystems.Exercise514.IsApprox (DomainTheory.NeighbourhoodSystems.Exercise514.Fun u) :=
  DomainTheory.NeighbourhoodSystems.Exercise514.Fun_isApprox

end DomainTheory.NeighbourhoodSystems.Exercise514

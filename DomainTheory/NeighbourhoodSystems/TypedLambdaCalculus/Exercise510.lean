/-ai
The identity map is strict.

The numbered name example_510 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_idMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

set_option linter.unusedVariables false

theorem example_510.{u_1} : ∀ {α : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
  @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict α α V₀ V₀
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀) :=
  @DomainTheory.NeighbourhoodSystems.Exercise510.isStrict_idMap

end DomainTheory.NeighbourhoodSystems.Exercise510

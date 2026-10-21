/-ai
The identity endofunctor on a category sends each object to itself and each morphism to itself, and therefore preserves identity morphisms and composition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

/-- The **identity endofunctor** on any category: it fixes objects and morphisms. (A convenient
witness that `Endofunctor` is inhabited; used to show Definition 6.8 is non-vacuous.) -/
def idEndofunctor (Obj : Type u) [Category Obj] : Endofunctor Obj where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

end DomainTheory.NeighbourhoodSystems

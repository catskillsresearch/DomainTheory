module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor_obj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

@[simp] theorem idEndofunctor_map {Obj : Type u} [Category Obj] {X Y : Obj}
    (f : (X ⟶ Y)) : (idEndofunctor Obj).map f = f := rfl

end DomainTheory.NeighbourhoodSystems

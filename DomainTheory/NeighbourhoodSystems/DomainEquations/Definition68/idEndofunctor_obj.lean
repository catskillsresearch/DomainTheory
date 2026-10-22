module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.idEndofunctor

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u

@[simp] theorem idEndofunctor_obj {Obj : Type u} [Category Obj] (X : Obj) :
    (idEndofunctor Obj).obj X = X := rfl

end DomainTheory.NeighbourhoodSystems

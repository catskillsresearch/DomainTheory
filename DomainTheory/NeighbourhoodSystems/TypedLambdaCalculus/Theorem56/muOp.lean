module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muBody

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The μ-operator `R(g) = λx,y. cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (muBody f)

end Mu

end DomainTheory.NeighbourhoodSystems.Theorem56

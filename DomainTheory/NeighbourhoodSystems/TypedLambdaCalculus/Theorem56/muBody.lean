/-ai
The minimization body is the approximable map sending a function g and a pair of arguments x and y to the conditional of the zero test of f at that pair, the value x, and g at the successor of x and at y. It is the conditional composed with the pairing of that zero test, the first argument, and the evaluation of the unknown function at the successor of the first argument and the second argument.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.qSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.kSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argY

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The body `M(g, ⟨x, y⟩) = cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp (f.comp qSel))
      (paired argX
        ((evalMap (prod N N) N).comp
          (paired kSel (paired (succMap.comp argX) argY)))))

end Mu

end DomainTheory.NeighbourhoodSystems.Theorem56

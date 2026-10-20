module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.kSel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.argY

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

section PrimRec

variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)

/-- The two-argument body `M(k, ⟨x, y⟩) = cond(zero(x), f(y), g(pred x, y, k(pred x, y)))`. -/
def primBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp argX)
      (paired (f.comp argY)
        (g.comp
          (paired (predMap.comp argX)
            (paired argY
              ((evalMap (prod N N) N).comp
                (paired kSel (paired (predMap.comp argX) argY))))))))

end PrimRec

end DomainTheory.NeighbourhoodSystems.Theorem56

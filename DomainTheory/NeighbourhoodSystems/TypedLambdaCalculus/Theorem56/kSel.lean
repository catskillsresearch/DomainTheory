/-ai
The unknown function is the first projection from the product of the function space of N times N into N with N times N onto that function space.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

/-- The unknown function `k` (`= proj₀`). -/
def kSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (funSpace (prod N N) N) :=
  proj₀ (funSpace (prod N N) N) (prod N N)

end DomainTheory.NeighbourhoodSystems.Theorem56

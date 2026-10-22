module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muRec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

section Mu

variable (f : ApproximableMap (prod N N) N)

/-- The minimization `μ : N → N`, `h̄(m) = ḡ(0̂, m)` (the strict `0`-seeded search). -/
def muMap : ApproximableMap N N := muRec f |>.comp (paired (constLiftN N (fun _ => zeroElt)) (idMap N))

end Mu

end DomainTheory.NeighbourhoodSystems.Theorem56

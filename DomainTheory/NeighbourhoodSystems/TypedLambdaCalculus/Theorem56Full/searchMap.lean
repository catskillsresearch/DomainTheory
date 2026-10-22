/-ai
Given a map φf, the search map is the approximable map from the universal argument domain to N obtained by converting the least fixed point of the search operator of φf back into an approximable map. The counter lives in coordinate 0.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.LamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_argElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)

section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- `searchMap : 𝒩 → N`, the least fixed point of `findOp` (the counter lives in coordinate `0`). -/
def searchMap : ApproximableMap 𝒩 N := toApproxMap (findOp φf).fixElement

end Rfind

end DomainTheory.NeighbourhoodSystems.Theorem56Full

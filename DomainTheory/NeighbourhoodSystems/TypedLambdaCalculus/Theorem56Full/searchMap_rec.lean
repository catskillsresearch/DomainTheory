/-ai
The search map obeys its recursion equation. At an argument z it conditions on the zero-test of the given map at z, returning the head of z when the test succeeds and otherwise continuing the search at the argument obtained by pushing the successor of that head in front of the tail.

The least fixed point of the search operator is fixed by the operator's element map. Currying the search body and evaluating at that fixed point and at z, then rewriting by the definition of the operator and by this fixed-point equation, gives the claim after the element-map form of the body.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.findBody_apply

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




/-- The defining recursion equation of the search. -/
theorem searchMap_rec (z : 𝒩.Element) :
    (searchMap φf).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((searchMap φf).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have hfix : (findOp φf).toElementMap (findOp φf).fixElement = (findOp φf).fixElement :=
    toElementMap_fixElement (findOp φf)
  have hval := toElementMap_curry_apply (findBody φf) (findOp φf).fixElement z
  rw [← findOp, hfix] at hval
  rw [searchMap, hval, findBody_apply]

end Rfind
end DomainTheory.NeighbourhoodSystems.Theorem56Full

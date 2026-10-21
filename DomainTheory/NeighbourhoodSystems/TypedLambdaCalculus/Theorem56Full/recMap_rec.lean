/-ai
The recursion map obeys the primitive-recursion equation. At an argument z it conditions on the zero-test of the head of z, returning the base map on the tail when the test succeeds and otherwise the step map on the argument that pushes the predecessor of the head in front of the push of the recursive value at that predecessor and the tail, followed by the tail.

The least fixed point of the recursion operator is fixed by the operator's element map. Currying the primitive-recursion body and evaluating at that fixed point and at z, then rewriting by the definition of the operator and by this fixed-point equation, gives the claim after the element-map form of the body.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.precBody_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)
open DomainTheory.NeighbourhoodSystems.Exercise511 (head tail push)





















section Prec

variable (φf φg : ApproximableMap 𝒩 N)




/-- The defining recursion equation. -/
theorem recMap_rec (z : 𝒩.Element) :
    (recMap φf φg).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((recMap φf φg).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  have hfix : (recOp φf φg).toElementMap (recOp φf φg).fixElement = (recOp φf φg).fixElement :=
    toElementMap_fixElement (recOp φf φg)
  have hval := toElementMap_curry_apply (precBody φf φg) (recOp φf φg).fixElement z
  rw [← recOp, hfix] at hval
  rw [recMap, hval, precBody_apply]

end Prec
end DomainTheory.NeighbourhoodSystems.Theorem56Full

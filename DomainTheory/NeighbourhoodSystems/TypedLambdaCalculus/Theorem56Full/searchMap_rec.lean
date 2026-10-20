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

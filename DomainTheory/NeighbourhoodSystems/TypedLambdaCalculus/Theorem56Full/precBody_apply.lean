/-ai
Evaluating the primitive-recursion body at a pair of a function-space element and an argument equals the conditional on the zero-test of the head of the argument, with true branch the base map on the tail and false branch the step map on the push of the predecessor of that head together with the push of the function-space element's value at the predecessor and the tail, followed by the tail.

Unfold the body and the element map of a composition, then simplify the element maps of pairing, composition, both projections, the two components of a pair, and evaluation.
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


theorem precBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (precBody φf φg).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((toApproxMap k).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  rw [precBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end Prec
end DomainTheory.NeighbourhoodSystems.Theorem56Full

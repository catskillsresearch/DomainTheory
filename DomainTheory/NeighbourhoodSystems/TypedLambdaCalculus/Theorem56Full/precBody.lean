/-ai
Given maps φf and φg out of the universal argument domain, the primitive-recursion body conditions on the zero-test of the head of the argument. The true branch applies φf to the tail. The false branch applies φg to the vector obtained by pushing the predecessor of the head together with the value of the function-space factor at that predecessor pushed onto the tail, and then the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import Mathlib.Computability.PartrecBasis
import all Mathlib.Computability.PartrecBasis
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.LamDef
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_argElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.component_vecElem

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

/-- The primitive-recursion body. -/
def precBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired (φf.comp ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
        (φg.comp
          ((push N).comp
            (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
              ((push N).comp
                (paired
                  ((evalMap 𝒩 N).comp
                    (paired (proj₀ (funSpace 𝒩 N) 𝒩)
                      ((push N).comp
                        (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                          ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))
                  ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))))))))

end Prec

end DomainTheory.NeighbourhoodSystems.Theorem56Full

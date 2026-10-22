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

/-- The search body `S(k, z) = cond(zero(f z), head z, k(push(succ(head z), tail z)))`. -/
def findBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp (φf.comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩))
        ((evalMap 𝒩 N).comp
          (paired (proj₀ (funSpace 𝒩 N) 𝒩)
            ((push N).comp
              (paired (succMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))))

end Rfind

end DomainTheory.NeighbourhoodSystems.Theorem56Full

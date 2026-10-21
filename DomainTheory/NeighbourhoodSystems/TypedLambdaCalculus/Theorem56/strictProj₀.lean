/-ai
Scott's strict first projection on the product of the flat naturals with itself is the approximable map sending a pair x₀ and x₁ to the conditional of the zero test of x₁ and two copies of x₀. It is the conditional composed with the pairing of the zero test of the second projection and two copies of the first projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond)

/-- Scott's **strict first projection** `λx₀, x₁. cond(zero(x₁), x₀, x₀)` on `N × N`. -/
def strictProj₀ : ApproximableMap (prod N N) N :=
  (cond N).comp
    (paired (zeroMap.comp (proj₁ N N))
      (paired (proj₀ N N) (proj₀ N N)))

end DomainTheory.NeighbourhoodSystems.Theorem56

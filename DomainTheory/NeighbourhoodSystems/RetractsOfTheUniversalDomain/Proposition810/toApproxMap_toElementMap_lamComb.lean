/-ai
Transported through the function-space equivalence, the lambda combinator sends an element to the second map composed after the map of that element composed after the first map.

Compare elements of the universal domain. Unfold the lambda combinator as the curry formula, and chain the elementwise law of curry, composition, the product of maps on a pair, the identity map, and evaluation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.lamComb_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **`lamComb a b`, transported through `funSpaceEquiv`, is exactly `λf. b∘f∘a`.** Chains
`toElementMap_curry_apply` (Theorem 3.12(i)), `toElementMap_prodMap_pair`/`toElementMap_idMap`,
and `evalMap_apply` (Theorem 3.11(i)). -/
theorem toApproxMap_toElementMap_lamComb (a b : ApproximableMap U U)
    (φ : (funSpace U U).Element) :
    toApproxMap ((lamComb a b).toElementMap φ) = b.comp ((toApproxMap φ).comp a) := by
  apply ext_of_toElementMap
  intro z
  rw [lamComb_eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

end DomainTheory.NeighbourhoodSystems

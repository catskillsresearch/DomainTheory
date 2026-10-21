/-ai
The map that reads a function on the three-point domain sends it to the pair of its values at true and at false.

Unfold the pairing into the two evaluations at the constant elements true and false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




theorem toElementMap_funToPair (φ : (funSpace TD E).Element) :
    (funToPair (E := E)).toElementMap φ
      = pair ((toApproxMap φ).toElementMap Example23.trueElt)
          ((toApproxMap φ).toElementMap Example23.falseElt) := by
  simp only [funToPair, toElementMap_paired, toElementMap_comp, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

end Prod
end DomainTheory.NeighbourhoodSystems

/-ai
Evaluation at bottom sends a function to the value, at the bottom of the domain, of the approximable map carried by that function.

Unfold evaluation as the composite of the evaluation map with the pairing of the identity and the constant bottom, and apply the evaluation law.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v


section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


theorem toElementMap_evalBotMap (φ : (funSpace A B).Element) :
    (evalBotMap A B).toElementMap φ = (toApproxMap φ).toElementMap A.bot := by
  simp [evalBotMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

end FunSpace
end DomainTheory.NeighbourhoodSystems

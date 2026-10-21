/-ai
The conditional of a sum, after the map that sends a sum element to the truth value tagging its side together with the two projected values, is the identity on the sum.

Compare the maps on elements. Composition, the identity, and the element formula for the tagging map reduce the composite to the embedded conditional of the tagged product, and the conditional-which identity says that this is the original sum element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_sumToProdT

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`condSum ∘ sumToProdT = I`.** Scott's identity `cond_which`, transported through
`condSumEmb`. -/
theorem condSum_comp_sumToProdT :
    (condSum E E hE hE).comp (sumToProdT hE) = idMap (sum E E hE hE) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_sumToProdT, condSum, toElementMap_comp,
    condSumEmb_toElementMap]
  exact cond_which w

end Sum
end DomainTheory.NeighbourhoodSystems

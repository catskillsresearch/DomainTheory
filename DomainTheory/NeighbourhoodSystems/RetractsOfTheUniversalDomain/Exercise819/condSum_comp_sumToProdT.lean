module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_sumToProdT

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.cond_which
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

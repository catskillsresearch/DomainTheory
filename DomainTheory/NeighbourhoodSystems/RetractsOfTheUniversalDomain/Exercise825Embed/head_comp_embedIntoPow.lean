module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.component_embedIntoPow_zero

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **`head` retracts `embedIntoPow`.** -/
theorem head_comp_embedIntoPow : (head V).comp (embedIntoPow V) = idMap V :=
  ApproximableMap.ext_of_toElementMap fun x => by
    rw [toElementMap_comp, toElementMap_idMap, head_apply, component_embedIntoPow_zero]

end DomainTheory.NeighbourhoodSystems

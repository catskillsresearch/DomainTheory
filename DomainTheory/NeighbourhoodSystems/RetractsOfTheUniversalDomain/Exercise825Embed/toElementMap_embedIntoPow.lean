module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.embedIntoPow

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


theorem toElementMap_embedIntoPow (x : V.Element) :
    (embedIntoPow V).toElementMap x = (push V).toElementMap (pair x (iterSys V).bot) := by
  rw [embedIntoPow, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

end DomainTheory.NeighbourhoodSystems

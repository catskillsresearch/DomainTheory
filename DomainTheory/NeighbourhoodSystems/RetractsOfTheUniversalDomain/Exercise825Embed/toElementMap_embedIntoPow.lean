/-ai
The singleton-stack embedding sends an element to the push of the pair of that element with the bottom of the infinite power.

Unfold the embedding and rewrite by the element actions of a composite, of a pairing, of the identity, and of a constant map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


theorem toElementMap_embedIntoPow (x : V.Element) :
    (embedIntoPow V).toElementMap x = (push V).toElementMap (pair x (iterSys V).bot) := by
  rw [embedIntoPow, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    toElementMap_constMap]

end DomainTheory.NeighbourhoodSystems

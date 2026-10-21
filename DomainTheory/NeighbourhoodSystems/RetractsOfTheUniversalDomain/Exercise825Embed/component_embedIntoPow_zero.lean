/-ai
The head coordinate of the singleton stack of an element is that element.

Rewrite by the element action of the embedding, the head applied to a component, and the head of a push.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.toElementMap_embedIntoPow

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The head of the singleton stack `⟨x, ⊥, ⊥, …⟩` is `x`. -/
theorem component_embedIntoPow_zero (x : V.Element) :
    component ((embedIntoPow V).toElementMap x) 0 = x := by
  rw [toElementMap_embedIntoPow, ← head_apply, head_push]

end DomainTheory.NeighbourhoodSystems

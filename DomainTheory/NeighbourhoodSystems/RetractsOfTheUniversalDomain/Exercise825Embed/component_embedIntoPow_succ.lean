/-ai
Every coordinate past the head of the singleton stack is the bottom.

Rewrite by the element action of the embedding, the tail of a component, the tail of a push, and the components of the bottom sequence.
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


/-- Every coordinate past the head of `⟨x, ⊥, ⊥, …⟩` is `⊥`. -/
theorem component_embedIntoPow_succ (x : V.Element) (n : ℕ) :
    component ((embedIntoPow V).toElementMap x) (n + 1) = V.bot := by
  rw [toElementMap_embedIntoPow, ← component_tail, tail_push, Exercise618.component_bot]

end DomainTheory.NeighbourhoodSystems
